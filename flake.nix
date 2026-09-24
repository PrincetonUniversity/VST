{
  description = "Dev shell for VST (vst_on_iris branch). System deps via Nix; Rocq, CompCert, Flocq, zlist, Iris, and vst-ora via opam in a project-local switch.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        # The .opam file used to drive `opam install --deps-only`.
        opamFile = "builddep/coq-vst-on-iris-builddep.opam";

        # Compiler versions chosen by opam for the local switch. Rocq 9.1.1 is
        # the newest stable release explicitly supported by this checkout.
        ocamlVersion = "4.14.2";
        rocqVersion = "9.1.1";
      in {
        # `coq-flocq`'s opam package pulls in `conf-clang` and then actually
        # invokes `clang` from its ./configure. Make clang the sole toolchain
        # via clangStdenv — mixing gcc and clang in the same shell causes
        # gcc's libstdc++ include path to win NIX_CFLAGS_COMPILE while clang's
        # glibc-path setup doesn't apply, breaking `#include_next <stdlib.h>`.
        devShells.default = (pkgs.mkShell.override { stdenv = pkgs.clangStdenv; }) {
          # Tools opam itself + the OCaml compiler build need on PATH.
          # We deliberately do NOT pull `ocaml` from Nixpkgs — opam manages the
          # compiler inside the local switch so versions are reproducible w.r.t.
          # the Coq ecosystem rather than Nixpkgs' OCaml.
          # NOTE: no gcc/clang here — clangStdenv (above) supplies the C/C++
          # toolchain (and the `cc`/`c++` aliases) for the shell.
          packages = with pkgs; [
            opam
            gnumake
            binutils
            m4
            unzip
            bzip2
            gzip
            patch
            rsync
            git
            curl
            wget
            pkg-config
            perl
            which
            gmp          # conf-gmp / zarith
            mpfr         # used by some flocq-adjacent packages
            ncurses      # readline-ish bits for coqtop
            zlib
            linuxHeaders # conf-linux-libc-dev probes <linux/limits.h>
            bubblewrap   # opam's sandbox; required for `opam install` on Linux
            cacert       # SSL roots for opam's downloads
          ];

          shellHook = ''
            set -e

            export OPAM_FILE="${opamFile}"
            export OCAML_VERSION="${ocamlVersion}"
            export ROCQ_VERSION="${rocqVersion}"

            # SSL roots for curl/opam downloads.
            export SSL_CERT_FILE="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
            export NIX_SSL_CERT_FILE="$SSL_CERT_FILE"

            # Nix supplies gmp/pkg-config/etc. via $buildInputs; tell opam to
            # trust that depexts are already on PATH instead of shelling out to
            # nix-build for them.
            export OPAMASSUMEDEPEXTS=1
            export OPAMCONFIRMLEVEL=unsafe-yes

            # 1. Initialize opam root if the user has never used opam.
            #    opam 2.2+ defaults to $XDG_DATA_HOME/opam, so don't hard-code ~/.opam;
            #    ask opam where it thinks the root is and check for a config file there.
            OPAM_ROOT_DIR="$(opam var root 2>/dev/null || echo "$HOME/.opam")"
            if [ ! -f "$OPAM_ROOT_DIR/config" ]; then
              echo "[vst-flake] opam root not found at $OPAM_ROOT_DIR; running opam init (one-time)..."
              opam init --bare --disable-sandboxing --no-setup -a -y
            fi

            # 2. Make sure a local switch in ./_opam exists AND is registered with the
            #    current opam root. If ./_opam exists but opam doesn't know about it
            #    (e.g. left over from a previous root), wipe and recreate.
            if ! opam switch list -s 2>/dev/null | grep -Fxq "$PWD"; then
              if [ -d "_opam" ]; then
                echo "[vst-flake] stale ./_opam (not registered with opam root); removing..."
                chmod -R u+w _opam 2>/dev/null || true
                rm -rf _opam
              fi
              echo "[vst-flake] creating local opam switch with OCaml $OCAML_VERSION..."
              opam switch create . "ocaml-base-compiler.$OCAML_VERSION" \
                --no-install -y --no-switch
            fi

            # 3. Activate the local switch.
            eval "$(opam env --switch=. --set-switch)"

            # 3.4. Probe whether the Rocq package repository is reachable at
            #      all before doing anything that would talk to it.
            #
            #      NOTE (2026-08-27): rocq-prover.org has been down -- TCP
            #      connects to it time out from every network we've tried,
            #      not just this machine's -- so hitting it unconditionally
            #      (as this hook used to, via an unconditional `opam
            #      repository set-url` below) makes `nix develop` hang
            #      indefinitely. Everything that needs the repo is now gated
            #      on this probe and skipped (falling back to whatever
            #      ./_opam already has installed) while it's down. This is
            #      self-healing: once the site responds again, the probe
            #      passes and this hook resumes its normal behavior with no
            #      further edits needed here.
            COQ_RELEASED_URL="https://rocq-prover.org/opam/released"
            COQ_RELEASED_REACHABLE=0
            if curl -sS -o /dev/null --connect-timeout 4 -m 6 "$COQ_RELEASED_URL"; then
              COQ_RELEASED_REACHABLE=1
            else
              echo "[vst-flake] WARNING: $COQ_RELEASED_URL is unreachable; skipping opam repo/package refresh and using whatever ./_opam already has installed."
            fi

            if [ "$COQ_RELEASED_REACHABLE" = 1 ]; then
              # 3.5. Ensure coq-released is attached to *this* switch. Done after
              #      activation (rather than via --on-switches=… at create time)
              #      so it's idempotent and survives partial-init failures.
              if ! opam repo list -s | grep -Fxq coq-released; then
                echo "[vst-flake] attaching the Rocq released-package repository..."
                opam repo add coq-released "$COQ_RELEASED_URL"
              else
                CURRENT_COQ_RELEASED_URL="$(opam repo list -a 2>/dev/null | awk '$1=="coq-released"{print $2}')"
                if [ "$CURRENT_COQ_RELEASED_URL" != "$COQ_RELEASED_URL" ]; then
                  opam repository set-url coq-released "$COQ_RELEASED_URL"
                fi
              fi

              # ORA 1.2 was published after older coq-released snapshots. Avoid
              # a network update on every shell entry, but refresh stale caches.
              if ! opam list --all-versions --short rocq-vst-ora 2>/dev/null \
                   | grep -Fxq rocq-vst-ora.1.2; then
                echo "[vst-flake] refreshing coq-released for rocq-vst-ora.1.2..."
                opam update -y coq-released
              fi

              # 4. Install Rocq and the build dependencies described in the
              #    .opam file. Requesting the compatibility package keeps the
              #    coqc/coqtop commands used by VST's Makefiles while installing
              #    the Rocq 9 runtime and Stdlib logical namespace.
              echo "[vst-flake] ensuring Rocq $ROCQ_VERSION..."
              opam install --assume-depexts -y "coq.$ROCQ_VERSION"

              #    `--deps-only` so we don't try to build VST itself via opam.
              #    Run unconditionally — opam is a no-op if everything is present,
              #    and a partial install from a prior failed shell needs catching up.
              echo "[vst-flake] ensuring VST build dependencies from $OPAM_FILE..."
              opam install --deps-only --assume-depexts -y "./$OPAM_FILE"
            elif ! command -v coqc >/dev/null 2>&1; then
              echo "[vst-flake] ERROR: $COQ_RELEASED_URL is unreachable and no Rocq toolchain is installed in ./_opam yet; cannot bootstrap offline." >&2
              exit 1
            fi

            set +e

            # Editor tooling (non-fatal): the language server, built against
            # this switch's Rocq so versions match. Launch VSCode from inside
            # this shell so the VsRocq extension finds `vsrocqtop` on PATH.
            echo "[vst-flake] ensuring Rocq/Coq language servers (vsrocqtop, coq-lsp)..."
            opam install --assume-depexts -y vsrocq-language-server \
              || echo "[vst-flake] WARNING: vsrocq-language-server install failed; VsRocq won't work until resolved."
            # coq-lsp provides petanque, which the rocq MCP server drives.
            opam install --assume-depexts -y coq-lsp \
              || echo "[vst-flake] WARNING: coq-lsp install failed; the rocq MCP server won't work until resolved."

            # Project-local VSCode profile (NO systemwide changes). Instead of
            # installing into the global ~/.vscode extensions dir, we keep an
            # isolated extensions + user-data dir under ./.vscode-dev. Within
            # *this* shell we shadow `code` with a function that binds it to
            # those dirs, so plain `code .` just works; your normal VSCode
            # install (and any `code` outside this shell) stays untouched.
            #
            # The renamed extension is rocq-prover.vsrocq (old: maximedenes.vscoq);
            # only it speaks to `vsrocqtop`.
            export VSCODE_EXT_DIR="$PWD/.vscode-dev/extensions"
            export VSCODE_DATA_DIR="$PWD/.vscode-dev/user-data"
            if command -v code >/dev/null 2>&1; then
              mkdir -p "$VSCODE_EXT_DIR" "$VSCODE_DATA_DIR/User"
              # Seed settings: point VsRocq at *this* switch's server explicitly,
              # so it resolves even if `code` is launched outside this shell.
              if [ ! -f "$VSCODE_DATA_DIR/User/settings.json" ]; then
                printf '{\n  "vsrocq.path": "%s/_opam/bin/vsrocqtop",\n  "coqpilot.coqLspServerPath": "%s/_opam/bin/coq-lsp"\n}\n' "$PWD" "$PWD" \
                  > "$VSCODE_DATA_DIR/User/settings.json"
              fi
              # NB: `command code` bypasses the function below so this (and the
              # function itself) doesn't recurse into the shadowing wrapper.
              if ! command code --extensions-dir "$VSCODE_EXT_DIR" --list-extensions 2>/dev/null \
                   | grep -Fxq rocq-prover.vsrocq; then
                echo "[vst-flake] installing VsRocq into project-local ./.vscode-dev ..."
                command code --extensions-dir "$VSCODE_EXT_DIR" --install-extension rocq-prover.vsrocq \
                  || echo "[vst-flake] WARNING: failed to install rocq-prover.vsrocq locally."
              fi
              if ! command code --extensions-dir "$VSCODE_EXT_DIR" --list-extensions 2>/dev/null \
                   | grep -Fxq openai.chatgpt; then
                echo "[vst-flake] installing Codex into project-local ./.vscode-dev ..."
                command code --extensions-dir "$VSCODE_EXT_DIR" --install-extension openai.chatgpt \
                  || echo "[vst-flake] WARNING: failed to install openai.chatgpt locally."
              fi
              # CoqPilot, from the local fork rather than the marketplace:
              # upstream v2.4.3 cannot talk to coq-lsp >= 0.2.4 (the only
              # versions built for Rocq 9). The fork's rocq9-coq-lsp-0.2.5
              # branch (github.com/mathtician/coqpilot) fixes that. Rebuild
              # the .vsix there after changes with:
              #   npm ci && npx tsc -p ./ && npx @vscode/vsce package
              COQPILOT_VSIX="$(ls -t "$PWD"/../coqpilot/coqpilot-*.vsix 2>/dev/null | head -1)"
              if [ -n "$COQPILOT_VSIX" ]; then
                if ! command code --extensions-dir "$VSCODE_EXT_DIR" --list-extensions 2>/dev/null \
                     | grep -Fxq jetbrains-research.coqpilot; then
                  echo "[vst-flake] installing CoqPilot (local fork) into ./.vscode-dev ..."
                  command code --extensions-dir "$VSCODE_EXT_DIR" --install-extension "$COQPILOT_VSIX" \
                    || echo "[vst-flake] WARNING: failed to install CoqPilot from $COQPILOT_VSIX."
                fi
              else
                echo "[vst-flake] note: no ../coqpilot/coqpilot-*.vsix found; skipping CoqPilot install."
              fi
              # Shadow `code` in this shell so it always uses the isolated
              # profile. `command code` calls the real binary, avoiding recursion.
              code() {
                command code --extensions-dir "$VSCODE_EXT_DIR" \
                             --user-data-dir "$VSCODE_DATA_DIR" "$@"
              }
              export -f code
            else
              echo "[vst-flake] note: 'code' not on PATH; cannot set up the project-local VSCode profile."
            fi
            echo
            echo "[vst-flake] Dev shell ready."
            echo "  switch:  $(opam var switch)"
            echo "  coq:     $(coqc --version 2>/dev/null | head -1)"
            echo "  ocaml:   $(ocaml -version 2>/dev/null)"
            echo "  vsrocq:  $(vsrocqtop --version 2>/dev/null | head -1)"
            echo
            echo "Next:"
            echo "  - build: 'make -j' (VsRocq needs .vo files; it won't compile deps for you)"
            echo "  - edit:  'code .' (in this shell, 'code' is bound to a project-local,"
            echo "           isolated extension profile; your global VSCode is untouched)"
          '';
        };
      });
}
