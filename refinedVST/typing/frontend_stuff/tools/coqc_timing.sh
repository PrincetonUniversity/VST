#!/bin/bash

set -e

# Wrapper for coqc that is used when running the perf script in the CI.
# Variable TIMECMD is expected to contain an absolute path to the perf script.
# If TIMECMD is not set (or empty), fallback to just calling coqc.
# we need to use opam exec -- coqc to get the coqc installed by opam, not this script
# If PROFILE is set, generate a profile in the $PROFILE file (relative to the root of the repo).

# This file is in "_build/default/tools"
REPO_DIR="$(dirname $(readlink -f $0))/../../../"

PROFILE_ARG=()
if [[ ! -z "$PROFILE" ]]; then
    PROFILE_ARG=("-profile" "$REPO_DIR/$PROFILE")
fi

opam exec -- ${TIMECMD} coqc "${PROFILE_ARG[@]}" "$@"
