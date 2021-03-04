Require Import VST.veric.juicy_extspec.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.Funspec_old_Notation.

Section specs.

Definition mmap_spec {CS : compspecs} :=
  WITH len : Z
  PRE [ 1%positive OF tptr tvoid, 2%positive OF tuint, 3%positive OF tint, 4%positive OF tint,
          5%positive OF tint, 6%positive OF tint ]
    PROP (0 <= len <= Ptrofs.max_unsigned)
    LOCAL (temp 1%positive nullval; temp 2%positive (Vint (Int.repr len));
               temp 3%positive (Vint (Int.repr 6)); temp 4%positive (Vint (Int.repr 32)) (* anonymous *);
               temp 5%positive (Vint (Int.repr (-1))); temp 6%positive (Vint (Int.repr 0)))
    SEP ()
  POST [ tint ]
   EX p : val,
    PROP ()
    LOCAL (temp ret_temp p)
    SEP (data_at_ Tsh (tarray tuchar len) p).

Definition mmap_specs {CS : compspecs} (ext_link : string -> ident) :=
  [(ext_link "mmap"%string, mmap_spec)].

Definition mmap_Espec {CS : compspecs} (ext_link : string -> ident) : OracleKind :=
  add_funspecs (ok_void_spec unit) ext_link (mmap_specs ext_link).

End specs.
