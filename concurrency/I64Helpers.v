Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Errors.
Require Import compcert.common.Globalenvs.
(*Require Import Cminor.*)
Require Import compcert.x86.Op.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.reach.
Require Import VST.msl.Axioms.
Require Import VST.sepcomp.globalSep.
Import String.

  (** * Axiomatization of the helper functions *)

Section HELPERS.

Context {F V: Type} (ge: Genv.t (AST.fundef F) V).

(*LENB: These are from CompCert2.6/backend/SelectLong.vp.
  Compcert2.1 / compcomp had additional helpers*)
Record helper_functions : Type := mk_helper_functions {
  i64_dtos: ident;                      (**r float64 -> signed long *)
  i64_dtou: ident;                      (**r float64 -> unsigned long *)
  i64_stod: ident;                      (**r signed long -> float64 *)
  i64_utod: ident;                      (**r unsigned long -> float64 *)
  i64_stof: ident;                      (**r signed long -> float32 *)
  i64_utof: ident;                      (**r unsigned long -> float32 *)
  i64_sdiv: ident;                      (**r signed division *)
  i64_udiv: ident;                      (**r unsigned division *)
  i64_smod: ident;                      (**r signed remainder *)
  i64_umod: ident;                      (**r unsigned remainder *)
  i64_shl: ident;                       (**r shift left *)
  i64_shr: ident;                       (**r shift right unsigned *)
  i64_sar: ident                        (**r shift right signed *)
}.

Variable hf: helper_functions.

Definition hf_names: list ident := hf.(i64_dtos)::hf.(i64_dtou) ::
  hf.(i64_stod) :: hf.(i64_utod) :: hf.(i64_stof) ::
  hf.(i64_utof) :: hf.(i64_sdiv) :: hf.(i64_udiv) ::
  hf.(i64_smod) :: hf.(i64_umod) ::
  hf.(i64_shl) :: hf.(i64_shr) :: hf.(i64_sar) :: nil.

End HELPERS.


Definition sig_l_l := mksignature (Tlong :: nil) (Some Tlong) cc_default.
Definition sig_l_f := mksignature (Tlong :: nil) (Some Tfloat) cc_default.
Definition sig_l_s := mksignature (Tlong :: nil) (Some Tsingle) cc_default.
Definition sig_f_l := mksignature (Tfloat :: nil) (Some Tlong) cc_default.
Definition sig_ll_l := mksignature (Tlong :: Tlong :: nil) (Some Tlong) cc_default.
Definition sig_li_l := mksignature (Tlong :: Tint :: nil) (Some Tlong) cc_default.
Definition sig_ii_l := mksignature (Tint :: Tint :: nil) (Some Tlong) cc_default.


(** Setting up the helper functions *)
(*Require Import ccc26x86.Cminor. (*LENB: Imported for globdef - should we really use Cminor globdefs, though?*)
Definition globdef := AST.globdef Cminor.fundef unit.

Definition globdef_of_interest (gd: globdef) : bool :=
  match gd with
  | Gfun (External (EF_external name sg)) => String.prefix "__i64_" name
  | _ => false
  end.

Definition record_globdef (globs: PTree.t globdef) (id_gd: ident * globdef) :=
  let (id, gd) := id_gd in
  if globdef_of_interest gd
  then PTree.set id gd globs
  else PTree.remove id globs.

Definition record_globdefs (p: Cminor.program) : PTree.t globdef :=
  List.fold_left record_globdef p.(prog_defs) (PTree.empty _).

Definition lookup_helper_aux
     (name: String.string) (sg: signature) (res: option ident)
     (id: ident) (gd: globdef) :=
  match gd with
  | Gfun (External (EF_external name' sg')) =>
      if String.string_dec name name' && signature_eq sg sg'
      then Some id
      else res
  | _ => res
  end.

Definition lookup_helper (globs: PTree.t globdef)
                         (name: String.string) (sg: signature) : res ident :=
  match PTree.fold (lookup_helper_aux name sg) globs None with
  | Some id => OK id
  | None    => Error (MSG name :: MSG ": missing or incorrect declaration" :: nil)
  end.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Definition get_helpers (p: Cminor.program) : res helper_functions :=
  let globs := record_globdefs p in
  do i64_dtos <- lookup_helper globs "__i64_dtos" sig_f_l ;
  do i64_dtou <- lookup_helper globs "__i64_dtou" sig_f_l ;
  do i64_stod <- lookup_helper globs "__i64_stod" sig_l_f ;
  do i64_utod <- lookup_helper globs "__i64_utod" sig_l_f ;
  do i64_stof <- lookup_helper globs "__i64_stof" sig_l_s ;
  do i64_utof <- lookup_helper globs "__i64_utof" sig_l_s ;
  do i64_sdiv <- lookup_helper globs "__i64_sdiv" sig_ll_l ;
  do i64_udiv <- lookup_helper globs "__i64_udiv" sig_ll_l ;
  do i64_smod <- lookup_helper globs "__i64_smod" sig_ll_l ;
  do i64_umod <- lookup_helper globs "__i64_umod" sig_ll_l ;
  do i64_shl <- lookup_helper globs "__i64_shl" sig_li_l ;
  do i64_shr <- lookup_helper globs "__i64_shr" sig_li_l ;
  do i64_sar <- lookup_helper globs "__i64_sar" sig_li_l ;
  OK (mk_helper_functions
     i64_dtos i64_dtou i64_stod i64_utod i64_stof i64_utof
     i64_sdiv i64_udiv i64_smod i64_umod
     i64_shl i64_shr i64_sar).*)


Inductive is_I64_helper hf : ident -> signature -> Prop :=
  ef_dtos: is_I64_helper hf hf.(i64_dtos) sig_f_l
| ef_dtou: is_I64_helper hf hf.(i64_dtou) sig_f_l
| ef_stod: is_I64_helper hf hf.(i64_stod) sig_l_f
| ef_utod: is_I64_helper hf hf.(i64_utod) sig_l_f
| ef_stof: is_I64_helper hf hf.(i64_stof) sig_l_s
| ef_utof: is_I64_helper hf hf.(i64_utof) sig_l_s
| ef_sdiv: is_I64_helper hf hf.(i64_sdiv) sig_ll_l
| ef_udiv: is_I64_helper hf hf.(i64_udiv) sig_ll_l
| ef_smod: is_I64_helper hf hf.(i64_smod) sig_ll_l
| ef_umod: is_I64_helper hf hf.(i64_umod) sig_ll_l
| ef_shl: is_I64_helper hf hf.(i64_shl) sig_li_l
| ef_shr: is_I64_helper hf hf.(i64_shr) sig_li_l
| ef_sarf: is_I64_helper hf hf.(i64_sar) sig_li_l.

Lemma is_I64_helper_dec hf name sg:
 {is_I64_helper hf name sg} + {~is_I64_helper hf name sg} .
Proof.
destruct (signature_eq sg sig_f_l); subst.
  destruct (ident_eq name hf.(i64_dtos)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_dtou)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition.
destruct (signature_eq sg sig_l_f); subst.
  destruct (ident_eq name hf.(i64_stod)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_utod)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition.
destruct (signature_eq sg sig_l_s); subst.
  destruct (ident_eq name hf.(i64_stof)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_utof)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition.
destruct (signature_eq sg sig_ll_l); subst.
  destruct (ident_eq name hf.(i64_sdiv)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_udiv)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_smod)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_umod)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition.
destruct (signature_eq sg sig_li_l); subst.
  destruct (ident_eq name hf.(i64_shl)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_shr)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_sar)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition.
right; intros N. inv N; intuition.
Qed.

Inductive is_I64_helperS : String.string -> signature -> Prop :=
  ef_dtosS: is_I64_helperS "__i64_dtos" sig_f_l
| ef_dtouS: is_I64_helperS "__i64_dtou" sig_f_l
| ef_stodS: is_I64_helperS "__i64_stod" sig_l_f
| ef_utodS: is_I64_helperS "__i64_utod" sig_l_f
| ef_stofS: is_I64_helperS "__i64_stof" sig_l_s
| ef_utofS: is_I64_helperS "__i64_utof" sig_l_s
| ef_sdivS: is_I64_helperS "__i64_sdiv" sig_ll_l
| ef_udivS: is_I64_helperS "__i64_udiv" sig_ll_l
| ef_smodS: is_I64_helperS "__i64_smod" sig_ll_l
| ef_umodS: is_I64_helperS "__i64_umod" sig_ll_l
| ef_shlS: is_I64_helperS "__i64_shl" sig_li_l
| ef_shrS: is_I64_helperS "__i64_shr" sig_li_l
| ef_sarfS: is_I64_helperS "__i64_sar" sig_li_l.

Lemma is_I64_helperS_dec name sg:
 {is_I64_helperS name sg} + {~is_I64_helperS name sg} .
Proof.
destruct (signature_eq sg sig_f_l); subst.
{ destruct (String.string_dec name "__i64_dtos").
  + subst; try solve[left; constructor].
  + destruct (String.string_dec name "__i64_dtou").
    - subst; try solve[left; constructor].
    - right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_l_f); subst.
{ destruct (String.string_dec name "__i64_stod").
  + subst; try solve[left; constructor].
  + destruct (String.string_dec name "__i64_utod").
    - subst; try solve[left; constructor].
    - right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_l_s); subst.
{ destruct (String.string_dec name "__i64_stof").
  + subst; try solve[left; constructor].
  + destruct (String.string_dec name "__i64_utof").
    - subst; try solve[left; constructor].
    - right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_ll_l); subst.
{ destruct (String.string_dec name "__i64_sdiv").
  + subst; try solve[left; constructor].
  + destruct (String.string_dec name "__i64_udiv").
    - subst; try solve[left; constructor].
    - destruct (String.string_dec name "__i64_smod").
      * subst; try solve[left; constructor].
      * destruct (String.string_dec name "__i64_umod").
        subst; try solve[left; constructor].
        right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_li_l); subst.
{ destruct (String.string_dec name "__i64_shl").
  + subst; try solve[left; constructor].
  + destruct (String.string_dec name "__i64_shr").
    - subst; try solve[left; constructor].
    - destruct (String.string_dec name "__i64_sar").
      * subst; try solve[left; constructor].
      * right; intros N; inv N; intuition. }
right; intros N. inv N; intuition.
Qed.

Inductive is_I64_helperSI hf : ident -> String.string -> signature -> Prop :=
  ef_dtosSI: is_I64_helperSI hf hf.(i64_dtos) "__i64_dtos" sig_f_l
| ef_dtouSI: is_I64_helperSI hf hf.(i64_dtou) "__i64_dtou" sig_f_l
| ef_stodSI: is_I64_helperSI hf hf.(i64_stod) "__i64_stod" sig_l_f
| ef_utodSI: is_I64_helperSI hf hf.(i64_utod) "__i64_utod" sig_l_f
| ef_stofSI: is_I64_helperSI hf hf.(i64_stof) "__i64_stof" sig_l_s
| ef_utofSI: is_I64_helperSI hf hf.(i64_utof) "__i64_utof" sig_l_s
| ef_sdivSI: is_I64_helperSI hf hf.(i64_sdiv) "__i64_sdiv" sig_ll_l
| ef_udivSI: is_I64_helperSI hf hf.(i64_udiv) "__i64_udiv" sig_ll_l
| ef_smodSI: is_I64_helperSI hf hf.(i64_smod) "__i64_smod" sig_ll_l
| ef_umodSI: is_I64_helperSI hf hf.(i64_umod) "__i64_umod" sig_ll_l
| ef_shlSI: is_I64_helperSI hf hf.(i64_shl) "__i64_shl" sig_li_l
| ef_shrSI: is_I64_helperSI hf hf.(i64_shr) "__i64_shr" sig_li_l
| ef_sarfSI: is_I64_helperSI hf hf.(i64_sar) "__i64_sar" sig_li_l.

Lemma is_I64_helperSI_dec hf name ide sg:
 {is_I64_helperSI hf ide name sg} + {~is_I64_helperSI hf ide name sg} .
Proof.
destruct (signature_eq sg sig_f_l); subst.
{ destruct (String.string_dec name "__i64_dtos").
  + destruct (ident_eq ide hf.(i64_dtos)); subst; try solve[left; constructor].
    right; intros N; inv N; intuition.
  + destruct (String.string_dec name "__i64_dtou").
    - destruct (ident_eq ide hf.(i64_dtou)); subst; try solve[left; constructor].
      right; intros N; inv N; intuition.
    - right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_l_f); subst.
{ destruct (String.string_dec name "__i64_stod").
  + destruct (ident_eq ide hf.(i64_stod)); subst; try solve[left; constructor].
    right; intros N; inv N; intuition.
  + destruct (String.string_dec name "__i64_utod").
    - destruct (ident_eq ide hf.(i64_utod)); subst; try solve[left; constructor].
      right; intros N; inv N; intuition.
    - right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_l_s); subst.
{ destruct (String.string_dec name "__i64_stof").
  + destruct (ident_eq ide hf.(i64_stof)); subst; try solve[left; constructor].
    right; intros N; inv N; intuition.
  + destruct (String.string_dec name "__i64_utof").
    - destruct (ident_eq ide hf.(i64_utof)); subst; try solve[left; constructor].
      right; intros N; inv N; intuition.
    - right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_ll_l); subst.
{ destruct (String.string_dec name "__i64_sdiv").
  + destruct (ident_eq ide hf.(i64_sdiv)); subst; try solve[left; constructor].
    right; intros N; inv N; intuition.
  + destruct (String.string_dec name "__i64_udiv").
    - destruct (ident_eq ide hf.(i64_udiv)); subst; try solve[left; constructor].
      right; intros N; inv N; intuition.
    - destruct (String.string_dec name "__i64_smod").
      * destruct (ident_eq ide hf.(i64_smod)); subst; try solve[left; constructor].
        right; intros N; inv N; intuition.
      * destruct (String.string_dec name "__i64_umod").
        { destruct (ident_eq ide hf.(i64_umod)); subst; try solve[left; constructor].
          right; intros N; inv N; intuition. }
        right; intros N; inv N; intuition. }
destruct (signature_eq sg sig_li_l); subst.
{ destruct (String.string_dec name "__i64_shl").
  + destruct (ident_eq ide hf.(i64_shl)); subst; try solve[left; constructor].
    right; intros N; inv N; intuition.
  + destruct (String.string_dec name "__i64_shr").
    - destruct (ident_eq ide hf.(i64_shr)); subst; try solve[left; constructor].
      right; intros N; inv N; intuition.
    - destruct (String.string_dec name "__i64_sar").
      * destruct (ident_eq ide hf.(i64_sar)); subst; try solve[left; constructor].
        right; intros N; inv N; intuition.
      * right; intros N; inv N; intuition. }
right; intros N. inv N; intuition.
Qed.
