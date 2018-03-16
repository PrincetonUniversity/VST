(** Heavily annotated for a tutorial introduction. *)

(** First, import the entire Floyd proof automation system, which includes
 ** the VeriC program logic and the MSL theory of separation logic**)
Require Import VST.floyd.proofauto.

(** Import the [reverse.v] file, which is produced by CompCert's clightgen
 ** from reverse.c.   The file reverse.v defines abbreviations for identifiers
 ** (variable names, etc.) of the C program, such as _head, _reverse.
 ** It also defines "prog", which is the entire abstract syntax tree
 ** of the C program *)
Require Import VST.progs.reverse.

(* The C programming language has a special namespace for struct
** and union identifiers, e.g., "struct foo {...}".  Some type-based operators
** in the program logic need access to an interpretation of this namespace,
** i.e., the meaning of each struct-identifier such as "foo".  The next
** line (which looks identical for any program) builds this
** interpretation, called "CompSpecs" *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(** Calculate the "types-of-global-variables" specification
 ** directly from the program *)
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** A convenience definition *)
Definition t_struct_list := Tstruct _list noattr.

(** Inductive definition of linked lists *)
Fixpoint listrep (sigma: list val) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (h,y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Fixpoint lsegrec (sigma: list val) (x z: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (h,y) x  *  lsegrec hs y z
 | nil => 
    !! (x = z) && emp
 end.

(* This file is only to demonstrate object language induction. *)

(* induction rule *)

Lemma list_ind_in_logc: forall {A: Type} (P: mpred) (Q: list A -> mpred),
  P |-- Q nil ->
  P |-- ALL a: A, (ALL l: list A, Q l --> Q (a :: l)) ->
  P |-- ALL l: list A, Q l.
Proof.
  intros.
  apply allp_right; intro l.
  induction l; auto.
  rewrite (add_andp _ _ IHl), (add_andp _ _ H0).
  apply imp_andp_adjoint.
  apply andp_left2.
  apply (allp_left _ a).
  apply (allp_left _ l).
  auto.
Qed.

(* application *)

Lemma listrep2lsegrec: forall l x,
  listrep l x |-- lsegrec l x nullval.
Proof.
  assert (emp |-- ALL l: list val, (ALL x: val, listrep l x -* lsegrec l x nullval)).
  + apply list_ind_in_logc.
    - apply allp_right; intros.
      apply wand_sepcon_adjoint.
      rewrite emp_sepcon.
      simpl.
      apply derives_refl.
    - apply allp_right; intros a.
      apply allp_right; intros l.
      apply imp_andp_adjoint.
      apply allp_right; intros x.
      apply andp_left2.
      apply wand_sepcon_adjoint.
      simpl.
      Intros y.
      Exists y.
      apply wand_sepcon_adjoint.
      apply (allp_left _ y).
      apply wand_sepcon_adjoint.
      cancel.
      apply wand_sepcon_adjoint.
      apply derives_refl.
  + intros.
    rewrite <- (emp_sepcon (listrep _ _)).
    apply wand_sepcon_adjoint.
    eapply derives_trans; [exact H | clear H].
    apply (allp_left _ l).
    apply (allp_left _ x).
    apply derives_refl.
Qed.
