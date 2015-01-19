Require Import floyd.proofauto.
Require Import mc_reify.bool_funcs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Require Export mc_reify.reify.
Require Export mc_reify.bool_funcs.
Require Import mc_reify.set_reif.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
Require Export MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Export mc_reify.reflexivity_tacs.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.
Require Import mc_reify.typ_eq.


Require Import mc_reify.reverse_defs.
Require Import mc_reify.rtac_base.
Require Import mc_reify.hoist_later_in_pre.
Require Import mc_reify.symexe.
Require Import mc_reify.func_defs.
Require Import mc_reify.denote_tac.


Lemma semax_load_localD:
(*    forall temp var ret gt (* Delta without gs *) id
      (e: type_id_env) gs sh P T1 T2 R Post (e1: Clight.expr) (t t_root: type)
      (efs: list efield) (gfs: list gfield) (tts: list type)
      (p: val) (v : val) (v' : reptype t_root) lr,
  forall {Espec: OracleKind},*)
forall (temp : PTree.t (type * bool)) (var : PTree.t type) 
     (ret : type) (gt : PTree.t type) (id : ident) (t t_root : type) (e0 e1 : Clight.expr)
     (efs : list efield) (tts : list type) 
     (e : type_id_env) (lr : LLRR) (n: nat)
     (gs : PTree.t funspec) (sh : Share.t) 
     (P : list Prop) (T1 : PTree.t val) (T2 : PTree.t (type * val))
     (R : list mpred) (Post : environ -> mpred)
     (gfs : list gfield)
     (p p' v : val) (v' : reptype t_root) 
     (Espec : OracleKind),
  typeof_temp (mk_tycontext temp var ret gt gs) id = Some t -> 
  is_neutral_cast (typeof e0) t = true ->
  msubst_efield_denote T1 T2 efs = Some gfs ->
  legal_nested_efield e t_root e1 gfs tts lr = true ->
  tc_efield_b_norho (mk_tycontext temp var ret gt gs) efs = true ->

  msubst_eval_LR T1 T2 e1 lr = Some p ->
  tc_LR_b_norho (mk_tycontext temp var ret gt gs) e1 lr = true ->
  (@eq (option mpred)) (nth_error R n) (Some (data_at sh t_root v' p')) ->
  (forall rho, 
      !!(tc_environ (mk_tycontext temp var ret gt gs) rho) && (assertD P (localD T1 T2) R rho) |-- !! (p = p')) ->
  proj_val t_root gfs v' = v ->
  assertD P (localD (my_set id v T1) T2) R = Post ->
  nested_efield e1 efs tts = e0 ->

  (forall rho, 
      !! (tc_environ (mk_tycontext temp var ret gt gs) rho) && (assertD P (localD T1 T2) R rho) |--
        !! (tc_val (typeof e0) v) &&

        !! (legal_nested_field t_root gfs)) ->
(*
  (*id = id /\ e = e /\ *)sh = sh /\ P = P /\ T1 = T1 /\
  T2 = T2 /\ R = R /\ Post = Post /\ (*e1 = e1 /\ t = t /\ t_root = t_root /\*)
  (*efs = efs /\*)
  gfs = gfs /\
  (*tts = tts /\*) p = p /\
  v = v /\ v' = v' /\ (*lr = lr /\ *)Espec = Espec ->
*)
 semax (mk_tycontext temp var ret gt gs) (|> assertD P (localD T1 T2) R) 
        (Sset id e0)
          (normal_ret_assert Post)
(* Similar solutions include hiding type Clight.expr in function return type
 like nested_efield_rel. *)
.
Proof.
Admitted.

Definition load_lemma (temp : PTree.t (type * bool)) (var : PTree.t type) 
     (ret : type) (gt : PTree.t type) (id : ident) (t t_root : type) (e0 e1 : Clight.expr)
    (efs: list efield) (tts : list type) (e : type_id_env) (lr : LLRR)
    (n: nat): my_lemma.
reify_lemma reify_vst (semax_load_localD temp var ret gt id t t_root e0 e1 efs tts e lr n).
Defined.

Print load_lemma.

Lemma lower_prop_right: forall (P: mpred) (Q: Prop), Q -> P |-- !! Q.
Proof.
  intros.
  apply prop_right.
  auto.
Qed.

Definition prop_right_lemma: my_lemma.
reify_lemma reify_vst lower_prop_right.
Defined.

Section tbled.

Variable tbl : SymEnv.functions RType_typ.
Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Definition APPLY_load temp var ret gt id t t_root e0 e1 efs tts e lr n :=
EAPPLY typ func (load_lemma temp var ret gt id t t_root e0 e1 efs tts e lr n).

Definition APPLY_prop_right := EAPPLY typ func prop_right_lemma.

Definition remove_global_spec (t : tycontext) := 
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.



End tbled.

Notation "'NOTATION_T1' v" := (PTree.Node PTree.Leaf None
         (PTree.Node PTree.Leaf None
            (PTree.Node
               (PTree.Node PTree.Leaf None
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some v)
                        PTree.Leaf) None PTree.Leaf)) None PTree.Leaf))) (at level 50).

Goal
forall {Espec : OracleKind} (sh:Share.t) (contents : list val) (v: val) ,  
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (NOTATION_T1 v) (PTree.empty (type * val))) 
       [data_at sh t_struct_list (default_val _) (force_ptr v)])
     (Sset _t
            (Efield (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)
              _tail (tptr t_struct_list)))         
     (normal_ret_assert      (assertD [] (localD (NOTATION_T1 v) (PTree.empty (type * val))) 
       [data_at sh t_struct_list (default_val _) (force_ptr v)])
)).
intros.
simpl (remove_global_spec Delta).
(*
intros.
eexists.
(*
Eval compute in (compute_nested_efield (Efield (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)
           _tail (tptr t_struct_list))).*)
eapply (semax_load_localD) with (efs := eStructField _tail :: nil) (tts := tptr t_struct_list :: nil)
  (e := Struct_env) (t_root := t_struct_list) (lr := LLLL)
  (e1 := (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)) (n := 0%nat).
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
+

*)

(*Set Printing Depth 300.*)

reify_expr_tac.

Eval vm_compute in (run_tac 
match (get_arguments e) with
| (Some Delta, Some Pre, Some st) => 
  FORWARD_LOAD tbl Delta Pre st
| _ => FAIL
end e).



(*
Eval vm_compute in (reflect_prop tbl0 load_lemma).
Require Import denote_tac.

Check reflect_prop.
assert (exists v, reflect_prop tbl0 e = Some v).
unfold tbl0, e.
simpl.
cbv_denote.
*)
 