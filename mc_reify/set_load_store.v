Require Import floyd.proofauto. 
Require Import mc_reify.bool_funcs.
Require Import Coq.Logic.JMeq.
Local Open Scope logic.

Lemma semax_set_localD:
  forall {Espec: OracleKind},
    forall temp var ret gt gs (* Delta *)
      id P T1 T2 R Post (e: Clight.expr) ty v,
      match PTree.get id temp with | Some (ty0, _) => Some ty0 | None => None end = Some ty ->
      is_neutral_cast (implicit_deref (typeof e)) ty = true ->
      msubst_eval_expr T1 T2 e = Some v ->
      tc_expr_b_norho (mk_tycontext temp var ret gt gs) e = true ->
      assertD P (localD (PTree.set id v T1) T2) R = Post ->
      semax (mk_tycontext temp var ret gt gs) (|> (assertD P (localD T1 T2) R))
        (Sset id e)
          (normal_ret_assert Post).
Proof.
  intros.
  subst Post.
  eapply semax_PTree_set; eauto.
  intro rho.
  apply tc_expr_b_sound with (rho := rho) in H2.
  normalize.
Qed.

Require Export mc_reify.reify.
Import floyd.proofauto.
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

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).

Lemma semax_load_localD:
(*    forall temp var ret gt (* Delta without gs *) id
      (e: type_id_env) gs sh P T1 T2 R Post (e1: Clight.expr) (t t_root: type)
      (efs: list efield) (gfs: list gfield) (tts: list type)
      (p: val) (v : val) (v' : reptype t_root) lr,
  forall {Espec: OracleKind},*)

forall (temp : PTree.t (type * bool)) (var : PTree.t type) 
     (ret : type) (gt : PTree.t type) (id : ident) (t t_root : type) (e0 e1 : Clight.expr)
     (e : type_id_env) (gs : PTree.t funspec) (sh : Share.t) 
     (P : list Prop) (T1 : PTree.t val) (T2 : PTree.t (type * val))
     (R : list mpred) (Post : environ -> mpred)
     (efs : list efield) (gfs : list gfield)
     (tts : list type) (p v : val) (v' : reptype t_root) 
     (lr : LLRR) (Espec : OracleKind),
  typeof_temp (mk_tycontext temp var ret gt gs) id = Some t -> 
  is_neutral_cast (typeof e0) t = true ->
  msubst_efield_denote T1 T2 efs = Some gfs ->
  legal_nested_efield e t_root e1 gfs tts lr = true ->
  tc_efield_b_norho (mk_tycontext temp var ret gt gs) efs = true ->

  msubst_eval_LR T1 T2 e1 lr = Some p ->
  tc_LR_b_norho (mk_tycontext temp var ret gt gs) e1 lr = true ->
  (forall rho, 
      !!(tc_environ (mk_tycontext temp var ret gt gs) rho) && (assertD P (localD T1 T2) R rho) |--
        (data_at sh t_root v' p) * TT) ->
  proj_val t_root gfs v' = v ->
  assertD P (localD (my_set id v T1) T2) R = Post ->
  nested_efield_rel e1 efs tts e0 ->

  (forall rho, 
      !! (tc_environ (mk_tycontext temp var ret gt gs) rho) && (assertD P (localD T1 T2) R rho) |--
        !! (tc_val (typeof e0) v) &&

        !! (legal_nested_field t_root gfs)) ->
(*
  id = id /\ e = e /\ sh = sh /\ P = P /\ T1 = T1 /\
  T2 = T2 /\ R = R /\ Post = Post /\ e1 = e1 /\ t = t /\ t_root = t_root /\
  efs = efs /\
  gfs = gfs /\
  tts = tts /\ p = p /\
  v = v /\ v' = v' /\ lr = lr /\ Espec = Espec
/\*)
 semax (mk_tycontext temp var ret gt gs) (|> assertD P (localD T1 T2) R) 
        (Sset id e0)
          (normal_ret_assert Post)
(* Similar solutions include hiding type Clight.expr in function return type
 like nested_efield_rel. *)
.
Proof.
Admitted.

Definition load_lemma (temp : PTree.t (type * bool)) (var : PTree.t type) 
     (ret : type) (gt : PTree.t type) (id : ident) (t t_root : type) (e0 e1 : Clight.expr): my_lemma.
reify_lemma reify_vst (semax_load_localD temp var ret gt id t t_root e0 e1).
Defined.

Require Import mc_reify.reverse_defs.
Require Import symexe.
Require Import mc_reify.func_defs.

Section tbled.
Locate RSym_sym.
Parameter tbl : SymEnv.functions RType_typ.
Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Definition APPLY_load temp var ret gt id t t_root e0 e1:=
EAPPLY typ func (load_lemma temp var ret gt id t t_root e0 e1).

Definition remove_global_spec (t : tycontext) := 
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.

Goal
forall {Espec : OracleKind} (contents : list val) , exists (PO : environ -> mpred), 
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (|> assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))         
     (normal_ret_assert PO)).
intros.
simpl (remove_global_spec Delta).

reify_expr_tac.

Eval vm_compute in (get_delta_statement e).
Eval vm_compute in
match (get_delta_statement e) with
| Some ((t, v, r, gt) , st) => 
  match st with
  | Sset i e0 => 
     let ty := match t ! i with
               | Some (ty, _) => ty
               | None => Tvoid
               end in
     run_tac (THEN INTROS (THEN (APPLY_load t v r gt _p ty tint e0 e0) (TRY (FIRST [(REFLEXIVITY_OP_CTYPE tbl0); (REFLEXIVITY_BOOL tbl0)]))))
  | _ => run_tac FAIL
  end
| _ => run_tac FAIL
end e.

Print load_lemma.
(*
Eval vm_compute in (reflect_prop tbl0 load_lemma).
Require Import denote_tac.

Check reflect_prop.
assert (exists v, reflect_prop tbl0 e = Some v).
unfold tbl0, e.
simpl.
cbv_denote.
*)