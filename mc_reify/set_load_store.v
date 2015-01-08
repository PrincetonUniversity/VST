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
Require Import mc_reify.get_set_reif.
Require Import mc_reify.func_defs.

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).

Lemma semax_load_localD:
(*    forall temp var ret gt (* Delta without gs *) id
      (e: type_id_env) gs sh P T1 T2 R Post (e1: Clight.expr) (t t_root: type)
      (efs: list efield) (gfs: list gfield) (tts: list type)
      (p: val) (v : val) (v' : reptype t_root) lr,
  forall {Espec: OracleKind},*)
forall (temp : PTree.t (type * bool)) (var : PTree.t type) 
     (ret : type) (gt : PTree.t type) (id : ident) (t t_root : type) (e0 e1 : Clight.expr)
     (efs : list efield) (tts : list type) 
     (e : type_id_env) (lr : LLRR) 
     (gs : PTree.t funspec) (sh : Share.t) 
     (P : list Prop) (T1 : PTree.t val) (T2 : PTree.t (type * val))
     (R : list mpred) (Post : environ -> mpred)
     (gfs : list gfield)
     (p v : val) (v' : reptype t_root) 
     (Espec : OracleKind),
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
    (efs: list efield) (tts : list type) (e : type_id_env) (lr : LLRR): my_lemma.
reify_lemma reify_vst (semax_load_localD temp var ret gt id t t_root e0 e1 efs tts e lr).
Defined.

Print load_lemma.

Require Import mc_reify.reverse_defs.
Require Import symexe.
Require Import mc_reify.func_defs.
Require Import mc_reify.denote_tac.

Section tbled.

Variable tbl : SymEnv.functions RType_typ.
Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.


Definition APPLY_load temp var ret gt id t t_root e0 e1 efs tts e lr :=
EAPPLY typ func (load_lemma temp var ret gt id t t_root e0 e1 efs tts e lr).

Definition remove_global_spec (t : tycontext) := 
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.

Notation "'T1' v" := (PTree.Node PTree.Leaf None
         (PTree.Node PTree.Leaf None
            (PTree.Node
               (PTree.Node PTree.Leaf None
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some v)
                        PTree.Leaf) None PTree.Leaf)) None PTree.Leaf))) (at level 50).

Goal
forall {Espec : OracleKind} (contents : list val) (v: val) , exists (PO : environ -> mpred), 
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (|> assertD [] (localD (T1 v) (PTree.empty (type * val))) [])
     (Sset _t
            (Efield (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)
              _tail (tptr t_struct_list)))         
     (normal_ret_assert PO)).
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
  (e1 := (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)).
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.

unfold tc_LR_b_norho, tc_lvalue_b_norho.
simpl typecheck_lvalue.
Print denote_tc_assert_b_norho.
unfold tc_lvalue_b_norho, tc_LR_b_norho.
*)
(*
intros.
reify_vst (PTree.empty (type * val)).

Definition TT1 := App
         (App
            (App (Inj (inr (Data (fnode tyval))))
               (Inj (inr (Data (fleaf tyval)))))
            (Inj (inr (Other (fnone tyval)))))
         (App
            (App
               (App (Inj (inr (Data (fnode tyval))))
                  (Inj (inr (Data (fleaf tyval)))))
               (Inj (inr (Other (fnone tyval)))))
            (App
               (App
                  (App (Inj (inr (Data (fnode tyval))))
                     (App
                        (App
                           (App (Inj (inr (Data (fnode tyval))))
                              (Inj (inr (Data (fleaf tyval)))))
                           (Inj (inr (Other (fnone tyval)))))
                        (App
                           (App
                              (App (Inj (inr (Data (fnode tyval))))
                                 (App
                                    (App
                                       (App (Inj (inr (Data (fnode tyval))))
                                          (Inj (inr (Data (fleaf tyval)))))
                                       (App (Inj (inr (Other (fsome tyval))))
                                          (Ext 1%positive)))
                                    (Inj (inr (Data (fleaf tyval))))))
                              (Inj (inr (Other (fnone tyval)))))
                           (Inj (inr (Data (fleaf tyval)))))))
                  (Inj (inr (Other (fnone tyval)))))
               (Inj (inr (Data (fleaf tyval)))))).

Definition TT2 :=  Inj (inr (Data (fempty (typrod tyc_type tyval)))) : expr typ func.

Eval compute in (rmsubst_eval_LR TT1 TT2 (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list) LLLL).
*)
reify_expr_tac.

Eval vm_compute in
(match (get_delta_statement e) with
| Some ((t, v, r, gt) , st) => 
  match st with
  | Sset i e0 => 
     let ty := match t ! i with
               | Some (ty, _) => ty
               | None => Tvoid
               end in
     let tmp := compute_nested_efield e0 in
     let e1 := (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list) in
     let efs := snd (fst tmp) in
     let tts := snd tmp in
     run_tac (THEN INTROS (THEN (APPLY_load t v r gt i ty t_struct_list e0 e1 efs tts Struct_env LLLL) (TRY (FIRST [(REFLEXIVITY_OP_CTYPE tbl0); (REFLEXIVITY_BOOL tbl0); (REFLEXIVITY_CEXPR tbl0); (REFLEXIVITY); REFLEXIVITY_MSUBST]))))
  | _ => run_tac FAIL
  end
| _ => run_tac FAIL
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
