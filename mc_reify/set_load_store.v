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

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).
Check nth_error.
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

Definition get_arguments_delta (e : expr typ func) :=
  match e with
  | App (Inj (inr (Smx (ftycontext t v r gt)))) gf => Some (t, v, r, gt, gf)
  | _ => None
  end.

Definition get_arguments_pre (e : expr typ func) :=
  match e with
  | App (Inj (inr (Smx flater)))
      (App (App (App (Inj (inr (Smx fassertD))) P)
        (App (App (Inj (inr (Smx flocalD))) T1) T2)) R) => Some (P, T1, T2, R)
  | _ => None
  end.

Definition get_arguments_statement (e : expr typ func) :=
  match e with
  | Inj (inr (Smx (fstatement s))) => Some s
  | _ => None
  end.

Fixpoint get_arguments (e : expr typ func) :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) Delta) Pre) CCmd) _ =>
  (get_arguments_delta Delta,
   get_arguments_pre Pre,
   get_arguments_statement CCmd)
| App _ e 
| Abs _ e => get_arguments e
| _ => (None, None, None)
end.

Instance RSym_SymEnv_fun : RSym SymEnv.func := {
  typeof_sym := fun _ => None;
  symD := fun _ => tt;
  sym_eqb := fun x y => Some (Pos.eqb x y)
}.

Instance RSymOk_SymEnv_fun : RSymOk RSym_SymEnv_fun.
split.
intros.
simpl.
pose proof Pos.eqb_eq a b.
destruct (a =? b)%positive; intros.
+ apply H; auto.
+ intro.
  apply H in H0.
  congruence.
Defined.

Definition sem_eqb_func := @sym_eqb _ _ _ (SymSum.RSym_sum
  (SymSum.RSym_sum (SymSum.RSym_sum RSym_SymEnv_fun RSym_ilfunc) RSym_bilfunc)
  RSym_Func').

Fixpoint expr_beq (e1 e2: expr typ func) : bool :=
  match e1, e2 with
  | Var i1, Var i2 => beq_nat i1 i2
  | Inj f1, Inj f2 =>
    match sem_eqb_func f1 f2 with
    | Some true => true
    | _ => false
    end
  | App e11 e12, App e21 e22 => andb (expr_beq e11 e21) (expr_beq e12 e22)
  | Abs ty1 e11, Abs ty2 e21 => andb (expr_beq e11 e21) (typ_beq ty1 ty2)
  | UVar i1, UVar i2 => beq_nat i1 i2
  | _, _ => false
  end.

Fixpoint nth_solver_rec (R: expr typ func) (p: expr typ func) (n: nat) :=
match R with
| Inj (inr (Data (fnil tympred))) => None
| App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
  match hd with
  | App (App (App (Inj (inr (Sep (fdata_at t_root)))) sh) v) p' =>
      if (expr_beq p p')
      then Some (t_root, n)
      else nth_solver_rec tl p (S n)
  | _ => nth_solver_rec tl p (S n)
  end
| _ => None
end.

Definition nth_solver R p := nth_solver_rec R p 0.
(*
Definition compute_load_arg (arg: 
         (PTree.t (type * bool) * PTree.t type * type * PTree.t type *
          expr typ func) *
       (expr typ func * expr typ func * expr typ func * expr typ func) *
       statement) :=
  match arg with
  | ((t, v, r, gt, gf), (P, T1, T2, R), s) =>
    match s with
    | Sset i e0 =>
      match t ! i, compute_nested_efield e0 with
      | Some (ty, _), (e1, efs, tts) =>
        let lr := compute_lr e1 efs in
        let p := rmsubst_eval_LR T1 T2 e1 lr in
        Some (R, p)
      | _, _ => None
      end
    | _ => None
    end
  end.
*)
Definition compute_load_arg (arg: 
         (PTree.t (type * bool) * PTree.t type * type * PTree.t type *
          expr typ func) *
       (expr typ func * expr typ func * expr typ func * expr typ func) *
       statement) :=
  match arg with
  | ((t, v, r, gt, gf), (P, T1, T2, R), s) =>
    match s with
    | Sset i e0 =>
      match t ! i, compute_nested_efield e0 with
      | Some (ty, _), (e1, efs, tts) =>
        let lr := compute_lr e1 efs in
        match rmsubst_eval_LR T1 T2 e1 lr with
        | App (Inj (inr (Other (fsome tyval)))) p =>
          match nth_solver R p with
          | Some (t_root, n) =>
              Some (t, v, r, gt, i, ty, t_root, e0, e1, efs, tts, lr, n)
          | _ => None
          end
        | _ => None
        end
      | _, _ => None
      end
    | _ => None
    end
  end.

Require Import mc_reify.reverse_defs.
Require Import symexe.
Require Import mc_reify.func_defs.
Require Import mc_reify.denote_tac.

Section tbled.

Parameter tbl : SymEnv.functions RType_typ.
Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Definition APPLY_load temp var ret gt id t t_root e0 e1 efs tts e lr n :=
EAPPLY typ func (load_lemma temp var ret gt id t t_root e0 e1 efs tts e lr n).

Definition remove_global_spec (t : tycontext) := 
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.

Notation "'NOTATION_T1' v" := (PTree.Node PTree.Leaf None
         (PTree.Node PTree.Leaf None
            (PTree.Node
               (PTree.Node PTree.Leaf None
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some v)
                        PTree.Leaf) None PTree.Leaf)) None PTree.Leaf))) (at level 50).

Goal
forall {Espec : OracleKind} (sh:Share.t) (contents : list val) (v: val) , exists (PO : environ -> mpred), 
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (|> assertD [] (localD (NOTATION_T1 v) (PTree.empty (type * val))) 
       [data_at sh t_struct_list (default_val _) (force_ptr v)])
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
*)

reify_expr_tac.


(*Set Printing Depth 300.*)

Eval vm_compute in
(match (get_arguments e) with
| (Some Delta, Some Pre, Some st) => 
  compute_load_arg (Delta, Pre, st) 
| _ => None
end).


Eval vm_compute in
(match (get_arguments e) with
| (Some Delta, Some Pre, Some st) => 
  match compute_load_arg (Delta, Pre, st) with
  | Some (t, v, r, gt, i, ty, t_root, e0, e1, efs, tts, lr, n) =>
          run_tac
            (THEN INTROS
            (THEN (APPLY_load t v r gt i ty t_root e0 e1 efs tts Struct_env lr n)
                  (TRY (FIRST [REFLEXIVITY_OP_CTYPE tbl0;
                               REFLEXIVITY_BOOL tbl0;
                               REFLEXIVITY_CEXPR tbl0;
                               REFLEXIVITY tbl0;
                               REFLEXIVITY_MSUBST tbl0]))))
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
