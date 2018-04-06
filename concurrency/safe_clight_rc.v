Require Import Bool.
Require Import ZArith.
Require Import BinPos.

Require Import Axioms.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import compcert_imports. Import CompcertCommon.
Require Import Clight.
Require Import Clight_coop.
Require Import Clight_eff.

Require Import VST.sepcomp. Import SepComp.
Require Import VST.concurrency.arguments.

Require Import VST.concurrency.jstep.
Require Import VST.concurrency.pred_lemmas.
Require Import VST.concurrency.rc_semantics.
Require Import VST.sepcomp.simulations. Import SM_simulation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Reach-Closed Clight *)

(** This file proves that safe Clight programs are also reach-closed. *)

Module SAFE_CLIGHT_RC. Section SafeClightRC.

Variable hf : I64Helpers.helper_functions.

Notation clsem := (CL_eff_sem1 hf).

Notation rcsem := (RC.effsem clsem).

Variable juicy_mem : Type. (* will be instantiated later to the actual [juicy_mem] *)

Variable transf : FSem.t mem juicy_mem.

Section Z.

Variable Z : Type.

Variable espec : external_specification juicy_mem external_function Z.

Variable espec_def :
  forall ef x tys args z m,
  ext_spec_pre espec ef x tys args z m ->
  vals_def args.

Variable espec_exit :
  forall v z m,
  ext_spec_exit espec (Some v) z m ->
  ~~is_vundef v.

Variable ge : Genv.t fundef Ctypes.type.

Definition cl_state_inv (c : RC.state CL_core) (m : mem) e te :=
  [/\ forall x b (ty : Ctypes.type),
        PTree.get x e = Some (b,ty) ->
        RC.roots ge c b
    & forall x v,
        PTree.get x te = Some v ->
        {subset getBlocks [:: v] <= RC.roots ge c}
  ].

Fixpoint cl_cont_inv (c : RC.state CL_core) (k : cont) (m : mem) :=
  match k with
    | Kstop => True
    | Kseq s k' => cl_cont_inv c k' m
    | Kloop1 s1 s2 k' => cl_cont_inv c k' m
    | Kloop2 s1 s2 k' => cl_cont_inv c k' m
    | Kswitch k' => cl_cont_inv c k' m
    | Kcall oid f e te k' => [/\ cl_state_inv c m e te & cl_cont_inv c k' m]
  end.

Definition cl_core_inv (c : RC.state CL_core) (m : mem) :=
  match RC.core c with
    | CL_State f s k e te =>
        [/\ cl_state_inv c m e te
          , {subset RC.reach_set ge c m <= RC.roots ge c}
          & cl_cont_inv c k m]
    | CL_Callstate f args k =>
        [/\ {subset getBlocks args <= RC.reach_set ge c m}
          , {subset RC.reach_set ge c m <= RC.roots ge c}
          & cl_cont_inv c k m]
    | CL_Returnstate v k =>
        [/\ {subset getBlocks [:: v] <= RC.reach_set ge c m}
          & cl_cont_inv c k m]
  end.

Lemma getBlocksP l b : reflect (exists ofs, List.In (Vptr b ofs) l) (b \in getBlocks l).
Proof.
case e: (b \in getBlocks l).
+ by apply: ReflectT; move: e; rewrite /in_mem /= /is_true /= getBlocks_char.
+ apply: ReflectF=> [][]ofs C.
rewrite /in_mem /= /is_true /= in e; move: C e; elim: l=> //= a l IH; case.
by move=> ->; rewrite /getBlocks /= /eq_block; case: (Coqlib.peq b b).
move=> Hin Hget; apply: IH=> //.
by move: Hget; rewrite getBlocksD; case: a=> // ? ?; rewrite orb_false_iff; case.
Qed.

Lemma sem_cast_getBlocks v v' ty ty' :
  Cop.sem_cast v ty ty' = Some v' ->
  {subset getBlocks [:: v'] <= getBlocks [:: v]}.
Proof.
rewrite /Cop.sem_cast.
case: (Cop.classify_cast ty ty')=> //; try solve
 [ case: v=> // ?; [by case; move=> ->|by move=> ?; case; move=> ->]
 | by move=> ? ?; case: v=> //; move=> ?; case=> <-
 | by move=> ?; case: v=> //; move=> ?; case=> <-
 | by move=> ? ?; case: v=> // ?; case: (Cop.cast_float_int _ _)=> // ?; case=> <-
 | by move=> ? ?; case: v=> // ?; case: (Cop.cast_float_int _ _)=> // ?; case=> <-
 | by case: v=> // ?; case=> <-
 | by move=> ?; case: v=> // ?; case: (Cop.cast_float_long _ _)=> // ?; case=> <-
 | by case: v=> // ?; [by case=> // <-|by move=> ?; case=> // <-]
 | by move=> ? ? ? ?; case: v=> // ? ?; case: (_ && _)=> //; case=> <-
 | by case=> <-].
Qed.

Lemma REACH_mono' U V (H: {subset U <= V}) m : {subset REACH m U <= REACH m V}.
Proof.
move=> b; rewrite /in_mem /= /is_true /=.
by apply: REACH_mono; apply: H.
Qed.

Lemma REACH_loadv chunk m b i b1 ofs1
  (LDV: Mem.loadv chunk m (Vptr b i) = Some (Vptr b1 ofs1)) L :
  b \in L -> b1 \in REACH m L.
Proof.
move=> H; eapply (REACH_cons _ _ b1 b (Integers.Int.unsigned i) ofs1);
  first by apply: REACH_nil.
move: LDV; rewrite /Mem.loadv; case/Mem.load_valid_access=> H2 H3; apply: H2.
split; [omega|case: chunk H3=> /= *; omega].
move: LDV; move/Mem.load_result=> H2; move: (sym_eq H2)=> {H2}H2.
by case: (decode_val_pointer_inv _ _ _ _ H2)=> -> /=; case=> ->.
Qed.

Lemma loadv_reach_set ch (c : RC.state CL_core) m b ofs v :
  Mem.loadv ch m (Vptr b ofs) = Some v ->
  b \in RC.roots ge c ->
  {subset getBlocks [:: v] <= RC.reach_set ge c m}.
Proof.
case: v=> // b' i'; move/REACH_loadv=> H H2 b'' Hget.
move: Hget; case/getBlocksP=> ?; case; case=> ? ?; subst.
by apply: H.
Qed.

Lemma eval_expr_reach' c m e te a v :
  cl_state_inv c m e te ->
  {subset RC.reach_set ge c m <= RC.roots ge c} ->
  eval_expr ge e te m a v ->
  {subset getBlocks [:: v] <= RC.roots ge c}.
Proof.
set (P := fun (a0 : expr) v0 =>
            {subset getBlocks [:: v0] <= RC.roots ge c}).
set (P0 := fun (a0 : expr) b0 i0 =>
            {subset getBlocks [:: Vptr b0 i0] <= RC.roots ge c}).
case=> H H2 Hclosed H3.
case: (eval_expr_lvalue_ind ge e te m P P0)=> //.

{ by move=> id ty v0 H5 b H6; apply: (H2 id v0 H5). }

{ move=> op a0 ty v1 v0 H4 H5 H6 b H7; elim: op H6=> /=.
  + rewrite /Cop.sem_notbool.
    case: (Cop.classify_bool (typeof a0))=> //.
    case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _).
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _ _).
    case: v1 H4 H5=> // i H8 H9.
    case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _).
    move=> _; case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    by rewrite /Val.of_bool; case: (Integers.Int64.eq _ _).
  + rewrite /Cop.sem_notint.
    case: (Cop.classify_notint (typeof a0))=> // _.
    case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case.
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case.
  + rewrite /Cop.sem_neg.
    case Hcl: (Cop.classify_neg (typeof a0))=> // [sgn||].
    case Hv1: v1 H4 H5=> // [v0']; subst.
    move=> H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case.
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case.
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case. }

{ move=> op a1 a2 ty v1 v2 v0 H4 H5 H6 H7 H8 b H9; elim: op H6 H8=> /=.
  { rewrite /Cop.sem_add.
    case: (Cop.classify_add _ _)=> //.
    move=> ? ? Heval; case: v1 H4 H5=> // b0 i H4 H5; case: v2 H7 Heval=> // i0 ? ?.
    case=> Heq; subst v0; move: H9; case/getBlocksP=> ?; case=> //; case=> ? ?; subst b0.
    by apply: H5; apply/getBlocksP; exists i; constructor.
    move=> ? ? Heval; case: v1 H4 H5=> // i H4 H5; case: v2 H7 Heval=> // ? ? H7 Heval.
    case=> Heq; subst v0; apply: H7; case: (getBlocksP _ _ H9)=> ?; case; case=> Heq' _; subst.
    by apply/getBlocksP; eexists; eauto; econstructor; eauto.
    move=> ? ? Heval; case: v1 H4 H5=> // ? ? H4 H5; case: v2 H7 Heval=> // ? ? ?; case=> ?; subst.
    apply: H5; case: (getBlocksP _ _ H9)=> ?; case; case=> <- _.
    by apply/getBlocksP; eexists; eauto; econstructor; eauto.
    move=> ? ? Heval; case: v1 H4 H5=> // i H4 H5; case: v2 H7 Heval=> // ? ? H7 Heval.
    case=> Heq; subst v0; apply: H7; case: (getBlocksP _ _ H9)=> ?; case; case=> Heq' _; subst.
    by apply/getBlocksP; eexists; eauto; econstructor; eauto.
    move=> Heval; rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //. }
  { move=> Heval; rewrite /Cop.sem_sub.
    case: (Cop.classify_sub _ _)=> //.
    move=> ty'.
    case: v1 H4 H5=> // ? ? Heval' Hp ?; case: v2 H7 Heval=> // i Hp' Heval''; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case; case=> <- _.
    by apply: Hp; apply/getBlocksP; eexists; econstructor; eauto.
    move=> ty'.
    case: v1 H4 H5=> // ? ? Heval' Hp; case: v2 H7 Heval=> // ? ? Hp' Heval''.
    case: (eq_block _ _)=> // ?; subst.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> ty'.
    move=> ?; case: v1 H4 H5=> // ? ? Heval' Hp; case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //; case=> ? _; subst.
    by apply: Hp; apply/getBlocksP; eexists; econstructor; eauto.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //. }
  { move=> Heval; rewrite /Cop.sem_mul.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //. }
  { move=> Heval; rewrite /Cop.sem_div.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    case: (_ || _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.eq _ _)=> //; case=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    case: (_ || _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int64.eq _ _)=> //; case=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //. }
  { move=> Heval; rewrite /Cop.sem_mod.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    case: (_ || _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.eq _ _)=> //; case=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    case: (_ || _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int64.eq _ _)=> //; case=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst. }
  { move: H9; case/getBlocksP=> ?; case=> //.
    move=> ? Heval; subst; rewrite /Cop.sem_and.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    case: a'=> // i; case: a''=> // ?; case: s=> //. }
  { move=> Heval; subst; rewrite /Cop.sem_or.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst. }
  { move: H9; case/getBlocksP=> ?; case=> //.
    move=> Heval; subst; rewrite /Cop.sem_xor.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move=> Heval; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst. }
  { move=> Heval; subst; rewrite /Cop.sem_shl.
    rewrite /Cop.sem_shift.
    case: (Cop.classify_shift _ _)=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    case: (Integers.Int.ltu _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    case: (Integers.Int64.ltu _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    case: (Integers.Int64.ltu _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    case: (Integers.Int.ltu _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //. }
  { move=> Heval; subst; rewrite /Cop.sem_shr.
    rewrite /Cop.sem_shift.
    case: (Cop.classify_shift _ _)=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    case: (Integers.Int.ltu _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    case: (Integers.Int64.ltu _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    case: (Integers.Int64.ltu _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    case: (Integers.Int.ltu _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //. }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    case: (_ && _)=> //; case=> ?; subst.
    move: H9; rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    move=> ? /=; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: v1 H4 H5=> // ? ? ?.
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.eq _ _)=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.eq _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //. }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    case: (_ && _)=> //; case=> ?; subst.
    move: H9; rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    move=> ? /=; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: v1 H4 H5=> // ? ? ?.
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.eq _ _)=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.eq _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //. }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    move=> Hp'; case: (_ && _)=> //; case=> H9; subst.
    move: H9; rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.ltu _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: v1 H4 H5=> // ? ? ?.
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.lt _ _)=> //.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.ltu _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.lt _ _)=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.ltu _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //. }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    move=> Hp'; case: (_ && _)=> //; case=> H9; subst.
    move: H9; rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.ltu _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: v1 H4 H5=> // ? ? ?.
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.lt _ _)=> //.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.ltu _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.lt _ _)=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.ltu _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //. }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    move=> Hp'; case: (_ && _)=> //; case=> H9; subst.
    move: H9; rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.ltu _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: v1 H4 H5=> // ? ? ?.
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.lt _ _)=> //.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.ltu _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.lt _ _)=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.ltu _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //. }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    move=> Hp'; case: (_ && _)=> //; case=> H9; subst.
    move: H9; rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.ltu _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: v1 H4 H5=> // ? ? ?.
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    case: (Integers.Int.lt _ _)=> //.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.ltu _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.lt _ _)=> // ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int64.ltu _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    move: H9; case/getBlocksP=> ?; case=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //.
    case: (Floats.Float.cmp _ _)=> //. }
}

{ move=> a0 ty v1 v0 H4 H5 H6 b H7; apply: H5.
  by apply: (sem_cast_getBlocks H6 H7). }

{ move=> a0 loc ofs v0 H4 H5 H6 b H7.
  case: {v0} H6 H7.
  + move=> ch v1 H8 H9 H10.
    have H11: {subset getBlocks [:: v1] <= RC.reach_set ge c m}.
    { have H12: loc \in getBlocks [:: Vptr loc ofs].
      { by apply/getBlocksP; exists ofs; constructor. }
      move: {H12}(H5 _ H12)=> H12 b' Hget.
      by apply: (loadv_reach_set H9)=> //; apply: REACH_nil. }
    by apply: Hclosed; apply: H11; apply: H10.
  + move=> H6; case/getBlocksP=> ofs'; case=> //; case=> <- _.
    by apply: H5; apply/getBlocksP; exists ofs; constructor.
  + move=> H6; case/getBlocksP=> ofs'; case=> //; case=> <- _.
    by apply: H5; apply/getBlocksP; exists ofs; constructor.
}

{ move=> id l ty H4 b; case/getBlocksP=> ofs; case=> //; case=> <- _.
  by apply: (H _ _ _ H4). }

{ move=> id l ty H4 H5 H6 b; case/getBlocksP=> ofs; case=> //; case=> <- _.
  by apply/orP; left; apply: (find_symbol_isGlobal _ _ _ H5). }

{ by move=> H4 H5 b H7; apply: (H4 _ _ H3). }
Qed.

Lemma eval_lvalue_reach c m e te a b ofs :
  cl_state_inv c m e te ->
  {subset RC.reach_set ge c m <= RC.roots ge c} ->
  eval_lvalue ge e te m a b ofs ->
  {subset getBlocks [:: Vptr b ofs] <= RC.roots ge c}.
Proof.
move=> H Hclosed H2 b'; case/getBlocksP=> ofs'; case=> //; case=> <- _; case: H2=> //.

{ case: H=> H ? ? ? ? ?; apply: H. eassumption. }

{ move=> id l ty H5 H6 H7.
  apply/orP; left.
  by apply: (find_symbol_isGlobal _ _ _ H6). }

{ move=> a0 ty l ofs0; move/(eval_expr_reach' H).
  move/(_ Hclosed l)=> X; apply: X; apply/getBlocksP.
  by exists ofs0; constructor. }

{ move=> a0 i ty l ofs0 id fList att delta; move/(eval_expr_reach' H).
  move/(_ Hclosed l)=> H2 ? ?; apply: H2; apply/getBlocksP.
  by exists ofs0; constructor. }

{ move=> a0 i ty l ofs0 id fList att; move/(eval_expr_reach' H).
  move/(_ Hclosed l)=> H2 ?; apply: H2; apply/getBlocksP.
  by exists ofs0; constructor. }
Qed.

Lemma eval_exprlist_reach' c m e te aa tys vv :
  cl_state_inv c m e te ->
  {subset RC.reach_set ge c m <= RC.roots ge c} ->
  eval_exprlist ge e te m aa tys vv ->
  {subset getBlocks vv <= RC.roots ge c}.
Proof.
move=> H Hclosed; elim=> // a bl ty tyl v1 v2 vl H2 H3 H4 H5.
move=> b; case/getBlocksP=> ofs; case.
+ move=> Heq; subst v2.
apply: (eval_expr_reach' H Hclosed H2).
apply: (sem_cast_getBlocks H3).
by apply/getBlocksP; exists ofs; constructor.
+ move=> H6; apply: H5; clear -H6.
elim: vl H6=> // a vl' H7; case.
by move=> Heq; subst a; apply/getBlocksP; exists ofs; constructor.
by move=> H8; apply/getBlocksP; exists ofs; right.
Qed.

Lemma freelist_effect_reach' (c : RC.state CL_core) m L b ofs :
  (forall b z1 z2, List.In (b,z1,z2) L -> b \in RC.roots ge c) ->
   FreelistEffect m L b ofs ->
   RC.reach_set ge c m b.
Proof.
elim: L c m b ofs=> //; case; case=> a q r l' IH c m b ofs /= H; case/orP.
by apply: IH=> // x y z H2; apply: (H x y z); right.
rewrite /FreeEffect.
case Hval: (valid_block_dec _ _)=> //.
case: (eq_block _ _)=> // Heq; subst.
by case/andP; case/andP=> _ _ _; apply: REACH_nil; apply: (H a q r)=> //; left.
Qed.

Lemma freelist_effect_reach b ofs f k e te locs m :
  let: c := {|
     RC.core := CL_State f (Sreturn None) k e te;
     RC.locs := locs |} in
   FreelistEffect m (blocks_of_env e) b ofs ->
   cl_state_inv c m e te ->
   {subset RC.reach_set ge c m <= RC.roots ge c} ->
   RC.reach_set ge c m b.
Proof.
move=> Hfree Hs Hsub.
apply: (freelist_effect_reach' (L:=blocks_of_env e)(b:=b)(ofs:=ofs))=> //.
move=> b' z1 z2; rewrite /blocks_of_env /PTree.elements List.in_map_iff.
case=> [[x [y z]]] []; subst; case=> ? ? ?; subst.
move=> Hl; case: (PTree.xelements_complete e _ _ _ _ Hl)=> //.
by rewrite -PTree.get_xget_h; case: Hs=> He Hte; move/(He _).
Qed.

Lemma builtin_effects_reach (c : RC.state CL_core) ef vargs m b ofs :
  BuiltinEffects.BuiltinEffect ge ef vargs m b ofs ->
  REACH m (getBlocks vargs) b.
Proof.
rewrite /BuiltinEffects.BuiltinEffect; case: ef=> //.
{ rewrite /BuiltinEffects.free_Effect.
  elim: vargs m b ofs=> // a l IH m b ofs; case: a=> // b' i.
  case: l IH=> // _.
  case Hload: (Mem.load _ _ _ _)=> // [v].
  case: v Hload=> // i' Hload; case/andP; case/andP; case/andP=> X Y W U.
  move: X; rewrite /eq_block; case: (Coqlib.peq b b')=> // Heq _; subst b'.
  by apply: REACH_nil; apply/getBlocksP; exists i; constructor. }
{ move=> sz z; rewrite /BuiltinEffects.memcpy_Effect.
  elim: vargs m b ofs=> // a l IH m b ofs; case: a=> // b' i.
  case: l IH=> // v l IH; case: v IH=> // b'' i'' IH.
  case: l IH=> // IH.
  case/andP; case/andP; case/andP; case: (eq_block b b')=> // Heq; subst b'.
  by move=> _ _ _ _; apply: REACH_nil; apply/getBlocksP; exists i; constructor. }
Qed.

Lemma eval_expr_reach c m a v :
  cl_core_inv c m ->
  match RC.core c with
    | CL_State f s k e te =>
        eval_expr ge e te m a v ->
        {subset getBlocks [:: v] <= RC.roots ge c}
    | _ => True
  end.
Proof.
rewrite /cl_core_inv; case: (RC.core c)=> //.
by move=> f s k e te []H U V W; move: H U W; apply: eval_expr_reach'.
Qed.

Lemma external_call_reach l (ef : external_function) vargs m t v m'
  (Hgbl: {subset isGlobalBlock ge <= l}) :
  ~BuiltinEffects.observableEF hf ef ->
  external_call ef ge vargs m t v m' ->
  {subset getBlocks vargs <= REACH m l} ->
  {subset getBlocks [:: v] <= [predU REACH m l & freshloc m m']}.
Proof.
rewrite /BuiltinEffects.observableEF; case: ef=> //.
{ move=> nm sg H.
  have Hh: (I64Helpers.is_I64_helper hf nm sg).
  { by case: (I64Helpers.is_I64_helper_dec hf nm sg). }
  move {H}; move: Hh=> /= H H2; inversion H2; subst; move {H2}.
  case: H args res H0 H1=> /=.
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd). }
{ move=> nm sg H.
  have Hh: (I64Helpers.is_I64_helper hf nm sg).
  { by case: (I64Helpers.is_I64_helper_dec hf nm sg). }
  move {H}; move: Hh=> /= H H2; inversion H2; subst; move {H2}.
  case: H args res H0 H1=> /=.
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd).
  + rewrite /proj_sig_res /= => ? ? ?; case=> //.
    move=> ? ? ? Hfnd _ b'; move/getBlocksP; case=> ?; case=> //; case=> <- _.
    apply/orP; left; apply: REACH_nil.
    by apply: Hgbl; apply: (find_symbol_isGlobal _ _ _ Hfnd). }
{ move=> _ /=; case=> n m0 m0' b m'' Ha Hs.
  move: (freshloc_alloc _ _ _ _ _ Ha)=> Ha'.
  move: (store_freshloc _ _ _ _ _ _ Hs)=> Hs'.
  have Hf: freshloc m0 m'' = fun b' => Coqlib.proj_sumbool (eq_block b' b).
  { extensionality b'.
    move: Ha' Hs'; rewrite -(freshloc_trans m0 m0' m'' b').
    by move=> -> ->; rewrite orbC.
    by apply: (alloc_forward _ _ _ _ _ Ha).
    by apply: (store_forward _ _ _ _ _ _ Hs). }
  rewrite Hf.
  move=> Hsub b'; move/getBlocksP; case=> ofs; case=> //; case=> <- _.
  rewrite in_predU; apply/orP; right; rewrite /in_mem /=.
  by case: (eq_block b b). }
{ move=> _ /=; case=> b lo sz m0 m0' Hl H2 Hf Hsub.
  rewrite (freshloc_free _ _ _ _ _ Hf).
  by move=> b'; move/getBlocksP; case=> ofs; case. }
{ by move=> sz al _; case. }
Qed.

Lemma cont_inv_call_cont c k m :
  cl_cont_inv c k m ->
  cl_cont_inv c (call_cont k) m.
Proof. by elim: k. Qed.

Scheme statement_ind := Induction for statement Sort Prop
  with labeled_statements_ind := Induction for labeled_statements Sort Prop.

Lemma cont_inv_find_label' c lbl s k s' k' m :
  cl_cont_inv c k m ->
  find_label lbl s k = Some (s', k') ->
  cl_cont_inv c k' m.
Proof.
set (P := fun s : statement =>
  forall k m,
  cl_cont_inv c k m ->
  find_label lbl s k = Some (s', k') ->
  cl_cont_inv c k' m).
set (P0 := fix F (ls : labeled_statements) :=
  match ls with
    | LSdefault s => P s
    | LScase i s ls => P s /\ F ls
  end).
apply: (@statement_ind P P0)=> //.
+ move=> s0 Hp0 s1 Hp1 k0 m0 Inv /=.
  case Hf: (find_label lbl s0 (Kseq s1 k0))=> [[x y]|].
  by case=> ? ?; subst; apply: (Hp0 _ _ _ Hf).
  by apply/Hp1.
+ move=> e s0 Hp0 s1 Hp1 k'' s'' Inv /=.
  case Hf: (find_label lbl s0 k'')=> [[x y]|].
  by case=> ? ?; subst; apply: (Hp0 _ _ _ Hf).
  by apply/Hp1.
+ move=> s0 Hp0 s1 Hp1 k'' s'' Inv /=.
  case Hf: (find_label lbl s0 (Kloop1 s0 s1 k''))=> [[x y]|].
  by case=> ? ?; subst; apply: (Hp0 _ _ _ Hf).
  by apply/Hp1.
+ move=> e l Hp k'' m'' Inv; elim: l Hp k'' m'' Inv=> /=.
  by move=> s0 Hp0 k'' m'' Inv /=; apply/(Hp0 _ m'').
  move=> i s0 l IH []H H2 k'' m'' Inv.
  case Hf: (find_label _ _ _)=> // [[? ?]|].
  by case=> ? ?; subst; apply: (H _ _ _ Hf).
  by apply: IH.
+ move=> l s0 H k'' m'' Inv /=.
  case Hid: (ident_eq lbl l)=> // [v|].
  by case=> ? ?; subst s0 k''.
  by move=> Hf; apply: (H _ _ Inv).
Qed.

Lemma cont_inv_find_label c lbl s k s' k' m :
  cl_cont_inv c k m ->
  find_label lbl s (call_cont k) = Some (s', k') ->
  cl_cont_inv c k' m.
Proof.
by move=> H H2; apply: (cont_inv_find_label' (cont_inv_call_cont H) H2).
Qed.

Lemma state_inv_freshlocs c0 c' m m' locs e te :
  let: c := {|RC.core := c0;
              RC.locs := locs |} in
  cl_state_inv c m e te ->
  cl_state_inv {|
     RC.core := c';
     RC.locs := REACH m' (fun b : block =>
            freshloc m m' b ||
            RC.reach_set ge c m b)|} m' e te.
Proof.
+ rewrite /cl_state_inv; case=> He Hte; split.
move=> x b ty H; apply/orP; right.
by apply: REACH_nil; apply/orP; right; apply: REACH_nil; apply: (He _ _ _ H).
move=> x v H b H2; apply/orP; right; apply: REACH_nil.
by apply/orP; right; apply: REACH_nil; apply: (Hte _ _ H _ H2).
Qed.

Lemma cont_inv_freshlocs c0 c' k m m' locs :
   let: c := {|RC.core := c0;
               RC.locs := locs |} in
   cl_cont_inv c k m ->
   cl_cont_inv
        {|RC.core := c';
          RC.locs := REACH m' (fun b : block =>
            freshloc m m' b ||
            RC.reach_set ge c m b)|} k m'.
Proof.
elim: k=> //= _ _ e te k' H []H2 H3; split=> //.
+ by apply: state_inv_freshlocs.
+ by apply: H.
Qed.

Lemma cont_inv_mem c k m m' :
  cl_cont_inv c k m ->
  cl_cont_inv c k m'.
Proof.
elim: k m m'=> //= _ _ e te k IH m m' []H H2; split=> //.
by apply: (IH _ _ H2).
Qed.

Lemma cont_inv_ext1 c c' locs k m :
  cl_cont_inv {| RC.core := c; RC.locs := locs |} k m ->
  cl_cont_inv {| RC.core := c'; RC.locs := locs |} k m.
Proof.
elim: k=> // ? ? ? ? ? IH /= [] ? ?; split=> //.
by apply: IH.
Qed.

Lemma cont_inv_retv c k v m :
  cl_cont_inv c k m ->
  cl_cont_inv
     {|
     RC.core := CL_Returnstate v k;
     RC.locs := [predU getBlocks [:: v] & RC.locs c] |} k m.
Proof.
elim: k=> //=.
by move=> s k IH H; move: (IH H); apply: cont_inv_ext1.
by move=> s s' k IH H; move: (IH H); apply: cont_inv_ext1.
by move=> s s' k IH H; move: (IH H); apply: cont_inv_ext1.
by move=> k IH H; move: (IH H); apply: cont_inv_ext1.
move=> oid f e te k IH []H H2; split=> //.
case: H=> He Hte; split.
move=> x b ty H; case: (orP (He _ _ _ H))=> X; apply/orP; first by left.
by right; apply/orP; right.
move=> x v0 H b Hget; case: (orP (Hte _ _ H _ Hget))=> X; apply/orP.
by left.
by right; apply/orP; right.
by move: (IH H2); apply: cont_inv_ext1.
Qed.

Lemma core_inv_freshlocs locs m m' f s k s' e te :
  let: c := {| RC.core := CL_State f s k e te; RC.locs := locs |} in
  let: locs' := REACH m' (fun b : block => freshloc m m' b || RC.reach_set ge c m b) in
  cl_core_inv c m ->
  cl_core_inv {| RC.core := CL_State f s' k e te; RC.locs := locs' |} m'.
Proof.
rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
case=> [][]He Hte Hsub; split=> //=.
split.
{ move=> x b ty H7.
  move: (He _ _ _ H7); case/orP; first by move=> ->.
  move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
  by apply: REACH_nil; apply/orP; right. }
{ move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
  rewrite /RC.reach_set /RC.roots /= => H10.
  by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
{ move=> b X; apply/orP; right.
  rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
  by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
  by apply: REACH_is_closed. }
{ by move: p; apply cont_inv_freshlocs. }
Qed.

Lemma create_undef_temps_undef l x v :
  (create_undef_temps l) ! x = Some v -> v = Vundef.
Proof.
elim: l=> //=; first by rewrite PTree.gempty.
case=> a ? l IH; case: (ident_eq a x).
{ by move=> ?; subst a; rewrite PTree.gss; case. }
{ by move=> Hneq; rewrite PTree.gso=> // ?; subst. }
Qed.

(*TODO: move elsewhere*)
Lemma alloc_variables_valid0 vars E m e m1 b :
  alloc_variables E m vars e m1 ->
  Mem.valid_block m b ->
  Mem.valid_block m1 b.
Proof.
elim: vars E m m1.
by move=> E m m1; inversion 1; subst.
case=> b' t' l IH E m m1; inversion 1; subst=> H2.
apply: (IH (PTree.set b' (b1,t') E) m2)=> //.
by apply: (Mem.valid_block_alloc _ _ _ _ _ H7).
Qed.

Lemma bind_parameters_valid0 vars E m vs m1 b :
  bind_parameters E m vars vs m1 ->
  Mem.valid_block m b ->
  Mem.valid_block m1 b.
Proof.
elim: vars vs E m m1.
by move=> vs E m m1; inversion 1; subst.
case=> b' t' l IH E m m1; inversion 1; subst=> H2.
move: H; inversion 1; subst.
apply: (IH vl m m3)=> //.
by move: (assign_loc_forward _ _ _ _ _ _ H7); case/(_ _ H2).
Qed.

Lemma alloc_variables_freshblocks: forall vars E m e m1
      (AL: alloc_variables E m vars e m1)
      id b t (Hid: e!id = Some (b,t)),
      E!id = Some (b,t) \/ (~Mem.valid_block m b /\ Mem.valid_block m1 b).
Proof. intros vars.
  induction vars; simpl; intros; inversion AL; subst; simpl in *.
    left; trivial.
  destruct (IHvars _ _ _ _ H6 _ _ _ Hid); clear IHvars.
    rewrite PTree.gsspec in H.
    destruct (Coqlib.peq id id0); subst.
      inversion H; subst. right.
      split.
      eapply Mem.fresh_block_alloc; eassumption.
      apply Mem.valid_new_block in H3.
      eapply alloc_variables_valid0; eauto.
      left; trivial.
    right.
      destruct H.
      split; auto.
      intros N; elim H; clear H.
      eapply Mem.valid_block_alloc; eassumption.
Qed.
(*end move*)

Lemma function_entry1_state_inv (c0 : RC.state CL_core) c1 f vargs m e te m' locs :
  let: c := {| RC.core := c0;
               RC.locs := locs |} in
  let: c' := {| RC.core := c1;
               RC.locs := REACH m' (fun b : block =>
                           freshloc m m' b ||
                           RC.reach_set ge c m b)|} in
  {subset getBlocks vargs <= RC.reach_set ge c m} ->
  function_entry1 f vargs m e te m' ->
  cl_state_inv c' m' e te.
Proof.
move=> Hsub; case=> m1 Hno Halloc Hbind ->; split.
{ move=> x b ty He; rewrite /RC.roots /=; apply/orP; right.
  case: (alloc_variables_freshblocks Halloc He).
  by rewrite PTree.gempty.
  move=> Hvalid; apply: REACH_nil; apply/orP; left; apply/andP; split.
  case: Hvalid=> _; move/bind_parameters_valid0; move/(_ _ _ _ _ Hbind).
  by case: (valid_block_dec m' b).
  by case: Hvalid=> Hvalid ?; move: Hvalid; case: (valid_block_dec m b). }
{ move=> x v Hundef b; case/getBlocksP=> ofs; case=> // ?; subst v.
  by move: (create_undef_temps_undef Hundef); discriminate. }
Qed.

Notation E := (@FSem.E _ _ transf).

Notation F := (@FSem.F _ _ transf _ _).

Lemma rc_step c m c' m' :
  cl_core_inv c (E m) ->
  corestep (F clsem) ge (RC.core c) m c' m' ->
  let: c'' := RC.mk c' (REACH (E m') (fun b => freshloc (E m) (E m') b
                                            || RC.reach_set ge c (E m) b))
  in [/\ corestep (F rcsem) ge c m c'' m' & cl_core_inv c'' (E m')].
Proof.
move=> Inv step.
rewrite FSem.step in step; case: step=> step Hprop.
move: step Inv.
remember (FSem.E mem juicy_mem transf m') as jm'.
remember (FSem.E mem juicy_mem transf m) as jm.
move=> step.
move: step Heqjm Heqjm'.
case: c=> /= core locs; case.

{ move=> f a1 a2 k e le m0 loc ofs v2 v m0' H H2 H3 H4 Hmeq Hmeq' Inv.
  set (c'' := Clight_coop.CL_State f Clight.Sskip k e le).
  set (c := {|
         RC.core := CL_State f (Sassign a1 a2) k e le;
         RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).

  split.
  rewrite FSem.step; split=> //=.
  exists (assign_loc_Effect (Clight.typeof a1) loc ofs); split.
  by rewrite -Hmeq -Hmeq' /=; econstructor; eauto.
  split=> //.

  { move=> b ofs'; rewrite /assign_loc_Effect.
  case Hac: (Ctypes.access_mode _)=> // [ch|].
  + case/andP; case/andP=> Heq _ _.
    have Heq': loc = b by rewrite /eq_block in Heq; case: (Coqlib.peq loc b) Heq.
    subst loc; move {Heq}; rewrite /cl_core_inv /= in Inv.
    case: Inv=> Inv Inv2 Inv3; apply: REACH_nil.
    by apply: (eval_lvalue_reach Inv Inv2 H); apply/getBlocksP; exists ofs; constructor.
  + case/andP; case/andP=> Heq _ _.
    have Heq': loc = b by rewrite /eq_block in Heq; case: (Coqlib.peq b loc) Heq.
    subst loc; move {Heq}; rewrite /cl_core_inv /= in Inv.
    case: Inv=> Inv Inv2 Inv3; apply: REACH_nil.
    by apply: (eval_lvalue_reach Inv Inv2 H); apply/getBlocksP; exists ofs; constructor. }
  { by rewrite -Hmeq -Hmeq'. }
  { by apply: core_inv_freshlocs. } }

{ move=> f id a k e te m0 v H Hmeq Hmeq' Inv.
  set (c'' := CL_State f Sskip k e (PTree.set id v te)).
  set (c := {|
         RC.core := CL_State f (Sset id a) k e te;
         RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //=.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  by rewrite -Hmeq -Hmeq' /=; econstructor; eauto.

  (*reestablish invariant*)
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
  case; case=> He Hte Hsub Hk; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7 b H8; case Heq: (ident_eq x id).
    + subst x; rewrite PTree.gss in H7; case: H7=> Heq'; subst v0.
      move: (eval_expr_reach _ _ Inv H); move/(_ b H8).
      rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
      by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    + rewrite PTree.gso in H7=> //; move: (Hte _ _ H7); move/(_ b H8).
      rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
      by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    rewrite Hmeq'.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by rewrite Hmeq'; apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f optid a a1 k e te m0 tyargs tyres vf vargs fd H H2 H3 H4 H5 Hmeq Hmeq' Inv.
  set (c'' := CL_Callstate fd vargs (Kcall optid f e te k)).
  set (c := {|
         RC.core := CL_State f (Scall optid a a1) k e te;
         RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  by rewrite -Hmeq -Hmeq' /=; econstructor; eauto.

  (*reestablish invariant*)
  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
  case=> He Hte //; split.
  move=> b H7; move: (eval_exprlist_reach' Inv Hsub H3).
  move/(_ b H7); rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
  by apply: REACH_nil; apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    rewrite Hmeq'.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by rewrite Hmeq'; apply: REACH_is_closed. }
  split; last by move: Hk; apply: cont_inv_freshlocs.
  by move: Inv; apply: state_inv_freshlocs. }

{ (*builtins*)
  move=> f optid ef tyargs a1 k e te m0 vargs t vres m0' H2 H3 H4 Hmeq Hmeq' Inv.
  set (c'' := CL_State f Sskip k e (set_opttemp optid vres te)).
  set (c := {|
          RC.core := CL_State f (Sbuiltin optid ef tyargs a1) k e te;
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists (BuiltinEffects.BuiltinEffect ge ef vargs m0); split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  move=> b ofs; move/(builtin_effects_reach c)=> Hreach.
  case: Inv=> Hs Hsub Hk; move: (eval_exprlist_reach' Hs Hsub H2)=> H7.
  by move: Hreach; rewrite Hmeq; apply: REACH_mono'.
  by rewrite -Hmeq -Hmeq'.

  (*reestablish invariant*)
  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /set_opttemp /=; move {locs'' c c''}.
    move {Hk}; case: optid Inv Hte Hsub.
    { move=> a Inv Hte Hsub x v.
      move: (eval_exprlist_reach' Inv Hsub H2)=> H7.
      have X: {subset getBlocks vargs
            <= RC.reach_set ge
                 {|
                 RC.core := CL_State f (Sbuiltin (Some a) ef tyargs a1) k e te;
                 RC.locs := locs |} m0}.
      { by move=> b Hget; move: (H7 _ Hget)=> H7'; apply: REACH_nil. }
      have Y: {subset isGlobalBlock ge
            <= RC.roots ge
                {|
                RC.core := CL_State f (Sbuiltin (Some a) ef tyargs a1) k e te;
                RC.locs := locs |}}.
      { by move=> b isGbl; apply/orP; left. }
      move: (external_call_reach Y H4 H3 X)=> H8.
      case: (ident_eq a x)=> Heq H9.
      + subst x; rewrite PTree.gss in H9; case: H9=> Heq'; subst vres.
        move=> b H9; move: (H8 _ H9); rewrite in_predU; case/orP=> H10.
        by apply/orP; right; apply: REACH_nil; apply/orP; right.
        by apply/orP; right; apply: REACH_nil; apply/orP; left.
      + rewrite PTree.gso in H9.
        move=> b H10; move: (Hte _ _ H9); move/(_ b H10); case/orP=> H.
        by apply/orP; left.
        apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
        by apply/orP; right.
        by move=> C; apply: Heq; rewrite C. }
    { move=> Inv Hte Hsub x v H7 b H8; move: (Hte _ _ H7); move/(_ b H8); case/orP=> H.
      by apply/orP; left.
      apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
      by apply/orP; right. } }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    rewrite Hmeq'.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by rewrite Hmeq'; apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f s1 (Kseq s2 k) e te).
  set (c := {|
          RC.core := CL_State f (Ssequence s1 s2) k e te;
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
    by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    rewrite Hmeq'.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by rewrite Hmeq'; apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f s k e te).
  set (c := {|
          RC.core := CL_State f Sskip (Kseq s k) e te;
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
    by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    rewrite Hmeq'.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f Scontinue k e te).
  set (c := {|
          RC.core := CL_State f Scontinue (Kseq s k) e te;
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
    by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f Sbreak k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //; first by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
    by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f a s1 s2 k e te m0 v1 b Heval H2 Hmeq Hmeq' Inv.
  set (c'' := CL_State f (if b then s1 else s2) k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //; first by rewrite -Hmeq -Hmeq'.
  by apply: (core_inv_freshlocs _ _ Inv). }

{ move=> f s1 s2 k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f s1 (Kloop1 s1 s2 k) e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //; first by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 x H Hmeq Hmeq' Inv.
  set (c'' := CL_State f s2 (Kloop2 s1 s2 k) e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //; first by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f Sskip k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //; first by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
    by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f (Sloop s1 s2) k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //; first by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f Sskip k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //; first by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f k e te m0 m0' Hfree Hmeq Hmeq' Inv.
  set (c'' := CL_Returnstate Vundef (call_cont k)).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists (FreelistEffect m0 (blocks_of_env e)); split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  case: Inv=> Inv Hsub Hk.
  by move=> b ofs Hfree'; rewrite -Hmeq; apply: (freelist_effect_reach Hfree' Inv).
  by rewrite -Hmeq -Hmeq'.
  move: Inv; case=> Hs Hsub Hk; split.
  by move=> ?; move/getBlocksP; case=> ?; case.
  apply: cont_inv_call_cont.
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f a k e te m0 v v' m0' Heval Hcast Hfree Hmeq Hmeq' Inv.
  set (c'' := CL_Returnstate v' (call_cont k)).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists (FreelistEffect m0 (blocks_of_env e)); split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  case: Inv=> Inv Hsub Hk.
  move=> b ofs Hfree'.
  rewrite -Hmeq. apply (freelist_effect_reach(k:=k)(f:=f) Hfree' Inv). assumption.

  by rewrite -Hmeq -Hmeq'.
  move: Inv; case=> Hs Hsub Hk; split.
  move=> b Hget; move: (sem_cast_getBlocks Hcast Hget)=> Hget'.
  move: (eval_expr_reach' Hs Hsub Heval Hget'); case/orP=> H; apply: REACH_nil; apply/orP.
  by left.
  by right; apply: REACH_nil; apply/orP; right; apply: REACH_nil; apply/orP; right.
  apply: cont_inv_call_cont.
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f k e te m0 m0' Hcall Hfree Hmeq Hmeq' Inv.
  set (c'' := CL_Returnstate Vundef k).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists (FreelistEffect m0 (blocks_of_env e)); split;
    first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  case: Inv=> Inv Hsub Hk.
  by move=> b ofs Hfree'; rewrite -Hmeq; apply: (freelist_effect_reach(k:=k)(f:=f) Hfree' Inv).
  by rewrite -Hmeq -Hmeq'.
  split; first by move=> ?; move/getBlocksP; case=> ?; case.
  move: Inv; case=> Hs Hsub Hk; apply cont_inv_freshlocs.
    by move: Hk; apply: cont_inv_ext1. }

{ move=> f s1 s2 k e te m0 n0 Heval Hmeq Hmeq' Inv.
  set (c'' := CL_State f (seq_of_labeled_statement (select_switch n0 s2))
               (Kswitch k) e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f x k e te m0 Hx Hmeq Hmeq' Inv.
  set (c'' := CL_State f Sskip k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f Scontinue k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f lbl s k e te m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f s k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f lbl k e te m0 s' k' Hfnd Hmeq Hmeq' Inv.
  set (c'' := CL_State f s' k' e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  move: Hfnd; apply: cont_inv_find_label.
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f vargs k m0 e te m0' Hentry Hmeq Hmeq' Inv.
  set (c'' := CL_State f (fn_body f) k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Inv Hsub Hk; split.
  split.
  { move=> x b ty H.
    set (c''' := {| RC.core := c''; RC.locs := locs'' |}).
    case: (@function_entry1_state_inv c''' (CL_Callstate (Internal f) vargs k)
                                  _ _ _ _ _ _ _ Inv Hentry)=> /=.
    by move=> He Hte; apply: (He _ _ _ H). }
  { move=> x v H.
    set (c''' := {| RC.core := c''; RC.locs := locs'' |}).
    case: (@function_entry1_state_inv c''' (CL_Callstate (Internal f) vargs k)
                                  _ _ _ _ _ _ _ Inv Hentry)=> /=.
    by move=> He Hte; apply: (Hte _ _ H). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> v optid f e te k m0 Hmeq Hmeq' Inv.
  set (c'' := CL_State f Sskip k e (set_opttemp optid v te)).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  split.
  rewrite FSem.step; split=> //.
  exists EmptyEffect; split; first by rewrite -Hmeq -Hmeq'; econstructor; eauto.
  split=> //.
  by rewrite -Hmeq -Hmeq'.

  case: Inv=> Hsub Inv.
  rewrite /cl_core_inv /= in Inv; case: Inv; case=> He Hte Hk; split.

  split.
  { move=> x b ty H; apply/orP; right; rewrite /locs'' /=.
    by apply: REACH_nil; move: H; move/He=> X; apply/orP; right; apply: REACH_nil. }
  { move=> x v0; rewrite /set_opttemp /locs'' /c /c''; move {locs'' c'' c}.
    case: optid Hsub Hk He Hte=> a.
    case: (ident_eq a x).
    + move=> Heq Hsub Hk He Hte; subst x; rewrite PTree.gss.
      case=> ?; subst v0=> b Hget; apply/orP; right.
      by apply: REACH_nil; apply/orP; right; apply: (Hsub _ Hget).
    + move=> Hneq Hsub Hk He Hte; rewrite PTree.gso=> H.
      move=> b Hget; apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
      by apply: (Hte _ _ H _ Hget).
      by subst x.
    move=> Inv He Hte H b Hget.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H _ Hget). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

Qed.

Lemma rc_aftext c m ef sg vs c' m' ov :
  cl_core_inv c m ->
  at_external (F clsem) (RC.core c) = Some (ef,sg,vs) ->
  after_external (F rcsem) ov c = Some c' ->
  cl_core_inv c' m'.
Proof.
move=> Inv; rewrite /= FSem.atext FSem.aftext /= /RC.at_external /RC.after_external /= => H.
have Hhlt: Clight_coop.CL_halted (RC.core c) = None.
{ move: H; case: (CL_at_external_halted_excl hf (RC.core c))=> // ->.
  discriminate. }
case Haft: (CL_after_external _ _)=> // [c''].
case Hov: ov=> [v|]; case=> <-.
{ move: Inv; rewrite /cl_core_inv /=.
  move: Haft; rewrite /CL_after_external Hov.
  case: (RC.core c)=> // fd vs' k.
  case: fd=> // ef' tys ty; case=> <-; case=> H0 H2 H3 /=.
  split.
  + by move=> b Hget; apply: REACH_nil; apply/orP; right; apply/orP; left.
  + move: (@cont_inv_mem c k m m' H3); clear.
    by apply: cont_inv_retv. }
{ move: Inv; rewrite /cl_core_inv.
  move: Haft; rewrite /CL_after_external Hov.
  case: (RC.core c)=> // fd args' k.
  case: fd=> // ef' tys ty; case=> <- /=; case=> H0 H2 H3.
  move: (@cont_inv_mem c k m m' H3).
  split.
  + by move=> b; move/getBlocksP; case=> ?; case.
  + by apply: cont_inv_retv. }
Qed.

Lemma rc_safe z c m n :
  cl_core_inv c (E m) ->
  safeN (F clsem) espec ge n z (RC.core c) m ->
  safeN (F rcsem) espec ge n z c m.
Proof.
move=> Inv H; move: z c m Inv H; elim: n=> // n IH z c m Inv H.
rewrite /= !FSem.atext /= /RC.at_external /RC.halted; move: H=> /=.
rewrite !FSem.atext /=.
case Hatext: (Clight_coop.CL_at_external _ _)=> // [[[ef sig] args]|].
rewrite !FSem.halted /= /RC.halted /=.
have Hhlt: Clight_coop.CL_halted (RC.core c) = None.
{ case: (CL_at_external_halted_excl hf (RC.core c))=> //.
  rewrite Hatext; discriminate. }
rewrite Hhlt; case=> x []Hpre Hpost.
have Hdef: vals_def args.
{ by eapply espec_def; eauto. }
rewrite Hdef; exists x; split=> // ret' m' z' Hpost'.
case: (Hpost _ _ _ Hpost')=> c' []Haft HsafeN; move {Hpost Hpost'}.
rewrite FSem.aftext /= /RC.after_external /=; case: ret' Haft.
{ move=> v Haft; exists (RC.mk c' [predU getBlocks [::v] & RC.locs c]).
  rewrite FSem.aftext /= in Haft; rewrite Haft; split=> //; apply: IH=> //.
  move: Inv; rewrite /cl_core_inv /=.
  move: Haft; rewrite /CL_after_external; case: (RC.core c)=> // fd vs k.
  case: fd=> // ef' tys ty; case=> <-; case=> H H2 H3 /=.
  split.
  + by move=> b Hget; apply: REACH_nil; apply/orP; right; apply/orP; left.
  + move: (@cont_inv_mem c k (FSem.E _ _ transf m) (FSem.E _ _ transf m') H3); clear.
    by apply: cont_inv_retv. }
{ rewrite FSem.aftext /=.
  move=> Heq; rewrite Heq; exists (RC.mk c' (RC.locs c)); split=> //.
  apply: IH=> //.
  rewrite /CL_after_external in Heq.
  move: Inv Heq; rewrite /cl_core_inv.
  case: (RC.core c)=> // fd args' k []H H2 H3.
  case: fd=> // ef' tys ty; case=> <- /=.
  move: (@cont_inv_mem c k (FSem.E _ _ transf m) (FSem.E _ _ transf m') H3).
  split.
  + by move=> b; move/getBlocksP; case=> ?; case.
  + by apply: cont_inv_retv. }
rewrite !FSem.halted /= /RC.halted /=.
case Hhlt: (Clight_coop.CL_halted (RC.core c))=> [v|].
{ move=> Hexit.
  have Hdef: ~~is_vundef v by (eapply espec_exit; eauto).
  by rewrite Hdef. }
case=> c' []m' []step Hsafe.
case: (rc_step Inv step)=> Hstep Hinv.
by eexists; exists m'; split; eauto.
Qed.

Lemma rc_init_safe z v vs c m :
  initial_core clsem ge v vs = Some c ->
  (forall n, safeN (FSem.F _ _ transf _ _ clsem) espec ge n z c m) ->
  let c' := {| RC.core := c; RC.locs := getBlocks vs |} in
  [/\ initial_core rcsem ge v vs = Some c'
    & forall n, safeN (FSem.F _ _ transf _ _ rcsem) espec ge n z c' m].
Proof.
rewrite /= /RC.initial_core /= => Heq; rewrite Heq=> Hsafe; split=> // n.
move: Heq (Hsafe n.+1); rewrite /= /CL_initial_core; case: v=> // b ofs.
rewrite FSem.atext FSem.halted /=.
case: (Integers.Int.eq_dec _ _)=> // Heq; subst ofs.
case Hg: (Genv.find_funct_ptr _ _)=> // [fd].
case Hfd: fd=> // [f].
case Hty: (type_of_fundef _)=> // [tys ty].
case Hval: (_ && _)=> //.
case=> <- /=; case=> c' []m'; rewrite FSem.step; case; case=> Hstep Hprop Hsafe'.
case: n Hsafe'=> // n Hsafe' /=.
rewrite !FSem.atext /= !FSem.halted /= /RC.corestep /RC.effstep /=.
set c'' := {| RC.core := c'
        ; RC.locs := REACH (FSem.E _ _ transf m')
     (fun b0 : block =>
      freshloc (FSem.E _ _ transf m) (FSem.E _ _ transf m') b0
      || RC.reach_set ge
           {|
           RC.core := CL_Callstate (Internal f) vs Kstop;
           RC.locs := getBlocks vs |} (FSem.E _ _ transf m) b0) |}.
exists c'', m'; split.
+ rewrite FSem.step; split=> //; exists EmptyEffect.
rewrite /RC.effstep /=; split=> //.
inversion Hstep; subst; constructor=> //.
apply: rc_safe; rewrite /c'' /=; rewrite /cl_core_inv /=.
inversion Hstep; subst=> /=; split=> //.
eapply (function_entry1_state_inv (c0 := c'')); eauto.
by move=> b' Hget; apply: REACH_nil; apply/orP; right.
rewrite /c'' /= => b' Hin; apply/orP; right.
move: Hin; rewrite /RC.reach_set /RC.roots /=.
move/REACH_split; case.
apply: REACH_mono'=> b''.
by move=> Hglob; apply/orP; right; apply: REACH_nil; apply/orP; left.
by move/REACH_is_closed.
by apply: safe_downward1.
Qed.

End Z. End SafeClightRC. End SAFE_CLIGHT_RC.

Import SAFE_CLIGHT_RC.

Program Definition id_transf (T : Type) : FSem.t T T :=
  FSem.mk T T (fun G C sem => sem) id (fun _ _ => True) _ _ _ _ _.
Next Obligation.
apply: prop_ext.
split=> //.
case=> //.
Qed.

Section Clight_RC.

Variable hf : I64Helpers.helper_functions.

Notation clsem := (CL_eff_sem1 hf).

Variable ge : Genv.t fundef Ctypes.type.

Definition I c m B :=
  (exists v vs, B = getBlocks vs /\ initial_core clsem ge v vs = Some c)
  \/ cl_core_inv ge (RC.mk c B) m.

Lemma init_I v vs c m :
  initial_core clsem ge v vs = Some c ->
  I c m (getBlocks vs).
Proof.
by left; exists v, vs.
Qed.

Let rcsem := RC.effsem clsem.

Lemma step_I c m c' m' B :
  I c m B ->
  corestep clsem ge c m c' m' ->
  let B'  := REACH m' (fun b => freshloc m m' b || RC.reach_set ge (RC.mk c B) m b) in
  let c'' := RC.mk c' B' in corestep rcsem ge (RC.mk c B) m c'' m' /\ I c' m' B'.
Proof.
move=> H Hstep.
case: H=> [[v [vs H]]|H].
{ move: H; rewrite /CL_initial_core.
  case=> Hget.
  case: v=> // b ofs /=.
  case Heq: (Integers.Int.eq_dec _ _)=> // [pf].
  case Hgenv: (Genv.find_funct_ptr _ _)=> // [fd].
  case Hfd: fd=> // [f].
  case Hty: (type_of_fundef _)=> // [targs tret].
  case Hcst: (_ && _)=> //.
  case=> Hceq; split; subst c.
  inversion Hstep; subst.
  exists EmptyEffect; split=> //.
  constructor=> //.
  right.
  inversion Hstep; subst; split=> //.
  set c'' := {|
     RC.core := CL_State f (fn_body f) Kstop e le;
     RC.locs := REACH m'
                  (fun b0 : block =>
                   freshloc m m' b0
                   || RC.reach_set ge
                        {|
                        RC.core := CL_Callstate (Internal f) vs Kstop;
                        RC.locs := getBlocks vs |} m b0) |}.
  eapply function_entry1_state_inv with (c0 := c''); eauto.
  by move=> b' Hget; apply: REACH_nil; apply/orP; right.
  rewrite /= => b' Hin; apply/orP; right.
  move: Hin; rewrite /RC.reach_set /RC.roots /=.
  move/REACH_split; case.
  apply: REACH_mono'=> b''.
  by move=> Hglob; apply/orP; right; apply: REACH_nil; apply/orP; left.
  by move/REACH_is_closed. }
{ case: (@rc_step hf mem (id_transf mem) _ _ _ _ _ H Hstep)=> H2 H3.
  split=> //.
  by right. }
Qed.

Lemma atext_I c m B ef sg vs :
  I c B m ->
  at_external clsem c = Some (ef,sg,vs) ->
  vals_def vs = true.
Proof.
rewrite /= /CL_at_external; case: c=> //; case=> // ????? _.
by case Hand: (_ && _)=> //; case: (andP Hand)=> ??; case=> _ _ <-.
Qed.

Lemma aftext_I c m B ef sg vs ov c' m' :
  I c m B ->
  at_external clsem c = Some (ef,sg,vs) ->
  after_external clsem ov c = Some c' ->
  I c' m' (fun b => match ov with None => B b
                      | Some v => getBlocks (v::nil) b || B b
                    end).
Proof.
case.
{ case=> v' []vs' []Hget; rewrite /=.
  case: c=> // fd args k /=.
  rewrite /CL_initial_core.
  case: v'=> // b ofs.
  case: (Integers.Int.eq_dec _ _)=> // Heq; subst ofs.
  case Hg: (Genv.find_funct_ptr _ _)=> // [fd'].
  case Hfd': fd'=> // [f].
  case Hty: (type_of_fundef _)=> // [tys ty].
  case Hval: (_ && _)=> //.
  case=> <- /= *; subst; congruence. }
move=> ?? Haft.
right.
eapply rc_aftext; eauto.
erewrite FSem.atext; eauto.
erewrite FSem.aftext; eauto.
simpl.
rewrite /RC.after_external Haft.
case: ov Haft=> //.
Grab Existential Variables.
refine ov.
refine (id_transf mem).
Qed.

Lemma halted_I c m B v :
  I c m B ->
  halted clsem c = Some v ->
  vals_def (v :: nil) = true.
Proof.
rewrite /= /CL_halted => _; case: c=> // ?; case=> //.
by case Hvd: (vals_def _)=> //; case=> <-.
Qed.

Definition Clight_RC : RCSem.t clsem ge :=
  @RCSem.Build_t _ _ _ clsem ge I init_I step_I atext_I aftext_I halted_I.

End Clight_RC.
