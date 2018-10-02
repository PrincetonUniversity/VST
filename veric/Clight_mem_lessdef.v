Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Clight.
Require Import VST.msl.base.
Require Import VST.veric.base.
Require Import VST.veric.mem_lessdef.

Lemma mem_lessdef_sem_cast:
  forall m1 m2, mem_lessdef m1 m2 ->
  forall v1 v1', Val.lessdef v1 v1' ->
  forall t1 t2 v, 
    classify_cast t1 t2 <> Cop.cast_case_void ->
    sem_cast v1 t1 t2 m1 = Some v ->
    sem_cast v1' t1 t2 m2 = Some v.
Proof.
intros until 3. rename H1 into H9. intros.
unfold sem_cast in *.
destruct (classify_cast t1 t2) eqn:?HH, v1; inv H1; inv H0; try reflexivity.
destruct Archi.ptr64 eqn:Hp; inv H3.
destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)) eqn:?; inv H1.
rewrite (mem_lessdef_weak_valid_pointer _ _ _ _ H Heqb0). auto.
contradiction H9.
auto.
Qed.

Lemma mem_lessdef_sem_binarith:
  forall m1 m2, mem_lessdef m1 m2 ->
  forall v1 v1', Val.lessdef v1 v1' ->
  forall v2 v2', Val.lessdef v2 v2' ->
  forall (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (sem_single: float32 -> float32 -> option val)
    (t1: type) (t2: type) v,
   sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m1 = Some v ->
   sem_binarith sem_int sem_long sem_float sem_single v1' t1 v2' t2 m2 = Some v.
Proof.
intros.
unfold sem_binarith in *.
destruct (sem_cast v1 t1 (Cop.binarith_type (Cop.classify_binarith t1 t2)) m1) eqn:?H; try discriminate.
destruct (sem_cast v2 t2 (binarith_type (classify_binarith t1 t2)) m1) eqn:?H; try discriminate.
apply (mem_lessdef_sem_cast _ _ H _ _ H0) in H3.
apply (mem_lessdef_sem_cast _ _ H _ _ H1) in H4.
rewrite H3, H4.
auto.
clear - H2.
destruct (classify_binarith t1 t2); inv H2; simpl;
clear; intro;
destruct t2; try destruct f; try congruence; destruct Archi.ptr64; try congruence.
destruct (classify_binarith t1 t2); inv H2; simpl;
clear; intro;
destruct t1; try destruct f; try congruence; destruct Archi.ptr64; try congruence.
Qed.

Lemma mem_lessdef_sem_shift:
  forall m1 m2, mem_lessdef m1 m2 ->
  forall v1 v1', Val.lessdef v1 v1' ->
  forall v2 v2', Val.lessdef v2 v2' ->
  forall (sem_int: signedness -> int -> int -> int)
    (sem_long: signedness -> int64 -> int64 -> int64)
    (t1: type) (t2: type) v,
   sem_shift sem_int sem_long v1 t1 v2 t2 = Some v ->
   sem_shift sem_int sem_long v1' t1 v2' t2 = Some v.
Proof.
intros.
unfold sem_shift in *.
destruct (classify_shift t1 t2); auto;
destruct v1; inv H2; inv H0; destruct v2; inv H4; inv H1; reflexivity.
Qed.

Lemma mem_lessdef_cmp_ptr:
  forall m1 m2, mem_lessdef m1 m2 ->
  forall v1 v1', Val.lessdef v1 v1' ->
  forall v2 v2', Val.lessdef v2 v2' ->
  forall op v,
      cmp_ptr m1 op v1 v2 = Some v ->
      cmp_ptr m2 op v1' v2' = Some v.
Proof.
intros.
unfold cmp_ptr in *.
unfold Val.cmpu_bool, Val.cmplu_bool in *.
destruct Archi.ptr64;
destruct v1; inv H2; inv H0; destruct v2; inv H4; inv H1; try reflexivity; rewrite H2;
simpl in *;
repeat match type of H2 with
 | context [eq_block ?b ?b0] => destruct (eq_block b b0); [subst b0 |]; simpl in *; try discriminate
 | context [Int64.eq ?i ?z] => destruct (Int64.eq i z); simpl in *; try discriminate 
 | context [Mem.valid_pointer m1 ?b ?z] =>
    let H9 := fresh "H" in 
    destruct (Mem.valid_pointer m1 b z) eqn:H9; 
    [ rewrite (mem_lessdef_valid_pointer _ _ _ _ H H9) |  ]
end;
rewrite ?andb_false_r in H2;
try discriminate;
rewrite ?orb_true_r;
auto.
Qed.

Lemma mem_lessdef_sem_cmp:
  forall m1 m2, mem_lessdef m1 m2 ->
  forall v1 v1', Val.lessdef v1 v1' ->
  forall v2 v2', Val.lessdef v2 v2' ->
  forall op (t1: type) (t2: type) v,
      sem_cmp op v1 t1 v2 t2 m1 = Some v ->
      sem_cmp op v1' t1 v2' t2 m2 = Some v.
Proof.
intros.
unfold sem_cmp in *.
destruct (classify_cmp t1 t2).
* (* cmp_ptr *)
eapply mem_lessdef_cmp_ptr; eassumption.
*
destruct v2; try discriminate; inv H1.
eapply mem_lessdef_cmp_ptr; try eassumption; apply Val.lessdef_refl.
all: destruct Archi.ptr64; auto;
eapply mem_lessdef_cmp_ptr; try eassumption; apply Val.lessdef_refl.
*
destruct v1; try discriminate; inv H0.
eapply mem_lessdef_cmp_ptr; try eassumption; apply Val.lessdef_refl.
all: destruct Archi.ptr64; auto;
eapply mem_lessdef_cmp_ptr; try eassumption; apply Val.lessdef_refl.
*
destruct v2; try discriminate; inv H1.
eapply mem_lessdef_cmp_ptr; try eassumption; apply Val.lessdef_refl.
all: destruct Archi.ptr64; auto;
eapply mem_lessdef_cmp_ptr; try eassumption; apply Val.lessdef_refl.
*
destruct v1; try discriminate; inv H0.
eapply mem_lessdef_cmp_ptr; try eassumption; apply Val.lessdef_refl.
all: destruct Archi.ptr64; auto;
eapply mem_lessdef_cmp_ptr; try eassumption; apply Val.lessdef_refl.
*
eapply mem_lessdef_sem_binarith; eauto.
Qed.

Lemma classify_cast_void_e:
 forall t ty, classify_cast t ty = cast_case_void -> ty=Tvoid.
Proof.
intros.
   destruct t as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   destruct ty as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | | ];
   inv H; auto.
Qed.

Lemma mem_lessdef_eval_expr: forall ge ve te m1 m2 a v1,
   mem_lessdef m1 m2 ->
   eval_expr ge ve te m1 a v1 -> 
   exists v2, eval_expr ge ve te m2 a v2 /\ Val.lessdef v1 v2
 with mem_lessdef_eval_lvalue: forall ge ve te m1 m2 a b z,
   mem_lessdef m1 m2 ->
   eval_lvalue ge ve te m1 a b z -> 
   eval_lvalue ge ve te m2 a b z.
Proof.
*
clear mem_lessdef_eval_expr.
intros.
induction H0;
try solve [eexists; split; [ | eapply Val.lessdef_refl ]; econstructor; eauto].
destruct IHeval_expr as [vx [? ?]].
destruct op; simpl in H1.
 +
   exists v. split; [ | apply Val.lessdef_refl]. econstructor; simpl; eauto.
   clear - H1 H3 H.
   unfold sem_notbool, bool_val in *.
   destruct (classify_bool (typeof a)), v1; inv H1; inv H3; try reflexivity.
   destruct Archi.ptr64 eqn:Hp; inv H2.
   destruct (Mem.weak_valid_pointer m1 b (Ptrofs.unsigned i)) eqn:?; inv H1.
   rewrite (mem_lessdef_weak_valid_pointer _ _ _ _ H Heqb0). auto.
 +
   eexists; split; [ econstructor; eauto; simpl | ].
  unfold sem_notint in *.
  destruct (classify_notint (typeof a)); destruct v1; simpl in H1|-*; inv H1; inv H3; reflexivity.
  apply Val.lessdef_refl.
 +
   eexists; split; [ econstructor; eauto; simpl | ].
  unfold sem_neg in *.
  destruct (classify_neg (typeof a)); destruct v1; simpl in H1|-*; inv H1; inv H3; reflexivity.
  apply Val.lessdef_refl.
 +
   eexists; split; [ econstructor; eauto; simpl | ].
  unfold sem_absfloat in *.
  destruct (classify_neg (typeof a)); destruct v1; simpl in H1|-*; inv H1; inv H3; reflexivity.
  apply Val.lessdef_refl.
 +
   destruct IHeval_expr1 as [?v [? ?]].
   destruct IHeval_expr2 as [?v [? ?]].
   rename v0 into v1'. rename v3 into v2'.
   exists v; split; [ | apply Val.lessdef_refl].
   econstructor; try eassumption.
   clear - H0 H2 H4 H.
   destruct op; simpl in *;
   try solve [eapply mem_lessdef_sem_binarith; eauto];
   try solve [eapply mem_lessdef_sem_cmp; eauto].
   - 
     unfold sem_add in *. destruct (classify_add (typeof a1) (typeof a2)).
     destruct v1; inv H0; inv H2; destruct v2; inv H3; inv H4; reflexivity.
     destruct v1; inv H0; inv H2; destruct v2; inv H3; inv H4; reflexivity.
     destruct v1; inv H0; inv H2; destruct v2; inv H3; inv H4; reflexivity.
     destruct v1; inv H0; inv H2; destruct v2; inv H3; inv H4; reflexivity.
     eapply mem_lessdef_sem_binarith; eauto.
  - 
     unfold sem_sub in *. destruct (classify_sub (typeof a1) (typeof a2)).
     destruct v1; inv H0; inv H2; destruct v2; inv H3; inv H4; reflexivity.
     destruct v1; inv H0; inv H2; destruct v2; inv H3; inv H4; reflexivity.
     destruct v1; inv H0; inv H2; destruct v2; inv H3; inv H4; reflexivity.
     eapply mem_lessdef_sem_binarith; eauto.
  -
     eapply mem_lessdef_sem_shift; eauto.
  -
     eapply mem_lessdef_sem_shift; eauto.
 +   
   destruct IHeval_expr as [v1' [? ?]].
   destruct (eq_dec ty Tvoid).
   **
   subst ty. inv H1.
   exists v1'. split. subst. econstructor; eauto. auto.
   **
   apply (mem_lessdef_sem_cast _ _ H _ _ H3) in H1.
   exists v. split. econstructor; eauto. apply Val.lessdef_refl.
   clear - n. contradict n.
   eapply classify_cast_void_e; eauto.
 +
   eapply mem_lessdef_eval_lvalue in H0; eauto.
   inv H1.
   2: eexists; split; [eapply eval_Elvalue; eauto; econstructor 2; eassumption | apply Val.lessdef_refl].
   2: eexists; split; [eapply eval_Elvalue; eauto; econstructor 3; eassumption | apply Val.lessdef_refl].
   unfold Mem.loadv in *.
   pose proof (Mem.load_valid_access _ _ _ _ _ H3).
   destruct H1 as [_ ?].
   destruct H as [? _].
   apply Mem.load_loadbytes in H3.
   destruct H3 as [bytes [? ?]]. apply H in H3.
   destruct H3 as [v' [? ?]].
   apply Mem.loadbytes_load in H3; auto.
   subst.
   exists (decode_val chunk v').
   split.
   eapply eval_Elvalue; eauto.
   econstructor 1; eauto.
   clear - H5.
   apply mem_lessdef_decode_val; auto.
*
clear mem_lessdef_eval_lvalue.
intros.
induction H0.
constructor 1; auto.
constructor 2; auto.
eapply mem_lessdef_eval_expr in H0; eauto.
destruct H0 as [v2 [? ?]].
inv H1.
econstructor; eauto.
eapply mem_lessdef_eval_expr in H0; eauto.
destruct H0 as [v2 [? ?]].
inv H4.
econstructor 4; eauto.
eapply mem_lessdef_eval_expr in H0; eauto.
destruct H0 as [v2 [? ?]].
inv H3.
econstructor 5; eauto.
Qed.

Lemma unaryop_mem_lessaloc {op u t m v m2}
      (V: sem_unary_operation op u t m = Some v)
      (M:mem_lessalloc m m2):
      sem_unary_operation op u t m2 = Some v.
Proof. destruct op; simpl; inv V; try econstructor.
unfold sem_notbool.
unfold bool_val.
remember (classify_bool t) as c.
destruct c; trivial.
destruct u; trivial.
rewrite (weak_valid_pointer_lessalloc M); trivial.
Qed.

Lemma sem_cast_mem_lessaloc {v t d m m2} (M:mem_lessalloc m m2):
      sem_cast v t d m = sem_cast v t d m2.
Proof.
unfold sem_cast.
destruct (classify_cast t d); trivial.
destruct v; trivial.
rewrite (weak_valid_pointer_lessalloc M); trivial.
Qed.

Lemma sem_cmp_mem_lessalloc {f v1 t1 v2 t2 m m2} (M : mem_lessalloc m m2):
      sem_cmp f v1 t1 v2 t2 m2 = sem_cmp f v1 t1 v2 t2 m.
Proof. unfold sem_cmp, cmp_ptr.
  destruct (classify_cmp t1 t2);
  try solve [destruct Archi.ptr64; rewrite (valid_pointer_lessalloc M); trivial].
 unfold sem_binarith.
    do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
Qed.

Lemma binaryop_mem_lessaloc {ge op v1 t1 v2 t2 m v m2}
      (V: sem_binary_operation ge op v1 t1 v2 t2 m = Some v)
      (M:mem_lessalloc m m2):
      sem_binary_operation ge op v1 t1 v2 t2 m2 = Some v.
Proof. destruct op; simpl; inv V; try econstructor; clear -M.
+ unfold sem_add.
  remember (classify_add t1 t2) as c.
  destruct c.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - unfold sem_binarith.
    do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_sub.
  remember (classify_sub t1 t2) as c.
  destruct c.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - unfold sem_binarith.
    do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_mul.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_div.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_mod.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_and.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_or.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_xor.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_cmp, cmp_ptr.
  destruct (classify_cmp t1 t2);
  try solve [destruct Archi.ptr64; rewrite (valid_pointer_lessalloc M); trivial].
 unfold sem_binarith.
    do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ apply (sem_cmp_mem_lessalloc M).
+ apply (sem_cmp_mem_lessalloc M).
+ apply (sem_cmp_mem_lessalloc M).
+ apply (sem_cmp_mem_lessalloc M).
+ apply (sem_cmp_mem_lessalloc M).
Qed.

Lemma eval_expr_eval_lvalue_mem_lessalloc ge ve te m:
     (forall (e : expr) (v : val),
        eval_expr ge ve te m e v ->
        forall m2 : mem, mem_lessalloc m m2 -> eval_expr ge ve te m2 e v) /\
     (forall (e : expr) (b : block) (i : ptrofs),
        eval_lvalue ge ve te m e b i ->
        forall m2 : mem, mem_lessalloc m m2 -> eval_lvalue ge ve te m2 e b i).
Proof. apply eval_expr_lvalue_ind; intros; try solve [econstructor; eauto].
+ econstructor; eauto. eapply unaryop_mem_lessaloc; eauto.
+ econstructor; eauto. eapply binaryop_mem_lessaloc; eauto.
+ econstructor; eauto. rewrite <- H1. symmetry. apply sem_cast_mem_lessaloc; trivial.
+ econstructor; eauto.
  destruct H2 as [M1 [M2 M3]].
  inv H1; simpl in *.
  - eapply deref_loc_value; eauto.
    simpl. destruct (Mem.load_loadbytes _ _ _ _ _ H3) as [vals [X Y]]; subst.
    rewrite M1 in X. apply Mem.load_valid_access in H3. destruct H3.
    eapply Mem.loadbytes_load; trivial.
  - apply deref_loc_reference; trivial.
  - apply deref_loc_copy; trivial.
Qed.

Lemma eval_expr_mem_lessalloc {ge ve te m m2 e v} (M:mem_lessalloc m m2):
      eval_expr ge ve te m e v -> eval_expr ge ve te m2 e v.
Proof. intros. eapply eval_expr_eval_lvalue_mem_lessalloc; eauto. Qed.

Lemma eval_exprlist_mem_lessalloc {ge ve te}:
      forall al tyargs vargs m m2 (M:mem_lessalloc m m2)
             (E:eval_exprlist ge ve te m al tyargs vargs),
      eval_exprlist ge ve te m2 al tyargs vargs.
Proof.
  induction al; simpl; intros; inv E.
   econstructor.
   apply (eval_expr_mem_lessalloc M) in H1.
   rewrite (sem_cast_mem_lessaloc M) in H2. econstructor; eauto.
Qed.

Lemma eval_lvalue_mem_lessalloc {ge ve te m m2 e b i} (M:mem_lessalloc m m2):
      eval_lvalue ge ve te m e b i -> eval_lvalue ge ve te m2 e b i.
Proof. intros. eapply eval_expr_eval_lvalue_mem_lessalloc; eauto. Qed.

(* Currently fails because jsafeN__ind is too weak.

Lemma jsafeN_mem_equiv {Z Jspec ge n z c jm1 jm2} :
  juicy_mem_equiv jm1 jm2 ->
  ext_spec_stable juicy_mem_equiv (JE_spec _ Jspec) ->
  @jsafeN Z Jspec ge n z c jm1 ->
  @jsafeN Z Jspec ge n z c jm2.
Proof. intros; eapply jsafeN__mem_equiv; eauto. Qed. should do it;
explicit proof attempt:
  unfold jsafeN in *.
  intros E [Spre Sexit] S1.
  revert jm2 E. unfold jsafeN in *.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 E.

  - constructor 1.

  - destruct (juicy_step_mem_equiv_sim E step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.

  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct E as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.

  - econstructor 4; eauto.
Qed.

Lemma jsafeN_mem_lessdef {Z Jspec ge n z c jm1 jm2} :
  juicy_mem_lessdef jm1 jm2 ->
  ext_spec_stable juicy_mem_lessdef (JE_spec _ Jspec) ->
  @jsafeN Z Jspec ge n z c jm1 ->
  @jsafeN Z Jspec ge n z c jm2.
Proof. intros; eapply jsafeN__mem_lessdef; eauto. Qed. should do it;
explicit proof attempt:
  intros L [Spre Sexit] S1.
  revert jm2 L.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 L.

  - constructor 1.

  - destruct (juicy_step_mem_lessdef_sim L step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.

  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct L as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.

  - econstructor 4; eauto.
Qed.*)