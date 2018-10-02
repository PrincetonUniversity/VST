Require Import VST.msl.msl_standard.
Require Import VST.veric.Clight_base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Export VST.veric.lift.
Require Export VST.veric.Cop2.
Require Import VST.veric.mpred. 
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.

Inductive rel_expr' {CS: compspecs} (rho: environ) (phi: rmap): expr -> val -> Prop :=
 | rel_expr'_const_int: forall i ty,
                 rel_expr' rho phi (Econst_int i ty) (Vint i)
 | rel_expr'_const_float: forall f ty,
                 rel_expr' rho phi (Econst_float f ty) (Vfloat f)
 | rel_expr'_const_single: forall f ty,
                 rel_expr' rho phi (Econst_single f ty) (Vsingle f)
 | rel_expr'_const_long: forall i ty,
                 rel_expr' rho phi (Econst_long i ty) (Vlong i)
 | rel_expr'_tempvar: forall id ty v,
                 Map.get (te_of rho) id = Some v ->
                 rel_expr' rho phi (Etempvar id ty) v
 | rel_expr'_addrof: forall a ty v,
                 rel_lvalue' rho phi a v ->
                 rel_expr' rho phi (Eaddrof a ty) v
 | rel_expr'_unop: forall a v1 v ty op,
                 rel_expr' rho phi a v1 ->
                 (forall m, Cop.sem_unary_operation op v1 (typeof a) m = Some v) ->
                 rel_expr' rho phi (Eunop op a ty) v
 | rel_expr'_binop: forall a1 a2 v1 v2 v ty op,
                 rel_expr' rho phi a1 v1 ->
                 rel_expr' rho phi a2 v2 ->
                 binop_stable cenv_cs op a1 a2 = true ->
                 (forall m, Cop.sem_binary_operation cenv_cs op v1 (typeof a1) v2 (typeof a2) m = Some v) ->
                 rel_expr' rho phi (Ebinop op a1 a2 ty) v
 | rel_expr'_cast: forall a v1 v ty,
                 rel_expr' rho phi a v1 ->
                 (forall m, Cop.sem_cast v1 (typeof a) ty m = Some v) ->
                 rel_expr' rho phi (Ecast a ty) v
 | rel_expr'_sizeof: forall t ty,
                 complete_type cenv_cs t = true ->
                 rel_expr' rho phi (Esizeof t ty) (Vptrofs (Ptrofs.repr (sizeof t)))
 | rel_expr'_alignof: forall t ty,
                 complete_type cenv_cs t = true ->
                 rel_expr' rho phi (Ealignof t ty) (Vptrofs (Ptrofs.repr (alignof t)))
 | rel_expr'_lvalue_By_value: forall a ch sh v1 v2,
                 access_mode (typeof a) = By_value ch ->
                 rel_lvalue' rho phi a v1 ->
                 app_pred (mapsto sh (typeof a) v1 v2 * TT ) phi ->
                 v2 <> Vundef ->
                 readable_share sh ->
                 rel_expr' rho phi a v2
 | rel_expr'_lvalue_By_reference: forall a v1,
                 access_mode (typeof a) = By_reference ->
                 rel_lvalue' rho phi a v1 ->
                 rel_expr' rho phi a v1
with rel_lvalue' {CS: compspecs} (rho: environ) (phi: rmap): expr -> val -> Prop :=
 | rel_expr'_local: forall id ty b,
                 Map.get (ve_of rho) id = Some (b,ty) ->
                 rel_lvalue' rho phi (Evar id ty) (Vptr  b Ptrofs.zero)
 | rel_expr'_global: forall id ty b,
                 Map.get (ve_of rho) id = None ->
                 Map.get (ge_of rho) id = Some b ->
                 rel_lvalue' rho phi (Evar id ty) (Vptr b Ptrofs.zero)
 | rel_lvalue'_deref: forall a b z ty,
                 rel_expr' rho phi a (Vptr b z) ->
                 rel_lvalue' rho phi (Ederef a ty) (Vptr b z)
 | rel_lvalue'_field_struct: forall i ty a b z id co att delta,
                 rel_lvalue' rho phi a (Vptr b z) ->
                 typeof a = Tstruct id att ->
                 cenv_cs ! id = Some co ->
                 field_offset cenv_cs i (co_members co) = Errors.OK delta ->
                 rel_lvalue' rho phi (Efield a i ty) (Vptr b (Ptrofs.add z (Ptrofs.repr delta))).

Scheme rel_expr'_sch := Minimality for rel_expr' Sort Prop
  with rel_lvalue'_sch := Minimality for  rel_lvalue' Sort Prop.

Definition rel_LR'_sch := fun CS rho phi P P0 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 e v => conj (rel_expr'_sch CS rho phi P P0 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 e v) (rel_lvalue'_sch CS rho phi P P0 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 e v).

Lemma rel_expr'_hered: forall {CS }e v rho, hereditary age (fun phi => @rel_expr' CS rho phi e v).
Proof.
intros.
intro; intros.
apply (rel_expr'_sch _ rho a (rel_expr' rho a') (rel_lvalue' rho a'));
  intros;
  try solve [econstructor; eauto].
  eapply rel_expr'_lvalue_By_value; eauto.
  eapply pred_hereditary; eassumption.
assumption.
Qed.

Lemma rel_lvalue'_hered: forall {CS} e v rho, hereditary age (fun phi => @rel_lvalue' CS rho phi e v).
Proof.
intros.
intro; intros.
induction H0; try solve [ econstructor; eauto].
constructor.
apply rel_expr'_hered with a; auto.
Qed.

Program Definition rel_expr {CS: compspecs} (e: expr) (v: val) (rho: environ) : pred rmap :=
    fun phi => rel_expr' rho phi e v.
Next Obligation. intros. apply rel_expr'_hered. Defined.

Program Definition rel_lvalue {CS: compspecs}  (e: expr) (v: val) (rho: environ) : pred rmap :=
    fun phi => rel_lvalue' rho phi e v.
Next Obligation. intros. apply rel_lvalue'_hered. Defined.

Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.expr_lemmas.

Definition rel_lvalue'_expr'_sch CS rho phi P P0 :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 =>
  conj (rel_expr'_sch CS rho phi P P0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)
       (rel_lvalue'_sch CS rho phi P P0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17).

Lemma rel_lvalue_expr_relate:
  forall {CS: compspecs} ge te ve rho jm,
    genv_cenv ge = cenv_cs ->
    rho = construct_rho (filter_genv ge) ve te ->
    (forall e v,
           rel_expr e v rho (m_phi jm) ->
           Clight.eval_expr ge ve te (m_dry jm) e v) /\
    (forall e v,
           rel_lvalue e v rho (m_phi jm) ->
           match v with
           | Vptr b z => Clight.eval_lvalue ge ve te (m_dry jm) e b z
           | _ => False
           end).
Proof.
intros.
unfold rel_expr, rel_lvalue.
simpl.
apply (rel_lvalue'_expr'_sch _ rho (m_phi jm)
     (Clight.eval_expr ge ve te (m_dry jm))
     (fun e v =>
      match v with
      | Vptr b z => Clight.eval_lvalue ge ve te (m_dry jm) e b z
      | _ => False end));
 intros; subst rho; try solve [econstructor; eauto].
* (* Eaddrof *)
   destruct v; try contradiction. constructor; auto.
* (* Ebinop *)
  econstructor; eauto.
  rewrite H. auto.
* (* Esizeof *)
  rewrite <- H.  constructor.
* (* Ealignof *)
  unfold alignof; rewrite <- H. constructor.
* (* lvalue *)
  destruct v1; try contradiction.
  eapply Clight.eval_Elvalue; eauto.
  destruct H4 as [m1 [m2 [? [? _]]]].
  unfold mapsto in H4.
  rewrite H1 in *.
  destruct (type_is_volatile (typeof a)) eqn:?; try contradiction.
  eapply deref_loc_value; try eassumption.
  unfold Mem.loadv.
  rewrite if_true in H4 by auto; clear H6.
  destruct H4 as [[_ ?] | [? _]]; [ | contradiction].
  apply core_load_load'.
  destruct H4 as [bl ?]; exists bl.
  destruct H4 as [[H3' ?] Hg]; split; auto.
  clear H3'.
  intro b'; specialize (H4 b'). hnf in H4|-*.
  if_tac; auto.
  + destruct H4 as [p ?].
    hnf in H4. rewrite preds_fmap_NoneP in H4.
    apply (resource_at_join _ _ _ b') in H0.
    rewrite H4 in H0; clear H4.
    inv H0.
    - symmetry in H11. do 2 eexists; eassumption.
    - symmetry in H11; do 2 eexists; eassumption.
  + apply I.
* (* lvalue By_reference *)
   destruct v1; try contradiction.
  eapply Clight.eval_Elvalue; eauto.
    eapply deref_loc_reference; try eassumption.
* (* Efield *)
  econstructor; eauto.
  + eapply Clight.eval_Elvalue; eauto.
    apply deref_loc_copy.
    rewrite H3; auto.
  + rewrite H; eauto.
  + rewrite H; eauto.
Qed.

Lemma rel_expr_relate:
  forall {CS: compspecs} ge te ve rho e jm v,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te ->
           rel_expr e v rho (m_phi jm) ->
           Clight.eval_expr ge ve te (m_dry jm) e v.
Proof.
  intros.
  apply (proj1 (rel_lvalue_expr_relate ge te ve rho jm H H0)).
  auto.
Qed.

Lemma rel_lvalue_relate:
  forall {CS: compspecs}  ge te ve rho e jm b z,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te ->
           rel_lvalue e (Vptr b z) rho (m_phi jm) ->
           Clight.eval_lvalue ge ve te (m_dry jm) e b z.
Proof.
  intros.
  apply ((proj2 (rel_lvalue_expr_relate ge te ve rho jm H H0)) e (Vptr b z)).
  auto.
Qed.

Lemma sem_cast_load_result:
 forall v1 t1 t2 v2 ch m,
  access_mode t1 = By_value ch ->
(*  Clight.eval_expr ge ve te m e2 v1 -> *)
   Cop.sem_cast v1 t2 t1 m = Some v2 ->
  Val.load_result ch v2 = v2.
Proof.
intros.
unfold Cop.sem_cast in H0.

destruct t1 as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
destruct t2 as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
inv H; try reflexivity;
 simpl in H0; try discriminate;
 destruct v1; inv H0;
  try invSome;
  unfold cast_int_int;
  destruct Archi.ptr64 eqn:Hp;
  try discriminate;
  simpl in *;
 try match goal with
  | H: (if Mem.weak_valid_pointer ?M ?B ?X then _ else _) = _ |- _ =>
      destruct (Mem.weak_valid_pointer M B X); inv H
  end;
 try  rewrite Int.sign_ext_idem by omega;
 try  rewrite Int.zero_ext_idem by omega;
 try reflexivity;
 try match goal with
 | |- context [Int.eq ?i Int.zero] =>
  destruct (Int.eq i Int.zero) eqn:?; try reflexivity
 | |- context [Int64.eq ?i Int64.zero] =>
  destruct (Int64.eq i Int64.zero) eqn:?; try reflexivity
 | |- context [Float.cmp Ceq ?f Float.zero] =>
     destruct (Float.cmp Ceq f Float.zero) eqn:?; try reflexivity
 | |- context [Float32.cmp Ceq ?f Float32.zero] =>
     destruct (Float32.cmp Ceq f Float32.zero) eqn:?; try reflexivity
 end.
Qed.

Lemma deref_loc_load_result:
  forall t ch m loc ofs v2,
  access_mode t = By_value ch ->
  deref_loc t m loc ofs v2 ->
  Val.load_result ch v2 = v2.
Proof.
intros.
destruct t as [ | [ | | | ] [ | ] ? | [ | ] ? | [ | ] ? | | | | | ];
 inv H0; inversion2 H H1; inv H; unfold Mem.loadv in *;
 apply Mem.load_result in H2; subst;
 unfold Val.load_result, Mptr; 
 destruct Archi.ptr64 eqn:Hp; 
simpl Mem.getN; 
 match goal with
  | |- context [decode_val _ (?x :: nil)] => destruct x; try reflexivity
  | |- context [decode_val _ (?x :: ?y :: nil)] => destruct x,y; try reflexivity
  | |- context [decode_val _ (?a :: ?b :: ?c :: ?d :: nil)] => destruct a,b,c,d; try reflexivity
  | |- context [decode_val _ (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: ?g :: ?h :: nil)] => 
                destruct a,b,c,d,e,f,g,h; try reflexivity
 end;
  unfold decode_val, proj_bytes;
  try rewrite Int.sign_ext_idem by omega;
  try rewrite Int.zero_ext_idem by omega;
  try reflexivity; simpl;
  rewrite ?Hp; simpl; try reflexivity;
  repeat match goal with n: nat |- _ =>
     destruct n; try (rewrite !andb_false_r; reflexivity)
   end;
 try solve [simple_if_tac; destruct v; auto].
Qed.

Lemma rel_LR'_fun:
 forall {CS: compspecs} rho phi e v, (rel_expr' rho phi e v -> forall v', rel_expr' rho phi e v' -> v=v') /\ (rel_lvalue' rho phi e v -> forall v', rel_lvalue' rho phi e v' -> v=v').

intros.
apply (rel_LR'_sch _ rho phi
      (fun e v => forall v', rel_expr' rho phi e v' -> v=v')
      (fun e v => forall v', rel_lvalue' rho phi e v' -> v=v'));
   auto; intros;
   try match goal with H : _ |- _ => inv H; auto; try congruence end;
   try match goal with H: rel_lvalue' _ _ _ _ |- _ => solve [inv H] end.
* (* Eunop *)
   specialize (H0 _ H7). specialize (H8 Mem.empty). congruence.
* (* Ebinop *)
   specialize (H0 _ H10). specialize (H2 _ H12).
   specialize (H4 Mem.empty). specialize (H14 Mem.empty).
   congruence.
* (* Ecast *)
   specialize (H0 _ H5). specialize (H1 Mem.empty). congruence.
*  inversion2 H H6.
   specialize (H1 _ H7).
   subst v0.   clear H0 H7.
   generalize H2; intros [wx [wy [_ [? _]]]].
   unfold mapsto in *.
   destruct (access_mode (typeof a)); try contradiction.
   destruct (type_is_volatile (typeof a)); try contradiction.
   destruct v1; try contradiction.
   rewrite if_true in H0, H2, H8 by auto.
   destruct H0 as [[? ?]|[? ?]]; [ |  hnf in H0; contradiction].
   clear H1.
   rewrite distrib_orp_sepcon in H2, H8.
   destruct H2 as [H2 |[? [? [? [[Hx _] _]]]]]; [ | hnf in Hx; contradiction].
   destruct H8 as [H8 |[? [? [? [[Hx _] _]]]]]; [ | hnf in Hx; contradiction].
   autorewrite with normalize in H2, H8; auto with typeclass_instances.
   destruct H8.
   eapply res_predicates.address_mapsto_fun; split; eauto.
*
   specialize (H0 _ H8). congruence.
Qed.

Lemma rel_expr'_fun:
 forall {CS: compspecs} rho phi e v v', rel_expr' rho phi e v -> rel_expr' rho phi e v' -> v=v'.
Proof.
intros.
pose proof rel_LR'_fun rho phi e v.
firstorder.
Qed.

Lemma rel_lvalue'_fun:
 forall {CS: compspecs} rho phi e v v', rel_lvalue' rho phi e v -> rel_lvalue' rho phi e v' -> v=v'.
Proof.
intros.
pose proof rel_LR'_fun rho phi e v.
firstorder.
Qed.

Lemma rel_LR_extend:
  forall {CS: compspecs} e v rho w,
    (rel_expr' rho w e v -> forall w', extendM w w' -> rel_expr' rho w' e v) /\
    (rel_lvalue' rho w e v -> forall w', extendM w w' -> rel_lvalue' rho w' e v).
Proof.
intros.
apply (rel_LR'_sch _ rho w
      (fun e v => forall w', extendM w w' -> rel_expr' rho w' e v)
      (fun e v => forall w', extendM w w' -> rel_lvalue' rho w' e v)); auto; intros;
  try solve [match goal with H : _ |- _ => inv H; econstructor; eauto end];
  try solve [match goal with H: forall w': rmap, _ |- _ => specialize (H w'); spec H; [auto | econstructor; eauto]
end].
*
eapply rel_expr'_lvalue_By_value; eauto.
destruct H5 as [w1 ?].
destruct H2 as [w3 [w4 [? [? _]]]].
destruct (join_assoc H2 H5) as [w6 [? ?]].
exists w3, w6; split3; auto.
*
eapply rel_expr'_lvalue_By_reference; eauto.
*
econstructor 2; eauto.
Qed.

Lemma rel_expr_extend:
  forall {CS: compspecs} e v rho, boxy extendM (rel_expr e v rho).
Proof.
intros. apply boxy_i; intros; auto.
hnf in H0|-*.
pose proof rel_LR_extend e v rho w.
firstorder.
Qed.

Lemma rel_lvalue_extend:
  forall {CS: compspecs} e v rho, boxy extendM (rel_lvalue e v rho).
Proof.
intros. apply boxy_i; intros; auto.
hnf in H0|-*.
pose proof rel_LR_extend e v rho w.
firstorder.
Qed.

