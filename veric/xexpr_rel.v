Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Export veric.lift.
Require Export veric.Cop2.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.res_predicates.
Require Import veric.extend_tc.
Require Import veric.seplog.

(* Why we need l_value/r_value instead of using expr directly?
Because we cannot represent Vptr constant in expr. *)

Inductive l_value : Type :=
  | L_var : ident -> type -> l_value
  | L_deref : r_value -> l_value
  | L_field : l_value -> type -> ident -> l_value
  | L_ilegal : expr -> l_value
with r_value : Type :=
  | R_const : val -> r_value
  | R_tempvar : ident -> r_value
  | R_addrof : l_value -> r_value
  | R_unop : Cop.unary_operation -> r_value -> type -> r_value
  | R_binop : Cop.binary_operation -> r_value -> type -> r_value -> type -> r_value
  | R_cast : r_value -> type -> type -> r_value
  | R_byref : l_value -> r_value
  | R_load : l_value -> type -> r_value
  | R_ilegal : expr -> r_value.

Fixpoint compute_r_value {cs: compspecs} (e: expr) : r_value :=
  match e with
  | Econst_int i ty => R_const (Vint i)
  | Econst_long i ty => R_const (Vlong i)
  | Econst_float f ty => R_const (Vfloat f)
  | Econst_single f ty => R_const (Vsingle f)
  | Etempvar id ty => R_tempvar id
  | Eaddrof a ty => R_addrof (compute_l_value a)
  | Eunop op a ty => R_unop op (compute_r_value a) (typeof a)
  | Ebinop op a1 a2 ty => if binop_stable cenv_cs op a1 a2
                          then R_binop op (compute_r_value a1) (typeof a1) (compute_r_value a2) (typeof a2)
                          else R_ilegal e
  | Ecast a ty => R_cast (compute_r_value a) (typeof a) ty
  | Evar id ty => match access_mode ty with
                  | By_reference => R_byref (L_var id ty)
                  | By_value _ => R_load (L_var id ty) ty
                  | _ => R_ilegal e
                  end
  | Ederef a ty => match access_mode ty with
                   | By_reference => R_byref (L_deref (compute_r_value a))
                   | By_value _ => R_load (L_deref (compute_r_value a)) ty
                   | _ => R_ilegal e
                   end
  | Efield a i ty => match access_mode ty with
                     | By_reference => R_byref (L_field (compute_l_value a) (typeof a) i)
                     | By_value _ => R_load (L_field (compute_l_value a) (typeof a) i) ty
                     | _ => R_ilegal e
                     end
  | Esizeof t ty => R_const (Vint (Int.repr (sizeof cenv_cs t)))
  | Ealignof t ty => R_const (Vint (Int.repr (alignof cenv_cs t)))
  end
with compute_l_value {cs: compspecs} (e:expr) : l_value := 
  match e with
  | Evar id ty => L_var id ty
  | Ederef a ty => L_deref (compute_r_value a)
  | Efield a i ty => L_field (compute_l_value a) (typeof a) i
  | _ => L_ilegal e
  end.

Inductive rel_r_value' {CS: compspecs} (rho: environ) (phi: rmap): r_value -> val -> Prop :=
 | rel_r_value'_const: forall v, 
                 rel_r_value' rho phi (R_const v) v
 | rel_r_value'_tempvar: forall id v,
                 Map.get (te_of rho) id = Some v ->
                 rel_r_value' rho phi (R_tempvar id) v
 | rel_r_value'_addrof: forall a v,
                 rel_l_value' rho phi a v ->
                 rel_r_value' rho phi (R_addrof a) v
 | rel_r_value'_unop: forall a ta v1 v op,
                 rel_r_value' rho phi a v1 ->
                 (forall m, Cop.sem_unary_operation op v1 ta m = Some v) ->
                 rel_r_value' rho phi (R_unop op a ta) v
 | rel_r_value'_binop: forall a1 ta1 a2 ta2 v1 v2 v op,
                 rel_r_value' rho phi a1 v1 ->
                 rel_r_value' rho phi a2 v2 ->
                 (forall m, Cop.sem_binary_operation cenv_cs op v1 ta1 v2 ta2 m = Some v) ->
                 rel_r_value' rho phi (R_binop op a1 ta1 a2 ta2) v
 | rel_r_value'_cast: forall a ta v1 v ty,
                 rel_r_value' rho phi a v1 ->
                 Cop.sem_cast v1 ta ty = Some v ->
                 rel_r_value' rho phi (R_cast a ta ty) v
 | rel_r_value'_byref: forall a v1,
                 rel_l_value' rho phi a v1 ->
                 rel_r_value' rho phi (R_byref a) v1
 | rel_r_value'_load: forall a ty sh v1 v2,
                 rel_l_value' rho phi a v1 ->
                 app_pred ((mapsto sh ty v1 v2) * TT) phi ->
                 v2 <> Vundef ->
                 readable_share sh ->
                 rel_r_value' rho phi (R_load a ty) v2
with rel_l_value' {CS: compspecs} (rho: environ) (phi: rmap): l_value -> val -> Prop :=
 | rel_r_value'_local: forall id ty b,
                 Map.get (ve_of rho) id = Some (b,ty) ->
                 rel_l_value' rho phi (L_var id ty) (Vptr  b Int.zero)
 | rel_r_value'_global: forall id ty b,
                 Map.get (ve_of rho) id = None ->
                 Map.get (ge_of rho) id = Some b ->
                 rel_l_value' rho phi (L_var id ty) (Vptr b Int.zero)
 | rel_l_value'_deref: forall a b z,
                 rel_r_value' rho phi a (Vptr b z) ->
                 rel_l_value' rho phi (L_deref a) (Vptr b z)
 | rel_l_value'_field_struct: forall i a ta b z id co att delta,
                 rel_l_value' rho phi a (Vptr b z) ->
                 ta = Tstruct id att ->
                 cenv_cs ! id = Some co ->
                 field_offset cenv_cs i (co_members co) = Errors.OK delta ->
                 rel_l_value' rho phi (L_field a ta i) (Vptr b (Int.add z (Int.repr delta))).

Scheme rel_r_value'_sch := Minimality for rel_r_value' Sort Prop
  with rel_l_value'_sch := Minimality for rel_l_value' Sort Prop.

Definition rel_LR_value'_sch := fun CS rho phi P P0 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 => conj (rel_r_value'_sch CS rho phi P P0 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10) (rel_l_value'_sch CS rho phi P P0 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10).

Lemma rel_r_value'_hered: forall {CS }e v rho, hereditary age (fun phi => @rel_r_value' CS rho phi e v).
Proof.
intros.
intro; intros.
apply (rel_r_value'_sch _ rho a (rel_r_value' rho a') (rel_l_value' rho a'));
  intros;
  try solve [econstructor; eauto; auto].
  eapply rel_r_value'_load; eauto.
  eapply pred_hereditary; eassumption.
  eapply rel_r_value'_global; eauto. auto.
Qed.

Lemma rel_l_value'_hered: forall {CS} e v rho, hereditary age (fun phi => @rel_l_value' CS rho phi e v).
Proof.
intros.
intro; intros.
induction H0; try solve [ econstructor; eauto].
 constructor 2; auto.
 constructor 3; auto.
apply rel_r_value'_hered with a; auto.
Qed.

Program Definition rel_r_value {CS: compspecs} (e: r_value) (v: val) (rho: environ) : pred rmap :=
    fun phi => rel_r_value' rho phi e v.
Next Obligation. intros. apply rel_r_value'_hered. Defined.

Program Definition rel_l_value {CS: compspecs} (e: l_value) (v: val) (rho: environ) : pred rmap :=
    fun phi => rel_l_value' rho phi e v.
Next Obligation. intros. apply rel_l_value'_hered. Defined.

Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.expr_lemmas.

Lemma compute_byref_spec: forall {CS: compspecs} e' e,
  compute_r_value e' = R_byref e ->
  compute_l_value e' = e /\ access_mode (typeof e') = By_reference.
Proof.
  intros.
  destruct e';
  try solve [inv H];
  simpl in H; try solve [if_tac in H; inv H];
  destruct (access_mode t) eqn:HH; inv H;
  simpl; rewrite HH; eauto.
Qed.

Lemma compute_load_spec: forall {CS: compspecs} e' e t,
  compute_r_value e' = R_load e t ->
  compute_l_value e' = e /\ typeof e' = t /\ exists ch, access_mode t = By_value ch.
Proof.
  intros.
  destruct e';
  try solve [inv H];
  simpl in H; try solve [if_tac in H; inv H];
  destruct (access_mode t0) eqn:HH; inv H;
  rewrite HH; simpl; eauto.
Qed.

Lemma rel_lr_value_relate:
  forall {CS: compspecs} ge te ve rho jm,
    genv_cenv ge = cenv_cs ->
    rho = construct_rho (filter_genv ge) ve te ->
    (forall e v,
           rel_r_value e v rho (m_phi jm) ->
     forall e',
           compute_r_value e' = e ->
           Clight.eval_expr ge ve te (m_dry jm) e' v) /\
    (forall e v,
           rel_l_value e v rho (m_phi jm) ->
     forall e',
           compute_l_value e' = e ->
           match v with
           | Vptr b z => Clight.eval_lvalue ge ve te (m_dry jm) e' b z
           | _ => False
           end).
Proof.
Ltac tac H HH :=
  simpl in H;
  try match type of H with match ?A with _ => _ end = _ => destruct A eqn:HH end;
  inv H.
intros.
unfold rel_r_value, rel_l_value.
simpl.
apply (rel_LR_value'_sch _ rho (m_phi jm)
     (fun e v => forall e',
           compute_r_value e' = e ->
           Clight.eval_expr ge ve te (m_dry jm) e' v)
     (fun e v => forall e',
           compute_l_value e' = e ->
           match v with
           | Vptr b z => Clight.eval_lvalue ge ve te (m_dry jm) e' b z
           | _ => False
           end));
 intros; subst rho;
 match goal with
 | _: compute_r_value _ = R_byref _ |- _ => idtac
 | _: appcontext [mapsto] |- _ => idtac
 | _ =>
 destruct e';
 match goal with
 | H: compute_r_value _ = _ |- _ => tac H HH
 | H: compute_l_value _ = _ |- _ => tac H HH
 end
 end;
 try solve [econstructor; eauto].
* (* Esizeof *)
  rewrite <- H.
  eapply eval_Esizeof; eauto.
* (* Ealignof *)
  rewrite <- H.
  eapply eval_Ealignof; eauto.
* (* Eaddrof *)
  specialize (H2 e' eq_refl).
   destruct v; try contradiction. constructor; auto.
* (* Ebinop *)
  econstructor; eauto.
  rewrite H. auto.
* (* byref *)
  destruct (compute_byref_spec _ _ H3).
  specialize (H2 e' H0).
  destruct v1; try tauto.
  eapply eval_Elvalue; eauto.
  apply deref_loc_reference; auto.
* (* load *)
  destruct (compute_load_spec _ _ _ H6) as [? [? [? ?]]].
  specialize (H2 e' H0).
  destruct v1; try contradiction.
  eapply Clight.eval_Elvalue; eauto.
  destruct H3 as [m1 [m2 [? [? _]]]].
  unfold mapsto in H9.
  rewrite H8 in *.
  destruct (type_is_volatile ty) eqn:?; try contradiction.
  eapply deref_loc_value; [rewrite H7; eassumption |].
  unfold Mem.loadv.
  rewrite if_true in H9 by auto; clear H5.
  destruct H9 as [[_ ?] | [? _]]; [ | contradiction].
  apply core_load_load'.
  destruct H5 as [bl ?]; exists bl.
  destruct H5 as [H3' ?]; split; auto.
  clear H3'.
  intro b'; specialize (H5 b'). hnf in H5|-*.
  if_tac; auto.
  + destruct H5 as [p ?].
    hnf in H5. rewrite preds_fmap_NoneP in H5.
    apply (resource_at_join _ _ _ b') in H3.  
    rewrite H5 in H3; clear H5.
    inv H3.
    - symmetry in H15.
      exists rsh3, (Share.unrel Share.Rsh sh), p; assumption.
    - symmetry in H15.
      simpl.
      destruct sh3 as [sh3 p3].  exists rsh3, sh3, p3; auto.
  + apply I.
* (* Evar *)
  simpl in *.
  unfold Map.get, make_venv, filter_genv in H1,H2.
  destruct (Genv.find_symbol ge id) eqn:?; try discriminate.
  destruct (type_of_global ge b) eqn:?; inv H2;  apply Clight.eval_Evar_global; auto.
* (* Efield *)
  econstructor; eauto. 
  + eapply Clight.eval_Elvalue; eauto.
    apply deref_loc_copy.
    rewrite H8; auto.
  + rewrite H; eauto.
  + rewrite H; eauto.
Qed.

Lemma rel_r_value_relate:
  forall {CS: compspecs} ge te ve rho e' e jm v,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te ->
           rel_r_value e v rho (m_phi jm) ->
           compute_r_value e' = e ->
           Clight.eval_expr ge ve te (m_dry jm) e' v.
Proof.
  intros.
  apply (proj1 (rel_lr_value_relate ge te ve rho jm H H0) e); auto.
Qed.

Lemma rel_l_value_relate:
  forall {CS: compspecs}  ge te ve rho e' e jm b z,
           genv_cenv ge = cenv_cs ->
           rho = construct_rho (filter_genv ge) ve te ->
           rel_l_value e (Vptr b z) rho (m_phi jm) ->
           compute_l_value e' = e ->
           Clight.eval_lvalue ge ve te (m_dry jm) e' b z.
Proof.
  intros.
  apply ((proj2 (rel_lr_value_relate ge te ve rho jm H H0)) e (Vptr b z)); auto.
Qed.

Lemma sem_cast_load_result:
 forall v1 t1 t2 v2 ch,
  access_mode t1 = By_value ch ->
   Cop.sem_cast v1 t2 t1 = Some v2 ->
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
 simpl;
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
 apply Mem.load_result in H2; subst; simpl;
 match goal with 
  | |- context [decode_val _ (?x :: nil)] => destruct x; try reflexivity
  | |- context [decode_val _ (?x :: ?y :: nil)] => destruct x,y; try reflexivity
  | |- context [decode_val ?ch ?a] => destruct (decode_val ch a) eqn:?; try reflexivity
  | |- _ => idtac
 end;
  simpl;
  try rewrite Int.sign_ext_idem by omega;
  try rewrite Int.zero_ext_idem by omega;
  try reflexivity;
 try match type of Heqv with
  | decode_val _ (?a :: ?b :: ?c :: ?d :: nil) = _ =>
    destruct a; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct b; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct c; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct d; try solve [unfold decode_val in Heqv; inv Heqv];
   unfold decode_val in Heqv; inv Heqv;
  try (if_tac in H0; inv H0)
 | decode_val _ (?a :: ?b :: ?c :: ?d :: ?e :: ?f :: ?g :: ?h :: nil) = _ =>
    destruct a; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct b; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct c; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct d; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct e; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct f; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct g; try solve [unfold decode_val in Heqv; inv Heqv];
    destruct h; try solve [unfold decode_val in Heqv; inv Heqv]
 end;
 try solve [destruct v; inv H1; auto].
Qed.

Lemma rel_LR_value'_fun:
 forall {CS: compspecs} rho phi, (forall e v, rel_r_value' rho phi e v -> forall v', rel_r_value' rho phi e v' -> v=v') /\ (forall e v, rel_l_value' rho phi e v -> forall v', rel_l_value' rho phi e v' -> v=v').
Proof.
intros.
apply (rel_LR_value'_sch _ rho phi
      (fun e v => forall v', rel_r_value' rho phi e v' -> v=v')
      (fun e v => forall v', rel_l_value' rho phi e v' -> v=v'));
   auto; intros;
   try match goal with H : _ |- _ => inv H; auto; try congruence end;
   try match goal with H: rel_l_value' _ _ _ _ |- _ => solve [inv H] end.
* (* Eunop *)
   specialize (H0 _ H7). specialize (H8 Mem.empty). congruence.
* (* Ebinnop *)
   specialize (H0 _ H11). specialize (H2 _ H12).
   specialize (H3 Mem.empty). specialize (H13 Mem.empty).
   congruence.
* (* Ecast *)
   specialize (H0 _ H7). congruence.
*  specialize (H0 _ H7).
   subst v0; clear H H7.
   generalize H1; intros [wx [wy [_ [? _]]]].
   unfold mapsto in *.
   destruct (access_mode ty); try contradiction.
   destruct (type_is_volatile ty); try contradiction.
   destruct v1; try contradiction.
   rewrite if_true in H, H1, H8 by auto.
   destruct H as [[? ?]|[? ?]]; [ |  hnf in H; contradiction].
   rewrite distrib_orp_sepcon in H1, H8.
   destruct H1 as [H1 |[? [? [? [[Hx _] _]]]]]; [ | hnf in Hx; contradiction].
   destruct H8 as [H8 |[? [? [? [[Hx _] _]]]]]; [ | hnf in Hx; contradiction].
   autorewrite with normalize in H1, H8; auto with typeclass_instances.
   destruct H8.
   eapply res_predicates.address_mapsto_fun; split; eauto.
*
   specialize (H0 _ H8). congruence.
Qed.

Lemma rel_r_value'_fun:
 forall {CS: compspecs} rho phi e v v', rel_r_value' rho phi e v -> rel_r_value' rho phi e v' -> v=v'.
Proof.
intros.
pose proof rel_LR_value'_fun rho phi.
firstorder.
Qed.

Lemma rel_l_value'_fun:
 forall {CS: compspecs} rho phi e v v', rel_l_value' rho phi e v -> rel_l_value' rho phi e v' -> v=v'.
Proof.
intros.
pose proof rel_LR_value'_fun rho phi.
firstorder.
Qed.

Lemma rel_LR_value_extend:
  forall {CS: compspecs} rho w,
    (forall e v, rel_r_value' rho w e v -> forall w', extendM w w' -> rel_r_value' rho w' e v) /\
    (forall e v, rel_l_value' rho w e v -> forall w', extendM w w' -> rel_l_value' rho w' e v).
Proof.
intros.
apply (rel_LR_value'_sch _ rho w
      (fun e v => forall w', extendM w w' -> rel_r_value' rho w' e v)
      (fun e v => forall w', extendM w w' -> rel_l_value' rho w' e v)); auto; intros;
  try solve [match goal with H : _ |- _ => inv H; econstructor; eauto end];
  try solve [match goal with H: forall w': compcert_rmaps.R.rmap, _ |- _ => specialize (H w'); spec H; [auto | econstructor; eauto]
end].
*
eapply rel_r_value'_load; eauto.
destruct H4 as [w1 ?].
destruct H1 as [w3 [w4 [? [? _]]]].
destruct (join_assoc H1 H4) as [w6 [? ?]].
exists w3, w6; split3; auto.
*
econstructor 2; eauto.
Qed.

Lemma rel_r_value_extend:
  forall {CS: compspecs} e v rho, boxy extendM (rel_r_value e v rho).
Proof.
intros. apply boxy_i; intros; auto.
hnf in H0|-*.
pose proof rel_LR_value_extend rho w.
firstorder.
Qed.

Lemma rel_l_value_extend:
  forall {CS: compspecs} e v rho, boxy extendM (rel_l_value e v rho).
Proof.
intros. apply boxy_i; intros; auto.
hnf in H0|-*.
pose proof rel_LR_value_extend rho w.
firstorder.
Qed.