Require Import VST.veric.Clight_base.
Require Import compcert.cfrontend.Clight.

Definition var_name (V: Type) (bdec: ident * globvar V) : ident :=
   fst bdec.

Definition no_dups (F V: Type) (fdecs: list (ident * F)) (bdecs: list (ident * globvar V)) : Prop :=
  list_norepet (map (@fst ident F) fdecs ++ map (@var_name V) bdecs).
Arguments no_dups [F V] _ _.

Lemma no_dups_inv:
  forall  (A V: Type) id f fdecs bdecs,
    no_dups ((id,f)::fdecs) bdecs ->
    no_dups fdecs bdecs /\
     ~ In id (map (@fst ident A) fdecs) /\
     ~ In id (map (@var_name V) bdecs).
Proof.
intros.
inversion H; clear H. subst.
repeat split.
apply H3.
intro; contradiction H2; apply in_or_app; auto.
intro; contradiction H2; apply in_or_app; auto.
Qed.
Arguments no_dups_inv [A V] _ _ _ _ _.


Lemma of_bool_Int_eq_e:
  forall i j, Val.of_bool (Int.eq i j) = Vtrue -> i = j.
Proof.
unfold Val.of_bool.
do 2 intro.
assert (if Int.eq i j then i=j else i<>j).
apply Int.eq_spec.
caseEq (Int.eq i j); intros.
rewrite H0 in H ; trivial.
inversion H1.
Qed.

Lemma eq_block_lem:
    forall (A: Set) a (b: A) c, (if eq_block a a then b else c) = b.
Proof.
intros.
unfold eq_block.
rewrite peq_true.
auto.
Qed.

Lemma signed_zero: Int.signed Int.zero = 0.
Proof. apply Int.signed_zero. Qed.

Lemma equiv_e1 : forall A B: Prop, A=B -> A -> B.
Proof.
intros.
rewrite <- H; auto.
Qed.
Arguments equiv_e1 [A B] _ _.

Lemma deref_loc_fun: forall {ty m b z bf v v'},
   Clight.deref_loc ty m b z bf v -> Clight.deref_loc ty m b z bf v' -> v=v'.
 Proof. intros.
  inv H; inv H0; try congruence.
  inv H1; inv H6; try congruence.
Qed.

Lemma eval_expr_lvalue_fun:
  forall ge e le m,
    (forall a v v', Clight.eval_expr ge e le m a v -> Clight.eval_expr ge e le m a v' -> v=v') /\
    (forall a b b' i i' bf bf', Clight.eval_lvalue ge e le m a b i bf -> Clight.eval_lvalue ge e le m a b' i' bf' ->
                               (b,i,bf)=(b',i',bf')).
Proof.
 intros.
 destruct (Clight.eval_expr_lvalue_ind ge e le m
   (fun a v =>  forall v', Clight.eval_expr ge e le m a v' -> v=v')
   (fun a b i bf => forall b' i' bf', Clight.eval_lvalue ge e le m a b' i' bf' -> (b,i,bf)=(b',i',bf')));
  simpl; intros;

  try solve [repeat
  match goal with
  |  H: eval_expr _ _ _ _ ?a _  |- _ => (is_var a; fail 1) || inv H
  | H: eval_lvalue _ _ _ _ ?a _ _ _ |- _  => (is_var a; fail 1) || inv H
  end; congruence].

 * inv H1. apply H0 in H5; congruence. inv H2.
 * inv H2. apply H0 in H7; congruence. inv H3.
 * inv H4. apply H0 in H10. apply H2 in H11. congruence. inv H5.
 * inv H2. apply H0 in H5. congruence. inv H4. inv H3. inv H3. inv H3. inv H3.
 * inv H; inv H2; apply H0 in H; inv H;
    try (eapply deref_loc_fun; eauto).
 * inv H1. apply H0 in H7. congruence.
 * inv H4. apply H0 in H8. congruence. congruence.
 * inv H4. apply H0 in H8. congruence. apply H0 in H8. congruence.

 * split; intros; [apply (H _ _ H1 _ H2) | apply (H0 _ _ _ _ H1 _ _ _ H2)].
Qed.

Lemma eval_expr_fun:   forall {ge e le m a v v'},
    Clight.eval_expr ge e le m a v -> Clight.eval_expr ge e le m a v' -> v=v'.
Proof.
  intros. destruct (eval_expr_lvalue_fun ge e le m).
  eauto.
Qed.

Lemma eval_exprlist_fun:   forall {ge e le m a ty v v'},
    Clight.eval_exprlist ge e le m a ty v -> Clight.eval_exprlist ge e le m a ty v' -> v=v'.
Proof.
  induction a; intros; inv H; inv H0; f_equal.
  apply (eval_expr_fun H3) in H6. subst. congruence.
  eauto.
Qed.


Lemma eval_lvalue_fun:   forall {ge e le m a b b' z z' bf bf'},
    Clight.eval_lvalue ge e le m a b z bf -> Clight.eval_lvalue ge e le m a b' z' bf' -> (b,z,bf)=(b',z',bf').
Proof.
  intros. destruct (eval_expr_lvalue_fun ge e le m).
  eauto.
Qed.


Lemma inv_find_symbol_fun:
  forall {ge id id' b},
    Senv.find_symbol ge id = Some b ->
    Senv.find_symbol ge id' = Some b ->
    id=id'.
Proof.
  intros.
  apply Senv.find_invert_symbol in H.
  apply Senv.find_invert_symbol in H0.
  rewrite H0 in H.
  inversion H.
  reflexivity.
Qed.

Lemma assign_loc_fun:
  forall {cenv ty m b ofs bf v m1 m2},
   assign_loc cenv ty m b ofs bf v m1 ->
   assign_loc cenv ty m b ofs bf v m2 ->
   m1=m2.
Proof.
 intros. inv H; inv H0; try congruence.
 inv H1; inv H7. congruence.
Qed.

Lemma alloc_variables_fun:
  forall {ge e m vl e1 m1 e2 m2},
     Clight.alloc_variables ge e m vl e1 m1 ->
     Clight.alloc_variables ge e m vl e2 m2 ->
     (e1,m1)=(e2,m2).
Proof.
 intros until vl; revert e m;
 induction vl; intros; inv H; inv H0; auto.
 inversion2 H5 H9.
 eauto.
Qed.

Lemma bind_parameters_fun:
  forall {ge e m p v m1 m2},
    Clight.bind_parameters ge e m p v m1 ->
    Clight.bind_parameters ge e m p v m2 ->
    m1=m2.
Proof.
intros until p. revert e m; induction p; intros; inv H; inv H0; auto.
 inversion2 H3 H10.
 apply (assign_loc_fun H5) in H11. inv H11. eauto.
Qed.

Lemma eventval_list_match_fun:
  forall {se a a' t v},
    Events.eventval_list_match se a t v ->
    Events.eventval_list_match se a' t v ->
    a=a'.
Proof.
 intros.
 revert a' H0; induction H; intros.
 inv H0; eauto.
 inv H1.
 f_equal. clear - H6 H.
 inv H; inv H6; auto.
 apply (inv_find_symbol_fun H1) in H5; subst; auto.
 eauto.
Qed.
