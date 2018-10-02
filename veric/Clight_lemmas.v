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

(*moved to coqlib4
Lemma nat_ind2_Type:
forall P : nat -> Type,
((forall n, (forall j:nat, (j<n )%nat -> P j) ->  P n):Type) ->
(forall n, P n).
Proof.
intros.
assert (forall j , (j <= n)%nat -> P j).
induction n.
intros.
replace j with 0%nat ; try omega.
apply X; intros.
elimtype False; omega.
intros.  apply X. intros.
apply IHn.
omega.
apply X0.
omega.
Qed.

Lemma nat_ind2:
forall P : nat -> Prop,
(forall n, (forall j:nat, (j<n )%nat -> P j) ->  P n) ->
(forall n, P n).
Proof.
intros; apply Wf_nat.lt_wf_ind. auto.
Qed.*)

Lemma signed_zero: Int.signed Int.zero = 0.
Proof. apply Int.signed_zero. Qed.

Lemma equiv_e1 : forall A B: Prop, A=B -> A -> B.
Proof.
intros.
rewrite <- H; auto.
Qed.
Arguments equiv_e1 [A B] _ _.

(*moved to coqlib4
Lemma equiv_e2 : forall A B: Prop, A=B -> B -> A.
Proof.
intros.
rewrite H; auto.
Qed.
Arguments equiv_e2 [A B] _ _.
*)

Lemma deref_loc_fun: forall {ty m b z v v'},
   Clight.deref_loc ty m b z v -> Clight.deref_loc ty m b z v' -> v=v'.
 Proof. intros.  inv H; inv H0; try congruence.
Qed.

Lemma eval_expr_lvalue_fun:
  forall ge e le m,
    (forall a v v', Clight.eval_expr ge e le m a v -> Clight.eval_expr ge e le m a v' -> v=v') /\
    (forall a b b' i i', Clight.eval_lvalue ge e le m a b i -> Clight.eval_lvalue ge e le m a b' i' ->
                               (b,i)=(b',i')).
Proof.
 intros.
 destruct (Clight.eval_expr_lvalue_ind ge e le m
   (fun a v =>  forall v', Clight.eval_expr ge e le m a v' -> v=v')
   (fun a b i => forall b' i', Clight.eval_lvalue ge e le m a b' i' -> (b,i)=(b',i')));
  simpl; intros;

  try solve [repeat
  match goal with
  |  H: eval_expr _ _ _ _ ?a _  |- _ => (is_var a; fail 1) || inv H
  | H: eval_lvalue _ _ _ _ ?a _ _ |- _  => (is_var a; fail 1) || inv H
  end; congruence].

 * inv H1. apply H0 in H5; congruence. inv H2.
 * inv H2. apply H0 in H7; congruence. inv H3.
 * inv H4. apply H0 in H10. apply H2 in H11. congruence. inv H5.
 * inv H2. apply H0 in H5. congruence. inv H4. inv H3. inv H3. inv H3.
 * inv H; inv H2. apply H0 in H. inv H. eapply deref_loc_fun; eauto.
   inv H. congruence. inversion2 H4 H10.  eapply deref_loc_fun; eauto.
   apply H0 in H. inv H.  eapply deref_loc_fun; eauto.
   apply H0 in H. inv H.  eapply deref_loc_fun; eauto.
   apply H0 in H. inv H.  eapply deref_loc_fun; eauto.
 * inv H1. apply H0 in H6. congruence.
 * inv H4. apply H0 in H8. congruence. congruence.
 * inv H3. apply H0 in H7. congruence. apply H0 in H7. congruence.

 * split; intros; [apply (H _ _ H1 _ H2) | apply (H0 _ _ _ H1 _ _ H2)].
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


Lemma eval_lvalue_fun:   forall {ge e le m a b b' z z'},
    Clight.eval_lvalue ge e le m a b z -> Clight.eval_lvalue ge e le m a b' z' -> (b,z)=(b',z').
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
  forall {cenv ty m b ofs v m1 m2},
   assign_loc cenv ty m b ofs v m1 ->
   assign_loc cenv ty m b ofs v m2 ->
   m1=m2.
Proof.
 intros. inv H; inv H0; try congruence.
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

Ltac fun_tac :=
  match goal with
  | H: ?A = Some _, H': ?A = Some _ |- _ => inversion2 H H'
  | H: Clight.eval_expr ?ge ?e ?le ?m ?A _,
    H': Clight.eval_expr ?ge ?e ?le ?m ?A _ |- _ =>
        apply (eval_expr_fun H) in H'; subst
  | H: Clight.eval_exprlist ?ge ?e ?le ?m ?A ?ty _,
    H': Clight.eval_exprlist ?ge ?e ?le ?m ?A ?ty _ |- _ =>
        apply (eval_exprlist_fun H) in H'; subst
  | H: Clight.eval_lvalue ?ge ?e ?le ?m ?A _ _,
    H': Clight.eval_lvalue ?ge ?e ?le ?m ?A _ _ |- _ =>
        apply (eval_lvalue_fun H) in H'; inv H'
  | H: Clight.assign_loc ?ge ?ty ?m ?b ?ofs ?v _,
    H': Clight.assign_loc ?ge ?ty ?m ?b ?ofs ?v _ |- _ =>
        apply (assign_loc_fun H) in H'; inv H'
  | H: Clight.deref_loc ?ty ?m ?b ?ofs _,
    H': Clight.deref_loc ?ty ?m ?b ?ofs _ |- _ =>
        apply (deref_loc_fun H) in H'; inv H'
  | H: Clight.alloc_variables ?ge ?e ?m ?vl _ _,
    H': Clight.alloc_variables ?ge ?e ?m ?vl _ _ |- _ =>
        apply (alloc_variables_fun H) in H'; inv H'
  | H: Clight.bind_parameters ?ge ?e ?m ?p ?vl _,
    H': Clight.bind_parameters ?ge ?e ?m ?p ?vl _ |- _ =>
        apply (bind_parameters_fun H) in H'; inv H'
  | H: Senv.find_symbol ?ge _ = Some ?b,
    H': Senv.find_symbol ?ge _ = Some ?b |- _ =>
       apply (inv_find_symbol_fun H) in H'; inv H'
  | H: Events.eventval_list_match ?ge _ ?t ?v,
    H': Events.eventval_list_match ?ge _ ?t ?v |- _ =>
       apply (eventval_list_match_fun H) in H'; inv H'
 end.

(* Lemmas about ident lists -- moved to general_base of mpred

Fixpoint id_in_list (id: ident) (ids: list ident) : bool :=
 match ids with i::ids' => orb (Pos.eqb id i) (id_in_list id ids') | _ => false end.

Fixpoint compute_list_norepet (ids: list ident) : bool :=
 match ids with
 | id :: ids' => if id_in_list id ids' then false else compute_list_norepet ids'
 | nil => true
 end.

Lemma id_in_list_true: forall i ids, id_in_list i ids = true -> In i ids.
Proof.
 induction ids; simpl; intros. inv H. apply orb_true_iff in H; destruct H; auto.
 apply Peqb_true_eq in H. subst; auto.
Qed.

Lemma id_in_list_false: forall i ids, id_in_list i ids = false -> ~In i ids.
Proof.
 induction ids; simpl; intros; auto.
 apply orb_false_iff in H. destruct H.
 intros [?|?]. subst.
 rewrite Pos.eqb_refl in H; inv H.
 apply IHids; auto.
Qed.

Lemma compute_list_norepet_e: forall ids,
     compute_list_norepet ids = true -> list_norepet ids.
Proof.
 induction ids; simpl; intros.
 constructor.
 revert H; case_eq (id_in_list a ids); intros.
 inv H0.
 constructor; auto.
 apply id_in_list_false in H.
 auto.
Qed.

Lemma list_norepet_rev:
  forall A (l: list A), list_norepet (rev l) = list_norepet l.
Proof.
induction l; simpl; auto.
apply prop_ext; split; intros.
apply list_norepet_app in H.
destruct H as [? [? ?]].
rewrite IHl in H.
constructor; auto.
eapply list_disjoint_notin with (a::nil).
apply list_disjoint_sym; auto.
intros x y ? ? ?; subst.
contradiction (H1 y y); auto.
rewrite <- In_rev; auto.
simpl; auto.
rewrite list_norepet_app.
inv H.
split3; auto.
rewrite IHl; auto.
repeat constructor.
intro Hx. inv Hx.
intros x y ? ? ?; subst.
inv H0.
rewrite <- In_rev in H; contradiction.
auto.
Qed.

Lemma block_eq_dec: forall b1 b2: block, {b1 = b2} + {b1 <> b2}.
Proof. exact (Coqlib.peq). Qed.

(*moved to mpred
Definition int_range (sz: intsize) (sgn: signedness) (i: int) :=
 match sz, sgn with
 | I8, Signed => -128 <= Int.signed i < 128
 | I8, Unsigned => 0 <= Int.unsigned i < 256
 | I16, Signed => -32768 <= Int.signed i < 32768
 | I16, Unsigned => 0 <= Int.unsigned i < 65536
 | I32, Signed => -2147483648 <= Int.signed i < 2147483648
 | I32, Unsigned => 0 <= Int.unsigned i < 4294967296
 | IBool, _ => 0 <= Int.unsigned i < 256
end.*)

Lemma rev_if_be_singleton:
  forall x, rev_if_be (x::nil) = (x::nil).
Proof. intro. unfold rev_if_be; destruct Archi.big_endian; auto. Qed.

Lemma rev_if_be_1: forall i, rev_if_be (i::nil) = (i::nil).
Proof. unfold rev_if_be; intros. destruct Archi.big_endian; reflexivity.
Qed.

Lemma decode_byte_val:
  forall m, decode_val Mint8unsigned (Byte m :: nil) =
              Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned m))).
Proof.
intros.
unfold decode_val. simpl.
f_equal.
unfold decode_int.
rewrite rev_if_be_singleton.
unfold int_of_bytes. f_equal. f_equal. apply Z.add_0_r.
Qed.

Lemma Vint_inj: forall x y, Vint x = Vint y -> x=y.
Proof. congruence. Qed.

*)