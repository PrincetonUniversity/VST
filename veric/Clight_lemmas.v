Require Import veric.base.
Require Import Clight.

Definition val_to_bool (v: val) : option bool :=
  match v with 
    | Vint n => Some (negb (Int.eq n Int.zero))
    | Vptr _ _ => Some true
    | _ => None
  end.

Definition bool_of_valf (v: val): option bool := 
match v with
  | Vint i => Some (negb (Int.eq i Int.zero))
  | Vlong i => Some (negb (Int64.eq i Int64.zero))
  | Vfloat _ => None
  | Vptr _ _ => Some true
  | Vundef => None
end.

Definition var_name (V: Type) (bdec: ident * globvar V) : ident := 
   fst bdec.

Definition no_dups (F V: Type) (fdecs: list (ident * F)) (bdecs: list (ident * globvar V)) : Prop :=
  list_norepet (map (@fst ident F) fdecs ++ map (@var_name V) bdecs).
Implicit Arguments no_dups.

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
Implicit Arguments no_dups_inv.
 

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
Qed.

Lemma signed_zero: Int.signed Int.zero = 0.
Proof. apply Int.signed_zero. Qed.

Lemma equiv_e1 : forall A B: Prop, A=B -> A -> B.
Proof.
intros.
rewrite <- H; auto.
Qed.
Implicit Arguments equiv_e1.

Lemma equiv_e2 : forall A B: Prop, A=B -> B -> A.
Proof.
intros.
rewrite H; auto.
Qed.
Implicit Arguments equiv_e2.

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
   (fun a b i => forall b' i', Clight.eval_lvalue ge e le m a b' i' -> (b,i)=(b',i'))); intros;

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
   inv H. congruence. inversion2 H4 H9.  eapply deref_loc_fun; eauto.
   apply H0 in H. inv H.  eapply deref_loc_fun; eauto.
   apply H0 in H. inv H.  eapply deref_loc_fun; eauto.
   apply H0 in H. inv H.  eapply deref_loc_fun; eauto.
 * inv H1. apply H0 in H6. congruence.
 * inv H3. apply H0 in H7. congruence. congruence.
 * inv H2. apply H0 in H6. congruence. apply H0 in H8. congruence.

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
  forall {F V ge id id' b},
    @Genv.find_symbol F V ge id = Some b ->
    @Genv.find_symbol F V ge id' = Some b -> 
    id=id'.
Proof.
 intros.
 destruct (ident_eq id id'); auto.
  contradiction (Genv.global_addresses_distinct ge n H H0); auto.
Qed.

Lemma assign_loc_fun: 
  forall {ty m b ofs v m1 m2},
   assign_loc ty m b ofs v m1 ->
   assign_loc ty m b ofs v m2 ->
   m1=m2.
Proof.
 intros. inv H; inv H0; try congruence.
Qed.


Lemma alloc_variables_fun: 
  forall {e m vl e1 m1 e2 m2},
     Clight.alloc_variables e m vl e1 m1 ->
     Clight.alloc_variables e m vl e2 m2 ->
     (e1,m1)=(e2,m2).
Proof.
 intros until vl; revert e m;
 induction vl; intros; inv H; inv H0; auto.
 inversion2 H5 H9.
 eauto. 
Qed.

Lemma bind_parameters_fun:
  forall {e m p v m1 m2}, 
    Clight.bind_parameters e m p v m1 ->
    Clight.bind_parameters e m p v m2 ->
    m1=m2.
Proof.
intros until p. revert e m; induction p; intros; inv H; inv H0; auto.
 inversion2 H3 H10.
 apply (assign_loc_fun H5) in H11. inv H11. eauto.
Qed.

Lemma eventval_list_match_fun:
  forall {F V ge a a' t v}, 
    @Events.eventval_list_match F V ge a t v ->
    @Events.eventval_list_match F V ge a' t v ->
    a=a'.
Proof.
 intros.
 revert a' H0; induction H; intros.
 inv H0; eauto.
 inv H1.
 f_equal. clear - H6 H.
 inv H; inv H6; auto.
 apply (inv_find_symbol_fun H0) in H3; subst; auto.
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
  | H: Clight.assign_loc ?ge ?ty ?m ?b ?ofs ?v _ _,
    H': Clight.assign_loc ?ge ?ty ?m ?b ?ofs ?v _ _ |- _ =>
        apply (assign_loc_fun H) in H'; inv H'
  | H: Clight.deref_loc ?ge ?ty ?m ?b ?ofs ?t _,
    H': Clight.deref_loc ?ge ?ty ?m ?b ?ofs ?t _ |- _ =>
        apply (deref_loc_fun H) in H'; inv H'
  | H: Clight.alloc_variables ?e ?m ?vl _ _,
    H': Clight.alloc_variables ?e ?m ?vl _ _ |- _ =>
        apply (alloc_variables_fun H) in H'; inv H'
  | H: Clight.bind_parameters ?ge ?e ?m ?p ?vl _,
    H': Clight.bind_parameters ?ge ?e ?m ?p ?vl _ |- _ =>
        apply (bind_parameters_fun H) in H'; inv H'
  | H: Genv.find_symbol ?ge _ = Some ?b,
    H': Genv.find_symbol ?ge _ = Some ?b |- _ => 
       apply (inv_find_symbol_fun H) in H'; inv H'
  | H: Events.eventval_list_match ?ge _ ?t ?v,
    H': Events.eventval_list_match ?ge _ ?t ?v |- _ =>
       apply (eventval_list_match_fun H) in H'; inv H'
 end. 


Lemma int_of_bytes_uniq:
  forall i j, length i = length j -> int_of_bytes i = int_of_bytes j -> i = j.
Proof.
  induction i; intros.
 destruct j; inv H. auto.
 destruct j; inv H.
 specialize (IHi _ H2).
 simpl in H0.
do 2 rewrite (Z.add_comm (Byte.unsigned _)) in H0.
 remember (int_of_bytes j * 256 + Byte.unsigned i0) as v eqn:?H.
 symmetry in H0.
 rename i0 into b.
 pose proof (Zmod_unique _ _ _ _ H (Byte.unsigned_range _)).
 pose proof (Zmod_unique _ _ _ _ H0 (Byte.unsigned_range _)).
 assert (Byte.repr (Byte.unsigned a) = Byte.repr (Byte.unsigned b)) by congruence.
 repeat rewrite Byte.repr_unsigned in H4.
 subst b.
 f_equal. clear H1.
 apply IHi.
 omega.
Qed.

Lemma decode_int_uniq:
  forall i j, length i = length j -> decode_int i = decode_int j -> i=j.
Proof.
 unfold decode_int, rev_if_be.
 destruct big_endian.
 intros. rewrite <- (rev_involutive i). rewrite <- (rev_involutive j).
 f_equal.
 assert (length (rev i) = length (rev j)).
 repeat rewrite rev_length; auto.
 eapply int_of_bytes_uniq; eauto.
 apply int_of_bytes_uniq.
Qed.

Lemma decode_int_range:
  forall l N, N = two_p (8 * Z.of_nat (length l)) -> 0 <= decode_int l < N.
Proof.
intros; subst; revert l.
unfold decode_int.
assert (forall l, 0 <= int_of_bytes l < two_p (8 * Z.of_nat (length l))).
2: intros; rewrite <- rev_if_be_length; auto.
induction l.
simpl; omega.
simpl int_of_bytes. simpl length.
rewrite Nat2Z.inj_succ.
unfold Z.succ.
rewrite Z.mul_add_distr_l.
rewrite two_p_is_exp; try omega.
change (two_p (8*1)) with 256.
pose proof (Byte.unsigned_range a).
change Byte.modulus with 256 in H.
omega.
Qed.

Lemma Vint_inj: forall i j, Vint i = Vint j -> i=j. 
Proof. congruence. Qed.

Lemma sign_ext_injective:
 forall n i j, 
    0 < n < Int.zwordsize ->
    0 <= i < two_p n -> 
    0 <= j < two_p n -> 
    Int.sign_ext n (Int.repr i) = Int.sign_ext n (Int.repr j) ->
    i=j.
Proof.
intros.
pose proof (Int.eqmod_sign_ext n (Int.repr i) H).
pose proof (Int.eqmod_sign_ext n (Int.repr j) H).
rewrite H2 in H3.
apply Int.eqmod_sym in H3.
pose proof (Int.eqmod_trans _ _ _ _ H3 H4).
rewrite Int.unsigned_repr in H5.
2: pose proof (two_p_monotone_strict n Int.zwordsize); 
   change Int.max_unsigned with (two_p Int.zwordsize - 1); 
   omega.
rewrite Int.unsigned_repr in H5.
2: pose proof (two_p_monotone_strict n Int.zwordsize); 
   change Int.max_unsigned with (two_p Int.zwordsize - 1); 
   omega.
apply Int.eqmod_small_eq in H5; auto.
Qed.


Lemma zero_ext_injective:
 forall n i j, 
    0 <= n < Int.zwordsize ->
    0 <= i < two_p n -> 
    0 <= j < two_p n -> 
    Int.zero_ext n (Int.repr i) = Int.zero_ext n (Int.repr j) ->
    i=j.
Proof.
intros.
pose proof (Int.eqmod_zero_ext n (Int.repr i) H).
pose proof (Int.eqmod_zero_ext n (Int.repr j) H).
rewrite H2 in H3.
apply Int.eqmod_sym in H3.
pose proof (Int.eqmod_trans _ _ _ _ H3 H4).
rewrite Int.unsigned_repr in H5.
2: pose proof (two_p_monotone_strict n Int.zwordsize); 
   change Int.max_unsigned with (two_p Int.zwordsize - 1); 
   omega.
rewrite Int.unsigned_repr in H5.
2: pose proof (two_p_monotone_strict n Int.zwordsize); 
   change Int.max_unsigned with (two_p Int.zwordsize - 1); 
   omega.
apply Int.eqmod_small_eq in H5; auto.
Qed.

Lemma repr_decode_int_inj:
  forall l1 l2, length l1 = 4%nat -> length l2 = 4%nat ->
    Int.repr (decode_int l1) = Int.repr (decode_int l2) ->
    l1=l2.
Proof.
intros.
apply decode_int_uniq; [congruence | ].
rewrite <- (Int.unsigned_repr (decode_int l1)).
Focus 2.
pose proof (decode_int_range l1 _ (eq_refl _)).
rewrite H in H2.
change (two_p (8 * Z.of_nat 4)) with (Int.max_unsigned + 1) in H2.
omega.
rewrite <- (Int.unsigned_repr (decode_int l2)).
Focus 2.
pose proof (decode_int_range l2 _ (eq_refl _)).
rewrite H0 in H2.
change (two_p (8 * Z.of_nat 4)) with (Int.max_unsigned + 1) in H2.
omega.
congruence.
Qed.

Lemma repr_decode_int64_inj:
  forall l1 l2, length l1 = 8%nat -> length l2 = 8%nat ->
    Int64.repr (decode_int l1) = Int64.repr (decode_int l2) ->
    l1=l2.
Proof.
intros.
apply decode_int_uniq; [congruence | ].
rewrite <- (Int64.unsigned_repr (decode_int l1)).
Focus 2.
pose proof (decode_int_range l1 _ (eq_refl _)).
rewrite H in H2.
change (two_p (8 * Z.of_nat 8)) with (Int64.max_unsigned + 1) in H2.
omega.
rewrite <- (Int64.unsigned_repr (decode_int l2)).
Focus 2.
pose proof (decode_int_range l2 _ (eq_refl _)).
rewrite H0 in H2.
change (two_p (8 * Z.of_nat 8)) with (Int64.max_unsigned + 1) in H2.
omega.
congruence.
Qed.

Transparent Float.single_of_bits.
Transparent Float.double_of_bits.

Lemma double_of_bits_inj:
  forall i j, Float.double_of_bits i = Float.double_of_bits j -> i=j.
Proof.
intros.
unfold Float.double_of_bits in H.
rewrite <- (Int64.repr_unsigned i).
rewrite <- (Int64.repr_unsigned j).
f_equal.
unfold Fappli_IEEE_bits.b64_of_bits in H.
rewrite <- (Fappli_IEEE_bits.bits_of_binary_float_of_bits 52 11 (refl_equal _) (refl_equal _) (refl_equal _) (Int64.unsigned i))
  by (apply Int64.unsigned_range).
rewrite <- (Fappli_IEEE_bits.bits_of_binary_float_of_bits 52 11 (refl_equal _) (refl_equal _) (refl_equal _) (Int64.unsigned j))
  by (apply Int64.unsigned_range).
f_equal; apply H.
Qed.

Lemma single_of_bits_inj:
  forall i j, Float.single_of_bits i = Float.single_of_bits j -> i=j.
Proof.
intros.
unfold Float.single_of_bits in H.
rewrite <- (Int.repr_unsigned i).
rewrite <- (Int.repr_unsigned j).
f_equal.
rewrite <- (Fappli_IEEE_bits.bits_of_binary_float_of_bits 23 8 (refl_equal _) (refl_equal _) (refl_equal _) (Int.unsigned i))
  by (apply Int.unsigned_range).
rewrite <- (Fappli_IEEE_bits.bits_of_binary_float_of_bits 23 8 (refl_equal _) (refl_equal _) (refl_equal _) (Int.unsigned j))
  by (apply Int.unsigned_range).
f_equal.
unfold Float.floatofbinary32 in H.
unfold Fappli_IEEE_bits.b32_of_bits in H.
match goal with |- ?A = ?B => forget A as u; forget B as v end.
clear i j.
destruct u,v; auto; try congruence;
 try destruct (Float.floatofbinary32_pl b0 n);
 try destruct (Float.floatofbinary32_pl b n);
 try destruct (Float.floatofbinary32_pl b0 n0);
 try congruence.
Admitted.  (* nontrivial, but perhaps true; see e-mail exchange
  between Andrew Appel and Guillaume Melquiond, April 2014 *)

Opaque Float.single_of_bits.
Opaque Float.double_of_bits.


Lemma decode_val_uniq: 
  forall ch b1 b2 v, 
    v <> Vundef ->
    length b1 = size_chunk_nat ch ->
    length b2 = size_chunk_nat ch ->
    decode_val ch b1 = v ->
    decode_val ch b2 = v ->
    b1=b2.
Proof.
 intros.
 unfold size_chunk_nat in *.
 unfold decode_val in *.
 destruct (proj_bytes b1) eqn:B1.
Focus 2.
{ destruct ch; try congruence.
 destruct (proj_bytes b2) eqn:B2.
subst v.
unfold proj_pointer in H3.
destruct b1; try congruence.
destruct m; try congruence.
if_tac in H3; try congruence.
clear - H2 H3 H.
subst v.
unfold proj_pointer in *.
destruct b1; try congruence.
destruct m; try congruence.
destruct b2; try congruence. destruct m; try congruence.
destruct (check_pointer 4 b i (Pointer b i n :: b1)) eqn:?; try congruence.
destruct (check_pointer 4 b0 i0 (Pointer b0 i0 n0 :: b2)) eqn:?; try congruence.
inv H3.
clear H.
unfold check_pointer in *; simpl in *.
repeat match goal with 
| H: ?A = true |- _ =>
  match A with 
  | context [eq_block ?a ?b]  =>
     destruct (eq_block a b); simpl in *; try congruence
  | context [Int.eq_dec ?i ?j] => 
     destruct (Int.eq_dec i j); simpl in *; try congruence
  | context [match ?n with _ => _ end] =>
     destruct n; simpl in *; try congruence
  end
end.
} Unfocus.
destruct (proj_bytes b2) eqn:B2.
Focus 2. {
destruct ch; try congruence.
unfold proj_pointer in H3.
destruct b2; try congruence.
destruct m; try congruence.
if_tac in H3; try congruence.
} Unfocus.
pose proof (length_proj_bytes _ _ B1).
pose proof (length_proj_bytes _ _ B2).
rewrite <- H4 in *; rewrite <- H5 in *.
assert (l=l0).
Focus 2. {
clear - H6 B1 B2.
revert l0 b1 b2 B1 B2 H6; induction l; destruct l0; intros; inv H6.
destruct b1; inv B1. destruct b2; inv B2; auto.
destruct m; try congruence.
destruct (proj_bytes b2);  inv H0.
destruct m; inv H0.
destruct (proj_bytes b1);  inv H1.
destruct b1; inv B1.
destruct m; inv H0.
destruct (proj_bytes b1) eqn:?; inv H1.
destruct b2; inv B2.
destruct m; inv H0.
destruct (proj_bytes b2) eqn:?; inv H1.
specialize (IHl _ _ _ Heqo Heqo0).
f_equal; auto.
} Unfocus.
clear b1 b2 H4 H5 B1 B2.
clear H.
subst v.
destruct ch; try apply Vint_inj in H3;
simpl in H0,H1; unfold Pos.to_nat in H0,H1; simpl in H0,H1;
 (* this "try" takes care of all signed and unsigned bytes and shorts *)
try (apply decode_int_uniq; [ congruence | ];
(apply sign_ext_injective in H3 || apply zero_ext_injective in H3);
 [ congruence |  compute; split; congruence
 | apply decode_int_range; rewrite H1; reflexivity
 | apply decode_int_range; rewrite H0; reflexivity
 ]).

* (* Mint32 *)  apply repr_decode_int_inj; auto.
* (* Mint64 *) apply repr_decode_int64_inj; congruence.
* (* Mfloat32 *)
  inv H3.
  apply decode_int_uniq; [congruence | ].
  apply single_of_bits_inj in H2.
  apply repr_decode_int_inj in H2; auto.
  congruence.
* (* Mfloat64 *)
  inv H3.
  apply decode_int_uniq; [congruence | ].
  apply double_of_bits_inj in H2.
  apply repr_decode_int64_inj in H2; auto.
  congruence.

* (* Mfloat64al32 *)
  inv H3.
  apply decode_int_uniq; [congruence | ].
  apply double_of_bits_inj in H2.
  apply repr_decode_int64_inj in H2; auto.
  congruence.
Qed.

