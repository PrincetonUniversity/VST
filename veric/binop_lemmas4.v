Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.res_predicates.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.Clight_Cop2.
Require Import VST.veric.binop_lemmas2.
Require Import VST.veric.binop_lemmas3.

Require Import VST.veric.juicy_mem.
Import Cop.
Import Cop2.
Import Clight_Cop2.

Section mpred.

Context `{!heapGS Σ}.

Lemma denote_tc_test_eq_Vint_l: forall i v,
  denote_tc_test_eq (Vint i) v ⊢
  ⌜i = Int.zero⌝.
Proof.
  intros.
  unfold denote_tc_test_eq; simpl.
  destruct Archi.ptr64, v; try solve [iIntros "[]"]; simpl; by iIntros "[% _]".
Qed.

Lemma denote_tc_test_eq_Vint_r: forall i v,
  denote_tc_test_eq v (Vint i) ⊢
  ⌜i = Int.zero⌝.
Proof.
  intros.
  unfold denote_tc_test_eq; simpl.
  destruct Archi.ptr64, v; try solve [iIntros "[]"]; simpl; by iIntros "[% ?]".
Qed.


Lemma sameblock_eq_block:
 forall p q r s, 
  is_true (sameblock (Vptr p r) (Vptr q s)) -> p=q.
Proof.
 simpl; intros. destruct (peq p q); auto. inv H.
Qed.

Lemma denote_tc_test_eq_Vint_l': forall i v,
  denote_tc_test_eq (Vint i) v ⊢
  ⌜Int.eq i Int.zero = true⌝.
Proof.
  intros.
  unfold denote_tc_test_eq; simpl.
  destruct v; try solve [iIntros "[]"]; destruct Archi.ptr64; try solve [iIntros "[]"];
    iIntros "[-> _]"; iPureIntro; apply Int.eq_true.
Qed.

Lemma denote_tc_test_eq_Vint_r': forall i v,
  denote_tc_test_eq v (Vint i) ⊢
  ⌜Int.eq i Int.zero = true⌝.
Proof.
  intros.
  unfold denote_tc_test_eq; simpl.
  destruct v; try solve [iIntros "[]"]; destruct Archi.ptr64; try solve [iIntros "[]"];
    (iIntros "[_ ->]" || iIntros "[-> _]"); iPureIntro; apply Int.eq_true.
Qed.

Lemma denote_tc_test_eq_Vlong_l': forall i v,
  denote_tc_test_eq (Vlong i) v ⊢
  ⌜Int64.eq i Int64.zero = true⌝.
Proof.
  intros.
  unfold denote_tc_test_eq; simpl.
  destruct v; try solve [iIntros "[]"]; destruct Archi.ptr64; try solve [iIntros "[]"];
    iIntros "[-> _]"; iPureIntro; apply Int64.eq_true.
Qed.

Lemma denote_tc_test_eq_Vlong_r': forall i v,
  denote_tc_test_eq v (Vlong i) ⊢
  ⌜Int64.eq i Int64.zero = true⌝.
Proof.
  intros.
  unfold denote_tc_test_eq; simpl.
  destruct v; try solve [iIntros "[]"]; destruct Archi.ptr64; try solve [iIntros "[]"];
    (iIntros "[_ ->]" || iIntros "[-> _]"); iPureIntro; apply Int64.eq_true.
Qed.

Lemma denote_tc_test_order_eqblock:
  forall b0 i0 b i,
   denote_tc_test_order (Vptr b0 i0) (Vptr b i) ⊢
   ⌜b0 = b⌝.
Proof.
intros.
unfold denote_tc_test_order; simpl.
unfold test_order_ptrs; simpl.
destruct (peq b0 b); auto.
Qed.

Lemma valid_pointer_dry:
  forall b ofs d m, mem_auth m ∗ valid_pointer' (Vptr b ofs) d ⊢
         ⌜Mem.valid_pointer m b (Ptrofs.unsigned ofs + d) = true⌝.
Proof.
intros.
iIntros "[Hm (% & % & >H)]".
iDestruct (mapsto_lookup with "Hm H") as %[Hdq H]; iPureIntro.
rewrite Mem.valid_pointer_nonempty_perm /Mem.perm.
destruct H as (_ & H & _).
rewrite /juicy_view.access_cohere /access_at in H.
destruct (Maps.PMap.get _ _ _ _); try constructor.
simpl in H.
destruct (perm_of_dfrac dq) eqn: Hp; first by destruct dq, r; try if_tac in H.
apply perm_of_dfrac_None in Hp; subst; contradiction.
Qed.

Lemma weak_valid_pointer_dry:
  forall b ofs m, mem_auth m ∗ weak_valid_pointer (Vptr b ofs) ⊢
           ⌜(Mem.valid_pointer m b (Ptrofs.unsigned ofs)
            || Mem.valid_pointer m b (Ptrofs.unsigned ofs - 1))%bool = true⌝.
Proof.
intros.
rewrite orb_true_iff /weak_valid_pointer.
iIntros "[Hm [H | H]]".
- iLeft; rewrite <- (Z.add_0_r (Ptrofs.unsigned ofs)).
  iApply valid_pointer_dry; iFrame.
- iRight; rewrite <- Z.add_opp_r.
  iApply valid_pointer_dry; iFrame.
Qed.

Lemma test_eq_relate':
  forall v1 v2 op
    (OP: op = Ceq \/ op = Cne) m,
     mem_auth m ∗ denote_tc_test_eq v1 v2 ⊢
     ⌜cmp_ptr m op v1 v2 = 
     Some (force_val (sem_cmp_pp op v1 v2))⌝.
Proof.
intros; iIntros "[Hm H]".
unfold cmp_ptr, sem_cmp_pp.
unfold denote_tc_test_eq.
 rewrite bool2val_eq.
 destruct v1; try done; auto;
 destruct v2; try done; auto.
*
 simpl.
 destruct Archi.ptr64; try done.
 iDestruct "H" as "[-> H]".
 rewrite ?Int.eq_true ?Int64.eq_true /=.
 iDestruct (weak_valid_pointer_dry with "[$Hm $H]") as %->.
 destruct OP; subst; simpl; auto.
*
 simpl.
 destruct Archi.ptr64; try done.
 iDestruct "H" as "[-> H]".
 rewrite ?Int.eq_true ?Int64.eq_true /=.
 iDestruct (weak_valid_pointer_dry with "[$Hm $H]") as %->.
 destruct OP; subst; simpl; auto.
*
 simpl.
 unfold test_eq_ptrs.
 unfold sameblock.
 destruct (peq b b0);
  simpl proj_sumbool; cbv iota;
 [rewrite -> !if_true by auto | rewrite -> !if_false by auto].
 - iDestruct (weak_valid_pointer_dry with "[-]") as %->.
   { iDestruct "H" as "[$ _]"; iFrame. }
   iDestruct (weak_valid_pointer_dry with "[-]") as %->.
   { iDestruct "H" as "[_ $]"; iFrame. }
   done.
 - iDestruct (valid_pointer_dry with "[-]") as %H.
   { iDestruct "H" as "[$ _]"; iFrame. }
   iDestruct (valid_pointer_dry with "[-]") as %H0.
   { iDestruct "H" as "[_ $]"; iFrame. }
   rewrite -> Z.add_0_r in H,H0; rewrite H H0.
   destruct OP; subst; done.
Qed.

Lemma sem_cast_relate:
 forall i sz si a si' a' m,
  Cop.sem_cast (Vint i) (Tint sz si a) (Tint I32 si' a') m =
 sem_cast (Tint sz si a)  (Tint I32 si' a') (Vint i).
Proof.
intros.
reflexivity.
Qed.
Lemma sem_cast_int_lemma:
 forall sz si a si' a' i, 
  sem_cast (Tint sz si a)  (Tint I32 si' a') (Vint i) = Some (Vint i).
Proof.
intros.
unfold sem_cast, classify_cast, tint, sem_cast_pointer.
auto.
Qed.

Lemma sem_cast_relate_int_long:
 forall i sz si a si' a' m,
  Cop.sem_cast (Vint i) (Tint sz si a) (Tlong si' a') m =
 sem_cast (Tint sz si a)  (Tlong si' a') (Vint i).
Proof.
intros.
reflexivity.
Qed.

Lemma sem_cast_relate_long:
 forall i si a si' a' m,
  Cop.sem_cast (Vlong i) (Tlong si a) (Tlong si' a') m =
 sem_cast (Tlong si a)  (Tlong si' a') (Vlong i).
Proof.
intros.
reflexivity.
Qed.

Lemma sem_cast_int_long_lemma:
 forall sz si a si' a' i, 
  sem_cast (Tint sz si a)  (Tlong si' a') (Vint i) = Some (Vlong (cast_int_long si i)).
Proof.
intros.
unfold sem_cast, classify_cast, tint, sem_cast_pointer, sem_cast_i2l.
auto.
Qed.
Lemma sem_cast_long_lemma:
 forall si a si' a' i, 
  sem_cast (Tlong si a)  (Tlong si' a') (Vlong i) = Some (Vlong i).
Proof.
intros.
unfold sem_cast, classify_cast, tint, sem_cast_pointer, sem_cast_i2l.
auto.
Qed.

Lemma denote_tc_test_eq_xx:
 forall v si i,
 denote_tc_test_eq v (Vint i) ⊢
 denote_tc_test_eq v (Vptrofs (ptrofs_of_int si i)).
Proof.
intros.
unfold denote_tc_test_eq.
destruct v; try (iIntros "[]");
unfold Vptrofs, ptrofs_of_int; simpl;
destruct Archi.ptr64; try contradiction;
destruct H; hnf in *; subst; destruct si; split; hnf; auto.
Qed.

Lemma denote_tc_test_eq_yy:
 forall v si i,
 denote_tc_test_eq (Vint i) v ⊢
 denote_tc_test_eq (Vptrofs (ptrofs_of_int si i)) v.
Proof.
intros.
unfold denote_tc_test_eq .
destruct v; try (iIntros "[]");
unfold Vptrofs, ptrofs_of_int; simpl;
destruct Archi.ptr64; try contradiction;
destruct H; hnf in *; subst; destruct si; split; hnf; auto.
Qed.

Lemma sem_cast_long_intptr_lemma:
 forall si a i,
  force_val1 (sem_cast (Tlong si a) size_t) (Vlong i)
 = Vptrofs (Ptrofs.of_int64 i).
Proof.
intros.
 unfold Vptrofs, size_t, sem_cast, classify_cast, sem_cast_pointer.
 destruct Archi.ptr64 eqn:Hp.
 simpl. rewrite Ptrofs.to_int64_of_int64; auto.
 simpl.
 f_equal.
 rewrite Ptrofs_to_of64_lemma; auto.
Qed.

Lemma test_order_relate':
  forall v1 v2 op m,
     mem_auth m ∗ denote_tc_test_order v1 v2 ⊢
   ⌜cmp_ptr m op v1 v2 = Some (force_val (sem_cmp_pp op v1 v2))⌝.
Proof.
  intros; iIntros "[Hm H]".
  unfold denote_tc_test_order.
  destruct v1; try done; auto;
  destruct v2; try done; auto;
  unfold cmp_ptr, sem_cmp_pp; simpl;
  rewrite bool2val_eq; auto.
  unfold test_order_ptrs.
  unfold sameblock.
  destruct (peq b b0);
  simpl proj_sumbool; cbv iota;
    [rewrite -> !if_true by auto | rewrite -> !if_false by auto; done].
  iDestruct (weak_valid_pointer_dry with "[-]") as %->.
  { iDestruct "H" as "[$ _]"; iFrame. }
  iDestruct (weak_valid_pointer_dry with "[-]") as %->.
  { iDestruct "H" as "[_ $]"; iFrame. }
  done.
Qed.

Lemma sem_cast_int_intptr_lemma:
 forall sz si a i,
  force_val1 (sem_cast (Tint sz si a) size_t) (Vint i)
 = Vptrofs (ptrofs_of_int si i).
Proof.
intros.
 unfold Vptrofs, size_t, sem_cast, classify_cast, sem_cast_pointer.
 destruct Archi.ptr64 eqn:Hp.
+ simpl. unfold cast_int_long, ptrofs_of_int.
 destruct si; auto.
 unfold Ptrofs.to_int64.
 unfold Ptrofs.of_ints.
 f_equal.
 rewrite (Ptrofs.agree64_repr Hp) Int64.repr_unsigned. auto.
 f_equal.
 unfold Ptrofs.to_int64.
 unfold Ptrofs.of_intu. unfold Ptrofs.of_int.
 rewrite Ptrofs.unsigned_repr; auto.
 pose proof (Int.unsigned_range i).
 pose proof (Ptrofs.modulus_eq64 Hp).
 unfold Ptrofs.max_unsigned.
 rewrite H0.
 assert (Int.modulus < Int64.modulus) by (compute; auto).
 lia.
+ try ( (* Archi.ptr64=false *)
  simpl; f_equal;
  unfold Ptrofs.to_int, ptrofs_of_int, Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int;
  destruct si;
  rewrite ?(Ptrofs.agree32_repr Hp)
    ?Int.repr_unsigned ?Int.repr_signed; auto).
Qed.

Lemma test_eq_fiddle_signed_xx:
 forall si si' v i, 
denote_tc_test_eq v (Vptrofs (ptrofs_of_int si i)) ⊢
denote_tc_test_eq v (Vptrofs (ptrofs_of_int si' i)).
Proof.
intros.
unfold denote_tc_test_eq.
unfold Vptrofs, ptrofs_of_int.
destruct v; try (iIntros "[]");
destruct Archi.ptr64 eqn:Hp; try (iIntros "[]"); subst.
-
iPureIntro; intros [??]; split; auto.
clear H.
destruct si; auto.
*
unfold Ptrofs.of_ints in *.
unfold Ptrofs.to_int, Ptrofs.to_int64 in *.
rewrite -> ?Ptrofs.agree32_repr, ?Ptrofs.agree64_repr,
             ?Int.repr_unsigned, ?Int64.repr_unsigned in H0 by auto.
assert (i=Int.zero)
  by first [apply Int64repr_Intsigned_zero; solve [auto]
              | rewrite <- (Int.repr_signed i); auto].
subst i.
destruct si'; auto.
*
destruct si'; auto.
unfold Ptrofs.of_intu in H0.
try ( (* Archi.ptr64=false case *)
 rewrite -> Ptrofs.to_int_of_int in H0 by auto;
 subst;
 unfold Ptrofs.of_ints;
 rewrite Int.signed_zero;
 unfold Ptrofs.to_int;
 rewrite Ptrofs.unsigned_repr; [reflexivity |];
 unfold Ptrofs.max_unsigned; rewrite (Ptrofs.modulus_eq32 Hp);
 compute; split; congruence);
(* Archi.ptr64=true case *)
try (unfold Ptrofs.of_int, Ptrofs.to_int64 in H0;
rewrite Ptrofs.unsigned_repr in H0;
 [apply Int64repr_Intunsigned_zero in H0; subst; reflexivity
 | pose proof (Int.unsigned_range i);
   destruct H; split; auto;
   assert (Int.modulus < Ptrofs.max_unsigned)
     by (unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize; rewrite Hp; compute; auto);
    lia]).
-
iIntros "[% $]"; iPureIntro.
destruct si, si'; auto.
*
unfold Ptrofs.of_ints, Ptrofs.of_intu in *.
unfold Ptrofs.to_int64 in H.
rewrite (Ptrofs.agree64_repr Hp) in H.
rewrite Int64.repr_unsigned in H.
apply Int64repr_Intsigned_zero in H. subst.
reflexivity.
*
unfold Ptrofs.of_ints, Ptrofs.of_intu in *.
unfold Ptrofs.to_int64, Ptrofs.of_int in H.
rewrite (Ptrofs.agree64_repr Hp) in H.
rewrite Int64.repr_unsigned in H.
apply Int64repr_Intunsigned_zero in H. subst.
reflexivity.
-
iIntros "[% $]"; iPureIntro.
destruct si, si'; auto;
unfold Ptrofs.to_int, Ptrofs.of_intu, Ptrofs.of_ints, Ptrofs.of_int in *;
rewrite (Ptrofs.agree32_repr Hp) in H;
rewrite (Ptrofs.agree32_repr Hp);
rewrite -> Int.repr_unsigned in *;
rewrite -> Int.repr_signed in *; rewrite -> Int.repr_unsigned in *; auto.
Qed.

Lemma test_eq_fiddle_signed_yy:
 forall si si' v i,
denote_tc_test_eq (Vptrofs (ptrofs_of_int si i)) v ⊢
denote_tc_test_eq (Vptrofs (ptrofs_of_int si' i)) v.
Proof.
intros.
unfold denote_tc_test_eq.
unfold Vptrofs, ptrofs_of_int.
destruct v; try (iIntros "[]");
destruct Archi.ptr64 eqn:Hp; try (iIntros "[]"); subst.
-
iPureIntro; intros [??]; split; auto.
clear H0.
hnf in H|-*.
destruct si; auto.
*
unfold Ptrofs.of_ints in *.
unfold Ptrofs.to_int, Ptrofs.to_int64 in *.
rewrite -> ?Ptrofs.agree32_repr, ?Ptrofs.agree64_repr,
             ?Int.repr_unsigned, ?Int64.repr_unsigned in H by auto.
assert (i=Int.zero)
  by first [apply Int64repr_Intsigned_zero; solve [auto]
              | rewrite <- (Int.repr_signed i); auto].
subst i.
destruct si'; auto.
*
destruct si'; auto.
unfold Ptrofs.of_intu in H.
try ( (* Archi.ptr64=false case *)
 rewrite -> Ptrofs.to_int_of_int in H by auto;
 subst;
 unfold Ptrofs.of_ints;
 rewrite Int.signed_zero;
 unfold Ptrofs.to_int;
 rewrite Ptrofs.unsigned_repr; [reflexivity |];
 unfold Ptrofs.max_unsigned; rewrite (Ptrofs.modulus_eq32 Hp);
 compute; split; congruence);
(* Archi.ptr64=true case *)
try (unfold Ptrofs.of_int, Ptrofs.to_int64 in H;
rewrite Ptrofs.unsigned_repr in H;
 [apply Int64repr_Intunsigned_zero in H; subst; reflexivity
 | pose proof (Int.unsigned_range i);
   destruct H; split; auto;
   assert (Int.modulus < Ptrofs.max_unsigned)
     by (unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize; rewrite Hp; compute; auto);
    lia]).
-
iIntros "[% $]"; iPureIntro.
destruct si, si'; auto.
*
unfold Ptrofs.of_ints, Ptrofs.of_intu in *.
unfold Ptrofs.to_int64 in H.
rewrite (Ptrofs.agree64_repr Hp) in H.
rewrite Int64.repr_unsigned in H.
apply Int64repr_Intsigned_zero in H. subst.
reflexivity.
*
unfold Ptrofs.of_ints, Ptrofs.of_intu in *.
unfold Ptrofs.to_int64, Ptrofs.of_int in H.
rewrite (Ptrofs.agree64_repr Hp) in H.
rewrite Int64.repr_unsigned in H.
apply Int64repr_Intunsigned_zero in H. subst.
reflexivity.
-
iIntros "[% $]"; iPureIntro.
destruct si, si'; auto;
unfold Ptrofs.to_int, Ptrofs.of_intu, Ptrofs.of_ints, Ptrofs.of_int in *;
rewrite (Ptrofs.agree32_repr Hp) in H;
rewrite (Ptrofs.agree32_repr Hp);
rewrite -> Int.repr_unsigned in *;
rewrite -> Int.repr_signed in *; rewrite -> Int.repr_unsigned in *; auto.
Qed.


Lemma test_order_fiddle_signed_xx:
 forall si si' v i,
denote_tc_test_order v (Vptrofs (ptrofs_of_int si i)) ⊢
denote_tc_test_order v (Vptrofs (ptrofs_of_int si' i)).
Proof.
intros.
unfold denote_tc_test_order.
unfold Vptrofs, ptrofs_of_int.
destruct v; try (iIntros "[]");
destruct Archi.ptr64 eqn:Hp; try (iIntros "[]"); subst.
iPureIntro; intros [??]; split; auto.
clear H.
destruct si, si'; auto;
try ( (* Archi.ptr64 = false *)
unfold Ptrofs.to_int, Ptrofs.of_intu, Ptrofs.of_ints, Ptrofs.of_int in *;
rewrite (Ptrofs.agree32_repr Hp) in H0;
rewrite (Ptrofs.agree32_repr Hp);
rewrite -> Int.repr_unsigned in *;
rewrite -> Int.repr_signed in *; rewrite -> Int.repr_unsigned in *; auto);
try ((* Archi.ptr64 = true *)
  unfold Ptrofs.to_int, Ptrofs.of_intu, Ptrofs.of_ints, Ptrofs.of_int in *;
  unfold Ptrofs.to_int64 in *;
  rewrite -> Ptrofs.unsigned_repr_eq in *;
  change Ptrofs.modulus with Int64.modulus in *;
  rewrite <- Int64.unsigned_repr_eq in *;
  rewrite -> Int64.repr_unsigned in *;
  first [apply Int64repr_Intsigned_zero in H0 
          |apply Int64repr_Intunsigned_zero in H0];
  subst i; reflexivity).
Qed.

Lemma test_order_fiddle_signed_yy:
 forall si si' v i,
denote_tc_test_order (Vptrofs (ptrofs_of_int si i)) v ⊢
denote_tc_test_order (Vptrofs (ptrofs_of_int si' i)) v.
Proof.
intros.
unfold denote_tc_test_order.
unfold Vptrofs, ptrofs_of_int.
destruct v; try iIntros "[]";
destruct Archi.ptr64 eqn:Hp; try iIntros "[]"; subst.
iPureIntro; intros [??]; split; auto.
clear H0.
destruct si, si'; auto;
try ( (* Archi.ptr64 = false *)
unfold Ptrofs.to_int, Ptrofs.of_intu, Ptrofs.of_ints, Ptrofs.of_int in *;
rewrite (Ptrofs.agree32_repr Hp) in H;
rewrite (Ptrofs.agree32_repr Hp);
rewrite -> Int.repr_unsigned in *;
rewrite -> Int.repr_signed in *; rewrite -> Int.repr_unsigned in *; auto);
try ((* Archi.ptr64 = true *)
  unfold Ptrofs.to_int, Ptrofs.of_intu, Ptrofs.of_ints, Ptrofs.of_int in *;
  unfold Ptrofs.to_int64 in *;
  rewrite -> Ptrofs.unsigned_repr_eq in *;
  change Ptrofs.modulus with Int64.modulus in *;
  rewrite <- Int64.unsigned_repr_eq in *;
  rewrite -> Int64.repr_unsigned in *;
  first [apply Int64repr_Intsigned_zero in H 
          |apply Int64repr_Intunsigned_zero in H];
  subst i; reflexivity).
Qed.

Lemma denote_tc_nonzero_e':
 forall i, denote_tc_nonzero (Vint i) ⊢ ⌜Int.eq i Int.zero = false⌝.
Proof.
simpl; intros; iPureIntro; apply Int.eq_false.
Qed.

Lemma denote_tc_nodivover_e':
 forall i j, denote_tc_nodivover (Vint i) (Vint j) ⊢
   ⌜Int.eq i (Int.repr Int.min_signed) && Int.eq j Int.mone = false⌝.
Proof.
simpl; intros; iPureIntro.
rewrite andb_false_iff.
destruct (Int.eq j Int.mone) eqn: Hj; auto.
apply Int.same_if_eq in Hj as ->.
destruct (Int.eq) eqn: Hi; auto.
apply Int.same_if_eq in Hi as ->; tauto.
Qed.

Lemma denote_tc_nonzero_e64':
 forall i, denote_tc_nonzero (Vlong i) ⊢ ⌜Int64.eq i Int64.zero = false⌝.
Proof.
simpl; intros; iPureIntro; apply Int64.eq_false.
Qed.

Lemma denote_tc_nodivover_e64_ll':
 forall i j, denote_tc_nodivover (Vlong i) (Vlong j) ⊢
   ⌜Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone = false⌝.
Proof.
simpl; intros; iPureIntro.
rewrite andb_false_iff.
destruct (Int64.eq j Int64.mone) eqn: Hj; auto.
apply Int64.same_if_eq in Hj as ->.
destruct (Int64.eq) eqn: Hi; auto.
apply Int64.same_if_eq in Hi as ->; tauto.
Qed.

Lemma denote_tc_nodivover_e64_il':
 forall s i j,
   Int64.eq (cast_int_long s i) (Int64.repr Int64.min_signed) && Int64.eq j Int64.mone = false.
Proof.
intros.
assert (⊢denote_tc_nodivover (Vint i) (Vlong j)) as H by auto.
rewrite (denote_tc_nodivover_e64_il s) in H.
apply ouPred.pure_soundness in H.
rewrite andb_false_iff.
destruct (Int64.eq j Int64.mone) eqn: Hj; auto.
apply Int64.same_if_eq in Hj as ->.
destruct (Int64.eq) eqn: Hi; auto.
apply Int64.same_if_eq in Hi; tauto.
Qed.

Lemma denote_tc_nodivover_e64_li':
 forall s i j, denote_tc_nodivover (Vlong i) (Vint j) ⊢
   ⌜Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq (cast_int_long s j) Int64.mone = false⌝.
Proof.
intros.
rewrite andb_false_iff (denote_tc_nodivover_e64_li s); iPureIntro.
destruct (Int64.eq i _) eqn: Hi; auto.
apply Int64.same_if_eq in Hi as ->.
destruct (Int64.eq) eqn: Hj; auto.
apply Int64.same_if_eq in Hj; tauto.
Qed.

Lemma Int64_eq_repr_signed32_nonzero':
  forall i, Int.eq i Int.zero = false ->
             Int64.eq (Int64.repr (Int.signed i)) Int64.zero = false.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
pose proof (Int64_eq_repr_signed32_nonzero i H0).
apply Int64.eq_false; auto.
Qed.

Lemma Int64_eq_repr_unsigned32_nonzero':
  forall i, Int.eq i Int.zero = false ->
             Int64.eq (Int64.repr (Int.unsigned i)) Int64.zero = false.
Proof.
intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
pose proof (Int64_eq_repr_unsigned32_nonzero i H0).
apply Int64.eq_false; auto.
Qed.

Lemma Int64_eq_repr_int_nonzero':
  forall s i, Int.eq i Int.zero = false ->
    Int64.eq (cast_int_long s i) Int64.zero = false.
Proof.
  intros.
pose proof (Int.eq_spec i Int.zero). rewrite H in H0. clear H.
pose proof (Int64_eq_repr_int_nonzero s i H0).
apply Int64.eq_false; auto.
Qed.

Lemma denote_tc_igt_e':
  forall i j, denote_tc_igt j (Vint i) ⊢
        ⌜Int.ltu i j = true⌝.
Proof.
intros. rewrite /Int.ltu denote_tc_igt_e; iPureIntro.
intros; rewrite if_true; auto.
Qed.

Lemma denote_tc_lgt_e':
  forall i j, denote_tc_lgt j (Vlong i) ⊢
        ⌜Int64.ltu i j = true⌝.
intros. rewrite /Int64.ltu denote_tc_lgt_e; iPureIntro.
intros; rewrite if_true; auto.
Qed.

Lemma denote_tc_iszero_long_e':
 forall i,
  denote_tc_iszero (Vlong i) ⊢
  ⌜Int64.eq (Int64.repr (Int64.unsigned i)) Int64.zero = true⌝.
Proof.
intros; simpl; iPureIntro.
pose proof (Int64.eq_spec i Int64.zero).
destruct (Int64.eq i Int64.zero);
  try contradiction.
subst; reflexivity.
Qed.


Lemma sem_binary_operation_stable: 
  forall (cs1: compspecs) cs2 
   (CSUB: forall id co, (@cenv_cs cs1)!!id = Some co -> cs2!!id = Some co)
   b v1 e1 v2 e2 m v t rho,
   (* mem_auth m ∗ *) denote_tc_assert(CS := cs1) (isBinOpResultType(CS := cs1) b e1 e2 t) rho ⊢
   ⌜sem_binary_operation (@cenv_cs cs1) b v1 (typeof e1) v2 (typeof e2) m = Some v ->
    sem_binary_operation cs2 b v1 (typeof e1) v2 (typeof e2) m = Some v⌝.
Proof.
intros.
assert (CONSIST:= @cenv_consistent cs1).
rewrite den_isBinOpR /=.
forget (op_result_type (Ebinop b e1 e2 t)) as err.
forget (arg_type (Ebinop b e1 e2 t)) as err0.
destruct b; simpl; auto;
unfold Cop.sem_add, Cop.sem_sub, binarithType';
rewrite ?classify_add_eq ?classify_sub_eq;
repeat lazymatch goal with
| |-context [classify_add'] => pose proof (classify_add_reflect (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_add' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into HC end
| |-context [classify_sub'] => pose proof (classify_sub_reflect (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_sub' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into HC end
| |-context [classify_binarith'] => 
   pose proof (classify_binarith_rel (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_binarith' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into HC end;
   try destruct s
| |-context [classify_shift'] => pose proof (classify_shift_reflect (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_shift' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into HC end
| |-context [classify_cmp'] => pose proof (classify_cmp_reflect (typeof e1) (typeof e2)) as Hrel; inv Hrel;
   match goal with H : _ = classify_cmp' _ _ |- _ => let C := fresh "C" in symmetry in H; rename H into HC end
end; simpl; unfold_lift; rewrite ?tc_bool_e ?tc_andp_sound; first [iIntros (H) || auto]; iPureIntro; decompose [and] H;
unfold Cop.sem_add_ptr_int, Cop.sem_add_ptr_long in *;
simpl in *;
rewrite -> (sizeof_stable _ _ CSUB) by auto; auto.
Qed.

Lemma eq_block_lem':
 forall a, eq_block a a = left (eq_refl a).
Proof.
intros.
destruct (eq_block a). f_equal. apply proof_irr.
congruence.
Qed.

Lemma isptr_e:
 forall {v}, isptr v -> exists b ofs, v = Vptr b ofs.
Proof. destruct v; try contradiction; eauto. Qed.

Lemma is_int_e': forall {sz sg v}, 
  is_int sz sg v -> exists i, v = Vint i.
Proof. destruct v; try contradiction; eauto. Qed.

Lemma is_long_e: forall {v}, is_long v -> exists i, v = Vlong i.
Proof. destruct v; try contradiction; eauto. Qed.

Lemma is_single_e: forall {v}, is_single v -> exists f, v = Vsingle f.
Proof. destruct v; try contradiction; eauto. Qed.

Lemma is_float_e: forall {v}, is_float v -> exists f, v = Vfloat f.
Proof. destruct v; try contradiction; eauto. Qed.

Definition weak_valid_pointer' m v :=
  match v with Vptr b o => Mem.weak_valid_pointer m b (Ptrofs.unsigned o) | _ => false end.

Lemma sem_cast_relate' : forall ty1 ty2 v v' m
  (Hty1 : eqb_type ty1 int_or_ptr_type = false) (Hty2 : eqb_type ty2 int_or_ptr_type = false)
  (Hv : tc_val ty1 v) (Hvalid : forall t a, stupid_typeconv ty1 = Tpointer t a -> weak_valid_pointer' m v = true),
  sem_cast ty1 ty2 v = Some v' ->
  Cop.sem_cast v ty1 ty2 m = Some v'.
Proof.
  unfold sem_cast, Cop.sem_cast; intros.
  rewrite -> classify_cast_eq by auto.
  destruct (classify_cast ty1 ty2) eqn: Hclass; auto.
  - inv H.
    unfold classify_cast in Hclass.
    destruct ty1, ty2; try destruct i; try destruct f; try destruct i0; try destruct f0; try rewrite -> Hty1 in *; try rewrite -> Hty2 in *; try discriminate;
      unfold tc_val in Hv; rewrite ?Hty1 in Hv; destruct v'; try contradiction; auto.
  - destruct v; try discriminate; try solve [inv H; reflexivity].
    unfold weak_valid_pointer' in Hvalid.
    simpl in H.
    simple_if_tac; inv H.
    unfold classify_cast in Hclass; unfold tc_val in Hv.
    destruct ty1, ty2; try destruct i; try destruct f; try destruct i0; try destruct f0; try rewrite -> Hty1 in *; try rewrite -> Hty2 in *; try discriminate; try contradiction; try (destruct i1; discriminate);
      erewrite Hvalid; eauto.
Qed.

Lemma sem_binarith_relate : forall sem_int sem_long sem_float sem_single ty1 ty2 v1 v2 v m
  (Hty1 : eqb_type ty1 int_or_ptr_type = false) (Hty2 : eqb_type ty2 int_or_ptr_type = false)
  (Hv1 : tc_val ty1 v1) (Hvalid1 : forall t a, stupid_typeconv ty1 = Tpointer t a -> weak_valid_pointer' m v1 = true)
  (Hv2 : tc_val ty2 v2) (Hvalid2 : forall t a, stupid_typeconv ty2 = Tpointer t a -> weak_valid_pointer' m v2 = true),
  sem_binarith sem_int sem_long sem_float sem_single ty1 ty2 v1 v2 = Some v ->
  Cop.sem_binarith sem_int sem_long sem_float sem_single v1 ty1 v2 ty2 m = Some v.
Proof.
  unfold sem_binarith, Cop.sem_binarith; intros.
  destruct (classify_binarith ty1 ty2) eqn: Hclass; auto.
  - unfold both_int in H.
    destruct (sem_cast ty1 _ _) eqn: Hcast1; try discriminate.
    destruct v0; try discriminate.
    destruct (sem_cast ty2 _ _) eqn: Hcast2; try discriminate.
    destruct v0; try discriminate.
    eapply sem_cast_relate' in Hcast1 as ->; auto.
    eapply sem_cast_relate' in Hcast2 as ->; auto.
  - unfold both_long in H.
    destruct (sem_cast ty1 _ _) eqn: Hcast1; try discriminate.
    destruct v0; try discriminate.
    destruct (sem_cast ty2 _ _) eqn: Hcast2; try discriminate.
    destruct v0; try discriminate.
    eapply sem_cast_relate' in Hcast1 as ->; auto.
    eapply sem_cast_relate' in Hcast2 as ->; auto.
  - unfold both_float in H.
    destruct (sem_cast ty1 _ _) eqn: Hcast1; try discriminate.
    destruct v0; try discriminate.
    destruct (sem_cast ty2 _ _) eqn: Hcast2; try discriminate.
    destruct v0; try discriminate.
    eapply sem_cast_relate' in Hcast1 as ->; auto.
    eapply sem_cast_relate' in Hcast2 as ->; auto.
  - unfold both_single in H.
    destruct (sem_cast ty1 _ _) eqn: Hcast1; try discriminate.
    destruct v0; try discriminate.
    destruct (sem_cast ty2 _ _) eqn: Hcast2; try discriminate.
    destruct v0; try discriminate.
    eapply sem_cast_relate' in Hcast1 as ->; auto.
    eapply sem_cast_relate' in Hcast2 as ->; auto.
Qed.

Lemma sem_shift_relate : forall sem_int sem_long ty1 ty2 v1 v2 v
  (Hnoover : match classify_shift ty1 ty2 with
            | shift_case_ii _ => match v2 with Vint i2 => Int.unsigned i2 < Int.unsigned Int.iwordsize | _ => True end
            | shift_case_ll _ => match v2 with Vlong i2 => Int64.unsigned i2 < Int64.unsigned Int64.iwordsize | _ => True end
            | shift_case_il _ => match v2 with Vlong i2 => Int64.unsigned i2 < 32 | _ => True end
            | shift_case_li _ => match v2 with Vint i2 => Int.unsigned i2 < Int.unsigned Int64.iwordsize' | _ => True end
            | _ => True
            end),
  sem_shift ty1 ty2 sem_int sem_long v1 v2 = Some v ->
  Cop.sem_shift sem_int sem_long v1 ty1 v2 ty2 = Some v.
Proof.
  unfold sem_shift, Cop.sem_shift; intros.
  destruct (classify_shift ty1 ty2) eqn: Hclass; auto.
  - unfold sem_shift_ii in H.
    destruct v2; auto.
    unfold Int.ltu; if_tac; auto; lia.
  - unfold sem_shift_ii in H.
    destruct v2; auto.
    unfold Int64.ltu; if_tac; auto; lia.
  - unfold sem_shift_il in H.
    destruct v2; auto.
    unfold Int64.ltu; if_tac; auto.
    rewrite -> Int64.unsigned_repr in *; try lia.
    by compute.
  - unfold sem_shift_li in H.
    destruct v2; auto.
    unfold Int.ltu; if_tac; auto; lia.
Qed.

End mpred.
