Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.
Require Import Lia.
Require malloc. (*TODO: remove this dependency by making the constants parametrs of ASI_malloc,
and nstantiate them in VSU_malloc*)

(* This file has background for memmgr that's independent of the program file *)

(*+ misc *)

(* from VFA, for Z.ltb and Z.eqb *)
Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof. intros x y. apply iff_reflect. symmetry. apply Z.eqb_eq. Qed.
#[export] Hint Resolve Z.ltb_spec0 beq_reflect : bdestruct.
(*  ReflOmegaCore.ZOmega.IP.beq_reflect beq_reflect : bdestruct. *)

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof. intros x y. apply iff_reflect. symmetry. apply Z.leb_le. Qed.
#[export] Hint Resolve ble_reflect : bdestruct.

Lemma andb_reflect : forall x y, reflect (x = true /\ y = true) (x && y).
Proof.
  intros. apply iff_reflect. split.
  intros [Hx Hy]. subst. reflexivity.
  unfold andb. simple_if_tac; intuition.
Qed.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop); assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].


(* A bit of infrastructure for brute force proof of claim3. 
   TODO consider using Zseq in place of seq in mem_mgr. 
*)
Definition Zseq n := 
  if n <? 0 then [] else map Z.of_nat (seq 0 (Z.to_nat n)).

Lemma in_Zseq: forall len n : Z, len >= 0 -> ( In n (Zseq len) <-> (0 <= n < len) ). 
Proof.
  intros. unfold Zseq.  bdestruct (len <? 0); try lia. clear H0.
  rewrite in_map_iff. split.
  - intros. destruct H0. destruct H0. 
    rewrite in_seq in H1.
    rewrite <- H0. split. rep_lia. destruct H1. simpl in H2.
    apply inj_lt in H2. rewrite Z2Nat.id in H2 by lia. auto.
  - intro. exists (Z.to_nat n).
    split; try rep_lia.
    rewrite in_seq.
    assert (0 <= Z.to_nat n)%nat by (destruct H0; lia). 
    simpl. split; try lia.
Qed.

Lemma forall_Forall_range: 
     forall (P : Z -> Prop) (n : Z), 0 <= n ->
       ( (forall x, 0 <= x < n -> P x) <-> Forall P (Zseq n) ).
Proof.
  intros.
  assert (Hi:  
          (forall x : Z, 0 <= x < n -> P x) <->  (forall x : Z, In x (Zseq n) -> P x)).
  { split. - intros; apply H0; rewrite <- in_Zseq; try lia; auto.
    - intros; apply H0; rewrite in_Zseq; try lia. }
  rewrite Hi. rewrite Forall_forall. reflexivity.
Qed.

(* background for upd_Znth_same_val, belongs in a library *)
Lemma list_extensional {A}{d: Inhabitant A}: 
  forall (xs ys: list A),
  Zlength xs = Zlength ys ->
  (forall i, 0 <= i < Zlength xs -> Znth i xs = Znth i ys) -> xs = ys.
Proof.
  intros xs.
  induction xs. 
  - intros [|w ws] H Hi. reflexivity.
    rewrite Zlength_nil in H. rewrite Zlength_cons in H. 
    assert (0 <= Zlength ws) by apply Zlength_nonneg. lia.
  - intros [|w ws] H Hi. 
    rewrite Zlength_nil in H; rewrite Zlength_cons in H. 
    assert (H0: 0 <= Zlength xs) by apply Zlength_nonneg; lia.
    specialize (IHxs ws). 
    assert (H1: Zlength xs = Zlength ws) by 
        ( do 2 rewrite Zlength_cons in H; apply Z.succ_inj in H; auto).
    assert (H2: 0<=0<Zlength (a::xs)) by 
        (split; try lia; rewrite Zlength_cons; rep_lia).
    assert (H3: Znth 0 (a :: xs) = Znth 0 (w :: ws)) by (apply Hi; auto).
    apply IHxs in H1.
    + subst. apply Hi in H2. do 2 rewrite Znth_0_cons in H2. subst. reflexivity.
    + apply Hi in H2. do 2 rewrite Znth_0_cons in H2.  subst. 
      intros. specialize (Hi (i+1)).   do 2 rewrite Znth_pos_cons in Hi; try lia.
      replace (i+1-1) with i in Hi by lia.
      apply Hi. split; try lia. rewrite Zlength_cons; rep_lia.
Qed.

Lemma upd_Znth_same_val {A} {d: Inhabitant A}:
  forall n (xs: list A), 0 <= n < Zlength xs ->
   (upd_Znth n xs (Znth n xs)) = xs.
Proof.
  intros.  symmetry.  eapply list_extensional.
  rewrite upd_Znth_Zlength; auto.
  intros.  bdestruct (n =? i).
  - subst. rewrite upd_Znth_same; auto. 
  - rewrite upd_Znth_diff; auto.
Qed.

Lemma upd_Znth_twice {A} {d: Inhabitant A}:
forall n x y (xs:list A),
   0 <= n < Zlength xs ->
   (upd_Znth n (upd_Znth n xs x) y) = (upd_Znth n xs y).
Proof.
  intros n x y xs H. symmetry.
  eapply list_extensional.
  repeat (rewrite upd_Znth_Zlength; auto).
  intros. bdestruct (n =? i).
  - subst. repeat rewrite upd_Znth_same; auto. 
    rewrite upd_Znth_Zlength in *; auto.
  - assert (0 <= i < Zlength xs) by (rewrite upd_Znth_Zlength in H0; auto). 
    repeat rewrite upd_Znth_diff; auto;
    rewrite upd_Znth_Zlength in *; auto.
Qed. 


Definition zip3 (bs:list nat) (cs:list val) (ds:list Z) := (combine (combine bs cs) ds).

Lemma Zlength_zip3:
   forall bs cs ds,
   Zlength bs = Zlength cs -> Zlength cs = Zlength ds ->
   Zlength (zip3 bs cs ds) = Zlength bs.
Proof.
  intros bs cs ds Hbc Hcd.  unfold zip3.  do 2 rewrite Zlength_correct in *.
  do 2 rewrite combine_length.  
  do 2 rewrite Nat2Z.inj_min. rewrite Hbc. rewrite <- Hcd.  
  rewrite Z.min_r; try reflexivity.  rewrite Z.min_r; try reflexivity.
Qed.

Lemma Znth_zip3:
   forall bs cs ds n,
   Zlength bs = Zlength cs -> Zlength cs = Zlength ds ->
   0 <= n < Zlength bs ->
   Znth n (zip3 bs cs ds) = (Znth n bs, Znth n cs, Znth n ds).
Proof.
  intros bs cs ds n Hbc Hcd Hn. 
  pose proof (Zlength_zip3 bs cs ds Hbc Hcd) as Hz.
  unfold zip3. rewrite <- nth_Znth.
- rewrite combine_nth. rewrite combine_nth.
  rewrite nth_Znth; try lia. rewrite nth_Znth; try lia.
  rewrite nth_Znth; try lia; reflexivity.
  repeat rewrite Zlength_correct in *; lia. rewrite combine_length. 
  assert (H3: length bs = length cs) by (repeat rewrite Zlength_correct in *; lia).
  assert (H4: length cs = length ds) by (repeat rewrite Zlength_correct in *; lia).
  rewrite H3; rewrite H4; rewrite Nat.min_id; reflexivity.
- unfold zip3 in Hz; lia.
Qed.


Lemma sublist_zip3:
forall i j bs cs ds, 
  0 <= i <= j -> j <= Zlength bs ->
  Zlength bs = Zlength cs -> Zlength cs = Zlength ds ->
(sublist i j (zip3 bs cs ds)) = 
(zip3 (sublist i j bs) (sublist i j cs) (sublist i j ds)).
Proof. 
  intros.  destruct H as [Hi Hij]. 
  apply list_extensional.
  - repeat (try rewrite Zlength_sublist; try rewrite Zlength_zip3; try lia).
  - intros.  destruct H as [Hi0lo Hi0hi].
  assert (Hi0: i0 < j - i) by
    (rewrite Zlength_sublist in Hi0hi; auto; rewrite Zlength_zip3; try lia).
  repeat (try rewrite Znth_sublist; try rewrite Znth_zip3; try rewrite Zlength_sublist; 
          try lia); auto.
Qed.

Lemma In_zip3:
  forall x bs cs ds,
    In x (zip3 bs cs ds) -> 
    In (fst (fst x)) bs /\ In (snd (fst x)) cs /\ In (snd x) ds.
Proof.
intros.
assert (Hx: In (fst x) (combine bs cs)).
{ unfold zip3 in *.
eapply in_combine_l with (y:=snd x).
rewrite <- surjective_pairing. apply H.
}
split3.
- eapply in_combine_l with (y:=snd (fst x)).
  rewrite <- surjective_pairing. apply Hx.
- unfold zip3 in *.
  eapply in_combine_r with (x:=fst (fst x)).
  rewrite <- surjective_pairing. apply Hx.
- unfold zip3 in *.
  eapply in_combine_r with (x:=fst x).
  rewrite <- surjective_pairing. 
  apply H.
Qed.

Lemma Zdiv_prod:
  forall a b c, (a*b|c) -> (a|c).
Proof.
  intros. unfold Z.divide in *. destruct H as [z Hz]. exists (z*b)%Z. lia.
Qed.

Ltac simple_if_tac' H := 
  match goal with |- context [if ?A then _ else _] => 
    lazymatch type of A with
    | bool => destruct A eqn: H
    | sumbool _ _ => fail "Use if_tac instead of simple_if_tac, since your expression "A" has type sumbool"
    | ?t => fail "Use simple_if_tac only for bool; your expression"A" has type" t
  end end.
Ltac simple_if_tac'' := let H := fresh in simple_if_tac' H.


(*+ VST related *)


(* maybe some of the next lemmas belong in floyd *)

Lemma malloc_compatible_prefix:
  forall n s p, 0 <= n <= s -> 
  malloc_compatible s p -> malloc_compatible n p.
Proof.
  intros n s p H H0; unfold malloc_compatible in *; destruct p; try auto.
  destruct H0. split; try assumption; rep_lia.
Qed.

Lemma malloc_compatible_offset:
  forall n m p, 0 <= n -> 0 <= m ->
  malloc_compatible (n+m) p -> (natural_alignment | m) -> 
  malloc_compatible n (offset_val m p).
Proof.
  intros n m p Hn Hm Hp Ha. unfold malloc_compatible in *.
  destruct p; try auto. destruct Hp as [Hi Hinm]. simpl.  split.
- replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr m)))
     with (m + (Ptrofs.unsigned i)).
  apply Z.divide_add_r; auto.
  rewrite Ptrofs.add_unsigned;
  rewrite Ptrofs.unsigned_repr; rewrite Ptrofs.unsigned_repr;
     try lia; try split; try rep_lia. 
- replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr m)))
     with (m + (Ptrofs.unsigned i)); try rep_lia. 
  rewrite Ptrofs.add_unsigned;
  rewrite Ptrofs.unsigned_repr; rewrite Ptrofs.unsigned_repr;
     try lia; try split; try rep_lia. 
Qed. 

Lemma malloc_compatible_offset_isptr:
  forall n m q, malloc_compatible n (offset_val m q) -> isptr q.
Proof. intros. destruct q; auto. unfold isptr; auto. 
Qed.

Ltac mcoi_tac := 
  eapply malloc_compatible_offset_isptr;  
  match goal with | H: malloc_compatible _ _ |- _ => apply H end.

(* variations on VST's memory_block_split *)
Local Open Scope logic.

Lemma memory_block_split_repr:
  forall (sh : share) (b : block) (ofs : ptrofs) (n m : Z), 0 <= n -> 0 <= m ->
       n + m <= n + m + (Ptrofs.unsigned ofs) < Ptrofs.modulus -> 
       memory_block sh (n + m) (Vptr b ofs) =
       memory_block sh n (Vptr b ofs) *
       memory_block sh m (Vptr b (Ptrofs.add ofs (Ptrofs.repr n))).
Proof.
  intros sh b ofs n m Hn Hm Hnm.
  assert (Hofs: ofs = (Ptrofs.repr (Ptrofs.unsigned ofs)))
    by (rewrite Ptrofs.repr_unsigned; auto). 
  rewrite Hofs.
  normalize.
  erewrite memory_block_split; try assumption.
  reflexivity.
Qed.

Lemma memory_block_split_offset:
  forall (sh : share) (p : val) (n m : Z), 0 <= n -> 0 <= m ->
       memory_block sh (n + m) p =
       memory_block sh n p *
       memory_block sh m (offset_val n p).
Proof.
  intros sh p n m Hn Hm.
  apply pred_ext. (* to enable use of entailer - at cost of duplicate proof *)
  - (* LHS |-- RHS *)
    destruct p; try entailer!.
    rewrite <- offset_val_unsigned_repr.
    simpl.
    rewrite memory_block_split_repr; try assumption. 
    + entailer!. 
      rewrite Ptrofs.unsigned_repr. cancel.
      unfold size_compatible' in *; rep_lia. 
    + unfold size_compatible' in *; rep_lia.
  - (* RHS |-- LHS 
       TODO almost same proof, followed by clumsy finish *)
    destruct p; try entailer!. 
    rewrite <- offset_val_unsigned_repr.
    simpl.  rewrite memory_block_split_repr; try assumption. 
    entailer!. rewrite Ptrofs.unsigned_repr. cancel.
    unfold size_compatible' in *. rep_lia. 
    unfold size_compatible' in *.
    split. rep_lia. 
    simpl in *.
    rewrite Ptrofs.modulus_eq32; try unfold Archi.ptr64; auto.
    replace (n+m+Ptrofs.unsigned i) with ((n + Ptrofs.unsigned i)+m) by lia.
    assert (Hni: 
              n + Ptrofs.unsigned i = (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr n)))).
    { rewrite Ptrofs.add_unsigned. rewrite Ptrofs.unsigned_repr; try rep_lia.
      rewrite Ptrofs.unsigned_repr; try rep_lia. 
      split; try rep_lia. rewrite Ptrofs.unsigned_repr; rep_lia. 
    }
    rewrite Hni; rep_lia.
Qed.

(* Two lemmas from hashtable exercise *)
Lemma iter_sepcon_1:
  forall {A}{d: Inhabitant A} (a: A) (f: A -> mpred), iter_sepcon f [a] = f a.
Proof. intros. unfold iter_sepcon. normalize. 
Qed.

Lemma iter_sepcon_split3: 
  forall {A}{d: Inhabitant A} (i: Z) (al: list A) (f: A -> mpred),
   0 <= i < Zlength al   -> 
  iter_sepcon f al = 
  iter_sepcon f (sublist 0 i al) * f (Znth i al) * iter_sepcon f (sublist (i+1) (Zlength al) al).
Proof. 
  intros. rewrite <- (sublist_same 0 (Zlength al) al) at 1 by auto.
  rewrite (sublist_split 0 i (Zlength al)) by rep_lia.
  rewrite (sublist_split i (i+1) (Zlength al)) by rep_lia.
  rewrite sublist_len_1 by rep_lia.
  rewrite iter_sepcon_app. rewrite iter_sepcon_app. rewrite iter_sepcon_1.
  rewrite sepcon_assoc. reflexivity.
Qed.

(* Pointer misc *)

Lemma weak_valid_pointer_end:
forall p,
valid_pointer (offset_val (-1) p) |-- weak_valid_pointer p.
Proof.
intros.
unfold valid_pointer, weak_valid_pointer.
change predicates_hered.orp with orp. (* delete me *)
apply orp_right2.
destruct p; try solve [simpl; auto].
all: try apply derives_refl.
simpl.
change predicates_hered.FF with FF. apply FF_left.
unfold offset_val.
hnf.
Transparent Nveric.
red.
Opaque Nveric.
red.
hnf; intros; try contradiction.
simpl.
replace (Ptrofs.unsigned i + -1)
with (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (-1))) + 0); auto.
(*clear H.
rewrite Z.add_0_r. *)
Abort.  (* Not true *)

Lemma max_unsigned_32: Ptrofs.max_unsigned = Int.max_unsigned.
Proof.
  unfold Ptrofs.max_unsigned, Int.max_unsigned.
  unfold Ptrofs.modulus, Int.modulus.
  unfold Ptrofs.wordsize, Int.wordsize.
  unfold Wordsize_Ptrofs.wordsize, Wordsize_32.wordsize.
  unfold Archi.ptr64.
  reflexivity.
Qed.

Lemma ptrofs_add_for_alignment:
   forall poff n, 0 <= n -> Ptrofs.unsigned poff + n <= Ptrofs.max_unsigned ->
     Ptrofs.unsigned (Ptrofs.add poff (Ptrofs.repr n))
     = Ptrofs.unsigned poff + n. 
Proof.
  intros.
  replace poff with (Ptrofs.repr(Ptrofs.unsigned poff)) at 1
    by (rewrite Ptrofs.repr_unsigned; reflexivity).
  rewrite ptrofs_add_repr.
  rewrite Ptrofs.unsigned_repr; try reflexivity.
  split.
  assert (0 <= Ptrofs.unsigned poff) by apply Ptrofs.unsigned_range.
  rep_lia.
  assumption.
Qed.


(*+ constants *)

(* These constants should have the same values as the same-named constants
   in the code. *)

Definition WORD: Z := 4.  (* sizeof(size_t) is 4 for 32bit Clight *)
Definition ALIGN: Z := 2.
Definition BINS: Z.
   let x := constr:(gvar_info malloc.v_bin) in
   let x := eval simpl in x in 
   match x with tarray _ ?B => exact B
   end.
Defined.

Definition BIGBLOCK: Z := ((Z.pow 2 17) * WORD).
Definition WA: Z := (WORD*ALIGN) - WORD. (* WASTE at start of block *)

(* Note re CompCert 3: I'm currently using tuint for what in the code
is size_t.  That works for 32bit mode.  To generalize the proof
to 64bit as well, it may work to replace tuint by t_size_t defined like 
t_size_t := if Archi.ptr64 then tulong else tuint
*)

Lemma WORD_ALIGN_aligned:
  (natural_alignment | WORD * ALIGN)%Z.
Proof. unfold natural_alignment, WORD, ALIGN; simpl. apply Z.divide_refl. Qed.


(* The following hints empower rep_lia and lessen the need for 
   manually unfolding the constant definitions. *)

Ltac compute_eq A := let x := eval vm_compute in A in
    exact (A = x).

Lemma BINS_eq: ltac:(compute_eq BINS).  Proof. reflexivity. Qed.
#[export] Hint Rewrite BINS_eq : rep_lia.
Global Opaque BINS. (* make rewrites only happen in rep_lia *)

Lemma BIGBLOCK_eq: ltac:(compute_eq BIGBLOCK).  Proof. reflexivity. Qed.
#[export] Hint Rewrite BIGBLOCK_eq : rep_lia.
Global Opaque BIGBLOCK.

Lemma WORD_eq: ltac:(compute_eq WORD).  Proof. reflexivity. Qed.
#[export] Hint Rewrite WORD_eq : rep_lia.
Global Opaque WORD.

Lemma ALIGN_eq: ltac:(compute_eq ALIGN).  Proof. reflexivity. Qed.
#[export] Hint Rewrite ALIGN_eq : rep_lia.
Global Opaque ALIGN.

Lemma WA_eq: ltac:(compute_eq WA).  Proof. reflexivity. Qed.
#[export] Hint Rewrite WA_eq : rep_lia.
Global Opaque WA.

(*+ bin/size conversions and their properties *)

Definition bin2sizeZ := fun b: Z => (((b+1)*ALIGN - 1) * WORD)%Z. 

Definition size2binZ : Z -> Z := fun s => 
   if (bin2sizeZ(BINS-1)) <? s 
   then -1 
   else (s+(WORD * (ALIGN-1))-1) / (WORD * ALIGN).

Lemma bin2size_range: 
  forall b, 0 <= b < BINS -> 
    WORD <= bin2sizeZ b <= bin2sizeZ(BINS-1). 
Proof. intros. unfold bin2sizeZ in *. split; simpl in *; try rep_lia. Qed.

Lemma  bin2sizeBINS_eq: ltac:(compute_eq (bin2sizeZ(BINS-1))).
Proof. reflexivity. Qed.
#[export] Hint Rewrite bin2sizeBINS_eq: rep_lia.

Lemma bin2size_align:
  forall b, 0 <= b < BINS -> (natural_alignment | bin2sizeZ b + WORD).
Proof. (* by counting in unary *)
  apply forall_Forall_range; try rep_lia; rewrite BINS_eq; rewrite WORD_eq.
  unfold natural_alignment.
  cbn.
  repeat constructor;
  (apply Zmod_divide; [intro Hx; inv Hx | reflexivity ]).
Qed.


Lemma size2bin_range: 
  forall s, 0 <= s <= bin2sizeZ(BINS-1) -> 0 <= size2binZ s < BINS.
Proof. 
  intros. unfold size2binZ. 
  bdestruct (bin2sizeZ (BINS - 1) <? s); try lia.
  rewrite bin2sizeBINS_eq in *.
  rewrite WORD_eq. rewrite ALIGN_eq. rewrite BINS_eq. simpl. 
  replace (s + 4 - 1) with (s + 3) by lia.
  split.
  - apply Z.div_pos; rep_lia.
  - apply Z.div_lt_upper_bound; rep_lia.
Qed.

Fact small_chunks_nonempty: bin2sizeZ(size2binZ(0)) > 0.
Proof. reflexivity. Qed.

Lemma claim1: forall s, 
  s <= bin2sizeZ(BINS-1) -> s <= bin2sizeZ(size2binZ s).
Proof. 
  intros s H. 
  unfold bin2sizeZ, size2binZ in *. 
  bdestruct (bin2sizeZ (BINS - 1) <? s); try rep_lia.
  rewrite WORD_eq in *; rewrite ALIGN_eq in *; rewrite BINS_eq in *.
  simpl in *; clear H0.
  replace ((((s + 4 - 1) / 8 + 1) * 2 - 1) * 4)%Z
     with ((s + 4 - 1) / 8 * 8 + 4)%Z by lia.
  replace (s + 4 - 1)%Z with (s + 3) by lia.
 (*OLD proof
  assert (Zmod_eq': forall a b, b > 0 -> (a / b * b)%Z = a - a mod b) 
     by (intros; rewrite Zmod_eq; lia);
  rewrite Zmod_eq' by lia; clear Zmod_eq'.
  replace (s + 3 - (s + 3) mod 8 + 4)%Z  with (s + 7 - (s + 3) mod 8)%Z by lia.
  assert ( 0 <= (s+3) mod 8 < 8 ) by (apply Z_mod_lt; lia); lia.*)

  (*NOW:*)
  specialize (Z_div_mod (s + 3) 8); intros X.
  destruct (Z.div_eucl (s + 3) 8) as [eu1 eu2]; lia.
Qed.

Lemma claim2: forall s, 
  0 <= s <= bin2sizeZ(BINS-1) -> 0 <= size2binZ s < BINS.
Proof. 
  intros; unfold bin2sizeZ in *; unfold size2binZ.
  rewrite WORD_eq in *;  rewrite ALIGN_eq in *.
  bdestruct (bin2sizeZ (BINS - 1) <? s); try rep_lia.
  rewrite Z.sub_add in H.
  change (4*(2-1))%Z with 4.
  simpl.
  split.
  apply Z.div_pos; try lia.
  apply Z.div_lt_upper_bound; try lia.
Qed.

Lemma claim3: forall s, 0 <= s <= bin2sizeZ(BINS-1) 
    -> size2binZ(bin2sizeZ(size2binZ(s))) = size2binZ(s).
Proof. 
  intros. 
  pose proof ((size2bin_range s) H). 
  pose proof ((bin2size_range (size2binZ(s))) H0).
  unfold size2binZ.
  bdestruct (bin2sizeZ (BINS - 1) <? s).
  bdestruct (bin2sizeZ (BINS - 1) <? bin2sizeZ (-1)); try lia.
  bdestruct (bin2sizeZ (BINS - 1) <?
             bin2sizeZ ((s + WORD * (ALIGN - 1) - 1) / (WORD * ALIGN))).
  - rewrite WORD_eq in *;  rewrite ALIGN_eq in *;  simpl.
    replace (s + 4 - 1) with (s + 3) by lia.
    exfalso; clear H2.
    replace  ((s + 4 * (2 - 1) - 1) / (4 * 2)) with (size2binZ s) in H3; try lia. 
    unfold size2binZ; bdestruct (bin2sizeZ (BINS - 1) <? s); try lia.
    rewrite WORD_eq in *; rewrite ALIGN_eq in *; lia.
  - unfold bin2sizeZ; rewrite WORD_eq in *;  rewrite ALIGN_eq in *; simpl.
    (* gave up fumbling with algebra; 
       finish by evaluation, of enumerating the values of s in a list *)
    assert (Htest: forall s,  0 <= s < bin2sizeZ(BINS-1) + 1 -> 
      ((((s + 4 - 1) / 8 + 1) * 2 - 1) * 4 + 4 - 1) / 8  = (s + 4 - 1) / 8).
    { set (Q:=fun t => 
                ((((t + 4 - 1) / 8 + 1) * 2 - 1) * 4 + 4 - 1) / 8  = (t + 4 - 1) / 8).
      assert (Hs: 0 <= s < bin2sizeZ(BINS - 1) + 1) by lia.
      assert (Hb: 0 <= bin2sizeZ(BINS - 1) + 1) by lia.
      pose proof (forall_Forall_range Q ((bin2sizeZ (BINS - 1))+1) Hb). 
      clear H1 H2 H3 Hb; unfold Q in H4; rewrite H4.
      rewrite bin2sizeBINS_eq. simpl. cbn.
      repeat constructor.
    }
    apply (Htest s); lia.
Qed.

(* TODO another brute force proof; can use this and claim2 to prove claim3 *)
Lemma bin2size2bin_id: 
  forall b, 0 <= b < BINS -> size2binZ (bin2sizeZ b) = b.
Proof.
  set (Q:= fun x => size2binZ(bin2sizeZ x) = x).
  assert (HB: 0 <= BINS) by rep_lia.
  pose proof (forall_Forall_range Q BINS HB). 
  unfold  Q in H. rewrite H. rewrite BINS_eq.
  cbn. repeat constructor.
Qed.

Lemma bin2size2bin_small:
  forall s, s >= 0 -> s <= bin2sizeZ(BINS - 1) -> size2binZ s < BINS.
Proof. intros. apply claim2; rep_lia. Qed.

Lemma bin2siz2e2bin_large:
  forall s, bin2sizeZ(BINS - 1) < s -> size2binZ s = -1.
Proof.
  intros. unfold size2binZ. bdestruct (bin2sizeZ(BINS-1) <? s). reflexivity. contradiction.
Qed.

(* BIGBLOCK needs to be big enough for at least one chunk of the 
largest size, because list_from_bin unconditionally initializes the last chunk. *)
Lemma BIGBLOCK_enough: (* and not too big *)
  forall s, 0 <= s <= bin2sizeZ(BINS-1) ->  
            0 < (BIGBLOCK - WA) / (s + WORD) < Int.max_signed.
Proof.
  intros; rewrite bin2sizeBINS_eq in *; split. 
  apply Z.div_str_pos; rep_lia.
  rewrite Z_div_lt; rep_lia.
Qed.

Lemma BIGBLOCK_enough_j: 
  forall s j, 0 <= s -> j < (BIGBLOCK-WA) / (s+WORD) ->
              (s+WORD) <= (BIGBLOCK-WA) - (j * (s+WORD)).
Proof.
  assert (Hlem: forall sw j bw, 0 < sw -> 0 < bw -> j < bw / sw -> sw <= bw - j*sw).
  { intros. assert (j+1 <= bw/sw) by lia.
    assert (bw/sw*sw <= bw) by (rewrite Z.mul_comm; apply Z.mul_div_le; rep_lia).
    assert ((j+1)*sw <= bw/sw*sw) by (apply Zmult_le_compat_r; rep_lia).
    assert ((j+1)*sw <= bw) by rep_lia.
    replace ((j+1)*sw)%Z with (sw + j*sw)%Z in *.
    rep_lia. replace (j+1) with (Z.succ j) by lia; rewrite Z.mul_succ_l; lia.
  }
  intros; apply Hlem; try rep_lia.
Qed.

Lemma malloc_compat_WORD_q:
(* consequence of the list_from_block loop invariant: remainder of big block is aligned *)
forall N j p s q,
  malloc_compatible BIGBLOCK p ->
  N = (BIGBLOCK-WA) / (s+WORD) -> 
  0 <= j < N ->
  0 <= s <= bin2sizeZ(BINS-1) ->  
  q = (offset_val (WA+(j*(s+WORD))) p) -> 
  (natural_alignment | (s + WORD)) -> 
  malloc_compatible (BIGBLOCK - (WA + j * (s + WORD)) - WORD) (offset_val WORD q).
Proof.
  intros N j p s q H HN Hj Hs Hq Ha.
  replace (offset_val (WA + (j*(s+WORD))) p) with
          (offset_val WA (offset_val (j*(s+WORD)) p)) in Hq.
  2: (rewrite offset_offset_val; 
      replace (j * (s + WORD) + WA) with (WA + j * (s + WORD)) by lia; reflexivity).
  subst q. do 2 rewrite offset_offset_val.
  apply malloc_compatible_offset.
  - pose proof (BIGBLOCK_enough_j s j) as He.
    destruct Hj as [Hj0 Hj1]; destruct Hs as [Hs0 Hs1]; subst N.
    apply He in Hs0 as H0; auto.
    replace (BIGBLOCK - (WA + j * (s + WORD)) - WORD)
      with (BIGBLOCK - WA - j * (s + WORD) - WORD) by lia.
    apply Zle_minus_le_0.
    rep_lia.
  - apply Z.add_nonneg_nonneg; try rep_lia.
(*    apply Z.mul_nonneg_nonneg; try rep_lia.*)
  - replace (BIGBLOCK - (WA + j * (s + WORD)))%Z
      with (BIGBLOCK - WA - j * (s + WORD))%Z by lia.
    replace (BIGBLOCK - WA - j * (s + WORD) - WORD + (j * (s + WORD) + (WA + WORD)))%Z
    with BIGBLOCK by lia; auto.
  - assert ((natural_alignment | WA+WORD)) 
      by (pose proof WORD_ALIGN_aligned; change (WA+WORD) with (WORD*ALIGN)%Z; auto).
    apply Z.divide_add_r; try auto. 
    apply Z.divide_mul_r; try auto. 
Qed.

(*+ resource vectors to support pre_fill *) 

(* Note on design: 
The interface specs could be done in terms of a vector indexed on request sizes.
Instead we index on bin number.  
The bin size corresponds to the free list length; we use Z bin size, for 
compatibility with other VST interfaces.

TODO maxSmallChunk should be constant in the C code too, at least in free.  
*)

Definition resvec := list Z. (* resource vector *)

Definition no_neg rvec : Prop := Forall (fun n => 0 <= n) rvec.

Definition emptyResvec : resvec := repeat 0 (Z.to_nat BINS).  

Definition maxSmallChunk := bin2sizeZ(BINS-1).

Lemma maxSmallChunk_eq: ltac:(compute_eq maxSmallChunk).  Proof. reflexivity. Qed.
#[export] Hint Rewrite maxSmallChunk_eq : rep_lia.
Global Opaque maxSmallChunk. (* make rewrites only happen in rep_lia *)

(* requested size n fits a bin and the bin is nonempty *)
Definition guaranteed (rvec: resvec) (n: Z): bool :=
  (Zlength rvec =? BINS) && (0 <=? n) && (n <=? maxSmallChunk) &&   
  (0 <? Znth (size2binZ n) rvec).

(* add m to size of bin b *)
Definition add_resvec (rvec: resvec) (b: Z) (m: Z): resvec :=
   if ((Zlength rvec =? BINS) && (0 <=? b) && (b <? BINS))%bool
   then upd_Znth b rvec (Znth b rvec + m)
   else rvec.

Definition eq_except (rv rv': resvec) (b: Z): Prop :=
  Zlength rv = Zlength rv' /\
  forall i, 0 <= i < Zlength rv -> i <> b -> Znth i rv = Znth i rv'.

(* number of chunks obtained from one BIGBLOCK, for bin b *)
Definition chunks_from_block (b: Z): Z := 
   if ((0 <=? b) && (b <? BINS))%bool
   then (BIGBLOCK - WA) / ((bin2sizeZ b) + WORD)
   else 0.

Lemma chunks_from_block_nonneg:
  forall b, 0 <= chunks_from_block b.
Proof.
intros.
unfold chunks_from_block.
bdestruct (0 <=? b); simpl; [ | lia].
bdestruct (b <? BINS); simpl; [ | lia].
exploit (bin2size_range b); intros. lia.
exploit (BIGBLOCK_enough (bin2sizeZ b)); intros. rep_lia.
(*Old proof: rep_lia.*)
(*Now*)
  specialize (Z_div_mod (BIGBLOCK - WA) (bin2sizeZ b + WORD)); intros X.
  destruct (Z.div_eucl (BIGBLOCK - WA) (bin2sizeZ b + WORD)) as [eu1 eu2]; rep_lia.
Qed.

Lemma chunks_from_block_pos:
  forall b, 0 <= b < BINS -> 0 < chunks_from_block b.
Proof.
intros.
unfold chunks_from_block.
bdestruct (0 <=? b); simpl; [ | lia].
bdestruct (b <? BINS); simpl; [ | lia].
exploit (bin2size_range b); intros. lia.
exploit (BIGBLOCK_enough (bin2sizeZ b)); intros. rep_lia.
(*Old proof: rep_lia.*)
(*Now*)
  specialize (Z_div_mod (BIGBLOCK - WA) (bin2sizeZ b + WORD)); intros X.
  destruct (Z.div_eucl (BIGBLOCK - WA) (bin2sizeZ b + WORD)) as [eu1 eu2]; rep_lia.
Qed.

Lemma Zlength_add_resvec:
  forall rvec b m,
  Zlength (add_resvec rvec b m) = Zlength rvec.
Proof.
intros. unfold add_resvec.
bdestruct (Zlength rvec =? BINS); simpl; auto.
bdestruct (0 <=? b); simpl; auto.
bdestruct (b <? BINS); simpl; auto.
apply upd_Znth_Zlength.
lia.
Qed.

Lemma add_resvec_no_neg:
  forall rvec b m, no_neg rvec -> 0 <= m + Znth b rvec -> no_neg (add_resvec rvec b m).
Proof.
intros.
unfold add_resvec.
bdestruct (Zlength rvec =? BINS); simpl; auto.
bdestruct (0 <=? b); simpl; auto.
bdestruct (b <? BINS); simpl; auto.
unfold no_neg. rewrite Z.add_comm.
unfold upd_Znth. if_tac.
+ apply Forall_app.
  split.
  - apply Forall_sublist; auto.
  - constructor. lia.
    apply Forall_sublist; auto.
+ lia.
Qed.

Lemma add_resvec_eq_except:
  forall rvec b m, eq_except (add_resvec rvec b m) rvec b.
Proof.
intros. unfold eq_except. split.
rewrite Zlength_add_resvec; auto.
intros. unfold add_resvec.
bdestruct (Zlength rvec =? BINS); simpl; auto.
bdestruct (0 <=? b); simpl; auto.
bdestruct (b <? BINS); simpl; auto.
rewrite upd_Znth_diff; try rep_lia. rewrite Zlength_add_resvec in *; auto.
Qed.

Lemma eq_except_reflexive:
  forall rvec b, eq_except rvec rvec b.
Proof.
  intros. unfold eq_except. split; reflexivity.
Qed.

Lemma guaranteed_reflect:
  forall lens n, 
    reflect (Zlength lens = BINS /\ 0 <= n <= maxSmallChunk /\ 0 < Znth (size2binZ n) lens)
            (guaranteed lens n).
Proof.
intros.
apply iff_reflect.
split; intros.
- destruct H as [Hlen [[Hn Hnb] Hnz]].
  unfold guaranteed.
 bdestruct (Zlength lens =? BINS); try contradiction.
 bdestruct (0 <=? n); try contradiction.
 bdestruct (n <=? maxSmallChunk); try contradiction.
 bdestruct (0 <? Znth (size2binZ n) lens); try contradiction.
 auto.
- unfold guaranteed in H.
 bdestruct (Zlength lens =? BINS); try discriminate.
 bdestruct (0 <=? n); try discriminate.
 bdestruct (n <=? maxSmallChunk); try discriminate.
 bdestruct (0 <? Znth (size2binZ n) lens); try discriminate.
 auto.
Qed.

(* TODO are the following three lemmas useful to clients?
   Otherwise they can go in the code verifications where each is used once. *)

Lemma is_guaranteed: forall lens n, 
   guaranteed lens n = true -> 0 < Znth (size2binZ n) lens.
Proof.
  intros. destruct (guaranteed_reflect lens n) as [Ht|Hf].
  destruct Ht as [Hlen [[Hn Hnb] Hnz]]. assumption. inv H.
Qed.

Lemma large_not_guaranteed: forall lens n,
  maxSmallChunk < n -> guaranteed lens n = false.
Proof.
  intros. destruct (guaranteed_reflect lens n) as [Ht|Hf].
  destruct Ht as [Hlen [[Hn Hnb] Hnz]]. rep_lia. reflexivity.
Qed.

Lemma small_not_guaranteed_zero:
  forall rvec n, Zlength rvec = BINS -> 0 <= n <= maxSmallChunk -> no_neg rvec ->
            guaranteed rvec n = false -> Znth (size2binZ n) rvec = 0.
Proof.
intros. unfold guaranteed in *.
unfold no_neg in *.
bdestruct (Zlength rvec =? BINS); try contradiction.
bdestruct (0 <=? n); try lia.
bdestruct (n <=? maxSmallChunk); try lia.
bdestruct (0 <? Znth (size2binZ n) rvec); try discriminate.
assert (0 <= Znth (size2binZ n) rvec).
{ apply Forall_Znth. apply H1. rewrite H. apply size2bin_range. apply H0. }
rep_lia.
Qed.