(* This file is for lemmas that
  (a) are used in the proof that the functional prog = functional spec
  AND (b) are used in the proof about the C program.
This file DOES NOT IMPORT anything about C or CompCert
  (except the CompCert Integers module)
*)

Require Recdef.
Require Import Integers.
Require Coq.Strings.String.
Require Coq.Strings.Ascii.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import sha.SHA256.
Require Import msl.Coqlib2.

Local Open Scope nat.

Lemma length_map2:
 forall A B C (f: A -> B -> C) al bl n,
  length al = n -> length bl = n -> 
  length (map2 f al bl) = n.
Proof.
induction al; destruct bl,n; simpl; intros; auto.
inv H.
Qed.

Lemma skipn_nil: forall A n, skipn n (@nil A) = nil.
Proof. induction n; simpl; auto.
Qed.

Lemma skipn_drop:
 forall A n m (al: list A), skipn n (skipn m al) = skipn (n+m) al.
Proof.
induction m; intros.
* simpl; auto. f_equal; omega.
* replace (n + S m)%nat with (S (n + m))%nat by omega.
  destruct al; [ rewrite skipn_nil; auto | ].
  unfold skipn at 3; fold skipn.
 rewrite <- IHm.
 f_equal.
Qed.

Lemma skipn_app1:
 forall A n (al bl: list A),
  (n <= length al)%nat ->
  skipn n (al++bl) = skipn n al ++ bl.
Proof.
intros. revert al H;
induction n; destruct al; intros; simpl in *; try omega; auto.
apply IHn; omega.
Qed.

Lemma skipn_app2:
 forall A n (al bl: list A),
  (n >= length al)%nat ->
  skipn n (al++bl) = skipn (n-length al) bl.
Proof.
intros. revert al H;
induction n; destruct al; intros; simpl in *; try omega; auto.
apply IHn; omega.
Qed. 

Lemma list_repeat_app: forall A a b (x:A),
  list_repeat a x ++ list_repeat b x = list_repeat (a+b) x.
Proof.
intros; induction a; simpl; f_equal.
auto.
Qed.

Lemma firstn_app1:
 forall A n (al bl: list A), 
  (n <= length al -> firstn n (al++bl) = firstn n al)%nat.
Proof.
intros. revert n al H; induction n; destruct al; simpl; intros; auto.
inv H.
f_equal; auto.
apply IHn.
omega.
Qed.

Lemma firstn_same:
  forall A n (b: list A), n >= length b -> firstn n b = b.
Proof.
induction n; destruct b; simpl; intros; auto.
inv H.
f_equal; auto.
apply IHn.
omega.
Qed.

Lemma nth_firstn_low:
 forall A i n al (d: A),
  i < n <= length al -> nth i (firstn n al) d = nth i al d.
Proof.
intros.
revert n al H; induction i; destruct n,al; simpl; intros; auto; try omega.
apply IHi; omega.
Qed.

Lemma nth_error_nth:
  forall A (d: A) i al, (i < length al)%nat -> nth_error al i = Some (nth i al d).
Proof.
induction i; destruct al; simpl; intros; auto.
inv H.
inv H.
apply IHi; omega.
Qed.

Local Open Scope Z.

Definition roundup (a b : Z) := (a + (b-1))/b*b.

Lemma Zlength_app: forall T (al bl: list T),
    Zlength (al++bl) = Zlength al + Zlength bl.
Proof. induction al; intros. simpl app; rewrite Zlength_nil; omega.
 simpl app; repeat rewrite Zlength_cons; rewrite IHal; omega.
Qed.
Lemma Zlength_rev: forall T (vl: list T), Zlength (rev vl) = Zlength vl.
Proof. induction vl; simpl; auto. rewrite Zlength_cons. rewrite <- IHvl.
rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil; omega.
Qed.

Lemma Zlength_map: forall A B (f: A -> B) l, Zlength (map f l) = Zlength l.
Proof. induction l; simpl; auto. repeat rewrite Zlength_cons. f_equal; auto.
Qed.

Lemma roundup_minus:
   forall a b,  b > 0 -> roundup a b - a = (- a) mod b.
Proof.
unfold roundup; intros.
replace (a+(b-1)) with (a-1+1*b) by omega.
rewrite Z_div_plus_full by omega.
rewrite Z.mul_add_distr_r.
assert (H4 := Zmod_eq a b H).
assert (a mod b = 0 \/ a mod b <> 0) by omega.
destruct H0; [rewrite Z.mod_opp_l_z | rewrite Z.mod_opp_l_nz]; try omega.
rewrite H0 in H4.
assert (a = a/b*b) by omega.
rewrite H1 at 1.
replace (a/b*b-1) with (a/b*b+ -1) by omega.
rewrite Z_div_plus_full_l by omega.
rewrite Z.mul_add_distr_r.
rewrite <- H1.
assert (b=1 \/ b>1) by omega.
destruct H2.
subst b. simpl. omega.
rewrite (Z_div_nz_opp_full 1) by (rewrite Z.mod_small; omega).
rewrite  Z.div_small by omega.
omega.
rewrite H4.
assert ( (a-1)/b*b = a/b*b); [ | omega].
f_equal.
assert (a = a mod b + a/b*b) by omega.
replace (a-1) with (a mod b - 1 + a/b*b) by omega.
rewrite Z_div_plus_full by omega.
rewrite Z.div_small; try omega.
pose proof (Z_mod_lt a b H).
omega.
Qed.

Lemma length_Round:
  forall regs f n, 
   length regs = 8%nat ->
   length (Round regs f n) = 8%nat.
Proof.
intros.
destruct (zlt n 0).
rewrite Round_equation.
rewrite if_true by auto; auto.
replace n with (n+1-1) by omega.
rewrite <- (Z2Nat.id (n+1)) by omega.
revert regs H; induction (Z.to_nat (n+1)); intros.
rewrite Round_equation.
change (Z.of_nat 0 - 1) with (-1).
rewrite if_true by omega. auto.
clear n g. rename n0 into n.
rewrite Round_equation.
rewrite inj_S.
unfold Z.succ.
rewrite Z.add_simpl_r.
rewrite if_false by omega.
specialize (IHn0 _ H).
clear - IHn0.
rename f into f'.
destruct (Round regs f' (Z.of_nat n - 1))
  as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; try inv IHn0.
reflexivity.
Qed.

Lemma length_hash_block:
 forall regs block, 
   length regs = 8%nat ->
   length block = 16%nat ->
   length (hash_block regs block) = 8%nat.
Proof.
intros.
unfold hash_block.
rewrite (length_map2 _ _ _ _ _ _ 8%nat); auto.
apply length_Round; auto.
Qed.

(* END COMMON LEMMAS *)