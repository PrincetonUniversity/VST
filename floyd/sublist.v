Require Import Coqlib.
Require Import msl.Coqlib2.
Require Import List.
Import ListNotations.

Lemma firstn_app:
 forall {A} n m (al: list A), firstn n al ++ firstn m (skipn n al) =
  firstn (n+m) al.
Proof. induction n; destruct al; intros; simpl; auto.
destruct m; reflexivity.
f_equal; auto.
Qed.

Lemma nth_skipn:
  forall {A} i n data (d:A),
       nth i (skipn n data) d = nth (i+n) data d.
Proof.
intros.
revert i data; induction n; simpl; intros.
f_equal; omega.
destruct data; auto.
destruct i; simpl; auto.
rewrite IHn.
replace (i + S n)%nat with (S (i + n))%nat by omega; auto.
Qed.

Lemma skipn_skipn: forall {A} n m (xs: list A),
  skipn n (skipn m xs) = skipn (m + n) xs.
Proof.
  intros.
  revert xs; induction m; intros.
  + reflexivity.
  + simpl.
    destruct xs.
    - destruct n; reflexivity.
    - apply IHm.
Qed.

Lemma firstn_exact_length: forall {A} (xs: list A), firstn (length xs) xs = xs.
Proof.
  intros.
  induction xs.
  + reflexivity.
  + simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma skipn_exact_length: forall {A} (xs: list A), skipn (length xs) xs = nil.
Proof.
  intros.
  induction xs.
  + reflexivity.
  + simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma len_le_1_rev: forall {A} (contents: list A),
  (length contents <= 1)%nat ->
  contents = rev contents.
Proof.
  intros.
  destruct contents.
  + reflexivity.
  + destruct contents.
    - reflexivity.
    - simpl in H. omega.
Qed.

Lemma firstn_firstn: forall {A} (contents: list A) n m,
  (n <= m)%nat ->
  firstn n (firstn m contents) = firstn n contents.
Proof.
  intros.
  revert n m H;
  induction contents;
  intros.
  + destruct n, m; reflexivity.
  + destruct n, m; try solve [omega].
    - simpl; reflexivity.
    - simpl; reflexivity.
    - simpl.
      rewrite IHcontents by omega.
      reflexivity.
Qed.

Lemma firstn_1_skipn: forall {A} n (ct: list A) d,
  (n < length ct)%nat ->
  nth n ct d :: nil = firstn 1 (skipn n ct).
Proof.
  intros.
  revert ct H; induction n; intros; destruct ct.
  + simpl in H; omega.
  + simpl. reflexivity.
  + simpl in H; omega.
  + simpl in H |- *.
    rewrite IHn by omega.
    reflexivity.
Qed.

Lemma skipn_length: forall {A} (contents: list A) n,
  length (skipn n contents) = (length contents - n)%nat.
Proof.
  intros.
  revert n;
  induction contents;
  intros.
  + destruct n; reflexivity.
  + destruct n; simpl.
    - reflexivity.
    - apply IHcontents.
Qed.

Lemma nth_firstn: forall {A} (contents: list A) n m d,
  (n < m)%nat ->
  nth n (firstn m contents) d = nth n contents d.
Proof.
  intros.
  revert n m H;
  induction contents;
  intros.
  + destruct n, m; reflexivity.
  + destruct n, m; try omega.
    - simpl. reflexivity.
    - simpl. apply IHcontents. omega.
Qed.

Lemma skipn_length_short:
  forall {A} n (al: list A), 
    (length al <= n)%nat -> 
    (length (skipn n al) = 0)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 omega.
 apply IHn. omega.
Qed.

Lemma skipn_short:
   forall {A} n (al: list A), (n >= length al)%nat -> skipn n al = nil.
Proof.
intros.
pose proof (skipn_length_short n al).
assert (length al <= n)%nat by auto.
specialize (H0 H1).
destruct (skipn n al); inv H0; auto.
Qed.

Lemma nth_map':
  forall {A B} (f: A -> B) d d' i al,
  (i < length al)%nat ->
   nth i (map f al) d = f (nth i al d').
Proof.
induction i; destruct al; simpl; intros; try omega; auto.
apply IHi; omega.
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
  forall A n (b: list A), (n >= length b)%nat -> firstn n b = b.
Proof.
induction n; destruct b; simpl; intros; auto.
inv H.
f_equal; auto.
apply IHn.
omega.
Qed.

Lemma nth_firstn_low:
 forall A i n al (d: A),
  (i < n <= length al)%nat -> nth i (firstn n al) d = nth i al d.
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

Lemma skipn_rev:
  forall {A} n (vl: list A),
   skipn n (rev vl) = rev (firstn (length vl - n) vl).
Proof.
induction n; intros.
simpl. rewrite NPeano.Nat.sub_0_r. rewrite firstn_exact_length. auto.
destruct (rev vl) eqn:?.
pose proof (rev_length vl). rewrite Heql in H.
destruct vl; inv H. reflexivity.
simpl. 
assert (vl = rev l ++ rev [a]).
rewrite <- rev_app_distr. simpl app. rewrite <- Heql; rewrite rev_involutive; auto.
rewrite H.
rewrite app_length.
simpl length.
rewrite <- (rev_involutive l) at 1.
rewrite IHn.
replace (length (rev l) + 1 - S n)%nat with (length (rev l) -n)%nat by omega.
f_equal.
rewrite firstn_app1 by omega.
reflexivity.
Qed.

Lemma Forall_list_repeat:
  forall {A} (P: A -> Prop) (n: nat) (a: A),
    P a -> Forall P (list_repeat n a).
Proof.
induction n; intros.
constructor.
constructor; auto.
Qed.

Lemma skipn_firstn: forall {A} n m (xs: list A),
  skipn n (firstn m xs) = firstn (m-n) (skipn n xs).
Proof.
intros.
revert xs n; induction m; intros.
simpl. destruct n; reflexivity.
destruct xs; simpl.
rewrite skipn_nil.
destruct match n with
            | O => S m
            | S l => (m - l)%nat
            end; reflexivity.
destruct n.
simpl. reflexivity.
simpl.
apply IHm.
Qed.

Lemma rev_skipn:
 forall {A} n (vl: list A),
  rev (skipn n vl) = firstn (length vl -n) (rev vl).
Proof.
induction n; intros.
simpl. rewrite NPeano.Nat.sub_0_r.
rewrite <- rev_length.
rewrite firstn_exact_length.
auto.
destruct vl.
simpl. auto.
simpl.
rewrite IHn.
rewrite firstn_app1 by (rewrite rev_length; omega).
auto.
Qed.

Lemma firstn_skipn_rev:
  forall {A} lo n (vl: list A),
  (n+lo <= length vl)%nat ->
  firstn n (skipn lo (rev vl)) =
  rev (firstn n (skipn (length vl - (lo+n))%nat vl)).
Proof.
intros.
rewrite skipn_rev.
assert (n = (length vl - lo) - (length vl - (lo+n)))%nat by omega.
rewrite H0 at 2.
rewrite <- skipn_firstn.
rewrite rev_skipn.
rewrite firstn_length. rewrite min_l by omega.
f_equal.
auto.
Qed.

Lemma map_firstn:
  forall A B (F: A -> B) n (al: list A),
  map F (firstn n al) = firstn n (map F al).
Proof.
induction n; destruct al; simpl; intros; auto.
f_equal; auto.
Qed.

Lemma map_skipn:
  forall A B (F: A -> B) n (al: list A),
  map F (skipn n al) = skipn n (map F al).
Proof.
induction n; destruct al; simpl; intros; auto.
Qed.

(* Beginning of Z-list stuff *)

Lemma Zlength_length:
  forall A (al: list A) (n: Z),
    0 <= n ->
    (Zlength al = n <-> length al = Z.to_nat n).
Proof.
intros. rewrite Zlength_correct.
split; intro.
rewrite <- (Z2Nat.id n) in H0 by omega.
apply Nat2Z.inj in H0; auto.
rewrite H0.
apply Z2Nat.inj; try omega.
rewrite Nat2Z.id; auto.
Qed.

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

Lemma ZtoNat_Zlength: 
 forall {A} (l: list A), Z.to_nat (Zlength l) = length l.
Proof.
intros. rewrite Zlength_correct. apply Nat2Z.id.
Qed.
Hint Rewrite @ZtoNat_Zlength : norm.

Lemma Zlength_nonneg:
 forall {A} (l: list A), 0 <= Zlength l.
Proof.
intros. rewrite Zlength_correct. omega.
Qed.

Definition Znth {X} n (xs: list X) (default: X) :=
  if (zlt n 0) then default else nth (Z.to_nat n) xs default.

Lemma Znth_map:
  forall A B i (f: A -> B) (al: list A) (d': A) (b: B),
  0 <= i < Zlength al ->
  @Znth B i (map f al) b = f (Znth i al d').
Proof.
unfold Znth.
intros.
rewrite if_false by omega.
rewrite if_false by omega.
rewrite nth_map' with (d'0 := d'); auto.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
rewrite <- Zlength_correct; omega.
Qed.

Lemma Znth_succ: forall {A} i lo (v: list A), Z.succ lo <= i -> Znth (i - lo) v = Znth (i - (Z.succ lo)) (skipn 1 v).
Proof.
  intros.
  extensionality default.
  unfold Znth.
  if_tac; [omega |].
  if_tac; [omega |].
  rewrite nth_skipn.
  f_equal.
  change 1%nat with (Z.to_nat 1).
  rewrite <- Z2Nat.inj_add by omega.
  f_equal.
  omega.
Qed.

Lemma split3_full_length_list: forall {A} lo mid hi (ct: list A) d,
  lo <= mid < hi ->
  Zlength ct = hi - lo ->
  ct = firstn (Z.to_nat (mid - lo)) ct ++
       (Znth (mid - lo) ct d :: nil) ++
       skipn (Z.to_nat (mid - lo + 1)) ct.
Proof.
  intros.
  rewrite <- firstn_skipn with (l := ct) (n := Z.to_nat (mid - lo)) at 1.
  f_equal.
  rewrite Z2Nat.inj_add by omega.
  rewrite <- skipn_skipn.
  replace (Znth (mid - lo) ct d :: nil) with (firstn (Z.to_nat 1) (skipn (Z.to_nat (mid - lo)) ct)).
  + rewrite firstn_skipn; reflexivity.
  + unfold Znth.
    if_tac; [omega |].
    rewrite firstn_1_skipn; [reflexivity |].
    rewrite <- (Nat2Z.id (length ct)).
    apply Z2Nat.inj_lt.
    - omega.
    - omega.
    - rewrite Zlength_correct in H0.
      omega.
Qed.

Lemma Forall_Znth:
 forall {A} (F: A -> Prop) (al: list A) i d,
   0 <= i < Zlength al ->
   Forall F al ->
   F (Znth i al d).
Proof.
intros.
unfold Znth. rewrite if_false by omega.
rewrite Zlength_correct in H.
assert (Z.to_nat i < length al)%nat.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega; omega.
clear H.
revert al H0 H1; induction (Z.to_nat i); destruct al; intros; simpl in *.
omega.
inv H0. auto.
inv H1.
inv H0.
apply IHn; auto.
omega.
Qed.

Lemma app_Znth1:
  forall A (l l': list A) (d: A) (i:Z),
  i < Zlength l -> Znth i (l++l') d = Znth i l d.
Proof.
intros.
unfold Znth.
if_tac; auto.
apply app_nth1.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
rewrite Zlength_correct in H; auto.
Qed.

Lemma app_Znth2:
  forall A (l l': list A) (d: A) (i:Z),
  i >= Zlength l -> Znth i (l++l') d = Znth (i-Zlength l) l' d.
Proof.
intros.
unfold Znth.
pose proof (Zlength_nonneg l).
if_tac.
rewrite if_true by omega; auto.
rewrite if_false by omega.
rewrite app_nth2.
f_equal.
rewrite Z2Nat.inj_sub by auto.
rewrite Zlength_correct.
rewrite Nat2Z.id; auto.
apply Nat2Z.inj_ge. rewrite Z2Nat.id by omega.
rewrite <- Zlength_correct; auto.
Qed.

Lemma Znth_firstn: 
  forall {A} (al: list A) (n m : Z) (d: A),
  n<m -> Znth n (firstn (Z.to_nat m) al) d = Znth n al d.
Proof.
intros.
unfold Znth.
if_tac; auto.
apply nth_firstn.
apply Z2Nat.inj_lt; omega.
Qed.

Lemma Znth_skipn: forall {A} i n xs (default: A),
  0 <= i ->
  0 <= n ->
  Znth i (skipn (nat_of_Z n) xs) default = Znth (i+n) xs default.
Proof.
  intros.
  unfold Znth.
  rewrite if_false by omega. rewrite if_false by omega.
  rewrite nth_skipn. f_equal.
  rewrite Z2Nat.inj_add by omega. auto. 
Qed.

Lemma Z2Nat_neg: forall i, i < 0 -> Z.to_nat i = 0%nat.
Proof.
  intros.
  destruct i; try reflexivity.
  pose proof Zgt_pos_0 p; omega.
Qed.

Lemma Zlength_firstn:
  forall {A} n (v: list A), Zlength (firstn (Z.to_nat n) v) = Z.min (Z.max 0 n) (Zlength v).
Proof.
intros. rewrite !Zlength_correct.
rewrite firstn_length.
(* solve by SMT *)
rewrite Zmin_spec, Zmax_spec.
if_tac; [rewrite min_l | rewrite min_r].
if_tac.
rewrite Z2Nat_neg; auto.
apply Z2Nat.id; omega.
if_tac in H. 
rewrite Z2Nat_neg; auto. omega.
rewrite <- (Nat2Z.id (length v)).
apply Z2Nat.inj_le; try omega.
auto.
if_tac in H.
destruct (length v); try omega.
rewrite inj_S in H. omega.
rewrite <- (Nat2Z.id (length v)).
apply Z2Nat.inj_le; try omega.
Qed.

Lemma Zlength_skipn:
  forall {A} n (v: list A), 
  Zlength (skipn (Z.to_nat n) v) = Z.max 0 (Zlength v - (Z.max 0n)).
Proof.
intros.
(* solve by SMT *)
rewrite !Zlength_correct.
rewrite skipn_length. rewrite !Zmax_spec.
if_tac.
if_tac in H.
omega.
apply inj_minus2. apply Nat2Z.inj_gt. rewrite Z2Nat.id by omega.
omega.
if_tac.
rewrite (Z2Nat_neg n) by omega.
rewrite NPeano.Nat.sub_0_r.
omega.
rewrite Nat2Z.inj_sub. 
rewrite Z2Nat.id by omega. auto.
apply Nat2Z.inj_le.
rewrite Z2Nat.id by omega.  omega.
Qed.

Lemma Znth_cons:
 forall {A} i (al: list A) d bl,
  0 <= i < Zlength al  ->
  Znth i al d :: bl = firstn (Z.to_nat 1) (skipn (Z.to_nat i) al) ++ bl.
Proof.
intros.
pose proof (Znth_skipn 0 i al).
rewrite Z.add_0_l in H0.
rewrite <- H0 by omega; clear H0.
change (Znth 0 (skipn (nat_of_Z i) al) d :: bl) with 
   ([Znth 0 (skipn (Z.to_nat i) al) d] ++ bl).
f_equal.
unfold Znth.
rewrite if_false  by omega.
assert (Zlength (skipn (Z.to_nat i) al) > 0).
rewrite Zlength_skipn.
rewrite (Z.max_r 0 i) by omega.
rewrite Z.max_r by omega.
omega.
destruct (skipn (Z.to_nat i) al).
rewrite Zlength_nil in H0; omega.
reflexivity.
Qed.

Lemma Zfirstn_app1:
 forall A n (al bl: list A), 
  n <= Zlength al -> firstn (Z.to_nat n) (al++bl) = firstn (Z.to_nat n) al.
Proof.
intros.
apply firstn_app1.
apply Nat2Z.inj_le. rewrite Zlength_correct in H.
destruct (zlt n 0).
rewrite Z2Nat_neg by auto. change (Z.of_nat 0) with 0; omega.
rewrite Z2Nat.id by omega.
omega.
Qed.

Lemma Zfirstn_same:
  forall A n (b: list A), n >= Zlength b -> firstn (Z.to_nat n) b = b.
Proof.
intros.
apply firstn_same.
rewrite Zlength_correct in H.
apply Nat2Z.inj_ge.
rewrite Z2Nat.id by omega.
auto.
Qed.

Lemma firstn_app2: forall {A} (n: nat) (al bl: list A),
 (n >= length al)%nat -> 
 firstn n (al++bl) = al ++ firstn (n - length al) bl.
Proof.
intros. revert al H.
induction n; destruct al; intros.
reflexivity.
inv H.
simpl.
destruct bl; auto.
simpl.
f_equal. apply IHn.
simpl in H; omega.
Qed.

Lemma Zfirstn_app2: forall {A} n (al bl: list A),
 n >= Zlength al -> 
 firstn (Z.to_nat n) (al++bl) = al ++ firstn (Z.to_nat (n - Zlength al)) bl.
Proof.
intros.
rewrite firstn_app2.
f_equal. f_equal.
rewrite Z2Nat.inj_sub.
rewrite Zlength_correct, Nat2Z.id. auto.
apply Zlength_nonneg.
apply Nat2Z.inj_ge.
rewrite Zlength_correct in H.
rewrite Z2Nat.id by omega.
auto.
Qed.

Lemma Zfirstn_firstn: forall {A} (contents: list A) n m,
  n <= m ->
  firstn (Z.to_nat n) (firstn (Z.to_nat m) contents) = firstn (Z.to_nat n) contents.
Proof.
intros.
destruct (zlt n 0).
rewrite (Z2Nat_neg n) by omega.
reflexivity.
apply firstn_firstn.
apply Z2Nat.inj_le; omega.
Qed.
Lemma Zskipn_app1:
 forall A n (al bl: list A),
  n <= Zlength al ->
  skipn (Z.to_nat n) (al++bl) = skipn (Z.to_nat n) al ++ bl.
Proof.
intros. 
apply skipn_app1.
rewrite Zlength_correct in H.
apply Nat2Z.inj_le.
destruct (zlt n 0).
rewrite (Z2Nat_neg n) by omega.
change (Z.of_nat 0) with 0.  omega. 
rewrite Z2Nat.id by omega.
auto.
Qed.

Lemma Zskipn_app2:
 forall A n (al bl: list A),
  n >= Zlength al ->
  skipn (Z.to_nat n) (al++bl) = skipn (Z.to_nat (n-Zlength al)) bl.
Proof.
intros.
rewrite Zlength_correct in *.
rewrite skipn_app2.
f_equal.
rewrite Z2Nat.inj_sub by omega.
rewrite Nat2Z.id.
auto.
apply Nat2Z.inj_ge.
destruct (zlt n 0).
rewrite (Z2Nat_neg n) by omega.
change (Z.of_nat 0) with 0.  omega. 
rewrite Z2Nat.id by omega.
auto.
Qed. 

Lemma Znth_rev:
  forall {A} i (al:list A) d,
  0 <= i < Zlength al ->
  Znth i (rev al) d = Znth (Zlength al - i - 1) al d.
Proof.
intros.
 unfold Znth. rewrite !if_false by omega.
rewrite !Z2Nat.inj_sub by omega.
rewrite Zlength_correct in*.
rewrite Nat2Z.id.
assert (Z.to_nat i < length al)%nat.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega. omega.
change (Z.to_nat 1) with 1%nat.
clear H.
rewrite rev_nth; auto.
f_equal.
omega.
Qed.

Lemma Zskipn_firstn: forall {A} n m (xs: list A),
 0 <= n ->
 skipn (Z.to_nat n) (firstn (Z.to_nat m) xs) =
  firstn (Z.to_nat (m-n)) (skipn (Z.to_nat n) xs).
Proof.
intros.
rewrite skipn_firstn.
f_equal.
rewrite Z2Nat.inj_sub; auto.
Qed.

Lemma Zskipn_skipn: forall {A} n m (xs: list A),
  0 <= n -> 0 <= m ->
  skipn (Z.to_nat n) (skipn (Z.to_nat m) xs) = skipn (Z.to_nat (m + n)) xs.
Proof.
  intros.
  rewrite skipn_skipn.
 f_equal.
 rewrite Z2Nat.inj_add; auto.
Qed.

Lemma Zfirstn_app:
 forall {A} n m (al: list A),
  0 <= n -> 0 <= m ->
  firstn (Z.to_nat n) al ++ firstn (Z.to_nat m) (skipn (Z.to_nat n) al) =
  firstn (Z.to_nat (n+m)) al.
Proof. 
intros.
rewrite firstn_app.
f_equal.
rewrite Z2Nat.inj_add; omega.
Qed.

Lemma Zfirstn_exact_length:
  forall {A} n (al: list A),
  n = Zlength al ->
  firstn (Z.to_nat n) al = al.
Proof.
intros.
subst.
rewrite Zlength_correct.
rewrite Nat2Z.id.
apply firstn_exact_length.
Qed.

(*****   SUBLIST  ******)

Definition sublist {A} (lo hi: Z) (al: list A) : list A :=
  firstn (Z.to_nat (hi-lo)) (skipn (Z.to_nat lo) al).

Lemma sublist_sublist:
  forall {A} lo hi lo' hi' (al: list A),
 0 <= lo <= hi ->
 hi <= hi'-lo' ->
 0 <= lo' <= hi' ->
 hi' <= Zlength al ->
 sublist lo hi (sublist lo' hi' al) = sublist (lo+lo') (hi+lo') al.
Proof.
intros.
unfold sublist.
rewrite Zskipn_firstn by omega.
rewrite Zfirstn_firstn by omega.
rewrite Zskipn_skipn by omega.
f_equal. f_equal. omega.
f_equal. f_equal. omega.
Qed.

Lemma sublist_rejoin:
  forall {A} lo mid hi (al: list A),
  0 <= lo <= mid ->
  mid <= hi <= Zlength al ->
  sublist lo mid al ++ sublist mid hi al = sublist lo hi al.
Proof.
intros.
unfold sublist.
replace (hi-lo) with ((mid-lo)+(hi-mid)) by omega.
rewrite <- Zfirstn_app by omega.
f_equal.
rewrite Zskipn_skipn by omega.
f_equal. f_equal. f_equal. omega.
Qed.

Lemma sublist_map:
  forall {A B} (F: A -> B) lo hi (al: list A),
  sublist lo hi (map F al) = map F (sublist lo hi al).
Proof.
intros.
unfold sublist.
rewrite map_firstn, map_skipn; auto.
Qed.

Lemma map_sublist:
  forall {A B} (F: A -> B) lo hi (al: list A),
  map F (sublist lo hi al) = sublist lo hi (map F al).
Proof.
intros.
symmetry. apply sublist_map.
Qed.

Lemma Znth_cons_sublist:
  forall {A} i (al: list A) d bl,
  0 <= i < Zlength al ->
  Znth i al d :: bl = sublist i (i+1) al ++ bl.
Proof.
intros.
unfold sublist.
replace (i+1-i) with 1 by omega.
rewrite Znth_cons by omega. reflexivity.
Qed.

Lemma Zlength_sublist:
  forall {A} lo hi (al: list A),
 0 <= lo <= hi -> hi <= Zlength al ->
 Zlength (sublist lo hi al) = hi-lo.
Proof.
intros.
unfold sublist.
rewrite Zlength_firstn, Z.max_r by omega.
rewrite Zlength_skipn.
rewrite (Z.max_r 0 lo) by omega.
rewrite Z.max_r by omega.
rewrite Z.min_l by omega.
auto.
Qed.

Lemma sublist_same:
forall {A} lo hi (al: list A),
  lo = 0 -> hi = Zlength al -> 
  sublist lo hi al = al.
Proof.
intros.
unfold sublist; subst.
rewrite Z.sub_0_r.
change (Z.to_nat 0) with O.
rewrite Zlength_correct, Nat2Z.id.
simpl. apply firstn_exact_length.
Qed.

Lemma Znth_sublist:
  forall {A} lo i hi (al: list A) d,
 0 <= lo -> hi <= Zlength al ->
 0 <= i < hi-lo ->
 Znth i (sublist lo hi al) d = Znth (i+lo) al d.
Proof.
intros.
unfold sublist.
rewrite Znth_firstn by omega.
rewrite Znth_skipn by omega. auto.
Qed.

Lemma rev_sublist:
  forall {A} lo hi (al: list A),
  0 <= lo <= hi -> hi <= Zlength al ->
  rev (sublist lo hi al) = sublist (Zlength al - hi) (Zlength al - lo) (rev al).
Proof.
intros.
unfold sublist.
replace (skipn (Z.to_nat lo) al) 
 with (skipn (length al - (Z.to_nat (Zlength al - hi) + (Z.to_nat (hi - lo)))) al).
rewrite <- firstn_skipn_rev.
f_equal.
f_equal. omega.
apply Nat2Z.inj_le.
rewrite Nat2Z.inj_add.
rewrite <- Zlength_correct.
rewrite !Z2Nat.id by omega.
omega.
f_equal.
apply Nat2Z.inj.
rewrite Nat2Z.inj_sub.
rewrite Nat2Z.inj_add.
rewrite !Z2Nat.id by omega.
rewrite <- Zlength_correct; omega.
apply Nat2Z.inj_le.
rewrite <- Zlength_correct.
rewrite Nat2Z.inj_add.
rewrite !Z2Nat.id by omega.
omega.
Qed.

Lemma sublist_nil:
  forall {A} lo (al: list A),
  sublist lo lo al = nil.
Proof.
intros.
unfold sublist.
rewrite Z.sub_diag. reflexivity.
Qed.

Lemma sublist_rev:
  forall {A} lo hi (al: list A),
  0 <= lo <= hi -> hi <= Zlength al ->
  sublist lo hi (rev al) = rev (sublist (Zlength al - hi) (Zlength al - lo) al).
Proof.
intros.
rewrite rev_sublist by omega.
f_equal; omega.
Qed.

Lemma sublist_app:
  forall {A} lo hi (al bl: list A),
  0 <= lo <= hi -> hi <= Zlength al + Zlength bl ->
  sublist lo hi (al++bl) = 
  sublist (Z.min lo (Zlength al)) (Z.min hi (Zlength al)) al ++
  sublist (Z.max (lo-Zlength al) 0) (Z.max (hi-Zlength al) 0) bl.
Proof.
intros.
unfold sublist.
destruct (zlt hi (Zlength al)).
rewrite (Z.min_l hi (Zlength al)) by omega.
rewrite (Z.min_l lo (Zlength al)) by omega.
rewrite (Z.max_r (hi-Zlength al) 0) by omega.
rewrite (Z.max_r (lo-Zlength al) 0) by omega.
simpl firstn.
rewrite <- app_nil_end.
rewrite Zskipn_app1 by omega.
rewrite Zfirstn_app1
 by (rewrite Zlength_skipn, !Z.max_r; try omega;
      rewrite Z.max_r; omega).
auto.
rewrite (Z.min_r hi (Zlength al)) by omega.
rewrite (Z.max_l (hi-Zlength al) 0) by omega.
destruct (zlt lo (Zlength al)).
rewrite (Z.min_l lo (Zlength al)) by omega.
rewrite (Z.max_r (lo-Zlength al) 0) by omega.
rewrite Zskipn_app1 by omega.
rewrite Zfirstn_app2
 by (rewrite Zlength_skipn, !Z.max_r; try omega;
      rewrite Z.max_r; omega).
rewrite Zlength_skipn, !Z.max_r; try omega;
      rewrite ?Z.max_r; try omega.
simpl skipn.
f_equal.

rewrite Zfirstn_exact_length; auto.
rewrite Zlength_skipn, !Z.max_r; try omega.
rewrite Z.max_r; omega.
f_equal.
f_equal.
omega.
rewrite (Z.min_r lo (Zlength al)) by omega.
rewrite (Z.max_l (lo-Zlength al) 0) by omega.
rewrite Zskipn_app2 by omega.
rewrite Z.sub_diag.
simpl app.
f_equal.
f_equal.
omega.
Qed.

Lemma sublist_split:
  forall {A} lo mid hi (al: list A),
  0 <= lo <= mid ->
  mid <= hi <= Zlength al ->
  sublist lo hi al = sublist lo mid al ++ sublist mid hi al.
Proof.
intros.
symmetry; apply sublist_rejoin; auto.
Qed.

Lemma Zlen_le_1_rev:
 forall {A} (al: list A),
  Zlength al <= 1 -> rev al = al.
Proof.
intros.
symmetry.
apply len_le_1_rev.
apply Nat2Z.inj_le. rewrite <- Zlength_correct; apply H.
Qed.
