Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import Coq.Lists.List.
Import ListNotations.

Class Inhabitant (A: Type) := default : A.

Instance Inhabitant_Z : Inhabitant Z := 0.
Instance Inhabitant_nat : Inhabitant nat := O.
Instance Inhabitant_positive : Inhabitant positive := 1%positive.
Instance Inhabitant_list {T: Type} : Inhabitant (list T) := @nil T.
Instance Inhabitant_fun {T1 T2: Type} {H: Inhabitant T2} : Inhabitant (T1->T2) := fun _ => H.
Instance Inhabitant_Prop : Inhabitant Prop := False.
Instance Inhabitant_bool : Inhabitant bool := false.
Instance Inhabitant_pair {T1 T2 : Type} {x1: Inhabitant T1} {x2: Inhabitant T2} : Inhabitant (T1*T2)%type := (x1,x2).

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

Lemma firstn_app1: forall {A} n (p l: list A),
  (n <= Datatypes.length p)%nat ->
   firstn n (p ++ l) = firstn n p.
Proof. intros A n.
induction n; simpl; intros. trivial.
  destruct p; simpl in H. omega.
  apply le_S_n in H. simpl. f_equal. auto.
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

Lemma firstn_list_repeat {A} (v:A): forall i k, (i<=k)%nat ->
      firstn i (list_repeat k v) = list_repeat i v.
Proof.
  induction i; simpl; trivial; intros.
  destruct k. omega. simpl. rewrite IHi; trivial. omega.
Qed.

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
simpl. rewrite Nat.sub_0_r. rewrite firstn_exact_length. auto.
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
simpl. rewrite Nat.sub_0_r.
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

Definition Zlength' := @Zlength.

Ltac pose_Zlength_nonneg1 T A :=
     lazymatch goal with
      | H:  0 <= @Zlength T A |- _ => idtac
      | H:  0 <= @Zlength T A /\ _ |- _ => idtac
      | |- _ => pose proof (@Zlength_nonneg T A)
     end;
     (* the next three lines are to avoid blowups in the change command *)
     let x := fresh "x" in set (x:= @Zlength T A) in *;
     let y := fresh "y" in set (y := @Zlength) in x;
     fold @Zlength' in y; subst y; subst x.

Ltac pose_Zlength_nonneg :=
 repeat
  match goal with
  | |- context [@Zlength ?T ?A] => pose_Zlength_nonneg1 T A
  | H: context [@Zlength ?T ?A] |- _ => pose_Zlength_nonneg1 T A
 end;
  unfold Zlength' in *.

Ltac list_solve := autorewrite with sublist; pose_Zlength_nonneg; omega.

Definition Znth {X}{d: Inhabitant X} n (xs: list X) :=
  if (zlt n 0) then default else nth (Z.to_nat n) xs d.

Lemma Znth_map:
  forall {A:Type} {da: Inhabitant A}{B:Type}{db: Inhabitant B} i (f: A -> B) (al: list A),
  0 <= i < Zlength al ->
  Znth i (map f al)  = f (Znth i al).
Proof.
unfold Znth.
intros.
rewrite if_false by omega.
rewrite if_false by omega.
rewrite nth_map' with (d' := da); auto.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
change (Inhabitant A) with A.
rewrite <- Zlength_correct. omega.
Qed.

Hint Rewrite 
   (@Znth_map Z _) (@Znth_map nat _) (@Znth_map positive _)
    using (auto; rewrite ?Zlength_map in *; omega) : sublist.

(* Add these in a later file where things are in scope ...
Hint Rewrite (Znth_map Int.zero) (Znth_map Vundef)
    using (auto; rewrite ?Zlength_map in *; omega) : sublist.
*)

Lemma Znth_succ: forall {A}{a: Inhabitant A} i lo (v: list A), Z.succ lo <= i -> Znth (i - lo) v = Znth (i - (Z.succ lo)) (skipn 1 v).
Proof.
  intros.
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

Lemma Znth_0_cons {A}{a: Inhabitant A} l (v:A): Znth 0 (v::l) = v.
Proof. reflexivity. Qed.

Lemma Znth_pos_cons {A}{a: Inhabitant A} i l (v:A): 0<i -> Znth i (v::l) = Znth (i-1) l.
Proof. intros. unfold Znth. if_tac. omega. if_tac. omega.
  assert (Z.to_nat i = S (Z.to_nat (i-1))).
    rewrite <- Z2Nat.inj_succ. assert (i = Z.succ (i - 1)). omega. rewrite <- H2. trivial. omega.
  rewrite H2; reflexivity.
Qed.

Lemma Znth_In : forall {A}{a: Inhabitant A} i l, 0 <= i < Zlength l -> In (Znth i l) l.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [omega|].
  apply nth_In; rewrite Zlength_correct in *.
  apply Nat2Z.inj_lt; rewrite Z2Nat.id; omega.
Qed.

Lemma split3_full_length_list: forall {A}{a: Inhabitant A} lo mid hi (ct: list A),
  lo <= mid < hi ->
  Zlength ct = hi - lo ->
  ct = firstn (Z.to_nat (mid - lo)) ct ++
       (Znth (mid - lo) ct :: nil) ++
       skipn (Z.to_nat (mid - lo + 1)) ct.
Proof.
  intros.
  rewrite <- firstn_skipn with (l := ct) (n := Z.to_nat (mid - lo)) at 1.
  f_equal.
  rewrite Z2Nat.inj_add by omega.
  rewrite <- skipn_skipn.
  replace (Znth (mid - lo) ct :: nil) with (firstn (Z.to_nat 1) (skipn (Z.to_nat (mid - lo)) ct)).
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
 forall {A}{a: Inhabitant A} (F: A -> Prop) (al: list A) i,
   0 <= i < Zlength al ->
   Forall F al ->
   F (Znth i al).
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
  forall A (a: Inhabitant A) (l l': list A) (i:Z),
  i < Zlength l -> Znth i (l++l') = Znth i l.
Proof.
intros.
unfold Znth.
if_tac; auto.
apply app_nth1.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega.
rewrite Zlength_correct in H; auto.
Qed.

Lemma app_Znth2:
  forall A (a: Inhabitant A) (l l': list A) (i:Z),
  i >= Zlength l -> Znth i (l++l') = Znth (i-Zlength l) l'.
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
  forall {A}{a: Inhabitant A} (al: list A) (n m : Z),
  n<m -> Znth n (firstn (Z.to_nat m) al) = Znth n al.
Proof.
intros.
unfold Znth.
if_tac; auto.
apply nth_firstn.
apply Z2Nat.inj_lt; omega.
Qed.

Lemma Znth_skipn: forall {A}{a: Inhabitant A}  i n xs,
  0 <= i ->
  0 <= n ->
  Znth i (skipn (nat_of_Z n) xs) = Znth (i+n) xs.
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
rewrite Nat.sub_0_r.
omega.
rewrite Nat2Z.inj_sub.
rewrite Z2Nat.id by omega. auto.
apply Nat2Z.inj_le.
rewrite Z2Nat.id by omega.  omega.
Qed.

Lemma Znth_cons:
 forall {A}(a: Inhabitant A)  i (al: list A) bl,
  0 <= i < Zlength al  ->
  Znth i al :: bl = firstn (Z.to_nat 1) (skipn (Z.to_nat i) al) ++ bl.
Proof.
intros.
pose proof (Znth_skipn 0 i al).
rewrite Z.add_0_l in H0.
rewrite <- H0 by omega; clear H0.
change (Znth 0 (skipn (nat_of_Z i) al) :: bl) with
   ([Znth 0 (skipn (Z.to_nat i) al)] ++ bl).
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
  forall {A}{d: Inhabitant A} i (al:list A),
  0 <= i < Zlength al ->
  Znth i (rev al) = Znth (Zlength al - i - 1) al.
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

Definition upd_Znth {A} (i: Z) (al: list A) (x: A): list A :=
   sublist 0 i al ++ x :: sublist (i+1) (Zlength al) al.

Lemma sublist_sublist {A} i j k m (l:list A): 0<=m -> 0<=k <=i -> i <= j-m ->
  sublist k i (sublist m j l) = sublist (k+m) (i+m) l.
Proof.
 unfold sublist; intros.
  rewrite skipn_firstn.
  rewrite firstn_firstn, skipn_skipn, <- Z2Nat.inj_add,(Z.add_comm _ k), Zminus_plus_simpl_r; trivial.
  omega.
  rewrite <- Z2Nat.inj_sub; trivial. apply Z2Nat.inj_le; try omega. omega.
Qed.
(*
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
*)
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

Lemma sublist_len_1:
  forall {A}{d: Inhabitant A} i (al: list A),
  0 <= i < Zlength al ->
  sublist i (i+1) al = Znth i al :: nil.
Proof.
  intros.
  unfold sublist.
  replace (i+1-i) with 1 by omega.
  rewrite Znth_cons by omega.
  symmetry; apply app_nil_r.
Qed.

Lemma Znth_cons_sublist:
  forall {A}{d: Inhabitant A} i (al: list A) bl,
  0 <= i < Zlength al ->
  Znth i al :: bl = sublist i (i+1) al ++ bl.
Proof.
  intros.
  erewrite sublist_len_1 by eauto.
  reflexivity.
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

Lemma sublist_same_gen:
forall {A} lo hi (al: list A),
  lo = 0 -> hi >= Zlength al ->
  sublist lo hi al = al.
Proof.
intros.
unfold sublist; subst.
rewrite Z.sub_0_r.
simpl; rewrite firstn_all2; auto.
apply Nat2Z.inj_le.
pose proof (Zlength_nonneg al).
rewrite Z2Nat.id, <- Zlength_correct; omega.
Qed.

Lemma sublist_same:
forall {A} lo hi (al: list A),
  lo = 0 -> hi = Zlength al ->
  sublist lo hi al = al.
Proof.
intros; apply sublist_same_gen; omega.
Qed.

Lemma Znth_sublist:
  forall {A}{d: Inhabitant A} lo i hi (al: list A),
 0 <= lo ->
 0 <= i < hi-lo ->
 Znth i (sublist lo hi al) = Znth (i+lo) al.
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

Lemma sublist_nil_gen : forall {A} (l : list A) i j, j <= i -> sublist i j l = [].
Proof.
  intros; unfold sublist.
  replace (Z.to_nat (j - i)) with O; auto.
  apply Nat2Z.inj; simpl.
  destruct (Z.eq_dec (j - i) 0); [rewrite e; auto|].
  rewrite Z2Nat_neg; auto; omega.
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

Lemma sublist_last_1 : forall {A}{d: Inhabitant A} lo hi (al : list A), 0 <= lo <= hi -> hi + 1 <= Zlength al ->
  sublist lo (hi + 1) al = sublist lo hi al ++ [Znth hi al].
Proof.
  intros.
  erewrite sublist_split with (mid := hi)(hi0 := hi + 1), sublist_len_1; auto; omega.
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

Lemma skipn_0:
  forall A (l: list A), skipn 0 l = l.
Proof.
reflexivity.
Qed.

Lemma sublist_1_cons {A} l (v:A) n: sublist 1 n (v::l) = sublist 0 (n-1) l.
Proof.
  unfold sublist. rewrite Z2Nat.inj_sub, skipn_0, Zminus_0_r. simpl. rewrite Z2Nat.inj_sub. trivial.
  omega. omega.
Qed.

Lemma sublist_nil': forall (A : Type) (lo lo': Z) (al : list A), lo=lo' -> sublist lo lo' al = [].
Proof. intros. subst. apply sublist_nil. Qed.

Lemma sublist_skip {A} (l:list A) i : 0<=i ->  sublist i (Zlength l) l = skipn (Z.to_nat i) l.
Proof. unfold sublist; intros. apply firstn_same. rewrite skipn_length.
  rewrite Z2Nat.inj_sub, Zlength_correct, Nat2Z.id. omega. trivial.
Qed.

Lemma sublist_firstn {A} (l:list A) i: sublist 0 i l = firstn (Z.to_nat i) l.
Proof. unfold sublist; intros. rewrite Zminus_0_r, skipn_0. trivial. Qed.

Lemma sublist_app1:
  forall (A : Type) (k i : Z) (al bl : list A),
  0 <= k <= i -> i <= Zlength al -> sublist k i (al ++ bl) = sublist k i al.
Proof. intros.
  unfold sublist. rewrite skipn_app1. rewrite firstn_app1. trivial.
  rewrite skipn_length, Z2Nat.inj_sub. apply Nat2Z.inj_le.
  repeat rewrite Nat2Z.inj_sub. rewrite Z2Nat.id, <- Zlength_correct. omega. omega.
  rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; omega.
  apply Z2Nat.inj_le; omega. omega. rewrite <- ZtoNat_Zlength. apply Z2Nat.inj_le; omega.
Qed.

Lemma sublist0_app1 {A} i (al bl:list A): 0<= i <= Zlength al ->
  sublist 0 i (al ++ bl) = sublist 0 i al.
Proof. intros. apply sublist_app1; omega. Qed.

Lemma sublist_app2 {A} i j (al bl:list A): 0<=Zlength al <= i->
  sublist i j (al ++ bl) = sublist (i-Zlength al) (j-Zlength al) bl.
Proof.
  unfold sublist; intros.
  rewrite skipn_app2.
  repeat rewrite Z2Nat.inj_sub. repeat rewrite ZtoNat_Zlength.
  remember ((Z.to_nat i - length al)%nat) as k.
  rewrite <- Nat.sub_add_distr.
  assert (K: (length al + k = Z.to_nat i)%nat).
    subst k. rewrite <- le_plus_minus. trivial.
    apply Nat2Z.inj_le. rewrite Z2Nat.id. rewrite Zlength_correct in H; apply H. omega.
  rewrite K. trivial.
  omega. omega. omega. omega.
  apply Nat2Z.inj_le. rewrite Z2Nat.id. rewrite Zlength_correct in H; apply H. omega.
Qed.

Lemma sublist_sublist0 {A} i j k (l:list A): 0<=k -> k<=i<=j ->
  sublist k i (sublist 0 j l) = sublist k i l.
Proof. intros. rewrite sublist_sublist; repeat rewrite Zplus_0_r; trivial; omega. Qed.

Lemma sublist_sublist00 {A} i j (l:list A): 0<=i<=j ->
  sublist 0 i (sublist 0 j l) = sublist 0 i l.
Proof. intros. apply sublist_sublist0; omega. Qed.

Lemma skipn_list_repeat:
   forall A k n (a: A),
     (k <= n)%nat -> skipn k (list_repeat n a) = list_repeat (n-k) a.
Proof.
 induction k; destruct n; simpl; intros; auto.
 apply IHk; auto. omega.
Qed.

(* not this version!
Lemma sublist_list_repeat {A} i j k (v:A) (I: 0<=i)
          (IJK: (Z.to_nat i <= Z.to_nat j <= k)%nat):
      sublist i j (list_repeat k v) = list_repeat (Z.to_nat (j-i)) v.
Proof.
  unfold sublist.
  rewrite skipn_list_repeat; try omega.
  rewrite Z2Nat.inj_sub; try omega.
  rewrite firstn_list_repeat; trivial; omega.
Qed.
*)

Lemma sublist_list_repeat {A} i j k (v:A) (I: 0<=i)
          (IJK: i <= j <= k):
      sublist i j (list_repeat (Z.to_nat k) v) = list_repeat (Z.to_nat (j-i)) v.
Proof.
  unfold sublist.
  rewrite skipn_list_repeat.
  rewrite firstn_list_repeat.
  trivial.
  rewrite <- Z2Nat.inj_sub by omega.
  apply Z2Nat.inj_le; omega.
  apply Z2Nat.inj_le; omega.
Qed.

Lemma Zlength_list_repeat:
  forall {A} n (x: A),
  0 <= n ->
  Zlength (list_repeat (Z.to_nat n) x) = n.
Proof.
intros.
rewrite Zlength_correct.
rewrite length_list_repeat.
apply Z2Nat.id; auto.
Qed.

Lemma list_repeat_0:
  forall {A} (x:A), list_repeat (Z.to_nat 0) x = nil.
Proof.
simpl. auto.
Qed.

Lemma Znth_list_repeat_inrange:
  forall {A}{d: Inhabitant A} i n (a: A),
   (0 <= i < n)%Z ->
   Znth i (list_repeat (Z.to_nat n) a) = a.
Proof.
intros.
unfold Znth; rewrite if_false by omega.
assert (Z.to_nat i < Z.to_nat n)%nat
  by (apply Z2Nat.inj_lt; omega).
forget (Z.to_nat n) as k.
revert k H0; induction (Z.to_nat i); destruct k; simpl; intros.
omega. auto. omega. apply IHn0; omega.
Qed.

Lemma firstn_nil {A} n: firstn n (nil:list A) = nil.
Proof.  destruct n; reflexivity. Qed.

Lemma firstn_In {A} (x:A): forall l n, In x (firstn n l) -> In x l.
Proof.
  induction l; simpl; intros.
  rewrite firstn_nil in H. inv H.
  destruct n; simpl in *. contradiction.
  destruct H; eauto.
Qed.
Lemma skipn_In {A} (x:A): forall l n, In x (skipn n l) -> In x l.
Proof.
  induction l; simpl; intros.
  rewrite skipn_nil in H. inv H.
  destruct n; simpl in *. trivial. right; eauto.
Qed.

Lemma sublist_In {A} lo hi data (x:A) (I:In x (sublist lo hi data)): In x data.
Proof. eapply skipn_In. eapply firstn_In. apply I. Qed.

Lemma Zlength_list_repeat' {A} n (v:A): Zlength (list_repeat n v) = Z.of_nat n.
Proof. rewrite Zlength_correct, length_list_repeat; trivial. Qed.

Lemma sublist0_app2 {A : Type} i (al bl : list A):
  Zlength al <= i <= Zlength al + Zlength bl ->
  sublist 0 i (al ++ bl) = al ++ sublist 0 (i - Zlength al) bl.
Proof. specialize (Zlength_nonneg al); specialize (Zlength_nonneg bl); intros.
rewrite <- (sublist_rejoin 0 (Zlength al) i); try rewrite Zlength_app; try omega.
rewrite sublist0_app1, sublist_same; try omega.
 rewrite sublist_app2, Zminus_diag; trivial. omega.
Qed.


Lemma sublist_rejoin':
  forall {A} lo mid mid' hi (al: list A),
  mid=mid' ->
  0 <= lo <= mid ->
  mid' <= hi <= Zlength al ->
  sublist lo mid al ++ sublist mid' hi al = sublist lo hi al.
Proof.
intros.
subst mid'.
apply sublist_rejoin; auto.
Qed.

Hint Rewrite @sublist_nil' using list_solve: sublist.
Hint Rewrite @app_nil_l : sublist.
Hint Rewrite @Zlength_rev : sublist.
Hint Rewrite @sublist_rejoin' using list_solve : sublist.

Lemma subsub1:
 forall a b : Z, (a-(a-b)) = b.
Proof.  intros. omega. Qed.
Hint Rewrite subsub1 : sublist.

Lemma sublist_app':
  forall {A} lo hi (al bl: list A),
  0 <= lo <= Zlength al ->
  0 <= hi-Zlength al <= Zlength bl ->
  sublist lo hi (al++bl) =
  sublist lo (Zlength al) al ++
  sublist 0 (hi-Zlength al) bl.
Proof.
intros.
unfold sublist.
simpl.
rewrite Zskipn_app1 by omega.
rewrite Zfirstn_app2
 by (rewrite Zlength_skipn, Z.max_r;
      rewrite ?Z.max_r; omega).
rewrite Zlength_skipn, Z.max_r;
      rewrite ?Z.max_r; try omega.
rewrite (Zfirstn_exact_length (Zlength al - lo))
 by (rewrite Zlength_skipn, Z.max_r;
      rewrite ?Z.max_r; omega).
f_equal.
f_equal.
f_equal.
omega.
Qed.

Lemma upd_Znth_Zlength {A} i (l:list A) v: 0<=i < Zlength l ->
      Zlength (upd_Znth i l v) = Zlength l.
Proof. intros.
   unfold upd_Znth. rewrite Zlength_app, Zlength_cons; simpl.
  repeat rewrite Zlength_sublist; simpl; omega.
Qed.

Lemma upd_Znth_map {A B} (f:A -> B) i l v:
      upd_Znth i (map f l) (f v) =
      map f (upd_Znth i l v).
Proof. unfold upd_Znth; intros. rewrite map_app, Zlength_map.
  do 2 rewrite sublist_map; trivial.
Qed.

Lemma upd_Znth_lookup K {A}{d: Inhabitant A}: forall l (L:Zlength l = K) i j (v:A) (I: 0<=i<K) (J: 0<=j<K),
   (i=j /\ Znth i (upd_Znth j l v) = v) \/
   (i<>j /\ Znth i (upd_Znth j l v) = Znth i l).
Proof.
  intros. unfold upd_Znth.
  destruct (zeq i j); subst.
  + left; split; trivial.
    rewrite app_Znth2; rewrite Zlength_sublist; try rewrite Zminus_0_r; try rewrite Zminus_diag; try omega.
    rewrite Znth_0_cons. trivial.
  + right; split; trivial.
    destruct (zlt i j).
    - rewrite app_Znth1; try rewrite Zlength_sublist; try omega.
      rewrite Znth_sublist; try omega. rewrite Zplus_0_r; trivial.
    - rewrite app_Znth2; rewrite Zlength_sublist; try omega.
      rewrite Zminus_0_r, Znth_pos_cons, Znth_sublist; try omega.
      assert (H: i - j - 1 + (j + 1) = i) by omega. rewrite H; trivial.
Qed.

Lemma upd_Znth_lookup' K {A}{d: Inhabitant A}: forall l (L:Zlength l = K) i (I: 0<=i<K) j (J: 0<=j<K) (v:A),
    Znth i (upd_Znth j l v) = if zeq i j then v else Znth i l.
Proof. intros.
  destruct (upd_Znth_lookup K l L i j v I J) as [[X Y] | [X Y]]; if_tac; try omega; trivial.
Qed.

Lemma upd_Znth_char {A} n l1 (v:A) l2 w: Zlength l1=n ->
      upd_Znth n (l1 ++ v :: l2) w = l1 ++ w :: l2.
Proof. intros. unfold upd_Znth.
  specialize (Zlength_nonneg l1); intros.
  f_equal. rewrite sublist0_app1. apply sublist_same; omega. omega.
  f_equal. rewrite sublist_app2, <- H, Zlength_app, Zlength_cons. do 2 rewrite Zminus_plus.
                rewrite sublist_1_cons. apply sublist_same; omega. omega.
Qed.

Lemma upd_Znth_same {A}{d: Inhabitant A}: forall i l u, 0<= i< Zlength l -> Znth i (upd_Znth i l u) = u.
Proof.
  intros. rewrite (upd_Znth_lookup' _ _ (eq_refl _)); trivial.
  rewrite zeq_true; trivial.
Qed.

Lemma upd_Znth_diff {A}{d: Inhabitant A}: forall i j l u, 0<= i< Zlength l -> 0<= j< Zlength l -> i<>j ->
      Znth i (upd_Znth j l u) = Znth i l.
Proof.
  intros. rewrite (upd_Znth_lookup' _ _ (eq_refl _)); trivial.
  rewrite zeq_false; trivial.
Qed.

Lemma upd_Znth_app1 {A} i l1 l2 (I: 0 <= i < Zlength l1) (v:A):
      upd_Znth i (l1++l2) v = upd_Znth i l1 v ++ l2.
Proof.
  assert (L2NN:= Zlength_nonneg l2).
  unfold upd_Znth.
  rewrite sublist_app1, Zlength_app, <- app_assoc; try omega.
  f_equal. simpl. f_equal.
  rewrite <- (sublist_rejoin (i+1) (Zlength l1)); try omega.
  rewrite sublist_app1; try omega. f_equal.
  rewrite sublist_app2, Zminus_diag, Zminus_plus; try omega.
  apply sublist_same; trivial.
  rewrite Zlength_app; omega.
Qed.

Lemma upd_Znth_app2 {A} (l1 l2:list A) i v:
  Zlength l1 <= i <= Zlength l1 + Zlength l2 ->
  upd_Znth i (l1 ++ l2) v = l1 ++ upd_Znth (i-Zlength l1) l2 v.
Proof. unfold upd_Znth. intros.
  rewrite sublist0_app2; trivial. rewrite <- app_assoc. f_equal. f_equal. f_equal.
  rewrite sublist_app2, Zlength_app, Zminus_plus.
  assert (i + 1 - Zlength l1 = i - Zlength l1 + 1) by omega. rewrite H0; trivial.
  specialize (Zlength_nonneg l1); omega.
Qed.

Lemma upd_Znth0 {A} (l:list A) v:
upd_Znth 0 l v = v :: sublist 1 (Zlength l) l.
Proof. unfold upd_Znth. rewrite sublist_nil. reflexivity. Qed.

Lemma sublist_upd_Znth_l: forall {A} (l: list A) i lo hi v,
  0 <= lo <= hi ->
  hi <= i < Zlength l ->
  sublist lo hi (upd_Znth i l v) = sublist lo hi l.
Proof.
  intros.
  unfold upd_Znth.
  rewrite sublist_app1.
  2: omega.
  2: rewrite Zlength_sublist by omega; omega.
  rewrite sublist_sublist by omega.
  f_equal; omega.
Qed.

Lemma sublist_upd_Znth_r: forall {A} (l: list A) i lo hi v,
  0 <= i < lo ->
  lo <= hi <= Zlength l ->
  sublist lo hi (upd_Znth i l v) = sublist lo hi l.
Proof.
  intros.
  unfold upd_Znth.
  replace (sublist 0 i l ++ v :: sublist (i + 1) (Zlength l) l) with
    ((sublist 0 i l ++ v :: nil) ++ sublist (i + 1) (Zlength l) l)
    by (rewrite <- app_assoc; auto).
  rewrite sublist_app2.
  2: rewrite Zlength_app, Zlength_sublist, Zlength_correct by omega; simpl; omega.
  rewrite Zlength_app, Zlength_sublist, Zlength_correct by omega; simpl.
  rewrite sublist_sublist by omega.
  f_equal; omega.
Qed.

Lemma sublist_upd_Znth_lr: forall {A} (l: list A) i lo hi v,
  0 <= lo <= i->
  i < hi <= Zlength l ->
  sublist lo hi (upd_Znth i l v) = upd_Znth (i - lo) (sublist lo hi l) v.
Proof.
  intros.
  unfold upd_Znth.
  change (v :: sublist (i + 1) (Zlength l) l) with
    ((v :: nil) ++ sublist (i + 1) (Zlength l) l).
  rewrite !sublist_app'.
  2: change (Zlength [v]) with 1; omega.
  2: change (Zlength [v]) with 1; rewrite !Zlength_sublist by omega; omega.
  2: rewrite !Zlength_sublist by omega; omega.
  2: rewrite Zlength_app, !Zlength_sublist by omega; change (Zlength [v]) with 1; omega.
  rewrite !Zlength_sublist by omega.
  change (Zlength [v]) with 1.
  rewrite (@sublist_len_1 _ v) by (change (Zlength [v]) with 1; omega).
  change (@Znth _ v 0 [v]) with v.
  simpl.
  rewrite !sublist_sublist by omega.
  f_equal; [| f_equal]; f_equal; omega.
Qed.

(*Hint Rewrite @Zlength_list_repeat'  : sublist.*)
Hint Rewrite @Znth_list_repeat_inrange : sublist.
Hint Rewrite @Zlength_cons @Zlength_nil: sublist.
Hint Rewrite @list_repeat_0: sublist.
Hint Rewrite <- @app_nil_end : sublist.
Hint Rewrite @Zlength_app: sublist.
Hint Rewrite @Zlength_map: sublist.
Hint Rewrite @Zlength_list_repeat using list_solve: sublist.
Hint Rewrite Z.sub_0_r Z.add_0_l Z.add_0_r : sublist.
Hint Rewrite @Zlength_sublist using list_solve: sublist.
Hint Rewrite Z.max_r Z.max_l using omega : sublist.
Hint Rewrite Z.min_r Z.min_l using omega : sublist.
Hint Rewrite Z.add_simpl_r Z.sub_add Z.sub_diag : sublist.
Hint Rewrite @sublist_sublist using list_solve : sublist.
Hint Rewrite @sublist_app1 using list_solve : sublist.
Hint Rewrite @sublist_app2 using list_solve : sublist.
Hint Rewrite @sublist_list_repeat  using list_solve : sublist.
Hint Rewrite @sublist_same using list_solve : sublist.
Hint Rewrite Z.add_simpl_l : sublist.
Hint Rewrite Z.add_add_simpl_l_l Z.add_add_simpl_l_r
     Z.add_add_simpl_r_l Z.add_add_simpl_r_r : sublist.
Hint Rewrite Z.add_0_r : sublist.
Hint Rewrite @app_Znth1 using list_solve : sublist.
Hint Rewrite @app_Znth2 using list_solve : sublist.
Hint Rewrite @Znth_sublist using list_solve : sublist.
Hint Rewrite @upd_Znth_Zlength using list_solve : sublist.


Hint Rewrite @sublist_nil : sublist.


Lemma list_repeat_app':
 forall {A: Type} a b (x:A), 
    0 <= a -> 0 <= b ->
    list_repeat (Z.to_nat a) x ++ list_repeat (Z.to_nat b) x = list_repeat (Z.to_nat (a+b)) x.
Proof.
 intros.
 rewrite list_repeat_app. f_equal.
  apply Nat2Z.inj. rewrite <- Z2Nat.inj_add; auto.
Qed.

Lemma Znth_overflow:
  forall {A}{d: Inhabitant A} i (al: list A), i >= Zlength al -> Znth i al = d.
Proof.
intros.
  pose proof (Zlength_nonneg al).
   unfold Znth. rewrite if_false by omega.
  apply nth_overflow.
  apply Nat2Z.inj_le. rewrite <- Zlength_correct.
  rewrite Z2Nat.id by omega. omega.
Qed.

Lemma Znth_underflow:
  forall {A}{d: Inhabitant A} i (al: list A),  i < 0 -> Znth i al = d.
Proof.
intros.
   unfold Znth. rewrite if_true by omega. auto.
Qed.

Lemma Znth_outofbounds:
  forall {A}{d: Inhabitant A} i (al: list A),  (i < 0 \/ i >= Zlength al) -> Znth i al = d.
Proof.
intros.
  destruct H. apply Znth_underflow; auto. apply Znth_overflow; auto.
Qed.

Lemma sublist_one:
  forall {A}{d: Inhabitant A} lo hi (al: list A),
    0 <= lo -> hi <= Zlength al ->
    lo+1=hi -> sublist lo hi al = Znth lo al :: nil.
Proof.
intros.
subst.
rewrite Znth_cons_sublist by omega. rewrite <- app_nil_end.
auto.
Qed.

Lemma Forall_app :
forall {A} P (l1 l2 :list A),
Forall P (l1 ++ l2) <->
Forall P l1 /\ Forall P l2.
intros.
split; induction l1; intros.
inv H. destruct l2; inv H0. auto.
split. auto. simpl in H2. inv H2.
constructor; auto.
split. inv H. constructor; auto. apply IHl1 in H3.
intuition.
inv H. apply IHl1 in H3. intuition.
simpl. intuition.
simpl. constructor.
destruct H. inv H. auto.
apply IHl1. intuition.
inv H0; auto.
Qed.

Lemma Forall_firstn:
  forall A (f: A -> Prop) n l, Forall f l -> Forall f (firstn n l).
Proof.
induction n; destruct l; intros.
constructor. constructor. constructor.
inv H. simpl. constructor; auto.
Qed.

Lemma Forall_skipn:
  forall A (f: A -> Prop) n l, Forall f l -> Forall f (skipn n l).
Proof.
induction n; destruct l; intros.
constructor. inv H; constructor; auto. constructor.
inv H. simpl.  auto.
Qed.

Lemma Forall_map:
  forall {A B} (f: B -> Prop) (g: A -> B) al,
   Forall f (map g al) <-> Forall (Basics.compose f g) al.
Proof.
intros.
induction al; simpl; intuition; inv H1; constructor; intuition.
Qed.

Lemma Forall_sublist:
  forall {A} (f: A -> Prop) lo hi al,
   Forall f al -> Forall f (sublist lo hi al).
Proof.
intros. unfold sublist.
apply Forall_firstn. apply Forall_skipn. auto.
Qed.

Hint Rewrite @upd_Znth_app1 using list_solve : sublist.
Hint Rewrite @upd_Znth_app2 using list_solve : sublist.

Lemma map_list_repeat: forall {A B} (f: A->B) n (x:A), map f (list_repeat n x) = list_repeat n (f x).
Proof.
intros. induction n; simpl; f_equal; auto.
Qed.
Hint Rewrite @map_list_repeat : sublist.

Lemma Zlength_sublist_correct: forall {A} (l: list A) (lo hi: Z),
  0 <= lo <= hi ->
  hi <= Zlength l ->
  Zlength (sublist lo hi l) = hi - lo.
Proof.
  intros.
  unfold sublist.
  rewrite Zlength_firstn.
  rewrite Z.max_r by omega.
  rewrite Z.min_l; auto.
  rewrite Zlength_skipn.
  rewrite (Z.max_r 0 lo) by omega.
  rewrite Z.max_r by omega.
  omega.
Qed.

Lemma Zlength_sublist_incorrect: forall {A} (l: list A) (lo hi: Z),
  0 <= lo < hi ->
  hi > Zlength l ->
  Zlength (sublist lo hi l) < hi - lo.
Proof.
  intros.
  unfold sublist.
  rewrite Zlength_firstn.
  rewrite Z.max_r by omega.
  assert (Zlength (skipn (Z.to_nat lo) l) < hi - lo); [| rewrite Z.min_r; omega].
  rewrite Zlength_skipn.
  rewrite (Z.max_r 0 lo) by omega.
  apply Z.max_lub_lt; omega.
Qed.

Lemma nth_Znth {A} {d: Inhabitant A}:
forall n (xs:list A), 0 <= n < Zlength xs -> (nth (Z.to_nat n) xs d) = (Znth n xs).
Proof. intros; unfold Znth; if_tac; unfold default. omega. reflexivity. Qed.


 