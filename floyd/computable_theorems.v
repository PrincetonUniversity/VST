From Stdlib Require Import ZArith.ZArith ZArith.Znumtheory Lists.List Bool.Bool.
Require Import compcert.cfrontend.Ctypes.

Definition in_eq: forall {A: Type} (a:A) l, In a (a::l) :=
  fun {A} a l => or_introl eq_refl.

Definition Forall_forall: forall {A : Type} (P : A -> Prop) (l : list A),
       Forall P l <-> (forall x : A, In x l -> P x)   :=
fun {A : Type} (P : A -> Prop) (l : list A) =>
conj
  (fun H : Forall P l =>
   Forall_ind (fun l0 : list A => forall x : A, In x l0 -> P x)
     (fun (x : A) (H0 : In x nil) => False_ind (P x) H0)
     (fun (x : A) (l0 : list A) (H0 : P x) (_ : Forall P l0)
        (IHForall : forall x0 : A, In x0 l0 -> P x0) (x0 : A)
        (H2 : In x0 (x :: l0)) =>
      or_ind
        (fun H3 : x = x0 =>
         eq_ind_r (fun x1 : A => P x1 -> P x0) (fun H4 : P x0 => H4) H3 H0)
        (fun H3 : In x0 l0 =>
         (fun H4 : In x0 l0 -> P x0 => (fun H5 : P x0 => H5) (H4 H3))
           (IHForall x0)) H2) H)
  (list_ind
     (fun l0 : list A => (forall x : A, In x l0 -> P x) -> Forall P l0)
     (fun _ : forall x : A, In x nil -> P x => Forall_nil P)
     (fun (a : A) (l0 : list A)
        (IHl : (forall x : A, In x l0 -> P x) -> Forall P l0)
        (H : forall x : A, In x (a :: l0) -> P x) =>
      (fun H0 : forall x : A, In x l0 -> P x =>
       (fun H1 : forall x : A, In x l0 -> P x =>
        (fun H2 : Forall P l0 =>
         (fun H3 : A =>
          (fun X : A =>
           (fun H4 : In X (a :: l0) -> P X =>
            (fun (_ : a = X -> P X)
               (_ : (fix In (a0 : A) (l1 : list A) {struct l1} : Prop :=
                       match l1 with
                       | nil => False
                       | b :: m => b = a0 \/ In a0 m
                       end) X l0 -> P X) =>
             Forall_cons a (H a (in_eq a l0)) H2)
              (fun H5 : a = X => H4 (or_introl H5))
              (fun
                 H5 : (fix In (a0 : A) (l1 : list A) {struct l1} : Prop :=
                         match l1 with
                         | nil => False
                         | b :: m => b = a0 \/ In a0 m
                         end) X l0 => H4 (or_intror H5))) (H X)) H3) a)
          (IHl H1)) H0)
        (fun (x : A) (H0 : In x l0) =>
         (fun H1 : In x (a :: l0) -> P x =>
          (fun (_ : a = x -> P x)
             (H3 : (fix In (a0 : A) (l1 : list A) {struct l1} : Prop :=
                      match l1 with
                      | nil => False
                      | b :: m => b = a0 \/ In a0 m
                      end) x l0 -> P x) => (fun H4 : P x => H4) (H3 H0))
            (fun H2 : a = x => H1 (or_introl H2))
            (fun
               H2 : (fix In (a0 : A) (l1 : list A) {struct l1} : Prop :=
                       match l1 with
                       | nil => False
                       | b :: m => b = a0 \/ In a0 m
                       end) x l0 => H1 (or_intror H2))) (H x))) l).

Lemma Forall_forall1: forall {A : Type} (P : A -> Prop) (l : list A),
       Forall P l -> (forall x : A, In x l -> P x).
Proof.
intros until 1.
destruct (@Forall_forall A P l).
apply H0. auto.
Defined.

Lemma Zcompare_refl: forall n, Z.compare n n = Eq.
Proof.
intros.
destruct n; simpl.
apply eq_refl.
unfold Pos.compare.
induction p; simpl; auto.
unfold Pos.compare.
induction p; simpl; auto.
Defined.

Lemma Zle_refl: forall n, Z.le n n.
Proof.
intros.
unfold Z.le. rewrite Zcompare_refl. intro; discriminate.
Defined.

Lemma Zle_max_l: forall n m : Z, n <= Z.max n m.
Proof.
intros.
unfold Z.max.
unfold Z.le.
destruct (n?=m) eqn:H.
rewrite Zcompare_refl; intro; discriminate.
rewrite H. intro; discriminate.
rewrite Zcompare_refl; intro; discriminate.
Defined.

Definition Pos_compare_cont_antisym :
  forall (p q : positive) (c : comparison),
       eq (CompOpp (Pos.compare_cont c p q))
         (Pos.compare_cont (CompOpp c) q p ) :=
fun (p q : positive) (c : comparison) =>
positive_ind
  (fun p0 : positive =>
   forall (q0 : positive) (c0 : comparison),
   CompOpp (Pos.compare_cont c0 p0 q0) =
   Pos.compare_cont (CompOpp c0) q0 p0)
  (fun (p0 : positive)
     (IHp : forall (q0 : positive) (c0 : comparison),
            CompOpp (Pos.compare_cont c0 p0 q0) =
            Pos.compare_cont (CompOpp c0) q0 p0)
     (q0 : positive) =>
   match
     q0 as p1
     return
       (forall c0 : comparison,
        CompOpp (Pos.compare_cont c0 p0~1 p1) =
        Pos.compare_cont (CompOpp c0) p1 p0~1)
   with
   | (q1~1)%positive =>
       fun c0 : comparison => IHp q1 c0
   | (q1~0)%positive =>
       fun c0 : comparison => IHp q1 Gt
   | 1%positive => fun c0 : comparison => eq_refl
   end)
  (fun (p0 : positive)
     (IHp : forall (q0 : positive) (c0 : comparison),
            CompOpp (Pos.compare_cont c0 p0 q0) =
            Pos.compare_cont (CompOpp c0) q0 p0)
     (q0 : positive) =>
   match
     q0 as p1
     return
       (forall c0 : comparison,
        CompOpp (Pos.compare_cont c0 p0~0 p1) =
        Pos.compare_cont (CompOpp c0) p1 p0~0)
   with
   | (q1~1)%positive =>
       fun c0 : comparison => IHp q1 Lt
   | (q1~0)%positive =>
       fun c0 : comparison => IHp q1 c0
   | 1%positive => fun c0 : comparison => eq_refl
   end)
  (fun q0 : positive =>
   match
     q0 as p0
     return
       (forall c0 : comparison,
        CompOpp (Pos.compare_cont c0 1 p0) =
        Pos.compare_cont (CompOpp c0) p0 1)
   with
   | (q1~1)%positive =>
       fun c0 : comparison => eq_refl
   | (q1~0)%positive =>
       fun c0 : comparison => eq_refl
   | 1%positive => fun c0 : comparison => eq_refl
   end) p q c.

Definition Pos_compare_antisym:
  forall p q : positive,
       eq (Pos.compare q p) (CompOpp (Pos.compare p q)) :=
  fun p q : positive =>
eq_ind_r (fun c : comparison => eq (Pos.compare_cont Eq q p) c) eq_refl
  (Pos_compare_cont_antisym p q Eq).

Lemma Pos_compare_absurd:
  forall x y c, (eq (Pos.compare_cont c x y) Eq) -> c=Eq.
Proof.
induction x; destruct y; simpl; intros; eauto; try discriminate.
apply IHx in H; discriminate.
apply IHx in H; discriminate.
Defined.

Lemma Pos_compare_cont_eq:
  forall x y c, eq (Pos.compare_cont c x y) Eq -> eq x y.
Proof.
induction x; destruct y; simpl; intros; auto; try discriminate.
f_equal. eauto.
apply Pos_compare_absurd in H; inversion H.
apply Pos_compare_absurd in H; inversion H.
f_equal. eauto.
Defined.

Lemma Pos_compare_eq:
  forall x y, eq (Pos.compare x y) Eq -> eq x y.
Proof.
intros.
apply Pos_compare_cont_eq in H; auto.
Defined.

Lemma Zmax_comm: forall n m, Z.max n m = Z.max m n.
Proof.
destruct n, m; simpl; try apply eq_refl.
*
 unfold Z.max; simpl.
 rename p0 into q.
 rewrite Pos_compare_antisym.
 destruct (Pos.compare q p) eqn:?; simpl; try reflexivity.
 apply Pos_compare_eq in Heqc.
 apply f_equal. symmetry; auto.
*
 unfold Z.max; simpl.
 rename p0 into q.
 rewrite Pos_compare_antisym.
 destruct (Pos.compare q p) eqn:?; simpl; try reflexivity.
 apply Pos_compare_eq in Heqc.
 apply f_equal. symmetry; auto.
Defined.

Lemma Zle_max_r: forall n m : Z, m <= Z.max n m.
Proof.
intros.
rewrite Z.max_comm. apply Zle_max_l.
Defined.

Local Open Scope nat.

Definition le_pred: forall n m : nat, n <= m -> pred n <= pred m :=
fun (n m : nat) (H : n <= m) =>
le_ind n (fun m0 : nat => pred n <= pred m0) (le_n (pred n))
  (fun (m0 : nat) (H0 : n <= m0) (IHle : pred n <= pred m0) =>
   match
     m0 as n0 return (n <= n0 -> pred n <= pred n0 -> pred n <= pred (S n0))
   with
   | 0 => fun (_ : n <= 0) (IHle0 : pred n <= pred 0) => IHle0
   | S m1 =>
       fun (_ : n <= S m1) (IHle0 : pred n <= pred (S m1)) =>
       le_S (pred n) m1 IHle0
   end H0 IHle) m H.

Definition le_S_n : forall n m : nat, S n <= S m -> n <= m  :=
   fun n m => le_pred (S n) (S m).

Definition max_l: forall n m : nat, m <= n -> max n m = n :=
fun n : nat =>
nat_ind (fun n0 : nat => forall m : nat, m <= n0 -> max n0 m = n0)
  (fun m : nat =>
   match m as n0 return (n0 <= 0 -> max 0 n0 = 0) with
   | 0 => fun _ : 0 <= 0 => eq_refl
   | S m0 =>
       fun H : S m0 <= 0 =>
       (fun H0 : 0 = 0 -> S m0 = 0 => H0 eq_refl)
         match H in (_ <= n0) return (n0 = 0 -> S m0 = 0) with
         | le_n _ =>
             fun H0 : S m0 = 0 =>
             (fun H1 : S m0 = 0 =>
              (fun H2 : False =>
               (fun H3 : False => False_ind (S m0 = 0) H3) H2)
                (eq_ind (S m0)
                   (fun e : nat =>
                    match e with
                    | 0 => False
                    | S _ => True
                    end) I 0 H1)) H0
         | le_S _ m1 H0 =>
             fun H1 : S m1 = 0 =>
             (fun H2 : S m1 = 0 =>
              (fun H3 : False =>
               (fun H4 : False => False_ind (S m0 <= m1 -> S m0 = 0) H4) H3)
                (eq_ind (S m1)
                   (fun e : nat =>
                    match e with
                    | 0 => False
                    | S _ => True
                    end) I 0 H2)) H1 H0
         end
   end)
  (fun (n0 : nat) (IHn : forall m : nat, m <= n0 -> max n0 m = n0) (m : nat) =>
   match m as n1 return (n1 <= S n0 -> max (S n0) n1 = S n0) with
   | 0 => fun _ : 0 <= S n0 => eq_refl
   | S m0 =>
       fun H : S m0 <= S n0 => f_equal S (IHn m0 (le_S_n m0 n0 H))
   end) n.

Definition max_r     : forall n m : nat, n <= m -> max n m = m :=
fun n : nat =>
nat_ind (fun n0 : nat => forall m : nat, n0 <= m -> max n0 m = m)
  (fun m : nat =>
   match m as n0 return (0 <= n0 -> max 0 n0 = n0) with
   | 0 => fun _ : 0 <= 0 => eq_refl
   | S m0 => fun _ : 0 <= S m0 => eq_refl
   end)
  (fun (n0 : nat) (IHn : forall m : nat, n0 <= m -> max n0 m = m) (m : nat) =>
   match m as n1 return (S n0 <= n1 -> max (S n0) n1 = n1) with
   | 0 =>
       fun H : S n0 <= 0 =>
       (fun H0 : 0 = 0 -> S n0 = 0 => H0 eq_refl)
         match H in (_ <= n1) return (n1 = 0 -> S n0 = 0) with
         | le_n _ =>
             fun H0 : S n0 = 0 =>
             (fun H1 : S n0 = 0 =>
              (fun H2 : False =>
               (fun H3 : False => False_ind (S n0 = 0) H3) H2)
                (eq_ind (S n0)
                   (fun e : nat =>
                    match e with
                    | 0 => False
                    | S _ => True
                    end) I 0 H1)) H0
         | le_S _ m0 H0 =>
             fun H1 : S m0 = 0 =>
             (fun H2 : S m0 = 0 =>
              (fun H3 : False =>
               (fun H4 : False => False_ind (S n0 <= m0 -> S n0 = 0) H4) H3)
                (eq_ind (S m0)
                   (fun e : nat =>
                    match e with
                    | 0 => False
                    | S _ => True
                    end) I 0 H2)) H1 H0
         end
   | S m0 =>
       fun H : S n0 <= S m0 => f_equal S (IHn m0 (le_S_n n0 m0 H))
   end) n.

Definition le_n_S : forall n m : nat, n <= m -> S n <= S m :=
fun (n m : nat) (H : n <= m) =>
le_ind n (fun m0 : nat => S n <= S m0) (le_n (S n))
  (fun (m0 : nat) (_ : n <= m0) (IHle : S n <= S m0) =>
   le_S (S n) (S m0) IHle) m H.

Definition lt_n_S: forall n m : nat, n < m -> S n < S m :=
fun (n m : nat) (H : n < m) => le_n_S (S n) m H.

Definition le_trans: forall n m p : nat, n <= m -> m <= p -> n <= p :=
fun (n m p : nat) (H : n <= m) (H0 : m <= p) =>
le_ind m (fun p0 : nat => n <= p0) H
  (fun (m0 : nat) (_ : m <= m0) (IHle : n <= m0) => le_S n m0 IHle) p H0.

Definition le_Sn_le: forall n m : nat, S n <= m -> n <= m :=
fun (n m : nat) (H : S n <= m) => le_trans n (S n) m (le_S n n (le_n n)) H.

Definition lt_le_weak: forall n m : nat, n < m -> n <= m :=
fun (n m : nat) (H : n < m) => le_Sn_le n m H.

Lemma le_or_lt: forall n m : nat, n <= m \/ m < n.
Proof.
induction n; intros.
left. induction m; simpl; auto.
destruct m.
right. unfold lt. clear. induction n; simpl; auto.
destruct (IHn m); [left | right].
apply le_n_S. auto.
apply lt_n_S. auto.
Defined.

Lemma le_max_l: forall n m : nat, n <= max n m.
Proof.
intros.
destruct (le_or_lt n m).
rewrite max_r; auto.
rewrite max_l; auto.
apply lt_le_weak; auto.
Defined.

Lemma le_max_r: forall n m : nat, m <= max n m.
Proof.
intros.
destruct (le_or_lt n m).
rewrite max_r; auto.
rewrite max_l; auto.
apply lt_le_weak; auto.
apply lt_le_weak; auto.
Defined.

Lemma rank_type_members:
  forall ce m1 m, In m1 m -> (rank_type ce (type_member m1) <= rank_members ce m)%nat.
Proof.
  induction m as [|[|]]; simpl; intros; intuition auto; try subst m1.
  apply le_max_l.
  eapply le_trans; [eassumption | ].
  apply le_max_r.
  apply Peano.le_0_n.
Defined.
