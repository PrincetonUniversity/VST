Require Import floyd.base.
Require floyd.fieldlist. Import floyd.fieldlist.fieldlist.
Open Scope nat.


Definition in_eq: forall {A: Type} (a:A) l, In a (a::l) :=
  fun A a l => or_introl eq_refl.

Definition Forall_forall: forall {A : Type} (P : A -> Prop) (l : list A),
       Forall P l <-> (forall x : A, In x l -> P x)   :=
fun (A : Type) (P : A -> Prop) (l : list A) =>
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
         | le_n =>
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
         | le_S m1 H0 =>
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
         | le_n =>
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
         | le_S m0 H0 =>
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
  forall ce id t m, In (id, t) m -> (rank_type ce t <= rank_members ce m)%nat.
Proof.
  induction m; simpl; intros; intuition auto.
  subst a.
  apply le_max_l.
  eapply le_trans; [eassumption | ].
  apply le_max_r.
Defined.

Inductive ListType: list Type -> Type :=
  | Nil: ListType nil
  | Cons: forall {A B} (a: A) (b: ListType B), ListType (A :: B).

Fixpoint ListTypeGen {A} (F: A -> Type) (f: forall A, F A) (l: list A) : ListType (map F l) :=
  match l with
  | nil => Nil
  | cons h t => Cons (f h) (ListTypeGen F f t)
  end.

Lemma ListTypeGen_preserve: forall A F f1 f2 (l: list A),
  (forall a, In a l -> f1 a = f2 a) ->
  ListTypeGen F f1 l = ListTypeGen F f2 l.
Proof.
  intros.
  induction l.
  + reflexivity.
  + simpl.
    rewrite H, IHl.
    - reflexivity.
    - intros; apply H; simpl; tauto.
    - simpl; left; auto.
Defined.

Definition decay' {X} {F: Type} {l: list X} (v: ListType (map (fun _ => F) l)): list F.
  remember (map (fun _ : X => F) l) eqn:E.
  revert l E.
  induction v; intros.
  + exact nil.
  + destruct l; inversion E.
    specialize (IHv l H1).
    rewrite H0 in a.
    exact (a :: IHv).
Defined.

Fixpoint decay'' {X} {F: Type} (l0 : list Type) (v: ListType l0) :
  forall (l: list X), l0 = map (fun _ => F) l -> list F :=
  match v in ListType l1
    return forall l2, l1 = map (fun _ => F) l2 -> list F
  with
  | Nil => fun _ _ => nil
  | Cons A B a b =>
    fun (l1 : list X) (E0 : A :: B = map (fun _ : X => F) l1) =>
    match l1 as l2 return (A :: B = map (fun _ : X => F) l2 -> list F) with
    | nil => fun _ => nil (* impossible case *)
    | x :: l2 =>
       fun E1 : A :: B = map (fun _ : X => F) (x :: l2) =>
       (fun
          X0 : map (fun _ : X => F) (x :: l2) =
               map (fun _ : X => F) (x :: l2) -> list F => 
        X0 eq_refl)
         match
           E1 in (_ = y)
           return (y = map (fun _ : X => F) (x :: l2) -> list F)
         with
         | eq_refl =>
             fun H0 : A :: B = map (fun _ : X => F) (x :: l2) =>
              (fun (H3 : A = F) (H4 : B = map (fun _ : X => F) l2) =>
                  (eq_rect A (fun A0 : Type => A0) a F H3) :: (decay'' B b l2 H4))
                 (f_equal
                    (fun e : list Type =>
                     match e with
                     | nil => A
                     | T :: _ => T
                     end) H0)
                (f_equal
                   (fun e : list Type =>
                    match e with
                    | nil => B
                    | _ :: l3 => l3
                    end) H0)
         end
    end E0
  end.

Definition decay {X} {F: Type} {l: list X} (v: ListType (map (fun _ => F) l)): list F :=
  let l0 := map (fun _ => F) l in 
  let E := @eq_refl _ (map (fun _ => F) l) : l0 = map (fun _ => F) l in
  decay'' l0 v l E.

Lemma decay_spec: forall A F f l,
  decay (ListTypeGen (fun _: A => F) f l) = map f l.
Proof.
  intros.
  unfold decay.
  induction l.
  + simpl.
    reflexivity.
  + simpl.
    f_equal.
    auto.
Defined.

Section COMPOSITE_ENV.
Context {cs: compspecs}.

Lemma type_ind: forall P : type -> Prop,
  (forall t,
  match t with
  | Tarray t0 _ _ => P t0
  | Tstruct id _ => let m := co_members (get_co id) in Forall (fun it => P (field_type (fst it) m)) m
  | Tunion id _ => let m := co_members (get_co id) in Forall (fun it => P (field_type (fst it) m)) m
  | _ => True
  end -> P t) ->
  forall t, P t.
Proof.
  intros P IH_TYPE.
  intros.
  remember (rank_type cenv_cs t) as n eqn: RANK'.
  assert (rank_type cenv_cs t <= n)%nat as RANK.
  subst. apply le_n.
  clear RANK'.
  revert t RANK.
  induction n;
  intros;
  specialize (IH_TYPE t); destruct t;
  try solve [specialize (IH_TYPE I); auto].
  + (* Tarray level 0 *)
    simpl in RANK. inv RANK.
  + (* Tstruct level 0 *)
    simpl in RANK.
    unfold get_co in IH_TYPE.
    destruct (cenv_cs ! i); [inv RANK | apply IH_TYPE; simpl; constructor].
  + (* Tunion level 0 *)
    simpl in RANK.
    unfold get_co in IH_TYPE.
    destruct (cenv_cs ! i); [inv RANK | apply IH_TYPE].
    simpl; constructor.
  + (* Tarray level positive *)
    simpl in RANK.
    specialize (IHn t).
    apply IH_TYPE, IHn.
    apply le_S_n; auto.
  + (* Tstruct level positive *)
    simpl in RANK.
    pose proof get_co_members_no_replicate i.
    unfold get_co in *.
    destruct (cenv_cs ! i) as [co |] eqn:CO; [| apply IH_TYPE; simpl; constructor].
    apply IH_TYPE; clear IH_TYPE.
    apply Forall_forall.
    intros [i0 t0] ?; simpl.
    apply IHn.
    pose proof In_field_type _ _ H H0.
    simpl in H1; rewrite H1.
    apply rank_type_members with (ce := cenv_cs) in H0.
    rewrite <- co_consistent_rank in H0.
    eapply le_trans; [eassumption |].
    apply le_S_n; auto.
    exact (cenv_consistent i co CO).
  + (* Tunion level positive *)
    simpl in RANK.
    pose proof get_co_members_no_replicate i.
    unfold get_co in *.
    destruct (cenv_cs ! i) as [co |] eqn:CO; [| apply IH_TYPE; simpl; constructor].
    apply IH_TYPE; clear IH_TYPE.
    apply Forall_forall.
    intros [i0 t0] ?; simpl.
    apply IHn.
    pose proof In_field_type _ _ H H0.
    simpl in H1; rewrite H1.
    apply rank_type_members with (ce := cenv_cs) in H0.
    rewrite <- co_consistent_rank in H0.
    eapply le_trans; [eassumption |].
    apply le_S_n; auto.
    exact (cenv_consistent i co CO).
Defined.

Ltac type_induction t :=
  pattern t;
  match goal with
  | |- ?P t =>
    apply type_ind; clear t;
    let t := fresh "t" in
    intros t IH;
    let id := fresh "id" in
    let a := fresh "a" in
    destruct t as [| | | | | | | id a | id a]
  end.

Variable A: type -> Type.

Definition FT_aux id :=
    let m := co_members (get_co id) in
    ListType (map (fun it => A (field_type (fst it) m)) m).

Variable F_ByValue: forall t: type, A t.
Variable F_Tarray: forall t n a, A t -> A (Tarray t n a).
Variable F_Tstruct: forall id a, FT_aux id -> A (Tstruct id a).
Variable F_Tunion: forall id a, FT_aux id -> A (Tunion id a).

Fixpoint func_type_rec (n: nat) (t: type): A t :=
  match n with
  | 0 =>
    match t as t0 return A t0 with
    | Tstruct id a =>
       match cenv_cs ! id with
       | None => let m := co_members (get_co id) in
                       F_Tstruct id a (ListTypeGen (fun it => A (field_type (fst it) m)) (fun it => F_ByValue (field_type (fst it) m)) m)
       | _ => F_ByValue (Tstruct id a)
       end
    | Tunion id a =>
       match cenv_cs ! id with
       | None => let m := co_members (get_co id) in
                      F_Tunion id a (ListTypeGen (fun it => A (field_type (fst it) m)) (fun it => F_ByValue (field_type (fst it) m)) m)
       | _ => F_ByValue (Tunion id a)
       end
    | t' => F_ByValue t'
    end
  | S n' =>
    match t as t0 return A t0 with
    | Tarray t0 n a => F_Tarray t0 n a (func_type_rec n' t0)
    | Tstruct id a =>  let m := co_members (get_co id) in
                            F_Tstruct id a (ListTypeGen (fun it => A (field_type (fst it) m)) (fun it => func_type_rec n' (field_type (fst it) m)) m)
    | Tunion id a =>  let m := co_members (get_co id) in
                            F_Tunion id a (ListTypeGen (fun it => A (field_type (fst it) m)) (fun it => func_type_rec n' (field_type (fst it) m)) m)
    | t' => F_ByValue t'
    end
  end.

Definition func_type t := func_type_rec (rank_type cenv_cs t) t.

Lemma rank_type_Tstruct: forall id a co, cenv_cs ! id = Some co ->
  rank_type cenv_cs (Tstruct id a) = S (co_rank (get_co id)).
Proof.
  intros.
  unfold get_co; simpl.
  destruct (cenv_cs ! id); auto; congruence.
Defined.

Lemma rank_type_Tunion: forall id a co, cenv_cs ! id = Some co ->
  rank_type cenv_cs (Tunion id a) = S (co_rank (get_co id)).
Proof.
  intros.
  unfold get_co; simpl.
  destruct (cenv_cs ! id); auto; congruence.
Defined.

(*
Lemma func_type_rec_rank_irrelevent1: forall t n,
  n >= rank_type cenv_cs t ->
  func_type_rec (S n) t = func_type_rec n t.
Proof.
  intro t. type_induction t; simpl; intros;
  try solve [destruct n; try solve [inv H]; reflexivity];
  (destruct n; [inv H | ]).
  simpl; rewrite <- (IH n) by (apply le_S_n; auto); reflexivity.
  simpl.
  clear - H1.
  rewrite H1.
  destruct (cenv_cs ! id) eqn:?; try solve [inv H1]; simpl. rewrite Heqo.
  f_equal.
  unfold get_co. rewrite Heqo.
  simpl. reflexivity.
  simpl.
  f_equal.
  unfold get_co in *.
  destruct (cenv_cs ! id) eqn:?.
    revert IH; induction (co_members c); simpl.
  intros; auto.
  simpl. intros.
  f_equal.
  rewrite <- IH.
  unfold get_co in IH. rewrite Heqo in IH.
 try solve [inv H]; simpl. rewrite Heqo.
  f_equal.
  unfold get_co. rewrite Heqo.
  simpl. reflexivity.
  
  
 simpl. rewrite H1.
   clear F_ByValue.
 F_Tarray F_Tstruct F_Tunion.
  revert 
  destruct (co_members (get_co id)) eqn:?.
  unfold get_co.
  destruct (cenv_cs ! id) eqn:?; try solve [inv H1]; simpl. rewrite Heqo.
unfold get_co. rewrite Heqo.

  clear H1.
  revert F_ByValue F_Tarray F_Tstruct IH.
  revert IH; destruct  (co_members (get_co id)) eqn:?.
  f_equal.
  

 f_equal. rewrite <- 
  simpl.
  simpl.
  simpl.
  induction n; destruct t; intros; simpl; try solve [inv H]; try reflexivity;;
  simpl in *.
  destruct (cenv_cs ! i); try solve [inv H].
  f_equal.
  clear H.
  destruct (co_members (get_co i)); simpl; auto.
  f_equal.
  f_equal.

  try solve [  destruct n; reflexivity].
  destruct n. inv H. simpl.
  f_equal.
  simpl in H.
  induction n; simpl; auto.

Focus 2.
  apply IHn.
  destruct t; try reflexivity; try solve [inv H].
simpl in *. destruct (cenv_cs ! i); try reflexivity; try solve [inv H ];
  simpl in H.
  f_equal.
 simpl.
 unfold rank_type in H.
simpl in *.
 inv H.
simpl in H.
Print rank_type.
 simpl.
 simp
  type_induction t; intros.
 unfold func_type_rec.
*)

Lemma func_type_rec_rank_irrelevent: forall t n n0,
  n >= rank_type cenv_cs t ->
  n0 >= rank_type cenv_cs t ->
  func_type_rec n t = func_type_rec n0 t.
Proof.
 (* DON'T USE omega IN THIS PROOF!  
   We want the proof to compute reasonably efficiently.
*)
  intros t.
  type_induction t;
  intros;
  try solve [destruct n; simpl; auto; destruct n0; simpl; auto].
  + (* Tarray *)
    destruct n; simpl in H; try solve [inv H].
    destruct n0; simpl in H; try solve [inv H0].
    simpl. f_equal. 
    apply IH; apply le_S_n; auto.
  + (* Tstruct *)
    destruct (cenv_cs ! id) as [co |] eqn: CO.
    - erewrite rank_type_Tstruct in H by eauto.
      erewrite rank_type_Tstruct in H0 by eauto.
      clear co CO.
    destruct n; simpl in H; try solve [inv H].
    destruct n0; simpl in H; try solve [inv H0].
      simpl.
      f_equal.
      apply ListTypeGen_preserve.
      intros [i t] Hin.
      simpl in IH.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      specialize (IH (i, t) Hin n n0).
      apply le_S_n in H; apply le_S_n in H0.
      assert (H3 := rank_type_members cenv_cs i t _ Hin).
      pose proof get_co_members_no_replicate id.
      pose proof In_field_type (i, t) _ H1 Hin.
      rewrite <- (co_consistent_rank cenv_cs (get_co id) (get_co_consistent _)) in H3.
      apply IH;
       (eapply le_trans; [ | eassumption]; rewrite H2; auto).
    - destruct n, n0; simpl;  unfold FT_aux in *;
      generalize (F_Tstruct id a) as FF; unfold get_co;
      rewrite CO; intros; auto.
  + (* Tunion *)
    destruct (cenv_cs ! id) as [co |] eqn: CO.
    - erewrite rank_type_Tunion in H by eauto.
      erewrite rank_type_Tunion in H0 by eauto.
      clear co CO.
    destruct n; simpl in H; try solve [inv H].
    destruct n0; simpl in H; try solve [inv H0].
      simpl.
      f_equal.
      apply ListTypeGen_preserve.
      intros [i t] Hin.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      specialize (IH (i, t) Hin n n0).
      apply le_S_n in H; apply le_S_n in H0.
      assert (H3 := rank_type_members cenv_cs i t _ Hin).
      pose proof get_co_members_no_replicate id.
      pose proof In_field_type (i, t) _ H1 Hin.
      rewrite <- (co_consistent_rank cenv_cs (get_co id) (get_co_consistent _)) in H3.
      apply IH;
       (eapply le_trans; [ | eassumption]; rewrite H2; auto).
    - destruct n, n0; simpl;  unfold FT_aux in *;
      generalize (F_Tunion id a) as FF; unfold get_co;
      rewrite CO; intros; auto.
Defined.

Definition FTI_aux id :=
    let m := co_members (get_co id) in
    (ListTypeGen (fun it => A (field_type (fst it) m)) (fun it => func_type (field_type (fst it) m)) m).


Lemma func_type_ind: forall t, 
  func_type t =
  match t as t0 return A t0 with
  | Tarray t0 n a => F_Tarray t0 n a (func_type t0)
  | Tstruct id a => F_Tstruct id a (FTI_aux id)
  | Tunion id a => F_Tunion id a (FTI_aux id)
  | t' => F_ByValue t'
  end.
Proof.
  intros.
  type_induction t; try reflexivity.
  + (* Tstruct *)
    unfold func_type in *.
    simpl func_type_rec.
    destruct (cenv_cs ! id) as [co |] eqn:CO; simpl.
    - f_equal.
      apply ListTypeGen_preserve; intros [i t].
      unfold get_co; rewrite CO.
      intro Hin.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      apply func_type_rec_rank_irrelevent.
      * assert (H0 := get_co_members_no_replicate id).
        unfold get_co in H0; rewrite CO in H0.
        rewrite (In_field_type _ _ H0 Hin).
        rewrite (co_consistent_rank cenv_cs _
                           (cenv_consistent id co CO)).
        eapply rank_type_members; eauto.
      * apply le_n.
    - rewrite CO.
      f_equal.
      unfold FTI_aux, get_co; rewrite CO.
      reflexivity.
  + (* Tunion *)
    unfold func_type in *.
    simpl func_type_rec.
    destruct (cenv_cs ! id) as [co |] eqn:CO; simpl.
    - f_equal.
      apply ListTypeGen_preserve; intros [i t].
      unfold get_co; rewrite CO.
      intro Hin.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      apply func_type_rec_rank_irrelevent.
      * assert (H0 := get_co_members_no_replicate id).
        unfold get_co in H0; rewrite CO in H0.
        rewrite (In_field_type _ _ H0 Hin).
        rewrite (co_consistent_rank cenv_cs _
                           (cenv_consistent id co CO)).
        eapply rank_type_members; eauto.
      * apply le_n.
    - rewrite CO.
      f_equal.
      unfold FTI_aux, get_co; rewrite CO.
      reflexivity.
Defined.

End COMPOSITE_ENV.

Arguments func_type {cs} A F_ByValue F_Tarray F_Tstruct F_Tunion t / .

Ltac type_induction t :=
  pattern t;
  match goal with
  | |- ?P t =>
    apply type_ind; clear t;
    let t := fresh "t" in
    intros t IH;
    let id := fresh "id" in
    let a := fresh "a" in
    destruct t as [| | | | | | | id a | id a]
  end.

