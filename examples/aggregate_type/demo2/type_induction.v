Require Import AggregateType.demo2.expr.
Require Import AggregateType.demo2.computable_theorems.
Open Scope nat.

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
  | Tstruct id => let m := co_members (get_co id) in Forall (fun it => P (field_type (fst it) m)) m
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
  + (* Tstruct level 0 *)
    simpl in RANK.
    unfold get_co in IH_TYPE.
    destruct (Maps.PTree.get id cenv_cs); [inv RANK | apply IH_TYPE; simpl; constructor].
  + (* Tstruct level positive *)
    simpl in RANK.
    pose proof I. (*get_co_members_no_replicate i.*)
    unfold get_co in *.
    destruct (Maps.PTree.get id cenv_cs) as [co |] eqn:CO; [| apply IH_TYPE; simpl; constructor].
    apply IH_TYPE; clear IH_TYPE.
    apply Forall_forall.
    intros [i0 t0] ?; simpl.
    apply IHn.
    pose proof rank_type_field_type _ _ _ _ H0.
    eapply le_trans; [eassumption |].
    apply le_S_n; auto.
    rewrite <- co_consistent_rank; auto.
    exact (cenv_consistent id co CO).
Defined.

Ltac type_induction t :=
  pattern t;
  match goal with
  | |- ?P t =>
    apply type_ind; clear t;
    let t := fresh "t" in
    intros t IH;
    let id := fresh "id" in
    destruct t as [ | id]
  end.

Variable A: type -> Type.

Definition FT_aux id :=
    let m := co_members (get_co id) in
    ListType (map (fun it => A (field_type (fst it) m)) m).

Variable F_Tint: forall t: type, A t.
Variable F_Tstruct: forall id, FT_aux id -> A (Tstruct id).

Fixpoint type_func_rec (n: nat) (t: type): A t :=
  match n with
  | 0 =>
    match t as t0 return A t0 with
    | Tstruct id =>
       match (Maps.PTree.get id cenv_cs)with
       | None => let m := co_members (get_co id) in
                       F_Tstruct id (ListTypeGen (fun it => A (field_type (fst it) m)) (fun it => F_Tint (field_type (fst it) m)) m)
       | _ => F_Tint (Tstruct id)
       end
    | t' => F_Tint t'
    end
  | S n' =>
    match t as t0 return A t0 with
    | Tstruct id =>  let m := co_members (get_co id) in
                            F_Tstruct id (ListTypeGen (fun it => A (field_type (fst it) m)) (fun it => type_func_rec n' (field_type (fst it) m)) m)
    | t' => F_Tint t'
    end
  end.

Definition type_func t := type_func_rec (rank_type cenv_cs t) t.

Lemma rank_type_Tstruct: forall id co, (Maps.PTree.get id cenv_cs) = Some co ->
  rank_type cenv_cs (Tstruct id) = S (co_rank (get_co id)).
Proof.
  intros.
  unfold get_co; simpl.
  destruct (Maps.PTree.get id cenv_cs); auto; congruence.
Defined.

Lemma type_func_rec_rank_irrelevent: forall t n n0,
  n >= rank_type cenv_cs t ->
  n0 >= rank_type cenv_cs t ->
  type_func_rec n t = type_func_rec n0 t.
Proof.
 (* DON'T USE omega IN THIS PROOF!
   We want the proof to compute reasonably efficiently.
*)
  intros t.
  type_induction t;
  intros;
  try solve [destruct n; simpl; auto; destruct n0; simpl; auto].
  + (* Tstruct *)
    unfold get_co in IH.
    destruct (Maps.PTree.get id cenv_cs) as [co |] eqn: CO.
    - erewrite rank_type_Tstruct in H by eauto.
      erewrite rank_type_Tstruct in H0 by eauto.
      destruct n; simpl in H; try solve [inv H].
      destruct n0; simpl in H; try solve [inv H0].
      simpl.
      f_equal.
      apply ListTypeGen_preserve.
      intros [i t] Hin.
      unfold get_co in H, H0, Hin |- *; rewrite CO in H, H0, Hin |- *.
      simpl in IH.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      specialize (IH (i, t) Hin n n0).
      apply le_S_n in H; apply le_S_n in H0.
      assert (H3 := rank_type_members cenv_cs i t _ Hin).
      apply IH.
      * simpl.
        eapply le_trans; [ | eassumption].
        erewrite co_consistent_rank; [eapply rank_type_field_type; eassumption |].
        exact (cenv_consistent id co CO).
      * simpl.
        eapply le_trans; [ | eassumption].
        erewrite co_consistent_rank; [eapply rank_type_field_type; eassumption |].
        exact (cenv_consistent id co CO).
    - destruct n, n0; simpl;  unfold FT_aux in *;
      generalize (F_Tstruct id) as FF; unfold get_co;
      rewrite CO; intros; auto.
Defined.

Definition FTI_aux id :=
    let m := co_members (get_co id) in
    (ListTypeGen (fun it => A (field_type (fst it) m)) (fun it => type_func (field_type (fst it) m)) m).


Lemma type_func_ind: forall t,
  type_func t =
  match t as t0 return A t0 with
  | Tstruct id => F_Tstruct id (FTI_aux id)
  | t' => F_Tint t'
  end.
Proof.
  intros.
  type_induction t; try reflexivity.
  + (* Tstruct *)
    unfold type_func in *.
    simpl type_func_rec.
    destruct (Maps.PTree.get id cenv_cs) as [co |] eqn:CO; simpl.
    - f_equal.
      apply ListTypeGen_preserve; intros [i t].
      unfold get_co; rewrite CO.
      intro Hin.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      apply type_func_rec_rank_irrelevent.
      * simpl.
        erewrite co_consistent_rank; [eapply rank_type_field_type; eassumption |].
        exact (cenv_consistent id co CO).
      * apply le_n.
    - rewrite CO.
      f_equal.
      unfold FTI_aux, get_co; rewrite CO.
      reflexivity.
Defined.

End COMPOSITE_ENV.

Arguments type_func {cs} A F_Tint F_Tstruct t / .

Ltac type_induction t :=
  pattern t;
  match goal with
  | |- ?P t =>
    apply type_ind; clear t;
    let t := fresh "t" in
    intros t IH;
    let id := fresh "id" in
    destruct t as [ | id]
  end.
