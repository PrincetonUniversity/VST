Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.fieldlist.
Require Import VST.floyd.computable_theorems.
Require Export stdpp.hlist. (* use this instead of ListType to avoid universe inconsistencies? *)
Open Scope nat.

(*Inductive ListType: list Type -> Type :=
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
    rewrite H; first rewrite IHl.
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
Defined.*)

Fixpoint tmap {A} (f : A -> Type) l : tlist :=
  match l with
  | [] => tnil
  | x :: rest => tcons (f x) (tmap f rest)
  end.

Fixpoint hmap {A} (F: A -> Type) (f: forall A, F A) (l: list A) : hlist (tmap F l) :=
  match l with
  | nil => hnil
  | cons h t => hcons (f h) (hmap F f t)
  end.

Lemma hmap_preserve: forall A F f1 f2 (l: list A),
  (forall a, In a l -> f1 a = f2 a) ->
  hmap F f1 l = hmap F f2 l.
Proof.
  intros.
  induction l.
  + reflexivity.
  + simpl.
    rewrite H; first rewrite IHl.
    - reflexivity.
    - intros; apply H; simpl; tauto.
    - simpl; left; auto.
Defined.

Definition decay' {X} {F: Type} {l: list X} (v: hlist (tmap (fun _ => F) l)): list F.
  remember (tmap (fun _ : X => F) l) eqn:E.
  revert l E.
  induction v; intros.
  + exact nil.
  + destruct l; inversion E.
    specialize (IHv l H1).
    rewrite H0 in a.
    exact (a :: IHv).
Defined.

Fixpoint decay'' {X} {F: Type} (l0 : tlist) (v: hlist l0) :
  forall (l: list X), l0 = tmap (fun _ => F) l -> list F :=
  match v in hlist l1
    return forall l2, l1 = tmap (fun _ => F) l2 -> list F
  with
  | hnil => fun _ _ => nil
  | hcons A B a b =>
    fun (l1 : list X) (E0 : tcons A B = tmap (fun _ : X => F) l1) =>
    match l1 as l2 return (tcons A B = tmap (fun _ : X => F) l2 -> list F) with
    | nil => fun _ => nil (* impossible case *)
    | x :: l2 =>
       fun E1 : tcons A B = tmap (fun _ : X => F) (x :: l2) =>
       (fun
          X0 : tmap (fun _ : X => F) (x :: l2) =
               tmap (fun _ : X => F) (x :: l2) -> list F =>
        X0 eq_refl)
         match
           E1 in (_ = y)
           return (y = tmap (fun _ : X => F) (x :: l2) -> list F)
         with
         | eq_refl =>
             fun H0 : tcons A B = tmap (fun _ : X => F) (x :: l2) =>
              (fun (H3 : A = F) (H4 : B = tmap (fun _ : X => F) l2) =>
                  (eq_rect A (fun A0 : Type => A0) a F H3) :: (decay'' B b l2 H4))
                 (f_equal
                    (fun e : tlist =>
                     match e with
                     | tnil => A
                     | tcons T _ => T
                     end) H0)
                (f_equal
                   (fun e : tlist =>
                    match e with
                    | tnil => B
                    | tcons _ l3 => l3
                    end) H0)
         end
    end E0
  end.

Definition decay {X} {F: Type} {l: list X} (v: hlist (tmap (fun _ => F) l)): list F :=
  let l0 := tmap (fun _ => F) l in
  let E := @eq_refl _ (tmap (fun _ => F) l) : l0 = tmap (fun _ => F) l in
  decay'' l0 v l E.

Lemma decay_spec: forall A F f l,
  decay (hmap (fun _: A => F) f l) = map f l.
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
  | Tstruct id _ => let m := co_members (get_co id) in Forall (fun it => P (field_type (name_member it) m)) m
  | Tunion id _ => let m := co_members (get_co id) in Forall (fun it => P (field_type (name_member it) m)) m
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
    destruct (Maps.PTree.get i cenv_cs); [inv RANK | apply IH_TYPE; simpl; constructor].
  + (* Tunion level 0 *)
    simpl in RANK.
    unfold get_co in IH_TYPE.
    destruct (Maps.PTree.get i cenv_cs); [inv RANK | apply IH_TYPE].
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
    destruct (Maps.PTree.get i cenv_cs) as [co |] eqn:CO; [| apply IH_TYPE; simpl; constructor].
    apply IH_TYPE; clear IH_TYPE.
    apply Forall_forall.
    intros ? ?; simpl.
    * apply IHn.
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
    destruct (Maps.PTree.get i cenv_cs) as [co |] eqn:CO; [| apply IH_TYPE; simpl; constructor].
    apply IH_TYPE; clear IH_TYPE.
    apply Forall_forall.
    intros ? ?; simpl.
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

Definition A_members (ms: members) (m: member) : Type :=
    A (field_type (name_member m) ms).

Definition FT_aux id :=
    let m := co_members (get_co id) in hlist (tmap (fun it => A (field_type (name_member it) m)) m).

Variable F_ByValue: forall t: type, A t.
Variable F_Tarray: forall t n a, A t -> A (Tarray t n a).
Variable F_Tstruct: forall id a, FT_aux id -> A (Tstruct id a).
Variable F_Tunion: forall id a, FT_aux id -> A (Tunion id a).


Fixpoint type_func_rec (n: nat) (t: type): A t :=
  match n with
  | 0 =>
    match t as t0 return A t0 with
    | Tstruct id a =>
       match Maps.PTree.get id cenv_cs with
       | None => let m := co_members (get_co id) in
                       F_Tstruct id a (hmap (fun it => A (field_type (name_member it) m))
                                     (fun it => F_ByValue (field_type (name_member it) m)) m)
       | _ => F_ByValue (Tstruct id a)
       end
    | Tunion id a =>
       match Maps.PTree.get id cenv_cs with
       | None => let m := co_members (get_co id) in
                      F_Tunion id a (hmap (fun it => A (field_type (name_member it) m))
                                     (fun it => F_ByValue (field_type (name_member it) m)) m)
       | _ => F_ByValue (Tunion id a)
       end
    | t' => F_ByValue t'
    end
  | S n' =>
    match t as t0 return A t0 with
    | Tarray t0 n a => F_Tarray t0 n a (type_func_rec n' t0)
    | Tstruct id a =>  let m := co_members (get_co id) in
                            F_Tstruct id a (hmap (fun it => A (field_type (name_member it) m))
                                        (fun it => type_func_rec n' (field_type (name_member it) m)) m)
    | Tunion id a =>  let m := co_members (get_co id) in
                            F_Tunion id a (hmap (fun it => A (field_type (name_member it) m))
                                        (fun it => type_func_rec n' (field_type (name_member it) m)) m)
    | t' => F_ByValue t'
    end
  end.

Definition type_func t := type_func_rec (rank_type cenv_cs t) t.

Lemma rank_type_Tstruct: forall id a co, Maps.PTree.get id cenv_cs = Some co ->
  rank_type cenv_cs (Tstruct id a) = S (co_rank (get_co id)).
Proof.
  intros.
  unfold get_co; simpl.
  destruct (Maps.PTree.get id cenv_cs); auto; congruence.
Defined.

Lemma rank_type_Tunion: forall id a co, Maps.PTree.get id cenv_cs = Some co ->
  rank_type cenv_cs (Tunion id a) = S (co_rank (get_co id)).
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
 (* DON'T USE lia IN THIS PROOF!
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
    destruct (Maps.PTree.get id cenv_cs) as [co |] eqn: CO.
    - erewrite rank_type_Tstruct in H by eauto.
      erewrite rank_type_Tstruct in H0 by eauto.
      clear co CO.
    destruct n; simpl in H; try solve [inv H].
    destruct n0; simpl in H; try solve [inv H0].
      simpl.
      f_equal.
      apply hmap_preserve.
      intros m Hin.
      simpl in IH.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      specialize (IH _ Hin n n0).
      apply le_S_n in H; apply le_S_n in H0.
      assert (H3 := rank_type_members cenv_cs _ _ Hin).
      pose proof get_co_members_no_replicate id.
      pose proof In_field_type _ _ H1 Hin.
      rewrite <- (co_consistent_rank cenv_cs (get_co id) (get_co_consistent _)) in H3.
      unfold field_type in H2.
      apply IH;
       (eapply le_trans; [ | eassumption]; rewrite H2; auto).
    - destruct n, n0; simpl;  unfold FT_aux in *;
      generalize (F_Tstruct id a) as FF; unfold get_co;
      rewrite CO; intros; auto.
  + (* Tunion *)
    destruct (Maps.PTree.get id cenv_cs) as [co |] eqn: CO.
    - erewrite rank_type_Tunion in H by eauto.
      erewrite rank_type_Tunion in H0 by eauto.
      clear co CO.
    destruct n; simpl in H; try solve [inv H].
    destruct n0; simpl in H; try solve [inv H0].
      simpl.
      f_equal.
      apply hmap_preserve.
      intros m Hin.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      specialize (IH _ Hin n n0).
      apply le_S_n in H; apply le_S_n in H0.
      assert (H3 := rank_type_members cenv_cs _ _ Hin).
      pose proof get_co_members_no_replicate id.
      pose proof In_field_type _ _ H1 Hin.
      rewrite <- (co_consistent_rank cenv_cs (get_co id) (get_co_consistent _)) in H3.
      apply IH;
       (eapply le_trans; [ | eassumption]; rewrite H2; auto).
    - destruct n, n0; simpl;  unfold FT_aux in *;
      generalize (F_Tunion id a) as FF; unfold get_co;
      rewrite CO; intros; auto.
Defined.

Definition FTI_aux id :=
    let m := co_members (get_co id) in
    (hmap (fun it => A (field_type (name_member it) m)) (fun it => type_func (field_type (name_member it) m)) m).

Lemma type_func_eq: forall t,
  type_func t =
  match t as t0 return A t0 with
  | Tarray t0 n a => F_Tarray t0 n a (type_func t0)
  | Tstruct id a => F_Tstruct id a (FTI_aux id)
  | Tunion id a => F_Tunion id a (FTI_aux id)
  | t' => F_ByValue t'
  end.
Proof.
  intros.
  type_induction t; try reflexivity.
  + (* Tstruct *)
    unfold type_func in *.
    simpl type_func_rec.
    destruct (Maps.PTree.get id cenv_cs) as [co |] eqn:CO; simpl.
    - f_equal.
      apply hmap_preserve; intro m.
      unfold get_co; rewrite CO.
      intro Hin.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      apply type_func_rec_rank_irrelevent.
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
    unfold type_func in *.
    simpl type_func_rec.
    destruct (Maps.PTree.get id cenv_cs) as [co |] eqn:CO; simpl.
    - f_equal.
      apply hmap_preserve; intro m.
      unfold get_co; rewrite CO.
      intro Hin.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      apply type_func_rec_rank_irrelevent.
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

Arguments type_func {cs} A F_ByValue F_Tarray F_Tstruct F_Tunion t / .

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
