Require Import floyd.base.
Require Import floyd.fieldlist.
Require Import floyd.computable_theorems.
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
      unfold field_type in H2.
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


(*

Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Lists.List.
Require Import VST.msl.Coqlib2.

Definition is_double (x y: nat): Prop := (S x) * 2 = (S y) \/ (S x) * 2 + 1 = (S y).

Lemma wf_double: well_founded is_double.
Proof.
  hnf; intros.
  assert (forall b, b <= a -> Acc is_double b); [| apply (H a); omega].
  induction a; intros.
  + assert (b = 0) by omega; subst.
    constructor.
    intros.
    unfold is_double in H0.
    omega.
  + constructor.
    intros.
    destruct H0.
    - apply IHa.
      omega.
    - apply IHa.
      omega.
Defined.

Definition is_double_exists: forall y, {x | is_double x (S y)}.
Proof.
  intros.
  assert ({x | is_double x (S y)} *
          {x | is_double x (S (S y))}); [| tauto].
  induction y.
  + split; [exists 0; left | exists 0; right]; auto.
  + destruct IHy as [[x1 ?] [x2 ?]].
    split; [exists x2 | exists (S x1)]; auto.
    destruct i; [left | right]; omega.
Defined.

Definition bit_type_ind: forall y, (forall x, is_double x y -> Type) -> Type.
Proof.
  intros.
  destruct y.
  + exact bool.
  + destruct (is_double_exists y) as [x H].
    exact (prod bool (X x H)).
Defined.

Definition bit_type (a: nat): Type :=
  Fix wf_double (fun _ => Type) bit_type_ind a.

Goal bit_type 0 = bool.
unfold bit_type.
unfold Fix.
unfold wf_double.
simpl.
Abort.

(*
Require Import Coq.Program.Wf.

Program Fixpoint div2 (n : nat) {measure n} : Type :=
match n with
| S (S p) => prod bool (div2 p)
| _ => bool
end.

Program Fixpoint true_div2 (n : nat) {measure n} : div2 n :=
match n as n_PAT return div2 n_PAT with
| S (S p) => (true, true_div2 p)
| _ => true
end.
*)

Definition proj1 {P Q: Prop}: P /\ Q -> P.
intros.
destruct H as [? _].
exact H.
Defined.

Definition proj2 {P Q: Prop}: P /\ Q -> Q.
intros.
destruct H as [_ ?].
exact H.
Defined.


Inductive div2R: nat -> nat -> Prop :=
  | SS: forall x, div2R x (S (S x)).

Definition wf_div2R: well_founded div2R.
Proof.
  hnf; intros.
  assert (Acc div2R a /\ Acc div2R (S a)); [| exact (proj1 H)].
  induction a.
  + split; constructor; intros.
    - inversion H.
    - inversion H.
  + split; [exact (proj2 IHa) |].
    constructor.
    intros.
    inversion H; subst.
    exact (proj1 IHa).
Defined.

Definition div2_ind: forall y, (forall x, div2R x y -> Type) -> Type.
Proof.
  intros.
  destruct y as [| [| ]].
  + exact bool.
  + exact bool.
  + specialize (X n).
    refine (prod bool (X _)).
    constructor.
Defined.

Definition div2 (n: nat) : Type :=
  Fix wf_div2R (fun _ => Type) div2_ind n.

Definition true_div2_ind: forall y, (forall x, div2R x y -> div2 x) -> div2 y.
Proof.
  intros.
  destruct y as [| [| ]].
  + exact true.
  + exact true.
  + specialize (X n).
    refine (pair true (X _)).
    constructor.
Defined.

Definition false_first (n: nat): div2 n -> div2 n :=
  match n as n_PAT return div2 n_PAT -> div2 n_PAT with
  | S (S p) => fun v => (false, snd v)
  | _ => fun _ => false
  end.
Goal div2 5 = (bool * bool)%type.
cbv.

unfold proj1.
Print div2.
Print Fix_sub.
SearchAbout Fix_sub.
Locate Fix_eq.
Print Fix_F_sub.
Print F_sub.

reflexivity.
Eval compute in (bit_type 0).
Definition all_true_ind: forall y, (forall x, is_double x y -> Type) -> Type.

Definition all_true (a: nat): bit_type a :=
  Fix wf_double (fun a => bit_type a) 
Print Fix_F.
*)