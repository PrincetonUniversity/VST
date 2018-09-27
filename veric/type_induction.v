Require Import VST.veric.base.
Require Import compcert.cfrontend.Ctypes.

Section COMPOSITE_ENV.

Context (cenv: composite_env)
        (cenv_consistent: composite_env_consistent cenv).

Lemma type_ind: forall P : type -> Prop,
  (forall t,
  match t with
  | Tarray t0 _ _ => P t0
  | Tstruct id _ 
  | Tunion id _ => match cenv ! id with
                    | Some co => Forall (Basics.compose P snd) (co_members co)
                    | _ => True
                    end
  | _ => True
  end -> P t) ->
  forall t, P t.
Proof.
  intros P IH_TYPE.
  intros.
  remember (rank_type cenv t) as n eqn: RANK'.
  assert (rank_type cenv t <= n)%nat as RANK.
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
    destruct (cenv ! i); [inv RANK | apply IH_TYPE; simpl; constructor].
  + (* Tunion level 0 *)
    simpl in RANK.
    destruct (cenv ! i); [inv RANK | apply IH_TYPE].
    simpl; constructor.
  + (* Tarray level positive *)
    simpl in RANK.
    specialize (IHn t).
    apply IH_TYPE, IHn.
    apply le_S_n; auto.
  + (* Tstruct level positive *)
    simpl in RANK.
    destruct (cenv ! i) as [co |] eqn:CO; auto.
    apply IH_TYPE; clear IH_TYPE.
    erewrite co_consistent_rank in RANK by (eapply cenv_consistent; eauto).
    clear - RANK IHn; induction (co_members co) as [| [i t] ?]; auto.
    simpl in RANK.
    pose proof Max.le_max_l (rank_type cenv t) (rank_members cenv m).
    pose proof Max.le_max_r (rank_type cenv t) (rank_members cenv m).
    constructor.
    - apply IHn; simpl; omega.
    - apply IHm; omega.
  + (* Tunion level positive *)
    simpl in RANK.
    destruct (cenv ! i) as [co |] eqn:CO; auto.
    apply IH_TYPE; clear IH_TYPE.
    erewrite co_consistent_rank in RANK by (eapply cenv_consistent; eauto).
    clear - RANK IHn; induction (co_members co) as [| [i t] ?]; auto.
    simpl in RANK.
    pose proof Max.le_max_l (rank_type cenv t) (rank_members cenv m).
    pose proof Max.le_max_r (rank_type cenv t) (rank_members cenv m).
    constructor.
    - apply IHn; simpl; omega.
    - apply IHm; omega.
Defined.

End COMPOSITE_ENV.

Ltac type_induction t cenv cenv_consistent :=
  pattern t;
  match goal with
  | |- ?P t =>
    apply (type_ind cenv cenv_consistent); clear t;
    let t := fresh "t" in
    intros t IH;
    let id := fresh "id" in
    let a := fresh "a" in
    destruct t as [| | | | | | | id a | id a]
  end.