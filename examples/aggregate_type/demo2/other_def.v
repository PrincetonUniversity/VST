Require Import AggregateType.demo2.expr.
Require Import AggregateType.demo2.computable_theorems.

(***************************************************

1. Define two well-founded relation here and one induction principle here

***************************************************)

Module TypeTree.
Section TypeTree.

Context {cs: compspecs}.

Definition typeR (t1: type) (t2: type): Prop :=
  match t2 with
  | Tstruct sid => exists i1, In (i1, t1) (co_members (get_co sid))
  | _ => False
  end.

Lemma wf_typeR: well_founded typeR.
Proof.
  hnf; intro t.
  remember (rank_type cenv_cs t) eqn:?H.
  pose proof le_n n.
  rewrite H in H0 at 1; clear H.
  revert t H0; induction n; intros.
  + constructor; intros.
    destruct t.
    - inversion H.
    - destruct H as [yid ?].
      unfold get_co in H.
      cbv [rank_type] in H0; simpl in H0.
      destruct (Maps.PTree.get id cenv_cs) eqn:?; [inversion H0 |].
      simpl in H; inversion H.
  + constructor; intros.
    destruct t.
    - inversion H.
    - destruct H as [yid ?].
      unfold get_co in H.
      cbv [rank_type] in H0; simpl in H0.
      destruct (Maps.PTree.get id cenv_cs) eqn:?; [| inversion H].
      apply rank_type_members with (ce := cenv_cs) in H.
      pose proof co_consistent_rank _ _ (cenv_consistent id c Heqo).
      rewrite <- H1 in H.
      apply le_S_n in H0.
      apply IHn.
      apply le_trans with (co_rank c); assumption.
Defined.

End TypeTree.
End TypeTree.

Module RankLt.
Section RankLt.

Context {cs: compspecs}.

Definition typeR (t1: type) (t2: type): Prop := (rank_type cenv_cs t1 < rank_type cenv_cs t2)%nat.

Lemma wf_typeR: well_founded typeR.
Proof.
  hnf; intro t.
  remember (rank_type cenv_cs t) eqn:?H.
  pose proof le_n n.
  rewrite H in H0 at 1; clear H.
  revert t H0; induction n; intros.
  + constructor; intros.
    unfold typeR in H.
    pose proof le_trans _ _ _ H H0.
    inversion H1.
  + constructor; intros.
    destruct t.
    - inversion H.
    - unfold typeR in H.
      simpl in *.
      destruct (Maps.PTree.get id cenv_cs) eqn:?; [| inversion H].
      pose proof le_trans _ _ _ H H0.
      apply le_S_n in H1.
      apply IHn; auto.
Defined.

End RankLt.
End RankLt.

Module RankInd.
Section RankInd.

Context {cs: compspecs}.

Lemma type_ind: forall P : type -> Prop,
  (forall t,
  match t with
  | Tstruct id => let m := co_members (get_co id) in Forall (fun it => P (snd it)) m
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
    pose proof rank_type_members _ _ _ _ H0.
    eapply le_trans; [eassumption |].
    apply le_S_n; auto.
    rewrite <- co_consistent_rank; auto.
    exact (cenv_consistent id co CO).
Defined.

End RankInd.

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

End RankInd.

(***************************************************

2. Several different approaches of defining reptype.

***************************************************)

Module Fix_TypeTree.
Section Fix_TypeTree.

Context {cs: compspecs}.

Lemma typeR_spec_members_aux: forall (m : members),
  Forall (fun p : ident * type => exists i1 : ident, In (i1, snd p) m) m.
Proof.
  intros.
  induction m.
  + constructor.
  + destruct a.
    constructor.
    - exists i; left; auto.
    - revert IHm; apply Forall_impl.
      intros.
      destruct H as [i1 ?].
      exists i1.
      right; auto.
Defined.

Definition typeR_spec_members sid: Forall (fun p => TypeTree.typeR (snd p) (Tstruct sid)) (co_members (get_co sid)) :=
  typeR_spec_members_aux (co_members (get_co sid)).

Definition typeR_spec (t: type):
  match t with
  | Tint => True
  | Tstruct sid => Forall (fun p => TypeTree.typeR (snd p) t) (co_members (get_co sid))
  end :=
  match t with
  | Tint => I
  | Tstruct sid => typeR_spec_members sid
  end.

Definition reptype_fix_aux (y: type): (forall x, TypeTree.typeR x y -> Type) -> Type.
Proof.
  refine
  ((match y as y_PAT
      return match y_PAT with
             | Tint => True
             | Tstruct sid => Forall (fun p => TypeTree.typeR (snd p) y_PAT) (co_members (get_co sid))
             end ->
             (forall x : type, TypeTree.typeR x y_PAT -> Type) ->
             Type
    with
    | Tint => fun _ _ => val
    | Tstruct sid => fun H f =>
       (fix reptype_fix_aux_members (m: members): Forall (fun p => TypeTree.typeR (snd p) (Tstruct sid)) m -> Type :=
          match m as m_PAT
            return Forall (fun p => TypeTree.typeR (snd p) (Tstruct sid)) m_PAT -> Type
          with
          | nil => fun _ => unit
          | (i, t) :: m0 => fun H => prod (f t _) (reptype_fix_aux_members m0 _)
          end) _ H
    end) (typeR_spec y)).
  + apply Forall_inv in H; exact H.
  + apply Forall_inv2 in H; exact H.
Defined.

Definition reptype : type -> Type := Fix TypeTree.wf_typeR (fun _ => Type) reptype_fix_aux.

Lemma reptype_eq: forall t: type, reptype t =
  match t with
  | Tint => val
  | Tstruct id =>
      (fix reptype_members (m: members): Type :=
        match m with
        | nil => unit
        | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
        end) (co_members (get_co id))
  end.
Proof.
  intros.
  unfold reptype.
  rewrite Fix_eq.
  Focus 2. {
    intros.
    unfold reptype_fix_aux.
    destruct x; auto.
    simpl in *.
    unfold typeR_spec_members.
    generalize (typeR_spec_members_aux (co_members (get_co id))).
    revert f g H.
    (* We should be really careful that we only do induction on the occurence as m not M. *)
    set (m := co_members (get_co id)) at 5 13 21. clearbody m.
    set (M := co_members (get_co id)). clearbody M.
    intros.
    induction m as [| [i0 t0] m]; auto.
    intros.
    f_equal; auto.
  } Unfocus.
  destruct t; auto.
  unfold reptype_fix_aux at 1; simpl.
  unfold typeR_spec_members.
  generalize (typeR_spec_members_aux (co_members (get_co id))).
  (* We should be really careful that we only do induction on the occurence as m not M. *)
  set (m := co_members (get_co id)) at 2 9 10; clearbody m.
  set (M := co_members (get_co id)); clearbody M.
  induction m as [| [i0 t0] m]; auto.
  intros.
  f_equal; auto.
Qed.

Definition default_val_fix_aux (y: type): (forall x, TypeTree.typeR x y -> reptype x) -> reptype y.
Proof.
  intros.
  (* We have to use explicit type casting here because we do not want to access the intermediate function Fix_F in standard WF-recursion library. *)
  refine
   (eq_rect_r (fun T => T)
    ((match y as y_PAT
        return match y_PAT with
               | Tint => True
               | Tstruct sid => Forall (fun p => TypeTree.typeR (snd p) y_PAT) (co_members (get_co sid))
               end ->
               (forall x : type, TypeTree.typeR x y_PAT -> reptype x) ->
               match y_PAT with
               | Tint => val
               | Tstruct id =>
                   (fix reptype_members (m: members): Type :=
                     match m with
                     | nil => unit
                     | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
                     end) (co_members (get_co id))
               end
      with
      | Tint => fun _ _ => Vundef
      | Tstruct sid => fun H f =>
         (fix default_val_fix_aux_members (m: members):
            Forall (fun p => TypeTree.typeR (snd p) (Tstruct sid)) m ->
            (fix reptype_members (m: members): Type :=
                     match m with
                     | nil => unit
                     | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
                     end) m :=
            match m as m_PAT
              return Forall (fun p => TypeTree.typeR (snd p) (Tstruct sid)) m_PAT ->
                     (fix reptype_members (m: members): Type :=
                     match m with
                     | nil => unit
                     | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
                     end) m_PAT
            with
            | nil => fun _ => tt
            | (i, t) :: m0 => fun H => (f t _, default_val_fix_aux_members m0 _)
            end) _ H
      end) (typeR_spec y) X)
    (reptype_eq y)).
  + apply Forall_inv in H; exact H.
  + apply Forall_inv2 in H; exact H.
Defined.

Definition default_val: forall (t: type), reptype t := Fix TypeTree.wf_typeR reptype default_val_fix_aux.

End Fix_TypeTree.
End Fix_TypeTree.

Module Function_TypeTree.
Section Function_TypeTree.

Variable env: composite_env.
Hypothesis consist_env: composite_env_consistent env.

(* Automation system of Program Fixpoint fail to catch the correct induction principle. *)
(*
Program Fixpoint reptype (t: type) {wf (TypeTree.typeR env) t}: Type :=
  match t with
  | Tint => val
  | Tstruct id =>
      (fix reptype_members (m: members): Type :=
        match m with
        | nil => unit
        | cons (_, t0) m0 => ((reptype t0) * reptype_members m0)%type
        end) (co_members (get_co env id))
  end.
Next Obligation.
*)

(* Function keyword does not allow nested recursion. *)
(*
Function reptype (t: type) {wf (TypeTree.typeR env) t}: Type :=
  match t with
  | Tint => val
  | Tstruct id =>
      (fix reptype_members (m: members): Type :=
        match m with
        | nil => unit
        | cons (_, t0) m0 => ((reptype t0) * reptype_members m0)%type
        end) (co_members (get_co env id))
  end.
*)

End Function_TypeTree.
End Function_TypeTree.

Module ManualWf_TypeTree.

Section ManualWf_TypeTree.

Context {cs: compspecs}.

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
    ForallT_nil : ForallT P nil
  | ForallT_cons : forall (x : A) (l : list A),
                  P x -> ForallT P l -> ForallT P (x :: l).

Inductive acc_type: type -> Type :=
  | acc_Tint: acc_type Tint
  | acc_Tstruct: forall id, ForallT (fun p => acc_type (snd p)) (co_members (get_co id)) -> acc_type (Tstruct id).

Section AccTypeInd.

Variable P: forall t, acc_type t -> Prop.

Fixpoint P_members (m: members) (wit_m: ForallT (fun p => acc_type (snd p)) m): Prop :=
  match wit_m with
  | ForallT_nil => True
  | ForallT_cons (i, t) m0 wit_t wit_m0 => P t wit_t /\ P_members m0 wit_m0
  end.

Hypothesis P_Tint: P Tint acc_Tint.

Hypothesis P_Tstruct: forall sid (wit: ForallT (fun p => acc_type (snd p)) (co_members (get_co sid))), P_members (co_members (get_co sid)) wit -> P (Tstruct sid) (acc_Tstruct sid wit).

Fixpoint acc_type__ind (t: type) (wit_t: acc_type t): P t wit_t :=
  match wit_t as wit_t_PAT in acc_type t_PAT
    return P t_PAT wit_t_PAT
  with
  | acc_Tint => P_Tint
  | acc_Tstruct sid wit =>
      P_Tstruct sid wit
      ((fix acc_type_ind_members (m: members) (wit_m: ForallT (fun p => acc_type (snd p)) m): P_members m wit_m :=
        match wit_m as wit_m_PAT in ForallT _ m_PAT
          return P_members m_PAT wit_m_PAT
        with
        | ForallT_nil => I
        | ForallT_cons (i0, t0) m0 wit_t0 wit_m0 => conj (acc_type__ind t0 wit_t0) (acc_type_ind_members m0 wit_m0)
        end) (co_members (get_co sid)) wit)
  end.

End AccTypeInd.

Definition acc_type_gen (t: type): acc_type t.
  remember (rank_type cenv_cs t) eqn:?H.
  pose proof le_n n.
  rewrite H in H0 at 1; clear H.
  revert t H0; induction n; intros.
  + destruct t.
    - constructor.
    - constructor.
      unfold get_co.
      cbv [rank_type] in H0; simpl in H0.
      destruct (Maps.PTree.get id cenv_cs) eqn:?; [apply le_Sn_0 in H0; inversion H0 |].
      simpl; constructor.
  + destruct t.
    - constructor.
    - constructor; intros.
      unfold get_co.
      cbv [rank_type] in H0; simpl in H0.
      destruct (Maps.PTree.get id cenv_cs) eqn:?; [| simpl; constructor].
      pose proof co_consistent_rank _ _ (cenv_consistent id c Heqo).
      rewrite H in H0.
      apply le_S_n in H0.
      remember (co_members c) as m.
      clear c Heqo Heqm H.
      induction m; constructor.
      * destruct a; simpl in H0 |- *.
        apply IHn.
        pose proof le_max_l (rank_type cenv_cs t) (rank_members cenv_cs m).
        eapply le_trans; eassumption.
      * apply IHm.
        destruct a; simpl in H0.
        pose proof le_max_r (rank_type cenv_cs t) (rank_members cenv_cs m).
        eapply le_trans; eassumption.
Defined.

Fixpoint reptype_aux (t: type) (wit_t: acc_type t): Type :=
  match wit_t in acc_type t_PAT with
  | acc_Tint => val
  | acc_Tstruct id wit_id =>
     (fix reptype_aux_members (m: members) (wit_m: ForallT (fun p => acc_type (snd p)) m): Type :=
        match wit_m with
        | ForallT_nil => unit
        | ForallT_cons (_, t0) m0 wit_t0 wit_m0 => (reptype_aux t0 wit_t0 * reptype_aux_members m0 wit_m0)%type
        end) (co_members (get_co id)) wit_id
  end.

Definition reptype (t: type) := reptype_aux t (acc_type_gen t).

Lemma reptype_eq: forall t: type, reptype t =
  match t with
  | Tint => val
  | Tstruct id =>
      (fix reptype_members (m: members): Type :=
        match m with
        | nil => unit
        | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
        end) (co_members (get_co id))
  end.
Proof.
  intros.
  unfold reptype at 1.
  (* Because the function acc_type_gen is complicated. It is impossible to unfold it and prove by induction or case analysis on t. *)
  (* So, the only way is to prove (reptype_aux t wit1 = reptype_aux t wit2) first, which is similar to proving Fix_F_inv in the standard well-founded recursion library. Also, the proof goal will be much harder to read and operate in this specific example. *)
Abort.

Fixpoint default_val_aux (t: type) (wit_t: acc_type t): reptype_aux t wit_t :=
  match wit_t as wit_t_PAT in acc_type t_PAT return reptype_aux t_PAT wit_t_PAT with
  | acc_Tint => Vundef
  | acc_Tstruct id wit_id =>
     (fix default_val_aux_members (m: members) (wit_m: ForallT (fun p => acc_type (snd p)) m):
        (fix reptype_aux_members (m: members) (wit_m: ForallT (fun p => acc_type (snd p)) m): Type :=
        match wit_m with
        | ForallT_nil => unit
        | ForallT_cons (_, t0) m0 wit_t0 wit_m0 => (reptype_aux t0 wit_t0 * reptype_aux_members m0 wit_m0)%type
        end) m wit_m :=
        match wit_m  as wit_m_PAT in (ForallT _ m_PAT) return (fix reptype_aux_members (m: members) (wit_m: ForallT (fun p => acc_type (snd p)) m): Type :=
        match wit_m with
        | ForallT_nil => unit
        | ForallT_cons (_, t0) m0 wit_t0 wit_m0 => (reptype_aux t0 wit_t0 * reptype_aux_members m0 wit_m0)%type
        end) m_PAT wit_m_PAT with
        | ForallT_nil => tt
        | ForallT_cons (_, t0) m0 wit_t0 wit_m0 => (default_val_aux t0 wit_t0, default_val_aux_members m0 wit_m0)%type
        end) (co_members (get_co id)) wit_id
  end.

Definition default_val (t: type): reptype t := default_val_aux t (acc_type_gen t).

End ManualWf_TypeTree.

End ManualWf_TypeTree.

Module Fix_RankLt.

Section Fix_RankLt.

Context {cs: compspecs}.

Definition typeR (t1: type) (t2: type): Prop := (rank_type cenv_cs t1 < rank_type cenv_cs t2)%nat.

Lemma wf_typeR: well_founded typeR.
Proof.
  hnf; intro t.
  remember (rank_type cenv_cs t) eqn:?H.
  pose proof le_n n.
  rewrite H in H0 at 1; clear H.
  revert t H0; induction n; intros.
  + constructor; intros.
    unfold typeR in H.
    pose proof le_trans _ _ _ H H0.
    inversion H1.
  + constructor; intros.
    destruct t.
    - inversion H.
    - unfold typeR in H.
      simpl in *.
      destruct (Maps.PTree.get id cenv_cs) eqn:?; [| inversion H].
      pose proof le_trans _ _ _ H H0.
      apply le_S_n in H1.
      apply IHn; auto.
Defined.

Lemma typeR_spec_members_aux: forall (m : members),
  Forall (fun p : ident * type => rank_type cenv_cs (snd p) < S (rank_members cenv_cs m))%nat m.
Proof.
  intros.
  induction m.
  + constructor.
  + destruct a.
    constructor.
    - simpl.
      apply le_n_S.
      apply le_max_l.
    - revert IHm; apply Forall_impl.
      intros.
      apply (le_trans _ _ _ H).
      simpl.
      apply le_n_S.
      apply le_max_r.
Defined.

Lemma typeR_spec_members sid: Forall (fun p => typeR (snd p) (Tstruct sid)) (co_members (get_co sid)).
Proof.
  unfold typeR.
  simpl.
  unfold get_co.
  destruct (Maps.PTree.get sid cenv_cs) eqn:?.
  + erewrite co_consistent_rank by (eapply (cenv_consistent _ _ Heqo)).
    apply typeR_spec_members_aux.
  + constructor.
Defined.

Definition typeR_spec (t: type):
  match t with
  | Tint => True
  | Tstruct sid => Forall (fun p => typeR (snd p) t) (co_members (get_co sid))
  end :=
  match t with
  | Tint => I
  | Tstruct sid => typeR_spec_members sid
  end.

Definition reptype_fix_aux (y: type): (forall x, typeR x y -> Type) -> Type.
Proof.
  refine
  ((match y as y_PAT
      return match y_PAT with
             | Tint => True
             | Tstruct sid => Forall (fun p => typeR (snd p) y_PAT) (co_members (get_co sid))
             end ->
             (forall x : type, typeR x y_PAT -> Type) ->
             Type
    with
    | Tint => fun _ _ => val
    | Tstruct sid => fun H f =>
       (fix reptype_fix_aux_members (m: members): Forall (fun p => typeR (snd p) (Tstruct sid)) m -> Type :=
          match m as m_PAT
            return Forall (fun p => typeR (snd p) (Tstruct sid)) m_PAT -> Type
          with
          | nil => fun _ => unit
          | (i, t) :: m0 => fun H => prod (f t _) (reptype_fix_aux_members m0 _)
          end) _ H
    end) (typeR_spec y)).
  + apply Forall_inv in H; exact H.
  + apply Forall_inv2 in H; exact H.
Defined.

Definition reptype : type -> Type := Fix wf_typeR (fun _ => Type) reptype_fix_aux.

Lemma reptype_eq: forall t: type, reptype t =
  match t with
  | Tint => val
  | Tstruct id =>
      (fix reptype_members (m: members): Type :=
        match m with
        | nil => unit
        | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
        end) (co_members (get_co id))
  end.
Proof.
  intros.
  unfold reptype.
  rewrite Fix_eq.
  Focus 2. {
    intros.
    unfold reptype_fix_aux.
    destruct x; auto.
    simpl in *.
    (* We should be careful not to unfold this proof at all. *)
    generalize (typeR_spec_members id).
    revert f g H.
    unfold typeR, get_co; simpl.
    destruct (Maps.PTree.get id cenv_cs) eqn:?; [| auto].
    set (m := (co_members c)). clearbody m.
    intros.
    induction m as [| [i0 t0] m]; auto.
    intros.
    f_equal; auto.
  } Unfocus.
  destruct t; auto.
  unfold reptype_fix_aux at 1; simpl.
  (* We should be careful not to unfold this proof at all. *)
  generalize (typeR_spec_members id).
  unfold typeR, get_co; simpl.
  destruct (Maps.PTree.get id cenv_cs) eqn:?; [| auto].
  set (m := (co_members c)). clearbody m.
  intros.
  induction m as [| [i0 t0] m]; auto.
  intros.
  f_equal; auto.
Qed.

Definition default_val_fix_aux (y: type): (forall x, typeR x y -> reptype x) -> reptype y.
Proof.
  intros.
  (* We have to use explicit type casting here because we do not want to access the intermediate function Fix_F in standard WF-recursion library. *)
  refine
   (eq_rect_r (fun T => T)
    ((match y as y_PAT
        return match y_PAT with
               | Tint => True
               | Tstruct sid => Forall (fun p => typeR (snd p) y_PAT) (co_members (get_co sid))
               end ->
               (forall x : type, typeR x y_PAT -> reptype x) ->
               match y_PAT with
               | Tint => val
               | Tstruct id =>
                   (fix reptype_members (m: members): Type :=
                     match m with
                     | nil => unit
                     | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
                     end) (co_members (get_co id))
               end
      with
      | Tint => fun _ _ => Vundef
      | Tstruct sid => fun H f =>
         (fix default_val_fix_aux_members (m: members):
            Forall (fun p => typeR (snd p) (Tstruct sid)) m ->
            (fix reptype_members (m: members): Type :=
                     match m with
                     | nil => unit
                     | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
                     end) m :=
            match m as m_PAT
              return Forall (fun p => typeR (snd p) (Tstruct sid)) m_PAT ->
                     (fix reptype_members (m: members): Type :=
                     match m with
                     | nil => unit
                     | cons (_, t0) m0 => (reptype t0 * reptype_members m0)%type
                     end) m_PAT
            with
            | nil => fun _ => tt
            | (i, t) :: m0 => fun H => (f t _, default_val_fix_aux_members m0 _)
            end) _ H
      end) (typeR_spec y) X)
    (reptype_eq y)).
  + apply Forall_inv in H; exact H.
  + apply Forall_inv2 in H; exact H.
Defined.

Definition default_val: forall (t: type), reptype t := Fix wf_typeR reptype default_val_fix_aux.

End Fix_RankLt.

End Fix_RankLt.

(***************************************************

3. Directly define reptype recursive on rank

***************************************************)

Module RankRec.

Require Import AggregateType.demo2.type_induction.
Open Scope nat.

Section RankRec.

Context {cs: compspecs}.

Fixpoint reptype_aux (n: nat) (t: type): Type :=
  match t with
  | Tint => val
  | Tstruct id =>
     match n with
     | O => unit
     | S n' => fold_right prod unit (map (reptype_aux n') (map snd (co_members (get_co id))))
     end
  end.

Definition reptype t := reptype_aux (rank_type cenv_cs t) t.

Lemma reptype_aux_rank_irrelevent: forall t n n0,
  n >= rank_type cenv_cs t ->
  n0 >= rank_type cenv_cs t ->
  reptype_aux n t = reptype_aux n0 t.
Proof.
  intros t.
  RankInd.type_induction t;
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
      rewrite !map_map.
      apply list_map_exten.

      intros [i t] Hin.
      unfold get_co in H, H0, Hin. rewrite CO in H, H0, Hin.
      simpl in IH.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      specialize (IH (i, t) Hin n n0).
      apply le_S_n in H; apply le_S_n in H0.
      assert (H3 := rank_type_members cenv_cs i t _ Hin).
      symmetry; apply IH.
      * simpl.
        eapply le_trans; [ | eassumption].
        erewrite co_consistent_rank; [eapply rank_type_members; eassumption |].
        exact (cenv_consistent id co CO).
      * simpl.
        eapply le_trans; [ | eassumption].
        erewrite co_consistent_rank; [eapply rank_type_members; eassumption |].
        exact (cenv_consistent id co CO).
    - destruct n, n0; simpl;
      unfold get_co;
      rewrite ?CO; intros; auto.
Defined.

Lemma reptype_eq: forall t: type, reptype t =
  match t with
  | Tint => val
  | Tstruct id => fold_right prod unit (map reptype (map snd (co_members (get_co id))))
  end.
Proof.
  intros.
  RankInd.type_induction t; try reflexivity.
  + (* Tstruct *)
    unfold reptype in *.
    simpl reptype_aux.
    destruct (Maps.PTree.get id cenv_cs) as [co |] eqn:CO; simpl.
    - f_equal.
      rewrite !map_map.
      apply list_map_exten.
      intros [i t].
      unfold get_co; rewrite CO.
      intro Hin.
      generalize (Forall_forall1 _ _ IH); clear IH; intro IH.
      apply reptype_aux_rank_irrelevent.
      * apply le_n.
      * simpl.
        erewrite co_consistent_rank; [eapply rank_type_members; eassumption |].
        exact (cenv_consistent id co CO).
    - unfold FTI_aux, get_co; rewrite CO.
      reflexivity.
Defined.

End RankRec.
End RankRec.

Module Test.

Require Import compcert.lib.Maps.

Definition _f1 := 1%positive.
Definition _f2 := 2%positive.
Definition _f3 := 3%positive.
Definition _f4 := 4%positive.
Definition _f5 := 5%positive.
Definition cd1 := Build_composite ((_f1, Tint) :: (_f2%positive, Tint) :: nil) 0.
Definition cd2 := Build_composite ((_f3, Tstruct 101%positive) ::
                                   (_f4, Tstruct 101%positive) ::
                                   (_f5, Tint) :: nil) 1.

Definition cenv : composite_env.
  pose (PTree.set 102%positive cd2 (PTree.set 101%positive cd1 (PTree.empty _))).
  cbv - [cd1 cd2] in t.
  match goal with
  | _ := ?t |- _ => clear; exact t
  end.
Defined.

Definition cenv_cons: composite_env_consistent cenv.
  hnf.
  intros.
  apply PTree.elements_correct in H.
  simpl in H.
  destruct H as [| [|[]]]; inversion H; subst.
  + split; reflexivity.
  + split; reflexivity.
Defined.

Instance test_cs: compspecs := mkcompspecs cenv cenv_cons.

Goal Fix_TypeTree.reptype (Tstruct 101%positive) = (val * (val * unit))%type.
  reflexivity.
Qed.

Goal Fix_TypeTree.reptype (Tstruct 102%positive) = ((val * (val * unit)) * ((val * (val * unit)) * (val * unit)))%type.
  reflexivity.
Qed.

Goal ManualWf_TypeTree.reptype (Tstruct 101%positive) = (val * (val * unit))%type.
  reflexivity.
Qed.

Goal ManualWf_TypeTree.reptype (Tstruct 102%positive) = ((val * (val * unit)) * ((val * (val * unit)) * (val * unit)))%type.
  reflexivity.
Qed.

Goal Fix_RankLt.reptype (Tstruct 101%positive) = (val * (val * unit))%type.
  reflexivity.
Qed.

Goal Fix_RankLt.reptype (Tstruct 102%positive) = ((val * (val * unit)) * ((val * (val * unit)) * (val * unit)))%type.
  reflexivity.
Qed.

Goal RankRec.reptype (Tstruct 101%positive) = (val * (val * unit))%type.
  reflexivity.
Qed.

Goal RankRec.reptype (Tstruct 102%positive) = ((val * (val * unit)) * ((val * (val * unit)) * (val * unit)))%type.
  reflexivity.
Qed.

End Test.

