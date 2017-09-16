Require Import VST.msl.msl_standard.
Require Import VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Export VST.veric.lift.

(* This file contains two align criteria: a strong one and a weak one.
   The strong one derives alignment of types from align_memdata.
   The weak one only requires every single field to be well aligned. *)

(* Aux: relative_complete_type *)

Fixpoint relative_complete_type {A: Type} (env: PTree.t A) (t: type): bool :=
  match t with
  | Tvoid => false
  | Tint _ _ _ => true
  | Tlong _ _ => true
  | Tfloat _ _ => true
  | Tpointer _ _ => true
  | Tarray t' _ _ => relative_complete_type env t'
  | Tfunction _ _ _ => false
  | Tstruct id _ => match env ! id with
                    | Some _ => true
                    | None => false
                    end
  | Tunion id _ => match env ! id with
                   | Some _ => true
                   | None => false
                   end
  end.

Print Build_composite.
Print make_composite_env.
Print build_composite_env.
Print add_composite_definitions.
(* Aux: composite_env's PTree members reordering *)

Definition PTree_get_list {A: Type} (i: positive) (T: PTree.t (list A)): list A :=
  match PTree.get i T with
  | Some l => l
  | None => nil
  end.

Definition PTree_set_cons {A: Type} (i: positive) (a: A) (T: PTree.t (list A)) :=
  PTree.set i (a :: PTree_get_list i T) T.

Definition rebuild_composite_tree (env: composite_env): PTree.t (list (ident * composite)) :=
  fold_right (fun ic => PTree_set_cons (Pos.of_succ_nat (co_rank (snd ic))) ic) (PTree.empty _) (PTree.elements env).

Definition max_rank_composite (env: composite_env): nat :=
  fold_right (fun ic => max (co_rank (snd ic))) O (PTree.elements env).

Lemma max_rank_composite_is_upper_bound: forall env i co,
  PTree.get i env = Some co ->
  (co_rank co <= max_rank_composite env)%nat.
Proof.
  intros.
  apply PTree.elements_correct in H.
  unfold max_rank_composite.
  induction (PTree.elements env).
  + inv H.
  + destruct H.
    - subst.
      simpl.
      apply Max.le_max_l.
    - apply IHl in H.
      etransitivity; [exact H |].
      simpl.
      apply Max.le_max_r.
Qed.

(* Strong align requirement *)
Fixpoint plain_alignof (env_al: PTree.t Z) t: Z :=
  match t with
  | Tvoid
  | Tfunction _ _ _ => 1
  | Tint I8 _ _ => 1
  | Tint I16 _ _ => 2
  | Tint I32 _ _ => 4
  | Tint IBool _ _ => 1
  | Tlong _ _ => 8
  | Tfloat F32 _ => 4
  | Tfloat F64 _ => 4
  | Tpointer _ _ => 4
  | Tarray t' _ _ => plain_alignof env_al t'
  | Tstruct id _ =>
      match env_al ! id with
      | Some al => al
      | None => 1
      end
  | Tunion id _ =>
      match env_al ! id with
      | Some al => al
      | None => 1
      end
  end.

Print composite_env.
Print composite.
Print compcert.cfrontend.Ctypes.composite_env_consistent.
Print composite_consistent.
Print alignof_composite.

Fixpoint plain_alignof_composite (env_al: PTree.t Z) (m: members): Z :=
  match m with
  | nil => 1
  | (_, t) :: m' => Z.max (plain_alignof env_al t) (plain_alignof_composite env_al m')
  end.

Definition composites_plain_alignof_S (l: list (positive * composite)) (env_al: PTree.t Z) :=
  fold_right (fun ic => PTree.set (fst ic) (plain_alignof_composite env_al (co_members (snd ic)))) env_al l.

Definition composites_plain_alignof_rec (env: composite_env) T: nat -> PTree.t Z :=
  fix composites_plain_alignof_rec (n: nat): PTree.t Z :=
    match n with
    | O => PTree.empty _
    | S n' => composites_plain_alignof_S (PTree_get_list (Pos.of_succ_nat n') T) (composites_plain_alignof_rec n')
    end.

Definition composites_plain_alignof (env: composite_env): PTree.t Z :=
  let T := rebuild_composite_tree env in
  composites_plain_alignof_rec env T (S (max_rank_composite env)).

Definition consistent_plain_alignof env env_al: Prop :=
  forall i al co,
    PTree.get i env_al = Some al ->
    PTree.get i env = Some co ->
    al = plain_alignof_composite env_al (co_members co).

Lemma composites_plain_alignof_S_fact: forall l env env_al,
  consistent_plain_alignof env env_al ->
  (forall i co r list_r, In (i, co) l -> PTree.get env_al r = Some list_r ->
     In (i, co) list_r 
    
Lemma co_consistent_plain_alignof: forall env env_al,
  env_al = composites_plain_alignof env ->
  composite_env_consistent env ->
  consistent_plain_alignof env env_al.
Proof.
  intros.  
  cbv zeta beta delta [composites_plain_alignof] in H.
  set (RCT := rebuild_composite_tree env) in H.
  pose proof max_rank_composite_is_upper_bound env _ _ H2.
  apply le_lt_n_Sm in H3.
  subst env_al.
  revert i al co H1 H2 H3; induction (S (max_rank_composite env)); intros.
  + clear - H3; exfalso. omega.
  + set (CPA := composites_plain_alignof_rec env RCT n) in IHn.
    change (composites_plain_alignof_rec env RCT (S n)) with (composites_plain_alignof_S (PTree_get_list (Pos.of_succ_nat n) RCT) CPA) in H1 |- *.
















    
    Locate op

Lemma plain_alignof_spec: forall env t,
  alignof env t = align_attr (attr_of_type t) (plain_alignof env t).
Proof.
  intros.
  destruct t; auto.
Qed.

Lemma plain_alignof_two_p: forall env t, exists n,
  plain_alignof env t = two_power_nat n.
Proof.
  intros.
  destruct t as [| []  ? ? | | [] ? | | | | |];
  try solve [exists 0%nat; reflexivity | exists 1%nat; reflexivity | exists 2%nat; reflexivity].
  + simpl.
    apply alignof_two_p.
  + simpl.
    destruct (env ! i); [apply co_alignof_two_p | exists 0%nat; auto].
  + simpl.
    destruct (env ! i); [apply co_alignof_two_p | exists 0%nat; auto].
Qed.

Definition local_legal_alignas_type env (t: type): bool :=
  Z.leb (plain_alignof env t) (alignof env t) &&
  match t with
  | Tarray t' n a => Z.eqb ((sizeof env t') mod (alignof env t')) 0 && Z.leb 0 n
  | Tlong _ _ => Z.leb 8 (alignof env t)
  | _ => true
  end.

Lemma local_legal_alignas_type_spec: forall env t,
  local_legal_alignas_type env t = true ->
  (plain_alignof env t | alignof env t).
Proof.
  intros.
  apply andb_true_iff in H.
  destruct H as [? _].
  apply Zle_is_le_bool in H.
  apply power_nat_divide'; [apply alignof_two_p | apply plain_alignof_two_p | omega].
Qed.

Lemma align_chunk_alignof: forall env t ch, local_legal_alignas_type env t = true -> access_mode t = By_value ch -> (Memdata.align_chunk ch | alignof env t).
Proof.
  intros.
  destruct t; inversion H0.
  - eapply Z.divide_trans; [| apply local_legal_alignas_type_spec; auto].
    destruct i, s; inversion H2; simpl; unfold align_attr;
    destruct (attr_alignas a); reflexivity.
  - unfold local_legal_alignas_type in H.
    rewrite andb_true_iff in H; destruct H as [_ ?].
    apply Zge_is_le_bool in H.
    apply power_nat_divide' in H.
    * auto.
    * apply alignof_two_p.
    * exists 3%nat; auto.
  - eapply Z.divide_trans; [| apply local_legal_alignas_type_spec; auto].
    destruct f; inversion H2; simpl; unfold align_attr;
    destruct (attr_alignas a); reflexivity.
  - eapply Z.divide_trans; [| apply local_legal_alignas_type_spec; auto].
    inversion H2; simpl; unfold align_attr;
    destruct (attr_alignas a); reflexivity.
Qed.

Definition composite_legal_alignas (env : composite_env) (co : composite) : Prop :=
  (co_alignof co >= alignof_composite env (co_members co)).

Definition composite_env_legal_alignas env :=
  forall (id : positive) (co : composite),
    env ! id = Some co -> composite_legal_alignas env co.

