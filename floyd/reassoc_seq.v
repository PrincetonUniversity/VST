Require Import VST.floyd.base2.
Require Import VST.floyd.semax_tactics.
Import ListNotations.

(* Unlike unfold_Ssequence in veric/SeparationLogic.v, unfold_seq preserves Sfor and Swhile.
   In fact, it folds them even if they were not explicitly written in the input.
   Note that we don't treat Sdowhile, because there are no floyd tactics for it, and because
   it would result in 2198 cases when unfold_seq is printed. *)
Fixpoint unfold_seq c : list statement :=
  match c with
  | Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip =>
    [Swhile e s]
  | Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4) =>
    (* TODO check if this matches cases we don't want it to match and if so, check that the loop
       iteration variable of s1 is the same as in the increment in s4, but then we'll exclude
       multi-statement for loop initialisations *)
    [Sfor s1 e2 s3 s4]
  | Ssequence c1 c2 => unfold_seq c1 ++ unfold_seq c2
  | _ => [c]
  end.

Fixpoint fold_seq lc : statement :=
  match lc with
  | nil => Sskip
  | [c1] => c1
  | c :: lc0 => Ssequence c (fold_seq lc0)
  end.

Lemma flat_map_app: forall {A B: Type} (f: A -> list B) l1 l2,
  flat_map f l1 ++ flat_map f l2 = flat_map f (l1 ++ l2).
Proof.
  intros. induction l1.
  - reflexivity.
  - simpl. rewrite <- app_assoc. congruence.
Qed.

Lemma unfold_Ssequence_idempotent: forall c,
  flat_map unfold_Ssequence (unfold_Ssequence c) = unfold_Ssequence c.
Proof.
  intro c. induction c; try reflexivity.
  simpl. rewrite <- flat_map_app. congruence.
Qed.

Lemma flat_map_unfold_Ssequence_idempotent: forall ls,
  flat_map unfold_Ssequence (flat_map unfold_Ssequence ls) = flat_map unfold_Ssequence ls.
Proof.
  intro. induction ls.
  - reflexivity.
  - simpl. rewrite <- flat_map_app. f_equal; [ | assumption ].
    apply unfold_Ssequence_idempotent.
Qed.

Lemma unfold_seq_to_unfold_Ssequence: forall cs,
  unfold_Ssequence cs = flat_map unfold_Ssequence (unfold_seq cs).
Proof.
  intro cs. induction cs; try reflexivity.
  - simpl. rewrite IHcs1, IHcs2. rewrite flat_map_app.
    destruct cs2; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    destruct cs2_1; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    destruct cs2_1_1; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    destruct cs2_1_1_1; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    destruct cs2_1_1_2; try reflexivity;
    try rewrite flat_map_unfold_Ssequence_idempotent; try reflexivity.
    rewrite <- flat_map_app.
    simpl. rewrite app_nil_r. f_equal; [ symmetry; assumption | ].
    destruct cs2_2; reflexivity.
  - simpl.
    destruct cs1; try reflexivity.
    destruct cs1_1; try reflexivity.
    destruct cs1_1_1; try reflexivity.
    destruct cs1_1_2; try reflexivity.
    destruct cs2; reflexivity.
Qed.

Lemma semax_unfold_seq {Espec: OracleKind} {CS: compspecs} : forall c1 c2,
  unfold_seq c1 = unfold_seq c2 ->
  forall P Q Delta, semax Delta P c1 Q -> semax Delta P c2 Q.
Proof.
  intros. eapply semax_unfold_Ssequence; [ | eassumption ].
  do 2 rewrite unfold_seq_to_unfold_Ssequence.
  congruence.
Qed.

Ltac reassoc_seq_raw :=
  cbv [Sfor Swhile Sdowhile];
  match goal with
  | |- semax _ _ ?cs _ =>
    let cs' := eval cbv [unfold_seq fold_seq app]
               in (fold_seq (unfold_seq cs)) in
    apply (semax_unfold_seq cs' cs eq_refl)
  end.

Ltac reassoc_seq := unfold_abbrev'; reassoc_seq_raw; abbreviate_semax.

(* if size does not divide (Zlength l), the last chunk will be smaller *)
Fixpoint partition {T: Type} (firstSize size: Z) (l: list T) : list (list T) := 
  match l with
  | h :: t => if firstSize =? 0 then
      match partition (size-1) size t with
      | wip :: res => nil :: (h :: wip) :: res
      | nil => nil :: [h] :: nil
      end
    else
      match partition (firstSize-1) size t with
      | wip :: res => (h :: wip) :: res
      | nil => [h] :: nil
      end
  | nil => nil
  end.

Definition reassoc_into_chunks (cs: statement) (chunksize: Z) : statement :=
  fold_seq (map fold_seq (partition chunksize chunksize (unfold_seq cs))).

(* requires that unfold_abbrev' was already invoked *)
Ltac reassoc_seq_chunks chunksize :=
  cbv [Sfor Swhile Sdowhile];
  match goal with
  | |- semax _ _ ?cs _ => let cs' := eval cbv
       [reassoc_into_chunks fold_seq map partition unfold_seq Zlength Zlength_aux Z.succ Z.add
        Pos.add Pos.succ Pos.add_carry app Z.eqb Pos.eqb Z.sub Z.opp Z.pos_sub
        Z.succ_double Z.pred_double Z.double Pos.pred_double]
       in (reassoc_into_chunks cs chunksize)
       in apply (semax_unfold_seq cs' cs eq_refl)
  end.

(* This tactic calculates the effect of reassoc_seq, without any proofs.
  It's useful with the find_statement_in_body  tactic *)
Ltac reassociate_stmt S :=
 lazymatch S with
 | Ssequence (Ssequence ?S1 ?S2) ?S3 => 
       reassociate_stmt (Ssequence S1 (Ssequence S2 S3))
 | Ssequence ?S1 ?S2 => 
       let S1' := reassociate_stmt S1 in
       let S2' := reassociate_stmt S2 in
       let S' := constr:(Ssequence S1' S2') in
       match S1' with (Ssequence _ _) => reassociate_stmt S' | _ => S' end
 | Sloop ?S1 ?S2 => 
       let S1' := reassociate_stmt S1 in
       let S2' := reassociate_stmt S2 in
       let S' := constr:(Sloop S1' S2') in S'
 | Sifthenelse ?E ?S1 ?S2 =>
       let S1' := reassociate_stmt S1 in
       let S2' := reassociate_stmt S2 in
       let S' := constr:(Sifthenelse E S1' S2') in S'
 | Sswitch ?E ?LS =>
       let LS' := reassociate_stmt_ls LS in
       let S' := constr:(Sswitch E LS') in S'
 | _ => S
 end
with reassociate_stmt_ls LS :=
 match S with
 | LSnil => let S' := constr:(LSnil) in S'
 | LScons ?L ?S1 ?LS1 => 
       let S1' := reassociate_stmt S1 in
       let LS1' := reassociate_stmt LS1 in
       let LS' := constr:(LScons L S1' LS1') in LS'
 end.  
