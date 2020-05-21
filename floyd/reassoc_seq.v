Require Import VST.floyd.base2.
Require Import VST.floyd.semax_tactics.
Import ListNotations.

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
