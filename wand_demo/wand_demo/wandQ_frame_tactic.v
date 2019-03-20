Require Import VST.floyd.proofauto.
Require Import WandDemo.wand_frame.
Require Import WandDemo.wandQ_frame.

Ltac non_wandQ_sep_conjunct_rec P :=
  match P with
  | ?Q * ?R =>
    let res1 := non_wandQ_sep_conjunct_rec Q in
    match res1 with
    | Some _ => res1
    | _ => non_wandQ_sep_conjunct_rec R
    end
  | allp _ =>
    constr:(@None mpred)
  | _ => constr:(Some P)
  end.

Ltac non_wandQ_sep_conjunct P :=
  let res := non_wandQ_sep_conjunct_rec P in
  match res with
  | Some ?Q => Q
  | _ => emp
  end.

Lemma wandQ_elim_alg: forall P Q R S: mpred,
  .

Lemma wandQ_elim_alg: forall {A} (P: A -> mpred) Q RHS R a,
  P a |-- Q -* R a ->
  R a |-- RHS ->  
  allp P * Q |-- RHS.
Proof.
  intros.
  apply wand_sepcon_adjoint.
  apply allp_left with a.
  sep_apply H.
  apply wand_derives; auto.
Qed.

Ltac sep_absorb Q :=
   match goal with
   | |- ?A |-- _ =>
       match A with
       | context [allp ?P] => 
         pull_left Q;
         pull_left (allp P);
         match goal with
         | |- allp P * Q |-- _ =>
           eapply wandQ_elim_alg;
           [ apply wand_derives;
             [ solve [ecancel]
             | match goal with
               | |- ?LHS |-- _ ?a =>
                 let LHS' := eval pattern a in LHS in
                 change LHS with LHS';
                 apply derives_refl
               end
             ]
           | cbv beta ]
         end              
       end
   end.

Ltac solve_wandQ sp :=
  unfold sp;
  match goal with
  | |- _ |-- allp _ =>
    apply allp_right; intro
  | |- ?P |-- _ => let Q := non_wandQ_sep_conjunct P in sep_absorb Q
  end.



Parameter listrep: list val -> val -> mpred.

Definition lseg l p q := ALL l': list val, listrep l' q -* listrep (l ++ l') p.


Goal forall p q r l1 l2, lseg l2 q r * lseg l1 p q |-- lseg (l1 ++ l2) p r.
  intros.
  solve_wandQ lseg.
Abort.
Locate Ltac safe_unify.
Goal forall p q l1 l2, listrep l2 q * lseg l1 p q |-- listrep (l1 ++ l2) p.
  intros.
  solve_wandQ lseg.
  .
ecancel.