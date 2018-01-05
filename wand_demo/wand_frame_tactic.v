Require Import VST.floyd.proofauto.
Require Import WandDemo.wand_frame.

Ltac pull_left_wand :=
   match goal with
   | |- ?A |-- _ =>
       match A with
       | context [?P -* ?Q] => 
           let frame := fresh "frame" in evar (frame: list mpred);
           apply derives_trans with ((P -* Q) * fold_right_sepcon frame);
           [ solve [cancel] | subst frame; unfold fold_right_sepcon; rewrite ?sepcon_emp]
       end
   end.

Ltac right_ver :=
   match goal with
   | |- (?P -* ?Q) * ?A |-- _ =>
       match A with
       | context [?Q -* ?R] =>
           let frame := fresh "frame" in evar (frame: list mpred);
           apply derives_trans with ((P -* Q) * ((Q -* R) * fold_right_sepcon frame));
           [ apply sepcon_derives; [apply derives_refl | solve [cancel]]
           | rewrite <- sepcon_assoc;
             eapply derives_trans;
             [ apply sepcon_derives; [apply wand_frame_ver | apply derives_refl]
             | subst frame; unfold fold_right_sepcon; rewrite ?sepcon_emp ]]
       end
   end.
   
Ltac left_ver :=
   match goal with
   | |- (?Q -* ?R) * ?A |-- _ =>
       match A with
       | context [?P -* ?Q] =>
           let frame := fresh "frame" in evar (frame: list mpred);
           apply derives_trans with ((Q -* R) * ((P -* Q) * fold_right_sepcon frame));
           [ apply sepcon_derives; [apply derives_refl | solve [cancel]]
           | rewrite <- sepcon_assoc;
             eapply derives_trans;
             [ apply sepcon_derives; [rewrite sepcon_comm; apply wand_frame_ver | apply derives_refl]
             | subst frame; unfold fold_right_sepcon; rewrite ?sepcon_emp ]]
       end
   end.

Ltac apply_wand_frame_ver :=
  try (
    pull_left_wand;
    repeat right_ver;
    repeat left_ver;
    match goal with
    | |- (?P -* ?Q) * ?A |-- _ =>
           let PQ := fresh "PQ" in
           set (PQ := P -* Q);
           apply_wand_frame_ver;
           subst PQ
    end).

Ltac apply_one_wand_frame_elim :=
  match goal with
  | |- (?P -* ?Q) * ?A |-- _ =>
       let frame := fresh "frame" in evar (frame: list mpred);
       apply derives_trans with (P * (P -* Q) * fold_right_sepcon frame);
       [ solve [cancel]
       | eapply derives_trans;
         [ apply sepcon_derives; [apply wand_frame_elim | apply derives_refl]
         | subst frame; unfold fold_right_sepcon; rewrite ?sepcon_emp ]]
   end.

Ltac apply_wand_frame_elim :=
  repeat (
    pull_left_wand;
    apply_one_wand_frame_elim
  ).
      
Goal forall A B C D E F G H: mpred, (B -* C) * E * (A -* B) * (F -* G) * (C -* D) * (G -* H) |-- A * F -* D * E * H.
  intros.
  apply_wand_frame_ver.
  apply -> wand_sepcon_adjoint.
  apply_wand_frame_elim.
  cancel.
Qed.
