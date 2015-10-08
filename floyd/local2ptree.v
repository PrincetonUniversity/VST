Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.canonicalize.

Local Open Scope logic.

Inductive vardesc : Type :=
| vardesc_local_global: type -> val -> val -> vardesc
| vardesc_local: type -> val -> vardesc
| vardesc_visible_global: val -> vardesc
| vardesc_shadowed_global: val -> vardesc.

Definition denote_vardesc {cs: compspecs} (Q: list (environ -> Prop)) (i: ident) (vd: vardesc) : list (environ -> Prop) :=
  match vd with
  |  vardesc_local_global t v v' =>  lvar i t v :: sgvar i v' :: Q
  |  vardesc_local t v => lvar i t v :: Q
  |  vardesc_visible_global v => gvar i v :: Q
  |  vardesc_shadowed_global v => sgvar i v :: Q
  end. 

Definition pTree_from_elements {A} (el: list (positive * A)) : PTree.t A :=
 fold_right (fun ia t => PTree.set (fst ia) (snd ia) t) (PTree.empty _) el.

Inductive local2ptree {cs: compspecs}:
  list (environ -> Prop) -> PTree.t val -> PTree.t vardesc
    -> list Prop -> list (environ -> Prop) -> Prop :=
  | local2ptree_nil:
      local2ptree nil (PTree.empty _) (PTree.empty _) nil nil
  | local2ptree_temp: forall v i T1' P'1 Q T1 T2 P' Q',
      local2ptree Q T1 T2 P' Q' ->
      (T1',P'1) = match T1 ! i with
                       | None => (PTree.set i v T1, P')
                       | Some v' => (T1, (v=v')::P')
                      end ->
      local2ptree (temp i v :: Q) T1' T2 P'1 Q'
  | local2ptree_lvar: forall v i t Q T2' P'1 T1 T2 P' Q',
      local2ptree Q T1 T2 P' Q' ->
      (T2', P'1) = match T2 ! i with
      | None => (PTree.set i (vardesc_local t v) T2, P')
      | Some (vardesc_local_global t' vl vg) => (T2, (vl=v)::(t'=t)::P')
      | Some (vardesc_local t' vl) => (T2, (vl=v)::(t'=t)::P')
      | Some (vardesc_visible_global vg) => (* impossible *) (T2, False :: P') 
      | Some (vardesc_shadowed_global vg) => (PTree.set i (vardesc_local_global t v vg) T2, P')
      end ->
      local2ptree (lvar i t v :: Q) T1 T2' P'1 Q'
  | local2ptree_gvar: forall v i Q T2' P'1 T1 T2 P' Q',
      local2ptree Q T1 T2 P' Q' ->
      (T2', P'1) = match T2 ! i with
      | None => (PTree.set i (vardesc_visible_global v) T2, P')
      | Some (vardesc_local_global t vl vg) => (*impossible*) (T2, False::P')
      | Some (vardesc_local t vl) => (*impossible*) (T2, False::P')
      | Some (vardesc_visible_global vg) => (T2, (vg=v)::P') 
      | Some (vardesc_shadowed_global vg) => (PTree.set i (vardesc_visible_global v) T2, (vg=v)::P')
      end ->
      local2ptree (gvar i v :: Q) T1 T2' P'1 Q'
  | local2ptree_sgvar: forall v i Q T2' P'1 T1 T2 P' Q',
      local2ptree Q T1 T2 P' Q' ->
      (T2', P'1) = match T2 ! i with
      | None => (PTree.set i (vardesc_shadowed_global v) T2, P')
      | Some (vardesc_local_global t vl vg) => (T2, (vg=v)::P')
      | Some (vardesc_local t vl) => (PTree.set i (vardesc_local_global t vl v) T2, P')
      | Some (vardesc_visible_global vg) => (T2, (vg=v)::P') 
      | Some (vardesc_shadowed_global vg) =>  (T2, (vg=v)::P') 
      end ->
      local2ptree (sgvar i v :: Q) T1 T2' P'1 Q'
  | local2ptree_unknown: forall Q0 Q T1 T2 P' Q',
      local2ptree Q T1 T2 P' Q'->
      local2ptree (Q0 :: Q) T1 T2 P' (Q0 :: Q').
(* repeat constructor will try the first succesful tactic. So local2ptree_temp_ *)
(* var, local2ptree_gl_var will be used whenever is possible before local2ptree_*)
(* unknown.                                                                     *)


Ltac prove_local2ptree :=
  match goal with |- local2ptree _ _ _ _ _ =>
    first [ solve [econstructor] 
           | econstructor ; [prove_local2ptree | reflexivity ]
           | econstructor ; [ prove_local2ptree ]
           ]
   end.

Ltac construct_local2ptree Q H :=
  let T1 := fresh "T" in evar (T1: PTree.t val);
  let T2 := fresh "T" in evar (T2: PTree.t vardesc);
  let P' := fresh "P'" in evar (P' : list Prop);
  let Q' := fresh "Q'" in evar (Q' : list (environ -> Prop));
  assert (local2ptree Q T1 T2 P' Q') as H; subst T1 T2 P' Q';
   [ prove_local2ptree | ].

Goal forall {cs: compspecs}, False.
 intros.
  construct_local2ptree (temp 1%positive Vundef :: lvar 1%positive tint (Vint (Int.repr 1)) :: 
   (`(eq 1 3)) :: nil) H.
Abort.

Definition LocalD {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (Q: list (environ -> Prop)) :=
  PTree.fold (fun Q i v => temp i v :: Q) T1
  (PTree.fold denote_vardesc T2 Q).

Lemma PTree_elements_set: forall {A} i (v: A) elm T,
  In elm (PTree.elements (PTree.set i v T)) ->
  elm = (i, v) \/ In elm (PTree.elements T).
Proof.
  intros.
  destruct elm as [i' v'].
  apply PTree.elements_complete in H.
  destruct (ident_eq i i').
  + subst.
    rewrite PTree.gss in H.
    inversion H.
    subst.
    left; auto.
  + rewrite PTree.gso in H by auto.
    right.
    apply PTree.elements_correct.
    auto.
Qed.

Lemma LocalD_sound_temp {cs: compspecs} : 
  forall i v T1 T2 Q,
  PTree.get i T1 = Some v -> In (temp i v) (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 forget (PTree.fold denote_vardesc T2 Q) as Q'.
 rewrite !PTree.fold_spec, <- !fold_left_rev_right.
 apply PTree.elements_correct in H.
 rewrite in_rev in H.
 forget (rev (PTree.elements T1)) as L.
 induction L; intros; destruct H.
 subst a. left. reflexivity.
 right. apply IHL. auto.
Qed.

Lemma LocalD_sound_local_global {cs: compspecs} : 
  forall i t v v' T1 T2 Q,
  PTree.get i T2 = Some (vardesc_local_global t v v') ->
   In (lvar i t v) (LocalD T1 T2 Q) /\ In (sgvar i v') (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 rewrite !PTree.fold_spec, <- !fold_left_rev_right.
 apply PTree.elements_correct in H.
 rewrite in_rev in H.
 forget (rev (PTree.elements T1)) as L.
 induction L; [ | split; right; apply IHL].
 forget (rev (PTree.elements T2)) as L.
 simpl.
 induction L; intros; destruct H.
 subst a.
 split.
 left; reflexivity.
 right; left; reflexivity.
 destruct (IHL H); clear IHL H.
 split; simpl.
 destruct a as [ia vda]; destruct vda; simpl in *; auto.
 destruct a as [ia vda]; destruct vda; simpl in *; auto.
Qed.

Lemma LocalD_sound_local {cs: compspecs} : 
  forall i t v T1 T2 Q,
  PTree.get i T2 = Some (vardesc_local t v) ->
   In (lvar i t v) (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 rewrite !PTree.fold_spec, <- !fold_left_rev_right.
 apply PTree.elements_correct in H.
 rewrite in_rev in H.
 forget (rev (PTree.elements T1)) as L.
 induction L; [ | right; apply IHL].
 forget (rev (PTree.elements T2)) as L.
 simpl.
 induction L; intros; destruct H.
 subst a.
 left; reflexivity.
 simpl.
 destruct a as [ia vda]; destruct vda; simpl in *; auto.
Qed.

Lemma LocalD_sound_visible_global {cs: compspecs} : 
  forall i v T1 T2 Q,
  PTree.get i T2 = Some (vardesc_visible_global v) ->
   In (gvar i v) (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 rewrite !PTree.fold_spec, <- !fold_left_rev_right.
 apply PTree.elements_correct in H.
 rewrite in_rev in H.
 forget (rev (PTree.elements T1)) as L.
 induction L; [ | right; apply IHL].
 forget (rev (PTree.elements T2)) as L.
 simpl.
 induction L; intros; destruct H.
 subst a.
 left; reflexivity.
 simpl.
 destruct a as [ia vda]; destruct vda; simpl in *; auto.
Qed.

Lemma LocalD_sound_shadowed_global{cs: compspecs} : 
  forall i v T1 T2 Q,
  PTree.get i T2 = Some (vardesc_shadowed_global v) ->
   In (sgvar i v) (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 rewrite !PTree.fold_spec, <- !fold_left_rev_right.
 apply PTree.elements_correct in H.
 rewrite in_rev in H.
 forget (rev (PTree.elements T1)) as L.
 induction L; [ | right; apply IHL].
 forget (rev (PTree.elements T2)) as L.
 simpl.
 induction L; intros; destruct H.
 subst a.
 left; reflexivity.
 simpl.
 destruct a as [ia vda]; destruct vda; simpl in *; auto.
Qed.

Lemma LocalD_sound_other {cs: compspecs} : 
  forall q T1 T2 Q,
  In q Q ->
   In q (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 rewrite !PTree.fold_spec, <- !fold_left_rev_right.
 forget (rev (PTree.elements T1)) as L.
 induction L; [ | right; apply IHL].
 forget (rev (PTree.elements T2)) as L.
 simpl.
 induction L; auto.
 simpl. 
 destruct a as [ia vda]; destruct vda; simpl in *; auto.
Qed.


Lemma LocalD_sound {cs: compspecs} : forall q T1 T2 Q,
  (exists i v, PTree.get i T1 = Some v /\ q = temp i v) \/
  (exists i t v v', PTree.get i T2 = Some (vardesc_local_global t v v') 
           /\ q = lvar i t v) \/
  (exists i t v v', PTree.get i T2 = Some (vardesc_local_global t v v') 
           /\ q = sgvar i v') \/
  (exists i t v, PTree.get i T2 = Some (vardesc_local t v) 
           /\ q = lvar i t v) \/
  (exists i v, PTree.get i T2 = Some (vardesc_visible_global v) 
           /\ q = gvar i v) \/
  (exists i v, PTree.get i T2 = Some (vardesc_shadowed_global v) 
           /\ q = sgvar i v) \/
  In q Q  ->
  In q (LocalD T1 T2 Q).
Proof.
intros.
repeat match type of H with
             | _ \/ _ => destruct H 
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst.
apply LocalD_sound_temp; auto.
apply (@LocalD_sound_local_global cs)  with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply (@LocalD_sound_local_global cs) with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply (@LocalD_sound_local cs) with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply (@LocalD_sound_visible_global cs) with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply (@LocalD_sound_shadowed_global cs)  with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply (@LocalD_sound_other cs) with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
Qed.

Lemma LocalD_complete {cs: compspecs} : forall q T1 T2 Q,
  In q (LocalD T1 T2 Q) ->
  (exists i v, PTree.get i T1 = Some v /\ q = temp i v) \/
  (exists i t v v', PTree.get i T2 = Some (vardesc_local_global t v v') 
           /\ q = lvar i t v) \/
  (exists i t v v', PTree.get i T2 = Some (vardesc_local_global t v v') 
           /\ q = sgvar i v') \/
  (exists i t v, PTree.get i T2 = Some (vardesc_local t v) 
           /\ q = lvar i t v) \/
  (exists i v, PTree.get i T2 = Some (vardesc_visible_global v) 
           /\ q = gvar i v) \/
  (exists i v, PTree.get i T2 = Some (vardesc_shadowed_global v) 
           /\ q = sgvar i v) \/
  In q Q.
Proof.
  intros.
  unfold LocalD in H.
  rewrite !PTree.fold_spec, <- !fold_left_rev_right in H.
 remember (rev (PTree.elements T1)) as L.
 simpl in H.
 change L with (nil ++ L) in HeqL.
 forget (@nil (positive * val)) as K.
 revert K HeqL; induction L; intros.
 right.
 clear K T1 HeqL.
 remember (rev (PTree.elements T2)) as L.
 simpl in H.
 change L with (nil ++ L) in HeqL.
 forget (@nil (positive * vardesc)) as K.
 revert K HeqL; induction L; intros.
 repeat right. apply H.
 assert (In a (PTree.elements T2)).
 rewrite in_rev, <- HeqL. rewrite in_app. right; left; auto.
 destruct a as [i vv].
 apply PTree.elements_complete in H0.
 destruct vv; destruct H; try subst q; eauto 50.
 destruct H; try subst q; eauto 50;
 specialize (IHL H (K ++ (i, vardesc_local_global t v v0) :: nil));
 rewrite app_ass in IHL; specialize (IHL HeqL); eauto.
 specialize (IHL H (K ++ (i, vardesc_local t v) :: nil));
 rewrite app_ass in IHL; specialize (IHL HeqL); eauto.
 specialize (IHL H (K ++ (i, vardesc_visible_global v) :: nil));
 rewrite app_ass in IHL; specialize (IHL HeqL); eauto.
 specialize (IHL H (K ++ (i, vardesc_shadowed_global v) :: nil));
 rewrite app_ass in IHL; specialize (IHL HeqL); eauto.
 destruct H.
 subst q.
 assert (In a (PTree.elements T1)).
 rewrite in_rev, <- HeqL. rewrite in_app. right; left; auto.
 destruct a as [i v]; apply PTree.elements_complete in H; eauto.
 destruct a as [i v].
 specialize (IHL H (K ++ (i,v)::nil)).
   rewrite app_ass in IHL; specialize (IHL HeqL); eauto.
Qed.
 

Lemma in_temp_aux:
  forall q L Q,
    In q (fold_right
     (fun (y : positive * val) (x : list (environ -> Prop)) =>
      temp (fst y) (snd y) :: x) Q L) <->
    ((exists i v, q = temp i v /\ In (i,v) L) \/ In q Q).
Proof.
 intros.
 induction L.
 simpl. intuition. destruct H0 as [? [? [? ?]]]. contradiction.
 intuition.
  destruct H0. simpl in *. subst q.
  left. eauto.
  specialize (H H0).
  destruct H as [[? [? [? ?]]] | ?].
  left. exists x, x0. split; auto. right; auto.
  right; auto.
  destruct H3 as [i [v [? ?]]]. destruct H3. inv H3. left. reflexivity.
  right; apply H1. eauto.
  right; auto.
  right; auto.
Qed.

Lemma LOCALx_expand_temp_var {cs: compspecs} : forall i v T1 T2 Q Q0,
  In Q0 (LocalD (PTree.set i v T1) T2 Q) <-> 
  In Q0 (temp i v :: LocalD (PTree.remove i T1) T2 Q).
Proof.
  intros; split; intros.
  + simpl.
    apply LocalD_complete in H.
    destruct H.
    - destruct H as [i0 [v0 [? ?]]].
      subst.
      destruct (ident_eq i0 i).
      * subst.
        rewrite PTree.gss in H.
        inversion H; subst.
        left; reflexivity.
      * rewrite PTree.gso in H by auto.
        right.
        apply LocalD_sound_temp.
        rewrite PTree.gro by auto. auto.
    - right.
       destruct H.
       destruct H as [j [t [v1 [v2 [? ?]]]]]; subst Q0.
       unfold LocalD.
      rewrite !PTree.fold_spec, <- !fold_left_rev_right.
      induction (rev (PTree.elements (PTree.remove i T1))); simpl.
      apply PTree.elements_correct in H. rewrite in_rev in H.
      induction  (rev (PTree.elements T2)). inv H.
      destruct H. destruct a. inv H. simpl. left; auto.
      simpl. destruct a as [? [?|?|?|?]]; simpl; repeat right; auto.
      right; apply IHl.
       destruct H.
       destruct H as [j [t [v1 [v2 [? ?]]]]]; subst Q0.
       unfold LocalD.
      rewrite !PTree.fold_spec, <- !fold_left_rev_right.
      induction (rev (PTree.elements (PTree.remove i T1))); simpl.
      apply PTree.elements_correct in H. rewrite in_rev in H.
      induction  (rev (PTree.elements T2)). inv H.
      destruct H. destruct a. inv H. simpl. right; left; auto.
      simpl. destruct a as [? [?|?|?|?]]; simpl; repeat right; auto.
      right; apply IHl.
       destruct H.
       destruct H as [j [t [v1 [? ?]]]]; subst Q0.
       unfold LocalD.
      rewrite !PTree.fold_spec, <- !fold_left_rev_right.
      induction (rev (PTree.elements (PTree.remove i T1))); simpl.
      apply PTree.elements_correct in H. rewrite in_rev in H.
      induction  (rev (PTree.elements T2)). inv H.
      destruct H. destruct a. inv H. simpl. left; auto.
      simpl. destruct a as [? [?|?|?|?]]; simpl; repeat right; auto.
      right; apply IHl.
       destruct H.
       destruct H as [j [v1 [? ?]]]; subst Q0.
       unfold LocalD.
      rewrite !PTree.fold_spec, <- !fold_left_rev_right.
      induction (rev (PTree.elements (PTree.remove i T1))); simpl.
      apply PTree.elements_correct in H. rewrite in_rev in H.
      induction  (rev (PTree.elements T2)). inv H.
      destruct H. destruct a. inv H. simpl. left; auto.
      simpl. destruct a as [? [?|?|?|?]]; simpl; repeat right; auto.
      right; apply IHl.
       destruct H.
       destruct H as [j [v1 [? ?]]]; subst Q0.
       unfold LocalD.
      rewrite !PTree.fold_spec, <- !fold_left_rev_right.
      induction (rev (PTree.elements (PTree.remove i T1))); simpl.
      apply PTree.elements_correct in H. rewrite in_rev in H.
      induction  (rev (PTree.elements T2)). inv H.
      destruct H. destruct a. inv H. simpl. left; auto.
      simpl. destruct a as [? [?|?|?|?]]; simpl; repeat right; auto.
      right; apply IHl.
       unfold LocalD.
      rewrite !PTree.fold_spec, <- !fold_left_rev_right.
      induction (rev (PTree.elements (PTree.remove i T1))); simpl.
      induction (rev (PTree.elements T2)); simpl; auto.
      destruct a as [? [?|?|?|?]]; simpl; repeat right; auto.
      auto.
  + 
     destruct H. subst.
     apply LocalD_sound_temp. apply PTree.gss.
     unfold LocalD in *.
     rewrite !PTree.fold_spec, <- !fold_left_rev_right in *.
     forget  (fold_right
            (fun (y : positive * vardesc) (x : list (environ -> Prop)) =>
             denote_vardesc x (fst y) (snd y)) Q (rev (PTree.elements T2))) as JJ.
    clear - H.
  rewrite in_temp_aux. rewrite in_temp_aux in H.
  destruct H as [[j [w [? ?]]] |?].
  left; exists j,w; split; auto.
  rewrite <- in_rev in *.
  apply PTree.elements_correct. apply PTree.elements_complete in H0.
  clear - H0.
  destruct (ident_eq i j); subst. rewrite PTree.grs in H0; inv H0.
  rewrite PTree.gro in H0 by auto. rewrite PTree.gso; auto.
 right; auto.
Qed.

Lemma denote_vardesc_prefix {cs: compspecs} :
  forall Q i vd, exists L, denote_vardesc Q i vd = L ++ Q.
Proof.
 intros; destruct vd; simpl.
  exists (lvar i t v :: sgvar i v0 :: nil); reflexivity.
  exists (lvar i t v :: nil); reflexivity.
  exists (gvar i v :: nil); reflexivity.
  exists (sgvar i v :: nil); reflexivity.
Qed.


Lemma In_LocalD_remove_set {cs: compspecs} :
   forall q T1 i vd T2 Q,
      In q (LocalD T1 (PTree.remove i T2) Q) ->
      In q (LocalD T1 (PTree.set i vd T2) Q).
Proof.
 intros.
 apply LocalD_sound.
 apply LocalD_complete in H.
    repeat match type of H with
             | _ \/ _ => destruct H 
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst.
*
 left; eauto 50.
*
 right; left. exists x,x0,x1,x2. split; auto.
 destruct (ident_eq i x). subst. rewrite PTree.grs in H; inv H.
 rewrite PTree.gro in H by auto; rewrite PTree.gso by auto; auto.
*
 right; right; left. exists x,x0,x1,x2. split; auto.
 destruct (ident_eq i x). subst. rewrite PTree.grs in H; inv H.
 rewrite PTree.gro in H by auto; rewrite PTree.gso by auto; auto.
*
 right; right; right; left. exists x,x0,x1. split; auto.
 destruct (ident_eq i x). subst. rewrite PTree.grs in H; inv H.
 rewrite PTree.gro in H by auto; rewrite PTree.gso by auto; auto.
*
 right; right; right; right; left. exists x,x0. split; auto.
 destruct (ident_eq i x). subst. rewrite PTree.grs in H; inv H.
 rewrite PTree.gro in H by auto; rewrite PTree.gso by auto; auto.
*
 right; right; right; right; right; left. exists x,x0. split; auto.
 destruct (ident_eq i x). subst. rewrite PTree.grs in H; inv H.
 rewrite PTree.gro in H by auto; rewrite PTree.gso by auto; auto.
*
 repeat right. auto.
Qed.

Lemma LOCALx_expand_vardesc {cs: compspecs} : forall i vd T1 T2 Q Q0,
  In Q0 (LocalD T1 (PTree.set i vd T2) Q) <-> 
  In Q0 (denote_vardesc (LocalD T1 (PTree.remove i T2) Q) i vd).
Proof.
  intros; split; intros.
  + simpl.
    apply LocalD_complete in H.
    repeat match type of H with
             | _ \/ _ => destruct H 
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst.
    -
      destruct vd; simpl;
      repeat right; apply LocalD_sound_temp; auto.
    -
      destruct (ident_eq i x).
      * subst x;   rewrite PTree.gss in H; inv H. simpl. auto.
      * rewrite PTree.gso in H by auto.
         destruct vd; simpl.
        repeat right. apply LocalD_sound.
        right.
        left. exists x,x0,x1,x2. rewrite PTree.gro by auto. auto.
        right.  apply LocalD_sound.
        right. left.  exists x,x0,x1,x2. rewrite PTree.gro by auto. auto.
        right.  apply LocalD_sound.
        right. left.  exists x,x0,x1,x2. rewrite PTree.gro by auto. auto.
        right.  apply LocalD_sound.
        right. left.  exists x,x0,x1,x2. rewrite PTree.gro by auto. auto.
     -
      destruct (ident_eq i x).
      * subst x;   rewrite PTree.gss in H; inv H. simpl. auto.
      * rewrite PTree.gso in H by auto.
         destruct vd; simpl.
        repeat right. apply LocalD_sound.
        right. right.
        left. exists x,x0,x1,x2. rewrite PTree.gro by auto. auto.
        right.  apply LocalD_sound.
        right; right. left.  exists x,x0,x1,x2. rewrite PTree.gro by auto. auto.
        right.  apply LocalD_sound.
        right; right. left.  exists x,x0,x1,x2. rewrite PTree.gro by auto. auto.
        right.  apply LocalD_sound.
        right; right. left.  exists x,x0,x1,x2. rewrite PTree.gro by auto. auto.
    -
      destruct (ident_eq i x).
      * subst x;   rewrite PTree.gss in H; inv H. simpl. auto.
      * rewrite PTree.gso in H by auto.
         destruct vd; simpl;
        repeat right; apply LocalD_sound;
        right; right; right;  left;
        exists x,x0,x1; rewrite PTree.gro by auto; auto.
   - 
      destruct (ident_eq i x).
      * subst x;   rewrite PTree.gss in H; inv H. simpl. auto.
      * rewrite PTree.gso in H by auto.
         destruct vd; simpl;
        repeat right; apply LocalD_sound;
        right; right; right; right;  left;
        exists x,x0; rewrite PTree.gro by auto; auto.
   - 
      destruct (ident_eq i x).
      * subst x;   rewrite PTree.gss in H; inv H. simpl. auto.
      * rewrite PTree.gso in H by auto.
         destruct vd; simpl;
        repeat right; apply LocalD_sound;
        right; right; right; right; right;  left;
        exists x,x0; rewrite PTree.gro by auto; auto.
   - 
      destruct (denote_vardesc_prefix ((LocalD T1 (PTree.remove i T2)) Q) i vd) as [L ?].
      rewrite H0. rewrite in_app; right.
      apply LocalD_sound_other. auto.
 +
   destruct vd; simpl in H; destruct H; subst.
    -
      apply LocalD_sound.
      right. left. exists i,t,v,v0; split; auto. apply PTree.gss.
   -
     destruct H; subst.
      apply LocalD_sound.
      right. right. left. exists i,t,v,v0; split; auto. apply PTree.gss.
      apply In_LocalD_remove_set; auto.
   -
      apply LocalD_sound.
      right; right; right. left. exists i,t,v; split; auto. apply PTree.gss.
   - 
      apply In_LocalD_remove_set; auto.
   - 
      apply LocalD_sound.
      right; right; right; right. left. exists i,v; split; auto. apply PTree.gss.
   -
      apply In_LocalD_remove_set; auto.
   - 
     apply LocalD_sound.
     do 5 right. left; exists i,v. split; auto. apply PTree.gss.
   - 
      apply In_LocalD_remove_set; auto.
Qed.

Lemma LOCALx_expand_res {cs: compspecs} : forall Q1 T1 T2 Q Q0,
  In Q0 (LocalD T1 T2 (Q1 ::Q)) <-> 
  In Q0 (Q1 ::LocalD T1 T2 Q).
Proof.
  intros; split; intros.
  + simpl.
    apply LocalD_complete in H.
    repeat match type of H with
             | _ \/ _ => destruct H 
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst.
    - right.
      apply LocalD_sound_temp; auto.
    - right.
      apply LocalD_sound.
      right; left; repeat econstructor; eauto.
    - 
       right.
      apply LocalD_sound.
      do 2 right; left; repeat econstructor; eauto.
    - 
       right.
      apply LocalD_sound.
      do 3 right; left; repeat econstructor; eauto.
    - 
       right.
      apply LocalD_sound.
      do 4 right; left; repeat econstructor; eauto.
    - 
       right.
      apply LocalD_sound.
      do 5 right; left; repeat econstructor; eauto.
    - 
       destruct H; auto.
       right.
      apply LocalD_sound_other. auto.
+
    destruct H. subst. apply LocalD_sound_other. left; auto.
    apply LocalD_complete in H.
    apply LocalD_sound.
    repeat match type of H with
             | _ \/ _ => destruct H 
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst.
    * do 0 right; left; repeat econstructor; eauto.
    * do 1 right; left; repeat econstructor; eauto.
    * do 2 right; left; repeat econstructor; eauto.
    * do 3 right; left; repeat econstructor; eauto.
    * do 4 right; left; repeat econstructor; eauto.
    * do 5 right; left; repeat econstructor; eauto.
    * do 6 right. right; auto.
Qed.

Lemma LOCALx_shuffle: forall P Q Q' R,
  (forall Q0, In Q0 Q' -> In Q0 Q) ->
  PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q' (SEPx R)).
Proof.
  intros.
  induction Q'; [simpl; intro; normalize; autorewrite with norm1 norm2; normalize |].
  pose proof (H a (or_introl _ eq_refl)).
  rewrite <- insert_local.
  apply andp_right.
  + clear -H0.
    induction Q; [inversion H0 |].
    rewrite <- insert_local.
    simpl in H0; inversion H0.
    - subst.
      apply andp_left1.
      apply derives_refl.
    - apply andp_left2.
      apply IHQ, H.
  + apply IHQ'.
    intros.
    apply H.
    simpl.
    right.
    apply H1.
Qed.

Lemma LOCALx_shuffle': forall P Q Q' R,
  (forall Q0, In Q0 Q' <-> In Q0 Q) ->
  PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q' (SEPx R)).
Proof.
  intros.
  apply pred_ext; apply LOCALx_shuffle; intros; apply H; auto.
Qed.

Lemma LocalD_remove_empty_from_PTree1 {cs: compspecs} : forall i T1 T2 Q Q0,
  T1 ! i = None ->
  (In Q0 (LocalD (PTree.remove i T1) T2 Q) <-> In Q0 (LocalD T1 T2 Q)).
Proof.
  intros until Q0; intro G; split; intros;
  apply LocalD_sound; apply LocalD_complete in H;
    repeat match type of H with
             | _ \/ _ => destruct H 
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst.
   - do 0 right; left. exists x,x0; split; auto.
      destruct (ident_eq i x). subst. rewrite PTree.grs in H; inv H.
      rewrite PTree.gro in H; auto.
   - do 1 right; left. repeat eexists. eauto.
   - do 2 right; left. repeat eexists. eauto.
   - do 3 right; left. repeat eexists. eauto.
   - do 4 right; left. repeat eexists. eauto.
   - do 5 right; left. repeat eexists. eauto.
   - do 6 right. auto.
   - do 0 right; left. exists x,x0; split; auto.
      destruct (ident_eq i x). subst. congruence.
      rewrite PTree.gro; auto.
   - do 1 right; left. repeat eexists. eauto.
   - do 2 right; left. repeat eexists. eauto.
   - do 3 right; left. repeat eexists. eauto.
   - do 4 right; left. repeat eexists. eauto.
   - do 5 right; left. repeat eexists. eauto.
   - do 6 right. auto.
Qed.

Lemma LocalD_remove_empty_from_PTree2{cs: compspecs} : forall i T1 T2 Q Q0,
  T2 ! i = None ->
  (In Q0 (LocalD T1 (PTree.remove i T2) Q) <-> In Q0 (LocalD T1 T2 Q)).
Proof.
  intros until Q0; intro G; split; intros;
  apply LocalD_sound; apply LocalD_complete in H;
    repeat match type of H with
             | _ \/ _ => destruct H 
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst;
   try solve [left; repeat eexists; eauto] ;
   try solve [repeat right; auto];
     try (destruct (ident_eq i x); 
           [try congruence; subst x; rewrite PTree.grs in H; inv H
           | try rewrite PTree.gro in H by auto]).
  - do 1 right; left; repeat eexists; eauto.
  - do 2 right; left; repeat eexists; eauto.
  - do 3 right; left; repeat eexists; eauto.
  - do 4 right; left; repeat eexists; eauto.
  - do 5 right; left; repeat eexists; eauto.
  - do 1 right; left; repeat eexists; rewrite PTree.gro by auto; eauto.
  - do 2 right; left; repeat eexists; rewrite PTree.gro by auto; eauto.
  - do 3 right; left; repeat eexists; rewrite PTree.gro by auto; eauto.
  - do 4 right; left; repeat eexists; rewrite PTree.gro by auto; eauto.
  - do 5 right; left; repeat eexists; rewrite PTree.gro by auto; eauto.
Qed.

Lemma subst_lvar {cs: compspecs} : forall i v j t v2,
   subst i v (lvar j t v2) = lvar j t v2.
Proof.
 intros; unfold subst, lvar.
 extensionality rho. simpl. auto.
Qed.

Lemma subst_gvar: forall i v j v1,
   subst i v (gvar j v1) = gvar j v1.
Proof.
 intros; unfold subst, gvar.
 extensionality rho. simpl. auto.
Qed.

Lemma subst_sgvar: forall i v j v1,
   subst i v (sgvar j v1) = sgvar j v1.
Proof.
 intros; unfold subst, sgvar.
 extensionality rho. simpl. auto.
Qed.

Hint Rewrite @subst_lvar subst_gvar subst_sgvar : subst.

Lemma LocalD_subst {cs: compspecs} : forall id v Q0 T1 T2 Q,
  In Q0 (LocalD (PTree.remove id T1) T2 (map (subst id v) Q)) ->
  In Q0 (map (subst id v) (LocalD T1 T2 Q)). 
Proof.
  intros.
  apply in_map_iff.
  apply LocalD_complete in H.
    repeat match type of H with
             | _ \/ _ => destruct H 
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end;
 try (destruct (peq id x);
  [subst; rewrite PTree.grs in H; inv H 
  | rewrite PTree.gro in H by auto ]).
- exists Q0; split; subst; autorewrite with subst; auto.
   apply LocalD_sound_temp; auto.
- exists Q0; split; subst; autorewrite with subst; auto.
   eapply LocalD_sound_local_global in H; destruct H; eassumption.
- exists Q0; split; subst; autorewrite with subst; auto.
   eapply LocalD_sound_local_global in H; destruct H; eassumption.
- exists Q0; split; subst; autorewrite with subst; auto.
   eapply LocalD_sound_local in H; eassumption.
- exists Q0; split; subst; autorewrite with subst; auto.
   eapply LocalD_sound_visible_global in H; eassumption.
- exists Q0; split; subst; autorewrite with subst; auto.
   eapply LocalD_sound_shadowed_global in H; eassumption.
- apply in_map_iff in H.
    destruct H as [x [?H ?H]].
    exists x.
    split; [auto |].
    apply LocalD_sound_other; auto.
Qed.

Lemma SC_remove_subst {cs: compspecs} : forall P T1 T2 R id v old,
   PROPx P
     (LOCALx (temp id v :: map (subst id `old) (LocalD T1 T2 nil))
        (SEPx (map (subst id `old) (map liftx R))))
   |-- PROPx P
         (LOCALx (LocalD (PTree.set id v T1) T2 nil) (SEPx (map liftx R))).
Proof.
  intros.
  replace (SEPx (map (subst id `old) (map liftx R))) with (SEPx (map liftx R)).
  Focus 2. {
    f_equal.
    f_equal.
    rewrite map_map.
    f_equal.
  } Unfocus.
  apply LOCALx_shuffle; intros.
  apply LOCALx_expand_temp_var in H.
  destruct H; [left; auto | right].
  apply LocalD_subst, H.
Qed.

Lemma local2ptree_sound_aux: forall P Q R Q0 Q1 Q2,
  Q1 && local Q0 = Q2 && local Q0 ->
  In Q0 Q ->
  Q1 && PROPx P (LOCALx Q (SEPx R)) = Q2 && PROPx P (LOCALx Q (SEPx R)).
Proof.
  intros.
  pose proof in_local _ P _ R H0.
  rewrite (add_andp _ _ H1).
  rewrite (andp_comm _ (local Q0)).
  rewrite <- !andp_assoc.
  f_equal.
  exact H.
Qed.

Lemma LOCALx_expand_vardesc' {cs: compspecs} : forall P R i vd T1 T2 Q,
  PROPx P (LOCALx (LocalD T1 (PTree.set i vd T2) Q) (SEPx R)) =
  PROPx P (LOCALx (denote_vardesc (LocalD T1 (PTree.remove i T2) Q) i vd) (SEPx R)).
Proof.
 intros.
 apply LOCALx_shuffle'; intro.
 symmetry; apply LOCALx_expand_vardesc.
Qed.

Lemma local_equal_lemma {cs: compspecs} :
 forall i t v t' v',
  local (lvar i t v) && local (lvar i t' v') =
  !!(v' = v) && !!(t'=t) && local (lvar i t' v').
Proof.
intros; extensionality rho.
unfold local, lift1; simpl.
normalize. f_equal. apply prop_ext.
split; intros [? ?].
hnf in H,H0.
destruct (Map.get (ve_of rho) i) as [[? ?] | ] eqn:H8; try contradiction.
destruct (eqb_type t t0) eqn:?; try contradiction.
destruct (eqb_type t' t0) eqn:?; try contradiction.
apply eqb_type_true in Heqb0.
apply eqb_type_true in Heqb1.
subst.
repeat split; auto.
hnf. rewrite H8. rewrite eqb_type_refl. auto.
destruct H0; subst; auto.
intuition.
destruct H0; subst; auto.
Qed.

Lemma local2ptree_soundness {cs: compspecs} : forall P Q R T1 T2 P' Q',
  local2ptree Q T1 T2 P' Q' ->
  PROPx P (LOCALx Q (SEPx R)) = PROPx (P' ++ P) (LOCALx (LocalD T1 T2 Q') (SEPx R)).
Proof.
  intros.
  induction H.
  + unfold LocalD.
    rewrite !PTree.fold_spec.
    simpl.
    reflexivity.
  + rewrite <- insert_local.
    rewrite IHlocal2ptree.
    rewrite insert_local.
    destruct (T1 ! i) eqn:H8; inv H0.
    Focus 2. {
    apply LOCALx_shuffle'; intros.
    eapply iff_trans; [apply LOCALx_expand_temp_var |].
    simpl.
    pose proof LocalD_remove_empty_from_PTree1 i T1 T2 Q' Q0 H8.
    tauto. } Unfocus.
    simpl app.
    rewrite <- move_prop_from_LOCAL.
    rewrite <- !insert_local.
(*    rewrite IHlocal2ptree. *)
    apply local2ptree_sound_aux with (Q0 := temp i v0).
    - extensionality rho.
      unfold temp.
      apply pred_ext; normalize.
      autorewrite with subst norm1 norm2; normalize.
      autorewrite with subst norm1 norm2; normalize.     
    - apply LocalD_sound_temp. auto.
  + rewrite <- insert_local.
    rewrite IHlocal2ptree; clear IHlocal2ptree.
    rewrite insert_local.
    destruct (T2 ! i) as [ vd |  ] eqn:H9;
    try assert (H8 := LOCALx_expand_vardesc i vd T1 T2 Q'); 
    try destruct vd; inv H0.
    -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite <- insert_local.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17, <- !insert_local, <- !andp_assoc.
     rewrite local_equal_lemma; auto.
   -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite <- insert_local.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17, <- !insert_local, <- !andp_assoc.
     rewrite local_equal_lemma; auto.
  -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite <- !insert_local.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17, <- !insert_local, <- !andp_assoc.
     f_equal.
     extensionality rho; unfold local, lift1, lvar, gvar; simpl;
     normalize.
     f_equal; apply prop_ext; intuition.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
  - 
     rewrite <- (PTree.gsident _ _ H9) at 1 by auto.
     rewrite <- !insert_local.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !insert_local, <- !andp_assoc. auto.
  - 
     rewrite <- !insert_local.
     rewrite !LOCALx_expand_vardesc'.
     unfold denote_vardesc.
     rewrite <- !insert_local.
     rewrite LOCALx_shuffle'
       with (Q:= LocalD T1 (PTree.remove i T2) Q')
              (Q':= LocalD T1 T2 Q'); auto.
    intro; symmetry; apply (LocalD_remove_empty_from_PTree2); auto.
 +
    rewrite <- insert_local.
    rewrite IHlocal2ptree; clear IHlocal2ptree.
    destruct (T2 ! i) as [ vd |  ] eqn:H9;
    try assert (H8 := LOCALx_expand_vardesc i vd T1 T2 Q'); 
    try destruct vd; inv H0.
    -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17, <- !insert_local, <- !andp_assoc.
     f_equal.
     extensionality rho; unfold local, lift1, lvar, gvar; simpl;
     normalize.
     f_equal; apply prop_ext; intuition.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
   -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17, <- !insert_local, <- !andp_assoc.
     f_equal.
     extensionality rho; unfold local, lift1, lvar, gvar; simpl;
     normalize.
     f_equal; apply prop_ext; intuition.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
  -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17, <- !insert_local, <- !andp_assoc.
     f_equal.
     extensionality rho; unfold local, lift1, lvar, gvar; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? ?].
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (ge_of rho i); intuition. subst; auto.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     subst; auto.
  - 
     rewrite <- (PTree.gsident _ _ H9) at 1 by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17,  <- !insert_local, <- !andp_assoc.
     f_equal.
     extensionality rho; unfold local, lift1, lvar, gvar, sgvar; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? ?].
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (ge_of rho i); intuition. subst; auto.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     subst; auto.
  - 
     rewrite !LOCALx_expand_vardesc'.
     unfold denote_vardesc.
     rewrite <- !insert_local.
     rewrite LOCALx_shuffle'
       with (Q:= LocalD T1 (PTree.remove i T2) Q')
              (Q':= LocalD T1 T2 Q'); auto.
    intro; symmetry; apply (LocalD_remove_empty_from_PTree2); auto.
 +
    rewrite <- insert_local.
    rewrite IHlocal2ptree; clear IHlocal2ptree.
    destruct (T2 ! i) as [ vd |  ] eqn:H9;
    try assert (H8 := LOCALx_expand_vardesc i vd T1 T2 Q'); 
    try destruct vd; inv H0.
    -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17, <- !insert_local, <- !andp_assoc.
     f_equal.
     extensionality rho; unfold local, lift1, lvar, gvar, sgvar; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? [? ?]].
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (ge_of rho i); intuition. subst; auto.
     subst.
     destruct (ge_of rho i); intuition.
   -
     rewrite <- (PTree.gsident _ _ H9) at 1 by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?canon17, <- !insert_local, <- !andp_assoc.
     f_equal.
     apply andp_comm.
  -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17, <- !insert_local, <- !andp_assoc.
     f_equal.
     extensionality rho; unfold local, lift1, lvar, gvar, sgvar; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? ?].
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (ge_of rho i); intuition. subst; auto.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (ge_of rho i); intuition. subst; auto.
  - 
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !canon17,  <- !insert_local, <- !andp_assoc.
     f_equal.
     extensionality rho; unfold local, lift1, lvar, gvar, sgvar; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? ?].
     destruct (ge_of rho i); intuition. subst; auto.
     destruct (ge_of rho i); intuition. subst; auto.
  - 
     rewrite !LOCALx_expand_vardesc'.
     unfold denote_vardesc.
     rewrite <- !insert_local.
     rewrite LOCALx_shuffle'
       with (Q:= LocalD T1 (PTree.remove i T2) Q')
              (Q':= LocalD T1 T2 Q'); auto.
    intro; symmetry; apply (LocalD_remove_empty_from_PTree2); auto.
 +
    rewrite <- !insert_local.
    rewrite IHlocal2ptree; clear IHlocal2ptree.
    rewrite insert_local.
    apply LOCALx_shuffle'; intros.
    apply LOCALx_expand_res.
Qed.

Definition eval_vardesc (ty: type) (vd: option vardesc) : option val :=
                    match  vd with
                    | Some (vardesc_local_global ty' v _) =>
                      if eqb_type ty ty'
                      then Some v
                      else None
                    | Some (vardesc_local ty' v) =>
                      if eqb_type ty ty'
                      then Some v
                      else None
                    | Some (vardesc_visible_global v) =>
                          Some v
                    | Some (vardesc_shadowed_global _) =>
                          None
                    | None => None
                    end.

Fixpoint msubst_eval_expr {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (e: Clight.expr) : option val :=
  match e with
  | Econst_int i ty => Some (Vint i)
  | Econst_long i ty => Some (Vlong i)
  | Econst_float f ty => Some (Vfloat f)
  | Econst_single f ty => Some (Vsingle f)
  | Etempvar id ty => PTree.get id T1
  | Eaddrof a ty => msubst_eval_lvalue T1 T2 a 
  | Eunop op a ty => option_map (eval_unop op (typeof a))
                                        (msubst_eval_expr T1 T2 a) 
  | Ebinop op a1 a2 ty =>
      match (msubst_eval_expr T1 T2 a1), (msubst_eval_expr T1 T2 a2) with
      | Some v1, Some v2 => Some (eval_binop op (typeof a1) (typeof a2) v1 v2) 
      | _, _ => None
      end
  | Ecast a ty => option_map (eval_cast (typeof a) ty) (msubst_eval_expr T1 T2 a)
  | Evar id ty => option_map (deref_noload ty) (eval_vardesc ty (PTree.get id T2))

  | Ederef a ty => option_map (deref_noload ty)
                              (option_map force_ptr (msubst_eval_expr T1 T2 a))
  | Efield a i ty => option_map (deref_noload ty) 
                                (option_map (eval_field (typeof a) i)
                                    (msubst_eval_lvalue T1 T2 a))
  | Esizeof t _ => Some (Vint (Int.repr (sizeof cenv_cs t)))
  | Ealignof t _ => Some (Vint (Int.repr (alignof cenv_cs t)))
  end
  with msubst_eval_lvalue {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) (e: Clight.expr) : option val := 
  match e with 
  | Evar id ty => eval_vardesc ty (PTree.get id T2)
  | Ederef a ty => option_map force_ptr (msubst_eval_expr T1 T2 a)
  | Efield a i ty => option_map (eval_field (typeof a) i)
                              (msubst_eval_lvalue T1 T2 a)
  | _  => Some Vundef
  end.

Lemma msubst_eval_expr_eq_aux:
  forall {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) e rho v,
    (forall i v, T1 ! i = Some v -> eval_id i rho = v) ->
    (forall i t v,
     eval_vardesc t T2 ! i = Some v -> eval_var i t rho = v) ->
    msubst_eval_expr T1 T2 e = Some v ->
    eval_expr e rho = v
with msubst_eval_lvalue_eq_aux: 
  forall {cs: compspecs} (T1: PTree.t val) (T2: PTree.t vardesc) e rho v,
    (forall i v, T1 ! i = Some v -> eval_id i rho = v) ->
    (forall i t v,
     eval_vardesc t T2 ! i = Some v -> eval_var i t rho = v) ->
    msubst_eval_lvalue T1 T2 e = Some v ->
    eval_lvalue e rho = v.
Proof.
  + clear msubst_eval_expr_eq_aux.
    induction e; intros; simpl in H1 |- *; try solve [inversion H1; auto].
    -
      unfold_lift; simpl.
      specialize (H0 i t);
      destruct (eval_vardesc t T2 ! i) eqn:?; inv H1.
      rewrite (H0 v0); reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
    - erewrite msubst_eval_lvalue_eq_aux; eauto.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e1) eqn:?; [| inversion H1].
      destruct (msubst_eval_expr T1 T2 e2) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe1 with (v := v0) by auto.
      rewrite IHe2 with (v := v1) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_lvalue T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      erewrite msubst_eval_lvalue_eq_aux by eauto.
      reflexivity.
  + clear msubst_eval_lvalue_eq_aux.
    induction e; intros; simpl in H1 |- *; try solve [inversion H1; auto].
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      erewrite msubst_eval_expr_eq_aux by eauto;
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_lvalue T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
Qed.

Lemma local_ext: forall Q0 Q rho, In Q0 Q -> fold_right `and `True Q rho -> Q0 rho.
Proof.
  intros.
  induction Q.
  + inversion H.
  + destruct H.
    - subst; simpl in H0; unfold_lift in H0.
      tauto.
    - apply IHQ; auto.
      unfold_lift in H0.
      unfold_lift.
      simpl in H0.
      tauto.
Qed.

Lemma msubst_eval_eq_aux {cs: compspecs}: forall T1 T2 Q rho,
  fold_right `and `True (LocalD T1 T2 Q) rho ->
  (forall i v, T1 ! i = Some v -> eval_id i rho = v) /\
  (forall i t v, eval_vardesc t (T2 ! i) = Some v ->
      eval_var i t rho = v).
Proof.
  intros; split; intros.
  + intros.
    assert (In (temp i v) (LocalD T1 T2 Q)).
      apply LocalD_sound.
      left.
      eauto.
    pose proof local_ext _ _ _ H1 H.
    unfold_lift in H2.
    auto.
  + intros.
      unfold eval_vardesc in H0.
      destruct (T2 ! i) as [ [?|?|?|?] | ] eqn:HT; simpl in *.
    -destruct (eqb_type t t0) eqn:?; inv H0.
      apply eqb_type_true in Heqb. subst t0.
      assert (In (lvar i t v) (LocalD T1 T2 Q))
        by (apply LocalD_sound; eauto 50).
      assert (H3 := local_ext _ _ _ H0 H). clear - H3.
      unfold lvar, eval_var in *.
      destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
      destruct (eqb_type t t0); try contradiction. destruct H3; auto.
     -destruct (eqb_type t t0) eqn:?; inv H0.
      apply eqb_type_true in Heqb. subst t0.
      assert (In (lvar i t v) (LocalD T1 T2 Q))
        by (apply LocalD_sound; eauto 50).
      assert (H3 := local_ext _ _ _ H0 H). clear - H3.
      unfold lvar, eval_var in *.
      destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
      destruct (eqb_type t t0); try contradiction. destruct H3; auto.
     - inv H0.
      assert (In (gvar i v) (LocalD T1 T2 Q))
        by (apply LocalD_sound; eauto 50).
      assert (H3 := local_ext _ _ _ H0 H). clear - H3.
      unfold gvar, eval_var in *.
      destruct (Map.get (ve_of rho) i) as [[? ?] | ]; try contradiction.
      destruct (ge_of rho i); try contradiction. auto.
     - inv H0.
     - inv H0.
Qed.

Lemma msubst_eval_expr_eq: forall {cs: compspecs} P T1 T2 Q R e v,
  msubst_eval_expr T1 T2 e = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_expr e)).
Proof.
  intros.
  apply andp_left2.
  apply andp_left1.
  simpl; intro rho.
  simpl in H.
  normalize; intros.
      autorewrite with subst norm1 norm2; normalize.
  destruct (msubst_eval_eq_aux _ _ _ _ H0).
  apply eq_sym, msubst_eval_expr_eq_aux with (T1 := T1) (T2 := T2); auto.
Qed.

Lemma msubst_eval_lvalue_eq: forall P {cs: compspecs} T1 T2 Q R e v,
  msubst_eval_lvalue T1 T2 e = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_lvalue e)).
Proof.
  intros.
  apply andp_left2.
  apply andp_left1.
  simpl; intro rho.
  simpl in H.
  normalize; intros.
      autorewrite with subst norm1 norm2; normalize.
  destruct (msubst_eval_eq_aux _ _ _ _ H0).
  apply eq_sym, msubst_eval_lvalue_eq_aux with (T1 := T1) (T2 := T2); auto.
Qed.

Definition localD {cs: compspecs} (temps : PTree.t val) (locals : PTree.t vardesc) :=
LocalD temps locals nil.

Definition assertD (P : list Prop) (Q : list (environ -> Prop)) (sep : list mpred) := 
PROPx P (LOCALx Q (SEPx (map (liftx) sep))).

Fixpoint explicit_cast_exprlist (et: list type) (el: list expr) {struct et} : list expr :=
 match et, el with
 | t::et', e::el' => Ecast e t :: explicit_cast_exprlist et' el'
 | _, _ => nil
 end.

Fixpoint force_list {A} (al: list (option A)) : option (list A) :=
 match al with 
 | Some a :: al' => match force_list al' with Some bl => Some (a::bl) | _ => None end
 | nil => Some nil
 | _ => None
 end.

Lemma msubst_eval_exprlist_eq:
  forall P {cs: compspecs} T1 T2 Q R tys el vl,
  force_list
           (map (msubst_eval_expr T1 T2)
              (explicit_cast_exprlist tys el)) = Some vl ->
 PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |-- 
   local (`(eq vl) (eval_exprlist tys el)).
Proof.
intros.
revert tys vl H; induction el; destruct tys, vl; intros; 
  try solve [inv H];
  try solve [go_lowerx;  apply prop_right; reflexivity].
 simpl map in H.
 unfold force_list in H; fold (@force_list val) in H.
 destruct (msubst_eval_expr T1 T2 a) eqn:?.
 simpl in H.
 destruct (force_list
        (map (msubst_eval_expr T1 T2) (explicit_cast_exprlist tys el))); inv H.
 simpl in H. inv H.
 simpl in H.
 destruct (option_map (force_val1 (sem_cast (typeof a) t))
        (msubst_eval_expr T1 T2 a)) eqn:?; inv H.
  destruct ( force_list
         (map (msubst_eval_expr T1 T2) (explicit_cast_exprlist tys el))) eqn:?; inv H1.
  specialize (IHel _ _ Heqo0).
  simpl eval_exprlist.
  destruct (msubst_eval_expr T1 T2 a) eqn:?; inv Heqo.
  apply msubst_eval_expr_eq with (P0:=P)(Q0:=Q)(R0:=R) in Heqo1.
  apply derives_trans with (local (`(eq v0) (eval_expr a)) && local (`(eq vl) (eval_exprlist tys el))).
  apply andp_right; auto.
  go_lowerx. unfold_lift. intros. apply prop_right.
  rewrite <- H. rewrite <- H0.
 auto.
Qed. 

