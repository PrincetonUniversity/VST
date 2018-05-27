Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.

Local Open Scope logic.

Inductive vardesc : Type :=
| vardesc_local_global: type -> val -> val -> vardesc
| vardesc_local: type -> val -> vardesc
| vardesc_visible_global: val -> vardesc
| vardesc_shadowed_global: val -> vardesc.

Definition denote_vardesc (Q: list localdef) (i: ident) (vd: vardesc) : list localdef :=
  match vd with
  |  vardesc_local_global t v v' =>  lvar i t v :: sgvar i v' :: Q
  |  vardesc_local t v => lvar i t v :: Q
  |  vardesc_visible_global v => gvar i v :: Q
  |  vardesc_shadowed_global v => sgvar i v :: Q
  end.

Definition pTree_from_elements {A} (el: list (positive * A)) : PTree.t A :=
 fold_right (fun ia t => PTree.set (fst ia) (snd ia) t) (PTree.empty _) el.

Definition local_trees :=
   (PTree.t val * PTree.t vardesc * list Prop * list localdef)%type.

Definition local2ptree1 (Q: localdef)
   (T1: PTree.t val) (T2: PTree.t vardesc) (P': list Prop) (Q': list localdef)
   (f:  PTree.t val -> PTree.t vardesc -> list Prop -> list localdef ->
     local_trees)
   : local_trees :=
match Q with
| temp i v =>  match T1 ! i with
                       | None => f (PTree.set i v T1) T2 P' Q'
                       | Some v' => f T1 T2 ((v=v')::P')  Q'
                      end
| lvar i t v => match T2 ! i with
      | None => f T1 (PTree.set i (vardesc_local t v) T2) P' Q'
      | Some (vardesc_local_global t' vl vg) => f T1 T2 ((vl=v)::(t'=t)::P') Q'
      | Some (vardesc_local t' vl) => f T1 T2 ((vl=v)::(t'=t)::P') Q'
      | Some (vardesc_visible_global vg) => (* impossible *) f T1 T2 (False :: P') Q'
      | Some (vardesc_shadowed_global vg) =>
               f T1 (PTree.set i (vardesc_local_global t v vg) T2) P' Q'
      end
| gvar i v => match T2 ! i with
      | None => f T1 (PTree.set i (vardesc_visible_global v) T2) P' Q'
      | Some (vardesc_local_global t vl vg) => (*impossible*) f T1 T2 (False::P') Q'
      | Some (vardesc_local t vl) => (*impossible*) f T1 T2 (False::P') Q'
      | Some (vardesc_visible_global vg) => f T1 T2  ((vg=v)::P') Q'
      | Some (vardesc_shadowed_global vg) => f T1 (PTree.set i (vardesc_visible_global v) T2) ((vg=v)::P') Q'
      end
| sgvar i v => match T2 ! i with
      | None => f T1 (PTree.set i (vardesc_shadowed_global v) T2) P' Q'
      | Some (vardesc_local_global t vl vg) => f T1 T2 ((vg=v)::P') Q'
      | Some (vardesc_local t vl) => f T1 (PTree.set i (vardesc_local_global t vl v) T2) P' Q'
      | Some (vardesc_visible_global vg) => f T1 T2 ((vg=v)::P') Q'
      | Some (vardesc_shadowed_global vg) =>  f T1 T2 ((vg=v)::P') Q'
      end
(*| tc_env D => f T1 T2 P' (tc_env D :: Q') *)
| localprop P => f T1 T2 (P :: P') Q'
| gvars gv => f T1 T2 P' (gvars gv :: Q')
end.

Fixpoint local2ptree_aux (Q: list localdef)
   (T1: PTree.t val) (T2: PTree.t vardesc) (P': list Prop) (Q': list localdef):
   local_trees :=
match Q with
| Q1 :: Qr => local2ptree1 Q1 T1 T2 P' Q' (local2ptree_aux Qr)
| nil => (T1,T2,P',Q')
end.

Definition local2ptree (Q: list localdef)
     : (PTree.t val * PTree.t vardesc * list Prop * list localdef ) :=
local2ptree_aux Q PTree.Leaf PTree.Leaf nil nil.

Definition CLEAR_ME {T} (x:T) := x.
Ltac hide_it z := let x := fresh "x" in set (x:=z); change z with (CLEAR_ME z) in x.

Ltac hnf_localdef_list A :=
  match A with
 | temp _ ?v :: ?Q' => hide_it v; hnf_localdef_list Q'
 | lvar _ ?t ?v :: ?Q' => hide_it t; hide_it v; hnf_localdef_list Q'
 | gvar _ ?v :: ?Q' => hide_it v; hnf_localdef_list Q'
 | sgvar _ ?v :: ?Q' => hide_it v; hnf_localdef_list Q'
 | localprop ?v :: ?Q' => hide_it v; hnf_localdef_list Q'
 | gvars ?v :: ?Q' => hide_it v; hnf_localdef_list Q'
(* | tc_env ?v :: ?Q' => hide_it v;  hnf_localdef_list Q'      *)
  | ?B :: ?C => let x := eval hnf in B in change B with x; hnf_localdef_list (x::C)
  | nil => idtac
  | _ => try (is_evar A; fail 1);
            let x := eval hnf in A in (change A with x); hnf_localdef_list x
  end.

Ltac grab_gvars L := 
 match L with gvars ?A :: ?B => let x := grab_gvars B in let z := constr:(A::x) in z
                | nil => let x := constr:(@nil globals) in x
  end.

Ltac prove_local2ptree :=
 clear;
 match goal with |- local2ptree ?A = _ => hnf_localdef_list A end;
 etransitivity;
 [unfold local2ptree, local2ptree_aux; simpl;
  repeat match goal with x := CLEAR_ME _ |- _ => unfold CLEAR_ME in x; subst x end;
  reflexivity |
  repeat match goal with x := CLEAR_ME _ |- _ => unfold CLEAR_ME in x; subst x end;
  apply f_equal;
  try reflexivity;
  match goal with |- ?L = _ => let x := grab_gvars L in instantiate(1:=x); reflexivity end
 ].

Goal exists x,  local2ptree (
      temp 1%positive Vundef
   :: temp 3%positive (Vint (Int.repr (3+4)))
   :: lvar 1%positive tint (Vint (Int.repr 1))
   :: localprop(eq (1+2) 3)
(*   :: tc_env empty_tycontext*)
   :: nil) = x.
set (Three := 3). (* This definition should not be unfolded! *)
set (T := temp 1%positive Vundef). (* This should be unfolded! *)
set (Q := (*tc_env empty_tycontext :: *) nil).  (* This should be unfolded! *)
eexists.
etransitivity.
prove_local2ptree.
match goal with |- context [1+2] => idtac end.
match goal with |- context [Three] => idtac end.
Abort.

Ltac construct_local2ptree Q H :=
  let t := fresh "t" in
  evar (t: (PTree.t val * PTree.t vardesc * list Prop * list localdef)%type);
  assert (H: local2ptree Q = t); subst t;
   [ prove_local2ptree | ].

Goal False.
  construct_local2ptree (temp 1%positive Vundef :: lvar 1%positive tint (Vint (Int.repr 1)) ::
   (localprop(eq (1+2) 3)) :: nil) H.
Abort.

Definition LocalD (T1: PTree.t val) (T2: PTree.t vardesc) (Q: list localdef) :=
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

Lemma LocalD_sound_temp:
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

Lemma LocalD_sound_local_global  :
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

Lemma LocalD_sound_local:
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

Lemma LocalD_sound_visible_global :
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

Lemma LocalD_sound_shadowed_global:
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

Lemma LocalD_sound_other:
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


Lemma LocalD_sound: forall q T1 T2 Q,
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
apply LocalD_sound_local_global  with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply LocalD_sound_local_global with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply LocalD_sound_local with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply LocalD_sound_visible_global with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply LocalD_sound_shadowed_global  with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply LocalD_sound_other with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
Qed.

Lemma LocalD_complete : forall q T1 T2 Q,
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
     (fun (y : positive * val) (x : list localdef) =>
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

Lemma LOCALx_expand_temp_var  : forall i v T1 T2 Q Q0,
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
            (fun (y : positive * vardesc) (x : list localdef) =>
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

Lemma denote_vardesc_prefix :
  forall Q i vd, exists L, denote_vardesc Q i vd = L ++ Q.
Proof.
 intros; destruct vd; simpl.
  exists (lvar i t v :: sgvar i v0 :: nil); reflexivity.
  exists (lvar i t v :: nil); reflexivity.
  exists (gvar i v :: nil); reflexivity.
  exists (sgvar i v :: nil); reflexivity.
Qed.


Lemma In_LocalD_remove_set :
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

Lemma LOCALx_expand_vardesc : forall i vd T1 T2 Q Q0,
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

Lemma LOCALx_expand_res: forall Q1 T1 T2 Q Q0,
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

Lemma LOCALx_shuffle_derives': forall P Q Q' R,
  (forall Q0, In Q0 Q' -> In Q0 Q) ->
  PROPx P (LOCALx Q R) |-- PROPx P (LOCALx Q' R).
Proof.
  intros.
  induction Q'.
  Focus 1. {
    unfold PROPx, LOCALx.
    normalize.
    apply andp_left2; auto.
  } Unfocus.
  pose proof (H a (or_introl _ eq_refl)).
  rewrite <- insert_local'.
  apply andp_right.
  + clear -H0.
    induction Q; [inversion H0 |].
    rewrite <- insert_local'.
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

Lemma LOCALx_shuffle_derives: forall P Q Q' R,
  (forall Q0, In Q0 Q' -> In Q0 Q) ->
  PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q' (SEPx R)).
Proof. intros. apply LOCALx_shuffle_derives'. auto. Qed.

Lemma LOCALx_shuffle': forall P Q Q' R,
  (forall Q0, In Q0 Q' <-> In Q0 Q) ->
  PROPx P (LOCALx Q R) = PROPx P (LOCALx Q' R).
Proof.
  intros.
  apply pred_ext; apply LOCALx_shuffle_derives'; intros; apply H; auto.
Qed.

Lemma LOCALx_shuffle: forall P Q Q' R,
  (forall Q0, In Q0 Q' <-> In Q0 Q) ->
  PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q' (SEPx R)).
Proof.
  intros.
  apply pred_ext; apply LOCALx_shuffle_derives; intros; apply H; auto.
Qed.

Lemma LocalD_remove_empty_from_PTree1: forall i T1 T2 Q Q0,
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

Lemma LocalD_remove_empty_from_PTree2: forall i T1 T2 Q Q0,
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

Lemma nth_error_local':
  forall n P Q R (Qn: localdef),
    nth_error Q n = Some Qn ->
    PROPx P (LOCALx Q R) |-- local (locald_denote Qn).
Proof.
intros.
apply andp_left2. apply andp_left1.
go_lowerx. normalize.
revert Q H H0; induction n; destruct Q; intros; inv H.
destruct H0; auto.
destruct H0. apply (IHn Q); auto.
Qed.

Lemma in_local': forall Q0 P Q R, In Q0 Q ->
   PROPx P (LOCALx Q R) |-- local (locald_denote Q0).
Proof.
  intros.
  destruct (in_nth_error _ _ H) as [?n ?H].
  eapply nth_error_local'.
  eauto.
Qed.

Lemma local2ptree_sound_aux: forall P Q R Q0 Q1 Q2,
  Q1 && local (locald_denote Q0) = Q2 && local (locald_denote Q0) ->
  In Q0 Q ->
  Q1 && PROPx P (LOCALx Q R) = Q2 && PROPx P (LOCALx Q R).
Proof.
  intros.
  pose proof in_local' _ P _ R H0.
  rewrite (add_andp _ _ H1).
  rewrite (andp_comm _ (local (locald_denote Q0))).
  rewrite <- !andp_assoc.
  f_equal.
  exact H.
Qed.

Lemma LOCALx_expand_vardesc': forall P R i vd T1 T2 Q,
  PROPx P (LOCALx (LocalD T1 (PTree.set i vd T2) Q) R) =
  PROPx P (LOCALx (denote_vardesc (LocalD T1 (PTree.remove i T2) Q) i vd) R).
Proof.
 intros.
 apply LOCALx_shuffle'; intro.
 symmetry; apply LOCALx_expand_vardesc.
Qed.

Lemma local_equal_lemma :
 forall i t v t' v',
  local (locald_denote (lvar i t v)) && local (locald_denote (lvar i t' v')) =
  !!(v' = v) && !!(t'=t) && local (locald_denote (lvar i t' v')).
Proof.
intros; extensionality rho.
unfold local, lift1; simpl.
normalize. f_equal. apply prop_ext.
unfold lvar_denote.
split; intros [? ?].
hnf in H,H0.
destruct (Map.get (ve_of rho) i) as [[? ?] | ] eqn:H8; try contradiction.
destruct H, H0; subst.
repeat split; auto.
destruct (Map.get (ve_of rho) i) as [[? ?] | ] eqn:H8; try contradiction.
destruct H0 as [[? ?] ?]; subst. subst. repeat split; auto.
destruct H0; contradiction.
Qed.

Lemma insert_locals:
  forall P A B C,
  local (fold_right `(and) `(True) (map locald_denote A)) && PROPx P (LOCALx B C) =
  PROPx P (LOCALx (A++B) C).
Proof.
intros.
induction A.
extensionality rho; simpl. unfold local, lift1. rewrite prop_true_andp by auto.
auto.
simpl app. rewrite <- (insert_local' a).
rewrite <- IHA.
rewrite <- andp_assoc.
f_equal.
extensionality rho; simpl; unfold_lift; unfold local, lift1; simpl.
normalize.
Qed.

Lemma LOCALx_app_swap:
  forall A B, LOCALx (A++B) = LOCALx (B++A).
Proof.
intros.
extensionality R rho; unfold LOCALx.
simpl andp. cbv beta. f_equal.
rewrite !map_app.
simpl map. unfold local,lift1. f_equal.
rewrite !fold_right_and_app.
apply prop_ext; intuition.
Qed.

Lemma local2ptree_soundness' : forall P Q R T1a T2a Pa Qa T1 T2 P' Q',
  local2ptree_aux Q T1a T2a Pa Qa = (T1, T2, P', Q') ->
  PROPx (Pa++P) (LOCALx (Q ++ LocalD T1a T2a Qa) R)
   = PROPx (P' ++ P) (LOCALx (LocalD T1 T2 Q') R).
Proof.
  intros until R.
  induction Q; intros.
  simpl in H. inv H. reflexivity.
  simpl in H.
  destruct a; simpl in H.
+
    destruct (T1a ! i) eqn:H8; inv H;
    rewrite <- (IHQ _ _ _ _ _ _ _ _ H1); clear H1 IHQ.
    simpl app. rewrite <- insert_prop.
    rewrite <- insert_local'.
    apply local2ptree_sound_aux with (Q0 := temp i v0).
    extensionality rho. unfold locald_denote; simpl.
    unfold local, lift1; unfold_lift; simpl. normalize.
    f_equal. apply prop_ext; split; intros [? ?]; subst; split; auto.
    rewrite in_app; right. apply LocalD_sound_temp. auto.
    apply LOCALx_shuffle'; intros.
    simpl In. rewrite !in_app. simpl In. intuition.
    apply LOCALx_expand_temp_var in H0. simpl In in H0.
    destruct H0; auto. right. right.
    apply LocalD_remove_empty_from_PTree1 in H; auto.
    right; apply LOCALx_expand_temp_var.
    simpl. left; auto.
    right;  apply LOCALx_expand_temp_var.
    simpl.
    right. apply (LocalD_remove_empty_from_PTree1 i T1a T2a Qa Q0 H8). auto.
  +
    destruct (T2a ! i) eqn:H8; try destruct v0; inv H;
    rewrite <- (IHQ _ _ _ _ _ _ _ _ H1); clear H1 IHQ;
    simpl app;
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc;
    rewrite <- !insert_locals;
    forget (local (fold_right `(and) `(True) (map locald_denote Q))) as QQ;
    destruct (T2a ! i) as [ vd |  ] eqn:H9;
    try assert (H8 := LOCALx_expand_vardesc i vd T1 T2 Q');
    inv H8.
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app.      unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc.
     f_equal.
     rewrite !andp_assoc.
     rewrite !(andp_comm QQ). rewrite <- !andp_assoc. f_equal.
     f_equal. apply local_equal_lemma.
   -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc.
     rewrite !andp_assoc.
     rewrite !(andp_comm QQ). rewrite <- !andp_assoc. f_equal.
     f_equal. apply local_equal_lemma.
  -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     rewrite !(andp_comm QQ). rewrite <- !andp_assoc. f_equal.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc.
     f_equal. simpl. unfold lvar_denote, gvar_denote.
     extensionality rho; unfold local, lift1; simpl;
     normalize.
     f_equal; apply prop_ext; intuition.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
  -
     rewrite !(andp_comm QQ). rewrite <- !andp_assoc. f_equal.
     rewrite <- (PTree.gsident _ _ H9) at 1 by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- !insert_local', <- !andp_assoc. auto.
  -
     rewrite !(andp_comm QQ). rewrite <- !andp_assoc. f_equal.
     rewrite !LOCALx_expand_vardesc'.
     unfold denote_vardesc.
     rewrite <- !insert_local'.
     rewrite LOCALx_shuffle'
       with (Q:= LocalD T1a (PTree.remove i T2a) Qa)
              (Q':= LocalD T1a T2a Qa); auto.
    intro; symmetry; apply (LocalD_remove_empty_from_PTree2); auto.
 +
    destruct (T2a ! i) eqn:H8; try destruct v0; inv H;
    rewrite <- (IHQ _ _ _ _ _ _ _ _ H1); clear H1 IHQ;
    simpl app;
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc;
    rewrite <- !insert_locals;
    forget (local (fold_right `(and) `(True) (map locald_denote Q))) as QQ;
     rewrite !(andp_comm QQ); rewrite <- !andp_assoc; f_equal; clear QQ;
    destruct (T2a ! i) as [ vd |  ] eqn:H9;
    try assert (H8 := LOCALx_expand_vardesc i vd T1 T2 Q');
    inv H8.
    -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc;
     f_equal. simpl. unfold lvar_denote, gvar_denote, sgvar_denote.
     extensionality rho; unfold local, lift1; simpl;
     normalize.
     f_equal; apply prop_ext; intuition.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
   -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc;
     f_equal. simpl. unfold lvar_denote, gvar_denote, sgvar_denote.
     extensionality rho; unfold local, lift1; simpl;
     normalize.
     f_equal; apply prop_ext; intuition.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
  -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc;
     f_equal. simpl. unfold lvar_denote, gvar_denote, sgvar_denote.
     extensionality rho; unfold local, lift1; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? ?].
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (Map.get (ge_of rho) i); intuition. subst; auto.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     subst; auto.
  -
     rewrite <- (PTree.gsident _ _ H9) at 1 by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc;
     f_equal. simpl. unfold lvar_denote, gvar_denote, sgvar_denote.
     extensionality rho; unfold local, lift1; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? ?].
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (Map.get (ge_of rho) i); intuition. subst; auto.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     subst; auto.
  -
     rewrite !LOCALx_expand_vardesc'.
     unfold denote_vardesc.
     rewrite <- !insert_local'.
     rewrite LOCALx_shuffle'
       with (Q:= LocalD T1a (PTree.remove i T2a) Qa)
              (Q':= LocalD T1a T2a Qa); auto.
    intro; symmetry; apply (LocalD_remove_empty_from_PTree2); auto.
 +
    destruct (T2a ! i) as [ [ | | | ] | ] eqn:H8;
     (rewrite <- (IHQ _ _ _ _ _ _ _ _ H); clear H IHQ;
        simpl app;
        rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc;
    rewrite <- !insert_locals;
    forget (local (fold_right `(and) `(True) (map locald_denote Q))) as QQ;
     rewrite !(andp_comm QQ); rewrite <- !andp_assoc; f_equal; clear QQ).
    -
     rewrite <- (PTree.gsident _ _ H8) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- !insert_local', <- !andp_assoc.
     f_equal. simpl. unfold lvar_denote, gvar_denote, sgvar_denote.
     extensionality rho; unfold local, lift1; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? [? ?]].
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (Map.get (ge_of rho) i); intuition. subst; auto.
     subst.
     destruct (Map.get (ge_of rho) i); intuition.
   -
     rewrite <- (PTree.gsident _ _ H8) at 1 by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- !insert_local', <- !andp_assoc.
     f_equal.
     apply andp_comm.
  -
     rewrite <- (PTree.gsident _ _ H8) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop, <- !insert_local', <- !andp_assoc.
     f_equal. simpl. unfold lvar_denote, gvar_denote, sgvar_denote.
     extensionality rho; unfold local, lift1; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? ?].
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (Map.get (ge_of rho) i); intuition. subst; auto.
     destruct (Map.get (ve_of rho) i) as [[? ?]|]; intuition.
     destruct (Map.get (ge_of rho) i); intuition. subst; auto.
  -
     rewrite <- (PTree.gsident _ _ H8) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app. unfold denote_vardesc.
     rewrite  <- ?insert_prop,  <- !insert_local', <- !andp_assoc.
     f_equal. simpl. unfold lvar_denote, gvar_denote, sgvar_denote.
     extensionality rho; unfold local, lift1; simpl;
     normalize.
     f_equal; apply prop_ext; split; intros [? ?].
     destruct (Map.get (ge_of rho) i); intuition. subst; auto.
     destruct (Map.get (ge_of rho) i); intuition. subst; auto.
  -
     rewrite !LOCALx_expand_vardesc'.
     unfold denote_vardesc. simpl app.
     rewrite <- !insert_local'.
     rewrite LOCALx_shuffle'
       with (Q:= LocalD T1a (PTree.remove i T2a) Qa)
              (Q':= LocalD T1a T2a Qa); auto.
    intro; symmetry; apply (LocalD_remove_empty_from_PTree2); auto.
 +
    rewrite <- (IHQ _ _ _ _ _ _ _ _ H); clear IHQ H.
    simpl app. rewrite <- insert_prop. rewrite <- insert_local'. reflexivity.
 +
    rewrite <- (IHQ _ _ _ _ _ _ _ _ H); clear IHQ H.
     apply LOCALx_shuffle'.
     intros.
     rewrite !in_app. rewrite LOCALx_expand_res.
     rewrite !in_cns. clear; intuition.
Qed.

Lemma local2ptree_soundness  : forall P Q R T1 T2 P' Q',
  local2ptree Q = (T1, T2, P', Q') ->
  PROPx P (LOCALx Q (SEPx R)) = PROPx (P' ++ P) (LOCALx (LocalD T1 T2 Q') (SEPx R)).
Proof. intros. eapply local2ptree_soundness' in H.
   etransitivity; [ | apply H]. clear H.
   simpl.
   unfold LocalD. rewrite !PTree.fold_spec. simpl. rewrite <- app_nil_end; auto.
Qed.

Lemma local2ptree_soundness'' : forall Q T1 T2,
  local2ptree Q = (T1, T2, nil, nil) ->
  LOCALx Q TT = LOCALx (LocalD T1 T2 nil) TT.
Proof.
  intros.
  eapply local2ptree_soundness in H.
  match goal with |- LOCALx _ ?B = _ =>
    replace B with (SEPx(TT::nil))
  end.
  instantiate (2:=@nil Prop) in H.
  simpl app in H.
  unfold PROPx in H.
  simpl fold_right in H.
  rewrite !prop_true_andp in H by auto. apply H.
  extensionality rho; unfold SEPx; simpl. rewrite sepcon_emp. reflexivity.
Qed.

Lemma local_ext: forall Q0 Q rho, In Q0 Q -> fold_right `(and) `(True) Q rho -> Q0 rho.
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

Lemma local_ext_rev: forall (Q: list (environ -> Prop)) rho, (forall Q0, In Q0 Q -> Q0 rho) -> fold_right `(and) `(True) Q rho.
Proof.
  intros.
  induction Q.
  + simpl; auto.
  + simpl.
    split.
    - apply H; simpl; auto.
    - apply IHQ; intros.
      apply H; simpl; auto.
Qed.

Definition localD (temps : PTree.t val) (locals : PTree.t vardesc) :=
LocalD temps locals nil.

Definition assertD (P : list Prop) (Q : list localdef) (sep : list mpred) :=
PROPx P (LOCALx Q (SEPx sep)).

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


Lemma make_func_ptr: 
 forall id (Espec: OracleKind) (CS: compspecs) Delta P Q R fs p c Post,
   (var_types Delta) ! id = None ->
   (glob_specs Delta) ! id = Some fs ->
   (glob_types Delta) ! id = Some (type_of_funspec fs) ->
    PTree.get id (snd (fst ((fst (local2ptree Q))))) = Some (vardesc_visible_global p) ->
  semax Delta (PROPx P (LOCALx Q (SEPx (func_ptr' fs p :: R)))) c Post ->
  semax Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
apply (semax_fun_id id fs Delta); auto.
eapply semax_pre; try apply H3. clear H3.
destruct (local2ptree Q) as [[[? ?] ?] ?] eqn:?.
simpl in H2.
pose proof (local2ptree_soundness P Q R t t0 l l0 Heqp0).
apply (LocalD_sound_visible_global id p t t0 l0) in H2.
forget (LocalD t t0 l0) as Q'.
clear - H2 H3.
rewrite <- insert_SEP.
unfold func_ptr'.
normalize.
rewrite corable_andp_sepcon1
  by (unfold_lift; simpl; intros; apply corable_func_ptr).
apply andp_right; [ | apply andp_left2; apply andp_left1; normalize].
rewrite H3.
clear H3.
rewrite <- andp_assoc.
eapply derives_trans.
apply andp_right.
apply andp_left1.
eapply in_local; eassumption.
apply andp_left2. apply derives_refl.
clear.
intro rho.
unfold_lift. unfold local, lift1; simpl.
normalize.
unfold eval_var.
hnf in H.
destruct (Map.get (ve_of rho) id) as [[? ?] | ]; try contradiction.
destruct (Map.get (ge_of rho) id); try contradiction.
subst; auto.
Qed.
