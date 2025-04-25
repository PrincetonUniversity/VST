Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.client_lemmas.
Import -(notations) compcert.lib.Maps.

Import LiftNotation.
Require Import iris.proofmode.monpred.

Definition pTree_from_elements {A} (el: list (positive * A)) : PTree.t A :=
 fold_right (fun ia t => PTree.set (fst ia) (snd ia) t) (PTree.empty _) el.

Definition local_trees :=
   (PTree.t val * PTree.t (type * val) * list Prop * option globals)%type.

Definition local2ptree1 (Q: localdef)
   (T1: PTree.t val) (T2: PTree.t (type * val)) (P': list Prop) (Q': option globals)
   (f:  PTree.t val -> PTree.t (type * val) -> list Prop -> option globals -> local_trees)
   : local_trees :=
match Q with
| temp i v =>   match T1 !! i with
                | None => f (PTree.set i v T1) T2 P' Q'
                | Some v' => f T1 T2 ((v=v')::P')  Q'
                end
| lvar i t v => match T2 !! i with
                | None => f T1 (PTree.set i (t, v) T2) P' Q'
                | Some (t', vl) => f T1 T2 ((vl=v)::(t'=t)::P') Q'
                end
| gvars gv =>   match Q' with
                | None => f T1 T2 P' (Some gv)
                | Some gv' => f T1 T2 ((gv' = gv)::P') Q'
                end
end.

Fixpoint local2ptree_aux (Q: list localdef)
   (T1: PTree.t val) (T2: PTree.t (type * val)) (P': list Prop) (Q': option globals):
   local_trees :=
match Q with
| Q1 :: Qr => local2ptree1 Q1 T1 T2 P' Q' (local2ptree_aux Qr)
| nil => (T1,T2,P',Q')
end.

Definition local2ptree (Q: list localdef)
     : (PTree.t val * PTree.t (type * val) * list Prop * option globals) :=
local2ptree_aux Q (PTree.empty _) (PTree.empty _) nil None.

Definition CLEAR_ME {T} (x:T) := x.
Ltac hide_it z := let x := fresh "x" in set (x:=z); change z with (CLEAR_ME z) in x.
(* TODO: compare this with unfold_name method in symbolic_go_lower. *)

Ltac hnf_localdef_list A :=
  match A with
 | temp ?i ?v :: ?Q' => hide_it v; let i' := eval compute in i in change i with i'; hnf_localdef_list Q'
 | lvar ?i ?t ?v :: ?Q' => hide_it t; hide_it v; let i' := eval compute in i in change i with i'; hnf_localdef_list Q'
 | gvars ?v :: ?Q' => hide_it v; hnf_localdef_list Q'
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
 [cbv beta iota delta [local2ptree local2ptree1 local2ptree_aux
     PTree.set PTree.empty PTree.set0 PTree.set'
     PTree.get PTree.get'   ]; 
  reflexivity |
  repeat match goal with x := CLEAR_ME _ |- _ => unfold CLEAR_ME in x; subst x end;
  apply f_equal;
  try reflexivity;
  match goal with |- ?L = _ => let x := grab_gvars L in instantiate(1:=x); reflexivity end
 ].

Goal exists x,  local2ptree (
      temp 1%positive Vundef
   :: temp 3%positive (Vint (Int.repr (3+4)))
   :: lvar 1%positive tint (Vint (Int.repr (1 + 2)))
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
  evar (t: (PTree.t val * PTree.t (type * val) * list Prop * option globals)%type);
  assert (H: local2ptree Q = t); subst t;
   [ prove_local2ptree | ].

Definition LocalD (T1: PTree.t val) (T2: PTree.t (type * val)) (Q: option globals) :=
  PTree.fold (fun Q i v => temp i v :: Q) T1
  (PTree.fold (fun Q i tv => match tv with (t, v) => lvar i t v end :: Q) T2
   match Q with Some gv => (gvars gv) :: nil | None => nil end).

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
  + rewrite PTree.gso // in H.
    right.
    apply PTree.elements_correct.
    auto.
Qed.

Lemma LocalD_sound_temp:
  forall i v T1 T2 Q,
  PTree.get i T1 = Some v -> In (temp i v) (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 forget (PTree.fold (fun Q i tv => match tv with (t, v) => lvar i t v end :: Q) T2
          match Q with Some gv => (gvars gv) :: nil | None => nil end) as Q'.
 rewrite !PTree.fold_spec  -!fold_left_rev_right.
 apply PTree.elements_correct in H.
 rewrite in_rev in H.
 forget (rev (PTree.elements T1)) as L.
 induction L; intros; destruct H.
 subst a. left. reflexivity.
 right. apply IHL. auto.
Qed.

Lemma LocalD_sound_local:
  forall i t v T1 T2 Q,
  PTree.get i T2 = Some (t, v) ->
   In (lvar i t v) (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 rewrite !PTree.fold_spec -!fold_left_rev_right.
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

Lemma LocalD_sound_gvars:
  forall gv T1 T2 Q,
  Q = Some gv->
  In (gvars gv) (LocalD T1 T2 Q).
Proof.
 unfold LocalD; intros.
 subst Q.
 rewrite !PTree.fold_spec -!fold_left_rev_right.
 forget (rev (PTree.elements T1)) as L.
 induction L; [ | right; apply IHL].
 forget (rev (PTree.elements T2)) as L.
 simpl.
 induction L.
 simpl; auto.
 simpl.
 destruct a as [ia vda]; destruct vda; simpl in *; auto.
Qed.

Lemma LocalD_sound: forall q T1 T2 Q,
  (exists i v, PTree.get i T1 = Some v /\ q = temp i v) \/
  (exists i t v, PTree.get i T2 = Some (t, v) /\ q = lvar i t v) \/
  (exists gv, Q = Some gv /\ q = gvars gv) ->
  In q (LocalD T1 T2 Q).
Proof.
intros.
repeat match type of H with
             | _ \/ _ => destruct H
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst.
apply LocalD_sound_temp; auto.
apply LocalD_sound_local with (T1:=T1) (T2:=T2)(Q:=Q) in H; intuition.
apply LocalD_sound_gvars with (T1:=T1) (T2:=T2); intuition.
Qed.

Lemma LocalD_complete : forall q T1 T2 Q,
  In q (LocalD T1 T2 Q) ->
  (exists i v, PTree.get i T1 = Some v /\ q = temp i v) \/
  (exists i t v, PTree.get i T2 = Some (t, v) /\ q = lvar i t v) \/
  (exists gv, Q = Some gv /\ q = gvars gv).
Proof.
  intros.
  unfold LocalD in H.
  rewrite !PTree.fold_spec -!fold_left_rev_right in H.
  remember (rev (PTree.elements T1)) as L.
  simpl in H.
  change L with (nil ++ L) in HeqL.
  forget (@nil (positive * val)) as K.
  revert K HeqL; induction L; intros.
  + right.
    clear K T1 HeqL.
    remember (rev (PTree.elements T2)) as L.
    simpl in H.
    change L with (nil ++ L) in HeqL.
    forget (@nil (positive * (type * val))) as K.
    revert K HeqL; induction L; intros.
    - repeat right.
      destruct Q; simpl in H; [| inv H].
      destruct H; [| tauto].
      subst; eexists; eauto.
    - assert (In a (PTree.elements T2)).
      { rewrite in_rev -HeqL. rewrite in_app. right; left; auto. }
      destruct a as [i [t v]].
      apply PTree.elements_complete in H0.
      destruct H; try subst q; eauto 50.
      specialize (IHL H (K ++ (i, (t, v)) :: nil));
      rewrite <- app_assoc in IHL; specialize (IHL HeqL); eauto.
  + destruct H.
    - subst q.
      assert (In a (PTree.elements T1)).
      { rewrite in_rev -HeqL. rewrite in_app. right; left; auto. }
      destruct a as [i v]; apply PTree.elements_complete in H; eauto.
    - destruct a as [i v].
      specialize (IHL H (K ++ (i,v)::nil)).
      rewrite <- app_assoc in IHL; specialize (IHL HeqL); eauto.
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
      * rewrite PTree.gso // in H.
        right.
        apply LocalD_sound_temp.
        rewrite PTree.gro //.
    - right.
      destruct H.
      * destruct H as [j [t [v1 [? ?]]]]; subst Q0.
        unfold LocalD.
        rewrite !PTree.fold_spec -!fold_left_rev_right.
        induction (rev (PTree.elements (PTree.remove i T1))); simpl.
       ++ apply PTree.elements_correct in H. rewrite in_rev in H.
          induction  (rev (PTree.elements T2)).
         -- inv H.
         -- destruct H.
           ** destruct a. inv H. simpl. left; auto.
           ** simpl. destruct a as [? ?]; simpl; repeat right; auto.
       ++ right; apply IHl.
      * unfold LocalD.
        rewrite !PTree.fold_spec -!fold_left_rev_right.
        destruct H as [gv [? ?]]; subst Q Q0.
        induction (rev (PTree.elements (PTree.remove i T1))); simpl.
       ++ induction (rev (PTree.elements T2)); simpl; auto.
       ++ destruct a as [? ?]; simpl; repeat right; auto.
  + destruct H.
    - subst.
      apply LocalD_sound_temp. apply PTree.gss.
    - unfold LocalD in *.
      rewrite !PTree.fold_spec -!fold_left_rev_right.
      rewrite !PTree.fold_spec -!fold_left_rev_right in H.
      forget  (fold_right (fun (y : positive * (type * val)) (x : list localdef) => (let (t, v0) := snd y in lvar (fst y) t v0) :: x)
        match Q with
        | Some gv => gvars gv :: nil
        | None => nil
        end (rev (PTree.elements T2))) as JJ.
      clear - H.
      rewrite in_temp_aux. rewrite in_temp_aux in H.
      destruct H as [[j [w [? ?]]] |?].
      * left; exists j,w; split; auto.
        rewrite <- in_rev in *.
        apply PTree.elements_correct. apply PTree.elements_complete in H0.
        clear - H0.
        destruct (ident_eq i j); subst.
       ++ rewrite PTree.grs in H0; inv H0.
       ++ rewrite PTree.gro // in H0. rewrite PTree.gso; auto.
      * right; auto.
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
 right; left. exists x,x0,x1. split; auto.
 destruct (ident_eq i x). subst. rewrite PTree.grs in H; inv H.
 rewrite PTree.gro // in H; rewrite PTree.gso //.
*
 repeat right. exists x; split; auto.
Qed.

Lemma LOCALx_expand_vardesc : forall i vd T1 T2 Q Q0,
  In Q0 (LocalD T1 (PTree.set i vd T2) Q) <->
  In Q0 (match vd with (t, v) => lvar i t v end :: (LocalD T1 (PTree.remove i T2) Q)).
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
      * rewrite PTree.gso // in H.
         destruct vd; simpl;
        repeat right; apply LocalD_sound;
        right; left;
        exists x,x0,x1; rewrite PTree.gro //.
    - right.
      apply LocalD_sound_gvars. auto.
 +
   destruct vd; simpl in H; destruct H; subst.
   -
      apply LocalD_sound.
      right. left. exists i,t,v; split; auto. apply PTree.gss.
   -
      apply In_LocalD_remove_set; auto.
Qed.

Lemma LOCALx_expand_gvars: forall T1 T2 gv Q0,
  In Q0 (LocalD T1 T2 (Some gv)) <->
  In Q0 (gvars gv ::LocalD T1 T2 None).
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
      inv H; auto.
+
    destruct H. subst. apply LocalD_sound_gvars. auto.
    apply LocalD_complete in H.
    apply LocalD_sound.
    repeat match type of H with
             | _ \/ _ => destruct H
             | ex _ => destruct H
             | _ /\ _ => destruct H
             end; subst.
    * do 0 right; left; repeat econstructor; eauto.
    * do 1 right; left; repeat econstructor; eauto.
    * inv H.
Qed.

Lemma raise_and:
forall `{heapGS Σ} (A B : assert),
    assert_of (fun rho: environ => A rho ∧ B rho) = (A ∧ B).
Proof.
intros. apply assert_ext; intros; monPred.unseal. done.
Qed.

Lemma local_assert:
forall `{heapGS Σ} (P Q : assert),
  P ⊣⊢ Q <-> forall rho, (P rho ⊣⊢ Q rho).
Proof.
  intros. split; intros HPQ; intros.
  - rewrite HPQ //.
  - constructor; auto.
Qed.

Section LOCAL2PTREE_DENOTE.

Context  `{heapGS0: heapGS Σ}.

Lemma LOCALx_shuffle_derives': forall P Q Q' R,
  (forall Q0, In Q0 Q' -> In Q0 Q) ->
  PROPx P (LOCALx Q R) ⊢ PROPx P (LOCALx Q' R).
Proof.
  intros.
  induction Q'.
  { go_lowerx.
    normalize.
  }
  pose proof (H a (or_introl _ eq_refl)).
  rewrite <- insert_local'.
  apply bi.and_intro.
  + clear -H0.
    induction Q; [inversion H0 |].
    rewrite <- insert_local'.
    simpl in H0; inversion H0.
    - subst. solve_andp.
    - rewrite bi.and_elim_r.
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
  PROPx P (LOCALx Q (SEPx R)) ⊢ PROPx P (LOCALx Q' (SEPx R)).
Proof. intros. apply LOCALx_shuffle_derives'. auto. Qed.

Lemma foldr_Forall' : forall Q rho, foldr (` and) (` True%type) (map locald_denote Q) rho ↔
  Forall (fun P => P rho) (map locald_denote Q).
Proof.
  induction Q; simpl; intros; unfold_lift.
  - split; [constructor | auto].
  - rewrite IHQ; split.
    + intros (? & ?); constructor; auto.
    + inversion 1; auto.
Qed.

Lemma LOCALx_shuffle': forall P Q Q' R,
  (forall Q0, In Q0 Q' <-> In Q0 Q) ->
  PROPx P (LOCALx Q R) = PROPx P (LOCALx Q' R).
Proof.
  intros.
  f_equal.
  unfold LOCALx; f_equal; f_equal.
  extensionality; apply prop_ext.
  rewrite !foldr_Forall' !Forall_forall.
  setoid_rewrite in_map_iff. setoid_rewrite H. done.
Qed.

Lemma LOCALx_shuffle: forall P Q Q' R,
  (forall Q0, In Q0 Q' <-> In Q0 Q) ->
  PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q' (SEPx R)).
Proof.
  intros.
  apply LOCALx_shuffle'; done.
Qed.

Lemma LocalD_remove_empty_from_PTree1: forall i T1 T2 Q Q0,
  T1 !! i = None ->
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
   - do 2 right. repeat eexists.
   - do 0 right; left. exists x,x0; split; auto.
      destruct (ident_eq i x). subst. congruence.
      rewrite PTree.gro; auto.
   - do 1 right; left. repeat eexists. eauto.
   - do 2 right. repeat eexists.
Qed.

Lemma LocalD_remove_empty_from_PTree2: forall i T1 T2 Q Q0,
  T2 !! i = None ->
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
           | try rewrite PTree.gro // in H]).
  - do 1 right; left; repeat eexists; eauto.
  - do 2 right; repeat eexists; eauto.
  - do 1 right; left; repeat eexists; rewrite PTree.gro //.
  - do 2 right; repeat eexists; rewrite PTree.gro //.
Qed.

Lemma nth_error_local':
  forall n P Q R (Qn: localdef),
    nth_error Q n = Some Qn ->
    PROPx P (LOCALx Q R) ⊢ local (locald_denote Qn).
Proof.
intros.
unfold PROPx. rewrite bi.and_elim_r. unfold LOCALx. rewrite bi.and_elim_l.

(* the slightly modified go_lowerx tactic *)
unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift; split => rho.
simpl.  
repeat rewrite -bi.and_assoc;
repeat ((simple apply go_lower_lem1 || apply bi.pure_elim_l || apply bi.pure_elim_r); intro);
try apply bi.pure_elim';
repeat rewrite -> prop_true_andp by assumption;
try apply entails_refl.

intros. iPureIntro. intros.
revert Q H H0; induction n; destruct Q; intros; inv H.
destruct H0; auto.
destruct H0. apply (IHn Q); auto.
Qed.

Lemma in_local': forall Q0 P Q R, In Q0 Q ->
   PROPx P (LOCALx Q R) ⊢ local (locald_denote Q0).
Proof.
  intros.
  destruct (in_nth_error _ _ H) as [?n ?H].
  eapply nth_error_local'.
  eauto.
Qed.

Lemma local2ptree_sound_aux: forall P Q R Q0 Q1 Q2,
  Q1 ∧ local (locald_denote Q0) ⊣⊢ Q2 ∧ local (locald_denote Q0) ->
  In Q0 Q ->
  Q1 ∧ PROPx P (LOCALx Q R) ⊣⊢ Q2 ∧ PROPx P (LOCALx Q R).
Proof.
  intros.
  pose proof in_local' _ P _ R H0.
  rewrite (add_andp _ _ H1).
  rewrite (bi.and_comm _ (local (locald_denote Q0))).
  rewrite !bi.and_assoc.
  rewrite H. reflexivity.
Qed.

Lemma LOCALx_expand_vardesc': forall P R i vd T1 T2 Q,
  PROPx P (LOCALx (LocalD T1 (PTree.set i vd T2) Q) R) =
  PROPx P (LOCALx (match vd with (t,v) => lvar i t v end :: LocalD T1 (PTree.remove i T2) Q) R).
Proof.
 intros.
 apply LOCALx_shuffle'; intro.
 symmetry; apply LOCALx_expand_vardesc.
Qed.

Lemma LOCALx_expand_gvars': forall P R gv T1 T2,
  PROPx P (LOCALx (LocalD T1 T2 (Some gv)) R) =
  PROPx P (LOCALx (gvars gv :: LocalD T1 T2 None) R).
Proof.
 intros.
 apply LOCALx_shuffle'; intro.
 symmetry; apply LOCALx_expand_gvars.
Qed.

Lemma local_equal_lemma :
 forall i t v t' v',
  (local(Σ:=Σ) (locald_denote (lvar i t v)) ∧ local (locald_denote (lvar i t' v'))) =
  (⌜(v' = v)⌝ ∧ ⌜(t'=t)⌝ ∧ local (locald_denote (lvar i t' v'))).
Proof.
intros. raise_rho.
unfold local, lift1; simpl.
apply assert_ext; intros; monPred.unseal; normalize.
f_equal; apply prop_ext; split.
- intros (? & ?).
  unfold lvar_denote in *.
  destruct (Map.get (ve_of rho) i) as [[? ?] | ] eqn:H8; try contradiction.
  destruct H, H0; subst; auto.
- intros (-> & -> & ?); auto.
Qed.

Lemma gvars_equal_lemma :
  forall g g0,
  (local(Σ:=Σ) (locald_denote (gvars g)) ∧ local (locald_denote (gvars g0))) = (⌜g0 = g⌝ ∧ local (locald_denote (gvars g0))).
Proof.
intros. raise_rho.
unfold local, lift1; simpl.
apply assert_ext; intros; monPred.unseal.
rewrite -!pure_and; f_equal; apply prop_ext; intuition.
- unfold gvars_denote in *; subst; auto.
- subst; auto.
Qed.

Lemma insert_locals:
  forall P A B C,
  (local (fold_right `(and) `((True:Prop)) (map locald_denote A)) ∧ PROPx P (LOCALx B C)) =
  PROPx P (LOCALx (A++B) C).
Proof.
intros.
induction A.
apply assert_ext; intros; monPred.unseal; simpl. rewrite prop_true_andp //.
simpl app. rewrite <- (insert_local' a).
rewrite <- IHA.
rewrite assert_lemmas.and_assoc'.
simpl.
apply assert_ext; intros; unfold PROPx; monPred.unseal; unfold_lift; unfold lift1.
normalize.
Qed.

Lemma LOCALx_app_swap:
  forall A B R, LOCALx (A++B) R = LOCALx (B++A) R.
Proof.
intros.
unfold LOCALx.
rewrite !map_app !fold_right_local_app.
rewrite (and_comm' (local _)) //.
Qed.

Lemma and_mono_iff:
  forall {prop:bi} (P P' Q Q': prop), (P ⊣⊢ Q) → (P' ⊣⊢ Q') → (P ∧ P') ⊣⊢ (Q ∧ Q').
Proof.
  intros; by apply bi.and_proper.
Qed.

Lemma local2ptree_soundness' : forall P Q R T1a T2a Pa Qa T1 T2 P' Q',
  local2ptree_aux Q T1a T2a Pa Qa = (T1, T2, P', Q') ->
  PROPx (Pa++P) (LOCALx (Q ++ LocalD T1a T2a Qa) R)
    ⊣⊢ PROPx (P' ++ P) (LOCALx (LocalD T1 T2 Q') R).
Proof.
  intros until R.
  induction Q; intros.
  simpl in H. inv H. reflexivity.
  simpl in H.
  destruct a; simpl in H.
+
    destruct (T1a !! i) eqn:H8; inv H;
    rewrite <- (IHQ _ _ _ _ _ _ _ _ H1); clear H1 IHQ.
    simpl app. rewrite <- insert_prop.
    rewrite <- insert_local'.
    apply local2ptree_sound_aux with (Q0 := temp i v0).
    unfold locald_denote; simpl.
    unfold local, lift1; unfold_lift; simpl.
    constructor; intro rho; rewrite !monPred_at_and /=.
    rewrite monPred_at_pure. rewrite -!pure_and.
    apply bi.pure_iff. split; intuition congruence.
    rewrite in_app; right. apply LocalD_sound_temp. auto.
    erewrite LOCALx_shuffle'; first done; intros.
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
    destruct (T2a !! i) as [[?t ?v] |] eqn:H8; inv H;
    rewrite <- (IHQ _ _ _ _ _ _ _ _ H1); clear H1 IHQ;
    simpl app;
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc;
    rewrite <- !insert_locals;
    forget (local(Σ:=Σ) (fold_right `(and) `(True:Prop) (map locald_denote Q))) as QQ;
    destruct (T2a !! i) as [ vd |  ] eqn:H9;
    try assert (H8 := LOCALx_expand_vardesc i vd T1 T2 Q');
    inv H8.
   -
     rewrite <- (PTree.gsident _ _ H9) by auto.
     rewrite !LOCALx_expand_vardesc'.
     simpl app.
     rewrite  <- ?insert_prop, <- ?insert_local', <- ?andp_assoc.
     rewrite !(bi.and_comm QQ).
     rewrite !bi.and_assoc.
     rewrite local_equal_lemma.
     rewrite !bi.and_assoc //.
   -
     rewrite !(bi.and_comm QQ). rewrite !bi.and_assoc. rewrite and_mono_iff //.
     rewrite !LOCALx_expand_vardesc'.
     rewrite <- !insert_local'.
     rewrite (LOCALx_shuffle' _
              (LocalD T1a (PTree.remove i T2a) Qa)
              (LocalD T1a T2a Qa)) //=.
    2: {intro; symmetry; apply (LocalD_remove_empty_from_PTree2); auto. }
    rewrite /PROPx /LOCALx. rewrite !bi.and_assoc //. 
 + destruct Qa; rewrite <- (IHQ _ _ _ _ _ _ _ _ H); clear IHQ H;
   simpl app; rewrite <- ?insert_prop; rewrite <- insert_local', <- ?andp_assoc;
   rewrite <- !insert_locals;
   forget (local(Σ:=Σ) (fold_right `(and) `(True:Prop) (map locald_denote Q))) as QQ.
   - rewrite LOCALx_expand_gvars'.
     simpl app.
     rewrite  <- ?insert_prop, <- ?insert_local'.
     rewrite [in QQ ∧ _]bi.and_comm. rewrite !bi.and_assoc.
     rewrite gvars_equal_lemma //.
   - rewrite LOCALx_expand_gvars'.
     simpl app.
     rewrite -?insert_prop -?insert_local' !bi.and_assoc.
     rewrite [in QQ ∧ _]bi.and_comm //.
Qed.

Lemma local2ptree_soundness  : forall P Q R T1 T2 P' Q',
  local2ptree Q = (T1, T2, P', Q') ->
  PROPx P (LOCALx Q (SEPx R)) ⊣⊢ PROPx (P' ++ P) (LOCALx (LocalD T1 T2 Q') (SEPx R)).
Proof. intros. eapply local2ptree_soundness' in H.
   etransitivity; [ | apply H]. clear H.
   simpl. rewrite app_nil_r; auto.
Qed.

Lemma local2ptree_soundness'' : forall Q T1 T2 gv,
  local2ptree Q = (T1, T2, nil, Some gv) ->
  LOCALx Q True ⊣⊢ LOCALx (LocalD T1 T2 (Some gv)) True.
Proof.
  intros.
  eapply local2ptree_soundness in H.
  match goal with |- LOCALx _ ?B ⊣⊢ _ =>
    assert (H0: B ⊣⊢ (@SEPx environ_index Σ (True::nil)))
  end.
  {  unfold SEPx. simpl. rewrite bi.sep_emp embed_pure //. }
  rewrite H0.
  instantiate (2:=@nil Prop) in H.
  simpl app in H.
  unfold PROPx in H.
  simpl fold_right in H.
  rewrite !bi.True_and in H.
  rewrite H.
  raise_rho; rewrite /SEPx //.
Qed.

Lemma local_ext: forall Q0 Q rho, In Q0 Q -> fold_right `(and) `(True:Prop) Q rho -> Q0 rho.
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

Lemma local_ext_rev: forall (Q: list (environ -> Prop)) rho, (forall Q0, In Q0 Q -> Q0 rho) -> fold_right `(and) `(True:Prop) Q rho.
Proof.
  intros.
  induction Q.
  + simpl; constructor.
  + simpl.
    split.
    - apply H; simpl; auto.
    - apply IHQ; intros.
      apply H; simpl; auto.
Qed.

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
 forall `{!VSTGS OK_ty Σ} {OK_spec: ext_spec OK_ty} id (CS: compspecs) E Delta P Q R fs gv p c Post,
   (var_types Delta) !! id = None ->
   (glob_specs Delta) !! id = Some fs ->
   (glob_types Delta) !! id = Some (type_of_funspec fs) ->
   snd (local2ptree Q) = Some gv /\ gv id = p ->
  semax E Delta (PROPx P (LOCALx Q (SEPx (func_ptr fs p :: R)))) c Post ->
  semax E Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
apply (semax_fun_id id fs E Delta); auto.
eapply semax_pre; try apply H3. clear H3.
destruct (local2ptree Q) as [[[? ?] ?] ?] eqn:?.
simpl in H2.
destruct H2 as [H3 H2']; subst o.
pose proof (local2ptree_soundness P Q R t t0 l _ Heqp0) as H3.
pose proof LocalD_sound_gvars gv t t0 _ eq_refl as H2.
forget (LocalD t t0 (Some gv)) as Q'.
assert (forall rho, local(Σ:=Σ) (tc_environ Delta) rho ⊢ ⌜Map.get (ve_of rho) id = None⌝) as TC.
{  
  intro rho. simpl.
  unfold local, lift1.
  apply bi.pure_mono.
  intros.
  destruct H4 as [_ [? _]].
  specialize (H4 id).
  rewrite H in H4.
  destruct (Map.get (ve_of rho) id) as [[? ?] |]; auto.
  specialize (H4 t1).
  destruct H4 as [_ ?].
  specialize (H4 (ex_intro _ b eq_refl)).
  inv H4.
}
clear - H2 H2' H3 TC.
rewrite -insert_SEP.
unfold func_ptr.
split => rho; monPred.unseal.
normalize.
iIntros "(%H0 & H1 & H2)".  iSplit. 2: { done. }
rewrite H3.
iPoseProof (in_local _ Delta (l ++ P) _ (SEPx R) H2 with "[H1]") as "H3".
{ rewrite /PROPx /LOCALx. iSplit;  done. }
iPoseProof (TC) as "%H4". apply H4 in H0.
subst p.
unfold local, lift1; simpl.
normalize.
unfold eval_var.
iDestruct "H3" as "%H5".
hnf in H5.
subst gv.
rewrite H0. done.
Qed.

End LOCAL2PTREE_DENOTE.
