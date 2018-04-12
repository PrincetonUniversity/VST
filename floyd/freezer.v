Require Import VST.floyd.base2.
Require Import VST.floyd.canon.
Require Import VST.floyd.entailer.
Require Import Coq.Lists.List.
Export ListNotations.
Require Import VST.floyd.client_lemmas.

Local Open Scope logic.

Module Type FREEZER.
Parameter FRZ : mpred -> mpred.
Parameter FRZ1: forall p, p |-- FRZ p.
Parameter FRZ2: forall p, FRZ p |-- p.

Parameter FRZL : list mpred -> mpred.
Parameter FRZL1: forall ps, fold_right sepcon emp ps |-- FRZL ps.
Parameter FRZL2: forall ps, FRZL ps |-- fold_right sepcon emp ps.

Parameter FRZRw : list mpred -> list mpred -> Type.
Parameter FRZRw_constr : forall {L1 G1: list mpred} {F: mpred},
    (fold_right sepcon emp G1) |-- fold_right sepcon emp L1 * F -> FRZRw L1 G1.
Parameter FRZR : forall L1 G1 {w: FRZRw L1 G1}, mpred.
Parameter FRZR1: forall L1 G1 (w: FRZRw L1 G1), fold_right sepcon emp G1 |-- fold_right sepcon emp L1 * @FRZR L1 G1 w.
Parameter FRZR2: forall L1 G1 L2 G2 F H, F |-- fold_right sepcon emp L2 -* fold_right sepcon emp G2 -> fold_right sepcon emp L2  * @FRZR L1 G1 (@FRZRw_constr L1 G1 F H) |-- fold_right sepcon emp G2.

End FREEZER.

Module Freezer : FREEZER.
Definition FRZ (p: mpred) := p.
Lemma FRZ1 p: p |-- FRZ p. apply derives_refl. Qed.
Lemma FRZ2 p: FRZ p |-- p. apply derives_refl. Qed.

Definition FRZL (ps:list mpred): mpred := fold_right sepcon emp ps.
Lemma FRZL1 ps: (fold_right_sepcon ps) |-- FRZL ps. apply derives_refl. Qed.
Lemma FRZL2 ps: FRZL ps |-- fold_right_sepcon ps. apply derives_refl. Qed.

Inductive FRZRw' (L1 G1: list mpred): Type :=
| FRZRw'_constr: forall F: mpred,
    (fold_right sepcon emp G1) |-- fold_right sepcon emp L1 * F -> FRZRw' L1 G1.

Definition FRZRw := FRZRw'.
Definition FRZRw_constr:= FRZRw'_constr.

Definition FRZR (L1 G1: list mpred) {w: FRZRw L1 G1}: mpred := 
  match w with
  | FRZRw'_constr F _ => F
  end.

Lemma FRZR1: forall L1 G1 (w: FRZRw L1 G1), fold_right sepcon emp G1 |-- fold_right sepcon emp L1 * @FRZR L1 G1 w.
Proof. intros ? ? [? ?]. auto. Qed.

Lemma FRZR2: forall L1 G1 L2 G2 F H, F |-- fold_right sepcon emp L2 -* fold_right sepcon emp G2 -> fold_right sepcon emp L2 * @FRZR L1 G1 (@FRZRw_constr L1 G1 F H) |-- fold_right sepcon emp G2.
Proof. intros ? ? ? ? ? ? ?. rewrite sepcon_comm. apply wand_sepcon_adjoint; auto. Qed.

End Freezer.

Notation FRZ := Freezer.FRZ.
Notation FRZL := Freezer.FRZL.
Notation FRZR := Freezer.FRZR.
Notation FRZRw := Freezer.FRZRw.

(************************ Freezing a single mpred ************************)
Lemma FRZ_ax:forall p, FRZ p = p.
Proof. intros. apply pred_ext. apply Freezer.FRZ2. apply Freezer.FRZ1. Qed.

Fixpoint freeze_nth (n: nat) (al: list mpred) {struct n}: list mpred :=
 match n, al with
 | O , a::al => (FRZ a) ::al
 | S n', a::al' => a :: freeze_nth n' al'
 | _, nil => nil
 end.

Lemma freeze1_SEP':
 forall n Espec {cs: compspecs} Delta P Q R c Post,
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (freeze_nth n R)))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros. subst.
eapply semax_pre; try apply H.
apply andp_left2.
go_lowerx; entailer!.  clear.
generalize dependent R.
induction n; destruct R; simpl; cancel. apply Freezer.FRZ1.
Qed.
Tactic Notation "freeze1_SEP" constr(n) :=
  eapply (freeze1_SEP' (nat_of_Z n)); simpl.
Tactic Notation "freeze1_SEP" constr(n) constr(m) :=
  (gather_SEP n m); eapply (freeze1_SEP' (nat_of_Z 0)); simpl.
Tactic Notation "freeze1_SEP" constr(n) constr(m) constr(k)  :=
  (gather_SEP n m k); eapply (freeze1_SEP' (nat_of_Z 0)); simpl.
Tactic Notation "freeze1_SEP" constr(n) constr(m) constr(k)  constr(p) :=
  (gather_SEP n m k p); eapply (freeze1_SEP' (nat_of_Z 0)); simpl.
Tactic Notation "freeze1_SEP" constr(n) constr(m) constr(k) constr(p) constr(q) :=
  (gather_SEP n m k p q); eapply (freeze1_SEP' (nat_of_Z 0)); simpl.

(*******************freezing a list of mpreds ******************************)

Fixpoint freezelist_nth (l: list nat) (al: list mpred): (list mpred) * (list mpred) :=
 match l with
 | nil => (nil,al)
 | (n::l') => let (xs, ys) := freezelist_nth l' al
              in (nth n ys emp::xs, delete_nth n ys)
 end.
Lemma FRZL_ax ps: FRZL ps = fold_right_sepcon ps.
Proof. intros. apply pred_ext. apply Freezer.FRZL2. apply Freezer.FRZL1. Qed.

Lemma fold_right_sepcon_deletenth: forall n (l: list mpred),
  fold_right_sepcon l = nth n l emp * fold_right_sepcon (delete_nth n l).
Proof.
  induction n; destruct l; simpl. rewrite sepcon_emp; trivial.
  reflexivity.
  rewrite sepcon_emp; trivial.
  rewrite IHn.
  do 2 rewrite <- sepcon_assoc. rewrite (sepcon_comm m). trivial.
Qed.
Lemma fold_right_sepcon_deletenth': forall n (l:list (LiftEnviron mpred)),
  @fold_right (environ -> mpred) (environ -> mpred) sepcon emp l =
  nth n l emp * fold_right sepcon emp (delete_nth n l).
Proof.
  induction n; destruct l; simpl. rewrite sepcon_emp; trivial.
  reflexivity.
  rewrite sepcon_emp; trivial.
  rewrite IHn; clear IHn. extensionality. simpl.
  do 2 rewrite <- sepcon_assoc. rewrite (sepcon_comm (l x)). trivial.
Qed.

Lemma freeze_SEP':
 forall l Espec {cs: compspecs} Delta P Q  R c Post xs ys,
 (xs, ys) = freezelist_nth l R ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (FRZL xs:: ys)))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros. subst.
eapply semax_pre; try eassumption.
apply andp_left2. unfold PROPx. normalize.
unfold LOCALx. apply derives_refl'.
f_equal. unfold SEPx. rewrite FRZL_ax. clear - H.
generalize dependent xs. generalize dependent ys.
clear.
induction l; intros. simpl in *. inv H. extensionality x. simpl. rewrite emp_sepcon; trivial.
simpl in H. remember (freezelist_nth l R). destruct p. inv H.
specialize (IHl _ _ (eq_refl _)). rewrite IHl. clear IHl.
extensionality. simpl.
rewrite (sepcon_comm (nth a l1 emp)). repeat rewrite sepcon_assoc. f_equal.
apply fold_right_sepcon_deletenth.
Qed.

Lemma map_delete_nth {A B} (f:A->B): forall n l, delete_nth n (map f l) = map f (delete_nth n l).
Proof.
  induction n; intros; destruct l; simpl; trivial.
  rewrite IHn. trivial.
Qed.

Fixpoint my_nth {A} (n : nat) (l : list A) (default : A) {struct l} : A :=
  match n with
  | 0%nat => match l with
             | [] => default
             | x :: _ => x
             end
  | S m => match l with
           | [] => default
           | _ :: t => my_nth m t default
           end
  end.

Lemma my_nth_nth {A}: forall n l (d:A), my_nth n l d = nth n l d.
Proof.
  induction n; destruct l; intros; simpl; trivial. Qed.

Fixpoint my_delete_nth {A} (n:nat) (xs:list A) : list A :=
 match n with
  | 0%nat => match xs with
             | [] => []
             | _ :: ys => ys
             end
  | S n' => match xs with
            | [] => []
            | y :: ys => y :: my_delete_nth n' ys
            end
  end.

Lemma my_delete_nth_delete_nth {A}: forall n (l:list A), my_delete_nth n l = delete_nth n l.
Proof. induction n; destruct l; intros; simpl; trivial. Qed.

Fixpoint my_freezelist_nth (l: list nat) (al: list mpred): (list mpred) * (list mpred) :=
 match l with
 | nil => (nil,al)
 | (n::l') => let (xs, ys) := my_freezelist_nth l' al
              in (my_nth n ys emp::xs, my_delete_nth n ys)
 end.
Lemma my_freezelist_nth_freezelist_nth: forall l al,
  my_freezelist_nth l al = freezelist_nth l al.
Proof. (*unfold my_freezelist_nth, freezelist_nth. *)
  induction l; simpl; intros; trivial.
  rewrite IHl; clear IHl.
  remember (freezelist_nth l al) as F. destruct F.
  rewrite my_nth_nth, my_delete_nth_delete_nth; trivial.
Qed.
(*Variant if l is monotonically decreasing
Fixpoint new_freezelist_nth (l: list nat) (al: list mpred): (list mpred) * (list mpred) :=
 match l with
 | nil => (nil,al)
 | (n::l') => let (xs, ys) := new_freezelist_nth l' (my_delete_nth n al)
              in (my_nth n al emp::xs, ys)
 end.*)

Lemma freeze_SEP'':
 forall l Espec {cs: compspecs} Delta P Q  R c Post xs ys,
 (xs, ys) = my_freezelist_nth l R ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (FRZL xs:: ys)))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof. intros. rewrite my_freezelist_nth_freezelist_nth in H.
  eapply freeze_SEP'; eassumption.  Qed.

Ltac freeze L name :=
  eapply (freeze_SEP'' (map nat_of_Z L));
  first [solve [reflexivity] |
         match goal with
           | |- semax _ (PROPx _ (LOCALx _ (SEPx ((FRZL ?xs) :: _)))) _ _ =>
           let D := fresh name in
           set (D:=xs);
(*           hnf in D;*)
           change xs with (@abbreviate (list mpred) xs) in D;
           simpl nat_of_Z; unfold my_delete_nth
         end].

(****************************************************************************)

Lemma flatten_emp_in_mpreds':
  forall n (R: list mpred),
   nth_error R n = Some emp ->
   SEPx R = SEPx (firstn n R ++ skipn (S n) R).
Proof.
unfold SEPx. intros. extensionality rho.
revert R H. clear.
induction n; destruct R; intros.
+ inv H.
+ simpl nth_error in H. inv H. simpl. apply emp_sepcon.
+ reflexivity.
+ inv H.
  specialize (IHn _ H1). clear H1. simpl firstn.
  change (m :: firstn n R) with (app (m::nil) (firstn n R)).
  rewrite app_ass. unfold app at 1.
  simpl; f_equal; auto.
Qed.

Lemma flatten_emp_in_SEP':
  forall n P Q (R: list mpred) R',
   nth_error R n = Some emp ->
   R' = firstn n R ++ skipn (S n) R ->
   PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q (SEPx R')).
Proof.
intros.
f_equal. f_equal. subst R'.
 apply flatten_emp_in_mpreds'. trivial.
Qed.
(*
Ltac flatten_emp_in_mpreds RR :=
 match RR with
 | (SEPx (?R)) =>
   match R with context [emp :: ?R'] =>
      let n := constr:(length R - Datatypes.S (length R'))%nat in
      let n' := eval lazy beta zeta iota delta in n in
      erewrite(@flatten_emp_in_mpreds' n' R _ (eq_refl _));
      [ |
        let RR := fresh "RR" in set (RR := R);
        unfold firstn, app, skipn; subst RR; cbv beta iota;
        apply eq_refl
      ]
   end
 end.

Ltac flatten_emp :=
  match goal with
  | |- semax _ ?PQR _ _ => flatten_emp_in_SEP PQR
  | |-  ?PQR |-- _ => first [flatten_emp_in_SEP PQR |
                             flatten_emp_in_mpreds PQR ]
end.*)


Ltac flatten_emp_in_SEP PQR :=
 match PQR with
 | PROPx ?P (LOCALx ?Q (SEPx (?R))) =>
   match R with context [emp :: ?R'] =>
      let n := constr:((length R - Datatypes.S (length R'))%nat) in
      let n' := eval lazy beta zeta iota delta in n in
      erewrite(@flatten_emp_in_SEP' n' P Q R _ (eq_refl _));
      [ |
        let RR := fresh "RR" in set (RR := R);
        unfold firstn, app, skipn; subst RR; cbv beta iota;
        apply eq_refl
      ]
   end
 end.

Ltac flatten_emp :=
  match goal with
  | |- semax _ ?PQR _ _ => flatten_emp_in_SEP PQR
  | |-  ?PQR |-- _ => flatten_emp_in_SEP PQR
end.

(*Thawing a freezer results in the sepcon product of the frozen items.*)

(*Tactic requires the resulting goal to be normalized manually.*)
Ltac thaw' name :=
  rewrite (FRZL_ax name); unfold name, abbreviate; clear name.

(*add simplification of the list operations inside the freezer,
   flatten the sepcon, and eliminate the emp term*)
Ltac thaw name :=
  thaw' name; simpl nat_of_Z; unfold my_delete_nth, my_nth, fold_right_sepcon;
  repeat flatten_sepcon_in_SEP; repeat flatten_emp.

(************************ Ramification ************************)

Inductive split_FRZ_in_SEP: list mpred -> list mpred -> list mpred -> Prop :=
| split_FRZ_in_SEP_nil: split_FRZ_in_SEP nil nil nil
| split_FRZ_in_SEP_FRZ: forall R R' RF F, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (FRZ F :: R) R' (FRZ F :: RF)
| split_FRZ_in_SEP_FRZL: forall R R' RF F, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (FRZL F :: R) R' (FRZL F :: RF)
| split_FRZ_in_SEP_FRZR: forall R R' RF L G w, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (@FRZR L G w :: R) R' (@FRZR L G w :: RF)
| split_FRZ_in_SEP_other: forall R R' RF R0, split_FRZ_in_SEP R R' RF -> split_FRZ_in_SEP (R0 :: R) (R0 :: R') RF.

Ltac prove_split_FRZ_in_SEP :=
  solve [
    repeat first
    [ simple apply split_FRZ_in_SEP_nil
    | simple apply split_FRZ_in_SEP_FRZ
    | simple apply split_FRZ_in_SEP_FRZL
    | simple apply split_FRZ_in_SEP_FRZR
    | simple apply split_FRZ_in_SEP_other]].

Lemma split_FRZ_in_SEP_spec: forall R R' RF,
  split_FRZ_in_SEP R R' RF ->
  fold_right_sepcon R = fold_right_sepcon R' * fold_right_sepcon RF.
Proof.
  intros.
  induction H.
  + simpl.
    rewrite sepcon_emp; auto.
  + simpl.
    rewrite IHsplit_FRZ_in_SEP.
    apply pred_ext; cancel.
  + simpl.
    rewrite IHsplit_FRZ_in_SEP.
    apply pred_ext; cancel.
  + simpl.
    rewrite IHsplit_FRZ_in_SEP.
    apply pred_ext; cancel.
  + simpl.
    rewrite IHsplit_FRZ_in_SEP.
    apply pred_ext; cancel.
Qed.

Lemma localize: forall R_L Espec {cs: compspecs} Delta P Q R R_FR R_G c Post,
  split_FRZ_in_SEP R R_G R_FR ->
  (let FR_L := @abbreviate _ R_L in
   let FR_G := @abbreviate _ R_G in
   exists  (w: FRZRw FR_L FR_G),
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (R_L ++ @FRZR FR_L FR_G w :: R_FR)))) c Post) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros.
  destruct H0 as [? ?].
  eapply semax_pre; [clear H0 | exact H0].
  apply split_FRZ_in_SEP_spec in H.
  apply andp_left2.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  rewrite H.
  rewrite fold_right_sepcon_app.
  simpl.
  cancel.
  apply Freezer.FRZR1.
Qed.

Ltac unfold_app :=
change (@app mpred)
  with (fix app (l m : list mpred) {struct l} : list mpred :=
  match l with
  | nil => m
  | cons a l1 => cons a (app l1 m)
  end);
change (@app Prop)
  with (fix app (l m : list Prop) {struct l} : list Prop :=
  match l with
  | nil => m
  | cons a l1 => cons a (app l1 m)
  end);
cbv beta iota.

Ltac localize R_L :=
  eapply (localize R_L); [prove_split_FRZ_in_SEP |];
  let FR_L := fresh "RamL" in
  let FR_G := fresh "RamG" in
  intros FR_L FR_G;
  eexists;
  unfold_app.

Lemma unlocalize_aux: forall R_G2 R R_FR R_L1 R_G1 R_L2 F w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: (fold_right_sepcon R_G1) |-- fold_right_sepcon R_L1 * F), w = @Freezer.FRZRw_constr _ _ _ H) ->
  F |-- fold_right_sepcon R_L2 -* fold_right_sepcon R_G2 ->
  fold_right_sepcon R |-- fold_right_sepcon (R_G2 ++ R_FR).
Proof.
  intros.
  apply split_FRZ_in_SEP_spec in H.
  rewrite H.
  rewrite fold_right_sepcon_app.
  simpl.
  cancel.
  destruct H0 as [? ?]; subst.
  apply Freezer.FRZR2.
  auto.
Qed.

Lemma unlocalize_triple: forall R_G2 Espec {cs: compspecs} Delta P Q R R_FR R_L1 R_G1 R_L2 c Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: fold_right_sepcon R_G1 |-- fold_right_sepcon R_L1 * (fold_right_sepcon R_L2 -* fold_right_sepcon R_G2)), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR)))) c Post) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros.
  eapply semax_pre; [clear H1 | exact (H1 I)].
  apply andp_left2.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  eapply unlocalize_aux; eauto.
Qed.

Lemma unlocalize_derives_canon: forall R_G2 Delta P Q R R_FR R_L1 R_G1 R_L2 Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: (fold_right_sepcon R_G1) |-- fold_right_sepcon R_L1 * (fold_right_sepcon R_L2 -* fold_right_sepcon R_G2)), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR))) |-- Post) ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
  intros.
  eapply derives_trans; [clear H1 | exact (H1 I)].
  apply andp_derives; auto.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  eapply unlocalize_aux; eauto.
Qed.

Lemma unlocalize_derives_unlift: forall R_G2 Pre R R_FR R_L1 R_G1 R_L2 Post w,
  construct_fold_right_sepcon Pre R ->
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  (exists (H: (fold_right_sepcon R_G1) |-- fold_right_sepcon R_L1 * (fold_right_sepcon R_L2 -* fold_right_sepcon R_G2)), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> fold_left_sepconx (R_G2 ++ R_FR) |-- Post) ->
  Pre |-- Post.
Proof.
  intros.
  apply construct_fold_right_sepcon_spec in H.
  subst Pre.
  eapply derives_trans; [clear H2 | exact (H2 I)].
  rewrite fold_left_sepconx_eq.
  eapply unlocalize_aux; eauto.
Qed.

Inductive ramif_frame_gen: mpred -> mpred -> Prop :=
| ramif_frame_gen_refl: forall P, ramif_frame_gen P P
| ramif_frame_gen_prop: forall (Pure: Prop) P Q, Pure -> ramif_frame_gen P (imp (prop Pure) Q) -> ramif_frame_gen P Q
| ramif_frame_gen_allp: forall {A: Type} (x: A) P Q, (forall x: A, ramif_frame_gen (P x) (Q x)) -> ramif_frame_gen (allp P) (Q x).

Ltac prove_ramif_frame_gen_rec wit :=
  match wit with
  | pair ?wit0 ?x =>
      prove_ramif_frame_gen_rec wit0;
      match goal with
      | |- ramif_frame_gen _ ?P => super_pattern P x
      end;
      apply (ramif_frame_gen_allp x);
      clear dependent x;
      intros x
  | _ =>
      match goal with
      | |- ramif_frame_gen _ ?P => super_pattern P wit
      end;
      apply (ramif_frame_gen_allp wit);
      clear dependent wit;
      intros wit
  end.

Ltac prove_ramif_frame_gen wit :=
  prove_ramif_frame_gen_rec wit;
  apply ramif_frame_gen_refl.

Ltac conj_gen assu :=
  match assu with
  | pair ?assu0 ?a => let r := conj_gen assu0 in constr:(conj r a)
  | _ => constr:(assu)
  end.

Ltac prove_ramif_frame_gen_prop assu :=
  let H := conj_gen assu in
  let Pure := type of H in
    apply (ramif_frame_gen_prop Pure _ _ H).

Lemma ramif_frame_gen_spec: forall P Q, ramif_frame_gen P Q -> P |-- Q.
Proof.
  intros.
  induction H.
  + apply derives_refl.
  + apply imp_andp_adjoint in IHramif_frame_gen.
    eapply derives_trans; [| apply IHramif_frame_gen].
    apply andp_right; auto.
    apply prop_right; auto.
  + apply (allp_left _ x).
    apply H0.
Qed.

Lemma unlocalizeQ_triple: forall R_G2 Espec {cs: compspecs} Delta P Q R R_FR R_L1 R_G1 R_L2 F c Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  ramif_frame_gen F (wand (fold_right_sepcon R_L2) (fold_right_sepcon R_G2)) ->
  (exists (H: (fold_right_sepcon R_G1) |-- sepcon (fold_right_sepcon R_L1) F), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR)))) c Post) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
  intros.
  eapply semax_pre; [clear H2 | exact (H2 I)].
  apply andp_left2.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  apply ramif_frame_gen_spec in H0; auto.
  eapply unlocalize_aux; eauto.
Qed.

Lemma unlocalizeQ_derives_canon: forall R_G2 Delta P Q R R_FR R_L1 R_G1 R_L2 F Post w,
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  ramif_frame_gen F (wand (fold_right_sepcon R_L2) (fold_right_sepcon R_G2)) ->
  (exists (H: (fold_right_sepcon R_G1) |-- sepcon (fold_right_sepcon R_L1) F), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx (R_G2 ++ R_FR))) |-- Post) ->
  local (tc_environ Delta) && PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
  intros.
  eapply derives_trans; [clear H2 | exact (H2 I)].
  apply andp_derives; auto.
  apply andp_derives; auto.
  apply andp_derives; auto.
  unfold SEPx; intro.
  apply ramif_frame_gen_spec in H0; auto.
  eapply unlocalize_aux; eauto.
Qed.

Lemma unlocalizeQ_derives_unlift: forall R_G2 Pre R R_FR R_L1 R_G1 R_L2 F Post w,
  construct_fold_right_sepcon Pre R ->
  split_FRZ_in_SEP R R_L2 (@FRZR R_L1 R_G1 w :: R_FR) ->
  ramif_frame_gen F (wand (fold_right_sepcon R_L2) (fold_right_sepcon R_G2)) ->
  (exists (H: (fold_right_sepcon R_G1) |-- sepcon (fold_right_sepcon R_L1) F), w = @Freezer.FRZRw_constr _ _ _ H) ->
  (@abbreviate _ (fun _ _ => True) R_L1 R_G1 -> fold_left_sepconx (R_G2 ++ R_FR) |-- Post) ->
  Pre |-- Post.
Proof.
  intros.
  apply construct_fold_right_sepcon_spec in H.
  subst Pre.
  eapply derives_trans; [clear H3 | exact (H3 I)].
  apply ramif_frame_gen_spec in H1; auto.
  rewrite fold_left_sepconx_eq.
  eapply unlocalize_aux; eauto.
Qed.

Ltac unlocalize_plain R_G2 :=
  match goal with
  | |- @semax _ _ _ _ _ _ =>
          eapply (unlocalize_triple R_G2)
  | |- local (tc_environ _) && _ |-- _ =>
          eapply (unlocalize_derives_canon R_G2)
  | |- @derives _ Nveric _ _ =>
          eapply (unlocalize_derives_unlift R_G2); [construct_fold_right_sepcon | ..]
  end;
  [ prove_split_FRZ_in_SEP
  | refine (ex_intro _ _ eq_refl);
    match goal with
    | |- fold_right_sepcon ?R_G1 |-- sepcon (fold_right_sepcon ?R_L1) _ =>
           unfold abbreviate in R_L1, R_G1; unfold R_L1, R_G1; clear R_L1 R_G1
    end;
    rewrite <- !fold_left_sepconx_eq;
    unfold fold_left_sepconx
  | match goal with
    | |- _ ?R_L1 ?R_G1 -> _ =>
      intros _;
      clear R_L1 R_G1;
      unfold_app
    end;
    try unfold fold_left_sepconx
  ].

Ltac unlocalize_wit R_G2 wit tac :=
  match goal with
  | |- @semax _ _ _ _ _ _ =>
          eapply (unlocalizeQ_triple R_G2)
  | |- local (tc_environ _) && _ |-- _ =>
          eapply (unlocalizeQ_derives_canon R_G2)
  | |- @derives _ Nveric _ _ =>
          eapply (unlocalizeQ_derives_unlift R_G2); [construct_fold_right_sepcon | ..]
  end;
  [ prove_split_FRZ_in_SEP
  | rewrite <- !fold_right_sepconx_eq;
    unfold fold_right_sepconx;
    tac;
    prove_ramif_frame_gen wit
  | refine (ex_intro _ _ eq_refl);
    match goal with
    | |- fold_right_sepcon ?R_G1 |-- sepcon (fold_right_sepcon ?R_L1) _ =>
           unfold abbreviate in R_L1, R_G1; unfold R_L1, R_G1; clear R_L1 R_G1
    end;
    rewrite <- !fold_right_sepconx_eq;
    unfold fold_right_sepconx
  | match goal with
    | |- _ ?R_L1 ?R_G1 -> _ =>
      intros _;
      clear R_L1 R_G1;
      unfold_app
    end;
    try unfold fold_left_sepconx
  ].

Tactic Notation "unlocalize" constr(R_G2) :=
  unlocalize_plain R_G2.

Tactic Notation "unlocalize" constr(R_G2) "using" constr(wit) :=
  unlocalize_wit R_G2 wit idtac.

Tactic Notation "unlocalize" constr(R_G2) "using" constr(wit) "assuming" constr(assu) :=
  let tac := prove_ramif_frame_gen_prop assu in
  unlocalize_wit R_G2 wit tac.
