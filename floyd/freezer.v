Require Import VST.floyd.base2.
Require Import VST.floyd.canon.
Require Import VST.floyd.entailer.
Require Import Coq.Lists.List.
Export ListNotations.
Require Import VST.floyd.client_lemmas.

Module Type FREEZER.
Parameter FRZ : mpred -> mpred.
Parameter FRZ1: forall p, p |-- FRZ p.
Parameter FRZ2: forall p, FRZ p |-- p.

Parameter FRZL : list mpred -> mpred.
Parameter FRZL1: forall ps, (fold_right sepcon emp ps) |-- FRZL ps.
Parameter FRZL2: forall ps, FRZL ps |-- fold_right sepcon emp ps.
End FREEZER.

Module Freezer : FREEZER.
Definition FRZ (p: mpred) := p.
Lemma FRZ1 p: p |-- FRZ p. apply derives_refl. Qed.
Lemma FRZ2 p: FRZ p |-- p. apply derives_refl. Qed.

Definition FRZL (ps:list mpred): mpred := fold_right sepcon emp ps.
Lemma FRZL1 ps: (fold_right_sepcon ps) |-- FRZL ps. apply derives_refl. Qed.
Lemma FRZL2 ps: FRZL ps |-- fold_right_sepcon ps. apply derives_refl. Qed.
End Freezer.

Notation FRZ := Freezer.FRZ.
Notation FRZL := Freezer.FRZL.

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
  fold_right_sepcon l = (nth n l emp * fold_right_sepcon (delete_nth n l))%logic.
Proof.
  induction n; destruct l; simpl. rewrite sepcon_emp; trivial.
  reflexivity.
  rewrite sepcon_emp; trivial.
  rewrite IHn.
  do 2 rewrite <- sepcon_assoc. rewrite (sepcon_comm m). trivial.
Qed.
Lemma fold_right_sepcon_deletenth': forall n (l:list (LiftEnviron mpred)),
  @fold_right (environ -> mpred) (environ -> mpred) sepcon emp l =
  (nth n l emp * fold_right sepcon emp (delete_nth n l))%logic.
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

(*************************** depercated auxiliary lemmas and tactics ********************
(*Freezes the mpreds at positions n0, n1, .. nk, where L= [n0; n1;..;nk] (counting starts at 0)*)
Ltac freeze' L :=
  eapply (freeze_SEP' (map nat_of_Z L));
  first [solve [reflexivity] |
         simpl].

(*A variant that abbreviates the resulting freezer and introduces it as a named hypothesis*)
Ltac freezeOLD L name :=
  eapply (freeze_SEP'' (map nat_of_Z L));
  first [(*solve [apply extract_trivial_liftx_e; repeat econstructor] | *)
         solve [reflexivity] |
         match goal with
           | |- semax _ (PROPx _ (LOCALx _ (SEPx ((FRZL ?xs) :: _)))) _ _ =>
           let D := fresh name in
           set (D:=xs);
(*           hnf in D;*)
           change xs with (@abbreviate (list mpred) xs) in D;
           simpl (*mapliftx*)
         end].
(*taken from hmac_pure_lemmas*)
Lemma mapnth': forall {A B : Type} (f : A -> B) (l : list A) (d : A) (n : nat) fd,
      fd = f d -> nth n (map f l) fd = f (nth n l d).
Proof. intros; subst. apply map_nth. Qed.

Lemma thaw_SEP':
 forall n Espec {cs: compspecs} Delta P Q  R c Post xs ys,
 nth n R emp = FRZL xs ->
 delete_nth n R = ys ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (xs ++ ys)))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros. subst.
eapply semax_pre_post. 3: eassumption. 2: intros; entailer.
apply andp_left2. unfold PROPx. normalize.
unfold LOCALx. apply derives_refl'.
f_equal. unfold SEPx. clear - H.
rewrite fold_right_sepcon_app. rewrite FRZL_ax in H.
extensionality x.
rewrite (fold_right_sepcon_deletenth n), H; trivial.
Qed.
Ltac thawOLD name := rewrite (FRZL_ax name); unfold name, abbreviate; simpl; clear name.

(*List-freezers appearing in (preconditions of) semax-goals can also be thawed.
 Instead of yielding the sepcon product, the (un)frozen items are prepended to the SEP-list*)

(*Tactic that does not attempt to clear the abbreviation identifier.*)
Ltac melt' i:=
  eapply (thaw_SEP' (nat_of_Z i));
  first [(*solve [apply extract_trivial_liftx_e; repeat econstructor] | *)
         solve [reflexivity] |
         simpl].

(*Variant that attempts to clear the abbreviation identifier.*)
Ltac melt i x:=
  eapply (thaw_SEP' (nat_of_Z i));
  first [(*solve [apply extract_trivial_liftx_e; repeat econstructor] | *)
         solve [reflexivity] |
         first [simpl; clear x |
                fail 2 "The identifier "x" cannot be cleared, or is not at position "i"." ]].

*******************************************************************************)
