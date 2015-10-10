Require Import floyd.base.
Local Open Scope logic.

(* is this lemma useful? *)
Lemma exp_prop: forall A P, exp (fun x: A => prop (P x)) = prop (exists x: A, P x).
Proof.
  intros.
  apply pred_ext; normalize; intros.
  + apply prop_right; exists x; auto.
  + destruct H as [x ?].
    apply (exp_right x).
    normalize.
Qed.

Definition PROPx (P: list Prop): forall (Q: environ->mpred), environ->mpred := 
     andp (prop (fold_right and True P)).

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z) (at level 10) : logic.
Notation "'PROP' ()   z" :=   (PROPx nil z) (at level 10) : logic.
Notation "'PROP' ( )   z" :=   (PROPx nil z) (at level 10) : logic.

Definition LOCALx (Q: list (environ -> Prop)) : forall (R: environ->mpred), environ->mpred := 
                 andp (local (fold_right (`and) (`True) Q)).

Notation " 'LOCAL' ( )   z" := (LOCALx nil z)  (at level 9) : logic.
Notation " 'LOCAL' ()   z" := (LOCALx nil z)  (at level 9) : logic.

Notation " 'LOCAL' ( x ; .. ; y )   z" := (LOCALx (cons x%type .. (cons y%type nil) ..) z)
         (at level 9) : logic.

Definition SEPx: forall (R: list(environ->mpred)), environ->mpred := fold_right sepcon emp.
Arguments SEPx R _ : simpl never.

Notation " 'SEP' ( x ; .. ; y )" := (SEPx (cons x%logic .. (cons y%logic nil) ..))
         (at level 8) : logic.

Notation " 'SEP' ( ) " := (SEPx nil) (at level 8) : logic.
Notation " 'SEP' () " := (SEPx nil) (at level 8) : logic.

Lemma insert_local: forall Q1 P Q R,
  local Q1 && (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx (Q1 :: Q) (SEPx R))).
Proof.
intros. extensionality rho.
unfold PROPx, LOCALx, SEPx, local; super_unfold_lift. simpl.
apply pred_ext; autorewrite with gather_prop; normalize;
decompose [and] H; clear H.
repeat apply andp_right; auto.
apply prop_right; repeat split; auto.
apply andp_right; auto.
apply prop_right; repeat split; auto.
Qed.
Hint Rewrite insert_local:  norm2.

Lemma go_lower_lem20:
  forall QR QR',
    QR |-- QR' ->
    PROPx nil QR |-- QR'.
Proof. unfold PROPx; intros; intro rho; normalize. Qed.

Ltac go_lowerx :=
   unfold PROPx, LOCALx,SEPx, local, lift1; unfold_lift; intro rho; simpl;
   repeat rewrite andp_assoc;
   repeat ((simple apply go_lower_lem1 || apply derives_extract_prop || apply derives_extract_prop'); intro);
   try apply prop_left;
   repeat rewrite prop_true_andp by assumption;
   try apply derives_refl.

Lemma grab_tc_environ:
  forall Delta P Q R S rho,
    (tc_environ Delta rho -> (PROPx P (LOCALx Q R)) rho |-- S) ->
    (PROPx P (LOCALx (tc_environ Delta :: Q) R)) rho |-- S.
Proof.
intros.
unfold PROPx,LOCALx in *; simpl in *.
normalize.
change (!! tc_environ Delta rho && 
              local  (fold_right `and `True Q) rho && R rho |-- S).
normalize.
rewrite (prop_true_andp _ _ H0) in H.
auto.
Qed.

Fixpoint delete_nth {A} (n: nat) (xs: list A) {struct n} : list A :=
 match n, xs with
 | O, y::ys => ys
 | S n', y::ys =>y :: delete_nth n' ys
 | _ , _ => nil
 end.

Lemma grab_nth_LOCAL:
   forall n P Q R,
     (PROPx P (LOCALx Q (SEPx R))) = 
     (PROPx P (LOCALx (nth n Q (lift0 True) :: delete_nth n Q) (SEPx R))).
Proof.
intros n P Q R.
f_equal.
unfold LOCALx, local; super_unfold_lift.
f_equal.
extensionality rho;  f_equal.
revert Q; induction n; intros.
destruct Q; simpl nth. unfold delete_nth.
apply prop_ext; simpl; intuition.
simpl. auto.
destruct Q; simpl nth; unfold delete_nth; fold @delete_nth.
apply prop_ext; simpl; intuition.
simpl.
apply prop_ext.
rewrite (IHn Q).
simpl.
clear IHn.
intuition.
Qed.

Lemma grab_nth_SEP:
   forall n P Q R,
    PROPx P (LOCALx Q (SEPx R)) = (PROPx P (LOCALx Q (SEPx (nth n R emp :: delete_nth n R)))).
Proof.
intros.
f_equal. f_equal.
extensionality rho; unfold SEPx.
revert R; induction n; intros; destruct R.
simpl. rewrite sepcon_emp; auto.
simpl nth.
unfold delete_nth.
auto.
simpl.
rewrite sepcon_emp; auto.
change (fold_right sepcon emp (m :: R) rho)
  with (m rho * fold_right sepcon emp R rho).
rewrite IHn.
simpl.
repeat rewrite <- sepcon_assoc.
f_equal.
apply sepcon_comm.
Qed.

Ltac find_in_list A L :=
 match L with 
  | A :: _ => constr:(O)
  | _ :: ?Y => let n := find_in_list A Y in constr:(S n)
  | nil => fail
  end.

Ltac length_of R :=
 match R with
  |  nil => constr:(O)
  |  _:: ?R1 => let n := length_of R1 in constr:(S n)
 end.

Fixpoint insert {A} (n: nat) (x: A) (ys: list A) {struct n} : list A :=
 match n with
 | O => x::ys
 | S n' => match ys with nil => x::ys | y::ys' => y::insert n' x ys' end
end.

(* Note: in the grab_indexes function,
  it's important that the {struct} induction NOT be on xs, because
  that list might not be concrete all the way to the end, where the ns list will be concrete.
  Thus we do it this particular way.  *)
Fixpoint  grab_indexes' {A} (ns: list (option nat)) (xs: list A) {struct ns} : list A * list A :=
match ns, xs with
| nil, xs => (nil, xs)
| _, nil => (nil,nil)
| Some n::ns', x::xs' => let (al,bl) := grab_indexes' ns' xs'
                               in (insert n x al, bl)
| None :: ns', x::xs' => let (al,bl) := grab_indexes' ns' xs'
                                  in (al, x::bl)
end.

Fixpoint grab_calc' (k: Z) (z: nat) (ns: list (option nat)): list (option nat) :=
match z, ns with
| O, _::ns' => Some (nat_of_Z k) :: ns'
| S z', None::ns' => None :: grab_calc' k z' ns'
| S z', Some n :: ns => Some n :: grab_calc' (k-1) z' ns
| O, nil => Some O :: nil
| S z', nil => None :: grab_calc' k z' nil
end.

Fixpoint grab_calc (k: Z) (zs: list Z) (ns: list (option nat)) : list (option nat) :=
match zs with
| nil => ns
| z::zs' => grab_calc (k+1) zs' (grab_calc' k (nat_of_Z z) ns)
end.

(* Eval compute in grab_calc 0 (3::1::5::nil) nil. *)

(* Define app_alt, just like app, so we have better control
  over which things get unfolded *)

Definition app_alt {A: Type} :=
fix app (l m : list A) : list A :=
  match l with
  | nil => m
  | a :: l1 => a :: app l1 m
  end.

Definition grab_indexes {A} (ns: list Z) (xs: list A) : list A :=
    let (al,bl) := grab_indexes' (grab_calc 0 ns nil) xs in app_alt al bl.

(* TESTING 
Variables (a b c d e f g h i j : assert).
Eval compute in grab_indexes (1::4::6::nil) (a::b::c::d::e::f::g::h::i::j::nil).
Eval compute in grab_indexes (1::6::4::nil) (a::b::c::d::e::f::g::h::i::j::nil).
*) 

Lemma fold_right_nil: forall {A B} (f: A -> B -> B) (z: B),
   fold_right f z nil = z.
Proof. reflexivity. Qed.
Hint Rewrite @fold_right_nil : norm1.
Hint Rewrite @fold_right_nil : subst.

Lemma fold_right_cons: forall {A B} (f: A -> B -> B) (z: B) x y,
   fold_right f z (x::y) = f x (fold_right f z y).
Proof. reflexivity. Qed.
Hint Rewrite @fold_right_cons : norm1.
Hint Rewrite @fold_right_cons : subst.

Lemma fold_right_and_app:
  forall (Q1 Q2: list (environ -> Prop)) rho,
   fold_right `and `True (Q1 ++ Q2) rho = 
   (fold_right `and `True Q1 rho /\  fold_right `and `True Q2 rho).
Proof.
intros.
induction Q1; simpl; auto.
apply prop_ext; intuition.
normalize. 
apply Coq.Init.Logic.I.
unfold_lift in IHQ1. unfold_lift.
rewrite IHQ1.
clear; apply prop_ext; intuition.
Qed.

Lemma fold_right_sepcon_app {A} {NA: NatDed A} {SL: SepLog A}{CA: ClassicalSep A}:
 forall P Q : list A, fold_right (@sepcon A NA SL) (@emp A NA SL) (P++Q) = 
        fold_right sepcon emp P * fold_right sepcon emp Q.
Proof.
intros; induction P; simpl.
rewrite emp_sepcon; auto.
rewrite sepcon_assoc;
f_equal; auto.
Qed.

Lemma grab_indexes_SEP : 
  forall (ns: list Z) (xs: list(environ->mpred)),   SEPx xs = SEPx (grab_indexes ns xs).
Proof.
intros.
unfold SEPx; extensionality rho.
unfold grab_indexes. change @app_alt with  @app.
forget (grab_calc 0 ns nil) as ks.
revert xs; induction ks; intro.
unfold grab_indexes'. simpl app. auto.
destruct a.
destruct xs. reflexivity.
unfold grab_indexes'.
fold @grab_indexes'.
rewrite fold_right_cons.
specialize (IHks xs).
case_eq (grab_indexes' ks xs); intros.
rewrite H in IHks.
rewrite fold_right_app.
transitivity (m rho * fold_right sepcon emp xs rho); try reflexivity.
rewrite IHks.
rewrite fold_right_app.
forget (fold_right sepcon emp l0) as P.
transitivity (fold_right sepcon P (m::l) rho). reflexivity.
clear.
revert l; induction n; intro l. reflexivity.
simpl. destruct l. simpl. auto.
simpl. rewrite <- sepcon_assoc. rewrite (sepcon_comm (m rho)).
rewrite sepcon_assoc. f_equal.
specialize (IHn l). simpl in IHn.
auto.
destruct xs. reflexivity.
unfold grab_indexes'.
fold @grab_indexes'.
rewrite fold_right_cons.
specialize (IHks xs).
case_eq (grab_indexes' ks xs); intros.
rewrite H in IHks.
simpl.
simpl in IHks; rewrite IHks.
clear.
induction l; simpl; auto.
rewrite <- IHl.
clear IHl.
repeat rewrite <- sepcon_assoc.
f_equal.
rewrite sepcon_comm; auto.
Qed.

(* The simpl_nat_of_P tactic is a complete hack,
  needed for compatibility between Coq 8.3/8.4,
  because the name of the thing to unfold varies
  between the two versions *)
Ltac simpl_nat_of_P :=
match goal with |- context [nat_of_P ?n] =>
  match n with xI _ => idtac | xO _ => idtac | xH => idtac | _ => fail end;
  let N := fresh "N" in
  set (N:= nat_of_P n);
  compute in N;
  unfold N; clear N
end.

Ltac grab_indexes_SEP ns :=
  rewrite (grab_indexes_SEP ns); 
    unfold grab_indexes; simpl grab_calc; 
   unfold grab_indexes', insert; 
   repeat simpl_nat_of_P; cbv beta iota;
   unfold app_alt; fold @app_alt.

Tactic Notation "focus_SEP" constr(a) := grab_indexes_SEP (a::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) := grab_indexes_SEP (a::b::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) := 
   grab_indexes_SEP (a::b::c::nil).
Tactic Notation "focus_SEP" constr(a) constr(b) constr(c) constr(d) := 
   grab_indexes_SEP (a::b::c::d::nil).

(* TESTING 
Variables (a b c d e f g h i j : assert).
Goal (SEP (a;b;c;d;e;f;g;h;i;j) = SEP (b;d;a;c;e;f;g;h;i;j)).
focus_SEP 1 3.
auto.
Qed.
Goal (SEP (a;b;c;d;e;f;g;h;i;j) = SEP (d;b;a;c;e;f;g;h;i;j)).
focus_SEP 3 1. 
auto.
Qed.

*)

Lemma semax_post0:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   (R' |-- R) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
intros. apply andp_left2; auto.
apply H.
Qed.

Lemma local_unfold: forall P rho, local P rho = !! (P rho).
Proof. reflexivity. Qed.
Hint Rewrite local_unfold : norm2.

Lemma lower_sepcon:
  forall P Q rho, @sepcon (environ->mpred) _ _ P Q rho = sepcon (P rho) (Q rho).
Proof. reflexivity. Qed.
Lemma lower_andp:
  forall P Q rho, @andp (environ->mpred) _ P Q rho = andp (P rho) (Q rho).
Proof. reflexivity. Qed.
Hint Rewrite lower_sepcon lower_andp : norm2.

Lemma lift_prop_unfold: 
   forall P z,  @prop (environ->mpred) _ P z = @prop mpred Nveric P.
Proof.  reflexivity. Qed.
Hint Rewrite lift_prop_unfold: norm2.

Lemma andp_unfold: forall (P Q: environ->mpred) rho,
  @andp (environ->mpred) _ P Q rho = @andp mpred Nveric (P rho) (Q rho).
Proof. reflexivity. Qed.
Hint Rewrite andp_unfold: norm2.

Lemma refold_andp:
  forall (P Q: environ -> mpred),
     (fun rho: environ => P rho && Q rho) = (P && Q).
Proof. reflexivity. Qed.
Hint Rewrite refold_andp : norm2.

Lemma exp_unfold : forall A P rho,
 @exp (environ->mpred) _ A P rho = @exp mpred Nveric A (fun x => P x rho).
Proof.
intros. reflexivity. 
Qed.
Hint Rewrite exp_unfold: norm2.

Lemma semax_pre_simple:
 forall P' Espec {cs: compspecs} Delta P c R,
     (local (tc_environ Delta) && P |-- P') ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; eauto.
intros; apply andp_left2; auto.
Qed.

Lemma semax_pre0:
 forall P' Espec  {cs: compspecs} Delta P c R,
     P |-- P' ->
     @semax cs Espec Delta P' c R  -> 
     @semax cs Espec Delta P c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
 apply andp_left2; auto.
Qed.

Lemma semax_pre:
 forall P' Espec  {cs: compspecs} Delta P1 P2 P3 c R,
     (PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3))) |-- P' ->
     @semax cs Espec Delta P' c R  -> 
     @semax cs Espec Delta (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
 rewrite insert_local. auto.
Qed.

Lemma semax_frame_PQR:
  forall Q2 R2 Espec {cs: compspecs} Delta R1 P Q P' Q' R1' c,
     closed_wrt_modvars c (LOCALx Q2 (SEPx R2)) ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c 
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R1')))) ->
     @semax cs Espec Delta (PROPx P (LOCALx (Q++Q2) (SEPx (R1++R2)))) c 
                     (normal_ret_assert (PROPx P' (LOCALx (Q'++Q2) (SEPx (R1'++R2))))).
Proof.
intros.
replace (PROPx P (LOCALx (Q++Q2) (SEPx (R1 ++ R2))))
   with (PROPx P (LOCALx Q (SEPx (R1))) * (LOCALx Q2 (SEPx R2))).
eapply semax_post0; [ | apply semax_frame; try eassumption].
intros ek vl rho.
unfold frame_ret_assert, normal_ret_assert.
normalize.
 unfold PROPx, SEPx, LOCALx, local, lift1.
normalize.
rewrite fold_right_sepcon_app.
normalize; autorewrite with norm1 norm2; normalize.
rewrite prop_true_andp; auto.
rewrite fold_right_and_app; split; auto.
clear.
extensionality rho.
simpl.
unfold PROPx, LOCALx, local, lift1, SEPx.
rewrite fold_right_sepcon_app.
simpl. normalize.
f_equal.
rewrite <- andp_assoc.
f_equal.
rewrite fold_right_and_app.
apply pred_ext; normalize. destruct H; normalize.
Qed.

Lemma semax_frame1:
 forall {Espec: OracleKind} {cs: compspecs} QFrame Frame Delta Delta1
     P Q c R P1 Q1 R1 P2 Q2 R2,
    semax Delta1 (PROPx P1 (LOCALx Q1 (SEPx R1))) c 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    Delta1 = Delta ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
    PROPx P1 (LOCALx (Q1++QFrame) (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c (LOCALx QFrame (SEPx Frame)) ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) c 
                      (normal_ret_assert (PROPx P2 (LOCALx (Q2++QFrame) (SEPx (R2++Frame))))).
Proof.
intros. subst.
eapply semax_pre.
apply H1.
apply semax_frame_PQR; auto.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   (forall ek vl, local (tc_environ (exit_tycon c Delta ek)) &&  R' ek vl |-- R ek vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
Qed.

Lemma semax_post_flipped:
  forall (R' : ret_assert) Espec {cs: compspecs} (Delta : tycontext) (R : ret_assert)
         (P : environ->mpred) (c : statement),
        @semax cs Espec Delta P c R' -> 
       (forall (ek : exitkind) (vl : option val),
        local (tc_environ (exit_tycon c Delta ek)) && R' ek vl |-- R ek vl) ->
       @semax cs Espec Delta P c R.
Proof. intros; eapply semax_post; eassumption. Qed.


Lemma semax_post': forall R' Espec {cs: compspecs} Delta R P c,
           R' |-- R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros. eapply semax_post; eauto. intros. apply andp_left2.
  intro rho; unfold normal_ret_assert; normalize.
 autorewrite with norm1 norm2; normalize.
Qed.

Lemma sequential:
  forall Espec {cs: compspecs} Delta P c Q,
        @semax cs Espec Delta P c (normal_ret_assert (Q EK_normal None)) ->
          @semax cs Espec Delta P c Q.
intros. eapply semax_post; eauto.
 intros. intro rho. unfold local,lift1; simpl.
 unfold normal_ret_assert; simpl.
 normalize.
Qed.

Lemma sequential': 
    forall Q Espec {cs: compspecs} Delta P c R,
               @semax cs Espec Delta P c (normal_ret_assert Q) -> 
               @semax cs Espec Delta P c (overridePost Q R).
Proof.
intros.
apply semax_post with (normal_ret_assert Q); auto.
intros.
unfold normal_ret_assert, overridePost.
normalize.
rewrite if_true; auto.
apply andp_left2; auto.
Qed.

Lemma semax_seq': 
 forall Espec {cs: compspecs} Delta P c1 P' c2 Q, 
         @semax cs Espec Delta P c1 (normal_ret_assert P') ->
         @semax cs Espec(update_tycon Delta c1) P' c2 Q ->
         @semax cs Espec Delta P (Ssequence c1 c2) Q.
Proof.
 intros. apply semax_seq with P'; auto.
 apply sequential'. auto. 
Qed.

Lemma semax_frame_seq:
 forall {Espec: OracleKind} {cs: compspecs} QFrame Frame Delta 
     P Q c1 c2 R P1 Q1 R1 P2 Q2 R2 R3,
    semax Delta (PROPx P1 (LOCALx Q1 (SEPx R1))) c1 
                      (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
    PROPx P1 (LOCALx (Q1++QFrame) (SEPx (R1 ++ Frame))) ->
    closed_wrt_modvars c1 (LOCALx QFrame (SEPx Frame)) ->
    semax (update_tycon Delta c1) 
         (PROPx P2 (LOCALx (Q2++QFrame) (SEPx (R2 ++ Frame)))) c2 R3 ->
    semax Delta (PROPx P (LOCALx Q (SEPx R))) (Ssequence c1 c2) R3.
Proof.
intros.
eapply semax_seq'.
eapply semax_pre.
apply H0.
apply semax_frame_PQR; auto.
apply H.
apply H2.
Qed.

Lemma derives_frame_PQR:
  forall R1 R2 P Q P' Q' R1',
  PROPx P (LOCALx Q (SEPx R1)) |-- PROPx P' (LOCALx Q' (SEPx R1')) ->
  PROPx P (LOCALx Q (SEPx (R1++R2))) |-- PROPx P' (LOCALx Q' (SEPx (R1'++R2))).
Proof.
intros.
eapply derives_trans; [ | eapply derives_trans].
2: apply sepcon_derives; [ apply H | apply (derives_refl  (fold_right sepcon emp R2))].
clear H.
unfold PROPx, LOCALx, SEPx, local; super_unfold_lift; intros.
rewrite fold_right_sepcon_app.
intro rho; simpl; normalize.
unfold PROPx, LOCALx, SEPx, local; super_unfold_lift; intros.
rewrite fold_right_sepcon_app.
intro rho; simpl; normalize.
Qed.

Ltac frame_SEP' L :=  (* this should be generalized to permit framing on LOCAL part too *)
 grab_indexes_SEP L;
 match goal with
 | |- @semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ => 
  rewrite <- (firstn_skipn (length L) R); 
    simpl length; unfold firstn, skipn;
    eapply (semax_frame_PQR nil);
      [ unfold closed_wrt_modvars;  auto 50 with closed
     | ]
 | |- (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ => 
  rewrite <- (firstn_skipn (length L) R); 
    simpl length; unfold firstn, skipn;
    apply derives_frame_PQR
end.

Tactic Notation "frame_SEP" constr(a) := frame_SEP' (a::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) := frame_SEP' (a::b::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) := 
   frame_SEP' (a::b::c::nil).
Tactic Notation "frame_SEP" constr(a) constr(b) constr(c) constr(d) := 
   frame_SEP' (a::b::c::d::nil).

Lemma gather_SEP:
  forall R1 R2, 
    SEPx (R1 ++ R2) = SEPx (fold_right sepcon emp R1 :: R2).
Proof. 
intros.
unfold SEPx.
extensionality rho.
induction R1; simpl. rewrite emp_sepcon; auto.
rewrite sepcon_assoc; f_equal; auto.
Qed.

Ltac gather_SEP' L :=
   grab_indexes_SEP L;
 match goal with |- context [SEPx ?R] => 
    let r := fresh "R" in 
    set (r := (SEPx R));
    revert r;
     rewrite <- (firstn_skipn (length L) R);
      unfold length at 1 2;
      unfold firstn at 1; unfold skipn at 1;
      rewrite gather_SEP;
   unfold fold_right at 1; try  rewrite sepcon_emp;
   intro r; unfold r; clear r
 end.

Tactic Notation "gather_SEP" constr(a) := gather_SEP' (a::nil).
Tactic Notation "gather_SEP" constr(a) constr(b) := gather_SEP' (a::b::nil).
Tactic Notation "gather_SEP" constr(a) constr(b) constr(c) := 
   gather_SEP' (a::b::c::nil).
Tactic Notation "gather_SEP" constr(a) constr(b) constr(c) constr(d) := 
   gather_SEP' (a::b::c::d::nil).


Fixpoint replace_nth {A} (n: nat) (al: list A) (x: A) {struct n}: list A :=
 match n, al with
 | O , a::al => x::al
 | S n', a::al' => a :: replace_nth n' al' x
 | _, nil => nil
 end.

Fixpoint my_nth{A} (n: nat) (al: list A) (default: A) {struct n} : A :=
  (* just like nth; make a new copy, for better control of unfolding *)
match n, al with
| O, a::al' => a
| S n', a::al' => my_nth n' al' default
| _, nil => default
end.

Lemma replace_nth_replace_nth: forall {A: Type} R n {Rn Rn': A},
  replace_nth n (replace_nth n R Rn) Rn' = replace_nth n R Rn'.
Proof.
  intros.
  revert R; induction n; destruct R; simpl in *.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
Qed.

Lemma replace_nth_nth_error: forall {A:Type} R n (Rn:A), 
  nth_error R n = Some Rn ->
  R = replace_nth n R Rn.
Proof.
  intros.
  revert R H; induction n; intros; destruct R.
  + reflexivity.
  + simpl. inversion H. reflexivity.
  + inversion H.
  + inversion H. simpl.
    rewrite (IHn R) at 1; simpl; [reflexivity|exact H1].
Qed.

Lemma nth_error_replace_nth: forall {A:Type} R n (Rn Rn':A), 
  nth_error R n = Some Rn ->
  nth_error (replace_nth n R Rn') n = Some Rn'.
Proof.
  intros.
  revert R H; induction n; intros; destruct R; simpl.
  + inversion H.
  + inversion H.
    reflexivity.
  + inversion H.
  + inversion H.
    apply IHn, H1.
Qed.

Lemma map_replace_nth:
  forall {A B} (f: A -> B) n R X, map f (replace_nth n R X) = 
       replace_nth n (map f R) (f X).
Proof.
intros.
 revert R; induction n; destruct R; simpl; auto.
 f_equal; auto.
Qed.

Lemma replace_nth_commute:
  forall {A} i j R (a b: A),
   i <> j ->
   replace_nth i (replace_nth j R b) a =
   replace_nth j (replace_nth i R a) b.
Proof.
intros.
rename i into i'. rename j into j'. rename R into R'.
assert (forall i j R (a b: A),
             (i<j)%nat -> 
              replace_nth i (replace_nth j R b) a = replace_nth j (replace_nth i R a) b). {
induction i; destruct j, R; simpl; intros; auto; try omega.
f_equal. apply IHi. omega.
}
assert (i'<j' \/ i'>j')%nat by omega.
clear H.
destruct H1.
apply H0; auto.
symmetry; apply H0; auto.
Qed.

Lemma nth_error_replace_nth':
  forall {A} i j R (a:A),
  (i <> j)%nat -> nth_error (replace_nth i R a) j = nth_error R j.
Proof.
induction i; destruct j,R; intros; simpl; auto.
contradiction H; auto.
Qed.

Lemma replace_SEP':
 forall n R' Espec {cs: compspecs} Delta P Q Rs c Post,
 (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (my_nth n Rs TT ::  nil)))) |-- R' ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (replace_nth n Rs R')))) c Post ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx Rs))) c Post.
Proof.
intros.
eapply semax_pre; [ | apply H0].
clear - H.
unfold PROPx, LOCALx, SEPx in *; intro rho; specialize (H rho).
unfold local, lift1 in *.
simpl in *; unfold_lift; unfold_lift in H.
normalize.
rewrite prop_true_andp in H by auto.
rewrite prop_true_andp in H by auto.
destruct H1; normalize.
clear - H.
rewrite sepcon_emp in H.

revert Rs H; induction n; destruct Rs; simpl ; intros; auto;
apply sepcon_derives; auto.
Qed.

Lemma replace_SEP'':
 forall n R' P Q Rs Post,
 (PROPx P (LOCALx Q (SEPx (my_nth n Rs TT ::  nil)))) |-- R' ->
 PROPx P (LOCALx Q (SEPx (replace_nth n Rs R'))) |-- Post ->
 PROPx P (LOCALx Q (SEPx Rs)) |-- Post.
Proof.
intros.
eapply derives_trans; [ | apply H0].
clear - H.
unfold PROPx, LOCALx, SEPx in *; intro rho; specialize (H rho).
unfold local, lift1 in *.
simpl in *; unfold_lift; unfold_lift in H.
normalize.
rewrite prop_true_andp in H by auto.
rewrite prop_true_andp in H by auto.
clear - H.
rewrite sepcon_emp in H.
revert Rs H; induction n; destruct Rs; simpl ; intros; auto;
apply sepcon_derives; auto.
Qed.

Ltac replace_SEP n R :=
  first [apply (replace_SEP' (nat_of_Z n) R) | apply (replace_SEP'' (nat_of_Z n) R)];
  unfold my_nth,replace_nth; simpl nat_of_Z;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota.

Ltac replace_in_pre S S' :=
 match goal with |- @semax _ _ _ ?P _ _ =>
  match P with context C[S] =>
     let P' := context C[S'] in 
      apply semax_pre with P'; [ | ]
  end
 end.

Lemma semax_extract_PROP_True:
  forall Espec {cs: compspecs} Delta (PP: Prop) P QR c Post,
        PP ->
        @semax cs Espec Delta (PROPx P QR) c Post -> 
       @semax cs Espec Delta (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply semax_pre_simple with (PROPx P QR); auto.
clear.
intro rho; unfold PROPx in *; simpl. normalize.
destruct H; normalize.
 autorewrite with norm1 norm2; normalize.
Qed.

Lemma semax_extract_PROP:
  forall Espec {cs: compspecs} Delta (PP: Prop) P QR c Post,
       (PP -> @semax cs Espec Delta (PROPx P QR) c Post) -> 
       @semax cs Espec Delta (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply semax_pre_simple with (!!PP && PROPx P QR).
intro rho; unfold PROPx in *; simpl; normalize.
destruct H0; normalize.
autorewrite with norm1 norm2; normalize.
apply semax_extract_prop.
auto.
Qed.

Lemma PROP_later_derives:
 forall P QR QR', QR |-- |>QR' ->
    PROPx P QR |-- |> PROPx P QR'.
Proof.
intros.
unfold PROPx.
normalize.
Qed.

Lemma LOCAL_later_derives:
 forall Q R R', R |-- |>R' -> LOCALx Q R |-- |> LOCALx Q R'.
Proof.
unfold LOCALx; intros; normalize.
rewrite later_andp.
apply andp_derives; auto.
apply now_later.
Qed.

Lemma SEP_later_derives:
  forall P Q P' Q', 
      P |-- |> P' ->
      SEPx Q |-- |> SEPx Q' ->
      SEPx (P::Q) |-- |> SEPx (P'::Q').
Proof.
unfold SEPx.
intros.
intro rho.
specialize (H0 rho).
intros; normalize.
simpl.
rewrite later_sepcon.
apply sepcon_derives; auto.
apply H.
Qed.
Hint Resolve PROP_later_derives LOCAL_later_derives SEP_later_derives : derives.

Lemma local_lift0: forall P, local (lift0 P) = prop P.
Proof.
intros. extensionality rho. reflexivity.
Qed.
Hint Rewrite @local_lift0: norm2.

Lemma move_prop_from_LOCAL:
  forall P1 P Q R, PROPx P (LOCALx (lift0 P1::Q) R) = PROPx (P1::P) (LOCALx Q R).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, local, lift0, lift1.
 unfold_lift.
 simpl.
 apply pred_ext; normalize.
 destruct H0. repeat rewrite prop_true_andp by auto; auto.
 destruct H.  repeat rewrite prop_true_andp by auto; auto.
Qed.

Ltac extract_prop_from_LOCAL :=
 match goal with |- @semax _ _ _ (PROPx _ (LOCALx ?Q _)) _ _ =>
   match Q with 
    | context [ lift0 ?z :: _ ] =>
        let n := find_in_list (lift0 z) Q
         in rewrite (grab_nth_LOCAL n); 
             unfold nth, delete_nth; 
             rewrite move_prop_from_LOCAL
   | context [@liftx (LiftEnviron Prop) ?z :: _ ] =>
       let n := find_in_list (@liftx (LiftEnviron Prop) z) Q
         in rewrite (grab_nth_LOCAL n); 
             change (@liftx (LiftEnviron Prop) z) with (@lift0 Prop z);
             unfold nth, delete_nth; 
             rewrite move_prop_from_LOCAL
  end
end.

Lemma extract_exists_pre:
      forall
        (A : Type) (P : A -> environ->mpred) (c : Clight.statement)
         Espec {cs: compspecs} Delta  (R : ret_assert),
       (forall x : A, @semax cs Espec Delta (P x) c R) ->
       @semax cs Espec Delta (exp (fun x => P x)) c R.
Proof.
intros.
apply semax_post with (existential_ret_assert (fun _:A => R)).
intros ek vl.
unfold existential_ret_assert.
apply andp_left2.
apply exp_left; auto.
apply extract_exists; auto.
Qed.

Lemma extract_exists_post:
  forall {Espec: OracleKind} {cs: compspecs} {A: Type} (x: A) Delta 
       (P: environ -> mpred) c (R: A -> environ -> mpred),
  semax Delta P c (normal_ret_assert (R x)) ->
  semax Delta P c (normal_ret_assert (exp R)).
Proof.
intros.
eapply semax_pre_post; try apply H.
apply andp_left2; auto.
intros ek vl rho.
unfold local, lift1, existential_ret_assert.
simpl.
apply andp_left2.
unfold normal_ret_assert.
normalize. autorewrite with norm1 norm2; normalize.
apply exp_right with x; normalize.
Qed.

Ltac repeat_extract_exists_pre :=
   first [(apply extract_exists_pre;
             let x := fresh "x" in intro x; normalize;
                repeat_extract_exists_pre;
                revert x)
           | autorewrite with canon
          ].
             
Lemma extract_exists_in_SEP:
  forall {A} (R1: A -> environ->mpred) P Q R,   
    PROPx P (LOCALx Q (SEPx (exp R1 :: R))) = 
    EX x:A, PROPx P (LOCALx Q (SEPx (R1 x::R))).
Proof.
intros.
extensionality rho.
unfold PROPx, LOCALx, SEPx; simpl.
normalize.
Qed.

Ltac extract_exists_in_SEP :=
 match goal with |- @semax _ _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ exp ?z :: _] =>
        let n := find_in_list (exp z) R 
         in rewrite (grab_nth_SEP n); unfold nth, delete_nth; rewrite extract_exists_in_SEP;
             repeat_extract_exists_pre
  end
end.

Lemma flatten_sepcon_in_SEP:
  forall P Q R1 R2 R, 
           PROPx P (LOCALx Q (SEPx ((R1*R2) :: R))) = 
           PROPx P (LOCALx Q (SEPx (R1 :: R2 :: R))).
Proof.
intros.
f_equal. f_equal. extensionality rho.
unfold SEPx.
simpl. rewrite sepcon_assoc. auto.
Qed.

Ltac flatten_sepcon_in_SEP :=
  match goal with
  | |- @semax _ _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ (sepcon ?x  ?y) :: ?R'] =>
  let n := length_of R in let n' := length_of R' in 
         rewrite (grab_nth_SEP (n-S n')); simpl minus; unfold nth, delete_nth; 
         rewrite flatten_sepcon_in_SEP
    end
  | |-  (PROPx _ (LOCALx _ (SEPx ?R))) |-- _ =>
   match R with context [ (sepcon ?x  ?y) :: ?R'] =>
  let n := length_of R in let n' := length_of R' in 
         rewrite (grab_nth_SEP (n-S n')); simpl minus; unfold nth, delete_nth; 
         rewrite flatten_sepcon_in_SEP
  end
end.

Lemma semax_ff:
  forall Espec {cs: compspecs} Delta c R,  
   @semax cs Espec Delta FF c R.
Proof.
intros.
apply semax_pre_post with (FF && FF) R.
apply andp_left2. apply andp_right; auto.
intros; apply andp_left2; auto.
apply semax_extract_prop. intros; contradiction.
Qed.

Lemma extract_prop_in_SEP:
  forall n P1 Rn P Q R, 
   nth n R emp = prop P1 && Rn -> 
   PROPx P (LOCALx Q (SEPx R)) = PROPx (P1::P) (LOCALx Q (SEPx (replace_nth n R Rn))).
Proof.
intros.
extensionality rho.
unfold PROPx,LOCALx,SEPx,local,lift1.
simpl.
apply pred_ext; normalize.
* match goal with |- _ |-- !! ?PP && _ => replace PP with P1
   by (apply prop_ext; intuition)
  end.
  rewrite (prop_true_andp _ _ H1).
 clear H1 Q H0 P.
  clear - H.
  revert R H; induction n; destruct R; simpl; intros.
  apply andp_right; auto.
  apply equal_f with rho in H.
  rewrite H; apply andp_left1; auto.
  rewrite H.
  normalize.
  apply andp_right; auto.
  apply equal_f with rho in H.
  rewrite H; apply andp_left1; auto.
  rewrite <- sepcon_andp_prop.
  apply sepcon_derives; auto.
*
  destruct H0; repeat rewrite prop_true_andp by auto.
 clear - H H0.
  revert R H; induction n; destruct R; simpl; intros; auto. 
  subst m. rewrite prop_true_andp; auto.
  apply sepcon_derives; auto.
Qed.

Lemma insert_SEP: 
 forall R1 P Q R, R1 * PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q (SEPx (R1::R))).
Proof.
intros. 
unfold PROPx,LOCALx,SEPx,local,lift1.
extensionality rho; simpl.
repeat rewrite sepcon_andp_prop. f_equal; auto.
Qed.

Lemma delete_emp_in_SEP:
  forall n (R: list (environ->mpred)), 
    nth_error R n = Some emp ->
    SEPx R = SEPx (firstn n R ++ list_drop (S n) R).
Proof.
intros.
unfold SEPx; extensionality rho.
revert R H; induction n; destruct R; simpl; intros; auto.
inv H. rewrite emp_sepcon; auto.
f_equal; auto.
etransitivity.
apply IHn; auto.
reflexivity.
Qed.

Ltac delete_emp_in_SEP :=
 change (@liftx (LiftEnviron mpred) (@emp mpred _ _)) with 
       (@emp (environ->mpred) _ _); 
 repeat  
 match goal with |- context [SEPx ?R] =>
   match R with context [emp:: ?R'] =>
     rewrite (delete_emp_in_SEP (length R - S (length R')) R) by reflexivity;
     simpl length; simpl minus; unfold firstn, app, list_drop; fold app
   end
 end.

Lemma extract_local_in_SEP :
  forall n Q1 Rn P Q R, 
   nth_error R n = Some (local Q1 && Rn) -> 
   PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx (Q1::Q) (SEPx (replace_nth n R Rn))).
Proof.
intros.
f_equal.
extensionality rho.
unfold PROPx,LOCALx,SEPx,local,lift1 in *.
unfold_lift; simpl in *.
revert R H; induction n; destruct R; simpl; intros;
 inv H.
apply pred_ext; subst; normalize.
rewrite prop_true_andp by auto.
auto.
destruct H; normalize.
specialize (IHn R).
do 2 rewrite <- sepcon_andp_prop.
rewrite IHn.
auto.
auto.
Qed.

Ltac move_local_from_SEP :=
match goal with |- context [PROPx _ (LOCALx _ (SEPx ?R))] =>
  match R with context [(local ?P1 && ?Rn) :: ?R'] =>
  let n := length_of R in let n' := length_of R' in 
   rewrite (extract_local_in_SEP (n-S n')%nat P1 Rn) by reflexivity;
    simpl minus; unfold replace_nth 
 end
end.

Ltac move_from_SEP :=
  (* combines extract_exists_in_SEP, move_prop_from_SEP, move_local_from_SEP, 
                  flatten_sepcon_in_SEP *)
match goal with |- context [PROPx _ (LOCALx _ (SEPx ?R))] =>
  match R with 
  | context [(local ?P1 && ?Rn) :: ?R'] =>
      let n := length_of R in let n' := length_of R' in 
       rewrite (extract_local_in_SEP (n-S n')%nat P1 Rn) by reflexivity;
        simpl minus; unfold replace_nth 
  | context [(prop ?P1 && ?Rn) :: ?R'] =>
      let n := length_of R in let n' := length_of R' in 
        rewrite (extract_prop_in_SEP (n-S n')%nat P1 Rn) by reflexivity;
        simpl minus; unfold replace_nth (*;
        try (apply semax_extract_PROP; intro)*)
  | context [ exp ?z :: _] =>
        let n := find_in_list (exp z) R 
         in rewrite (grab_nth_SEP n); unfold nth, delete_nth; rewrite extract_exists_in_SEP;
             repeat_extract_exists_pre
  | context [ (sepcon ?x  ?y) :: ?R'] =>
        let n := length_of R in let n' := length_of R' in 
         rewrite (grab_nth_SEP (n-S n')); simpl minus; unfold nth, delete_nth; 
         rewrite flatten_sepcon_in_SEP
 end
end.


Lemma move_local_from_SEP':
  forall P1 R1 P Q R, 
      PROPx P (LOCALx Q (SEPx ((local P1&&R1) :: R))) = PROPx P (LOCALx (P1::Q) (SEPx (R1::R))).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, SEPx, local, lift1; unfold_lift.
 normalize.
 apply pred_ext; normalize. autorewrite with norm1 norm2; normalize.
 rewrite prop_true_andp by auto. auto.
 autorewrite with norm1 norm2; normalize.
 destruct H0; normalize.
Qed.

Lemma nth_error_local:
  forall n P Q R (Qn: environ -> Prop),
    nth_error Q n = Some Qn ->
    PROPx P (LOCALx Q (SEPx R)) |-- local Qn.
Proof.
intros.
apply andp_left2. apply andp_left1.
go_lowerx. normalize.
revert Q H H0; induction n; destruct Q; intros; inv H.
destruct H0; auto.
destruct H0. apply (IHn Q); auto.
Qed.

Lemma in_nth_error: forall {A} (x: A) xs, In x xs -> exists n, nth_error xs n = Some x.
Proof.
  intros.
  induction xs.
  + inversion H.
  + destruct H.
    - subst; exists 0%nat.
      reflexivity.
    - destruct (IHxs H) as [?n ?H].
      exists (S n).
      simpl.
      tauto.
Qed.

Lemma in_local: forall Q0 P Q R, In Q0 Q -> PROPx P (LOCALx Q (SEPx R)) |-- local Q0.
Proof.
  intros.
  destruct (in_nth_error _ _ H) as [?n ?H].
  eapply nth_error_local.
  eauto.
Qed.

(* Hint Rewrite move_prop_from_SEP move_local_from_SEP : norm. *)

Lemma lower_PROP_LOCAL_SEP:
  forall P Q R rho, PROPx P (LOCALx Q (SEPx R)) rho = 
     (!!fold_right and True P && (local (fold_right (`and) (`True) Q) && (fold_right sepcon emp R))) rho.
Proof. reflexivity. Qed.
Hint Rewrite lower_PROP_LOCAL_SEP : norm2.

Lemma lower_TT: forall rho, @TT (environ->mpred) _ rho = @TT mpred Nveric.
Proof. reflexivity. Qed.
Hint Rewrite lower_TT : norm2.

Lemma lower_FF: forall rho, @FF (environ->mpred) _ rho = @FF mpred Nveric.
Proof. reflexivity. Qed.
Hint Rewrite lower_FF : norm2.

Lemma remember_value:
  forall e Espec {cs: compspecs} Delta P Q R c Post,
  (forall x:val, 
   @semax cs Espec Delta (PROPx P (LOCALx (`(eq x) e:: Q) (SEPx R))) c Post) ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
 intros.
 apply semax_pre0 with (EX x:val, PROPx P (LOCALx (`(eq x) e::Q) (SEPx R))).
 intro rho. simpl. apply exp_right with (e rho).
 unfold PROPx, LOCALx; simpl; apply andp_derives; auto.
 apply andp_derives; auto.
 unfold local; super_unfold_lift; simpl.
 apply prop_left; intro. apply prop_right. split; auto.
 apply extract_exists_pre.  apply H.
Qed.

Lemma assert_PROP:
 forall P1 Espec {cs: compspecs} Delta P Q R c Post,
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! P1 ->
   (P1 -> @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post) ->
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre.
apply andp_right.
apply H.
rewrite <- insert_local.
apply andp_left2; apply derives_refl.
apply semax_extract_prop.
auto.
Qed.

Lemma assert_PROP' {A}{NA: NatDed A}:
 forall P Pre (Post: A),
   Pre |-- !! P ->
   (P -> Pre |-- Post) ->
   Pre |-- Post.
Proof.
intros.
apply derives_trans with (!!P && Pre).
apply andp_right; auto.
apply derives_extract_prop. auto.
Qed.

Ltac assert_PROP A :=
 first [apply (assert_PROP A); [ | intro]
         | apply (assert_PROP' A); [ | intro]].

Lemma assert_LOCAL:
 forall Q1 Espec {cs: compspecs} Delta P Q R c Post,
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local Q1 ->
   @semax cs Espec Delta (PROPx P (LOCALx (Q1::Q) (SEPx R))) c Post ->
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; try apply H0.
rewrite <- (insert_local Q1); apply andp_right; auto.
rewrite <- insert_local; apply andp_left2; auto.
Qed.

Ltac assert_LOCAL A :=
 apply (assert_LOCAL A).

Lemma drop_LOCAL':
  forall (n: nat)  P Q R Post,
   PROPx P (LOCALx (delete_nth n Q) (SEPx R)) |-- Post ->
   PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
intros.
eapply derives_trans; try apply H.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. apply prop_derives; simpl.
clear.
revert Q; induction n; destruct Q; simpl; intros; intuition.
Qed.

Lemma drop_LOCAL:
  forall (n: nat) Espec {cs: compspecs} Delta P Q R c Post,
   @semax cs Espec Delta (PROPx P (LOCALx (delete_nth n Q) (SEPx R))) c Post ->
   @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros.
eapply semax_pre; try apply H.
rewrite <- insert_local. apply andp_left2.
apply andp_derives; auto.
apply andp_derives; auto.
intro rho; unfold local, lift1; unfold_lift. apply prop_derives; simpl.
clear.
revert Q; induction n; destruct Q; simpl; intros; intuition.
Qed.

Ltac drop_LOCAL n :=
   first [apply (drop_LOCAL n) | apply (drop_LOCAL' n)];
    unfold delete_nth.

(**** New experiments regarding TEMP and VAR *)

Definition temp (i: ident) (v: val) : environ -> Prop :=
   `(eq v) (eval_id i).

Definition var (i: ident) (t: type) (v: val) : environ -> Prop :=
   `(eq v) (eval_var i t).

Definition lvar {cs: compspecs} (i: ident) (t: type) (v: val) (rho: environ) : Prop :=
     (* local variable *)
   match Map.get (ve_of rho) i with
   | Some (b, ty') => 
       if eqb_type t ty' 
       then v = Vptr b Int.zero /\ size_compatible t v
       else False
   | None => False
   end.

Definition gvar (i: ident) (v: val) (rho: environ) : Prop :=
    (* visible global variable *)
   match Map.get (ve_of rho) i with
   | Some (b, ty') => False
   | None =>
       match ge_of rho i with
       | Some b => v = Vptr b Int.zero
       | None => False
       end
   end.

Definition sgvar (i: ident) (v: val) (rho: environ) : Prop := 
    (* (possibly) shadowed global variable *)
   match ge_of rho i with
       | Some b => v = Vptr b Int.zero
       | None => False
   end.

Lemma PROP_LOCAL_SEP_f:
  forall P Q R f, `(PROPx P (LOCALx Q (SEPx R))) f =
     PROPx P (LOCALx (map (fun q : environ -> Prop => `q f) Q)
            (SEPx (map (fun r : environ -> mpred => `r f) R))).
Proof. intros. extensionality rho.
cbv delta [PROPx LOCALx SEPx local lift lift1 liftx]; simpl.
f_equal. f_equal.
f_equal.
induction Q; simpl; auto. f_equal; auto.
induction R; simpl; auto. f_equal; auto.
Qed.
Hint Rewrite PROP_LOCAL_SEP_f: norm2.

Lemma SEP_PROP:
 forall P Q R P' Q' R', 
     PROPx P (LOCALx Q (SEPx (PROPx P' (LOCALx Q' (SEPx R')) :: R))) =
    PROPx (P++P') (LOCALx (Q++Q') (SEPx (R'++R))).
Proof.
intros.
extensionality rho.
cbv delta [PROPx LOCALx SEPx local lift lift1 liftx]; simpl.
apply pred_ext; normalize.
rewrite prop_true_andp.
rewrite prop_true_andp; auto.
clear; induction R'; simpl; normalize.
rewrite sepcon_assoc; apply sepcon_derives; auto.
revert H0; induction Q; simpl; intros; auto.
destruct H0; split; auto.
induction P; simpl; auto. destruct H; split; auto.
rewrite prop_true_andp.
rewrite prop_true_andp.
rewrite prop_true_andp.
rewrite prop_true_andp.
induction R'; simpl. normalize.
rewrite sepcon_assoc; apply sepcon_derives; auto.
induction Q; simpl; auto. destruct H0. auto.
induction P; simpl; auto. destruct H; auto.
induction Q; simpl; auto.
destruct H0; split; auto.
induction P; simpl; auto. destruct H; split; auto.
Qed.
Hint Rewrite SEP_PROP: norm1.

Ltac clean_up_app_carefully := (* useful after rewriting by SEP_PROP *)
 repeat
  match goal with
  | |- context [@app Prop (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (environ->Prop) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (lifted (LiftEnviron Prop)) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (environ->mpred) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app (lifted (LiftEnviron mpred)) (?a :: ?b) ?c] =>
    change (app (a::b) c) with (a :: app b c)
  | |- context [@app Prop nil ?c] => 
     change (app nil c) with c
  | |- context [@app (environ->Prop) nil ?c] => 
     change (app nil c) with c
  | |- context [@app (lifted (LiftEnviron Prop)) nil ?c] => 
     change (app nil c) with c
  | |- context [@app (lifted (environ->mpred)) nil ?c] => 
     change (app nil c) with c
  | |- context [@app (lifted (LiftEnviron mpred)) nil ?c] => 
     change (app nil c) with c
 end.


Definition not_conj_notation (P: Prop) := True.

Ltac not_conj_notation :=
 match goal with 
 | |- not_conj_notation (_ <= _ <= _)%Z => fail 1
 | |- not_conj_notation (_ <= _ < _)%Z => fail 1
 | |- not_conj_notation (_ < _ <= _)%Z => fail 1
 | |- not_conj_notation (_ <= _ <= _)%nat => fail 1
 | |- not_conj_notation (_ <= _ < _)%nat => fail 1
 | |- not_conj_notation (_ < _ <= _)%nat => fail 1
 | |- _ => apply Coq.Init.Logic.I
 end.

Lemma split_first_PROP:
  forall P Q R S, 
  not_conj_notation (P/\Q) ->
  PROPx ((P/\Q)::R) S = PROPx (P::Q::R) S.
Proof.
intros. unfold PROPx; simpl.
extensionality rho.
apply pred_ext; apply andp_derives; auto;
  apply prop_derives; intuition.
Qed.
Hint Rewrite split_first_PROP using not_conj_notation : norm1.



Require Import Permutation.

Lemma perm_derives:
  forall P Q R P' Q' R',
    Permutation P P' ->
    Permutation Q Q' ->
    Permutation R R' ->
    PROPx P (LOCALx Q (SEPx R)) |-- PROPx P' (LOCALx Q' (SEPx R')).
Proof.
intros.
apply andp_derives.
apply prop_derives.
clear - H.
induction H; simpl; intuition.
apply andp_derives.
clear- H0.
intro rho.
unfold local,lift1.
apply prop_derives.
induction H0; simpl; intuition.
destruct H; split; auto.
destruct H as [? [? ?]]. split3; auto.
clear- H1.
unfold SEPx.
induction H1; intuition.
unfold fold_right; fold fold_right. apply sepcon_derives; auto.
unfold fold_right; fold fold_right.
rewrite <- sepcon_assoc.
rewrite (sepcon_comm y).
rewrite sepcon_assoc; auto.
eapply derives_trans; eassumption.
Qed.

Lemma perm_search:
  forall {A} (a b: A) r s t,
     Permutation (a::t) s ->
     Permutation (b::t) r ->
     Permutation (a::r) (b::s).
Proof.
intros.
eapply perm_trans.
apply perm_skip.
apply Permutation_sym.
apply H0.
eapply perm_trans.
apply perm_swap.
apply perm_skip.
apply H.
Qed.


Lemma Permutation_app_comm_trans:
 forall (A: Type) (a b c : list A), 
   Permutation (b++a) c ->
   Permutation (a++b) c.
Proof.
intros.
eapply Permutation_trans.
apply Permutation_app_comm.
auto.
Qed.

Ltac solve_perm :=
    (* solves goals of the form (R ++ ?i = S)
          where R and S are lists, and ?i is a unification variable *)
  try match goal with
       | |-  Permutation (?A ++ ?B) _ =>
            is_evar A; first [is_evar B; fail 1| idtac];
            apply Permutation_app_comm_trans
       end;
  repeat first [ apply Permutation_refl
       | apply perm_skip
       | eapply perm_search
       ].

Goal exists e, Permutation ((1::2::nil)++e) (3::2::1::5::nil).
eexists.
solve_perm.
Qed.
 
Lemma semax_frame_perm:
forall (Qframe : list (environ -> Prop))
         (Rframe : list (environ -> mpred))
         (Espec : OracleKind) {cs: compspecs}
         (Delta : tycontext)
         (P : list Prop) (Q : list (environ -> Prop)) (c : statement)
         (R : list (environ -> mpred))
         (Q1 : list (environ -> Prop)) (R1 : list (environ -> mpred))
         (P2 : list Prop) (Q2 : list (environ -> Prop))
         (R2 : list (environ -> mpred)),
       closed_wrt_modvars c (LOCALx Qframe (SEPx Rframe)) ->
       Permutation (Qframe ++ Q1) Q ->
       Permutation (Rframe ++ R1)  R ->
       semax Delta (PROPx P (LOCALx Q1 (SEPx R1))) c
         (normal_ret_assert (PROPx P2 (LOCALx Q2 (SEPx R2)))) ->
       semax Delta (PROPx P (LOCALx Q (SEPx R))) c
         (normal_ret_assert
            (PROPx P2 (LOCALx (Q2 ++ Qframe) (SEPx (R2 ++ Rframe))))).
Proof.
 intros.
 eapply (semax_frame1 Qframe Rframe); try eassumption; auto.
 rewrite <- insert_local.
 apply andp_left2.
 apply perm_derives.
 apply Permutation_refl.
 eapply perm_trans; [apply Permutation_sym; eassumption | apply Permutation_app_comm].
 eapply perm_trans; [apply Permutation_sym; eassumption | apply Permutation_app_comm].
Qed.

Lemma semax_post_flipped' : 
   forall (R': environ->mpred) Espec {cs: compspecs} (Delta: tycontext) (R P: environ->mpred) c,
       @semax cs Espec Delta P c (normal_ret_assert R') ->
       R' |-- R ->
       @semax cs Espec Delta P c (normal_ret_assert R).
 Proof. intros; eapply semax_post'; eauto. Qed.

Tactic Notation "semax_frame" constr(Qframe) constr(Rframe) :=
 first
    [ simple eapply (semax_frame_perm Qframe Rframe);
          [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
    | eapply semax_post_flipped';
      [simple eapply (semax_frame_perm Qframe Rframe);
        [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
      | try solve [apply perm_derives; solve_perm]]
  ].

Tactic Notation "semax_frame" "[" "]" constr(Rframe) :=
 first
    [ simple eapply (semax_frame_perm nil Rframe);
          [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
    | eapply semax_post_flipped';
      [simple eapply (semax_frame_perm nil Rframe);
        [auto 50 with closed | solve_perm | solve_perm | unfold app; fold @app ]
      | try solve [apply perm_derives; solve_perm]]
  ].


Lemma semax_pre_later:
 forall P' Espec {cs: compspecs} Delta P1 P2 P3 c R,
     (PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3))) |-- P' ->
     @semax cs Espec Delta (|> P') c R  -> 
     @semax cs Espec Delta (|> (PROPx P1 (LOCALx P2 (SEPx P3)))) c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
eapply derives_trans; [ | apply later_derives; apply H ].
eapply derives_trans.
2: apply later_derives; rewrite <- insert_local; apply derives_refl.
rewrite later_andp; apply andp_derives; auto; apply now_later.
Qed.







