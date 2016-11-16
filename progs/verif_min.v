Require Import floyd.proofauto.
Require Import progs.min.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z.


Theorem fold_min_general:
  forall (al: list Z)(i: Z),
  In i (al) ->
  forall x, List.fold_right Z.min x al <= i.
Proof.
induction al; intros.
inversion H.
destruct H.
subst a.
simpl.
apply Z.le_min_l.
simpl. rewrite Z.le_min_r.
apply IHal.
apply H.
Qed.

Theorem fold_min:
  forall (al: list Z)(i: Z),
  In i (al) ->
  List.fold_right Z.min (hd 0 al) al <= i.
Proof.
intros.
apply fold_min_general.
apply H.
Qed.

Lemma Forall_fold_min:
  forall (f: Z -> Prop) (x: Z) (al: list Z),
    f x -> Forall f al -> f (fold_right Z.min x al).
Proof.
 intros.
 induction H0.
 simpl. auto.
 simpl.
 unfold Z.min at 1.
 destruct (Z.compare x0 (fold_right Z.min x l)) eqn:?; auto.
Qed.

Lemma fold_min_another:
  forall x al y, 
    fold_right Z.min x (al ++ [y]) = Z.min (fold_right Z.min x al) y.
Proof.
 intros.
 revert x; induction al; simpl; intros.
 apply Z.min_comm.
 rewrite <- Z.min_assoc. f_equal.
 apply IHal.
Qed.

Definition minimum_spec :=
 DECLARE _minimum
  WITH a: val, n: Z, al: list Z
  PRE [ _a OF tptr tint , _n OF tint ]
    PROP  (1 <= n <= Int.max_signed; Forall repable_signed al)
    LOCAL (temp _a a; temp _n (Vint (Int.repr n)))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
  POST [ tint ]
    PROP ()
    LOCAL(temp ret_temp  (Vint (Int.repr (fold_right Z.min (hd 0 al) al))))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a).

Definition Gprog : funspecs :=
      ltac:(with_library prog [minimum_spec]).

Lemma body_min: semax_body Vprog Gprog f_minimum minimum_spec.
Proof.
start_function.
assert_PROP (Zlength al = n). {
  entailer!. autorewrite with sublist; auto.
}
forward.  (* min = a[0]; *) {
  entailer!.
  destruct al. 
  autorewrite with sublist in *. omega.
  simpl. auto.
}
forward_for_simple_bound n 
  (EX i:Z,
    PROP() 
    LOCAL(temp _min (Vint (Int.repr (fold_right Z.min (hd 0 al) (sublist 0 i al)))); 
          temp _a a; 
          temp _n (Vint (Int.repr n)))
    SEP(data_at Ews (tarray tint n) (map (Vint oo Int.repr) al) a)).
*
 entailer!. destruct al. autorewrite with sublist in *. omega.
 simpl. reflexivity.
 rewrite map_map; cancel.
*
 forward. (* j = a[i]; *) {
   entailer!.
   autorewrite with sublist in *.
   rewrite Znth_map with (d':=0) by auto. apply I.
 }
 assert (repable_signed (Znth i al 0)).
     apply Forall_Znth; auto. omega.
 assert (repable_signed (fold_right Z.min (hd 0 al) (sublist 0 i al))). {
     apply Forall_fold_min.
     destruct al; simpl. repable_signed.
     destruct (zeq 0 i).
     subst i. apply H3.
     rewrite <- (sublist_same 0 (Zlength (z::al)) (z::al)) in H3 by auto.
     rewrite (sublist_split 0 1 (Zlength (z::al))) in H3 by omega.
     change (z::al) with ([z]++al) in *.
     rewrite app_Znth2 in H3; autorewrite with sublist in *; try omega.
     apply Forall_app in H0.
     destruct H0 as [H0 ?]; inv H0; auto.
     apply Forall_sublist; auto.
 }
 rewrite Znth_map with (d':=0) by omega.
 subst POSTCONDITION; unfold abbreviate.
 rewrite (sublist_split 0 i (i+1)) by omega.
 rewrite (sublist_one i (i+1) al 0) by omega.
 rewrite fold_min_another.
 forward_if. 
 +
 forward. (* min = j; *)
 entailer!.
 f_equal; f_equal.
 apply Z.min_r. omega.
 +
 forward. (* skip; *)
 entailer!.
 f_equal; f_equal.
 apply Z.min_l.
 omega.
*
 forward. (* return *)
 entailer!.
 autorewrite with sublist. simpl. auto.
 rewrite map_map; cancel.
Qed.


Definition minimum_spec2 :=
 DECLARE _minimum
  WITH a: val, n: Z, al: list Z
  PRE [ _a OF tptr tint , _n OF tint ]
    PROP  (1 <= n <= Int.max_signed; Forall repable_signed al)
    LOCAL (temp _a a; temp _n (Vint (Int.repr n)))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
  POST [ tint ]
   EX j: Z,
    PROP (In j al; Forall (fun x => j<=x) al)
    LOCAL(temp ret_temp  (Vint (Int.repr j)))
    SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a).

Definition invariant a al n :=
  (EX i:Z, EX j:Z,
    PROP(0 <= i < n;
         In j (sublist 0 (Z.max 1 i) al); 
         Forall (fun x => j <= x) (sublist 0 i al)) 
    LOCAL(temp _i (Vint (Int.repr i));
          temp _min (Vint (Int.repr j)); 
          temp _a a; 
          temp _n (Vint (Int.repr n)))
    SEP(data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)).

Lemma body_min2: semax_body Vprog Gprog f_minimum minimum_spec2.
Proof.
start_function.
assert_PROP (Zlength al = n).
  entailer!. autorewrite with sublist; auto.
forward.  (* min = a[0]; *) {
  entailer!.
  destruct al. 
 autorewrite with sublist in *. omega.
 simpl. auto.
}
forward_for_simple_bound n 
  (EX i:Z, EX j:Z,
    PROP(
         In j (sublist 0 (Z.max 1 i) al); 
         Forall (fun x => j <= x) (sublist 0 i al)) 
    LOCAL(
          temp _min (Vint (Int.repr j)); 
          temp _a a; 
          temp _n (Vint (Int.repr n)))
    SEP(data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)).
* (* Show that the precondition entails the loop invariant *)
Exists (Znth 0 al 0).
entailer!.
split; [split|].
rewrite sublist_one with (d:=0); auto; try omega. left; auto.
autorewrite with sublist. constructor.
rewrite map_map. rewrite Znth_map with (d':=0); auto. omega.
* (* Show that the loop body preserves the loop invariant *)
Intros.
forward. (* j = a[i]; *) {
 entailer!. clear H6.
 rewrite map_map in *.
 rewrite Znth_map with (d':=0). apply I. auto.
 }
 assert (repable_signed (Znth i al 0)). {
     apply Forall_Znth; auto. omega.
 }
(*
 assert (repable_signed (fold_right Z.min (hd 0 al) (sublist 0 i al))). {
   apply (Forall_sublist _ 0 i) in H0.
   apply Forall_fold_min.
   destruct al; simpl. repable_signed.
   destruct (zeq 0 i).
   subst i. assumption.
   rewrite <- (sublist_same 0 (Zlength (z::al)) (z::al)) in H5 by auto.
   rewrite (sublist_split 0 1 (Zlength (z::al))) in H5 by omega.
   change (z::al) with ([z]++al) in *.
   rewrite app_Znth2 in H5 by (autorewrite with sublist; omega).
   rewrite (sublist_split 0 1 i) in H0; autorewrite with sublist; try omega.
   autorewrite with sublist in H0.
   simpl in H0. inv H0. auto.
   autorewrite with sublist in H1. omega.
   apply H0.
}
*)
 forward_if.
 +
 rewrite map_map in H6.
 rewrite Znth_map with (d':=0) in H6 by omega. simpl in H6.
 apply typed_true_of_bool in H6.
 apply lt_repr in H6; auto.
 forward. (* min = j; *)
 Exists (Znth i al 0).
 entailer!.
 split; [split |].
 rewrite Z.max_r by omega.
 rewrite (sublist_split 0 i (i+1)) by omega.
 apply in_app; right. rewrite (sublist_one i (i+1) al 0) by omega.
 left; auto.
 rewrite (sublist_split 0 i (i+1)) by omega.
 apply Forall_app; split.
 eapply Forall_impl; try apply H4.
 intros. simpl in H10. omega.
 rewrite (sublist_one i (i+1) al 0) by omega.
 constructor; auto. omega.
 rewrite map_map. rewrite  Znth_map with (d':=0) by omega.
 auto.
 eapply Forall_sublist in H0.
 eapply Forall_forall in H3; eauto.
 +
 forward. (* skip; *)
 Exists x.
 entailer!.
 split.
 rewrite Z.max_r by omega.
 destruct (zlt 1 i).
 rewrite Z.max_r in H3 by omega. 
 rewrite (sublist_split 0 i (i+1)) by omega.
 apply in_app; left; auto.
 rewrite Z.max_l in H3 by omega.
 rewrite (sublist_split 0 1 (i+1)) by omega.
 apply in_app; left; auto.
 rewrite (sublist_split 0 i (i+1)) by omega.
 apply Forall_app. split; auto.
 rewrite (sublist_one i (i+1) al 0) by omega.
 repeat constructor.
 rewrite map_map in H6.
 rewrite  Znth_map with (d':=0) in H6 by omega.
 simpl in H6.
 apply typed_false_of_bool in H6.
 apply lt_repr_false in H6; try repable_signed.
 eapply Forall_forall in H3; [ | eapply Forall_sublist; eauto].
 auto.
* (* After the loop *)
 Intros x.
 rewrite Z.max_r in H2 by omega.
 autorewrite with sublist in *.
 forward. (* return *)
 Exists x.
 entailer!.
Qed.
