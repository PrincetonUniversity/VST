Require Import floyd.base.
Require Import floyd.assert_lemmas.
Local Open Scope logic.

Arguments sem_cmp c !t1 !t2 valid_pointer / v1 v2.  

Lemma prop_and {A} {NA: NatDed A}: 
    forall P Q: Prop, prop (P /\ Q) = (prop P && prop Q).
Proof. intros. apply pred_ext. apply prop_left. intros [? ?]; normalize.
   normalize.
Qed.

Hint Rewrite <- prop_and : gather_prop.

Lemma gather_prop_left {A}{NA: NatDed A}:
  forall P Q R,  !! P && (!! Q && R) = !!(P/\Q) && R.
Proof. intros. rewrite <- andp_assoc. rewrite <- prop_and; auto.
Qed.

Lemma gather_prop_right {A}{NA: NatDed A}:
  forall P Q R,  R && !! P && !! Q = !!(P/\Q) && R.
Proof. intros. rewrite andp_assoc. rewrite andp_comm.  rewrite <- prop_and; auto.
Qed.
Hint Rewrite gather_prop_left gather_prop_right : gather_prop.

Definition not_a_prop {A} (P: A) := True.

Ltac not_a_prop := match goal with
  | |- not_a_prop  (prop _) => fail 1 
  | |- _ => apply I 
end.

Lemma flip_prop {A}{NA: NatDed A}: forall P Q, 
      not_a_prop P -> (P&& !! Q = !! Q && P).
Proof. intros. apply andp_comm. Qed.

Hint Rewrite @flip_prop using not_a_prop : gather_prop.

Lemma gather_prop3 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> R && (!! P && Q) = !!P && (R && Q).
Proof. intros. rewrite andp_comm. rewrite andp_assoc.
        rewrite (andp_comm Q); auto.
Qed.

Hint Rewrite @gather_prop3 using not_a_prop : gather_prop.


Lemma gather_prop4 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> (!!P && R) && Q = !!P && (R && Q).
Proof. intros. rewrite andp_assoc. auto. 
Qed.
Hint Rewrite @gather_prop4 using not_a_prop : gather_prop.

Lemma gather_prop5 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> (R && !!P && Q) = !!P && (R && Q).
Proof. intros. rewrite andp_assoc. rewrite andp_comm. rewrite andp_assoc.
  f_equal; apply andp_comm.
Qed.
Hint Rewrite @gather_prop5 using not_a_prop : gather_prop.

Hint Rewrite @sepcon_andp_prop @sepcon_andp_prop' : gather_prop.

(**** BEGIN experimental normalize (to replace the one in msl/log_normalize.v ****)

Lemma prop_true_andp' (P: Prop) {A} {NA: NatDed A}:
  forall (Q: A),  P -> (!! P && Q = Q).
Proof with norm.
intros.
apply pred_ext. apply andp_left2...
apply andp_right... apply prop_right...
Qed.

Ltac norm_rewrite := autorewrite with norm.
 (* New version: rewrite_strat (topdown hints norm).
     But this will have to wait for a future version of Coq
    in which rewrite_strat discharges side conditions.
    According to Matthieu Sozeau, in the Coq trunk as of June 5, 2013,
    rewrite_strat is documented AND discharges side conditions.
    It might be about twice as fast, or 1.7 times as fast, as the old autorewrite.
    And then, maybe use "bottomup" instead of "topdown", see if that's better.

   To test whether your version of Coq works, use this:
Lemma L : forall n, n=n -> n + 1 = S n.
Proof. intros. rewrite <- plus_n_Sm ,<- plus_n_O. reflexivity.
Qed.
Hint Rewrite L using reflexivity : test888.
Goal forall n, S n = n + 1.
intros.
rewrite_strat (topdown hints test888).
match goal with |- S n = S n => reflexivity end.
(* should be no extra (n=n) goal here *)
Qed.
 *)

Lemma typed_false_cmp'':
  forall i j op e1 e2,
   typed_false tint (force_val (sem_cmp op tint tint true2 e1  e2 )) ->
   Vint (Int.repr i) = e1 ->
   Vint (Int.repr j) = e2 ->
   repable_signed i -> 
   repable_signed j -> 
   Zcmp (negate_comparison op) i j.
Proof.
intros. subst.
unfold sem_cmp in H. 
unfold classify_cmp in H. simpl in H.
eapply int_cmp_repr; auto.
unfold typed_false in H; simpl in H.
destruct op; simpl in *;
match goal with |- negb ?A = true => destruct A; inv H; auto
                        | |- ?A = true => destruct A; inv H; auto
 end.
Qed.

Lemma typed_true_cmp'':
  forall i j op e1 e2,
   typed_true tint (force_val (sem_cmp op tint tint true2 e1  e2 )) ->
   Vint (Int.repr i) = e1 ->
   Vint (Int.repr j) = e2 ->
   repable_signed i -> 
   repable_signed j -> 
   Zcmp op i j.
Proof.
intros. subst.
unfold sem_cmp in H. 
unfold classify_cmp in H. simpl in H.
eapply int_cmp_repr; auto.
unfold typed_true in H; simpl in H.
destruct (Int.cmp op (Int.repr i) (Int.repr j)); inv H; auto.
Qed.

Lemma int_min_signed_eq: Int.min_signed = -2147483648.
Proof. reflexivity. Qed.

Lemma int_max_signed_eq: Int.max_signed = 2147483647.
Proof. reflexivity. Qed.

Lemma int_max_unsigned_eq: Int.max_unsigned = 4294967295.
Proof. reflexivity. Qed.


Ltac repable_signed := 
   pose proof int_min_signed_eq; 
   pose proof int_max_signed_eq; 
   pose proof int_max_unsigned_eq; 
   unfold repable_signed in *;
   omega.

Lemma typed_false_ptr: 
  forall {t a v},  typed_false (Tpointer t a) v -> v=nullval.
Proof.
unfold typed_false, strict_bool_val, nullval; simpl; intros.
destruct v; try discriminate.
pose proof (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); subst; auto.
inv H.
Qed.
Lemma typed_false_cmp':
  forall op i j, 
   typed_false tint (force_val (sem_cmp op tint tint true2 i j )) ->
   Int.cmp (negate_comparison op) (force_int i) (force_int j) = true.
Proof.
intros.
unfold sem_cmp in H. 
unfold classify_cmp in H. simpl in H.
rewrite Int.negate_cmp.
destruct i; inv H. 
destruct j; inv H1.
simpl in *. destruct (Int.cmp op i i0); inv H0; auto.
Qed.


Lemma typed_true_cmp':
  forall op i j, 
   typed_true tint (force_val (sem_cmp op tint tint true2 i j)) ->
   Int.cmp op (force_int i) (force_int j) = true.
Proof.
intros.
unfold sem_cmp in H. 
unfold classify_cmp in H. simpl in H.
destruct i; inv H. destruct j; inv H1.
simpl in *. destruct (Int.cmp op i i0); inv H0; auto.
Qed.

Lemma typed_true_ptr: 
  forall {t a v},  typed_true (Tpointer t a) v -> isptr v.
Proof.
unfold typed_true, strict_bool_val; simpl; intros.
destruct v; try discriminate.
if_tac in H; inv H. simpl. auto.
Qed.

Lemma int_cmp_repr':
 forall op i j, repable_signed i -> repable_signed j ->
   Int.cmp op (Int.repr i) (Int.repr j) = false ->
   Zcmp (negate_comparison op) i j.
Proof.
intros.
apply int_cmp_repr; auto.
rewrite Int.negate_cmp.
rewrite H1; reflexivity.
Qed.

Lemma typed_false_of_bool:
 forall x, typed_false tint (Val.of_bool x) -> (x=false).
Proof.
unfold typed_false; simpl.
unfold strict_bool_val, Val.of_bool; simpl.
destruct x; simpl;  intuition congruence.
Qed.

Lemma typed_true_of_bool:
 forall x, typed_true tint (Val.of_bool x) -> (x=true).
Proof.
unfold typed_true; simpl.
unfold strict_bool_val, Val.of_bool; simpl.
destruct x; simpl;  intuition congruence.
Qed.

Ltac fancy_intro :=
 let H := fresh in
 intro H; 
 try simple apply ptr_eq_e in H;
 match type of H with
 | ?P => clear H; assert (H:P) by auto; clear H
 | ?x = ?y => first [subst x | subst y 
                             | is_var x; rewrite H 
                             | is_var y; rewrite <- H
                             | idtac]
 | isptr ?x => let Hx := fresh "P" x in rename H into Hx
 | is_pointer_or_null ?x => let Hx := fresh "PN" x in rename H into Hx
 | typed_false _ (Val.of_bool _) =>  
                    simple apply typed_false_of_bool in H
 | typed_true _ (Val.of_bool _) =>  
                    simple apply typed_true_of_bool in H
 | _ => try solve [discriminate H]
 end.

Ltac normalize1 := 
         match goal with      
            | |- context [@andp ?A (@LiftNatDed ?T ?B ?C) ?D ?E ?F] =>
                      change (@andp A (@LiftNatDed T B C) D E F) with (D F && E F)
            | |- context [@later ?A  (@LiftNatDed ?T ?B ?C) (@LiftIndir ?X1 ?X2 ?X3 ?X4 ?X5) ?D ?F] =>
                   change (@later A  (@LiftNatDed T B C) (@LiftIndir X1 X2 X3 X4 X5) D F) 
                     with (@later B C X5 (D F))   
            | |- context [@sepcon ?A (@LiftNatDed ?B ?C ?D) 
                                                         (@LiftSepLog ?E ?F ?G ?H) ?J ?K ?L] =>
                   change (@sepcon A (@LiftNatDed B C D) (@LiftSepLog E F G H) J K L)
                      with (@sepcon C D H (J L) (K L))
            | |- context [(?P && ?Q) * ?R] => rewrite (corable_andp_sepcon1 P Q R) by (auto with norm)
            | |- context [?Q * (?P && ?R)] => rewrite (corable_sepcon_andp1 P Q R) by (auto with norm)
            | |- context [(?Q && ?P) * ?R] => rewrite (corable_andp_sepcon2 P Q R) by (auto with norm)
            | |- context [?Q * (?R && ?P)] => rewrite (corable_sepcon_andp2 P Q R) by (auto with norm)
            | |-  derives ?A   ?B => match A with 
                   | FF => apply FF_left
                   | !! _ => apply derives_extract_prop0
                   | exp (fun y => _) => apply imp_extract_exp_left; (intro y || intro)
                   | !! _ && _ => apply derives_extract_prop
                   | _ && !! _ => apply derives_extract_prop'
                   | context [ ((!! ?P) && ?Q) && ?R ] => rewrite (andp_assoc (!!P) Q R)
                   | context [ ?Q && (!! ?P && ?R)] =>
                                  match Q with !! _ => fail 2 | _ => rewrite (andp_assoc' (!!P) Q R) end
                 (* In the next four rules, doing it this way (instead of leaving it to autorewrite)
                    preserves the name of the "y" variable *)
                   | context [andp (exp (fun y => _)) _] => 
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [andp _ (exp (fun y => _))] => 
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [sepcon (exp (fun y => _)) _] => 
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [sepcon _ (exp (fun y => _))] => 
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                                apply imp_extract_exp_left; intro y
                   end
              | |- TT |-- !! _ => apply TT_prop_right
              | |- _ |-- TT => apply TT_right
              | |- _ => solve [auto with typeclass_instances]
              | |- _ |-- !! (?x = ?y) && _ => 
                            (rewrite (prop_true_andp' (x=y))
                                            by (unfold y; reflexivity); unfold y in *; clear y) ||
                            (rewrite (prop_true_andp' (x=y))
                                            by (unfold x; reflexivity); unfold x in *; clear x)
              | |- _ = ?x -> _ => intro; subst x
              | |- ?x = _ -> _ => intro; subst x
              | |- ptr_eq ?x ?y -> _ => fancy_intro; first [subst x | subst y | idtac]
              |  |- ?ZZ -> ?YY => match type of ZZ with 
                                               | Prop => 
                                                 let Z1 := fresh "YY" in set (Z1:=YY); norm_rewrite; unfold Z1; clear Z1;
                                                   (simple apply and_rect ||    
                                                    (let H := fresh in
                                                       ((assert (H:ZZ) by auto; clear H; intros _) || intro H)))
                                               | _ => intros _
                                              end
              | |- _ => progress (norm_rewrite); auto with typeclass_instances
              | |- forall _, _ => let x := fresh "x" in (intro x; repeat normalize1; try generalize dependent x)
              end.

Lemma go_lower_lem1:
  forall (P1 P: Prop) (QR PQR: mpred),
      (P1 -> prop P && QR |-- PQR) ->
      (prop (P1 /\ P ) && QR |-- PQR).
Proof.
 intros.
 apply derives_extract_prop; intros [? ?].
 apply derives_trans with (!!P && QR).
 apply andp_right; auto. apply prop_right; auto.
 apply H; auto.
Qed.

Lemma go_lower_lem1':
  forall (P1 P2 P: Prop) (QR PQR: mpred),
      (prop (P1 /\ (P2 /\ P)) && QR |-- PQR) ->
      (prop ((P1 /\ P2) /\ P ) && QR |-- PQR).
Proof.
 intros.
 eapply derives_trans;  [ | apply H].
 apply andp_derives; auto.
 apply prop_derives; intuition.
Qed.


Hint Rewrite <- sepcon_assoc : gather_prop.

Ltac normalize := 
   autorewrite with gather_prop;
   repeat (((repeat simple apply go_lower_lem1'; simple apply go_lower_lem1)
              || simple apply derives_extract_prop
              || simple apply derives_extract_prop');
              fancy_intro);
   repeat normalize1; try contradiction.

(****** END experimental normalize ******************)


(* The following line should not be needed, and was not needed
 in Coq 8.3, but in Coq 8.4 it seems to be necessary. *)
Hint Resolve (@LiftClassicalSep environ) : typeclass_instances.

Definition func_ptr' f v := func_ptr f v && emp.

Lemma lift0_unfold: forall {A} (f: A)  rho,  lift0 f rho = f.
Proof. reflexivity. Qed.

Lemma lift0_unfoldC: forall {A} (f: A) (rho: environ),  `f rho = f.
Proof. reflexivity. Qed.

Lemma lift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        lift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift1_unfoldC: forall {A1 B} (f: A1 -> B) a1 (rho: environ),
        `f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        lift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift2_unfoldC: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 (rho: environ),
        `f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.

Lemma lift3_unfold: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: environ),
        lift3 f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma lift3_unfoldC: forall {A1 A2 A3 B} (f: A1 -> A2 -> A3 -> B) a1 a2 a3 (rho: environ),
        `f a1 a2 a3 rho = f (a1 rho) (a2 rho) (a3 rho).
Proof. reflexivity. Qed.

Lemma lift4_unfold: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: environ),
        lift4 f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

Lemma lift4_unfoldC: forall {A1 A2 A3 A4 B} (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4 (rho: environ),
        `f a1 a2 a3 a4 rho = f (a1 rho) (a2 rho) (a3 rho) (a4 rho).
Proof. reflexivity. Qed.

Hint Rewrite @lift0_unfold @lift1_unfold @lift2_unfold @lift3_unfold @lift4_unfold : norm.
Hint Rewrite @lift0_unfoldC @lift1_unfoldC @lift2_unfoldC @lift3_unfoldC @lift4_unfoldC : norm.

Lemma subst_lift0: forall {A} id v (f: A),
        subst id v (lift0 f) = lift0 f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift0': forall {A} id v (f: A),
        subst id v (fun _ => f) = (fun _ => f).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift0C:
  forall {B} id (v: environ -> val) (f: B) , 
          subst id v (`f) = `f.
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift0 (*@subst_lift0'*) @subst_lift0C : subst.

Lemma subst_lift1:
  forall {A1 B} id v (f: A1 -> B) a, 
          subst id v (lift1 f a) = lift1 f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1':
  forall {A1 B} id v (f: A1 -> B) a, 
          subst id v (fun rho => f (a rho)) = fun rho => f (subst id v a rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift1C:
  forall {A1 B} id (v: environ -> val) (f: A1 -> B) (a: environ -> A1), 
          subst id v (`f a)  = `f (subst id v a).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift1 (*@subst_lift1'*) @subst_lift1C  : subst.

Lemma subst_lift2:
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b, 
          subst id v (lift2 f a b) = lift2 f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2':
  forall {A1 A2 B} id v (f: A1 -> A2 -> B) a b, 
          subst id v (fun rho => f (a rho) (b rho)) = fun rho => f (subst id v a rho) (subst id v b rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift2C:
  forall {A1 A2 B} id (v: environ -> val) (f: A1 -> A2 -> B) (a: environ -> A1) (b: environ -> A2), 
          subst id v (`f a b) = `f (subst id v a) (subst id v b).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift2 (*@subst_lift2'*) @subst_lift2C : subst.

Lemma subst_lift3:
  forall {A1 A2 A3 B} id v (f: A1 -> A2 -> A3 -> B) a1 a2 a3, 
          subst id v (lift3 f a1 a2 a3) = lift3 f (subst id v a1) (subst id v a2) (subst id v a3).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3':
  forall {A1 A2 A3 B} id v (f: A1 -> A2 -> A3 -> B) a1 a2 a3, 
          subst id v (fun rho => f (a1 rho) (a2 rho) (a3 rho)) = 
          fun rho => f (subst id v a1 rho) (subst id v a2 rho) (subst id v a3 rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift3C:
  forall {A1 A2 A3 B} id (v: environ -> val) (f: A1 -> A2 -> A3 -> B) 
                  (a1: environ -> A1) (a2: environ -> A2) (a3: environ -> A3), 
          subst id v (`f a1 a2 a3) = `f (subst id v a1) (subst id v a2) (subst id v a3).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift3 (*@subst_lift3'*) @subst_lift3C : subst.

Lemma subst_lift4:
  forall {A1 A2 A3 A4 B} id v (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4, 
          subst id v (lift4 f a1 a2 a3 a4) = lift4 f (subst id v a1) (subst id v a2) (subst id v a3) (subst id v a4).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4':
  forall {A1 A2 A3 A4 B} id v (f: A1 -> A2 -> A3 -> A4 -> B) a1 a2 a3 a4, 
          subst id v (fun rho => f (a1 rho) (a2 rho) (a3 rho) (a4 rho)) = 
          fun rho => f (subst id v a1 rho) (subst id v a2 rho) (subst id v a3 rho) (subst id v a4 rho).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Lemma subst_lift4C:
  forall {A1 A2 A3 A4 B} id (v: environ -> val) (f: A1 -> A2 -> A3 -> A4 -> B) 
                  (a1: environ -> A1) (a2: environ -> A2) (a3: environ -> A3) (a4: environ -> A4), 
          subst id v (`f a1 a2 a3 a4) = `f (subst id v a1) (subst id v a2) (subst id v a3) (subst id v a4).
Proof.
intros. extensionality rho; reflexivity.
Qed.

Hint Rewrite @subst_lift4 (*@subst_lift4'*) @subst_lift4C : subst.


Lemma semax_ff:
  forall Espec Delta c R,  
   @semax Espec Delta FF c R.
Proof.
intros.
apply semax_pre_post with (FF && FF) R.
apply andp_left2. apply andp_right; auto.
intros; apply andp_left2; auto.
apply semax_extract_prop. intros; contradiction.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Espec Delta (R: ret_assert) P c,
   (forall ek vl, local (tc_environ (exit_tycon c Delta ek)) &&  R' ek vl |-- R ek vl) ->
   @semax Espec Delta P c R' ->  @semax Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
Qed.

Lemma semax_post_flipped:
  forall (R' : ret_assert) Espec (Delta : tycontext) (R : ret_assert)
         (P : environ->mpred) (c : statement),
        @semax Espec Delta P c R' -> 
       (forall (ek : exitkind) (vl : option val),
        local (tc_environ (exit_tycon c Delta ek)) && R' ek vl |-- R ek vl) ->
       @semax Espec Delta P c R.
Proof. intros; eapply semax_post; eassumption. Qed.


Lemma semax_post0:
 forall (R': ret_assert) Espec Delta (R: ret_assert) P c,
   (R' |-- R) ->
   @semax Espec Delta P c R' ->  @semax Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply andp_left2; auto.
intros. apply andp_left2; auto.
apply H.
Qed.

Lemma semax_post': forall R' Espec Delta R P c,
           R' |-- R ->
      @semax Espec Delta P c (normal_ret_assert R') ->
      @semax Espec Delta P c (normal_ret_assert R).
Proof. intros. eapply semax_post; eauto. intros. apply andp_left2.
  intro rho; unfold normal_ret_assert; normalize.
 simpl. 
 repeat apply andp_derives; auto.
Qed.

Lemma semax_pre_simple:
 forall P' Espec Delta P c R,
     (local (tc_environ Delta) && P |-- P') ->
     @semax Espec Delta P' c R  -> @semax Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; eauto.
intros; apply andp_left2; auto.
Qed.

Lemma extract_exists_pre:
      forall
        (A : Type) (P : A -> environ->mpred) (c : Clight.statement)
         Espec Delta  (R : ret_assert),
       (forall x : A, @semax Espec Delta (P x) c R) ->
       @semax Espec Delta (exp (fun x => P x)) c R.
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
  forall {Espec: OracleKind} {A: Type} (x: A) Delta 
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
apply normal_ret_assert_derives.
apply exp_right with x; auto.
Qed.

Lemma sequential:
  forall Espec Delta P c Q,
        @semax Espec Delta P c (normal_ret_assert (Q EK_normal None)) ->
          @semax Espec Delta P c Q.
intros. eapply semax_post; eauto.
 intros. intro rho. unfold local,lift1; simpl.
 unfold normal_ret_assert; simpl.
 normalize.
Qed.

Lemma sequential': 
    forall Q Espec Delta P c R,
               @semax Espec Delta P c (normal_ret_assert Q) -> 
               @semax Espec Delta P c (overridePost Q R).
Proof.
intros.
apply semax_post with (normal_ret_assert Q); auto.
intros.
unfold normal_ret_assert, overridePost.
normalize.
rewrite if_true; auto.
apply andp_left2; auto.
Qed.

Lemma bool_val_int_eq_e: 
  forall i j, Cop.bool_val (Val.of_bool (Int.eq i j)) type_bool = Some true -> i=j.
Proof.
 intros.
 revert H; case_eq (Val.of_bool (Int.eq i j)); simpl; intros; inv H0.
 pose proof (Int.eq_spec i j).
 revert H H0; case_eq (Int.eq i j); intros; auto.
 simpl in H0; unfold Vfalse in H0. inv H0. rewrite Int.eq_true in H2. inv H2.
Qed.

Lemma bool_val_notbool_ptr:
    forall v t,
   match t with Tpointer _ _ => True | _ => False end ->
   (Cop.bool_val (force_val (Cop.sem_notbool v t)) type_bool = Some true) = (v = nullval).
Proof.
 intros.
 destruct t; try contradiction. clear H.
 apply prop_ext; split; intros.
 destruct v; simpl in H; try discriminate.
 apply bool_val_int_eq_e in H. subst; auto.
 subst. simpl. auto.
Qed.

Definition retval : environ -> val := eval_id ret_temp.

Hint Rewrite eval_id_same : norm.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : norm.

Lemma retval_get_result1: 
   forall i rho, retval (get_result1 i rho) = (eval_id i rho).
Proof. intros. unfold retval, get_result1. simpl.
 normalize. 
Qed.
Hint Rewrite retval_get_result1 : norm.

Lemma retval_lemma1:
  forall rho v,     retval (env_set rho ret_temp v) = v.
Proof.
 intros. unfold retval.  normalize.
Qed.
Hint Rewrite retval_lemma1 : norm.

Lemma retval_make_args:
  forall v rho, retval (make_args (ret_temp::nil) (v::nil) rho) = v.
Proof. intros.  unfold retval, eval_id; simpl. try rewrite Map.gss. reflexivity.
Qed.
Hint Rewrite retval_make_args: norm.

Lemma simpl_and_get_result1:
  forall (Q R: environ->mpred) i,
    `(Q && R) (get_result1 i) = `Q (get_result1 i) && `R (get_result1 i).
Proof. intros. reflexivity. Qed.
Hint Rewrite simpl_and_get_result1 : norm.

Lemma liftx_local_retval:
  forall (P: val -> Prop) i,
   `(local (`P retval)) (get_result1 i) = local (`P (eval_id i)).
Proof. intros. reflexivity. Qed.
Hint Rewrite liftx_local_retval : norm.

Lemma ret_type_initialized:
  forall i Delta, ret_type (initialized i Delta) = ret_type Delta.
Proof.
intros.
unfold ret_type; simpl.
unfold initialized; simpl.
destruct ((temp_types Delta) ! i); try destruct p; reflexivity.
Qed.
Hint Rewrite ret_type_initialized : norm.

Hint Rewrite bool_val_notbool_ptr using (solve [simpl; auto]) : norm.

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
apply pred_ext; normalize.
repeat apply andp_right; auto.
apply prop_right; repeat split; auto.
apply andp_right; auto.
apply prop_right; repeat split; auto.
Qed.
Hint Rewrite insert_local:  norm.

Lemma go_lower_lem2:
  forall  (QR PQR: mpred),
      (QR |-- PQR) ->
      (prop True && QR |-- PQR).
Proof.
 intros.
 apply derives_extract_prop; intro; auto.
Qed.

Lemma go_lower_lem6:
  forall {A} P (Q: A -> environ->mpred) PQR,
    (forall x, P && Q x |-- PQR) ->
    P && exp Q |-- PQR.
Proof.
normalize.
Qed.

Lemma go_lower_lem7:
  forall (R1: environ->mpred) (Q1: environ -> Prop) P Q R PQR,
      R1 && (PROPx P (LOCALx (Q1::Q) (SEPx R))) |-- PQR ->
      (R1 && local Q1) && (PROPx P (LOCALx Q (SEPx R))) |-- PQR.
Proof.
intros.
rewrite andp_assoc. rewrite insert_local.
auto.
Qed.

Lemma go_lower_lem8:
  forall (R1 R2 R3: environ->mpred) PQR PQR',
      ((R1 && R2) && R3) && PQR |-- PQR' ->
      (R1 && (R2 && R3)) && PQR |-- PQR'.
Proof.
 intros. rewrite <- andp_assoc; auto.
Qed.

Lemma go_lower_lem9:
  forall (Q1: environ -> Prop) P Q R PQR,
      PROPx P (LOCALx (Q1::Q) (SEPx R)) |-- PQR ->
      local Q1 && (PROPx P (LOCALx Q (SEPx R))) |-- PQR.
Proof.
intros. rewrite insert_local; auto.
Qed.

Lemma go_lower_lem10:
  forall (R1 R2 R3: environ->mpred) PQR',
      (R1 && R2) && R3 |-- PQR' ->
      (R1 && (R2 && R3)) |-- PQR'.
Proof.
 intros. rewrite <- andp_assoc; auto.
Qed.

Lemma go_lower_lem11:
 forall P R,
   P |-- R ->
   P |-- prop True && R.
Proof.
 intros. normalize.
Qed.

Lemma go_lower_lem20:
  forall QR QR',
    QR |-- QR' ->
    PROPx nil QR |-- QR'.
Proof. unfold PROPx; intros; intro rho; normalize. Qed.

Lemma Vint_inj': forall i j,  (Vint i = Vint j) =  (i=j).
Proof. intros; apply prop_ext; split; intro; congruence. Qed.

Lemma TT_andp_right {A}{NA: NatDed A}:
 forall P Q, TT |-- P -> TT |-- Q -> TT |-- P && Q.
Proof.
  intros. apply andp_right; auto.
Qed. 

Lemma TT_prop_right {A}{NA: NatDed A}:
  forall P: Prop , P -> TT |-- prop P.
Proof. intros. apply prop_right. auto.
Qed.

Ltac go_lowerx :=
   unfold PROPx, LOCALx,SEPx, local, lift1; unfold_lift; intro rho; simpl;
   repeat rewrite andp_assoc;
   repeat ((simple apply go_lower_lem1 || apply derives_extract_prop || apply derives_extract_prop'); intro);
   try apply prop_left;
   repeat rewrite prop_true_andp by assumption;
   try apply derives_refl.

Ltac go_lower1 :=
 repeat match goal with 
   | |- andp _ (exp (fun y => _)) |-- _ => 
          (* Note: matching in this special way uses the user's name 'y'
                 as a hypothesis; thats we use a "match goal" 
                 rather than just trying to apply the various lemmas *)
             apply go_lower_lem6; intro y
   | |- (_ && local _) && (PROPx _ (LOCALx _ _)) |-- _ =>
                     apply go_lower_lem7
   | |- (_ && (_ && _)) && (PROPx _ _) |-- _ =>
               apply go_lower_lem8
   | |- local _ && (PROPx _ (LOCALx _ _)) |-- _ =>
                     apply go_lower_lem9
   | |- _ && (_ && _) |-- _ => 
                    apply go_lower_lem10
   end.

Lemma trivial_typecheck:
  forall P, P |-- local (denote_tc_assert tc_TT).
Proof. intros. intro rho. apply prop_right. apply I. Qed.


Lemma overridePost_normal_right:
  forall P Q R, 
   P |-- Q ->
   P |-- overridePost Q R EK_normal None.
Proof. intros.
  intro rho; unfold overridePost; simpl.
  normalize.
Qed.

Fixpoint fold_right_sepcon rho (l: list(environ->mpred)) : mpred :=
 match l with 
 | nil => emp
 | b::nil => b rho
 | b::r => b rho * fold_right_sepcon rho r
 end.

Fixpoint fold_right_andp rho (l: list (environ -> Prop)) : Prop :=
 match l with 
 | nil => True
 | b::nil => b rho
 | b::r => b rho /\ fold_right_andp rho r
 end.

Fixpoint fold_right_and P0 (l: list Prop) : Prop :=
 match l with 
 | nil => P0
 | b::r => b  /\ fold_right_and P0 r
 end.

Lemma go_lower_lem27a:
 forall P Q' R' rho,
  P |--  andp (prop (fold_right_andp rho Q'))  (fold_right_sepcon rho R') ->
  P |-- LOCALx Q' (SEPx R') rho.
Proof.
 intros. unfold SEPx.
 eapply derives_trans; [ apply H |].
 clear.
 unfold LOCALx. unfold local. super_unfold_lift; simpl.
 apply andp_derives.
 apply prop_left; intro H;  apply prop_right; revert H.
 induction Q'; simpl; auto.
 destruct Q'; simpl in *. auto.
 intros [? ?]; split; auto.
 induction R'; simpl; auto.
 destruct R'. apply derives_trans with (a rho * emp).
 rewrite sepcon_emp; auto.
 apply sepcon_derives; auto.
 apply sepcon_derives; auto.
Qed.

Lemma refold_frame:
 forall rho (F: list(environ->mpred)) A, 
   match F with nil => A | _ :: _ => A * fold_right_sepcon rho F end =
             A * fold_right sepcon emp F rho.
Proof. 
 induction F; simpl; intros; auto.
 rewrite sepcon_emp; auto.
 f_equal; auto.
Qed.


Lemma typed_true_isptr:
 forall t, match t with Tpointer _ _ => True | Tarray _ _ _ => True | Tfunction _ _ _ => True | _ => False end ->
          typed_true t = isptr.
Proof.
intros. extensionality x; apply prop_ext.
destruct t; try contradiction; unfold typed_true, strict_bool_val;
destruct x; intuition; try congruence;
destruct (Int.eq i Int.zero); inv H0.
Qed.

Hint Rewrite typed_true_isptr using apply I : norm.

Ltac super_unfold_lift_in H :=
   cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry lift lift0
    lift1 lift2 lift3] beta iota in H.

Ltac super_unfold_lift' := 
  cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry lift lift0
    lift1 lift2 lift3] beta iota.

Lemma tc_eval_id_i:
  forall Delta t i rho, 
               tc_environ Delta rho -> 
              (temp_types Delta)!i = Some (t,true) ->
              tc_val t (eval_id i rho).
Proof.
intros.
rewrite tc_val_eq.
unfold tc_environ in H.
destruct rho. 
destruct H as [? _].
destruct (H i true t H0) as [v [? ?]].
unfold eval_id. simpl in *. rewrite H1. simpl; auto.
destruct H2. inv H2. auto.
Qed.

Lemma is_int_e:
 forall v , is_int v -> exists n, v = Vint n.
Proof.
intros. destruct v; inv H; eauto.
Qed.

Definition name (id: ident) := True.

Tactic Notation "name" ident(s) constr(id) := 
    assert (s: name id) by apply I.

Definition reflect_temps_f (rho: environ) (b: Prop) (i: ident) (t: type*bool) : Prop :=
    match t with
    | (t',true) => tc_val t' (eval_id i rho) /\ b
    |  _  => b
   end.

Definition reflect_temps (Delta: tycontext) (rho: environ) : Prop :=
    PTree.fold (reflect_temps_f rho) (temp_types Delta) True.

Lemma reflect_temps_valid:
  forall Delta rho,
    tc_environ Delta rho -> reflect_temps Delta rho.
Proof.
intros.
unfold reflect_temps.
rewrite PTree.fold_spec.
remember  (PTree.elements (temp_types Delta)) as el.
assert (forall i v, In (i,v) el -> (temp_types Delta) ! i = Some v).
 intros. subst el. apply PTree.elements_complete; auto.
clear Heqel.
assert (forall b: Prop, b -> fold_left
  (fun (a : Prop) (p : positive * (type * bool)) =>
   reflect_temps_f rho a (fst p) (snd p)) el b);
  [ | auto].
revert H0; induction el; simpl; intros; auto.
unfold reflect_temps_f at 2.
destruct a as [i [t [|]]]; simpl; auto.
apply IHel; auto.
split; auto.
eapply tc_eval_id_i.
eassumption.
apply H0; auto.
Qed.

Definition abbreviate {A:Type} (x:A) := x.
Implicit Arguments abbreviate [[A][x]].

Ltac findvars :=
 match goal with DD: tc_environ ?Delta ?rho |- _ =>
  let H := fresh in
    assert (H := reflect_temps_valid _ _ DD);
    try (unfold Delta in H);
   cbv beta iota zeta delta [abbreviate PTree.fold PTree.append PTree.xfold temp_types fst snd
             reflect_temps reflect_temps_f] in H;
   simpl in H;
   repeat match goal with
    | Name: name ?J |- context [eval_id ?J rho] =>
            fold J in H;
            clear Name;
           forget (eval_id J rho) as Name
    | |- context [eval_id ?J rho] =>
           try fold J in H;
           let Name := fresh "_id" in forget (eval_id J rho) as Name
    | Name: name _ |- _ => 
          clear Name
     end;
    repeat match type of H with
                | _ (eval_id _ _) /\ _ =>  destruct H as [_ H]
                | is_int ?i /\ _ => let TC := fresh "TC" in destruct H as [TC H]; 
                                let i' := fresh "id" in rename i into i';
                               apply is_int_e in TC; destruct TC as [i TC]; subst i'
                | _ /\ _ => destruct H as [?TC H]
                end;
    clear H
 end.

Ltac findvar := 
match goal with
    | H: tc_environ ?Delta ?RHO, Name: name ?J |- _ =>
            clear Name; 
     match goal with
     | |- context [ J ] => 
     let Hty := fresh in let t := fresh "t" in evar (t : type);
         assert (Hty: (temp_types Delta) ! J = Some (t, true))
              by (unfold t; simpl; reflexivity);
       let TC := fresh "TC" in
       assert (TC: tc_val t (eval_id J RHO)) 
            by (exact  (tc_eval_id_i Delta _ _ _ H Hty));
       unfold t in *; clear t Hty;
       simpl tc_val in TC; 
       first [let Htc' := fresh in
                destruct (is_int_e _ TC) as [Name Htc'];
                rewrite Htc' in *;
                clear TC Htc'
              | forget (eval_id J RHO) as Name
              ]
     | _ => idtac
    end
   | H: tc_environ ?Delta ?RHO |- context [eval_id ?J ?RHO] =>
            let Name := fresh "_id" in name Name J; findvar
end.

Lemma Vint_inj: forall x y, Vint x = Vint y -> x=y.
Proof. congruence. Qed.
Lemma sem_cast_id:
  forall Delta rho,
      tc_environ Delta rho ->
  forall t1 t3 id,
  Cop.classify_cast t1 t3 = Cop.cast_case_neutral ->
  match (temp_types Delta)!id with Some (Tpointer _ _, true) => true | _ => false end = true ->
  force_val (sem_cast t1 t3 (eval_id id rho)) = eval_id id rho.
Proof.
intros.
 revert H1; case_eq ((temp_types Delta) ! id); intros; try discriminate.
 destruct p as [t2 ?].
 destruct t2; inv H2.
 destruct b; inv H4.
 pose proof (tc_eval_id_i _ _ _ _ H H1).
 rewrite tc_val_eq in H2.
 destruct (eval_id id  rho); inv H2.
 pose proof (Int.eq_spec i Int.zero). rewrite H4 in H2. subst. clear H4.
 destruct t1; destruct t3; inv H0; 
  try (destruct i; inv H3); try (destruct i0; inv H2); try reflexivity.
 destruct t1; destruct t3; inv H0; 
  try (destruct i0; inv H3); try (destruct i1; inv H2); try reflexivity.
Qed.

Lemma sem_cast_pointer2':
  forall (v : val) (t1 t2: type),
  match t1 with Tpointer _ _ | Tint I32 _ _ => True | _ => False end ->
  match t2 with Tpointer _ _ | Tint I32 _ _ => True | _ => False end ->
  is_pointer_or_null v -> force_val (sem_cast t1 t2 v) = v.
Proof.
intros.
unfold sem_cast, classify_cast.
subst.
destruct t1; try contradiction; try destruct i; try contradiction; simpl; auto;
destruct t2; try contradiction; try destruct i; try contradiction; simpl; auto;
destruct v; inv H1; simpl; auto.
Qed.

Hint Rewrite sem_cast_pointer2' using (try apply I; try assumption; reflexivity) : norm.

Lemma typecheck_val_eq:
  forall v t, (typecheck_val v t = true) = tc_val t v.
Proof. intros. rewrite tc_val_eq. reflexivity. Qed.
Hint Rewrite typecheck_val_eq : norm.

Lemma sem_cast_pointer2: 
  forall v t1 t2 t3 t1' t2',
   t1' = Tpointer t1 noattr ->
   t2' = Tpointer t2 noattr ->
   tc_val (Tpointer t3 noattr) v ->
   force_val (sem_cast t1' t2' v) = v.
Proof.
intros.
subst.
hnf in H1. destruct v; inv H1; reflexivity.
Qed.

Lemma force_eval_var_int_ptr :
forall Delta rho i t,
tc_environ Delta rho ->
tc_lvalue Delta (Evar i t) rho -> 
          force_val
            match eval_var i t rho with
            | Vundef => None
            | Vint _ => Some (eval_var i t rho)
            | Vlong _ => None
            | Vfloat _ => None
            | Vptr _ _ => Some (eval_var i t rho)
            end = eval_var i t rho.
Proof.
intros.
 pose proof (expr_lemmas.typecheck_lvalue_sound _ _ _ H H0).
 simpl in H1.
 destruct (eval_var i t rho); inv H1; simpl; auto.
Qed.


Lemma force_eval_var_int_ptr':
 forall i t rho,
  (exists Delta,
    tc_environ Delta rho /\  tc_lvalue Delta (Evar i t) rho) ->
  force_val
            match eval_var i t rho with
            | Vundef => None
            | Vint _ => Some (eval_var i t rho)
            | Vlong _ => None
            | Vfloat _ => None
            | Vptr _ _ => Some (eval_var i t rho)
            end = eval_var i t rho.
Proof.
intros.
 destruct H as [Delta [? ?]];
 eapply force_eval_var_int_ptr; eauto.
Qed.

Hint Rewrite force_eval_var_int_ptr' using 
   match goal with Delta := _ : tycontext |- _ => 
       exists Delta; split; hnf; solve [auto]
   end : norm.     

Lemma is_pointer_or_null_force_int_ptr:
   forall v, is_pointer_or_null v -> (force_val
        match v with
        | Vundef => None
        | Vint _ => Some v
        | Vlong _ => None
        | Vfloat _ => None
        | Vptr _ _ => Some v end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite is_pointer_or_null_force_int_ptr using assumption : norm.


Lemma is_pointer_force_int_ptr:
   forall v, isptr v -> (force_val
        match v with
        | Vundef => None
        | Vint _ => Some v
        | Vlong _ => None
        | Vfloat _ => None
        | Vptr _ _ => Some v end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite is_pointer_force_int_ptr using assumption : norm.


Lemma is_pointer_or_null_match :
   forall v, is_pointer_or_null v -> 
        (match v with
        | Vundef => None
        | Vint _ => Some v
        | Vlong _ => None
        | Vfloat _ => None
        | Vptr _ _ => Some v end) = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite is_pointer_or_null_match using assumption : norm.

Lemma is_pointer_force_int_ptr2:
   forall v, isptr v -> 
        match v with
        | Vundef => None
        | Vint _ => Some v
        | Vlong _ => None
        | Vfloat _ => None
        | Vptr _ _ => Some v end = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite is_pointer_force_int_ptr2 using assumption : norm.

Lemma is_pointer_or_null_force_int_ptr2:
   forall v, is_pointer_or_null (force_val
        match v with
        | Vundef => None
        | Vint _ => Some v
        | Vlong _ => None
        | Vfloat _ => None
        | Vptr _ _ => Some v end) -> (force_val
        match v with
        | Vundef => None
        | Vint _ => Some v
        | Vlong _ => None
        | Vfloat _ => None
        | Vptr _ _ => Some v end) = v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.

Hint Rewrite is_pointer_or_null_force_int_ptr2 using assumption : norm.

Lemma isptr_match : forall w0,
is_pointer_or_null
         match
           match w0 with
           | Vundef => None
           | Vint _ => Some w0
           | Vlong _ => None
           | Vfloat _ => None
           | Vptr _ _ => Some w0
           end
         with
         | Some v' => v'
         | None => Vundef
         end
= is_pointer_or_null w0.
intros.
destruct w0; auto.
Qed.

Hint Rewrite isptr_match : norm.

Lemma eval_cast_neutral_var:
 forall Delta rho, 
  tc_environ Delta rho -> 
  forall i t,
   tc_lvalue Delta (Evar i t) rho ->
  sem_cast_neutral (eval_var i t rho) = Some (eval_var i t rho).
Proof.
intros.
 pose proof (expr_lemmas.typecheck_lvalue_sound _ _ _ H H0).
 simpl in H1.
 destruct (eval_var i t rho); inv H1; simpl; auto.
Qed.
  
Lemma eval_cast_neutral_var':
 forall i t rho,
  (exists Delta,
    tc_environ Delta rho /\  tc_lvalue Delta (Evar i t) rho) ->
  sem_cast_neutral (eval_var i t rho) = Some (eval_var i t rho).
Proof.
intros.
 destruct H as [Delta [? ?]];
 eapply eval_cast_neutral_var; eauto.
Qed.

Hint Rewrite eval_cast_neutral_var' using 
   match goal with Delta := _ : tycontext |- _ => 
       exists Delta; split; hnf; solve [auto]
   end : norm.

Lemma eval_cast_neutral_tc_val:
   forall v, (exists t, tc_val t v /\ is_pointer_type t = true) -> 
       sem_cast_neutral v = Some v.
Proof.
intros. destruct H as [t [? ?]]; destruct t,v; inv H0; inv H; reflexivity.
Qed.

Hint Rewrite eval_cast_neutral_tc_val using solve [eauto] : norm.

Lemma eval_cast_neutral_is_pointer_or_null:
   forall v, is_pointer_or_null v -> sem_cast_neutral v = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite eval_cast_neutral_is_pointer_or_null using assumption : norm.

Lemma is_pointer_or_null_eval_cast_neutral:
  forall v, is_pointer_or_null (force_val (sem_cast_neutral v)) = is_pointer_or_null v.
Proof. destruct v; reflexivity. Qed.
Hint Rewrite is_pointer_or_null_eval_cast_neutral : norm.


Lemma eval_cast_neutral_isptr:
   forall v, isptr v -> sem_cast_neutral v = Some v.
Proof.
intros. destruct v; inv H; reflexivity.
Qed.
Hint Rewrite eval_cast_neutral_isptr using assumption : norm.

Ltac eval_cast_simpl :=
    try (try unfold eval_cast; simpl Cop.classify_cast; cbv iota);
     try match goal with H: tc_environ ?Delta ?rho |- _ =>
       repeat first [rewrite (eval_cast_neutral_var Delta rho H) by reflexivity
               | rewrite eval_cast_neutral_isptr by auto
               | rewrite (sem_cast_id Delta rho H); [ | reflexivity | reflexivity ]
               | erewrite sem_cast_pointer2; [ | | | eassumption ]; [ | reflexivity | reflexivity ]
               ]
     end.

(*
Ltac eval_cast_simpl :=
     try match goal with H: tc_environ ?Delta ?rho |- _ =>
       repeat first [rewrite (eval_cast_var Delta rho H); [ | reflexivity | hnf; simpl; normalize ]
               | rewrite (eval_cast_id Delta rho H); [ | reflexivity | reflexivity ]
               | rewrite eval_cast_int; [ | assumption]
               | erewrite eval_cast_pointer2; [ | | | eassumption ]; [ | reflexivity | reflexivity ]
               ]
     end.
*)


Lemma fold_right_nil: forall {A B} (f: A -> B -> B) (z: B),
   fold_right f z nil = z.
Proof. reflexivity. Qed.
Hint Rewrite @fold_right_nil : norm.
Hint Rewrite @fold_right_nil : subst.

Lemma fold_right_cons: forall {A B} (f: A -> B -> B) (z: B) x y,
   fold_right f z (x::y) = f x (fold_right f z y).
Proof. reflexivity. Qed.
Hint Rewrite @fold_right_cons : norm.
Hint Rewrite @fold_right_cons : subst.

Lemma grab_tc_environ:
  forall Delta P Q R S rho,
    (tc_environ Delta rho -> (PROPx P (LOCALx Q R)) rho |-- S) ->
    (PROPx P (LOCALx (tc_environ Delta :: Q) R)) rho |-- S.
Proof.
intros.
unfold PROPx,LOCALx in *; simpl in *.
normalize.
simpl in *.
 rewrite andp_assoc in *.
rewrite (prop_true_andp _ _ H0) in H.
apply derives_extract_prop.
auto.
Qed.

Arguments ret_type !Delta /.

Arguments Datatypes.id {A} x / .

Ltac unfold_for_go_lower :=
  cbv delta [PROPx LOCALx SEPx
                       eval_exprlist eval_expr eval_lvalue cast_expropt 
                       sem_cast eval_binop eval_unop force_val1 force_val2
                      tc_expropt tc_expr tc_exprlist tc_lvalue 
                      typecheck_expr typecheck_exprlist typecheck_lvalue
                      function_body_ret_assert frame_ret_assert
                      make_args' bind_ret get_result1 retval
                       classify_cast 
                       (* force_val sem_cast_neutral ... NOT THESE TWO!  *) 
                      denote_tc_assert (* tc_andp tc_iszero *)
    liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry 
     local lift lift0 lift1 lift2 lift3 
   ] beta iota.

Ltac go_lower0 := 
intros ?rho;
 try (simple apply grab_tc_environ; intro);
 repeat (progress unfold_for_go_lower; simpl).

Ltac go_lower :=
 go_lower0;
 autorewrite with go_lower;
 try findvars;
 simpl;
 autorewrite with go_lower;
 try match goal with H: tc_environ _ ?rho |- _ => clear H rho end.

Hint Rewrite eval_id_same : go_lower.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : go_lower.
Hint Rewrite Vint_inj' : go_lower.

Lemma local_unfold: forall P rho, local P rho = !! (P rho).
Proof. reflexivity. Qed.
Hint Rewrite local_unfold : norm.

Lemma lower_sepcon:
  forall P Q rho, @sepcon (environ->mpred) _ _ P Q rho = sepcon (P rho) (Q rho).
Proof. reflexivity. Qed.
Lemma lower_andp:
  forall P Q rho, @andp (environ->mpred) _ P Q rho = andp (P rho) (Q rho).
Proof. reflexivity. Qed.
Hint Rewrite lower_sepcon lower_andp : norm.

Lemma raise_sepcon:
 forall A B : environ -> mpred , 
    (fun rho: environ => A rho * B rho) = (A * B).
Proof. reflexivity. Qed.
Hint Rewrite raise_sepcon : norm.

Lemma lift_prop_unfold: 
   forall P z,  @prop (environ->mpred) _ P z = @prop mpred Nveric P.
Proof.  reflexivity. Qed.
Hint Rewrite lift_prop_unfold: norm.

Lemma andp_unfold: forall (P Q: environ->mpred) rho,
  @andp (environ->mpred) _ P Q rho = @andp mpred Nveric (P rho) (Q rho).
Proof. reflexivity. Qed.
Hint Rewrite andp_unfold: norm.

Lemma exp_unfold : forall A P rho,
 @exp (environ->mpred) _ A P rho = @exp mpred Nveric A (fun x => P x rho).
Proof.
intros. reflexivity. 
Qed.
Hint Rewrite exp_unfold: norm.


Lemma lift1_lift1_retval {A}: forall i (P: val -> A),
lift1 (lift1 P retval) (get_result1 i) = lift1 P (eval_id i).
Proof. intros.  extensionality rho. 
  unfold lift1.  f_equal; normalize.
Qed.

Lemma lift_lift_retval:
  forall (i: ident) P,
   @liftx (Tarrow environ (LiftEnviron mpred))
     (@liftx (Tarrow val (LiftEnviron mpred)) P retval) (get_result1 i) = `P (eval_id i).
Proof.
 reflexivity.
Qed.
Hint Rewrite lift_lift_retval: norm.


Lemma lift_lift_x:  (* generalizes lift_lift_val *)
  forall t t' P (v: t),
  (@liftx (Tarrow t (LiftEnviron t')) P (@liftx (LiftEnviron t) v)) =
  (@liftx (LiftEnviron t') (P v)).
Proof. reflexivity. Qed.
Hint Rewrite lift_lift_x : norm.

Lemma lift0_exp {A}{NA: NatDed A}:
  forall (B: Type) (f: B -> A), lift0 (exp f) = EX x:B, lift0 (f x).
Proof. intros; extensionality rho; unfold lift0. simpl.
f_equal; extensionality b; auto.
Qed.

Lemma lift0C_exp {A}{NA: NatDed A}:
  forall (B: Type) (f: B -> A), `(exp f) = EX x:B, `(f x).
Proof.
intros. unfold_lift. simpl. extensionality rho. f_equal; extensionality x; auto.
Qed.
Hint Rewrite @lift0_exp @lift0C_exp : norm.

Lemma lift0_andp {A}{NA: NatDed A}:
 forall P Q, 
   lift0 (@andp A NA P Q) = andp (lift0 P) (lift0 Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0C_andp {A}{NA: NatDed A}:
 forall P Q: A, 
  `(@andp A NA P Q) =
  andp (`P) (`Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0_prop {A}{NA: NatDed A}:
 forall P, lift0 (!! P) = !!P.
Proof. intros. extensionality rho; reflexivity. Qed.

Lemma lift0C_prop {A}{NA: NatDed A}:
 forall P, @liftx (LiftEnviron A) (@prop A NA P) = 
                  @prop (environ -> A) _ P.
Proof. reflexivity. Qed.

Lemma lift0_sepcon {A}{NA: NatDed A}{SA: SepLog A}:
 forall P Q, 
  lift0 (@sepcon A NA SA P Q) = sepcon (lift0 P) (lift0 Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.

Lemma lift0C_sepcon {A}{NA: NatDed A}{SA: SepLog A}:
 forall P Q N2 S2, 
  (@liftx (LiftEnviron A) (@sepcon A N2 S2 P Q)) = 
  (@sepcon (environ->A) _ _ 
     (@liftx (LiftEnviron A) P)
     (@liftx (LiftEnviron A) Q)).
Proof. reflexivity. Qed.

Lemma lift0_later {A}{NA: NatDed A}{IA: Indir A}:
  forall P:A, 
   lift0 (@later A NA IA P) = later  (lift0 P).
Proof. intros. reflexivity. Qed.

Lemma lift0C_later {A}{NA: NatDed A}{IA: Indir A}:
  forall P:A, 
   `(@later A NA IA P) = @later (environ->A) _ _ (`P).
Proof. intros. reflexivity. Qed.

Hint Rewrite (@lift0C_sepcon mpred _ _) : norm.
Hint Rewrite (@lift0C_andp mpred _) : norm.
Hint Rewrite (@lift0C_exp mpred _) : norm.
Hint Rewrite (@lift0C_later mpred _ _) : norm.
Hint Rewrite (@lift0C_prop mpred _) : norm.

Hint Rewrite
    @lift1_lift1_retval
    @lift0_exp
    @lift0_sepcon
    @lift0_prop
    @lift0_later
    : norm.

Lemma semax_post'': forall P Q R Espec Delta Pre Post c,
          PROPx P (LOCALx  (tc_environ (update_tycon Delta c) :: Q) (SEPx R)) |-- Post ->
      @semax Espec Delta Pre c (normal_ret_assert (PROPx P (LOCALx Q (SEPx R)))) ->
      @semax Espec Delta Pre c (normal_ret_assert Post).
Proof. intros. eapply semax_post; eauto. intros.
 intro rho. unfold local, lift1; simpl.
 apply derives_extract_prop; intro.
 unfold normal_ret_assert. normalize.
 eapply derives_trans; [ | apply H].
 unfold PROPx, LOCALx; simpl.
 apply andp_derives; auto.
 unfold local; super_unfold_lift.
 apply andp_derives; auto.
 apply prop_left; intro; apply prop_right.
 split; auto.
Qed.

Lemma fst_unfold: forall {A B} (x: A) (y: B), fst (x,y) = x.
Proof. reflexivity. Qed.
Lemma snd_unfold: forall {A B} (x: A) (y: B), snd (x,y) = y.
Proof. reflexivity. Qed.
Hint Rewrite @fst_unfold @snd_unfold : norm.

Lemma local_andp_prop:  forall P Q, local P && prop Q = prop Q && local P.
Proof. intros. apply andp_comm. Qed.
Lemma local_andp_prop1: forall P Q R, local P && (prop Q && R) = prop Q && (local P && R).
Proof. intros. rewrite andp_comm. rewrite andp_assoc. f_equal. apply andp_comm. Qed.
Hint Rewrite local_andp_prop local_andp_prop1 : norm.

Lemma local_sepcon_assoc1:
   forall P Q R, (local P && Q) * R = local P && (Q * R).
Proof.
intros.
extensionality rho; unfold local, lift1; simpl.
apply pred_ext; normalize.
Qed.
Lemma local_sepcon_assoc2:
   forall P Q R, R * (local P && Q) = local P && (R * Q).
Proof.
intros.
extensionality rho; unfold local, lift1; simpl.
apply pred_ext; normalize.
Qed.
Hint Rewrite local_sepcon_assoc1 local_sepcon_assoc2 : norm.

Definition do_canon (x y : environ->mpred) := (sepcon x y).

Ltac strip1_later P :=
 match P with 
 | do_canon ?L ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(do_canon L' R')
 | PROPx ?P ?QR => let QR' := strip1_later QR in constr:(PROPx P QR')
 | LOCALx ?Q ?R => let R' := strip1_later R in constr:(LOCALx Q R')
 | SEPx ?R => let R' := strip1_later R in constr:(SEPx R')
 | ?L::?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L'::R')
 | nil => constr:(nil)
 | ?L && ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L' && R')
 | ?L * ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L'*R')
 | |> ?L => constr:(L)
 | ?L => constr:(L)
end.

Lemma andp_later_derives {A} {NA: NatDed A}{IA: Indir A}:
  forall P Q P' Q': A, P |-- |> P' -> Q |-- |> Q' -> P && Q |-- |> (P' && Q').
Proof.
intros. rewrite later_andp. apply andp_derives; auto. Qed.

Lemma sepcon_later_derives {A} {NA: NatDed A}{SL: SepLog A}{IA: Indir A}{SI: SepIndir A}:
  forall P Q P' Q': A, P |-- |> P' -> Q |-- |> Q' -> P * Q |-- |> (P' * Q').
Proof.
intros. rewrite later_sepcon. apply sepcon_derives; auto. Qed.

Hint Resolve @andp_later_derives @sepcon_later_derives @sepcon_derives
              @andp_derives @imp_derives @now_later @derives_refl: derives.

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).

Notation " a 'OF' ta " := (a%type,ta%type) (at level 100, only parsing): formals.
Delimit Scope formals with formals.

Notation "'WITH' x : tx 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) tx (fun x => P%logic) (fun x => Q%logic))
            (at level 200, x at level 0, P at level 100, Q at level 100).

Notation "'WITH' x : tx 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) tx (fun x => P%logic) (fun x => Q%logic))
            (at level 200, x at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2)
           (fun x => let (x1,x2):=x in P%logic) (fun x => let (x1,x2):=x in Q%logic))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) (t1*t2)
           (fun x => let (x1,x2):=x in P%logic) (fun x => let (x1,x2):=x in Q%logic))
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100).


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2*t3)
           (fun x => match x with ((x1,x2),x3) => P%logic end)
           (fun x => match x with ((x1,x2),x3) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) (t1*t2*t3)
           (fun x => match x with ((x1,x2),x3) => P%logic end)
           (fun x => match x with ((x1,x2),x3) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, P at level 100, Q at level 100).


Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2*t3*t4)
           (fun x => match x with (((x1,x2),x3),x4) => P%logic end)
           (fun x => match x with (((x1,x2),x3),x4) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) (t1*t2*t3*t4)
           (fun x => match x with (((x1,x2),x3),x4) => P%logic end)
           (fun x => match x with (((x1,x2),x3),x4) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2*t3*t4)
           (fun x => match x with (((x1,x2),x3),x4) => P%logic end)
           (fun x => match x with (((x1,x2),x3),x4) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) (t1*t2*t3*t4*t5)
           (fun x => match x with ((((x1,x2),x3),x4),x5) => P%logic end)
           (fun x => match x with ((((x1,x2),x3),x4),x5) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2*t3*t4*t5)
           (fun x => match x with ((((x1,x2),x3),x4),x5) => P%logic end)
           (fun x => match x with ((((x1,x2),x3),x4),x5) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (((((x1,x2),x3),x4),x5),x6) => P%logic end)
           (fun x => match x with (((((x1,x2),x3),x4),x5,x6)) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
              x5 at level 0, x6 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (((((x1,x2),x3),x4),x5),x6) => P%logic end)
           (fun x => match x with (((((x1,x2),x3),x4),x5),x6) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, P at level 100, Q at level 100).

Lemma exp_derives {A}{NA: NatDed A}{B}:
   forall F G: B -> A, (forall x, F x |-- G x) -> exp F |-- exp G.
Proof.
intros.
apply exp_left; intro x. apply exp_right with x; auto.
Qed.

Lemma prop_true_andp1 {A}{NA: NatDed A} :
  forall (P1 P2: Prop) Q ,
    P1 -> (!! (P1 /\ P2) && Q = !!P2 && Q).
Proof.
intros. f_equal; auto.  f_equal.  apply prop_ext; intuition.
Qed.
Hint Rewrite prop_true_andp1 using solve [auto 3 with typeclass_instances]: norm.

Lemma and_assoc': forall A B C: Prop,
  ((A /\ B) /\ C) = (A /\ (B /\ C)).
Proof.
intros. apply prop_ext; apply and_assoc.
Qed.

Lemma and_assoc'' {T}{NT: NatDed T}: forall A B C: Prop,
  !! ((A /\ B) /\ C) = !! (A /\ (B /\ C)).
Proof.
intros. rewrite and_assoc'; auto.
Qed.

Hint Rewrite @and_assoc'' using solve [auto with typeclass_instances] : norm.
Hint Rewrite @and_assoc'' using solve [auto with typeclass_instances] : gather_prop.


Lemma semax_seq': 
 forall Espec Delta P c1 P' c2 Q, 
         @semax Espec Delta P c1 (normal_ret_assert P') ->
         @semax Espec(update_tycon Delta c1) P' c2 Q ->
         @semax Espec Delta P (Ssequence c1 c2) Q.
Proof.
 intros. apply semax_seq with P'; auto.
 apply sequential'. auto. 
Qed.

Lemma semax_pre0:
 forall P' Espec Delta P c R,
     P |-- P' ->
     @semax Espec Delta P' c R  -> 
     @semax Espec Delta P c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
 apply andp_left2; auto.
Qed.

Lemma semax_pre:
 forall P' Espec Delta P1 P2 P3 c R,
     (PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3))) |-- P' ->
     @semax Espec Delta P' c R  -> 
     @semax Espec Delta (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof.
intros.
eapply semax_pre_simple; try apply H0.
 rewrite insert_local. auto.
Qed.

Ltac hoist_later_in_pre :=
     match goal with |- semax _ ?P _ _ =>
       let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
     end.

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

(* OLD VERSION:
Ltac focus_SEP n := 
   rewrite (grab_nth_SEP n); unfold nth, delete_nth.
*) 

Lemma semax_frame_PQR:
  forall Espec Delta R1 R2 P Q P' Q' R1' c,
     closed_wrt_modvars c (SEPx R2) ->
     @semax Espec Delta (PROPx P (LOCALx Q (SEPx R1))) c 
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R1')))) ->
     @semax Espec Delta (PROPx P (LOCALx Q (SEPx (R1++R2)))) c 
                     (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx (R1'++R2))))).
Proof.
intros.
replace (PROPx P (LOCALx Q (SEPx (R1 ++ R2))))
   with (PROPx P (LOCALx Q (SEPx (R1))) * SEPx R2).
eapply semax_post0; [ | apply semax_frame; eassumption].
intros ek vl rho.
unfold frame_ret_assert, normal_ret_assert; 
 destruct ek; simpl; normalize; try congruence.
match goal with |- ?A |-- ?B => replace B with A; auto end.
f_equal.
unfold PROPx,LOCALx,SEPx.
normalize.
apply pred_ext; normalize.
clear; induction R1'; simpl. rewrite emp_sepcon. auto.
rewrite sepcon_assoc. apply sepcon_derives; auto.
clear; induction R1'; simpl. rewrite emp_sepcon. auto.
rewrite sepcon_assoc. apply sepcon_derives; auto.
extensionality rho; unfold PROPx,LOCALx,SEPx.
normalize.
f_equal. f_equal.
clear; induction R1; simpl. apply emp_sepcon.
rewrite sepcon_assoc. f_equal. auto.
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


Ltac frame_SEP' L :=
  grab_indexes_SEP L;
 match goal with
 | |- @semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ => 
  rewrite <- (firstn_skipn (length L) R); 
    simpl length; unfold firstn, skipn;
    eapply semax_frame_PQR;
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

Lemma replace_SEP':
 forall n R' Espec Delta P Q Rs c Post,
 (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (my_nth n Rs TT ::  nil)))) |-- R' ->
 @semax Espec Delta (PROPx P (LOCALx Q (SEPx (replace_nth n Rs R')))) c Post ->
 @semax Espec Delta (PROPx P (LOCALx Q (SEPx Rs))) c Post.
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
clear - H.
rewrite sepcon_emp in H.
revert Rs H; induction n; destruct Rs; simpl ; intros; auto;
apply sepcon_derives; auto.
Qed.

Ltac replace_SEP n R :=
  apply (replace_SEP' (nat_of_Z n) R);
  unfold my_nth,replace_nth; simpl nat_of_Z;
   repeat simpl_nat_of_P; cbv beta iota; cbv beta iota.

Ltac replace_in_pre S S' :=
 match goal with |- @semax _ _ ?P _ _ =>
  match P with context C[S] =>
     let P' := context C[S'] in 
      apply semax_pre with P'; [ | ]
  end
 end.

Lemma semax_extract_PROP_True:
  forall Espec Delta (PP: Prop) P QR c Post,
        PP ->
        @semax Espec Delta (PROPx P QR) c Post -> 
       @semax Espec Delta (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply semax_pre_simple with (PROPx P QR).
unfold PROPx in *; simpl. normalize. auto.
Qed.

Lemma semax_extract_PROP:
  forall Espec Delta (PP: Prop) P QR c Post,
       (PP -> @semax Espec Delta (PROPx P QR) c Post) -> 
       @semax Espec Delta (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply semax_pre_simple with (!!PP && PROPx P QR).
unfold PROPx in *; simpl. normalize.
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

Ltac type_of_field_tac :=
 simpl; 
  repeat first [rewrite if_true by auto 
                    | rewrite if_false by (let H:=fresh in intro H; inversion H)
                    | simpl; reflexivity].


Ltac simpl_tc_expr :=
    match goal with |- context [tc_expr ?A ?B] =>
        change (tc_expr A B) with (denote_tc_assert (typecheck_expr A B));
        simpl typecheck_expr; simpl denote_tc_assert
    end.


Lemma local_lift0: forall P, local (lift0 P) = prop P.
Proof.
intros. extensionality rho. reflexivity.
Qed.
Hint Rewrite @local_lift0: norm.

Lemma move_prop_from_LOCAL:
  forall P1 P Q R, PROPx P (LOCALx (lift0 P1::Q) R) = PROPx (P1::P) (LOCALx Q R).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, local, lift0, lift1.
 simpl.
 normalize.
 apply pred_ext; normalize.
Qed.

Ltac extract_prop_from_LOCAL :=
 match goal with |- @semax _ _ (PROPx _ (LOCALx ?Q _)) _ _ =>
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
 match goal with |- @semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
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
  match goal with |- @semax _ _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
   match R with context [ (sepcon ?x  ?y) :: ?R'] =>
  let n := length_of R in let n' := length_of R' in 
         rewrite (grab_nth_SEP (n-S n')); simpl minus; unfold nth, delete_nth; 
         rewrite flatten_sepcon_in_SEP
end
end.

Lemma prop_and1 {A}{NA: NatDed A}:
  forall P Q : Prop, P -> !!(P /\ Q) = !!Q.
Proof. intros. f_equal; apply prop_ext; intuition.
Qed.
Hint Rewrite prop_and1 using solve [auto 3 with typeclass_instances] : norm.

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
* clear - H H0.
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

(*
Ltac move_prop_from_SEP :=
match goal with |- context [PROPx _ (LOCALx _ (SEPx ?R))] =>
  match R with context [(prop ?P1 && ?Rn) :: ?R'] =>
  let n := length_of R in let n' := length_of R' in 
   rewrite (extract_prop_in_SEP (n-S n')%nat P1 Rn) by reflexivity;
    simpl minus; unfold replace_nth 
 end;
 try (apply semax_extract_PROP; intro)
end.

Lemma move_prop_from_SEP':
  forall P1 R1 P Q R, 
      PROPx P (LOCALx Q (SEPx ((!!P1&&R1) :: R))) = PROPx (P1::P) (LOCALx Q (SEPx (R1::R))).
Proof.
 intros.
 extensionality rho.
 unfold PROPx, LOCALx, SEPx, local, lift0, lift1.
 simpl.
 apply pred_ext; normalize.
Qed.
*)

Lemma extract_local_in_SEP:
  forall n Q1 Rn P Q R, 
   nth n R emp = local Q1 && Rn -> 
   PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx (Q1::Q) (SEPx (replace_nth n R Rn))).
Proof.
intros.
f_equal.
extensionality rho.
apply equal_f with rho in H.
unfold PROPx,LOCALx,SEPx,local,lift1 in *.
unfold_lift; simpl in *.
revert R H; induction n; destruct R; simpl; intros;
try solve [apply pred_ext; rewrite H; normalize; repeat rewrite prop_and; normalize].
specialize (IHn _ H).
do 2 rewrite <- sepcon_andp_prop.
rewrite IHn.
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
 unfold PROPx, LOCALx, SEPx, local; unfold_lift.
 simpl.
 f_equal.
 apply pred_ext; normalize.
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

(* Hint Rewrite move_prop_from_SEP move_local_from_SEP : norm. *)

Lemma subst_make_args':
  forall id v (P: environ->mpred) fsig tl el,
  length tl = length el ->
  length (fst fsig) = length el ->
  subst id v (`P (make_args' fsig (eval_exprlist tl el))) = 
           (`P (make_args' fsig (subst id v (eval_exprlist tl el)))).
Proof.
intros. unfold_lift. extensionality rho; unfold subst.
f_equal. unfold make_args'.
revert tl el H H0; induction (fst fsig); destruct tl,el; simpl; intros; inv H; inv H0.
reflexivity.
specialize (IHl _ _ H2 H1).
unfold_lift; rewrite IHl. auto.
Qed.
Hint Rewrite subst_make_args' using (solve[reflexivity]) : subst.

Lemma subst_andp {A}{NA: NatDed A}:
  forall id v (P Q: environ-> A), subst id v (P && Q) = subst id v P && subst id v Q.
Proof.
intros.
extensionality rho; unfold subst; simpl.
auto.
Qed.

Lemma subst_prop {A}{NA: NatDed A}: forall i v P,
    subst i v (prop P) = prop P.
Proof.
intros; reflexivity.
Qed.
Hint Rewrite @subst_andp subst_prop : subst.

Lemma map_cons: forall {A B} (f: A -> B) x y,
   map f (x::y) = f x :: map f y.
Proof. reflexivity. Qed.

Hint Rewrite @map_cons : norm.
Hint Rewrite @map_cons : subst.

Lemma map_nil: forall {A B} (f: A -> B), map f nil = nil.
Proof. reflexivity. Qed.

Hint Rewrite @map_nil : norm.
Hint Rewrite @map_nil : subst.


Lemma subst_sepcon: forall i v (P Q: environ->mpred),
  subst i v (P * Q) = (subst i v P * subst i v Q).
Proof. reflexivity. Qed.
Hint Rewrite subst_sepcon : subst.

Lemma subst_PROP: forall i v P Q R,
     subst i v (PROPx P (LOCALx Q (SEPx R))) =
    PROPx P (LOCALx (map (subst i v) Q) (SEPx (map (subst i v) R))).
Proof.
intros.
unfold PROPx.
autorewrite with subst norm.
f_equal.
unfold LOCALx, local.
autorewrite with subst norm.
f_equal.
extensionality rho.
unfold lift1.
simpl.
f_equal.
induction Q; simpl; auto.
autorewrite with subst norm.
f_equal;  apply IHQ.
unfold SEPx.
induction R; auto.
autorewrite with subst norm.
f_equal; auto.
Qed.
Hint Rewrite subst_PROP : subst.

Lemma subst_stackframe_of:
  forall i v f, subst i v (stackframe_of f) = stackframe_of f.
Proof.
unfold stackframe_of; simpl; intros.
unfold subst.
extensionality rho.
induction (fn_vars f). reflexivity.
simpl map. repeat rewrite fold_right_cons.
f_equal.
apply IHl.
Qed.
Hint Rewrite subst_stackframe_of : subst.

Lemma lower_PROP_LOCAL_SEP:
  forall P Q R rho, PROPx P (LOCALx Q (SEPx R)) rho = 
     (!!fold_right and True P && (local (fold_right (`and) (`True) Q) && (fold_right sepcon emp R))) rho.
Proof. reflexivity. Qed.
Hint Rewrite lower_PROP_LOCAL_SEP : norm.

Lemma lower_TT: forall rho, @TT (environ->mpred) _ rho = @TT mpred Nveric.
Proof. reflexivity. Qed.
Hint Rewrite lower_TT : norm.

Lemma lower_FF: forall rho, @FF (environ->mpred) _ rho = @FF mpred Nveric.
Proof. reflexivity. Qed.
Hint Rewrite lower_FF : norm.

Fixpoint iota_formals (i: ident) (tl: typelist) := 
 match tl with
 | Tcons t tl' => (i,t) :: iota_formals (i+1)%positive tl'
 | Tnil => nil
 end.

Lemma semax_post_flipped' : 
   forall (R': environ->mpred) Espec (Delta: tycontext) (R P: environ->mpred) c,
       @semax Espec Delta P c (normal_ret_assert R') ->
       R' |-- R ->
       @semax Espec Delta P c (normal_ret_assert R).
 Proof. intros; eapply semax_post'; eauto. Qed.

Ltac make_sequential :=
  match goal with
  | |- @semax _ _ _ _ (normal_ret_assert _) => idtac
  | |- _ => apply sequential
  end.

Lemma remember_value:
  forall e Espec Delta P Q R c Post,
  (forall x:val, 
   @semax Espec Delta (PROPx P (LOCALx (`(eq x) e:: Q) (SEPx R))) c Post) ->
  @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
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

Lemma isptr_force_ptr'' : forall p Q,
    (isptr p -> Q) ->
    (isptr (force_ptr p) -> Q).
Proof.
intros.
apply X.
destruct p; inv H; apply I.
Qed.

Lemma isptr_offset_val'': forall i p Q,
    (isptr p -> Q) ->
    (isptr (offset_val i p) -> Q).
Proof.
intros.
apply X.
destruct p; inv H; apply I.
Qed.

Lemma ptr_eq_e': forall v1 v2 B,
   (v1=v2 -> B) ->
   (ptr_eq v1 v2 -> B).
Proof.
intuition. apply X. apply ptr_eq_e; auto.
Qed.

Lemma typed_false_of_bool':
 forall x (P: Prop), 
    ((x=false) -> P) ->
    (typed_false tint (Val.of_bool x) -> P).
Proof.
intuition.
apply H, typed_false_of_bool; auto.
Qed.

Lemma typed_true_of_bool':
 forall x (P: Prop), 
    ((x=true) -> P) ->
    (typed_true tint (Val.of_bool x) -> P).
Proof.
intuition.
apply H, typed_true_of_bool; auto.
Qed.

Ltac intro_if_new :=
 repeat match goal with
  | |- ?A -> _ => ((assert A by auto; fail 1) || fail 1) || intros _
  | |- (_ <-> _) -> _ => 
         intro
  | |- (?A /\ ?B) -> ?C => 
         apply (@and_ind A B C)
  | |- isptr (force_ptr ?P) -> ?Q =>
         apply (isptr_force_ptr'' P Q)
  | |- isptr (offset_val ?i ?P) -> ?Q =>
         apply (isptr_offset_val'' i P Q)
  | H: is_pointer_or_null ?P |- isptr ?P -> _ =>
         clear H
  | |- ?x = ?y -> _ => 
          let H := fresh in intro H;
                     first [subst x | subst y 
                             | is_var x; rewrite H 
                             | is_var y; rewrite <- H
                             | solve [discriminate H]
                             | idtac]
  | |- isptr ?x -> _ => 
          let H := fresh "P" x in intro H
  | |- is_pointer_or_null ?x => 
          let H := fresh "PN" x in intro H
  | |- typed_false _ (Val.of_bool _) -> _ =>
          simple apply typed_false_of_bool'
  | |- typed_true _ (Val.of_bool _) -> _ =>
          simple apply typed_true_of_bool'
  | |- ptr_eq _ _ -> _ =>
          apply ptr_eq_e'
  | |- _ -> _ =>
          intro
  end.

Lemma TT_sepcon_TT:   (* put this in MSL as an axiom of seplog *)
     (@TT mpred _) * TT = TT.
Proof.
Transparent Nveric.
Transparent Sveric.
Transparent mpred.
unfold Nveric, Sveric, mpred.
simpl.
apply msl.predicates_sl.TT_sepcon_TT.
Opaque Nveric.
Opaque Sveric.
Opaque mpred.
Qed.

Lemma sepcon_prop_prop:
  forall P Q,  @prop mpred _ P * !! Q = !! (P /\ Q).
Proof.
intros.
rewrite <- (andp_TT (!!P)), <- (andp_TT (!!Q)).
normalize.
rewrite TT_sepcon_TT.
normalize.
Qed.

Lemma saturate_aux20:
 forall (P Q: mpred) P' Q' ,
    P |-- !! P' ->
    Q |-- !! Q' ->
    P * Q |-- !! (P' /\ Q').
Proof.
intros.
eapply derives_trans; [apply sepcon_derives; eassumption | ].
rewrite sepcon_prop_prop.
auto.
Qed.

Lemma saturate_aux21:
  forall (P Q: mpred) S (S': Prop), 
   P |-- S -> 
   S = !!S' ->
   !! S' && P |-- Q -> P |-- Q.
Proof.
intros. subst.
eapply derives_trans; [ | eassumption].
apply andp_right; auto.
Qed.

Lemma prop_True_right {A}{NA: NatDed A}: forall P:A, P |-- !! True.
Proof. intros; apply prop_right; auto.
Qed.

Ltac already_saturated :=
(match goal with |- ?P |-- ?Q =>
    let H := fresh in 
     assert (H: P |-- Q) by auto with nocore saturate_local;
     cbv beta in H;
     match type of H with _ |-- !! ?Q' =>
     assert (Q') by (repeat simple apply conj; auto);
     fail 3
     end
end || auto with nocore saturate_local)
 || simple apply prop_True_right.   

Ltac saturate_local := 
simple eapply saturate_aux21;
 [repeat simple apply saturate_aux20;
   (* use already_saturated if want to be fancy,
         otherwise the next two lines *)
   auto with nocore saturate_local;
    simple apply prop_True_right
 | cbv beta; reflexivity
 | simple apply derives_extract_prop; intro_if_new
 ].

Lemma mapsto_local_facts:
  forall sh t v1 v2,  mapsto sh t v1 v2 |-- !! (isptr v1).
  (* could make this slightly stronger by adding the fact
     (tc_val t v2 \/ v2=Vundef)  *)
Proof.
intros; unfold mapsto.
destruct (access_mode t); try apply FF_left.
destruct (type_is_volatile t); try apply FF_left.
destruct v1; try apply FF_left.
apply prop_right; split; auto; apply I.
Qed.

Lemma mapsto__local_facts:
  forall sh t v1, mapsto_ sh t v1 |-- !! (isptr v1).
Proof.
intros; apply mapsto_local_facts.
Qed.
Hint Resolve mapsto_local_facts mapsto__local_facts : saturate_local.
(*********************************************************)

Lemma prop_right_emp {A} {NA: NatDed A}:
 forall P: Prop, P -> emp |-- !! P.
Proof. intros. normalize.
Qed.

Ltac prop_right_cautious :=
 try solve [simple apply prop_right; auto].

(**********************************************************)
(* testing
Parameter f: nat -> Prop.
Parameter g h : mpred.

Goal ( !! f 1 && ((h && !! f 2) && h ) && (!! f 3 && (g && (!!f 4 && !! f 5) && !! f 6)) |-- FF).

*)

(*****************************************************************)

Ltac subst_any :=
 repeat match goal with 
  | H: ?x = ?y |- _ => first [ subst x | subst y ]
 end.

Lemma prop_and_right {A}{NA: NatDed A}:
 forall (U: A) (X Y: Prop),
    X ->
    U |-- !! Y ->
    U |-- !! (X /\ Y).
Proof. intros. apply derives_trans with (!!Y); auto.
apply prop_derives; auto.
Qed.

Lemma assert_PROP:
 forall P1 Espec Delta P Q R c Post,
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !! P1 ->
   (P1 -> @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post) ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
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

Ltac assert_PROP A :=
 apply (assert_PROP A); [ | intro].

Lemma assert_LOCAL:
 forall Q1 Espec Delta P Q R c Post,
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local Q1 ->
   @semax Espec Delta (PROPx P (LOCALx (Q1::Q) (SEPx R))) c Post ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
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
  forall (n: nat) Espec Delta P Q R c Post,
   @semax Espec Delta (PROPx P (LOCALx (delete_nth n Q) (SEPx R))) c Post ->
   @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
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

Lemma later_left2 {T}{ND: NatDed T}{IT: Indir T}:
 forall A B C : T, A && B |-- C -> A && |> B |-- |>C.
Proof.
intros.
apply derives_trans with (|> (A && B)).
rewrite later_andp.
apply andp_derives; auto.
apply now_later.
apply later_derives; assumption.
Qed.

Lemma subst_ewand: forall i v (P Q: environ->mpred),
  subst i v (ewand P Q) = ewand (subst i v P) (subst i v Q).
Proof. reflexivity. Qed.
Hint Rewrite subst_ewand : subst.

