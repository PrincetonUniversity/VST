Require Import floyd.proofauto.

Import ListNotations.
Local Open Scope logic.
Require Import sha.spec_sha.
Require Import sha.HMAC_functional_prog.

Lemma In_Nlist {A:Type}: forall (n:A) l x, In x (Nlist n l) -> x=n.
Proof. intros n l.
  induction l; simpl; intros. contradiction.
  destruct H; eauto.
Qed.
Lemma zeropad_isbyteZ: forall l, Forall isbyteZ l -> Forall isbyteZ (HMAC_FUN.zeroPad l).
Proof. unfold isbyteZ, HMAC_FUN.zeroPad; intros.
  rewrite Forall_forall in *. intros.
  apply in_app_or in H0.
  destruct H0. apply (H _ H0).
  apply In_Nlist in H0. subst; omega.
Qed.
Lemma mapnth': forall {A B : Type} (f : A -> B) (l : list A) (d : A) (n : nat) fd,
      fd = f d -> nth n (map f l) fd = f (nth n l d).
Proof. intros; subst. apply map_nth. Qed.
Lemma map_unsigned_Brepr_isbyte: forall l, Forall isbyteZ l ->
      map Byte.unsigned (map Byte.repr l) = l.
Proof. intros. induction l; simpl in *. trivial.
   rewrite IHl. rewrite Byte.unsigned_repr. trivial. 
   rewrite Forall_forall in H. 
   assert (In a (a::l)). left. trivial. 
   specialize (H _ H0); clear H0.
      unfold isbyteZ in H. unfold Byte.max_unsigned, Byte.modulus. simpl. omega.
   rewrite Forall_forall in *. intros. apply H. right; trivial.
Qed.
Lemma Ztest_Bytetest:
 forall a, Z.testbit (Byte.unsigned a) = Byte.testbit a.
Proof. reflexivity. Qed.
Hint Rewrite Ztest_Bytetest : testbit.

Lemma nthD_1 {A B}: forall (f: A ->B) n l d fx dd, (n < length l)%nat ->
      nth n (map f l) d = fx -> 
      exists x, In x l /\ nth n l dd = x /\ f x = fx.
Proof. intros f n.
  induction n; simpl; intros.
    destruct l; simpl in *. omega.
      exists a; split. left; trivial. split; trivial.
    destruct l; simpl in *. omega. 
    destruct (IHn l d fx dd) as [? [? [? ?]]]. omega. trivial.
    exists x; eauto.
Qed.

(*Same proof as semax_loadstore_array*)
Lemma NEWsemax_loadstore_array:
  forall {Espec: OracleKind},
 forall n k vi lo hi t1 (contents: Z -> reptype t1) v1 v2 (Delta: tycontext) e1 ei e2 sh P Q R, 
  (*H0*) reptype t1 = val -> 
  (*H1*) type_is_by_value t1 ->
  (*H2*) legal_alignas_type t1 = true ->
  (*H3*) typeof e1 = tarray t1 k->
  (*H4*) typeof ei = tint ->
  (*H8*) PROPx P (LOCALx Q (SEPx R)) |--  rel_expr e1 v1 && rel_expr ei (Vint (Int.repr vi))
           && rel_expr (Ecast e2 t1) v2 ->
  (*H7*) nth_error R n = Some (`(array_at t1 sh contents lo hi v1)) ->
  (*H *) writable_share sh ->
  (*H5*) tc_val t1 v2 ->
  (*H6*) in_range lo hi vi ->
   @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R))) (Sassign (Ederef (Ebinop Oadd e1 ei (tptr t1)) t1) e2) 
          (normal_ret_assert 
           (PROPx P (LOCALx Q (SEPx 
            (replace_nth n R `(array_at t1 sh (upd contents vi (valinject _ v2)) lo hi v1)))))).
Proof. 
intros until R.
intros H0 H1 H2 H3 H4 H8 H7 H H5 H6.
eapply semax_post_flipped'.
apply semax_loadstore_array'; eauto.
apply derives_trans with (!! isptr v1 && PROPx P (LOCALx Q (SEPx R))).
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
rewrite array_at_isptr. normalize.
normalize.
destruct v1; try contradiction.
instantiate (2:=v1).
simpl eval_binop. rewrite mul_repr.
apply andp_right; auto.
eapply derives_trans; [ apply H8 |].
intro rho. simpl.
repeat apply andp_right.
apply rel_lvalue_deref.
eapply rel_expr_binop.
repeat apply andp_left1. apply derives_refl.
apply andp_left1. apply andp_left2. apply derives_refl.
intro; rewrite H4; simpl. rewrite H3; simpl. 
  unfold Cop.sem_add; simpl. rewrite mul_repr. auto.
 apply andp_left2. auto.
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
apply derives_refl.
rewrite (SEP_replace_nth_isolate _ _ _ `(array_at t1 sh (upd contents vi (valinject t1 v2)) lo hi v1) H7).
rewrite insert_SEP.
auto.
Qed.

Lemma array_at_local_facts':
  forall (t : type) (sh : Share.t) (f : Z -> reptype t) (lo hi : Z) (v : val),
  array_at t sh f lo hi v |-- array_at t sh f lo hi v && !!isptr v && !!offset_in_range (sizeof t * lo) v &&
!!offset_in_range (sizeof t * hi) v && !!align_compatible t v.
Proof. intros. unfold array_at. entailer. Qed.


Lemma split_offset_array_at_: forall (ty : type) (sh : Share.t) 
         (z lo hi : Z) (v : val),
       z <= lo <= hi ->
       sizeof ty > 0 ->
       legal_alignas_type ty = true ->
       array_at_ ty sh z hi v =
       !! offset_in_range (sizeof ty * z) v &&
       !! offset_in_range (sizeof ty * hi) v &&
       array_at_ ty sh z lo v * 
       array_at_ ty sh 0 (hi - lo) 
       (offset_val (Int.repr (sizeof ty * lo)) v).
Proof.
  intros. unfold array_at_.
  rewrite <- split_offset_array_at; trivial.
Qed.
Lemma offset_val_array_at0:
 forall t sh f lo hi v,
  sizeof t > 0 -> hi >= 0 ->
  legal_alignas_type t = true ->
  array_at t sh (fun i => f (i-lo)%Z) lo (lo + hi) v 
  |--
  array_at t sh f 0 hi (offset_val (Int.repr (sizeof t * lo)) v).
Proof.
  intros.
  rewrite (split_offset_array_at t _ _ lo lo); trivial.
  rewrite array_at_emp.
  entailer. rewrite Zplus_comm. rewrite Z.add_simpl_r.
  apply array_at_ext'. intros. rewrite Z.add_simpl_r. trivial.
  omega.
Qed.

Lemma offset_val_array_at1:
 forall t sh f g k lo hi ofs v,
    sizeof t > 0 -> hi >= 0 ->
    legal_alignas_type t = true ->
    k = lo + hi ->
    g = (fun i => f (i-lo)%Z) ->
    ofs = Int.repr (sizeof t * lo) ->
  array_at t sh g lo k v |--
  array_at t sh f 0 hi ((offset_val ofs) v).
Proof.
  intros. subst. apply offset_val_array_at0; trivial.
Qed.
