Require Import msl.msl_standard.
Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Import veric.expr.

Definition mkEnviron' (ge: Clight.genv) (ve: Clight.env) (te: Clight.temp_env) :=
  mkEnviron (filter_genv ge) ve te.

Definition Delta1 : tycontext := (PTree.set 1%positive (type_int32s, false) (PTree.empty (type * bool)),
                                 PTree.empty type, Tvoid).


Lemma tc_assert_simpl_sound : forall asn rho, 
denote_tc_assert asn rho -> denote_tc_assert (tc_assert_simpl asn) rho.
Proof.
intros. induction asn; simpl; auto.

simpl in *. intuition. remember (tc_assert_simpl asn1).
remember (tc_assert_simpl asn2). destruct t; destruct t0; simpl in *; auto.

destruct e; auto. simpl in *. unfold denote_tc_nonzero in *. simpl in *.
destruct (Int.eq i Int.zero); intuition.

destruct e; auto. simpl in *. unfold denote_tc_ilt in *.
simpl in *. destruct (Int.ltu i0 i); simpl; intuition.

destruct e; auto. simpl in *. unfold denote_tc_Zle in *.
simpl in *. destruct (Float.Zoffloat f); intuition. rewrite H. simpl. auto.

destruct e; auto. simpl in *. unfold denote_tc_Zge in *.
simpl in *. destruct (Float.Zoffloat f); intuition. rewrite H. simpl. auto.
Qed.

Definition temp_element_correct (te : temp_env) :=
(fun (tyconEl : (PTree.elt * (type * bool))) => 
  match tyconEl with
  | (id, (elt, asn)) =>
    (*if asn then*)
    match te ! id with
    | Some v => typecheck_val v elt = true
    | _ => False
    end
    (*else True*)
end). 

Definition te_correct (te : temp_env) (Delta: tycontext) := Forall
  (temp_element_correct te)
  ((PTree.elements (temp_types Delta))).

Definition var_element_correct (ve: env) (ge:genviron) : 
(PTree.elt * type) -> Prop :=
(fun (varel : (PTree.elt * type)) => let (id,ty) := varel in
  match ve ! id with
  | Some (_,ty') => if type_eq ty ty' then True else False
  | None => match (ge id) with
        | Some (Vptr b i,ty2') => if type_eq ty ty2' && 
                              typecheck_val (Vptr b i) ty2' &&
                              is_pointer_type ty2'
        then True else False 
        | None => False
        | _ => False
        end
  end).

Definition ve_correct (ve:env) (ge:genviron) (Delta: tycontext) :=
Forall (var_element_correct ve ge) (PTree.elements (var_types Delta)).

Lemma typecheck_environ_sound : forall ge te ve Delta,
typecheck_environ (mkEnviron ge ve te) Delta = true ->
te_correct te Delta /\ ve_correct ve ge Delta.
Proof.
intros.
unfold typecheck_environ in *. destruct Delta. destruct p.
unfold te_correct. unfold ve_correct.
unfold temp_types in *. simpl in *. rewrite andb_true_iff in *. intuition. 

induction (PTree.elements t0).
constructor. 
unfold temp_element_correct.
simpl in *. destruct a. destruct p0. rewrite Forall_forall; intros. 
destruct x. destruct p0. simpl in *. intuition. inv H2. destruct (te!e).
if_tac in H0; congruence. congruence.

remember (te!p). destruct o; try congruence. remember (typecheck_val v t2).
destruct b1; try congruence. intuition. rewrite Forall_forall in *.
specialize (H (e, (t3, b0))). intuition.

unfold var_types in *; simpl in *. 
clear H0. rewrite Forall_forall. intros.  
destruct x. induction (PTree.elements t1). inv H.
simpl in *. destruct a. destruct H. inv H. destruct (ve !e). destruct p.
destruct (type_eq t2 t3); auto. congruence. destruct (ge e). destruct p. 
destruct v; intuition.
destruct (type_eq t2 t3). simpl in *. remember (is_pointer_type t3).
destruct t3; destruct b0; simpl in *; intuition. simpl in *. intuition.
intuition. 

apply IHl.
clear IHl.  destruct (ve ! p). destruct p0. 
destruct (type_eq t3 t4). subst.
auto. congruence. destruct (ge p). destruct p0.
destruct v; intuition. remember (is_pointer_type t4).
destruct (type_eq t3 t4); simpl in *; intuition. subst t3.
destruct t4; intuition; destruct b0; simpl in *; intuition.
congruence. auto.
Qed.

Lemma typecheck_te_sound : forall dv te,
typecheck_temp_environ dv te = true ->
Forall (temp_element_correct te) dv.
Proof.
intros. induction dv. auto.
simpl in *. destruct a. destruct p0. remember (te! p). destruct o; auto.
remember (typecheck_val v t) as b0. remember b. 
destruct b0; destruct b1; intuition. 
rewrite Forall_forall in *. intros. simpl in *. intuition.
unfold temp_element_correct. destruct x; destruct p0.
inv H2. 
rewrite <- Heqo. auto. 
rewrite Forall_forall in *. intuition.
simpl in *. intuition. inv H2. simpl. rewrite <- Heqo.
auto.
rewrite Forall_forall in *. intuition.
Qed.


Lemma in_fst_in : forall A B (L : list (A*B)) (a:A) (b:B), In (a, b) L  -> In a (map (@fst A B) L) .
Proof.
intros A B L. induction L; intros. auto. simpl in *. inv H. auto. right. eapply IHL. apply H0.
Qed.

Lemma in_rem_in : forall A B C (L : list (A*(B*C))) a b c,
In (a, (b, c)) L -> In (a,b) (map remove_assignedness (L)).
intros A B C L. induction L; intros. inv H. simpl in *.
inv H. left. auto. right. eapply  IHL. eauto.
Qed.


Lemma set_elements_PTree : forall A i (v:A) t, In (i,v) (PTree.elements (PTree.set i v t)).
Proof.
intros. apply PTree.elements_correct. apply PTree.gss.
Qed.

Lemma set_element_PTree2 : forall A i (v:A) t, 
       Forall2
      (fun i_x i_y => (fst i_x) <> i -> fst i_x = fst i_y /\  (snd i_x) = (snd i_y))
      (PTree.elements t) (PTree.elements (PTree.set i v t)).
Proof.
intros.
induction t. unfold PTree.elements. simpl. unfold PTree.set.
Admitted. (*not even sure this will help*)

Lemma typecheck_environ_put_te : forall ge te ve Delta id v ,
typecheck_environ (mkEnviron ge ve te) Delta = true ->
(*((temp_types Delta) ! id = Some t ->
  (typecheck_val v (fst t)) = true) ->*)
(*typecheck_expr Delta (Etempvar id (typeof e)) = true ->
typecheck_expr Delta e = true ->*) 
typecheck_environ (mkEnviron ge ve (PTree.set id v te)) Delta = true.
Proof.
intros. unfold typecheck_environ in *. simpl in *. repeat rewrite andb_true_iff in *.
intuition. clear H1. destruct Delta. destruct p. unfold temp_types in *; simpl in *.

remember (PTree.elements t0).
generalize dependent t0. 
induction l; intros; auto.

simpl in *. destruct  a. destruct p0.  
remember (te ! p). destruct o; intuition.
remember (typecheck_val v0 t2). destruct b; intuition.
remember ((PTree.set id v te) ! p).
destruct o. remember (typecheck_val v1 t2). destruct b; intuition.
simpl in *.

admit. (* need proof that a smaller tree exists if there is at least one element*)

assert (typecheck_val v1 t2 = true). 
destruct b0; intuition. simpl in *.
apply typecheck_te_sound in H0. rewrite Forall_forall in *.
unfold temp_element_correct in H0. 

admit. (* proof that we can look up p2 in t0 *)
rewrite H in Heqb. inv Heqb.
 

rewrite PTree.gsspec in Heqo0. 
assert (x:=eq_dec p id). destruct x. subst.
rewrite peq_true in Heqo0. inv Heqo0. rewrite peq_false in Heqo0; auto.
rewrite <- Heqo in Heqo0. inv Heqo0. destruct b0; intuition.
admit.
Qed. (* ===================================================================two admits, comments above*)


Lemma no_rep_in_pair : forall A B L a b b2, list_norepet (map (@fst A B) (L)) ->
  In (a, b) L -> In (a,b2) L -> b = b2.
Proof.
intros A B L. induction L; intros. inv H0. simpl in *.
inv H. intuition.
  destruct a. inv H0. inv H. auto.
 
  destruct H4. destruct a; simpl. inv H. eapply in_fst_in. eauto. 
  
  destruct H4. destruct a; simpl. inv H0. eapply in_fst_in. eauto.

  eapply IHL; eauto.
Qed. 


Lemma type_eq_true : forall a b, proj_sumbool  (type_eq a b) =true  -> a = b.
Proof. intros. destruct (type_eq a b). auto. simpl in H. inv H.
Qed.

Ltac of_bool_destruct :=
match goal with
  | [ |- context[Val.of_bool ?X] ] => destruct X
end.


Lemma classify_add_int_cases_both : forall i1 s1 a1 i2 s2 a2,
exists s3,
classify_add (Tint i1 s1 a1) (Tint i2 s2 a2) 
= add_case_ii s3.
Proof.
intros; destruct i1; destruct s1; destruct i2; destruct s2; eexists;  
unfold classify_add; simpl; eauto.
Qed.

Lemma undef_not_typecheck : forall t, typecheck_val Vundef t = false.
intros.
destruct t; auto.
Qed.

Ltac st:= simpl in *.

Lemma is_true_true : forall b, is_true b -> b = true.
Proof.
auto.
Qed.

Ltac tc_assert_ext := 
repeat match goal with
| [H : _ /\ _ |- _] => destruct H
end.

Ltac revert_all := repeat match goal with
| [H: _ |- _] => revert H
end.

Lemma orb_if : forall {D} b c (d:D) (e:D), (if (b || c) then d else e) = if b then d else if c then d else e.
intros.
remember (b || c). destruct b0; auto. symmetry in Heqb0. rewrite orb_true_iff in Heqb0.
intuition; subst; auto. destruct b; auto. symmetry in Heqb0; rewrite orb_false_iff in Heqb0.
intuition; subst; auto.
Qed.

Lemma andb_if : forall {D} b c (d:D) (e:D), (if (b && c) then d else e) = if b then (if c then d else e) else e.
Proof.
intros.
remember (b&&c). destruct b0; symmetry in Heqb0; try rewrite andb_true_iff in *; try rewrite andb_false_iff in *; if_tac; auto; intuition;
destruct c; auto; intuition.
Qed.

Lemma typecheck_binop_sound:
forall (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type),
denote_tc_assert (typecheck_expr Delta (Ebinop b e1 e2 t)) rho ->
(denote_tc_assert (typecheck_expr Delta e1) rho ->
 typecheck_val (eval_expr rho e1) (typeof e1) = true) ->
(denote_tc_assert (typecheck_expr Delta e2) rho ->
 typecheck_val (eval_expr rho e2) (typeof e2) = true) ->
typecheck_val (eval_expr rho (Ebinop b e1 e2 t)) (typeof (Ebinop b e1 e2 t)) =
true.
Proof.
Admitted.
(*intros. st. intuition.
destruct b; st;
match goal with 
| [ |- typecheck_val ( force_val (?X _ _ _ _)) _ = true ] => unfold X in *
| [ |- typecheck_val ( force_val (?X _ _ _ _ _)) _ = true ] => unfold X in *
| [ |- typecheck_val ( force_val (?X _ _ _ _ _ _)) _ = true ] => unfold X in *
end;

destruct (typeof e1); destruct (typeof e2); st; auto;

try solve [try destruct i; try destruct s; try destruct i0; try destruct s0; 
st;  
destruct (eval_expr rho e1); destruct (eval_expr rho e2); auto; destruct t;
tc_assert_ext; st; auto; repeat (try rewrite orb_if; rewrite andb_if); try repeat if_tac; st; 
try of_bool_destruct; auto].
Qed.*)

Transparent Float.intoffloat.
Transparent Float.intuoffloat.

Ltac unfold_tc_denote :=
unfold denote_tc_nonzero in *;
unfold denote_tc_isptr in *;
unfold denote_tc_ilt in *;
unfold denote_tc_Zle in *;
unfold denote_tc_Zge in *;
unfold denote_tc_samebase in *;
unfold denote_tc_nodivover in *;
unfold denote_tc_initialized in *.

Lemma eval_lvalue_ptr : forall rho e Delta te ve ge,
mkEnviron ge ve te = rho -> 
ve_correct ve ge Delta -> 
denote_tc_assert (typecheck_lvalue Delta e) rho ->
eval_lvalue rho e = Vundef \/ exists base, exists ofs, eval_lvalue rho e = Vptr base ofs.
Proof.
intros.
induction e; eauto.
simpl. 
remember ((ve_of rho) ! i). destruct o; intuition;
try destruct p; try remember (type_eq t t0); try destruct s;
try remember (negb (type_is_volatile t0));try destruct b0; auto;
try solve[right; eauto].
remember (ge_of rho i). destruct o; eauto. destruct p. if_tac; eauto.
unfold ve_correct in *. rewrite Forall_forall in *.
unfold var_element_correct in *. remember ((var_types Delta) ! i).
destruct o. subst. simpl in H1. remember (var_types Delta) ! i.
destruct o; intuition. symmetry in Heqo2. apply PTree.elements_correct in Heqo2.
specialize (H0 (i,t)); intuition. simpl in Heqo. rewrite <- Heqo in H.
simpl in Heqo0. rewrite <- Heqo0 in H. destruct v; eauto; intuition.
simpl in H1. rewrite <- Heqo1 in H1. intuition.

st. intuition. destruct (eval_expr rho e); eauto.

st. intuition. destruct (eval_lvalue rho e); eauto; intuition.
destruct (typeof e); try congruence. 
destruct (eval_lvalue rho e); intuition. destruct (typeof e); intuition.
destruct (field_offset i f); eauto.
Qed.

Lemma typecheck_both_sound: 
  forall Delta rho e , 
             typecheck_environ rho Delta = true ->
             (denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr rho e) (typeof e) = true) /\
             (forall pt, 
             denote_tc_assert (typecheck_lvalue Delta e) rho ->
             is_pointer_type pt = true -> 
             typecheck_val (eval_lvalue rho e) pt=true).
Proof.
intros. induction e; split; intros; try solve[subst; auto].

(*Const int*)
simpl. subst; destruct t; auto; simpl in H0; inv H0; intuition.

(*Const float*)
simpl in *. subst; destruct t; intuition. 

(*Var*)
st.  

apply typecheck_environ_sound in H. destruct H.
clear H. unfold ve_correct in *. rewrite Forall_forall in *.
unfold var_element_correct in *.

remember ((var_types Delta) ! i). destruct o; intuition. (*if it isn't in delta, it won't typecheck*)
simpl in *. intuition. remember (type_eq t t0). destruct s; intuition. (*pt is type that the var lookup checks as*)
subst. remember (negb(type_is_volatile t0)). destruct b; intuition.
clear H3. clear H.  
symmetry in Heqo.
apply PTree.elements_correct in Heqo. (*if we found something by lookup, it is in the elements*)
specialize (H2 (i,t0)). intuition.
remember ((ve_of rho) ! i). destruct o; intuition. (*one case we find it in ve, the other we don't*)
destruct p. remember (type_eq t0 t). destruct s; intuition.
subst. rewrite <- Heqb. destruct pt; auto. (*we get out of this one because we know we are getting a non-int pointer*)
destruct (ge_of rho i); auto. destruct p.
destruct v; auto.
remember (@proj_sumbool (t0 = t) (t0 = t -> False) (type_eq t0 t)).
destruct b0; auto. destruct (type_eq t0 t); auto. subst.
destruct t; auto. remember (is_pointer_type (Tpointer t a)). destruct b0; auto.
clear H. destruct pt; auto. destruct pt; auto. destruct pt; auto.
destruct pt; auto. destruct pt; auto.

(*Temp*)
Focus 1.
simpl in *. destruct rho. apply typecheck_environ_sound in H. intuition. 
unfold te_correct in *. unfold temp_element_correct in *.
rewrite Forall_forall in *. clear H2.
unfold eval_id. 

simpl. unfold force_val.
destruct Delta. destruct p. 
unfold temp_types in *. simpl in *.
remember (t1 ! i). destruct o.
  symmetry in Heqo. apply PTree.elements_correct in Heqo. 
  destruct p. specialize (H1 (i,(t3,b))). simpl in *. intuition.
  if_tac in H0; auto.
remember (type_eq t t3). destruct s; auto. subst. 
destruct (te ! i); intuition. if_tac in H0; intuition. 

(*deref*)  
simpl in *. intuition. specialize (H3 pt).
unfold_tc_denote.
remember (eval_expr rho e); destruct v;
simpl in *;
remember (typeof e); destruct t0; intuition; destruct pt; auto.

(*addrof*)
st. intuition. 
destruct t; auto.


(*Unop*)
intuition; simpl in *. intuition. 
destruct u; simpl in *. 

unfold sem_notbool in *.
remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; st; destruct (eval_expr rho e); intuition;
try of_bool_destruct; try destruct t; intuition.

unfold sem_notint.

remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; st; destruct (eval_expr rho e); intuition;
try of_bool_destruct; try destruct t; intuition.


unfold sem_neg.

remember (typeof e). destruct t0; simpl in *; intuition;
try destruct i; try destruct s; st; destruct (eval_expr rho e); intuition;
try of_bool_destruct; try destruct t; intuition.

(*binop*)
repeat rewrite andb_true_iff in *; intuition.
clear H4. clear H2. clear H. 
eapply typecheck_binop_sound; eauto.

(* cast *)
st. intuition.
remember (eval_expr rho e). 
destruct v; intuition; remember (typeof e); destruct t0; intuition; destruct t; intuition;
try destruct i; try destruct i0; try destruct i1; intuition;
unfold sem_cast; unfold classify_cast; unfold cast_float_int;
destruct s; auto; unfold_tc_denote; try unfold Float.intoffloat; try unfold Float.intuoffloat;
st; intuition; unfold_tc_denote; rewrite <- Heqv in *; destruct f; auto;
st; destruct e0; rewrite H1; rewrite H5; auto.

(*condition*)
admit. (*condition might go away*)
(*st. repeat rewrite andb_true_iff in *; intuition.
remember (eval_expr rho e2).
remember (eval_expr rho e3).

destruct (eval_expr rho e1); intuition.
remember (typeof e1); destruct t0; intuition. simpl.
destruct (negb (Int.eq i Int.zero)). destruct v; intuition; remember (typeof e2);
destruct t0; intuition; destruct t; intuition; try destruct i2; try destruct s0; intuition;
try destruct i3; try destruct s0; try destruct s1; try destruct i1; intuition.
destruct v0; intuition; remember (typeof e3); destruct t0; intuition; destruct t; intuition; 
try destruct i2; try destruct s0; intuition;
try destruct i3; try destruct s0; try destruct s1; try destruct i1; intuition.
remember (typeof e1); destruct t0; intuition. simpl.
destruct (negb (Float.cmp Ceq f Float.zero)).
remember (typeof e2). destruct v; destruct t0; destruct t; intuition;
try destruct i0; try destruct s; intuition; try destruct i1; try destruct s0; try destruct i; intuition.
remember (typeof e3). destruct v0; destruct t0; destruct t; intuition; 
try destruct i0; try destruct s; intuition; try destruct i1; try destruct s0; try destruct i; intuition.
remember (typeof e1). unfold bool_val. destruct t0; intuition.*)

(*EField*)
st. intuition. specialize  (H3 pt). intuition. remember rho.
destruct e0.
rewrite Heqe0 in H4.
apply typecheck_environ_sound in H. intuition. clear H0.
assert (PTR := eval_lvalue_ptr _ _ _ _ _ _ Heqe0 H6 H4).
rewrite Heqe0 in *. clear Heqe0.
intuition. 
remember (eval_lvalue rho e). unfold denote_tc_isptr in *.
destruct v; intuition; try congruence.
remember (eval_lvalue rho e). destruct H. destruct H.
destruct v; intuition; try congruence.
inv H.
destruct (typeof e); intuition. 
destruct (field_offset i f); intuition.

Qed.

Definition defined_val v :=
match v with
Vundef => False
| _ => True
end.

Lemma typecheck_both_bool_sound : forall Delta rho e,
 typecheck_environ rho Delta = true ->
 (typecheck_b Delta e= true ->
  defined_val (eval_expr rho e) ->
  typecheck_val (eval_expr rho e) (typeof e)=true)
 /\
 (forall pt, tc_might_be_true (typecheck_lvalue Delta e) =true ->
  defined_val (eval_lvalue rho e) ->
  is_pointer_type pt =true ->
  typecheck_val (eval_lvalue rho e) pt=true).
Proof.
intros. unfold typecheck_b. induction e; intuition.

(*int*)
destruct t; auto; st; try congruence.  

(*float*)
destruct t; auto; st; try congruence.

(*var*)
st. remember ((ve_of rho) ! i). destruct o.
  destruct p; repeat if_tac; destruct pt; auto.

  remember (ge_of rho i). destruct o.
    destruct p. if_tac. remember ((var_types Delta) ! i).
    destruct o. subst. destruct (type_eq t0 t1); st; try congruence.
    subst. apply typecheck_environ_sound in H. 
    intuition. clear H3. unfold ve_correct in *.
    rewrite Forall_forall in *. symmetry in Heqo1. 
    apply PTree.elements_correct in Heqo1.
    specialize (H4 (i,t1)). intuition. simpl in H; rewrite <- Heqo in H;
    rewrite <- Heqo0 in H. destruct v; try congruence; auto.
    destruct (type_eq t1 t1); auto; st; destruct t1; auto;
    destruct pt; auto. st; congruence. st; auto. auto.

(*temp*)
simpl in *. unfold defined_val in *.
unfold eval_id in *. unfold force_val.
 remember ((temp_types Delta) ! i).
destruct o.
  apply typecheck_environ_sound in H. intuition. 
  remember ((te_of rho) ! i); destruct o; auto. clear H3. symmetry in Heqo.
  apply PTree.elements_correct in Heqo. unfold te_correct in *.
  rewrite Forall_forall in *. specialize (H2 (i,p)). if_tac in H0; intuition.
  intuition. st. destruct p. st. repeat if_tac in H0; intuition.
  subst. remember ((te_of rho) ! i). destruct o; intuition. inv Heqo0.
  auto. subst. destruct ((te_of rho) ! i). inv Heqo0. auto.
  intuition. st. if_tac in H0; intuition. 
 
(*deref*)
st. remember (eval_expr rho e). destruct v; auto. destruct pt; auto.

(*addrof*)
st. rewrite andb_true_iff in *. intuition. specialize (H1 t).
intuition. apply H1. destruct t; auto.

(*unop*)
st. rewrite andb_true_iff in *. intuition. clear H1.
destruct u; st;
match goal with [ |- context[force_val (?H _ _)]] => unfold H in * end;
  remember (typeof e); destruct t0; st; try congruence; 
  try destruct i; try destruct s; st; try congruence; auto;
  destruct (eval_expr rho e); auto; st; try (of_bool_destruct); destruct t; auto;
  st; try congruence.

(*binop*)
admit.

(*cast*)
admit.

(*condition*)
admit.

(*field*)
st. remember (eval_lvalue rho e). destruct v; auto.
remember (typeof e). destruct t0; auto. remember (field_offset i f).
destruct r; auto. st. destruct pt; auto.
destruct pt; auto.

Qed. (*admits, not done, should work ==================================================================*)
    
Lemma typecheck_expr_sound : forall Delta rho e,
 typecheck_environ rho Delta = true -> 
              denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr rho e) (typeof e) = true.
Proof. intros. 
assert (TC := typecheck_both_sound Delta rho e). intuition. Qed.


Lemma typecheck_lvalue_sound : forall Delta rho e,
  typecheck_environ rho Delta = true ->
  denote_tc_assert (typecheck_lvalue Delta e) rho ->
  (forall pt, 
    is_pointer_type pt = true -> 
    typecheck_val (eval_lvalue rho e) pt=true).
intros. edestruct (typecheck_both_sound _ _ e H).
apply H3; eauto.
Qed.

Lemma get_typed_int:
    forall v att, typecheck_val v (Tint I32 Signed att) = true -> 
                      exists i:int, v = Vint i.
intros; destruct v; inv H; eauto.
Qed.

Definition is_ptr_type (ty: type) : bool :=
  match ty with
  | Tpointer _ _ => true
  | Tarray _ _ _ => true
  | Tfunction _ _ => true
  | Tstruct _ _ _ => true
  | Tunion _ _ _ => true
  | _ => false
end.

(*Not going to work because of null pointer
Lemma get_typed_ptr:
   forall v ty, 
                   typecheck_val v ty = true -> 
                   is_ptr_type ty = true ->
                      exists b, exists ofs, v = Vptr b ofs.
Proof.
intros; destruct v; destruct ty; inv H; eauto; inv H0.
Qed.*)




Lemma tc_binaryop_nomem : forall b e1 e2 m1 m2 t rho,
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
sem_binary_operation b (eval_expr rho e1) (typeof e1) (eval_expr rho e2)
  (typeof e2) (m1) =
sem_binary_operation b (eval_expr rho e1) (typeof e1) (eval_expr rho e2)
  (typeof e2) (m2).
Proof.
intros.
destruct b; st; auto;
 unfold sem_cmp; destruct (classify_cmp (typeof e1) (typeof e2));
   try destruct i; try destruct s; auto; contradiction.
Qed. 

Definition some_pt_type := Tpointer Tvoid noattr.

Lemma filter_genv_zero_ofs : forall ge ge2 b i t,
  filter_genv ge = ge2 ->
    (forall id, ge2 id = Some (Vptr b i, t) ->
      i = Int.zero).
Proof.
intros. unfold filter_genv in *. rewrite <- H in H0.
remember (Genv.find_symbol ge id). destruct o. 
destruct (type_of_global ge b0); inv H0; auto.
inv H0.
Qed.

Ltac ftn := try solve [st; try congruence; try contradiction]. 


Lemma eval_binop_relate_fail :
forall (Delta : tycontext) (rho : environ) (b : binary_operation)
  (e1 e2 : expr) (t : type) (m : mem),
typecheck_environ rho Delta = true ->
forall ge : genv,
filter_genv ge = ge_of rho ->
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isBinOpResultType b e1 e2 t) rho ->
denote_tc_assert (typecheck_expr Delta e1) rho ->
None =
sem_binary_operation b (eval_expr rho e1) (typeof e1) (eval_expr rho e2)
  (typeof e2) (fun (_ : block) (_ : Z) => false) ->
Clight_sem.eval_expr ge (ve_of rho) (te_of rho) m e2 (eval_expr rho e2) ->
Clight_sem.eval_expr ge (ve_of rho) (te_of rho) m e1 (eval_expr rho e1) ->
Clight_sem.eval_expr ge (ve_of rho) (te_of rho) m (Ebinop b e1 e2 t) Vundef.
Proof.
Admitted. (*Memory
intros. assert (TC1 := typecheck_expr_sound _ _ _ H H1).
assert (TC2 := typecheck_expr_sound _ _ _ H H3).
st. 
unfold sem_binary_operation in *. destruct b; 
st; 
remember (typeof e1); remember (typeof e2);
remember (eval_expr rho e1); remember (eval_expr rho e2);

(try match goal with
| [H : None = ?X _ _ _ _ |- _] => unfold X in *
| [H : None = ?X _ _ _ _ _ _ |- _ ] => unfold X in *
end; 

destruct v0; destruct t1; ftn; destruct v; destruct t0; ftn;
try destruct i1; try destruct s; ftn; try destruct i2; try destruct s0; ftn;
try destruct i0; ftn; st; try (rewrite <- Heqv in *; intuition);
try rewrite <- Heqv0 in *; intuition; 
try (repeat rewrite andb_if in H4); try (repeat rewrite orb_if in H4); repeat if_tac in H4; ftn).
*)



Lemma eval_both_relate:
  forall Delta ge rho e m,
           filter_genv ge = ge_of rho ->
           typecheck_environ rho Delta = true ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight_sem.eval_expr ge (ve_of rho) (te_of rho) m e  (eval_expr rho e))
           /\
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight_sem.eval_lvalue ge (ve_of rho) (te_of rho) m e b ofs /\
              eval_lvalue rho e = Vptr b ofs).
Proof.
intros. generalize dependent ge. induction e; intros;
try solve[intuition; constructor; auto | subst; inv H1]; intuition.

(* var*)
assert (TC_Sound:= typecheck_lvalue_sound).
specialize (TC_Sound Delta rho (Evar i t) H0 H1).
specialize (TC_Sound some_pt_type).
 
st. remember ((ve_of rho) ! i); destruct o; try destruct p.
if_tac. if_tac; intuition.
exists b. exists Int.zero. intuition. constructor.
subst; auto. remember (ge_of rho i). destruct o; auto;
try destruct p; intuition.

remember ((ge_of rho) i). destruct o; intuition. destruct p.
if_tac. subst. remember ((var_types Delta) ! i). destruct o; intuition.
symmetry in Heqo1. apply PTree.elements_correct in Heqo1.
apply typecheck_environ_sound in H0.
intuition. unfold ve_correct in *. rewrite Forall_forall in *.
specialize (H4 (i,t)). intuition. unfold var_element_correct in *.
rewrite <- Heqo in H0. rewrite <- Heqo0 in H0. destruct v; intuition.
repeat rewrite andb_if in H0. exists b; exists i0. intuition.
symmetry in Heqo0.
assert (Eq := filter_genv_zero_ofs _ _ b i0 t0 H _ Heqo0). subst.
apply Clight_sem.eval_Evar_global. auto. 
rewrite <- H in Heqo0. unfold filter_genv in Heqo0. 
destruct (Genv.find_symbol ge i); intuition;  
try destruct (type_of_global ge b0); intuition;
inv Heqo0; auto. rewrite <- H in Heqo0.
unfold filter_genv in *. destruct (Genv.find_symbol ge i).
remember (type_of_global ge b0); destruct o. inv Heqo0. rewrite Heqo2; auto.
inv Heqo0. 
if_tac in H0; try contradiction.
inv Heqo0. inv H2.

(*temp*)
assert (TC:= typecheck_expr_sound).
specialize (TC Delta rho (Etempvar i t)). st. 
intuition.
constructor. unfold eval_id in *. destruct ((te_of rho) ! i); auto. inv H3.

(*deref*)
assert (TC:= typecheck_lvalue_sound _ _ _ H0 H1).
specialize (IHe ge). intuition. simpl in H1.
intuition. simpl. unfold_tc_denote.
 remember (eval_expr rho e); destruct v;
intuition. 
exists b. exists i. st. intuition. constructor.
auto.

(*addrof*)

simpl in H1.
assert (ISPTR := eval_lvalue_ptr rho e Delta (te_of rho) (ve_of rho) (ge_of rho)).
specialize (IHe ge).
assert (mkEnviron (ge_of rho) (ve_of rho) (te_of rho) = rho). destruct rho; auto.
intuition; apply typecheck_environ_sound in H0. intuition. 
simpl. destruct H7. destruct H1. intuition. rewrite H0 in H9. inv H9.
destruct H7. destruct H1. destruct H0. destruct H0. simpl.
intuition. rewrite H9. constructor. auto.

(*unop*)
subst. st. intuition. unfold force_val. remember (sem_unary_operation u (eval_expr rho e) (typeof e)).
destruct o. eapply Clight_sem.eval_Eunop. eapply IHe; eauto. rewrite Heqo. auto.
apply typecheck_expr_sound in H3; auto. unfold sem_unary_operation in *.
destruct u. st. remember (typeof e); destruct t0; try inv H2;
try destruct i;try destruct s; try inv H2; st; destruct t; intuition;
destruct (eval_expr rho e); intuition; unfold sem_notbool in *;
st; inv Heqo. 

st. remember (typeof e). destruct t0;
try destruct i; try destruct s; try inv H3; st; destruct t; intuition;
destruct (eval_expr rho e); intuition; unfold sem_notint in *;
st; inv Heqo. 

st. remember (typeof e). destruct t0;
try destruct i; try destruct s; try inv H3; st; destruct t; intuition;
destruct (eval_expr rho e); intuition; unfold sem_neg in *;
st; inv Heqo.

(*binop*)
subst. st. intuition. unfold force_val.
remember (sem_binary_operation b (eval_expr rho e1) (typeof e1) (eval_expr rho e2)
(typeof e2) (fun (_ : block) (_ : Z) => false)).
destruct o. eapply Clight_sem.eval_Ebinop. eapply IHe1; eauto.
eapply IHe2. apply H. apply H3. auto. apply typecheck_expr_sound in H3; auto.
rewrite Heqo.

apply tc_binaryop_nomem with (t:=t); auto.
specialize (IHe1 ge). specialize (IHe2 ge). intuition.
clear H6 H8. 
eapply eval_binop_relate_fail; eauto.

(*Cast*)
subst. assert (TC := typecheck_expr_sound _ _ _ H0 H1).
st. intuition. unfold force_val. remember (sem_cast (eval_expr rho e) (typeof e) t).
destruct o. eapply Clight_sem.eval_Ecast. eapply IHe. auto. apply H2. auto.

specialize (IHe ge). intuition. (*seems too easy, maybe functions are exactly the same?
still suprising to not deal with float case, commented below*)
(*
apply typecheck_expr_sound in H2; auto. 
remember (typeof e). remember (eval_expr rho e). destruct v; intuition; st;
destruct t0; intuition; destruct t; intuition; try destruct i0; try destruct s;
try destruct i1;try destruct s0; intuition;try solve [inv Heqo]; try destruct i; intuition;
st; try rewrite <- Heqv in H3; unfold sem_cast in *;
try solve [st; intuition; try unfold Float.intoffloat in *; try unfold Float.intuoffloat in *;
destruct (Float.Zoffloat f); intuition;
rewrite H1 in Heqo; rewrite H4 in Heqo; st; inv Heqo; 
destruct i; intuition]. inv Heqo. inv Heqo. *)

admit. (*Pass for now, since cond might go away.....======================================================*)

(*Field*)
assert (TC:= typecheck_lvalue_sound _ _ _ H0 H1).
specialize (IHe ge). specialize (TC some_pt_type). intuition. simpl in H1. intuition.
st. remember (eval_lvalue rho e). destruct v; intuition.
remember (typeof e). destruct t0; intuition. remember (field_offset i f).
destruct r; intuition. st. exists b. exists (Int.add i0 (Int.repr z)). 
intuition. eapply Clight_sem.eval_Efield_struct; auto.
destruct H1. destruct H1. intuition. inv H7. 
(*new thing*)
eapply Clight_sem.eval_Elvalue in H4.
apply H4. rewrite <- Heqt0. auto. apply Csem.deref_loc_copy. rewrite <- Heqt0. auto.
eauto. eauto.  
st. exists b. exists i0. intuition. eapply Clight_sem.eval_Efield_union; eauto.

destruct H1. destruct H1. intuition. eapply Clight_sem.eval_Elvalue in H4.
apply H4. rewrite <- Heqt0. auto. inv H7. apply Csem.deref_loc_copy. rewrite <- Heqt0. auto.

Qed.

Lemma eval_expr_relate:
  forall Delta ge rho e m,
           filter_genv ge = ge_of rho ->
           typecheck_environ rho Delta = true ->
           (denote_tc_assert (typecheck_expr Delta e) rho ->
             Clight_sem.eval_expr ge (ve_of rho) (te_of rho) m e  (eval_expr rho e)).
Proof.
apply eval_both_relate.
Qed.

Lemma eval_lvalue_relate:
  forall Delta ge rho e m,
           filter_genv ge = ge_of rho ->
           typecheck_environ rho Delta = true ->
          
           (denote_tc_assert (typecheck_lvalue Delta e) rho ->
             exists b, exists ofs, 
              Clight_sem.eval_lvalue ge (ve_of rho) (te_of rho) m e b ofs /\
              eval_lvalue rho e = Vptr b ofs).
apply eval_both_relate.
Qed.

