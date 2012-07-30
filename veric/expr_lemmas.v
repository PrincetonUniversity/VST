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


Definition temp_element_correct (te : temp_env) :=
(fun (tyconEl : (PTree.elt * type)) => let (id,elt) := tyconEl in
  match te ! id with
  | Some v => typecheck_val v elt = true
  | _ => False
end). 

Definition te_correct (te : temp_env) (Delta: tycontext) := Forall
  (temp_element_correct te)
  (map remove_assignedness (PTree.elements (temp_types Delta))).

Definition var_element_correct (ve: env) (ge:genviron) : 
(PTree.elt * type) -> Prop :=
(fun (varel : (PTree.elt * type)) => let (id,ty) := varel in
  match ve ! id with
  | Some (_,ty') => if type_eq ty ty' then True else False
  | None => match (ge id) with
        | Some (Vptr b i,ty2') => if type_eq ty ty2' && 
                              typecheck_val (Vptr b i) ty2' &&
                              is_pointer_type ty2'(*Double check===================================*)
                              (*^will be correct with change to base.v*)
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
unfold temp_types in *. simpl in *. split.

induction (PTree.elements t0).
constructor. 
unfold temp_element_correct.
simpl in *. destruct a. destruct p0. rewrite Forall_forall; intros.
destruct x. simpl in *. destruct H0. inv H0. destruct (te!e). 
destruct (typecheck_val v t3). auto. inv H. inv H.
destruct (te!p). remember (typecheck_val v t2) as b0. destruct b0. 
intuition. rewrite Forall_forall in *. unfold temp_element_correct in *.
specialize (H1 (e,t3)). intuition. inv H. inv H.

unfold var_types in *; simpl in *. rewrite andb_true_iff in H. destruct H.
clear H. rewrite Forall_forall. intros.  
destruct x. induction (PTree.elements t1). inv H.
simpl in *. destruct a. destruct H. inv H. destruct (ve !e). destruct p.
destruct (type_eq t2 t3); auto. inv H0. destruct (ge e). destruct p. 
destruct v; intuition.
destruct (type_eq t2 t3). simpl in *. remember (is_pointer_type t3).
destruct t3; destruct b0; simpl in *; intuition. simpl in *. intuition.
intuition. 

apply IHl.
clear IHl.  destruct (ve ! p). destruct p0. 
destruct (type_eq t3 t4). subst.
auto. inv H0. destruct (ge p). destruct p0.
destruct v; intuition. remember (is_pointer_type t4).
destruct (type_eq t3 t4); simpl in *; intuition. subst t3.
destruct t4; intuition; destruct b0; simpl in *; intuition.
inv H0. auto.
Qed.

Lemma typecheck_te_sound : forall dv te,
typecheck_temp_environ dv te = true ->
Forall (temp_element_correct te) dv.
Proof.
intros. induction dv. auto.
simpl in *. destruct a. remember (te! p). destruct o; auto.
remember (typecheck_val v t) as b0. destruct b0. 
rewrite Forall_forall. intros. simpl in H0. destruct H0. inv H0.
unfold temp_element_correct. rewrite <- Heqo. auto. intuition.
rewrite Forall_forall in H1. apply H1. auto. inv H. inv H.
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

(*I think I need this eventually
but can't figure it out right now...
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

remember (map remove_assignedness (PTree.elements t0)).
generalize dependent t0.
induction l; intros; auto.

simpl in *. destruct  a.  
remember (te ! p). destruct o; intuition.
remember (typecheck_val v0 t2). destruct b0; intuition.
remember ((PTree.set id v te) ! p).
destruct o. remember (typecheck_val v1 t2). destruct b0.
eapply H.
Focus 2. clear H.
assert (typecheck_val v1 t2 = true). 
apply typecheck_te_sound in H0. rewrite Forall_forall in *.
unfold temp_element_correct in H0.
clear Heqb1. 

Focus 3. clear H.   
assert (In (p,t3) (p,t3::l)).
assert (x:=eq_dec p id). destruct x. subst. rewrite PTree.gss in Heqo0.
inv Heqo0. apply typecheck_te_sound in H1. rewrite Forall_forall in H1.
unfold temp_element_correct in H1.

unfold typecheck_temp_environ in H. 
 rewrite typecheck_environ_sound in H1. 
*)



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
(*| [H : denote_tc_assert (tc_bool (negb ?X)) _ |- _] => idtac H; simpl in H; auto; destruct X; simpl in H; auto
| [H : denote_tc_assert (tc_bool ?X) _ |- _] => idtac H; simpl in H; auto; destruct X; simpl in H; auto
| [H : is_true(?X) |- _] => apply is_true_true in H; subst*)
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
simpl in *. subst. destruct rho. apply typecheck_environ_sound in H. intuition. 
unfold te_correct in *. unfold temp_element_correct in *.
rewrite Forall_forall in *. clear H2. 

simpl. unfold force_val.
destruct Delta. destruct p. 
unfold temp_types in *. simpl in *.
remember (t1 ! i). destruct o.
  symmetry in Heqo. apply PTree.elements_correct in Heqo. 
  destruct p. specialize (H1 (i,t3)). simpl in *. 
remember (type_eq t t3). destruct s; auto. subst.
apply in_rem_in in Heqo. intuition. destruct (te ! i); auto.
intuition.  

(*deref*)  
simpl in *. intuition.
destruct (eval_expr rho e); auto. destruct pt; auto.


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
destruct s; auto; try unfold Float.intoffloat; try unfold Float.intuoffloat;
st; intuition; rewrite <- Heqv in *; destruct f; auto;
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
st. intuition. 
remember (eval_expr rho e).
destruct v; intuition; 
destruct (typeof e); intuition.
destruct (field_offset i f); intuition.
simpl. destruct pt; auto.
destruct pt; auto.

Qed.

Lemma typecheck_expr_sound : forall Delta rho e,
 typecheck_environ rho Delta = true -> 
              denote_tc_assert (typecheck_expr Delta e) rho ->
             typecheck_val (eval_expr rho e) (typeof e) = true.
Proof. intros. 
assert (TC := typecheck_both_sound Delta rho e). intuition. Qed.


(*Figure out where this is used, would not hold when pointers typecheck as
ints*)
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


Lemma eval_expr_relate:
  forall Delta ge rho e m P,
              filter_genv ge = ge_of rho ->
              typecheck_environ rho Delta = true ->
              denote_tc_assert P rho ->
              typecheck_expr Delta e = P ->
              Clight_sem.eval_expr ge (ve_of rho) (te_of rho) m e  (eval_expr rho e).
Admitted.

Lemma eval_lvalue_relate:
  forall Delta ge rho e m,
              filter_genv ge = ge_of rho ->
              typecheck_environ rho Delta = true ->
              tc_lvalue Delta e rho ->
              exists b, exists ofs, 
              Clight_sem.eval_lvalue ge (ve_of rho) (te_of rho) m e b ofs /\
              eval_lvalue rho e = Vptr b ofs.
Admitted. 
