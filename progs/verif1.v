Require Import msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import compcert.Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.client_lemmas.
Require Import progs.list.


Instance Nassert: NatDed assert := _.
Instance Sassert: SepLog assert := _.
Instance Cassert: ClassicalSep assert := _. 
Instance Iassert: Indir assert := _.
Instance SIassert: SepIndir assert := _.

Local Open Scope logic.

Lemma local_unfold: forall P rho, local P rho = !! (P rho).
Proof. reflexivity. Qed.
Hint Rewrite local_unfold : normalize.
Lemma lift2_unfold: forall {A1 A2 B} (f: A1 -> A2 -> B) a1 a2 rho,
        lift2 f a1 a2 rho = f (a1 rho) (a2 rho).
Proof. reflexivity. Qed.
Lemma lift1_unfold: forall {A1 B} (f: A1 -> B) a1 rho,
        lift1 f a1 rho = f (a1 rho).
Proof. reflexivity. Qed.
Hint Rewrite @lift2_unfold @lift1_unfold : normalize.


Lemma andp_unfold: forall P Q rho,
  @andp assert Nassert P Q rho = @andp mpred Nveric (P rho) (Q rho).
Proof. reflexivity. Qed.
Hint Rewrite andp_unfold: normalize.

Lemma prop_and {A} {NA: NatDed A}: 
    forall P Q: Prop, prop (P /\ Q) = (prop P && prop Q).
Proof. intros. apply pred_ext. apply prop_left. intros [? ?]; normalize.
   normalize. apply prop_left; normalize.
Qed.
Hint Rewrite @prop_and : normalize.

Lemma exp_unfold : forall A P rho,
 @exp assert Nassert A P rho = @exp mpred Nveric A (fun x => P x rho).
Proof.
intros. reflexivity. 
Qed.
Hint Rewrite exp_unfold: normalize.

Definition PROPx (P: list Prop) (Q: assert) := andp (prop (fold_right and True P)) Q.

Notation "'PROP' ( x ; .. ; y )   z" := (PROPx (cons x%type .. (cons y%type nil) ..) z) (at level 10) : logic.
Notation "'PROP' ()   z" :=   (PROPx nil z) (at level 10) : logic.
Notation "'PROP' ( )   z" :=   (PROPx nil z) (at level 10) : logic.

Definition LOCALx (Q: list (environ -> Prop)) (R: assert) := 
                 andp (local (fold_right (lift2 and) (lift0 True) Q)) R.

Notation " 'LOCAL' ( )   z" := (LOCALx nil z)  (at level 9) : logic.
Notation " 'LOCAL' ()   z" := (LOCALx nil z)  (at level 9) : logic.

Notation " 'LOCAL' ( x ; .. ; y )   z" := (LOCALx (cons x%type .. (cons y%type nil) ..) z)
         (at level 9) : logic.

Definition SEPx (R: list assert) : assert := fold_right sepcon emp R.

Notation " 'SEP' ( x * .. * y )" := (SEPx (cons x%logic .. (cons y%logic nil) ..))
         (at level 8) : logic.

Notation " 'SEP' ( ) " := (SEPx nil) (at level 8) : logic.
Notation " 'SEP' () " := (SEPx nil) (at level 8) : logic.

Definition do_canon := (@sepcon assert _ _).

Lemma canon1: forall P1 B  P Q R,
   do_canon (prop P1 && B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B  (PROPx (P1::P) (LOCALx Q (SEPx R))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho.
simpl.
normalize.
rewrite andp_assoc.
f_equal.
Qed.

Lemma canon2: forall Q1 B P Q R,
    do_canon (local Q1 && B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx (Q1::Q) (SEPx R))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho.
simpl.
normalize.
rewrite andp_assoc.
f_equal.
Qed.

Definition nonlocal (Q: assert) := True.

Ltac check_nonlocal :=
  match goal with
  |  |- nonlocal (local _) => fail 1 
  |  |- nonlocal (prop _) => fail 1 
  |  |- nonlocal (andp _ _) => fail 1
  |  |- nonlocal (sepcon _ _) => fail 1
  | |- _ => apply I
 end.

Lemma canon3: forall R1 B P Q R,
    nonlocal R1 ->
    do_canon (B * R1) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
clear H.
extensionality rho.
simpl.
rewrite sepcon_assoc.
f_equal.
rewrite sepcon_andp_prop.
f_equal.
normalize.
Qed.

Lemma canon4: forall P, do_canon emp P = P. 
Proof.
apply emp_sepcon.
Qed.

Lemma canon7: forall R1 P Q R, 
   nonlocal R1 -> 
   do_canon R1 (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho.
simpl.
normalize.
Qed.
 
Lemma canon8: forall R1 R2 R3 PQR,
    do_canon ((R1 && R2) && R3) PQR = do_canon (R1 && (R2 && R3)) PQR.
Proof. intros; rewrite andp_assoc; auto. 
Qed.

Lemma start_canon: forall P, P  = do_canon P (PROPx nil (LOCALx nil (SEPx nil ))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho; simpl.
normalize.
Qed.

Hint Rewrite canon1 canon2 canon4 canon8 : canon.
Hint Rewrite canon3 using check_nonlocal : canon.
Hint Rewrite canon7 using check_nonlocal : canon.
Hint Rewrite <- (@sepcon_assoc assert _) : canon.


Definition islocal (P: assert) := exists Q, P = local Q.
Lemma islocal_local: forall Q, islocal (local Q).
Proof. intros; econstructor; eauto. Qed.

Lemma islocal_andp: forall P Q, islocal P -> islocal Q -> islocal (P && Q).
Proof.
 intros. destruct H; destruct H0; subst.
  exists (fun rho, x rho /\ x0 rho).
 extensionality rho.
 unfold local, lift1. simpl.
 apply pred_ext; normalize.
Qed.

Lemma islocal_prop: forall Q, islocal (prop Q).
Proof.
intros. exists (fun rho => Q). unfold local, lift1. extensionality rho; simpl. auto.
Qed.
Hint Resolve islocal_local islocal_andp islocal_prop: local canon.

Lemma canon5: forall Q R S, 
       nonlocal Q ->
       Q && (local R && S) = local R && (Q && S).
Admitted.


Lemma canon5b: forall Q R S, 
       nonlocal Q ->
       Q && (S && local R) = local R && (Q && S).
Admitted.

Lemma canon5c: forall Q R, 
       nonlocal Q ->
       (Q && local R) = local R && Q.
Admitted.

Lemma canon6: forall Q R S, 
       nonlocal Q ->
       Q && (prop R && S) = prop R && (Q && S).
Admitted.

Lemma canon6b: forall Q R S, 
       nonlocal Q ->
       Q && (S && prop R) = prop R && (Q && S).
Admitted.

Lemma canon6c: forall Q R, 
       nonlocal Q ->
       (Q && prop R) = prop R && Q.
Admitted.

Hint Rewrite canon5 using check_nonlocal : canon.
Hint Rewrite canon5b using check_nonlocal : canon.
Hint Rewrite canon5c using check_nonlocal : canon.
Hint Rewrite canon6 using check_nonlocal : canon.
Hint Rewrite canon6b using check_nonlocal : canon.
Hint Rewrite canon6c using check_nonlocal : canon.

Lemma finish_canon: forall R1 P Q R, 
   do_canon R1 (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
unfold do_canon, PROPx, LOCALx, SEPx; intros.
extensionality rho.
simpl.
normalize.
Qed.

Goal forall (foo: environ -> Prop)(P: Prop) (Q: assert), 
   Q && (local foo && prop P) =  (PROP(P) LOCAL (foo) SEP (Q)).
intros.
 etransitivity.
 rewrite (start_canon (Q && (local foo && prop P))).
 autorewrite with canon. reflexivity.
 auto.
Qed.

Ltac canonicalize_pre :=
  match goal with |- semax _ _ ?P _ _ =>
      rewrite (start_canon P); autorewrite with canon
  end.    

(*
 Check (PROP(True) LOCAL (lift0 False) SEP (emp * emp)%logic)%logic.
Check (PROP (True) SEP (emp))%logic.
*)

Require progs.test1.
Module P := progs.test1.

Local Open Scope logic.

Instance t_list_spec: listspec P.t_listptr.
Proof.
econstructor.
reflexivity.
intro Hx; inv Hx.
intros.
unfold unroll_composite; simpl.
reflexivity.
econstructor; simpl; reflexivity.
Defined.

Definition int2valt (i: int) := (Vint i, P.t_int).

Definition ilseg (s: list int) p q := lseg P.t_listptr (map Vint s) p q.

Definition semax_body' (G:  funspecs) (f: function) (spec: ident * funspec) :=
  match spec with (i, mk_funspec _ A pre post) => semax_body G f A pre post end.

Lemma typecheck_val_ptr_lemma:
  forall rho Delta id t a init,
  typecheck_environ rho Delta = true ->
  (temp_types Delta) ! id =  Some (Tpointer t a, init) ->
  bool_val (eval_id id rho) (Tpointer t a) = Some true ->
  typecheck_val (eval_id id rho) (Tpointer t a) = true.
Proof.
Admitted.

(*
Lemma bool_val_notbool_ptr:
    forall v t a,
   (bool_val (force_val (sem_notbool v (Tpointer t a))) type_bool = Some true) = (v = nullval).
Proof.
 intros.
 apply prop_ext; split; intros.
 destruct v; simpl in H; try discriminate.
 apply bool_val_int_eq_e in H. subst; auto.
 subst. simpl. auto.
Qed.
*)

Lemma bool_val_notbool_ptr:
    forall v t,
   match t with Tpointer _ _ => True | _ => False end ->
   (bool_val (force_val (sem_notbool v t)) type_bool = Some true) = (v = nullval).
Proof.
 intros.
 destruct t; try contradiction. clear H.
 apply prop_ext; split; intros.
 destruct v; simpl in H; try discriminate.
 apply bool_val_int_eq_e in H. subst; auto.
 subst. simpl. auto.
Qed.

Hint Rewrite bool_val_notbool_ptr using (solve [simpl; auto]) : normalize.
Hint Rewrite Int.add_zero  Int.add_zero_l Int.sub_zero_l : normalize.

Lemma lseg_unroll': forall T {ls: listspec T} l x z , 
    lseg T l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || 
                          (EX h:val, EX r:list val, EX y:val, 
                          !! (ptr_neq x z) &&  !!(l=h::r) && 
                       field_mapsto Share.top list_struct list_data x h 
                      * field_mapsto Share.top list_struct list_link x y
                      * |> lseg T r y z).
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
normalize.
apply orp_right1; auto.
apply orp_right2.
apply exp_right with v.
apply exp_right with l.
normalize. intro y.
apply exp_right with y.
normalize.
apply orp_left; auto.
normalize.
normalize.
intros. inv H0.
apply orp_left.
normalize.
inv H0.
normalize.
intros.
inv H0.
apply exp_right with x2.
normalize.
Qed.

Definition ilseg_nil (l: list  int) x z : mpred := !! (ptr_eq x z) && !! (l=nil) && emp.
Definition ilseg_cons l x z : mpred := 
                          (EX h:int, EX r:list int, EX y:val, 
                          !! (ptr_neq x z) &&  !!(l=h::r) && 
                       field_mapsto Share.top list_struct list_data x (Vint h) 
                      * field_mapsto Share.top list_struct list_link x y
                      * |> ilseg r y z).

Lemma ilseg_unroll': forall l x z , 
    ilseg l x z = ilseg_nil l x z || ilseg_cons l x z.
Proof.
intros.
unfold ilseg at 1.
rewrite lseg_unroll'.
unfold ilseg_cons, ilseg_nil, ilseg.
f_equal.
f_equal. f_equal.
f_equal.
apply prop_ext; split; intro; destruct l; simpl in *; congruence.
apply pred_ext; normalize.
intros h r ? y. destruct l; inv H0.
apply exp_right with i.
apply exp_right with l.
apply exp_right with y.
normalize.
intros h r y.
apply exp_right with (Vint h).
apply exp_right with (map Vint r).
apply exp_right with y.
simpl.
normalize.
Qed.


Lemma expr_false_ptr: 
  forall e, match typeof e with Tpointer _ _ => True | _ => False end ->
     forall rho,  (expr_false e rho) = (eval_expr e rho = nullval).
Proof.
intros.
unfold expr_false.
destruct (typeof e); try contradiction.
unfold lift1, typed_false, strict_bool_val; simpl.
destruct (eval_expr e rho); apply prop_ext; intuition; try congruence.
inv H0. 
pose proof (Int.eq_spec i Int.zero); destruct (Int.eq i Int.zero); subst; auto.
inv H0.
inv H0. rewrite Int.eq_true. auto.
inv H0. inv H0.
Qed.

Lemma expr_true_Cnot_ptr: 
  forall e, match typeof e with Tpointer _ _ => True | _ => False end ->
     forall rho,  (expr_true (Cnot e) rho) = (eval_expr e rho = nullval).
Proof.
intros.
 unfold expr_true, Cnot.
 unfold lift1. simpl. destruct (typeof e); try contradiction.
 unfold typed_true; simpl.
 destruct (eval_expr e rho); simpl; try solve [ apply prop_ext; intuition discriminate].
 pose proof (Int.eq_spec i Int.zero).
 destruct (Int.eq i Int.zero).
 subst. simpl. apply prop_ext; intuition.
  subst. simpl. apply prop_ext; intuition.
 congruence. inv H1. contradiction H0. auto.
Qed.
Hint Rewrite expr_true_Cnot_ptr using (solve [simpl; auto]) : normalize.

Lemma expr_true_Cnot_ptr': 
  forall e, match typeof e with Tpointer _ _ => True | _ => False end ->
    local (expr_true (Cnot e)) = local (fun rho => eval_expr e rho = nullval).
Proof.
 intros. extensionality rho. unfold local, lift0, lift1. f_equal. 
apply expr_true_Cnot_ptr; auto.
Qed.
Hint Rewrite expr_true_Cnot_ptr' using (solve [simpl; auto]) : normalize.

Lemma fst_unfold: forall {A B} (x: A) (y: B), fst (x,y) = x.
Proof. reflexivity. Qed.
Lemma snd_unfold: forall {A B} (x: A) (y: B), snd (x,y) = y.
Proof. reflexivity. Qed.
Hint Rewrite @fst_unfold @snd_unfold : normalize.

Lemma ilseg_eq: forall s p, 
   typecheck_val p P.t_listptr = true -> 
    (ilseg s p p = !!(s=nil) && emp).
Proof. intros. unfold ilseg. rewrite lseg_eq; auto. f_equal. f_equal.
 apply prop_ext. destruct s; simpl; intuition congruence.
Qed.
Hint Rewrite ilseg_eq : normalize.

Lemma ilseg_nonnull:
  forall s v,
      typed_true P.t_listptr v ->
     ilseg s v nullval = ilseg_cons s v nullval.
Proof.
intros. subst. 
rewrite ilseg_unroll'.
unfold ilseg_cons, ilseg_nil.
apply pred_ext; normalize.
apply orp_left; auto. normalize.
unfold typed_true, strict_bool_val,ptr_eq in *.
destruct v; simpl in *; try contradiction.
rewrite H0 in H. inv H.
intros.
apply orp_right2. apply exp_right with x; normalize. apply exp_right with x0; normalize.
apply exp_right with x1; normalize.
Qed.

Lemma ilseg_nonnull':
  forall e' rho s e,
    expr_true e' rho ->
    e = eval_expr e' rho ->
     ilseg s e nullval = ilseg_cons s e nullval.
Proof.
intros. subst. 
rewrite ilseg_unroll'.
unfold ilseg_cons, ilseg_nil.
apply pred_ext; normalize.
apply orp_left; auto. normalize.
unfold expr_true, bool_val,ptr_eq in *.
unfold lift1, typed_true, strict_bool_val in H; simpl in H.
destruct (eval_expr e' rho); simpl in *; try contradiction.
rewrite H0 in H. destruct (typeof e'); inv H.
intros.
apply orp_right2. apply exp_right with x; normalize. apply exp_right with x0; normalize.
apply exp_right with x1; normalize.
Qed.

Lemma lift2_ilseg_cons: 
 forall s p q, lift2 (ilseg_cons s)  p q =
    EX h:int, EX r: list int, EX y: val,
      local (lift2 ptr_neq p q) &&
      !! (s = h::r) &&
      lift2 (field_mapsto Share.top list_struct list_data) p (lift0 (Vint h)) *
      lift2 (field_mapsto Share.top list_struct list_link) p (lift0 y) *
      |> lift2 (ilseg r) (lift0 y) q.
Proof. reflexivity. Qed.
Hint Rewrite lift2_ilseg_cons : normalize.

Lemma local_andp_prop:  forall P Q, local P && prop Q = prop Q && local P.
Proof. intros. apply andp_comm. Qed.
Lemma local_andp_prop1: forall P Q R, local P && (prop Q && R) = prop Q && (local P && R).
Proof. intros. rewrite andp_comm. rewrite andp_assoc. f_equal. apply andp_comm. Qed.
Hint Rewrite local_andp_prop local_andp_prop1 : normalize.

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
Hint Rewrite local_sepcon_assoc1 local_sepcon_assoc2 : normalize.

Lemma reassoc_local:
  forall P Q R, local P && (local Q && R) = (local P && local Q) && R.
Proof. intros. symmetry ; apply andp_assoc. Qed.

Ltac strip1_later P :=
 match P with 
 | |> ?L && |> ?R => constr:(L && R)
 | ?L && |> ?R => let Z := strip1_later L in constr:(Z && R)
 | |> ?L && ?R => let Z := strip1_later R in constr:(L && Z)
 | ?L && ?R => let L' := strip1_later L in let R' := strip1_later R in constr:(L' && R')
 | |> ?L * |> ?R => constr:(L * R)
 | ?L * |> ?R => let Z := strip1_later L in constr:(Z * R)
 | |> ?L * ?R => let Z := strip1_later R in constr:(L * Z)
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

Hint Resolve andp_later_derives sepcon_later_derives sepcon_derives
              andp_derives imp_derives now_later derives_refl: derives.



Lemma load_field_assoc:
  forall P Q R S : assert, islocal Q ->
            (P && |> (Q && (R * S))) = (P && (|> (S * (Q && R)))).
Proof.
intros.
f_equal.
f_equal.
destruct H as [Q' ?].
subst.
extensionality rho; unfold local, lift1; simpl.
normalize.
f_equal.
apply sepcon_comm.
Qed.

Lemma cconv_sepcon1 {A}{ND: NatDed A}{SA: SepLog A}:
  forall P Q Q': A,  Q |-- Q' -> P * Q |-- P * Q'.
Proof. 
 intros. apply sepcon_derives; auto.
Qed.
Lemma cconv_sepcon2 {A}{ND: NatDed A}{SA: SepLog A}:
  forall P Q Q': A,  Q |-- Q' -> Q * P |-- Q' * P.
Proof. 
 intros. apply sepcon_derives; auto.
Qed.
Lemma cconv_andp1 {A}{ND: NatDed A}:
  forall P Q Q': A,  Q |-- Q' -> P && Q |-- P && Q'.
Proof. 
 intros. apply andp_derives; auto.
Qed.
Lemma cconv_andp2 {A}{ND: NatDed A}:
  forall P Q Q': A,  Q |-- Q' -> Q && P |-- Q'  && P.
Proof. 
 intros. apply andp_derives; auto.
Qed.

Hint Resolve @cconv_sepcon1 @cconv_sepcon2 @cconv_andp1 @cconv_andp2 : cconv.

Notation "'DECLARE' x s" := (x: ident, s: funspec)
   (at level 160, x at level 0, s at level 150, only parsing).

Definition retval : environ -> val := eval_id ret_temp.

Notation "'WITH' x 'PRE' [ a : ta ] P 'POST' [ tz ] Q" := 
     (mk_funspec ((a, ta)::nil, tz) _ (fun x => P%logic) (fun x => Q%logic))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).

Notation "'WITH' x : tx 'PRE' [ a : ta ] P 'POST' [ tz ] Q" := 
     (mk_funspec ((a, ta)::nil, tz) tx (fun x => P%logic) (fun x => Q%logic))
            (at level 200, x at level 0, z at level 0, P at level 100, Q at level 100, a at level 0).

Definition sumlist_spec :=
 DECLARE P.i_sumlist
  WITH contents 
  PRE [ P.i_p : P.t_listptr]  lift2 (ilseg contents) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_int ]  local (lift1 (eq (Vint (fold_right Int.add Int.zero contents))) retval).

Definition reverse_spec :=
 DECLARE P.i_reverse
  WITH contents : list int
  PRE  [ P.i_p : P.t_listptr ] lift2 (ilseg contents) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_listptr ] lift2 (ilseg (rev contents)) retval (lift0 nullval).

Definition main_spec := (P.i_main, mk_funspec (nil, P.t_int) _ (main_pre P.prog) (main_post P.prog)).

Definition Gprog : funspecs := 
   sumlist_spec :: reverse_spec :: main_spec::nil.

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Definition sumlist_Inv (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL (lift1 (partial_sum contents cts) (eval_id P.i_s)) 
            SEP (lift2 (ilseg cts) (eval_id P.i_t) (lift0 nullval))).

Lemma closed_wrt_local_and: forall S P Q,
  closed_wrt_vars S (local P) ->
  closed_wrt_vars S (local Q) ->
  closed_wrt_vars S (local (lift2 and P Q)).
Proof.
Admitted.
Hint Resolve closed_wrt_local_and: closed.

Lemma closed_wrt_local1: forall a b f, 
  a <> b -> closed_wrt_vars (modified1 a) (local (lift1 f (eval_id b))).
Proof.
intros.
intros rho ? ?.
unfold local, lift1. f_equal.
f_equal.
unfold eval_id, force_val.
simpl.
destruct (H0 b). hnf in H1. subst; contradiction H; auto.
rewrite H1; auto.
Qed.
Hint Extern 2 (closed_wrt_vars (modified1 _) (local (lift1 _ (eval_id _)))) => 
      (apply closed_wrt_local1; solve [let Hx := fresh in (intro Hx; inv Hx)]) : closed.


Lemma closed_wrt_local2: forall a b c f, 
  a <> b -> a <> c -> closed_wrt_vars (modified1 a) (local (lift2 f (eval_id b) (eval_id c))).
Proof.
intros.
intros rho ? ?.
unfold local, lift1, lift2. f_equal.
f_equal.
admit.
admit.
Qed.
Hint Extern 2 (closed_wrt_vars (modified1 _) (local (lift2 _ (eval_id _) (eval_id _)))) => 
      (apply closed_wrt_local2; solve [let Hx := fresh in (intro Hx; inv Hx)]) : closed.

Lemma closed_wrt_lift1: forall a b f, 
  a <> b -> closed_wrt_vars (modified1 a) (lift1 f (eval_id b)).
Proof.
intros.
intros rho ? ?.
unfold lift1. f_equal.
unfold eval_id, force_val.
simpl.
destruct (H0 b). hnf in H1. subst; contradiction H; auto.
rewrite H1; auto.
Qed.

Hint Extern 2 (closed_wrt_vars (modified1 _) (lift1 _ (eval_id _))) => 
      (apply closed_wrt_lift1; solve [let Hx := fresh in (intro Hx; inv Hx)]) : closed.

Lemma closed_wrt_lift2: forall a b c f, 
  a <> b -> a <> c -> closed_wrt_vars (modified1 a) (lift2 f (eval_id b) (eval_id c)).
Proof.
intros.
intros rho ? ?.
unfold lift2, lift1. f_equal.
unfold eval_id, force_val.
simpl.
destruct (H1 b). hnf in H2. subst; contradiction H; auto.
rewrite H2; auto.
unfold eval_id, force_val.
simpl.
destruct (H1 c). hnf in H2. subst; contradiction H0; auto.
rewrite H2; auto.
Qed.
Hint Extern 2 (closed_wrt_vars (modified1 _) (lift2 _ (eval_id _) (eval_id _))) => 
      (apply closed_wrt_lift2; solve [let Hx := fresh in (intro Hx; inv Hx)]) : closed.
(*
Lemma closed_wrt_PROPx:
 forall S P Q, closed_wrt_vars S Q -> closed_wrt_vars S (PROPx P Q).
Proof.
Admitted. 
Hint Resolve closed_wrt_PROPx: closed.

Lemma closed_wrt_LOCALx:
 forall S Q R, closed_wrt_vars S (local Q) -> closed_wrt_vars S R -> closed_wrt_vars S (LOCALx Q R).
Admitted. 
Hint Resolve closed_wrt_LOCALx: closed.

Lemma closed_wrt_SEPx: forall S P, closed_wrt_vars S P -> closed_wrt_vars S (SEPx P).
Admitted. 
Hint Resolve closed_wrt_SEPx: closed.
Lemma closed_wrt_local_lift0: forall S Q, closed_wrt_vars S (local (lift0 Q)).
Proof.
intros. intro; intros. unfold local, lift1, lift0. auto.
Qed.
Hint Resolve closed_wrt_local_lift0: closed.

*)

Lemma forward_set:
  forall Delta G P1 P2 P3 id e c Q,
  typecheck_temp_id id (typeof e) Delta = true ->
  temp_free_in id e = false ->
  closed_wrt_vars (modified1 id) (PROPx P1 (LOCALx P2 (SEPx P3))) ->
  (forall rho, tc_expr Delta e rho) ->
  semax (initialized id Delta) G
             (PROPx P1 (LOCALx (lift2 eq (eval_id id) (eval_expr e) :: P2) (SEPx P3)))
             c Q ->
  semax Delta G (PROPx P1 (LOCALx P2 (SEPx P3))) (Ssequence (Sset id e) c) Q.
Proof.
intros.
eapply forward_set; try eassumption.
eapply semax_pre; try apply H3.
unfold PROPx, LOCALx, SEPx; intro rho; simpl; normalize.
Qed.


Lemma insert_local: forall Q1 P Q R,
  local Q1 && (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx (Q1 :: Q) (SEPx R))).
Proof.
intros. extensionality rho.
unfold PROPx, LOCALx, SEPx, lift2.
normalize.
unfold local, lift1. simpl.
f_equal.
apply pred_ext; normalize.
Qed.

Lemma semax_pre:
 forall P' Delta G P1 P2 P3 c R,
     (PROPx P1 (LOCALx (tc_environ Delta :: P2) (SEPx P3))) |-- P' ->
     semax Delta G P' c R  -> 
     semax Delta G (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof.
intros.
eapply semax_pre; try apply H0.
 rewrite insert_local. auto.
Qed.

Ltac forward_while Inv Postcond :=
  apply semax_pre with Inv; 
  [ | apply semax_seq with Postcond;
    [ apply semax_while ; [ | compute; auto | | ] | ]].

Hint Rewrite insert_local:  normalize.

Lemma exp_derives {A}{NA: NatDed A}{B}:
   forall F G: B -> A, (forall x, F x |-- G x) -> exp F |-- exp G.
Proof.
intros.
apply exp_left; intro x. apply exp_right with x; auto.
Qed.

Lemma lift_ilseg_cons_unfold:
   forall s p q, lift2 (ilseg_cons s) p q =
       EX h: int, EX r: list int, EX y: val,
         local (lift2 ptr_neq p q) && !!(s = h :: r) &&
         lift2 (field_mapsto Share.top list_struct list_data) p (lift0 (Vint h)) *
         lift2 (field_mapsto Share.top list_struct list_link) p (lift0 y) * |> lift2 (ilseg r) (lift0 y) q.
Proof. intros; extensionality rho; reflexivity.
Qed.
 

Ltac find_in_list A L :=
 match L with 
  | A :: _ => constr:(O)
  | _ :: ?Y => let n := find_in_list A Y in constr:(S n)
  | nil => fail
  end.

Fixpoint delete_nth {A} (n: nat) (xs: list A) {struct n} : list A :=
 match n, xs with
 | O, y::ys => ys
 | S n', y::ys =>y :: delete_nth n' ys
 | _ , _ => nil
 end.


Lemma grab_nth_LOCAL:
   forall n B P Q R,
    do_canon B (PROPx P (LOCALx Q (SEPx R))) = 
    do_canon (local (nth n Q (lift0 True)) && B) (PROPx P (LOCALx Q (SEPx R))).
Proof.
intros n B P Q R; revert n Q B.
induction n; intros.
destruct Q; simpl nth.
f_equal.
extensionality rho; unfold local, lift0,lift1. simpl. normalize.
rewrite canon2.
f_equal.
f_equal.
extensionality rho; unfold LOCALx; simpl.
f_equal.
unfold local, lift1, lift2.
f_equal.
apply prop_ext; intuition.
destruct Q; simpl nth.
f_equal.
extensionality rho; unfold local, lift0,lift1. simpl. normalize.
rewrite <- canon2.
rewrite <- canon2.
rewrite IHn.
f_equal.
unfold local, lift0, lift1, lift2; extensionality rho.
simpl.
apply pred_ext; normalize.
Qed.

Lemma grab_nth_SEP:
   forall n B P Q R,
    do_canon B (PROPx P (LOCALx Q (SEPx R))) = do_canon (B* nth n R emp) (PROPx P (LOCALx Q (SEPx (delete_nth n R)))).
Proof.
intros n B P Q R; revert n R B.
induction n; intros.
destruct R.
simpl nth.  unfold delete_nth.
f_equal. extensionality rho; simpl; symmetry; apply sepcon_emp.
simpl nth.
unfold delete_nth.
rewrite canon3 by apply I. auto.
destruct R.
simpl nth.  unfold delete_nth.
f_equal. extensionality rho; simpl; symmetry; apply sepcon_emp.
rewrite <- canon3 by apply I.
rewrite (IHn _ (B*a)).
simpl nth.
replace (delete_nth (S n) (a::R)) with (a :: delete_nth n R) by reflexivity.
rewrite <- canon3 by apply I.
f_equal.
repeat rewrite sepcon_assoc.
f_equal.
apply sepcon_comm.
Qed.

Lemma restart_canon: forall P Q R, (PROPx P (LOCALx Q (SEPx R))) = do_canon emp (PROPx P (LOCALx Q (SEPx R))).
Proof.
intros.
unfold do_canon. rewrite emp_sepcon. auto.
Qed.

Lemma ilseg_nonnullx: 
  forall s p q,
   local (lift1 (typed_true P.t_listptr) p) && lift2 (ilseg s) p q = 
   EX  h : int,
      EX  r : list int,
       EX  y : val,
         local (lift2 ptr_neq p q) && !!(s = h :: r) &&
         lift2 (field_mapsto Share.top list_struct list_data) p
           (lift0 (Vint h)) *
         lift2 (field_mapsto Share.top list_struct list_link) p (lift0 y) *
         |>lift2 (ilseg r) (lift0 y) q.
Admitted.

Lemma exp_do_canon:
   forall T (P: T -> assert) (Q: assert), do_canon (exp P) Q = EX x:_, do_canon (P x) Q.
Proof. apply exp_sepcon1. Qed.
Hint Rewrite exp_do_canon: canon.
Hint Rewrite exp_do_canon: normalize.

Ltac go_lower := 
 let rho := fresh "rho" in intro rho; unfold PROPx, LOCALx, SEPx; simpl; normalize.

Ltac change_in_pre S S' :=
 match goal with |- semax _ _ ?P _ _ =>
  match P with context C[S] =>
     let P' := context C[S'] in apply semax_pre with P'; [go_lower | ]
  end
 end.

Lemma semax_extract_PROP:
  forall Delta G (PP: Prop) P QR c Post,
       (PP -> semax Delta G (PROPx P QR) c Post) -> 
       semax Delta G (PROPx (PP::P) QR) c Post.
Proof.
intros.
apply client_lemmas.semax_pre with (!!PP && PROPx P QR).
unfold PROPx in *; simpl. normalize.
apply semax_extract_prop.
auto.
Qed.

Definition bind1' (i1: ident) (P: assert) (args: list val): mpred :=
   match args with a::nil => ALL rho: environ, !! (eval_id i1 rho = a) --> P rho
  | _ => FF
  end.


Lemma body_sumlist: semax_body' Gprog P.f_sumlist sumlist_spec.
Proof.
intro contents.
simpl fn_body; simpl fn_params; simpl fn_return.
normalize.    
canonicalize_pre.
apply forward_set; [compute; auto | compute; auto | auto 50 with closed | compute; auto | ].
admit. (* closed *)
apply forward_set; [compute; auto | compute; auto | auto with closed | compute; auto | ].
admit. (* closed *)

forward_while (sumlist_Inv contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P.i_s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv.
apply exp_right with contents.
go_lower.
rewrite H0. rewrite H1. simpl. unfold partial_sum.
rewrite Int.add_zero_l. normalize.
(* Prove that loop invariant implies typechecking condition *)
intros; unfold tc_expr; simpl; normalize.
(* Prove that invariant && not loop-cond implies postcondition *)
unfold sumlist_Inv.
go_lower.
intros cts ?.
unfold partial_sum in H0;  rewrite H0.
rewrite expr_false_ptr in H by (simpl; auto).
simpl in H. rewrite H. normalize.
(* Prove that loop body preserves invariant *)
unfold sumlist_Inv at 1.
normalize.
apply extract_exists_pre; intro cts.
normalize.
change_in_pre (ilseg cts) (ilseg_cons cts).
   rewrite ilseg_nonnull by auto.
   unfold ilseg_cons.
   normalize; intros h r ? y.
   apply exp_right with h; normalize.
   apply exp_right with r; normalize.
   apply exp_right with y; normalize.
rewrite lift_ilseg_cons_unfold.
rewrite restart_canon; rewrite (grab_nth_SEP 0);
   unfold nth, delete_nth.
   normalize; apply extract_exists_pre; intro h.
   normalize; apply extract_exists_pre; intro r.
   normalize; apply extract_exists_pre; intro y.
   autorewrite with canon.
apply semax_extract_PROP; intro. subst.

Admitted.

Lemma body_reverse: semax_body' Gprog P.f_reverse reverse_spec.
Proof.
intro contents.
simpl.
Admitted.

Lemma body_main:
   semax_body Gprog P.f_main _ (main_pre P.prog) (main_post P.prog).
Proof.
intro x; destruct x.
simpl.
Admitted.

Lemma all_funcs_correct:
  semax_func Gprog (prog_funct P.prog) Gprog.
Proof.
unfold Gprog, P.prog.
apply semax_func_cons; [ reflexivity | apply body_sumlist | ].
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.




