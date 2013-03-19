Load loadpath.
Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.queue.

Local Open Scope logic.

Instance QS: listspec t_struct_elem _next. 
Proof. eapply mk_listspec; reflexivity. Defined.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: int
  PRE [ 1%positive OF tint]
     PROP (4 <= Int.signed n) LOCAL (`(eq (Vint n)) (eval_id 1%positive)) SEP ()
  POST [ tptr tvoid ] `(memory_block Tsh n) retval.

Definition freeN_spec :=
 DECLARE _freeN
  WITH u: unit
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]  
      PROP() LOCAL () SEP (`(memory_block Tsh) (`force_int (eval_id 2%positive)) (eval_id 1%positive))
  POST [ tvoid ]  emp.

Definition elemrep (rep: elemtype QS) (p: val) : mpred :=
  field_mapsto Tsh t_struct_elem _a p (Vint (fst rep)) * 
  (field_mapsto Tsh t_struct_elem _b p (Vint (snd rep)) *
   (field_mapsto_ Tsh t_struct_elem _next p)).

Definition fifo (contents: list (elemtype QS)) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      field_mapsto Tsh t_struct_fifo _head p hd *
      field_mapsto Tsh t_struct_fifo _tail p tl *
      if isnil contents
      then (!!(tl=p) && emp)
      else (EX prefix: list (elemtype QS), EX ult:val, EX elem: elemtype QS,
              !!(tl=offset_val (Int.repr 8)  ult
                  /\ contents = prefix++(elem::nil))
            &&  (lseg QS Tsh prefix hd ult * 
                   elemrep elem ult)).

Definition fifo_new_spec :=
 DECLARE _fifo_new
  WITH u : unit
  PRE  [  ] emp
  POST [ (tptr t_struct_fifo) ] `(fifo nil) retval.

Definition fifo_put_spec :=
 DECLARE _fifo_put
  WITH q: val, contents: list (elemtype QS), elem: elemtype QS
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
          PROP () LOCAL (`(eq q) (eval_id _Q)) 
          SEP (`(fifo contents q); `(elemrep elem) (eval_id _p))
  POST [ tvoid ] `(fifo (contents++(elem :: nil)) q).

Definition fifo_empty_spec :=
 DECLARE _fifo_empty
  WITH q: val, contents: list (elemtype QS)
  PRE  [ _Q OF (tptr t_struct_fifo) ]
     PROP() LOCAL (`(eq q) (eval_id _Q)) SEP(`(fifo contents q))
  POST [ tint ] local (`(eq (if isnil contents then Vtrue else Vfalse)) retval) && `(fifo (contents) q).

Definition fifo_get_spec :=
 DECLARE _fifo_get
  WITH q: val, contents: list (elemtype QS), elem: elemtype QS
  PRE  [ _Q OF (tptr t_struct_fifo) ]
       PROP() LOCAL (`(eq q) (eval_id _Q)) SEP (`(fifo (elem :: contents) q)) 
  POST [ (tptr t_struct_elem) ] `(fifo contents q) * `(elemrep elem) retval.

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH a: int, b: int
  PRE  [ _a OF tint, _b OF tint ] 
        PROP() LOCAL(`(eq (Vint a)) (eval_id _a); `(eq (Vint b)) (eval_id _b)) SEP()
  POST [ (tptr t_struct_elem) ] `(elemrep (a,b)) retval.

Definition main_spec := 
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := 
    mallocN_spec :: freeN_spec :: fifo_new_spec :: fifo_put_spec 
         :: fifo_empty_spec :: fifo_get_spec 
         :: make_elem_spec :: main_spec::nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Lemma memory_block_fifo:
 forall e, 
   `(memory_block Tsh (Int.repr 8)) e =
  `(field_mapsto_ Tsh t_struct_fifo queue._head) e *
  `(field_mapsto_ Tsh t_struct_fifo queue._tail) e.
Proof.
 intros.
 extensionality rho. unfold_lift.
 normalize.
 change 8 with (sizeof t_struct_fifo).
 rewrite (memory_block_typed Tsh t_struct_fifo).
 simpl_typed_mapsto.
 reflexivity.
Qed.

Lemma list_cell_eq: forall sh p elem,
  list_cell QS sh p elem = 
   field_mapsto sh t_struct_elem _a p (Vint (fst elem)) * 
   field_mapsto sh t_struct_elem _b p (Vint (snd elem)). 
Proof. intros. simpl_list_cell. auto. Qed.

Lemma lift2more {A}{B}{T}:
  forall (v :A) (v': B) (F: A -> B -> T),
   @liftx (LiftEnviron T) (F v v') = 
     @liftx (Tarrow A (Tarrow B (LiftEnviron T))) F `v `v'.
Proof. reflexivity. Qed.

Lemma lift1more {A}{T}:
  forall (v :A) (F: A -> T),
   @liftx (LiftEnviron T) (F v) = 
     @liftx (Tarrow A (LiftEnviron T)) F `v.
Proof. reflexivity. Qed.

Definition blocks_match op v1 v2  :=
match op with Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => 
  match v1, v2 with
    Vptr b _, Vptr b2 _ => b=b2
    | _, _ => False
  end
| _ => True
end. 

Definition cmp_ptr_no_mem c v1 v2 :=
match v1,v2 with
Vptr b o, Vptr b1 o1 => 
  if zeq b b1 then
    Val.of_bool (Int.cmpu c o o1)
  else
    force_val (Cop.sem_cmp_mismatch c)
| _, _ => Vundef
end. 

Lemma semax_ptr_compare' : 
forall {Espec: OracleKind},
forall (Delta: tycontext) P Q R id cmp e1 e2 ty sh1 sh2,
    is_comparison cmp = true  ->
    typecheck_tid_ptr_compare Delta id = true ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R))
         |-- local (tc_expr Delta e1) &&
             local (tc_expr Delta e2)  && 
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1 ) * TT) && 
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2 ) * TT) ->
   @semax Espec Delta 
         (PROPx P (LOCALx Q (SEPx R)))
          (Sset id (Ebinop cmp e1 e2 ty)) 
        (normal_ret_assert 
          (EX old:val, 
           PROPx P
           (LOCALx (`eq (eval_id id)  (subst id `old 
                     (`(cmp_ptr_no_mem (op_to_cmp cmp)) (eval_expr e1) (eval_expr e2))) ::
                       map (subst id `old) Q)
           (SEPx (map (subst id `old) R))))).
Proof.
Admitted.


Lemma elemrep_isptr:
  forall elem v, elemrep elem v = !! (isptr v) && elemrep elem v.
Proof.
unfold elemrep; intros.
rewrite field_mapsto_isptr at 1.
normalize.
Qed.

Lemma address_mapsto_overlap:
  forall rsh sh ch1 v1 ch2 v2 a1 a2,
     adr_range a1 (Memdata.size_chunk ch1) a2 ->
     address_mapsto ch1 v1 rsh sh a1 * address_mapsto ch2 v2 rsh sh a2 |-- FF.
Proof.
 intros.
 apply res_predicates.address_mapsto_overlap.
 auto.
Qed.

Lemma field_mapsto__conflict:
  forall sh t fld v,
        field_mapsto_ sh t fld v
        * field_mapsto_ sh t fld v |-- FF.
Proof.
intros.
unfold field_mapsto_.
destruct v; normalize.
destruct t; normalize.
destruct (field_offset fld (unroll_composite_fields i0 (Tstruct i0 f a) f));
  normalize.
destruct (access_mode
    (type_of_field (unroll_composite_fields i0 (Tstruct i0 f a) f) fld)); 
  normalize.
intros.
apply address_mapsto_overlap.
split; auto.
pose proof (size_chunk_pos m); omega.
Qed.

Lemma body_fifo_empty: semax_body Vprog Gtot f_fifo_empty fifo_empty_spec.
Proof.
start_function.
name Q _Q.
name t _t.
name b _b.
unfold fifo.
match goal with |- semax _ _ _ ?P => set (Post := P) end.
normalize. intros [hd tl].
normalize.
repeat rewrite (lift1more q).
repeat rewrite (lift2more q).
replace_SEP 0 (`(field_mapsto Tsh t_struct_fifo _head) (eval_id _Q) `hd).
go_lower; subst; auto.
replace_SEP 1 (`(field_mapsto Tsh t_struct_fifo _tail) (eval_id _Q) `tl).
go_lower; subst; auto.
forward. (* t = Q->tail;*)
forward0.
make_sequential;
          eapply semax_post_flipped.
apply semax_ptr_compare' with Tsh Tsh; try reflexivity.
go_lower. subst.
 rewrite field_mapsto_isptr; normalize.
 repeat apply andp_right; try apply prop_right; auto.
 destruct (isnil contents). 
 normalize. 
 rewrite sepcon_comm. apply sepcon_derives; auto.
 eapply derives_trans; [apply field_mapsto_field_mapsto_ | ].
 apply derives_refl''.
 (* NOTE: In Coq 8.4, it is no longer necessary to unfold field_offset *)
 eapply mapsto_field_mapsto_; unfold field_offset; simpl; try reflexivity.
 rewrite align_0 by omega.
 destruct tl; inversion H. simpl. rewrite Int.add_zero. auto.
 normalize.
 unfold elemrep.
 repeat rewrite <- sepcon_assoc.
 rewrite sepcon_comm.
 apply sepcon_derives; auto.
 apply derives_refl''.
 (* NOTE: In Coq 8.4, it is no longer necessary to unfold field_offset *)
 eapply mapsto_field_mapsto_; unfold field_offset; simpl; try reflexivity.
 apply derives_trans with (field_mapsto Tsh t_struct_fifo _head Q hd * TT).
 cancel.
 apply sepcon_derives; auto.
 eapply derives_trans; [apply field_mapsto_field_mapsto_ | ].
 apply derives_refl''.
 (* NOTE: In Coq 8.4, it is no longer necessary to unfold field_offset *)
 eapply mapsto_field_mapsto_; unfold field_offset; simpl; try reflexivity.
 rewrite align_0 by omega. 
 destruct Q; inversion H; auto.
 intros. apply andp_left2. unfold Post0; apply derives_refl.
 apply extract_exists_pre; intro old.
 unfold_fold_eval_expr.
 autorewrite with subst.
 unfold Post; clear Post.
 forward. (* return b; *)
 go_lower.
  subst Q t.
   rewrite field_mapsto_isptr.
 simpl.
   repeat apply andp_right.
 apply prop_right; auto.
  normalize. simpl in H0. rewrite align_0 in H0 by omega.
 destruct (isnil contents).
 normalize. 
 destruct tl; match goal with H: Vint _ = _ |- _ => inversion H end.
 simpl in H0. rewrite zeq_true in H0. rewrite Int.add_zero in H0.
 rewrite Int.eq_true in H0. inv  H0. apply prop_right; auto.
 normalize.
 unfold elemrep.
 apply derives_trans with 
  (field_mapsto_ Tsh t_struct_elem _next ult * 
   field_mapsto Tsh t_struct_fifo _head q hd * TT); [cancel |].
 admit.  (* This is definitely provable, using lemmas similar to
                address_mapsto_overlap, but we need better lemmas
                for it. *)
apply exp_right with (hd, tl).
normalize.
cancel.
Qed.

Lemma replace_LOCAL':
 forall Q' Espec Delta P Q R c Post,
 (PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT)))) |-- LOCALx Q' (SEP (TT)) ->
 @semax Espec Delta (PROPx P (LOCALx Q' (SEPx R))) c Post ->
 @semax Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros until 1.
apply semax_pre.
unfold PROPx,LOCALx, local, lift1, lift; intro rho.
simpl.
apply derives_extract_prop; intro.
apply derives_extract_prop; intro.
unfold lift in H1.
repeat apply andp_right; auto.
apply prop_right; auto.
destruct H1.
specialize (H rho).
change SEPx with SEPx' in H.
unfold PROPx,LOCALx,SEPx', local, lift1, lift in H.
simpl in H.  rewrite sepcon_emp in H.
change (@prop mpred _ True) with (@TT mpred _) in H.
repeat rewrite andp_TT in H.
eapply derives_trans; [ | apply H].
rewrite prop_true_andp by auto.
apply prop_right; unfold lift; simpl.
split; auto.
Qed.

Lemma body_fifo_new: semax_body Vprog Gtot f_fifo_new fifo_new_spec.
Proof.
start_function.
name Q _Q.
name q 25%positive.
forward. (* q = mallocN(sizeof ( *Q)); *) 
instantiate (1:= Int.repr 8) in (Value of witness).
go_lower. normalize.
repeat apply andp_right; try apply prop_right.
compute; congruence.
compute; congruence.
cancel.
normalize.
forward. (* Q = (struct fifo * )q; *)  
replace_SEP 0 (`(memory_block Tsh (Int.repr 8)) (eval_id _Q)).
go_lower. subst. destruct q; inv TC; simpl; normalize.
apply replace_LOCAL' with (`eq (eval_id _Q) (eval_id 25%positive) :: nil).
go_lower. destruct q; inv H0; inv TC0; auto.
clear q.
rewrite memory_block_fifo.
flatten_sepcon_in_SEP.
forward. (* Q->head = NULL; *)
go_lower. apply andp_right; auto. apply prop_right; repeat split; auto.
forward.  (*  Q->tail = &(Q->head); *)
go_lower. apply andp_right; auto.
rewrite field_mapsto_isptr.
normalize.
forward. (* return Q; *)
go_lower.
  apply andp_right.
  rewrite field_mapsto_isptr; normalize.
  apply prop_right; destruct Q; inv H1; inv TC; hnf; simpl; auto.
  unfold fifo.
   destruct (@isnil (elemtype QS) nil); [ | congruence].
  apply exp_right with (nullval,Q).
  rewrite field_mapsto_isptr.  normalize.
  destruct Q; inv H1; inv TC; simpl; auto.
  unfold eval_cast; simpl. normalize.
 cancel.
Qed.

Lemma body_fifo_put: semax_body Vprog Gtot f_fifo_put fifo_put_spec.
Proof.
start_function.
name Q _Q.
name p _p.
name t _t.
normalize.
unfold fifo at 1.
normalize. intros [hd tl].
normalize.
repeat flatten_sepcon_in_SEP.
replace_SEP 1 (`(field_mapsto Tsh t_struct_fifo _tail) (eval_id _Q) `tl).
go_lower; subst. auto.
forward. (*   t = Q->tail; *)
destruct (@isnil (elemtype QS) contents).
(* CASE ONE:  isnil contents *)
subst contents.
apply semax_pre
 with (PROP  (tl=q)
   LOCAL  (`eq (eval_id queue._t) `tl; `(eq q) (eval_id _Q))
   SEP 
   (`(field_mapsto Tsh t_struct_fifo _tail) (eval_id _Q) `tl;
    `(mapsto_ Tsh (tptr t_struct_elem)) (eval_id _t);
    `(elemrep elem) (eval_id _p))).
go_lower. normalize. subst. cancel.
rewrite field_mapsto_isptr.
normalize.
eapply derives_trans; [apply field_mapsto_field_mapsto_  | ].
replace (field_mapsto_ Tsh t_struct_fifo _head Q)
   with (mapsto_ Tsh (tptr t_struct_elem) Q); auto.
eapply mapsto_field_mapsto_; try (unfold field_offset; simpl; reflexivity).
destruct Q; inv H. simpl. rewrite Int.add_zero; auto.
normalize.  subst tl.
forward.  (* *t = p *)
forward.  (* *(Q->tail) = &p->next;  *) 
go_lower. subst. rewrite elemrep_isptr at 1. normalize.
forward. (* return *)
go_lower.
 subst.
unfold fifo.
destruct (@isnil (elemtype QS) (elem::nil)) as [e3|n3]; [inv e3 | clear n3].
unfold align. simpl.
rewrite elemrep_isptr at 1.
normalize.
apply exp_right with (p, offset_val (Int.repr 8) p).
normalize.
apply exp_right with nil.
normalize. apply exp_right with p.
normalize. apply exp_right with elem.
normalize.
apply andp_right.
apply prop_right. destruct p; inv H; split; auto.
apply Int.eq_true.
cancel.
destruct p; inv H; simpl. cancel.
rewrite mapsto_isptr. normalize.
apply derives_refl'.
eapply mapsto_field_mapsto; simpl; eauto.
unfold field_offset; simpl; reflexivity.
destruct Q; simpl in TC1; try contradiction; simpl.
f_equal. 
rewrite int_add_repr_0_r. auto.
(* CASE TWO:  contents <> nil *)
focus_SEP 2.
normalize. intro prefix.
normalize. intro ult.
normalize. intro elem'.
repeat rewrite andp_assoc.
normalize.
clear n. subst.
unfold elemrep at 1.
normalize.
unfold elemtype in elem'. simpl in elem'.
destruct elem' as [a b].
simpl @fst; simpl @snd.
replace (field_mapsto_ Tsh t_struct_elem _next ult)
      with  (mapsto_ Tsh (tptr t_struct_elem)  (offset_val (Int.repr 8) ult)).
2: eapply mapsto_field_mapsto_; simpl; eauto; unfold field_offset; simpl; reflexivity.
replace_SEP 1 (`(mapsto_ Tsh (tptr t_struct_elem)) (eval_id queue._t)).
go_lower; subst; auto.
forward.  (* *t = p *)
forward.  (* *(Q->tail) = &p->next;  *) 
clear Post; go_lower. subst.
rewrite elemrep_isptr at 1. normalize.
forward. (* return; *)
go_lower.  subst.
unfold fifo.
match goal with |- context [isnil ?P] => 
  destruct (isnil P) as [e3|n3] end.
destruct prefix; inv e3. clear n3.
rewrite prop_true_andp by auto.
apply exp_right with (hd, 
     eval_cast (tptr (tptr t_struct_elem)) (tptr (tptr t_struct_elem))
     (offset_val (Int.repr (align 8 4)) (force_ptr p))).
cancel.
apply exp_right with (prefix ++ (a, b) :: nil).
apply exp_right with p.
apply exp_right with elem.
rewrite elemrep_isptr at 1.
normalize.
repeat apply andp_right; try apply prop_right; auto.
destruct p; inv H; reflexivity.
rewrite (lseg_unroll_right QS _ _  hd p).
rewrite distrib_orp_sepcon. apply orp_right2.
unfold lseg_cons_right.
rewrite sepcon_andp_prop'.
apply andp_right.
apply not_prop_right; intro.
apply ptr_eq_e in H0. subst hd.
rewrite lseg_unfold.
destruct prefix.
normalize. apply ptr_eq_e in H0; subst.
unfold elemrep.
apply derives_trans with 
  (field_mapsto Tsh t_struct_elem _a ult (Vint a) *
   field_mapsto Tsh t_struct_elem _a ult (Vint (fst elem)) * TT).
cancel.
eapply derives_trans.
apply sepcon_derives.
eapply derives_trans.
apply sepcon_derives; apply field_mapsto_field_mapsto_.
apply field_mapsto__conflict.
apply derives_refl.
rewrite FF_sepcon. auto.
normalize.
unfold elemrep.
apply derives_trans with 
 (field_mapsto Tsh t_struct_elem _next p tail *
  field_mapsto_ Tsh t_struct_elem _next p * TT).
cancel.
apply derives_trans with (FF * TT).
apply sepcon_derives; auto.
eapply derives_trans.
apply sepcon_derives.
apply field_mapsto_field_mapsto_.
apply derives_refl.
apply field_mapsto__conflict.
rewrite FF_sepcon.
apply derives_refl.
cancel.
apply exp_right with (a,b).
apply exp_right with prefix.
apply exp_right with ult.
normalize.
replace  (eval_cast (tptr t_struct_elem) (tptr t_struct_elem) p) with p
  by (destruct p; inv H; reflexivity).
replace (mapsto Tsh (tptr t_struct_elem) (offset_val (Int.repr 8) ult) p)
  with (field_mapsto Tsh t_struct_elem _next ult p).
Focus 2. symmetry.
 (* NOTE: In Coq 8.4, it is no longer necessary to unfold field_offset *)
 eapply mapsto_field_mapsto; unfold field_offset; simpl; try reflexivity.
rewrite list_cell_eq.
cancel.
Qed.

Lemma body_make_elem: semax_body Vprog Gtot f_make_elem make_elem_spec.
Proof.
start_function. rename a into a0; rename b into b0.
name a _a.
name b _b.
name p _p.
name p' 23%positive.
forward. (*  p = mallocN(sizeof ( *p));  *) 
instantiate (1:=Int.repr 12) in (Value of witness).
go_lower. subst a b. normalize.
repeat apply andp_right; try apply prop_right.
compute; congruence. reflexivity.
cancel.
normalize.
forward. (* finish the function call *)
apply semax_pre with
  (PROP  ()
   LOCAL (`(eq (Vint b0)) (eval_id _b); `(eq (Vint a0)) (eval_id _a))
   SEP  (`(field_mapsto_ Tsh t_struct_elem _a) (eval_id _p);
           `(field_mapsto_ Tsh t_struct_elem _b) (eval_id _p);
           `(field_mapsto_ Tsh t_struct_elem _next) (eval_id _p))).
go_lower; subst. normalize.
 change 12 with (sizeof t_struct_elem).
 rewrite memory_block_typed.
 simpl_typed_mapsto.
 cancel.
forward.  (*  p->a=a; *)
forward.  (*  p->b=b; *)
forward.  (* return p; *)
go_lower.
subst.
rewrite field_mapsto_isptr at 1.
normalize. destruct p; simpl in H; try contradiction.
apply andp_right.
apply prop_right.
simpl; auto.
unfold elemrep.
cancel.
Qed.

Lemma lift_elemrep_unfold:
  forall rep (p: environ -> val),
   `(elemrep rep) p = 
    (`(field_mapsto Tsh t_struct_elem _a))  p `(Vint (fst rep)) * 
     (`(field_mapsto Tsh t_struct_elem _b) p `(Vint (snd rep)) *
       `(field_mapsto_ Tsh t_struct_elem _next) p).
Proof. intros. reflexivity. Qed.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name i _i.
name j _j.
name Q _Q.
name p _p.
forward. (* Q = fifo_new(); *)
instantiate (1:= tt) in (Value of witness).
go_lower. normalize. cancel.
auto with closed.
autorewrite with subst. (* should have been done by forward *)
forward. (*  p = make_elem(1,10); *)
instantiate (1:= (Int.repr 1, Int.repr 10)) in (Value of witness).
normalize.
instantiate (1:= `(fifo nil) (eval_id _Q)::nil) in (Value of Frame).
go_lower. normalize.
auto with closed.
 autorewrite with subst. (* should have been done by forward *)
apply semax_pre with
  (EX q:val, EX p:val, 
 (PROP  ()
   LOCAL (`(eq q) (eval_id _Q); `(eq p) (eval_id _p))
   SEP  (`(elemrep (Int.repr 1, Int.repr 10)) (eval_id _p);
   (*subst _p `p0 *) (`(fifo nil) (eval_id _Q))))).
intro rho.
   normalize. apply exp_right with (eval_id _Q rho).
   normalize. apply exp_right with (eval_id _p rho).
   normalize.
apply extract_exists_pre; intro q.
apply extract_exists_pre; intro p'.
forward. (* fifo_put(Q,p);*)
 instantiate (1:= ((q,nil),(Int.repr 1, Int.repr 10))) in (Value of witness).
 unfold witness.
(*
 change (fun rho : environ =>
          local (`(eq q) (eval_id _Q)) rho &&
          `(fifo nil q) rho *
          `(elemrep (Int.repr 1, Int.repr 10)) (eval_id _p) rho)
    with (local (`(eq q) (eval_id _Q)) &&
          `(fifo nil q) *
          `(elemrep (Int.repr 1, Int.repr 10)) (eval_id _p)).
*)
 go_lower. subst p Q. normalize. cancel.
forward. (*  p = make_elem(2,20); *)
instantiate (1:= (Int.repr 2, Int.repr 20)) in (Value of witness).
go_lower. subst Q p. normalize.
instantiate (1:= `(fifo ((Int.repr 1, Int.repr 10) :: nil) q)::nil) in (Value of Frame).
unfold Frame; unfold_lift; simpl. cancel.
auto with closed.
 autorewrite with subst. (* should have been done by forward *)
apply semax_pre with
  (EX q:val, EX p:val, 
 (PROP  ()
   LOCAL (`(eq q) (eval_id _Q); `(eq p) (eval_id _p))
   SEP  (`(elemrep (Int.repr 2, Int.repr 20)) (eval_id _p);
           `(fifo ((Int.repr 1, Int.repr 10) :: nil)) (eval_id _Q)))).
unfold_lift; intro rho. normalize. apply exp_right with (eval_id _Q rho).
normalize. apply exp_right with (eval_id _p rho).
normalize.

apply extract_exists_pre; intro q2.
apply extract_exists_pre; intro p2.
forward.  (* fifo_put(Q,p); *)
 instantiate (1:= ((q2,((Int.repr 1, Int.repr 10) :: nil)),(Int.repr 2, Int.repr 20))) in (Value of witness).
 unfold witness.
 unfold_lift; go_lower. subst p Q. normalize. cancel.
simpl.
normalize.
forward. (*   p = fifo_get(Q); *)
 instantiate (1:= ((q2,((Int.repr 2, Int.repr 20) :: nil)),(Int.repr 1, Int.repr 10))) in (Value of witness).
unfold witness.
unfold_lift; go_lower. normalize. cancel.
auto with closed.
 autorewrite with subst. (* should have been done by forward *)
replace_SEP 0 (`(fifo ((Int.repr 2, Int.repr 20) :: nil) q2) *
                   `(elemrep (Int.repr 1, Int.repr 10)) (eval_id queue._p)).
go_lower.
match goal with |- semax _ (PROP () LOCAL (?Q1; ?Q2) SEP (_)) _ _ =>
  change Q1 with (`(eq q2) (eval_id _Q)); 
  change Q2 with (`(eq p2 p3))
end.
rewrite lift_elemrep_unfold.
repeat flatten_sepcon_in_SEP.
forward. (*   i = p->a;  *)
forward. (*   j = p->b; *)
forward. (*  freeN(p, sizeof( *p)); *)
instantiate (1:=tt) in (Value of witness).
simpl @fst; simpl @snd.
go_lower. normalize.
eapply derives_trans.
apply sepcon_derives.
apply field_mapsto_field_mapsto_.
apply sepcon_derives.
apply field_mapsto_field_mapsto_.
apply derives_refl.
repeat rewrite <- sepcon_assoc.
apply sepcon_derives.
change 12 with (sizeof t_struct_elem).
rewrite (eval_cast_neutral_tc_val p); eauto.
 unfold eval_cast_neutral, force_int. (* fixme *)
rewrite memory_block_typed.
clear. (* This "clear" is only needed to work around bug 2997 in Coq 8.4 *)
simpl_typed_mapsto.
cancel.
unfold Frame.
instantiate (1:= `(fifo ((Int.repr 2, Int.repr 20) :: nil) q2) :: nil).
simpl.
cancel.
forward. (* return i+j; *)
go_lower. normalize.
Qed.

(*
Notation "( e )" := (Etempvar e _) (at level 80) : C.
Notation "a = p '->' f ;" := 
   (Sset a (Efield (Ederef p _) f _)) (at level 100) : C.
Notation "p '- >' f = e ;" := 
   (Sassign (Efield (Ederef p _) f _) e) (at level 100) : C.
Notation "& e" := (Eaddrof e _) (at level 80) : C.
Notation "e - > f" := (Efield (Ederef e _) f _) (at level 82, left associativity): C.
Delimit Scope C with C.
*)

Lemma body_fifo_get: semax_body Vprog Gtot f_fifo_get fifo_get_spec.
Proof.
start_function.
name Q _Q.
name p _p.
name t _t.
name n _n.
name b _b.
unfold fifo at 1.
normalize.
intros [hd tl].
destruct (isnil (elem::contents)) as [e3|n3]; [inv e3 | clear n3].
normalize. intro prefix.
normalize. intro ult.
normalize. intro lastelem.
rewrite andp_assoc.
normalize. subst tl.
apply semax_pre with (PROP  ()
   LOCAL  (`(eq q) (eval_id _Q))
   SEP (`(lseg QS Tsh prefix hd ult); `(elemrep lastelem ult);
   `(field_mapsto Tsh t_struct_fifo _head) (eval_id _Q) `hd;
   `(field_mapsto Tsh t_struct_fifo _tail) (eval_id _Q) `(offset_val (Int.repr 8) ult))).
go_lower; subst; auto. apply andp_right; auto. apply prop_right; auto.
 forward. (*   p = Q->head; *)
 forward. (*   t=Q->tail; *)
 forward.  (*   b= t == &(p->next); *)
 go_lower. subst Q p t.
 admit.  (* To prove the first conjunct, need the rule for
               pointer-comparison (which should have been applied by
              the forward tactic, above, instead of forward_setx_closed_now.
             The prove the second conjunct (isptr hd), either prefix=nil or not,
             if it's nil, then hd=ult and isptr(ult); otherwise isptr(hd). *)
apply semax_seq with
    (PROP() LOCAL() SEP (`(fifo contents q); `(elemrep elem) (eval_id _p))).
 forward.  (*   if (t == &(p->next)) *)
 go_lower.
 subst p Q t. apply andp_right; auto.
 apply prop_right; repeat split; auto.
 apply sequential'.
 forward.
 go_lower. subst. rewrite field_mapsto_isptr.
 normalize. go_lower. subst. rewrite H2 in H1; clear b H2.
 simpl typeof in H1.
 unfold align, Zmax in H1; simpl in H1.
 assert (hd = ult).
 clear - H1.
 unfold typed_true, eval_binop, strict_bool_val, sem_cmp in H1.
 simpl in H1.
 unfold sem_cmp in H1.
 unfold tptr, classify_cmp in H1.
 simpl typeconv in H1. cbv beta iota in H1.
 forget (Int.unsigned) as uns.
 destruct ult; inv H1. 
 destruct hd; inv H0.
 destruct (Memory.Mem.valid_pointer Memory.Mem.empty b (uns (Int.add i (Int.repr 8))) &&
              Memory.Mem.valid_pointer Memory.Mem.empty b0
                (uns (Int.add i0 (Int.repr 8))))%bool; inv H1.
 destruct (zeq b b0); inv H0.
 f_equal.
  pose proof (Int.eq_spec (Int.add i (Int.repr 8)) (Int.add i0 (Int.repr 8))).
 destruct (Int.eq (Int.add i (Int.repr 8)) (Int.add i0 (Int.repr 8))).
 clear - H.
 admit.  (* straightforward *)
 simpl in H1. inv H1.
 subst ult.
 rewrite lseg_eq. normalize.
 simpl in H; inv H. 
 cancel.
 unfold fifo. apply exp_right with (hd,
    (eval_cast (tptr (tptr t_struct_elem)) (tptr (tptr t_struct_elem))
     (offset_val (Int.repr 0) (force_ptr Q)))).
 rewrite field_mapsto_isptr.
 destruct (isnil (@nil (elemtype QS))) as [e3|n3]; [clear e3 | contradiction n3; auto].
 normalize.
 apply andp_right; auto. apply prop_right.
 destruct Q; inv H. simpl. rewrite Int.add_zero.
 unfold eval_cast; reflexivity.
 cancel.
 apply TC0.
(* else clause *)
simpl typeof.
destruct prefix.
(* Case 1: prefix=nil -- contradiction *)
simpl in H. inv H.
rewrite @lseg_nil_eq.
focus_SEP 2.
normalize.
apply ptr_eq_e in H. subst ult.
simpl eval_expr.
apply semax_pre with (PROP (False) (LOCAL () SEP ())).
unfold elemrep.
go_lower. subst. rewrite H1 in H0; clear b H1. 
rewrite field_mapsto_isptr with (fld:=_a).
normalize.
elimtype False.
destruct hd; inv H.
simpl in H0.
unfold align, Zmax in H0; simpl in H0.
forget (Int.add i (Int.repr 8)) as j.
unfold typed_false, strict_bool_val in H0; simpl in H0.
unfold eval_binop in H0; simpl in H0.
unfold sem_cmp in H0; simpl in H0.
rewrite zeq_true in H0.
rewrite Int.eq_true in H0.
destruct (Memory.Mem.valid_pointer Memory.Mem.empty b (Int.unsigned j) &&
              Memory.Mem.valid_pointer Memory.Mem.empty b (Int.unsigned j))%bool;
 inv H0.
apply semax_extract_PROP. intro; contradiction.
(* case 2: prefix <> nil *)
simpl in H. inversion H; clear H; subst e contents.
 rewrite @lseg_cons_eq.
 normalize. intro h.
 normalize.
 replace_SEP 1
   (`(field_mapsto Tsh t_struct_elem _next) (eval_id _p) `h).
go_lower. subst. auto.
forward. (*  n=p->next; *)
apply sequential'.
forward. (*  Q->head=n; *)
go_lower.
subst.
unfold fifo.
destruct (isnil (prefix ++ lastelem::nil)) as [e3|n3]; [ | clear n3].
destruct prefix; inv e3.
normalize. apply exp_right with (h, offset_val (Int.repr 8) ult).
cancel.
rewrite exp_sepcon1; apply exp_right with prefix.
rewrite exp_sepcon1; apply exp_right with ult.
rewrite exp_sepcon1; apply exp_right with lastelem.
normalize.
cancel.
 rewrite list_cell_eq. unfold elemrep. cancel.

 apply field_mapsto_field_mapsto_.
 unfold update_tycon.
 forward.
 go_lower. normalize.
Qed.

Existing Instance NullExtension.Espec.

Parameter body_mallocN:
 semax_external
  (EF_external _mallocN
     {| sig_args := AST.Tint :: nil; sig_res := Some AST.Tint |}) int
  (fun n : int => PROP (4 <= Int.signed n) LOCAL (`(eq (Vint n)) (eval_id 1%positive)) SEP ())
  (fun n : int => `(memory_block Tsh n) retval).

Parameter body_freeN:
semax_external
  (EF_external _freeN
     {| sig_args := AST.Tint :: AST.Tint :: nil; sig_res := None |}) unit
  (fun _ : unit =>
      PROP() LOCAL () SEP (`(memory_block Tsh) (`force_int (eval_id 2%positive)) (eval_id 1%positive)))
 (fun _ : unit => emp).

Lemma all_funcs_correct:
  semax_func Vprog Gtot (prog_funct prog) Gtot.
Proof.
unfold Gtot, Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
apply semax_func_cons_ext; [ reflexivity | apply body_mallocN | ].
apply semax_func_cons_ext; [ reflexivity | apply body_freeN | ].
apply semax_func_cons; [ reflexivity | apply body_fifo_new | ].
apply semax_func_cons; [ reflexivity | apply body_fifo_put | ].
apply semax_func_cons; [ reflexivity | apply body_fifo_empty | ].
apply semax_func_cons; [ reflexivity | apply body_fifo_get | ].
apply semax_func_cons; [ reflexivity | apply body_make_elem | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.


