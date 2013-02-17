Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.forward.
Require Import progs.malloc_lemmas.
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
  POST [ tptr tvoid ] `(memory_block Share.top n) retval.

Definition freeN_spec :=
 DECLARE _freeN
  WITH u: unit
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]  
      PROP() LOCAL () SEP (`(memory_block Share.top) (`force_int (eval_id 2%positive)) (eval_id 1%positive))
  POST [ tvoid ]  emp.

(*
Definition elemtype := (int*int)%type.
*)

Definition elemrep (rep: elemtype QS) (p: val) : mpred :=
  field_mapsto Share.top t_struct_elem _a p (Vint (fst rep)) * 
  (field_mapsto Share.top t_struct_elem _b p (Vint (snd rep)) *
   (field_mapsto_ Share.top t_struct_elem _next p)).

Definition fifo (contents: list (elemtype QS)) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      field_mapsto Share.top t_struct_fifo _head p hd *
      field_mapsto Share.top t_struct_fifo _tail p tl *
      if isnil contents
      then (!!(tl=p) && emp)
      else (EX prefix: list (elemtype QS), EX ult:val, EX elem: elemtype QS,
              !!(tl=offset_val ult (Int.repr 8) 
                  /\ contents = prefix++(elem::nil))
            &&  (lseg QS Share.top prefix hd ult * 
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

Lemma andp_prop_gather {A}{NA: NatDed A}:
  forall P Q: Prop, andp (prop P) (prop Q) = prop (P /\ Q).
Proof.
intros. apply pred_ext; normalize.
Qed.

Lemma memory_block_fifo:
 forall e, 
   `(memory_block Share.top (Int.repr 8)) e =
  `(field_mapsto_ Share.top t_struct_fifo queue._head) e *
  `(field_mapsto_ Share.top t_struct_fifo queue._tail) e.
Proof.
 intros.
 extensionality rho.
 unfold coerce at 1; unfold lift1_C, lift1.
 change 8 with (sizeof t_struct_fifo).
 rewrite (memory_block_typed Share.top t_struct_fifo).
 simpl_typed_mapsto.
 reflexivity.
Qed.

Lemma list_cell_eq: forall sh p elem,
  list_cell QS sh p elem = 
   field_mapsto sh t_struct_elem _a p (Vint (fst elem)) * 
   field_mapsto sh t_struct_elem _b p (Vint (snd elem)). 
Proof. intros. simpl_list_cell. auto. Qed.

Lemma body_fifo_empty: semax_body Vprog Gtot f_fifo_empty fifo_empty_spec.
Proof.
start_function.
name _Q _Q.
name _t _t.
unfold fifo.
match goal with |- semax _ _ _ ?P => set (Post := P) end.
normalize. rewrite extract_exists_in_SEP.
apply extract_exists_pre; intros [hd tl].
normalize.
apply semax_pre_PQR with
  (PROP  ()
   LOCAL  (`(eq q) (eval_id queue._Q))
   SEP 
   (`(field_mapsto Share.top t_struct_fifo _head)  (eval_id queue._Q) `hd;
    `(field_mapsto Share.top t_struct_fifo _tail)  (eval_id queue._Q) `tl;
    `(if isnil contents
      then !!(tl = q) && emp
      else
       EX  prefix : list (elemtype QS),
       (EX  ult : val,
        (EX  elem : elemtype QS,
         !!(tl = offset_val ult (Int.repr 8) /\
            contents = prefix ++ elem :: nil) &&
         (lseg QS Share.top prefix hd ult * elemrep elem ult)))))).
go_lower; subst. apply andp_right. apply prop_right; auto.
 normalize.
  cancel.
unfold Post; clear Post.
forward. (* t = Q->tail;*)
forward. (* return (t == &(Q->head)); *)
go_lower.
subst _Q _t.
forget False as NOPROOF.
rewrite field_mapsto_isptr.
repeat apply andp_right.
normalize.
apply andp_right; apply prop_right; auto.
admit.  (* need to fix typechecking of pointer comparison *) 
simpl.
repeat apply andp_right.
normalize.
apply prop_right.
destruct q; inv H.
simpl.
destruct tl; inv TC; simpl.
unfold eval_binop; simpl. unfold sem_cmp; simpl.
rewrite H0. simpl. auto.
admit.  (* need to fix typechecking of pointer comparison *) 
normalize.
destruct q; inv H.
destruct (isnil contents).
normalize.
simpl. rewrite Int.add_zero.
admit.  (* need to fix typechecking of pointer comparison *) 
normalize.
clear n.
unfold elemrep.
unfold elemtype in elem.
destruct elem as [a1 b1].
simpl @fst; simpl @snd.
simpl. unfold align, Zmax; simpl. rewrite Int.add_zero.
apply derives_trans with
  (field_mapsto_ Share.top t_struct_elem _next ult *
   field_mapsto Share.top t_struct_fifo _head (Vptr b i) hd * TT); [cancel | ].
replace (field_mapsto_ Share.top t_struct_elem _next ult)
  with (mapsto_ Share.top (tptr t_struct_elem) (offset_val ult (Int.repr 8))).
2: eapply mapsto_field_mapsto_; try (simpl; reflexivity); unfold field_offset; simpl; reflexivity.
replace (field_mapsto_ Share.top t_struct_fifo _head (Vptr b i))
  with (mapsto_ Share.top (tptr t_struct_elem) (Vptr b i)).
2: eapply mapsto_field_mapsto_; try (simpl; reflexivity); unfold field_offset; simpl; try reflexivity;
   unfold align, Zmax; simpl;  rewrite Int.add_zero; reflexivity.
admit.  (* mapsto_ conflict *)
normalize.
apply exp_right with (hd, tl).
cancel.
Qed.

Lemma body_fifo_new: semax_body Vprog Gtot f_fifo_new fifo_new_spec.
Proof.
start_function.
name _Q _Q.
name _q 25%positive.
apply -> seq_assoc.
forward. (* q = mallocN(sizeof ( *Q)); *) 
instantiate (1:= Int.repr 8) in (Value of witness).
go_lower. normalize.
repeat apply andp_right; try apply prop_right.
compute; congruence.
compute; congruence.
cancel.
unfold assert.
normalize.
forward. (* Q = (struct fifo * )q; *)  
apply semax_pre_PQR with
   (PROP  ()
   LOCAL ()
   SEP  (`(memory_block Share.top (Int.repr 8)) (eval_id queue._Q))).
go_lower. subst. destruct _q; inv TC; simpl; normalize.
  eval_cast_simpl. auto.
clear _q.
rewrite memory_block_fifo.
flatten_sepcon_in_SEP.
forward. (* Q->head = NULL; *)
go_lower. apply andp_right; auto. apply prop_right; hnf; auto.
split; hnf; auto.
forward.  (*  Q->tail = &(Q->head); *)
go_lower. apply andp_right; auto.
  rewrite field_mapsto_nonnull at 1. normalize.
  apply prop_right. destruct _Q; inv H; inv TC.
    rewrite H0 in H1; inv H1. 
  hnf; reflexivity.
forward. (* return Q; *)
go_lower.
apply andp_right.
  rewrite field_mapsto_nonnull; normalize.
  apply prop_right; destruct _Q; inv H; inv TC; hnf; simpl; auto.
  rewrite H0 in H1; inv H1.
  unfold fifo.
   destruct (@isnil (elemtype QS) nil); [ | congruence].
  apply exp_right with (nullval,_Q).
  rewrite field_mapsto_nonnull.  normalize.
  destruct _Q; inv H; inv TC; simpl; auto.
  rewrite H0 in H1; inv H1. unfold eval_cast; simpl. normalize.
 cancel.
Qed.

Lemma elemrep_isptr:
  forall elem v, elemrep elem v = !! (isptr v) && elemrep elem v.
Proof.
unfold elemrep; intros.
rewrite field_mapsto_isptr at 1.
normalize.
Qed.

(*
Lemma lift_elemrep_unfold:
  forall rep (p: environ -> val),
   @coerce (val->mpred) ((environ->val)->(environ->mpred))
        (@lift1_C val mpred) (elemrep rep) p = 
    (`(field_mapsto Share.top t_struct_elem _a))  p `(Vint (fst rep)) * 
     (`(field_mapsto Share.top t_struct_elem _b) p `(Vint (fst (snd rep))) *
       `(field_mapsto_ Share.top t_struct_elem _next) p).
Proof. intros. reflexivity. Qed.
*)

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

Lemma body_fifo_put: semax_body Vprog Gtot f_fifo_put fifo_put_spec.
Proof.
start_function.
name _Q _Q.
name _p _p.
name _t _t.
normalize.
unfold fifo at 1.
normalize.
rewrite extract_exists_in_SEP.
apply extract_exists_pre; intros [hd tl].
normalize.
apply semax_pre_PQR with 
  (PROP  ()
   LOCAL  (`(eq q) (eval_id queue._Q))
   SEP 
   (`(field_mapsto Share.top t_struct_fifo _head) (eval_id queue._Q) `hd;
     `(field_mapsto Share.top t_struct_fifo _tail) (eval_id queue._Q) `tl;
      `(if isnil contents
       then !!(tl = q) && emp
       else
        EX  prefix : list (elemtype QS),
        (EX  ult : val,
         (EX  elem0 : elemtype QS,
          !!(tl = offset_val ult (Int.repr 8) /\
             contents = prefix ++ elem0 :: nil) &&
          (lseg QS Share.top prefix hd ult * elemrep elem0 ult))));
   `(elemrep elem) (eval_id queue._p))).
go_lower. subst.
 apply andp_right. apply prop_right; auto.
 cancel.
forward.
destruct (@isnil (elemtype QS) contents).
(* CASE ONE:  isnil contents *)
subst contents.
apply semax_pre_PQR
 with (PROP  (tl=q)
   LOCAL  (`eq (eval_id queue._t) `tl; `(eq q) (eval_id queue._Q))
   SEP 
   (`(field_mapsto Share.top t_struct_fifo _tail) (eval_id queue._Q) `tl;
    `(mapsto_ Share.top (tptr t_struct_elem)) (eval_id queue._t);
    `(elemrep elem) (eval_id queue._p))).
go_lower. normalizex. subst.
cancel.
rewrite field_mapsto_isptr.
normalize.
eapply derives_trans.
apply field_mapsto_field_mapsto_.
replace (field_mapsto_ Share.top t_struct_fifo _head _Q)
   with (mapsto_ Share.top (tptr t_struct_elem) _Q); auto.
eapply mapsto_field_mapsto_; try (unfold field_offset; simpl; reflexivity).
rewrite align_0 by (compute; congruence).
destruct _Q; inv H. simpl. rewrite Int.add_zero; auto.
normalizex.  subst tl.
forward.  (* *t = p *)
forward.  (* *(Q->tail) = &p->next;  *) 
go_lower. subst. rewrite elemrep_isptr at 1. normalize.
forward. (* return *)
go_lower. subst.
unfold fifo.
destruct (@isnil (elemtype QS) (elem::nil)) as [e3|n3]; [inv e3 | clear n3].
unfold align. simpl.
rewrite elemrep_isptr at 1.
normalize.
destruct _p; hnf in H; try contradiction.
simpl.
unfold eval_cast; simpl.
apply exp_right with (Vptr b i , Vptr b (Int.add i (Int.repr 8))).
cancel.
rewrite mapsto_isptr.
apply andp_right; auto.
rewrite sepcon_andp_prop.
rewrite sepcon_andp_prop'.
apply derives_extract_prop; intro.
replace (field_mapsto Share.top t_struct_fifo _head _Q (Vptr b i))
  with (mapsto Share.top (tptr t_struct_elem) _Q (Vptr b i)).
Focus 2.
eapply mapsto_field_mapsto; simpl; eauto.
unfold field_offset; simpl; reflexivity.
destruct _Q; simpl in H0; try contradiction; simpl.
rewrite align_0 by (compute; intuition).
rewrite int_add_repr_0_r. auto.
cancel.
apply exp_right with nil.
apply exp_right with (Vptr b i).
apply exp_right with elem.
normalize.
(* CASE TWO:  contents <> nil *)
focus_SEP 2%nat.
normalize. rewrite extract_exists_in_SEP. apply extract_exists_pre; intro prefix.
normalize. rewrite extract_exists_in_SEP. apply extract_exists_pre; intro ult.
normalize. rewrite extract_exists_in_SEP. apply extract_exists_pre; intro elem'.
normalize. 
rewrite andp_assoc.
do 2 rewrite move_prop_from_SEP.
flatten_sepcon_in_SEP.
normalizex.
subst. clear n.
unfold elemrep at 1.
normalize. repeat flatten_sepcon_in_SEP.
destruct elem' as [a b].
simpl @fst; simpl @snd.
replace (field_mapsto_ Share.top t_struct_elem _next ult)
      with  (mapsto_ Share.top (tptr t_struct_elem)  (offset_val ult (Int.repr 8))).
2: eapply mapsto_field_mapsto_; simpl; eauto; unfold field_offset; simpl; reflexivity.
apply semax_pre_PQR with
  (PROP  ()
   LOCAL  (`eq (eval_id queue._t) `(offset_val ult (Int.repr 8));
   `(eq q) (eval_id queue._Q))
   SEP 
   (`(mapsto_ Share.top (tptr t_struct_elem)) (eval_id queue._t);
   `(field_mapsto Share.top t_struct_elem _b ult (Vint b));
   `(field_mapsto Share.top t_struct_elem _a ult (Vint a));
   `(lseg QS Share.top prefix hd ult);
   `(field_mapsto Share.top t_struct_fifo _tail) (eval_id queue._Q)
      (eval_id queue._t);
   `(field_mapsto Share.top t_struct_fifo _head) (eval_id queue._Q) `hd;
   `(elemrep elem) (eval_id queue._p))).
go_lower. subst. normalize. cancel.
forward.  (* *t = p *)
forward.  (* *(Q->tail) = &p->next;  *) 
clear Post; go_lower. subst.
rewrite elemrep_isptr at 1. normalize.
forward. (* return; *)
go_lower. subst.
unfold fifo.
rewrite field_mapsto_isptr at 1. normalize.
destruct _Q; simpl in H; try contradiction. clear H.
rewrite elemrep_isptr at 1. normalize.
rename b0 into Q.
destruct _p; simpl in H; try contradiction. clear H.
rename b0 into p.
unfold eval_cast; simpl.
unfold align; simpl.
 apply exp_right with (hd,  Vptr p (Int.add i0 (Int.repr 8))).
match goal with |- context [isnil ?P] => 
  destruct (isnil P) as [e3|n3] end.
destruct prefix; inv e3. clear n3.
apply andp_right; auto.
cancel.
apply exp_right with (prefix ++ (a, b) :: nil).
apply exp_right with (Vptr p i0).
apply exp_right with elem.
apply andp_right.
apply prop_right; split; simpl; auto.

rewrite (lseg_unroll_right QS _ _  hd (Vptr p i0)).
rewrite distrib_orp_sepcon; apply orp_right2.
unfold lseg_cons_right.
rewrite sepcon_andp_prop'.
apply andp_right.
apply not_prop_right; intro.

apply ptr_eq_e in H. subst hd.
rewrite lseg_unfold.
destruct prefix.
normalize. apply ptr_eq_e in H; subst.
unfold elemrep.
apply derives_trans with 
  (field_mapsto Share.top t_struct_elem _a (Vptr p i0) (Vint a) *
   field_mapsto Share.top t_struct_elem _a (Vptr p i0) (Vint (fst elem)) * TT).
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
 (field_mapsto Share.top t_struct_elem _next (Vptr p i0) tail *
  field_mapsto_ Share.top t_struct_elem _next (Vptr p i0) * TT).
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
replace (mapsto Share.top (tptr t_struct_elem) (offset_val ult (Int.repr 8)) (Vptr p i0))
  with (field_mapsto Share.top t_struct_elem _next ult (Vptr p i0)).
Focus 2. symmetry; eapply mapsto_field_mapsto; simpl; try reflexivity.
               unfold field_offset; simpl; reflexivity.
cancel.

unfold list_cell.
simpl. 
 unfold withspacer, align, Zmax; simpl. 
 repeat rewrite field_mapsto_offset_zero.
rewrite sepcon_comm; auto.
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
unfold assert.
normalize.
forward. (* finish the function call *)
apply semax_pre_PQR with
  (PROP  ()
   LOCAL (`(eq (Vint b0)) (eval_id _b); `(eq (Vint a0)) (eval_id _a))
   SEP  (`(field_mapsto_ Share.top t_struct_elem _a) (eval_id _p);
           `(field_mapsto_ Share.top t_struct_elem _b) (eval_id _p);
           `(field_mapsto_ Share.top t_struct_elem _next) (eval_id _p))).
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
forward. (*  p = make_elem(1,10); *)
instantiate (1:= (Int.repr 1, Int.repr 10)) in (Value of witness).
unfold assert; normalize.
instantiate (1:= `(fifo nil) (eval_id _Q)::nil) in (Value of Frame).
go_lower. normalize.
auto with closed.
simpl.
unfold assert; normalize.
apply semax_pre_PQR with
  (EX q:val, EX p:val, 
 (PROP  ()
   LOCAL (`(eq q) (eval_id _Q); `(eq p) (eval_id _p))
   SEP  (`(elemrep (Int.repr 1, Int.repr 10)) (eval_id _p);
   subst _p `p0 (`(fifo nil) (eval_id _Q))))).
intro rho.
   normalize. apply exp_right with (eval_id _Q rho).
   normalize. apply exp_right with (eval_id _p rho).
   normalize.
apply extract_exists_pre; intro q.
apply extract_exists_pre; intro p'.
forward. (* fifo_put(Q,p);*)
 instantiate (1:= ((q,nil),(Int.repr 1, Int.repr 10))) in (Value of witness).
 unfold witness.
 change (fun rho : environ =>
          local (`(eq q) (eval_id _Q)) rho &&
          `(fifo nil q) rho *
          `(elemrep (Int.repr 1, Int.repr 10)) (eval_id _p) rho)
    with (local (`(eq q) (eval_id _Q)) &&
          `(fifo nil q) *
          `(elemrep (Int.repr 1, Int.repr 10)) (eval_id _p)).
 normalize.
 go_lower. subst p Q. normalize. cancel.
simpl.
forward. (*  p = make_elem(2,20); *)
instantiate (1:= (Int.repr 2, Int.repr 20)) in (Value of witness).
go_lower. subst Q p. normalize.
instantiate (1:= `(fifo ((Int.repr 1, Int.repr 10) :: nil) q)::nil) in (Value of Frame).
unfold Frame; simpl. cancel.
auto with closed.
simpl.
unfold assert; normalize.
apply semax_pre_PQR with
  (EX q:val, EX p:val, 
 (PROP  ()
   LOCAL (`(eq q) (eval_id _Q); `(eq p) (eval_id _p))
   SEP  (`(elemrep (Int.repr 2, Int.repr 20)) (eval_id _p);
           `(fifo ((Int.repr 1, Int.repr 10) :: nil)) (eval_id _Q)))).
intro rho. normalize. apply exp_right with (eval_id _Q rho).
normalize. apply exp_right with (eval_id _p rho).
normalize.
apply extract_exists_pre; intro q2.
apply extract_exists_pre; intro p2.
forward.  (* fifo_put(Q,p); *)
 instantiate (1:= ((q2,((Int.repr 1, Int.repr 10) :: nil)),(Int.repr 2, Int.repr 20))) in (Value of witness).
 unfold witness.
 go_lower. subst p Q. normalize. cancel.
simpl.
unfold assert; normalize.
forward. (*   p = fifo_get(Q); *)
 instantiate (1:= ((q2,((Int.repr 2, Int.repr 20) :: nil)),(Int.repr 1, Int.repr 10))) in (Value of witness).
unfold witness.
go_lower. normalize. cancel.
auto with closed.
simpl.
normalize.
change  (@coerce assert ((environ -> environ) -> environ -> mpred)
                 (lift1_C environ mpred) _ _)
with  (`(fifo ((Int.repr 2, Int.repr 20) :: nil) q2) *
           @coerce _ _ (lift1_C environ mpred)
              (`(elemrep (Int.repr 1, Int.repr 10)) retval)
                 (get_result1 queue._p)).
normalize.

Lemma lift_elemrep_unfold:
  forall rep (p: environ -> val),
   @coerce (val->mpred) ((environ->val)->(environ->mpred))
        (@lift1_C val mpred) (elemrep rep) p = 
    (`(field_mapsto Share.top t_struct_elem _a))  p `(Vint (fst rep)) * 
     (`(field_mapsto Share.top t_struct_elem _b) p `(Vint (snd rep)) *
       `(field_mapsto_ Share.top t_struct_elem _next) p).
Proof. intros. reflexivity. Qed.

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
rewrite memory_block_typed.
simpl_typed_mapsto.
eval_cast_simpl.
simpl.
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
unfold fifo at 1.
normalizex.
rewrite extract_exists_in_SEP.
apply extract_exists_pre; intros [hd tl].
destruct (isnil (elem::contents)) as [e3|n3]; [inv e3 | clear n3].
apply semax_pre_PQR with
 (EX  prefix : list (elemtype QS),
   EX  ult : val,
    EX  elem0 : elemtype QS,
     PROP (tl = offset_val ult (Int.repr 8);
            elem :: contents = prefix ++ elem0 :: nil)
      LOCAL (`(eq q) (eval_id _Q))
      SEP (`(field_mapsto Share.top t_struct_fifo _head) (eval_id _Q) `hd;
           `(field_mapsto Share.top t_struct_fifo _tail) (eval_id _Q) `tl;
            `(lseg QS Share.top prefix hd ult);
             `(elemrep elem0 ult))).
 go_lower2. normalize. intro lastelem. intro.
  apply exp_right with prefix. apply exp_right with ult. apply exp_right with lastelem.
  change SEPx with SEPx'. unfold PROPx, LOCALx, SEPx'; simpl; normalize.
 subst q. cancel.
 apply extract_exists_pre; intro prefix.
 apply extract_exists_pre; intro ult.
 apply extract_exists_pre; intro lastelem.
 normalizex.
 subst tl.
 forward. (*   p = Q->head; *)
 forward. (*   t=Q->tail; *)
 apply semax_seq with
    (`(fifo contents q) * `(elemrep elem) (eval_id _p)).
 forward1.  (*   if (t == &(p->next)) *)
 go_lower.
 admit.  (* need to fix typechecking of pointer comparison *) 
 apply sequential'.
 forward.
 go_lower. subst. rewrite field_mapsto_isptr.
 normalize.
 normalize. go_lower. subst.
 simpl typeof in H1.
 unfold align, Zmax; simpl.
 assert (hd = ult).
 clear - H1.
 unfold typed_true, eval_binop, strict_bool_val, sem_cmp in H1.
 simpl in H1. unfold align, Zmax in H1; simpl in H1.
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
 rewrite lseg_eq. normalize. simpl in H0.
 inv H0. 
 cancel.
 unfold fifo. apply exp_right with (hd,
    (eval_cast (tptr (tptr t_struct_elem)) (tptr (tptr t_struct_elem))
     (eval_struct_field 0 (force_ptr Q)))).
 rewrite field_mapsto_isptr.
 destruct (isnil (@nil (elemtype QS))) as [e3|n3]; [clear e3 | contradiction n3; auto].
 normalize.
 apply andp_right; auto. apply prop_right.
 destruct Q; inv H. simpl. rewrite Int.add_zero.
 unfold eval_cast; reflexivity.
 apply andp_right. apply prop_right; auto.
 cancel.
 apply TC0.
(* else clause *)
simpl typeof.
destruct prefix.
(* Case 1: prefix=nil -- contradiction *)
simpl in H0. inv H0.
rewrite @lseg_nil_eq.
focus_SEP 2%nat.
normalize.
apply semax_extract_PROP; intro.
apply ptr_eq_e in H. subst ult.
simpl eval_expr.
apply semax_pre_PQR with (PROP (False) (LOCAL () SEP ())).
unfold elemrep.
go_lower. subst. 
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
simpl in H0. inversion H0; clear H0; subst e contents.
 rewrite @lseg_cons_eq.
 normalize.
 focus_SEP 2%nat.
 rewrite extract_exists_in_SEP.
 apply extract_exists_pre; intro h.
 rewrite move_prop_from_SEP.
 apply semax_extract_PROP; intro.
 normalize.
 repeat flatten_sepcon_in_SEP.
 apply semax_extract_PROP; intro.
replace_in_pre 
   (@coerce mpred (environ -> mpred) (lift0_C mpred)
                    (field_mapsto Share.top t_struct_elem _next hd h))
   (`(field_mapsto Share.top t_struct_elem _next) (eval_id _p) `h).
apply go_lower_lem9.
go_lower. subst. apply andp_right; auto. apply prop_right; split; auto.
forward. (*  n=p->next; *)
apply sequential'.
forward. (*  Q->head=n; *)
go_lower.
subst.
unfold fifo.
destruct (isnil (prefix ++ lastelem::nil)) as [e3|n3]; [ | clear n3].
destruct prefix; inv e3.
normalize. apply exp_right with (h, offset_val ult (Int.repr 8)).
cancel.
rewrite exp_sepcon1; apply exp_right with prefix.
rewrite exp_sepcon1; apply exp_right with ult.
rewrite exp_sepcon1; apply exp_right with lastelem.
normalize.
cancel.
 rewrite list_cell_eq. unfold elemrep. cancel.
 apply field_mapsto_field_mapsto_.
 unfold update_tycon.
 canonicalize_pre.
 forward.
 set (Delta' := join_tycon Delta (initialized _n Delta)).
 go_lower. normalize. cancel.
Qed.

Parameter body_mallocN:
 semax_external
  (EF_external _mallocN
     {| sig_args := AST.Tint :: nil; sig_res := Some AST.Tint |}) int
  (fun n : int => PROP (4 <= Int.signed n) LOCAL (`(eq (Vint n)) (eval_id 1%positive)) SEP ())
  (fun n : int => `(memory_block Share.top n) retval).

Parameter body_freeN:
semax_external
  (EF_external _freeN
     {| sig_args := AST.Tint :: AST.Tint :: nil; sig_res := None |}) unit
  (fun _ : unit =>
      PROP() LOCAL () SEP (`(memory_block Share.top) (`force_int (eval_id 2%positive)) (eval_id 1%positive)))
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


