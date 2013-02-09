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

Instance QS: listspec _struct_elem _next.
Proof.
apply mk_listspec with  (Fcons _a tint
       (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil))).
simpl. reflexivity.
Defined.

Lemma wand_ponens {A}{NA: NatDed A}{SA: SepLog A}:
  forall P Q, P * (P -* Q) |-- Q.
Admitted.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: int
  PRE [ 1%positive OF tint]  (!! (4 <= Int.signed n) &&
                             local (`(eq (Vint n)) (eval_id 1%positive))) && emp
  POST [ tptr tvoid ]  `(memory_block Share.top n) retval.

Definition freeN_spec :=
 DECLARE _freeN
  WITH u: unit
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]  
         `(memory_block Share.top) (`force_int (eval_id 2%positive)) (eval_id 1%positive)
  POST [ tvoid ]  emp.

Definition elemtype := (int*(int*(unit*unit)))%type.

Definition elemrep (rep: elemtype) (p: val) : mpred :=
  field_mapsto Share.top t_struct_elem _a p (Vint (fst rep)) * 
  (field_mapsto Share.top t_struct_elem _b p (Vint (fst (snd rep))) *
   (field_storable Share.top t_struct_elem _next p)).

Definition fifo (contents: list elemtype) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      field_mapsto Share.top t_struct_fifo _head p hd *
      field_mapsto Share.top t_struct_fifo _tail p tl *
      if isnil contents
      then (!!(tl=p) && emp)
      else (EX prefix: list elemtype, EX ult:val, EX elem:elemtype,
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
  WITH q: val, contents: list elemtype, elem: elemtype
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
            local (`(eq q) (eval_id _Q)) && 
           `(fifo contents q) * `(elemrep elem) (eval_id _p)
  POST [ tvoid ] `(fifo (contents++(elem :: nil)) q).

Definition fifo_empty_spec :=
 DECLARE _fifo_empty
  WITH q: val, contents: list elemtype
  PRE  [ _Q OF (tptr t_struct_fifo) ]
     local (`(eq q) (eval_id _Q)) &&`(fifo contents q)
  POST [ tint ] local (`(eq (if isnil contents then Vtrue else Vfalse)) retval)
                        && `(fifo (contents) q).

Definition fifo_get_spec :=
 DECLARE _fifo_get
  WITH q: val, contents: list elemtype, elem: elemtype
  PRE  [ _Q OF (tptr t_struct_fifo) ]
            local (`(eq q) (eval_id _Q)) && `(fifo (elem :: contents) q) 
  POST [ (tptr t_struct_elem) ] `(fifo contents q) * `(elemrep elem) retval.

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH a: int, b: int
  PRE  [ _a OF tint, _b OF tint ] 
            local (`(eq (Vint a)) (eval_id _a))
       && local (`(eq (Vint b)) (eval_id _b))
       && emp
  POST [ (tptr t_struct_elem) ] `(elemrep (a,(b,(tt,tt)))) retval.

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


Definition storable (sh: share) (t: type) (v: val) :=
 EX v':val, mapsto sh t v v'.

Lemma mapsto_storable: forall sh t v v',
   mapsto sh t v v' |-- storable sh t v.
Proof. unfold storable; intros. apply exp_right with v'; auto.
Qed.

Lemma andp_prop_gather {A}{NA: NatDed A}:
  forall P Q: Prop, andp (prop P) (prop Q) = prop (P /\ Q).
Proof.
intros. apply pred_ext; normalize.
Qed.

Lemma memory_block_fifo:
 forall e, 
   `(memory_block Share.top (Int.repr 8)) e =
  `(field_storable Share.top t_struct_fifo queue._head) e *
  `(field_storable Share.top t_struct_fifo queue._tail) e.
Proof.
 intros.
 extensionality rho.
 unfold coerce at 1; unfold lift1_C, lift1.
 change 8 with (sizeof t_struct_fifo).
 rewrite (malloc_assert t_struct_fifo).
 simpl_malloc_assertion.
 reflexivity.
Qed.

Lemma lift1_lift1_retval {A}: forall i (P: val -> A),
lift1 (lift1 P retval) (get_result1 i) = lift1 P (eval_id i).
Proof. intros.  extensionality rho. 
  unfold lift1.  f_equal. 
Qed.

Lemma lift1_lift1_retvalC {A}: forall i (P: val -> A),
`(`P retval) (get_result1 i) = @coerce _ _ (lift1_C _ _) P (eval_id i).
Proof. intros.  extensionality rho.
  unfold coerce, lift1_C, lift1. 
  f_equal.  
Qed.


Lemma lift0_exp {A}{NA: NatDed A}:
  forall (B: Type) (f: B -> A), lift0 (exp f) = EX x:B, lift0 (f x).
Proof. intros; extensionality rho; unfold lift0. simpl.
f_equal. extensionality b; auto.
Qed.

Lemma lift0C_exp {A}{NA: NatDed A}:
  forall (B: Type) (f: B -> A), `(exp f) = EX x:B, `(f x).
Proof. apply lift0_exp. Qed. 
Hint Rewrite @lift0_exp @lift0C_exp : normalize.

Lemma lift0C_andp {A}{NA: NatDed A}:
 forall P Q, 
  (@coerce A (environ -> A) (lift0_C A) (@andp A NA P Q)) =
  andp (`P) (`Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.


Lemma lift0C_prop {A}{NA: NatDed A}:
 forall P, @coerce A (environ -> A) (lift0_C A) (!! P) = !!P.
Proof. intros. extensionality rho; reflexivity. Qed.

Lemma lift0C_sepcon {A}{NA: NatDed A}{SA: SepLog A}:
 forall P Q, 
  (@coerce A (environ -> A) (lift0_C A) (@sepcon A NA SA P Q)) =
  sepcon (`P) (`Q).
Proof.
intros. extensionality rho. reflexivity.
Qed.
Hint Rewrite @lift0C_andp @lift0C_prop @lift0C_sepcon : normalize.

Lemma lift0C_later {A}{NA: NatDed A}{IA: Indir A}:
  forall P:A, 
   @coerce A (environ -> A) (lift0_C A) (@later A NA IA P) =
      @later (environ->A) (@LiftNatDed environ A NA) 
                (@LiftIndir environ A NA IA)
             (@coerce A (environ->A) _ P).
Proof. intros. reflexivity. Qed.

Lemma lift1C_lift0C:
  forall {A}{J: A}{K: environ -> environ},
     (@coerce (environ -> A) ((environ -> environ) -> (environ -> A))
            (lift1_C environ A)
                 (@coerce A (environ -> A) (lift0_C A)  J) K) = `J.
Proof. intros. extensionality rho. reflexivity. Qed.

Lemma list_cell_elemrep:
  forall p elem, 
  field_storable Share.top t_struct_elem _next p * list_cell QS Share.top p elem 
    |-- elemrep elem p.
  intros.
  unfold list_cell, elemrep.
  simpl in elem.
  destruct elem as [a [b [[] []]]].
  simpl @fst; simpl @snd.
  SearchAbout wand.
 eapply derives_trans; [apply wand_ponens | ].
 simpl_malloc_assertion.
 fold t_struct_elem.
 cancel.
Qed.

Lemma body_fifo_empty: semax_body Vprog Gtot f_fifo_empty fifo_empty_spec.
Proof.
start_function.
name _Q _Q.
name _t _t.
unfold fifo.
match goal with |- semax _ _ _ ?P => set (Post := P) end.
normalize. rewrite extract_exists_in_SEP.
apply extract_exists_pre; intros [hd tl].
repeat rewrite lift0C_sepcon.
apply semax_pre_PQR with
  (PROP  ()
   LOCAL  (`(eq q) (eval_id queue._Q))
   SEP 
   (`(field_mapsto Share.top t_struct_fifo _head)  (eval_id queue._Q) `hd;
    `(field_mapsto Share.top t_struct_fifo _tail)  (eval_id queue._Q) `tl;
    `(if isnil contents
      then !!(tl = q) && emp
      else
       EX  prefix : list elemtype,
       (EX  ult : val,
        (EX  elem : elemtype,
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
rewrite sepcon_emp.
repeat apply andp_right.
normalize.
apply prop_right.
destruct q; inv H0.
simpl.
destruct tl; inv TC; simpl.
unfold eval_binop; simpl. unfold sem_cmp; simpl.
rewrite H1. simpl. auto.
admit.  (* need to fix typechecking of pointer comparison *) 
normalize.
destruct q; inv H0.
destruct (isnil contents).
normalize.
simpl. rewrite Int.add_zero.
admit.  (* need to fix typechecking of pointer comparison *) 
normalize.
clear n.
unfold elemrep.
unfold elemtype in elem.
destruct elem as [a1 [b1 [[] []]]].
simpl @fst; simpl @snd.
apply derives_trans with
  (field_storable Share.top t_struct_elem _next ult *
   field_mapsto Share.top t_struct_fifo _head (Vptr b i) hd * TT); [cancel | ].

replace (field_storable Share.top t_struct_elem _next ult)
  with (storable Share.top (tptr t_struct_elem) (offset_val ult (Int.repr 8))).
Focus 2.
eapply mapsto_field_storable; try (simpl; reflexivity). unfold field_offset; simpl; reflexivity.
eapply derives_trans. eapply sepcon_derives; [ | apply derives_refl].
apply sepcon_derives. apply derives_refl. apply field_mapsto_storable.
replace (field_storable Share.top t_struct_fifo _head (Vptr b i))
  with (storable Share.top (tptr t_struct_elem) (Vptr b i)).
Focus 2.
eapply mapsto_field_storable; try (simpl; reflexivity). unfold field_offset; simpl; reflexivity.
unfold align, Zmax; simpl.  rewrite Int.add_zero. reflexivity.
admit.  (* should be be provable, in principle *)
apply exp_right with (hd,tl).
normalize.
cancel.
Qed.

Lemma body_fifo_new: semax_body Vprog Gtot f_fifo_new fifo_new_spec.
Proof.
start_function.
name _Q _Q.
name _q 23%positive.
forward. (* q = mallocN(sizeof ( *Q)); *) 
instantiate (1:= Int.repr 8) in (Value of witness).
go_lower. rewrite andp_prop_gather. normalize.
repeat apply andp_right; try apply prop_right.
compute; congruence.
compute; congruence.
cancel.
normalize.
unfold assert.
rewrite lift1_lift1_retvalC.
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
   destruct (@isnil elemtype nil); [ | congruence].
  apply exp_right with (nullval,_Q).
  rewrite field_mapsto_nonnull.  normalize.
  destruct _Q; inv H; inv TC; simpl; auto.
  rewrite H0 in H1; inv H1. unfold eval_cast; simpl. normalize.
 cancel.
Qed.

Lemma elemrep_isptr:
  forall elem v, elemrep elem v = !! (denote_tc_isptr v) && elemrep elem v.
Proof.
unfold elemrep; intros.
rewrite field_mapsto_isptr at 1.
normalize.
Qed.

Lemma lift_elemrep_unfold:
  forall rep (p: environ -> val),
   @coerce (val->mpred) ((environ->val)->(environ->mpred))
        (@lift1_C val mpred) (elemrep rep) p = 
    (`(field_mapsto Share.top t_struct_elem _a))  p `(Vint (fst rep)) * 
     (`(field_mapsto Share.top t_struct_elem _b) p `(Vint (fst (snd rep))) *
       `(field_storable Share.top t_struct_elem _next) p).
Proof. intros. reflexivity. Qed.

Lemma address_mapsto_overlap:
  forall rsh sh ch1 v1 ch2 v2 a1 a2,
     adr_range a1 (Memdata.size_chunk ch1) a2 ->
     address_mapsto ch1 v1 rsh sh a1 * address_mapsto ch2 v2 rsh sh a2 |-- FF.
Proof.
 intros.
 apply res_predicates.address_mapsto_overlap.
 auto.
Qed.

Lemma field_storable_conflict:
  forall sh t fld v,
        field_storable sh t fld v
        * field_storable sh t fld v |-- FF.
Proof.
intros.
unfold field_storable.
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
destruct p as [q contents].
normalize. flatten_sepcon_in_SEP.
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
        EX  prefix : list elemtype,
        (EX  ult : val,
         (EX  elem0 : elemtype,
          !!(tl = offset_val ult (Int.repr 8) /\
             contents = prefix ++ elem0 :: nil) &&
          (lseg QS Share.top prefix hd ult * elemrep elem0 ult))));
   `(elemrep elem) (eval_id queue._p))).
go_lower. subst.
 apply andp_right. apply prop_right; auto.
 cancel.
forward.
destruct (@isnil elemtype contents).
(* CASE ONE:  isnil contents *)
subst contents.
apply semax_pre_PQR
 with (PROP  (tl=q)
   LOCAL  (`eq (eval_id queue._t) `tl; `(eq q) (eval_id queue._Q))
   SEP 
   (`(field_mapsto Share.top t_struct_fifo _tail) (eval_id queue._Q) `tl;
    (EX x:val, `(mapsto Share.top (tptr t_struct_elem)) (eval_id queue._t) `x);
    `(elemrep elem) (eval_id queue._p))).
go_lower. normalizex. subst. apply exp_right with hd.
normalize. cancel.
rewrite field_mapsto_nonnull. 
erewrite field_mapsto_typecheck_val by reflexivity.
normalize. simpl in H0.
replace (field_mapsto Share.top t_struct_fifo _head _Q hd)
  with (mapsto Share.top (tptr t_struct_elem) _Q hd);  auto.
eapply mapsto_field_mapsto; try (simpl; reflexivity).
unfold field_offset; simpl. reflexivity.
rewrite align_0.
destruct _Q; inv TC1; inv H.  rewrite H2 in H3; inv H3.
simpl; normalize. 
compute; intuition.
assumption.
normalizex.  subst tl. intro x.
forward.  (* *t = p *)
forward.  (* *(Q->tail) = &p->next;  *) 
go_lower. subst. rewrite elemrep_isptr at 1. normalize.
forward. (* return *)
go_lower. subst.
unfold fifo.
destruct (@isnil elemtype (elem::nil)) as [e3|n3]; [inv e3 | clear n3].
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
rewrite lift0C_andp.  rewrite lift0C_prop.
rewrite move_prop_from_SEP.
normalizex.
destruct H.
subst. clear n.
unfold elemrep at 1.
repeat rewrite @lift0C_sepcon.
destruct elem' as [a [b [u1 u2]]]; destruct u1; destruct u2.
simpl @fst; simpl @snd.
focus_SEP 1%nat.
rewrite flatten_sepcon_in_SEP.
focus_SEP 1%nat.
rewrite flatten_sepcon_in_SEP.
replace (field_storable Share.top t_struct_elem _next ult)
     with (EX v2:val, mapsto Share.top (tptr t_struct_elem) (offset_val ult (Int.repr 8)) v2).
2: eapply mapsto_field_storable; simpl; eauto; unfold field_offset; simpl; reflexivity.
focus_SEP 1%nat.
normalize. rewrite extract_exists_in_SEP. apply extract_exists_pre; intro v2.
apply semax_pre_PQR with
  (PROP  ()
   LOCAL  (`eq (eval_id queue._t) `(offset_val ult (Int.repr 8));
   `(eq q) (eval_id queue._Q))
   SEP 
   (`(mapsto Share.top (tptr t_struct_elem)) (eval_id queue._t) `v2;
   `(field_mapsto Share.top t_struct_elem _b ult (Vint b));
   `(field_mapsto Share.top t_struct_elem _a ult (Vint a));
   `(lseg QS Share.top prefix hd ult);
   `(field_mapsto Share.top t_struct_fifo _tail) (eval_id queue._Q)
      (eval_id queue._t);
   `(field_mapsto Share.top t_struct_fifo _head) (eval_id queue._Q) `hd;
   `(elemrep elem) (eval_id queue._p))).
go_lower. subst. normalize.
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
match goal with |- context [isnil ?P] => destruct (isnil P) end.
destruct prefix; inv e. clear n.
apply andp_right; auto.
cancel.
apply exp_right with (prefix ++ (a, (b, (tt, tt))) :: nil).
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
apply sepcon_derives; apply field_mapsto_storable.
apply field_storable_conflict.
apply derives_refl.
rewrite FF_sepcon. auto.
normalize.
change list_struct with t_struct_elem.
unfold elemrep.
apply derives_trans with 
 (field_mapsto Share.top t_struct_elem _next (Vptr p i0) tail *
  field_storable Share.top t_struct_elem _next (Vptr p i0) * TT).
cancel.
apply derives_trans with (FF * TT).
apply sepcon_derives; auto.
eapply derives_trans.
apply sepcon_derives.
apply field_mapsto_storable.
apply derives_refl.
apply field_storable_conflict.
rewrite FF_sepcon.
apply derives_refl.
cancel.
apply exp_right with (a,(b,(tt,tt))).
apply exp_right with prefix.
apply exp_right with ult.
change list_struct with t_struct_elem.
normalize.
replace (mapsto Share.top (tptr t_struct_elem) (offset_val ult (Int.repr 8)) (Vptr p i0))
  with (field_mapsto Share.top t_struct_elem _next ult (Vptr p i0)).
Focus 2. symmetry; eapply mapsto_field_mapsto; simpl; try reflexivity.
               unfold field_offset; simpl; reflexivity.
cancel.

unfold list_cell.
apply -> (@wand_sepcon_adjoint mpred _ _).
simpl_malloc_assertion.
fold t_struct_elem.
cancel.
Qed.

Lemma body_make_elem: semax_body Vprog Gtot f_make_elem make_elem_spec.
Proof.
start_function.
name _a _a.
name _b _b.
name _p _p.
name _p' 23%positive.
forward. (*  p = mallocN(sizeof ( *p));  *) 
instantiate (1:=Int.repr 12) in (Value of witness).
go_lower. normalize.
rewrite andp_prop_gather.
rewrite sepcon_andp_prop'.
apply andp_right. apply prop_right; split; auto. 
compute; congruence.
normalize.
instantiate (1:=nil) in (Value of Frame).
unfold Frame; simpl; normalize.
normalize.
unfold assert; rewrite lift1_lift1_retvalC .
forward.
apply semax_pre_PQR with
  (PROP  ()
   LOCAL (`(eq (Vint b)) (eval_id queue._b); `(eq (Vint a)) (eval_id queue._a))
   SEP  (`(field_storable Share.top t_struct_elem queue._a) (eval_id queue._p);
           `(field_storable Share.top t_struct_elem queue._b) (eval_id queue._p);
           `(field_storable Share.top t_struct_elem queue._next) (eval_id queue._p))).
go_lower; subst. normalize.
 change 12 with (sizeof t_struct_elem).
 rewrite malloc_assert.
 simpl_malloc_assertion.
 cancel.
forward.
forward.
forward.
go_lower.
subst.
rewrite field_mapsto_isptr at 1.
normalize. destruct _p; simpl in H; try contradiction.
apply andp_right.
apply prop_right.
simpl; auto.
unfold elemrep.
simpl @fst; simpl @snd.
normalize.
unfold eval_cast. simpl force_val.
cancel.
Qed.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name _i _i.
name _j _j.
name _Q _Q.
name _p _p.
forward. (* Q = fifo_new(); *)
instantiate (1:= tt) in (Value of witness).
go_lower. normalize. cancel.
auto with closed.
forward. (*  p = make_elem(1,10); *)
instantiate (1:= (Int.repr 1, Int.repr 10)) in (Value of witness).
unfold assert; rewrite lift1_lift1_retvalC.
instantiate (1:= `(fifo nil) (eval_id queue._Q)::nil) in (Value of Frame).
go_lower. normalize.
auto with closed.
simpl.
unfold assert; rewrite lift1_lift1_retvalC.
normalize.
apply semax_pre_PQR with
  (EX q:val, EX p:val, 
 (PROP  ()
   LOCAL (`(eq q) (eval_id queue._Q); `(eq p) (eval_id queue._p))
   SEP  (`(elemrep (Int.repr 1, (Int.repr 10, (tt, tt)))) (eval_id queue._p);
   subst queue._p `_p0 (`(fifo nil) (eval_id queue._Q))))).
intro rho. normalize. apply exp_right with (eval_id queue._Q rho).
normalize. apply exp_right with (eval_id queue._p rho).
normalize.
apply extract_exists_pre; intro q.
apply extract_exists_pre; intro p.
forward. (* fifo_put(Q,p);*)
 instantiate (1:= ((q,nil),(Int.repr 1, (Int.repr 10, (tt,tt))))) in (Value of witness).
 unfold witness.
 change (fun rho : environ =>
          local (`(eq q) (eval_id queue._Q)) rho &&
          `(fifo nil q) rho *
          `(elemrep (Int.repr 1, (Int.repr 10, (tt,tt)))) (eval_id queue._p) rho)
    with (local (`(eq q) (eval_id queue._Q)) &&
          `(fifo nil q) *
          `(elemrep (Int.repr 1, (Int.repr 10, (tt,tt)))) (eval_id queue._p)).
 normalize.
 go_lower. subst _p _Q. normalize.
 cancel.
match goal with |- context [coerce ?A  (make_args nil nil)] =>
  remember A as foo
end.
simpl in Heqfoo. subst foo.
forward. (*  p = make_elem(2,20); *)
instantiate (1:= (Int.repr 2, Int.repr 20)) in (Value of witness).
go_lower. subst _Q _p. normalize.
instantiate (1:= `(fifo ((Int.repr 1, (Int.repr 10, (tt, tt))) :: nil) q)::nil) in (Value of Frame).
unfold Frame; simpl. cancel.
auto with closed.
simpl.
unfold assert; rewrite lift1_lift1_retvalC.
normalize.
apply semax_pre_PQR with
  (EX q:val, EX p:val, 
 (PROP  ()
   LOCAL (`(eq q) (eval_id queue._Q); `(eq p) (eval_id queue._p))
   SEP  (`(elemrep (Int.repr 2, (Int.repr 20, (tt, tt)))) (eval_id queue._p);
           `(fifo ((Int.repr 1, (Int.repr 10, (tt, tt))) :: nil)) (eval_id queue._Q)))).
intro rho. normalize. apply exp_right with (eval_id queue._Q rho).
normalize. apply exp_right with (eval_id queue._p rho).
normalize.
apply extract_exists_pre; intro q1.
apply extract_exists_pre; intro p1.
forward.  (* fifo_put(Q,p); *)
 instantiate (1:= ((q1,((Int.repr 1, (Int.repr 10, (tt, tt))) :: nil)),(Int.repr 2, (Int.repr 20, (tt,tt))))) in (Value of witness).
 unfold witness.
 go_lower. subst _p _Q. normalize. cancel.
match goal with |- context [coerce ?A  (make_args nil nil)] =>
  remember A as foo
end.
simpl in Heqfoo. subst foo.
unfold assert; rewrite @lift1C_lift0C.
forward. (*   p = fifo_get(Q); *)
 instantiate (1:= ((q1,((Int.repr 2, (Int.repr 20, (tt, tt))) :: nil)),(Int.repr 1, (Int.repr 10, (tt,tt))))) in (Value of witness).
unfold witness.
go_lower. normalize. cancel.
auto with closed.
cbv iota beta.
simpl map.
normalize.
change  (@coerce assert ((environ -> environ) -> environ -> mpred)
                 (lift1_C environ mpred)
                 (fun rho : environ =>
                  @sepcon mpred Nveric Sveric
                    (@coerce mpred assert (lift0_C mpred)
                       (fifo
                          (@cons
                             (prod Int.int (prod Int.int (prod unit unit)))
                             (@pair Int.int (prod Int.int (prod unit unit))
                                (Int.repr (Zpos (xO xH)))
                                (@pair Int.int (prod unit unit)
                                   (Int.repr (Zpos (xO (xO (xI (xO xH))))))
                                   (@pair unit unit tt tt)))
                             (@nil
                                (prod Int.int (prod Int.int (prod unit unit)))))
                          q1) rho)
                    (@coerce (val -> mpred) ((environ -> val) -> assert)
                       (lift1_C val mpred)
                       (elemrep
                          (@pair Int.int (prod Int.int (prod unit unit))
                             (Int.repr (Zpos xH))
                             (@pair Int.int (prod unit unit)
                                (Int.repr (Zpos (xO (xI (xO xH)))))
                                (@pair unit unit tt tt)))) retval rho))
                 (get_result1 queue._p))
with  (`(fifo ((Int.repr 2, (Int.repr 20, (tt, tt))) :: nil) q1) *
           @coerce assert _ (lift1_C environ mpred)
              (`(elemrep (Int.repr 1, (Int.repr 10, (tt, tt)))) retval)
                 (get_result1 queue._p)).
unfold assert; rewrite lift1_lift1_retvalC.
rewrite lift_elemrep_unfold.
flatten_sepcon_in_SEP.
flatten_sepcon_in_SEP.
flatten_sepcon_in_SEP.
forward. (*   i = p->a;  *)
forward. (*   j = p->b; *)
forward. (*  freeN(p, sizeof( *p)); *)
instantiate (1:=tt) in (Value of witness).
simpl @fst; simpl @snd.
go_lower. normalize.
eapply derives_trans.
apply sepcon_derives.
apply field_mapsto_storable.
apply sepcon_derives.
apply field_mapsto_storable.
apply derives_refl.
repeat rewrite <- sepcon_assoc.
apply sepcon_derives.
change 12 with (sizeof t_struct_elem).
rewrite malloc_assert.
simpl_malloc_assertion.
cancel.
unfold Frame.
instantiate (1:= `(fifo ((Int.repr 2, (Int.repr 20, (tt, tt))) :: nil) q1) :: nil).
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
destruct p as [q contents].
name Q _Q.
name p _p.
name t _t.
name n _n.
rewrite move_local_from_SEP.
unfold fifo at 1.
normalizex.
rewrite extract_exists_in_SEP.
apply extract_exists_pre; intros [hd tl].
destruct (isnil (elem::contents)) as [e3|n3]; [inv e3 | clear n3].
apply semax_pre_PQR with
 (EX  prefix : list elemtype,
   EX  ult : val,
    EX  elem0 : elemtype,
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
 destruct (isnil (@nil elemtype)) as [e3|n3]; [clear e3 | contradiction n3; auto].
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
rewrite lseg_nil_eq.
focus_SEP 2%nat.
rewrite @lift0C_andp.
rewrite @lift0C_prop.
rewrite move_prop_from_SEP.
apply semax_extract_PROP.
intro. apply ptr_eq_e in H. subst ult.
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
 rewrite lseg_cons_eq.
 normalize.
 focus_SEP 2%nat.
 rewrite extract_exists_in_SEP.
 apply extract_exists_pre; intro h.
 rewrite move_prop_from_SEP.
 apply semax_extract_PROP; intro.
 repeat rewrite lift0C_sepcon.
 rewrite lift0C_andp.
 rewrite lift0C_prop.
 repeat flatten_sepcon_in_SEP.
 rewrite move_prop_from_SEP.
 apply semax_extract_PROP; intro.
replace_in_pre 
   (@coerce mpred (environ -> mpred) (lift0_C mpred)
                    (field_mapsto Share.top
                       (@list_struct _struct_elem _next QS) _next hd h))
   (`(field_mapsto Share.top list_struct _next) (eval_id _p) `h).
apply go_lower_lem9.

go_lower. subst. apply andp_right; auto. apply prop_right; split; auto.
 rewrite lift0C_later.
forward. (*  n=p->next; *)
apply sequential'.
forward. (*  Q->head=n; *)

go_lower.
subst.
unfold fifo.
destruct (isnil (prefix ++ lastelem::nil)) as [e3|n3].
destruct prefix; inv e3.
clear n3.
rewrite exp_sepcon1. apply exp_right with (h, offset_val ult (Int.repr 8)).
cancel.
normalize. apply exp_right with prefix.
normalize. apply exp_right with ult.
normalize. apply exp_right with lastelem.
normalize.
cancel.
 eapply derives_trans; [ | apply list_cell_elemrep].
 cancel.
 apply field_mapsto_storable.
 unfold update_tycon.
 canonicalize_pre.
 forward.
 set (Delta' := join_tycon Delta (initialized _n Delta)).
 go_lower.
 repeat apply andp_right.
 apply prop_right. auto.
 cancel.
Qed.

Parameter body_mallocN:
 semax_external
  (EF_external _mallocN
     {| sig_args := AST.Tint :: nil; sig_res := Some AST.Tint |}) int
  (fun n : int =>
   !!(4 <= Int.signed n) && local (`(eq (Vint n)) (eval_id 1%positive)) &&
   emp) (fun n : int => `(memory_block Share.top n) retval).

Parameter body_freeN:
semax_external
  (EF_external _freeN
     {| sig_args := AST.Tint :: AST.Tint :: nil; sig_res := None |}) unit
  (fun _ : unit =>
   `(memory_block Share.top) (`force_int (eval_id 2%positive))
     (eval_id 1%positive)) (fun _ : unit => emp).

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


