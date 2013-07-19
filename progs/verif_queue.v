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

Definition link := field_mapsto Tsh t_struct_elem _next.
Definition link_ := field_mapsto_ Tsh t_struct_elem _next.

Definition fifo (contents: list val) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      field_mapsto Tsh t_struct_fifo _head p hd *
      field_mapsto Tsh t_struct_fifo _tail p tl *
      if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val, 
              !!(contents = prefix++tl::nil)
            &&  (links QS Tsh prefix hd tl * link tl nullval)).

Definition fifo_new_spec :=
 DECLARE _fifo_new
  WITH u : unit
  PRE  [  ] emp
  POST [ (tptr t_struct_fifo) ] `(fifo nil) retval.

Definition fifo_put_spec :=
 DECLARE _fifo_put
  WITH q: val, contents: list val, p: val
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
          PROP () LOCAL (`(eq q) (eval_id _Q); `(eq p) (eval_id _p)) 
          SEP (`(fifo contents q); `(link_ p))
  POST [ tvoid ] `(fifo (contents++(p :: nil)) q).

Definition fifo_empty_spec :=
 DECLARE _fifo_empty
  WITH q: val, contents: list val
  PRE  [ _Q OF (tptr t_struct_fifo) ]
     PROP() LOCAL (`(eq q) (eval_id _Q)) SEP(`(fifo contents q))
  POST [ tint ] local (`(eq (if isnil contents then Vtrue else Vfalse)) retval) && `(fifo (contents) q).

Definition fifo_get_spec :=
 DECLARE _fifo_get
  WITH q: val, contents: list val, p: val
  PRE  [ _Q OF (tptr t_struct_fifo) ]
       PROP() LOCAL (`(eq q) (eval_id _Q)) SEP (`(fifo (p :: contents) q)) 
  POST [ (tptr t_struct_elem) ] 
        local (`(eq p) retval) && `(fifo contents q) * `link_ retval.

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

Lemma body_fifo_empty: semax_body Vprog Gtot f_fifo_empty fifo_empty_spec.
Proof.
start_function.
name Q _Q.
name h _h.
unfold fifo.
match goal with |- semax _ _ _ ?P => set (Post := P) end.
normalize. intros [hd tl].
normalize.
forward. (* h = Q->head;*)
forward. (* return (h == NULL); *)
go_lower.
clear Delta POSTCONDITION Post.
subst h q.  
apply andp_right.
apply prop_right; simpl; auto.
unfold fifo. 
normalize.
apply exp_right with (hd,tl).
destruct (isnil contents).
subst.
normalize.
normalize.
clear n.
apply exp_right with prefix.
apply andp_right.
destruct prefix.
rewrite links_nil_eq.
normalize.
apply prop_right.
destruct hd,tl; simpl in H; try contradiction.
unfold eval_binop; simpl.
destruct (Int.eq i (Int.repr 0)); reflexivity.
 simpl. reflexivity.
apply prop_right. destruct hd; inv TC; try reflexivity.
unfold eval_binop; simpl. change (Int.repr 0) with Int.zero; rewrite H0. simpl.
reflexivity.
apply andp_right.
destruct prefix.
rewrite links_nil_eq.
normalize.
unfold link.
rewrite (field_mapsto_isptr _ _next).
normalize.
apply ptr_eq_e in H; subst tl.
destruct hd; simpl in H0; try contradiction.
apply prop_right. reflexivity.
rewrite links_cons_eq.
normalize.
rewrite (field_mapsto_isptr _ _next).
normalize.
apply prop_right. destruct v; inv H1. reflexivity.
cancel.
normalize.
Qed.

Lemma body_fifo_new: semax_body Vprog Gtot f_fifo_new fifo_new_spec.
Proof.
start_function.
name Q _Q.
name Q' _Q'.
forward. (* Q' = mallocN(sizeof ( *Q)); *) 
instantiate (1:= Int.repr 8) in (Value of witness).
go_lower. normalize.
repeat apply andp_right; try apply prop_right.
compute; congruence.
compute; congruence.
cancel.
normalize.
forward. (* Q = (struct fifo * )Q'; *)
apply semax_pre 
  with (PROP  () LOCAL ()
   SEP  (`(memory_block Tsh (Int.repr 8)) (eval_id _Q))).
go_lower. destruct Q'; inv H0; inv TC; normalize.
rewrite memory_block_fifo. normalize.
forward. (* Q->head = NULL; *)
forward.  (*  Q->tail = NULL;  *)
forward. (* return Q; *)
go_lower.
  apply andp_right. apply prop_right; auto.
  rewrite field_mapsto_isptr; normalize.
  apply andp_right.
  apply prop_right; destruct Q; inv H; inv TC; hnf; simpl; auto.
  unfold fifo.
   destruct (@isnil val nil); [ | congruence].
  apply exp_right with (nullval,nullval).
  rewrite field_mapsto_isptr.  normalize.
  destruct Q; inv H; inv TC; simpl; auto.
Qed.

Lemma body_fifo_put: semax_body Vprog Gtot f_fifo_put fifo_put_spec.
Proof.
start_function.
name Q _Q.
name p' _p.
name h _h.
name t _t.
unfold fifo at 1.
normalize. intros [hd tl].
normalize.
replace_SEP 3 (`link_ (eval_id _p)).
clear POSTCONDITION MORE_COMMANDS.
go_lower; subst; auto.
unfold link_.
forward. (* p->next = NULL; *)
simpl typeof. simpl eval_expr. normalize.
change (eval_cast (tptr tvoid) (tptr t_struct_elem)
         (eval_cast tint (tptr tvoid) (Vint (Int.repr 0))))
  with (Vint Int.zero).
forward. (*   h = Q->head; *)
apply semax_seq with 
  (PROP() LOCAL () SEP (`(fifo (contents ++ p :: nil) q))).
forward.  (* if (h==NULL) ... *)
go_lower. 
subst. apply andp_right; auto.
apply prop_right; repeat split; auto.
right. hnf. apply Int.eq_true.
(* then clause *)
simplify_typed_comparison.
forward. (*  Q->head=p; *)
forward. (* Q->tail=p; *)
go_lower.
subst. subst hd.
destruct (@isnil val contents).
(* CASE ONE:  isnil contents *)
subst. normalize.
unfold fifo. apply exp_right with (p',p').
simpl.
destruct (isnil (p' ::nil)); [ congruence | ].
normalize.
apply exp_right with nil.
rewrite links_nil_eq.
rewrite (field_mapsto_isptr _ _next).
 normalize.
destruct p'; inv H. unfold link.
rewrite prop_true_andp by (split;  auto; apply Int.eq_true).
cancel.
(* CASE TWO: contents <> nil *)
normalize.
destruct prefix.
rewrite links_nil_eq.
normalize.
apply ptr_eq_e in H. subst tl.
unfold link.
repeat rewrite <- sepcon_assoc.
rewrite sepcon_comm.
rewrite field_mapsto_isptr.
normalize.
rewrite links_cons_eq.
normalize.
(* else clause *)
simplify_typed_comparison.
forward. (*  t = Q->tail; *)
(* simpl classify_cast. cbv iota. *)
destruct (isnil contents).
(* CASE THREE: contents = nil *)
apply semax_pre with FF; [ | apply semax_ff].
clear_abbrevs.
go_lower. subst. normalize.
focus_SEP 2.
change (`(EX  prefix : list val,
      !!(contents = prefix ++ tl :: nil) &&
      (links QS Tsh prefix hd tl * link tl nullval)))
 with (EX prefix: list val, 
      !!(contents = prefix ++ tl :: nil) &&
      `(links QS Tsh prefix hd tl * link tl nullval)).
rewrite extract_exists_in_SEP.
apply extract_exists_pre. intro prefix.
normalize.
unfold link.
replace_SEP 1 ( `(field_mapsto Tsh t_struct_elem _next) (eval_id _t) `nullval).
clear_abbrevs.
go_lower. subst; auto.
forward. (*  t->next=p; *)
simpl.
sequential.
forward. (* Q->tail=p; *)
go_lower. subst. clear n.
normalize.
unfold fifo.
apply exp_right with (hd, p').
destruct (isnil ((prefix ++ tl :: nil) ++ p' :: nil)).
destruct prefix; inv e.
clear n.
normalize.
apply exp_right with (prefix ++ tl :: nil).
rewrite (field_mapsto_isptr _ _ _ p').
normalize.
remember (link p' nullval) as A. (* prevent it from canceling! *)
cancel. subst.
eapply derives_trans; [ | apply links_cons_right ].
cancel.

(* after the if *)
unfold_abbrev.  (* FIXME this should not be necessary *)
forward. (* return ; *)
go_lower. normalize.
Qed.

Lemma flip_lifted_eq:
  forall (v1: environ -> val) (v2: val),
    `eq v1 `v2 = `(eq v2) v1.
Proof.
intros. unfold_lift. extensionality rho. apply prop_ext; split; intro; auto.
Qed.
Hint Rewrite flip_lifted_eq : norm.

Lemma body_fifo_get: semax_body Vprog Gtot f_fifo_get fifo_get_spec.
Proof.
start_function.
name Q _Q.
name h _h.
name n _n.
unfold fifo at 1.
normalize.
intros [hd tl].
destruct (isnil (p::contents)) as [e3|n3]; [inv e3 | clear n3].
normalize. intro prefix.
normalize.
 forward. (*   p = Q->head; *)
destruct prefix; inversion H; clear H.
(* CASE 1: prefix=nil *)
subst tl.
rewrite links_nil_eq.
normalize.
normalize. apply ptr_eq_e in H. subst hd.
unfold link.
 forward. (*  n=h->next; *)
 forward. (* Q->head=n; *)
 forward. (* return p; *)
 go_lower. subst. rewrite prop_true_andp by auto.
 rewrite prop_true_andp by (destruct h; apply TC0).
 rewrite prop_true_andp by (destruct h; inv TC0; auto).
 rewrite emp_sepcon.
 unfold fifo. normalize. apply exp_right with (nullval, h).
 destruct (@isnil val nil); [ | congruence].
 rewrite prop_true_andp by auto. unfold link_. cancel.
 apply field_mapsto_field_mapsto_.
(* CASE 2: prefix <> nil *)
rewrite links_cons_eq.
normalize. intro.
repeat rewrite andp_assoc.
normalize. subst v hd.
forward. (*  n=h->next; *)
 forward. (* Q->head=n; *)
 forward. (* return p; *)
go_lower. subst x h q.
 rewrite prop_true_andp by auto.
 rewrite prop_true_andp by (destruct p; apply TC0).
 unfold fifo. normalize. apply exp_right with (n, tl).
 subst.
 destruct (isnil (prefix ++ tl :: nil)); [ destruct prefix; inv e | ]. clear n0.
 normalize. apply exp_right with prefix.
 rewrite prop_true_andp by auto. unfold link_. cancel.
 apply field_mapsto_field_mapsto_.
Qed.

Lemma body_make_elem: semax_body Vprog Gtot f_make_elem make_elem_spec.
Proof.
start_function. rename a into a0; rename b into b0.
name a _a.
name b _b.
name p _p.
name p' _p'.
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
 instantiate (1:= ((q,nil),p')) in (Value of witness).
 unfold witness.
 go_lower. subst p Q. normalize. cancel.
unfold elemrep. cancel.
forward. (*  p = make_elem(2,20); *)
instantiate (1:= (Int.repr 2, Int.repr 20)) in (Value of witness).
go_lower. subst Q p. normalize.
instantiate (1:= (`(fifo (p' :: nil) q)::
       `(field_mapsto Tsh t_struct_elem _a p' (Vint (Int.repr 1)))::
       `(field_mapsto Tsh t_struct_elem _b p' (Vint (Int.repr 10)))::nil)) in (Value of Frame).
unfold Frame; unfold_lift; simpl. cancel.
auto with closed.
 autorewrite with subst. (* should have been done by forward *)
apply semax_pre with
  (EX q:val, EX p:val, 
 (PROP  ()
   LOCAL (`(eq q) (eval_id _Q); `(eq p) (eval_id _p))
   SEP  (`(elemrep (Int.repr 2, Int.repr 20)) (eval_id _p);
           `(fifo (p' :: nil)) (eval_id _Q);
           `(field_mapsto Tsh t_struct_elem _a p' (Vint (Int.repr 1)));
           `(field_mapsto Tsh t_struct_elem _b p' (Vint (Int.repr 10)))))).
unfold_lift; intro rho. normalize. apply exp_right with (eval_id _Q rho).
normalize. apply exp_right with (eval_id _p rho).
normalize.

apply extract_exists_pre; intro q2.
apply extract_exists_pre; intro p2.
forward.  (* fifo_put(Q,p); *)
 instantiate (1:= ((q2,(p':: nil)),p2)) in (Value of witness).
 unfold witness.
 unfold_lift; go_lower. subst Q p. normalize.
 unfold elemrep. cancel.
simpl.
normalize.
forward. (*   p = fifo_get(Q); *)
 instantiate (1:= ((q2,(p2 :: nil)),p')) in (Value of witness).
unfold witness.
unfold_lift; go_lower. normalize. cancel.
auto with closed.
 autorewrite with subst. (* should have been done by forward *)
apply semax_pre with
  (PROP  ()
   LOCAL  (`(eq q2) (eval_id _Q); `(eq p2 p3); `(eq p') (eval_id _p))
   SEP  (`(fifo (p2 :: nil) q2); `link_ (eval_id _p);
   `(field_mapsto Tsh t_struct_elem _a p2 (Vint (Int.repr 2)));
   `(field_mapsto Tsh t_struct_elem _b p2 (Vint (Int.repr 20)));
   `(field_mapsto Tsh t_struct_elem _a) (eval_id _p) `(Vint (Int.repr 1));
   `(field_mapsto Tsh t_struct_elem _b) (eval_id _p) `(Vint (Int.repr 10)))).
go_lower. subst. normalize. cancel.
forward. (*   i = p->a;  *)
forward. (*   j = p->b; *)
forward. (*  freeN(p, sizeof( *p)); *)
instantiate (1:=tt) in (Value of witness).
simpl @fst; simpl @snd.
go_lower. normalize.
simpl force_int.
rewrite (eval_cast_neutral_tc_val p); eauto.
change 12 with (sizeof t_struct_elem).
rewrite memory_block_typed.

unfold Frame.
instantiate (1:= `(fifo (p2 :: nil) q2 *
(field_mapsto Tsh t_struct_elem _a p2 (Vint (Int.repr 2)) *
 field_mapsto Tsh t_struct_elem _b p2 (Vint (Int.repr 20))))::nil).
clear. (* This "clear" is only needed to work around bug 2997 in Coq 8.4 *)
simpl_typed_mapsto.
simpl. normalize. cancel.
apply sepcon_derives; apply field_mapsto_field_mapsto_.
forward. (* return i+j; *)
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


