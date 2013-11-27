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
  field_mapsto Tsh t_struct_elem _a p (force_rep Vint (fst rep)) * 
  (field_mapsto Tsh t_struct_elem _b p (force_rep Vint (snd rep)) *
   (field_mapsto_ Tsh t_struct_elem _next p)).

Definition link := field_mapsto Tsh t_struct_elem _next.
Definition link_ := field_mapsto_ Tsh t_struct_elem _next.

Lemma link_local_facts:
 forall x y, link x y |-- !! (isptr x /\ is_pointer_or_null y).
Proof.
 intros. unfold link.
 eapply derives_trans; [eapply field_mapsto_local_facts; reflexivity |].
 apply prop_derives.
 simpl. intuition.
Qed.

Hint Resolve link_local_facts : saturate_local.

Lemma link__local_facts:
 forall x, link_ x |-- !! isptr x.
Proof.
intros.
unfold link_.
eapply derives_trans; [eapply field_mapsto__local_facts; reflexivity | ].
apply prop_derives; intuition.
Qed.

Hint Resolve link__local_facts : saturate_local.

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
  POST [ (tptr t_struct_elem) ] `(elemrep (Some a, Some b)) retval.

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
 extensionality rho. unfold_lift. simpl.
 change 8 with (sizeof t_struct_fifo).
 rewrite memory_block_typed by reflexivity.
 simpl_typed_mapsto.
 reflexivity.
Qed.

Lemma list_cell_eq: forall sh p elem,
  list_cell QS sh p elem = 
   field_umapsto sh t_struct_elem _a (force_rep Vint (fst elem)) p* 
   field_umapsto sh t_struct_elem _b (force_rep Vint (snd elem)) p. 
Proof. intros. simpl_list_cell. auto. Qed.

Lemma body_fifo_empty: semax_body Vprog Gtot f_fifo_empty fifo_empty_spec.
Proof.
start_function.
name Q _Q.
name h _h.
unfold fifo.
normalize. intros [hd tl]. normalize.
forward. (* h = Q->head;*)
forward. (* return (h == NULL); *)
(* goal_1 *)
unfold fifo.
entailer.
apply exp_right with (h,tl).
apply andp_right; auto.
destruct (isnil contents).
* entailer!.
* unfold link. normalize.
 destruct prefix; entailer!; elim_hyps; simpl; auto.
Qed.

Lemma body_fifo_new: semax_body Vprog Gtot f_fifo_new fifo_new_spec.
Proof.
start_function.
name Q _Q.
name Q' _Q'.
forward. (* Q' = mallocN(sizeof ( *Q)); *) 
  instantiate (1:= Int.repr 8) in (Value of witness).
  (* goal_2 *) entailer!.
forward. (* Q = (struct fifo * )Q'; *)
apply semax_pre 
  with (PROP  () LOCAL ()
   SEP  (`(memory_block Tsh (Int.repr 8)) (eval_id _Q))).
  (* goal_3 *) entailer!.
rewrite memory_block_fifo.
normalize.
forward. (* Q->head = NULL; *)
(* goal_4 *)
forward.  (*  Q->tail = NULL;  *)
forward. (* return Q; *)
(* goal_5 *)
  unfold fifo.
  apply exp_right with (nullval,nullval).
  rewrite if_true by auto.
  entailer.
Qed.

Lemma body_fifo_put: semax_body Vprog Gtot f_fifo_put fifo_put_spec.
Proof.
start_function.
name Q _Q.
name p' _p.
name h _h.
name t _t.
unfold fifo at 1.
normalize. intros [hd tl]. normalize.
replace_SEP 3 (`link_ (eval_id _p)).
(* goal_6 *) entailer.
unfold link_.
(* goal_7 *)
forward. (* p->next = NULL; *)
normalize. fold t_struct_elem. simpl typeof; simpl eval_expr. 
forward. (*   h = Q->head; *)
forward_if 
  (PROP() LOCAL () SEP (`(fifo (contents ++ p :: nil) q))).
* (* goal 8 *) entailer!.
* (* then clause *)
  (* goal 9 *)
  forward. (*  Q->head=p; *)
  forward. (* Q->tail=p; *)
  (* goal 10 *)
  entailer.
  destruct (@isnil val contents).
  + subst. unfold fifo. apply exp_right with (p',p').  
      simpl.
      rewrite if_false by congruence.
      normalize.
      apply exp_right with nil.
      rewrite links_nil_eq.
      entailer!.
  + unfold link.
      normalize.
      destruct prefix; normalize; entailer!; elim_hyps; inv H.
* (* else clause *)
  forward. (*  t = Q->tail; *)
  destruct (isnil contents).
  + apply semax_pre with FF; [ | apply semax_ff].
  (* goal 11 *) entailer.
  + normalize. intro prefix. normalize. unfold link.
     forward. (*  t->next=p; *)
  (* goal 12 *)
     forward. (* Q->tail=p; *)
  (* goal 13 *)
     entailer.
     unfold fifo.
     apply exp_right with (h, p').
     rewrite if_false by (clear; destruct prefix; simpl; congruence).
     normalize.
     apply exp_right with (prefix ++ t :: nil).
     entailer.
     remember (link p' nullval) as A. (* prevent it from canceling! *)
     cancel. subst A. 
     eapply derives_trans; [ | apply links_cons_right ].
     cancel.
* (* after the if *)
    forward. (* return ; *)
Qed.

Lemma body_fifo_get: semax_body Vprog Gtot f_fifo_get fifo_get_spec.
Proof.
start_function.
name Q _Q.
name h _h.
name n _n.
unfold fifo at 1.
normalize. intros [hd tl].
rewrite if_false by congruence.
normalize. intro prefix. normalize.
forward. (*   p = Q->head; *)
destruct prefix; inversion H; clear H.
+ subst_any.
   rewrite links_nil_eq.
   normalize. apply ptr_eq_e in H. subst_any.
   unfold link.
   forward. (*  n=h->next; *)
   forward. (* Q->head=n; *)
   forward. (* return p; *)
   entailer!.
   unfold fifo. normalize. apply exp_right with (nullval, h).
   rewrite if_true by congruence.
   unfold link_.
   entailer!.
+ rewrite links_cons_eq.
    normalize. intro.
    normalize. destruct H. subst_any.
    forward. (*  n=h->next; *)
    forward. (* Q->head=n; *)
    forward. (* return p; *)
    entailer.
    unfold fifo. normalize. apply exp_right with (n, tl).
    rewrite if_false by (destruct prefix; simpl; congruence).
    normalize. apply exp_right with prefix.
    unfold link_. entailer!.
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
entailer!.
normalize.
forward. (* finish the function call *)
change 12 with (sizeof (t_struct_elem)).
rewrite memory_block_typed by reflexivity.
simpl_typed_mapsto.
apply semax_pre with  (* with better store tactic, shouldn't need this *)
  (PROP  ()
   LOCAL (`(eq (Vint b0)) (eval_id _b); `(eq (Vint a0)) (eval_id _a))
   SEP  (`(field_mapsto_ Tsh t_struct_elem _a) (eval_id _p);
           `(field_mapsto_ Tsh t_struct_elem _b) (eval_id _p);
           `(field_mapsto_ Tsh t_struct_elem _next) (eval_id _p))).
entailer!.
forward.  (*  p->a=a; *)
forward.  (*  p->b=b; *)
forward.  (* return p; *)
unfold elemrep.
entailer!.
Qed.

Lemma andp_get_result1:
  forall (P Q: environ->mpred) i, `(P && Q) (get_result1 i) = `P (get_result1 i) && `Q (get_result1 i).
Proof. reflexivity. Qed.
Hint Rewrite andp_get_result1: norm.

Lemma lift_lift0_retval:
  forall T (P: T) i, @liftx (Tarrow environ (LiftEnviron T)) (`P) (get_result1 i) = `P.
Proof. reflexivity. Qed.

Hint Rewrite lift_lift0_retval : norm.

Lemma lift_local_get_result1:
 forall (P: environ->Prop) i,
  @liftx (Tarrow environ (LiftEnviron mpred)) (local P) (get_result1 i) =
   local (`P (get_result1 i)).
Proof. reflexivity. Qed.
Hint Rewrite lift_local_get_result1 : norm.


Lemma lift_retval_get_result1: 
 forall T (P: val -> T) i,
   @liftx (Tarrow environ (LiftEnviron T))
     (@liftx (Tarrow val (LiftEnviron T)) P retval) (get_result1 i) =
    `P (eval_id i).
Proof. reflexivity. Qed.
Hint Rewrite lift_retval_get_result1 : norm.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name i _i.
name j _j.
name Q _Q.
name p _p.
forward. (* Q = fifo_new(); *)
instantiate (1:= tt) in (Value of witness).
entailer!.
auto with closed.
normalize. autorewrite with subst.
apply (remember_value (eval_id _Q)); intro q.
forward. (*  p = make_elem(1,10); *)
instantiate (1:= (Int.repr 1, Int.repr 10)) in (Value of witness).
entailer!.
auto with closed.
normalize. autorewrite with subst.
apply (remember_value (eval_id _p)); intro p'.
forward. (* fifo_put(Q,p);*)
 instantiate (1:= ((q,nil),p')) in (Value of witness).
 unfold elemrep. entailer!.
normalize.
forward. (*  p = make_elem(2,20); *)
instantiate (1:= (Int.repr 2, Int.repr 20)) in (Value of witness).
unfold elemrep. entailer!.
auto with closed.
normalize. autorewrite with subst.
 apply (remember_value (eval_id _p)); intro p2.
 forward.  (* fifo_put(Q,p); *)
 instantiate (1:= ((q,(p':: nil)),p2)) in (Value of witness).
 unfold elemrep. entailer!.
normalize.
forward. (*   p' = fifo_get(Q); *)
 instantiate (1:= ((q,(p2 :: nil)),p')) in (Value of witness).
 entailer!.
 normalize. autorewrite with subst. (* should have been done by forward *)
 change (fun rho => local (`(eq p') retval) rho && `(fifo (p2 :: nil) q) rho * `link_ retval rho)
   with (local (`(eq p') retval) && `(fifo (p2::nil) q) * `link_ retval).
 normalize.
 forward. (* p = p'; *)
 (* BUG:  normalize does extract pure propositions from LOCAL *)
 apply semax_pre with   (PROP  ()
   LOCAL  (`(eq p') (eval_id _p); `(eq q) (eval_id _Q))
   SEP  (`(fifo (p2 :: nil) q); `(link_ p');
   `(field_mapsto Tsh t_struct_elem _a p2 (Vint (Int.repr 2)));
   `(field_mapsto Tsh t_struct_elem _b p2 (Vint (Int.repr 20)));
   `(field_mapsto Tsh t_struct_elem _a p' (Vint (Int.repr 1)));
   `(field_mapsto Tsh t_struct_elem _b p' (Vint (Int.repr 10)))));
  [entailer! | ].
clear p0 p1 x p3.
forward. (*   i = p->a;  *)
forward. (*   j = p->b; *)
forward. (*  freeN(p, sizeof( *p)); *)
instantiate (1:=tt) in (Value of witness).
simpl @fst; simpl @snd.
entailer.
change 12 with (sizeof t_struct_elem).
rewrite memory_block_typed by reflexivity.
instantiate (1:= `(fifo (p2 :: nil) q *
(field_mapsto Tsh t_struct_elem _a p2 (Vint (Int.repr 2)) *
 field_mapsto Tsh t_struct_elem _b p2 (Vint (Int.repr 20))))::nil) 
 in (Value of Frame). (* Need this explicitly because simpl_typed_mapsto does
                                      not work in the presence of evars *)
simpl_typed_mapsto.
entailer!.
forward. (* return i+j; *)
unfold main_post.
entailer!.
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


