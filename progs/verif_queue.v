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
  field_at Tsh t_struct_elem _a (fst rep) p * 
  (field_at Tsh t_struct_elem _b (snd rep) p *
   (field_at_ Tsh t_struct_elem _next) p).

Definition fifo (contents: list val) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      !! is_pointer_or_null hd && !! is_pointer_or_null tl &&
      field_at Tsh t_struct_fifo _head hd p *
      field_at Tsh t_struct_fifo _tail tl p *
      if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val, 
              !!(contents = prefix++tl::nil)
            &&  (links QS Tsh prefix hd tl * field_at Tsh t_struct_elem _next nullval tl)).

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
          SEP (`(fifo contents q); `(field_at_ Tsh t_struct_elem _next p))
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
        local (`(eq p) retval) && `(fifo contents q) * `(field_at_ Tsh t_struct_elem _next) retval.

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH a: int, b: int
  PRE  [ _a OF tint, _b OF tint ] 
        PROP() LOCAL(`(eq (Vint a)) (eval_id _a); `(eq (Vint b)) (eval_id _b)) SEP()
  POST [ (tptr t_struct_elem) ] `(elemrep (Vint a, Vint b)) retval.

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
  `(field_at_ Tsh t_struct_fifo queue._head) e *
  `(field_at_ Tsh t_struct_fifo queue._tail) e.
Proof.
 intros.
 extensionality rho. unfold_lift. simpl.
 change 8 with (sizeof t_struct_fifo).
 rewrite memory_block_typed by reflexivity.
 simpl_data_at.
 reflexivity.
Qed.

Lemma list_cell_eq: forall sh elem,
  list_cell QS sh elem = 
   field_at sh t_struct_elem _a (fst elem) * 
   field_at sh t_struct_elem _b (snd elem). 
Proof. reflexivity. Qed.
 
Lemma body_fifo_empty: semax_body Vprog Gtot f_fifo_empty fifo_empty_spec.
Proof.
start_function.
name Q _Q.
name h _h.
unfold fifo.
normalize. intros [hd tl]. normalize.
forward. (* h = Q->head;*)
forward.  (* return (h == NULL); *)
(* goal_1 *)
unfold fifo.
entailer.
apply exp_right with (h,tl).
entailer.
destruct (isnil contents).
* entailer!.
* normalize.
 destruct prefix; entailer; elim_hyps; simpl; apply prop_right; auto.
Qed.

Lemma body_fifo_new: semax_body Vprog Gtot f_fifo_new fifo_new_spec.
Proof.
start_function.
name Q _Q.
name Q' _Q'.
forward_call (* Q' = mallocN(sizeof ( *Q)); *) 
      (Int.repr 8).
  (* goal_2 *) entailer!.
after_call.
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
  entailer!.
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
(* goal_7 *)
forward. (* p->next = NULL; *)
normalize.
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
  destruct (isnil contents).
  + subst. apply exp_right with (p',p').  
      simpl.
      rewrite if_false by congruence.
      normalize.
      apply exp_right with nil.
      rewrite links_nil_eq.
      entailer!. 
  +  normalize.
      destruct prefix; normalize; entailer!; elim_hyps; inv H1.
* (* else clause *)
  forward. (*  t = Q->tail; *)
  destruct (isnil contents).
  + apply semax_pre with FF; [ | apply semax_ff].
  (* goal 11 *) entailer.
  + normalize. intro prefix. normalize.
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
     remember (field_at Tsh t_struct_elem _next nullval p') as A. (* prevent it from canceling! *)
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
destruct prefix; inversion H1; clear H1.
+ subst_any.
   rewrite links_nil_eq.
   normalize. apply ptr_eq_e in H1. subst_any.
   forward. (*  n=h->next; *)
   forward. (* Q->head=n; *)
   forward. (* return p; *)
   entailer!.
   unfold fifo. apply exp_right with (nullval, h).
   rewrite if_true by congruence.
   entailer!.
+ rewrite links_cons_eq.
    normalize. intro.
    normalize. subst_any.
    forward. (*  n=h->next; *)
    forward. (* Q->head=n; *)
    forward. (* return p; *)
    entailer.
    unfold fifo. normalize. apply exp_right with (n, tl).
    rewrite if_false by (destruct prefix; simpl; congruence).
    normalize. apply exp_right with prefix.
    entailer!.
Qed.

Lemma body_make_elem: semax_body Vprog Gtot f_make_elem make_elem_spec.
Proof.
start_function. rename a into a0; rename b into b0.
name a _a.
name b _b.
name p _p.
name p' _p'.
forward_call (*  p = mallocN(sizeof ( *p));  *) 
  (Int.repr 12).
entailer!.
auto 50 with closed.
after_call.
change 12 with (sizeof (t_struct_elem)).
rewrite memory_block_typed by reflexivity.
simpl_data_at.
forward.  (*  p->a=a; *)
forward.  (*  p->b=b; *)
forward.  (* return p; *)
unfold elemrep.
entailer!.
Qed.

(*
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
*)

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name i _i.
name j _j.
name Q _Q.
name p _p.
forward_call (* Q = fifo_new(); *) tt.
entailer!.
auto with closed.
after_call.
apply (remember_value (eval_id _Q)); intro q.
forward_call (*  p = make_elem(1,10); *)
   (Int.repr 1, Int.repr 10).
entailer!.
auto with closed.
after_call.
apply (remember_value (eval_id _p)); intro p'.
forward_call (* fifo_put(Q,p);*)
    ((q, @nil val),p').
unfold elemrep; entailer!.
after_call.
forward_call (*  p = make_elem(2,20); *)
    (Int.repr 2, Int.repr 20).
unfold elemrep; entailer!.
auto with closed.
after_call.
 apply (remember_value (eval_id _p)); intro p2.
 forward_call  (* fifo_put(Q,p); *)
    ((q,(p':: nil)),p2).
 unfold elemrep; entailer!.
after_call.
forward_call (*   p' = fifo_get(Q); p = p'; *)
  ((q,(p2 :: nil)),p').
 entailer!.
 auto 50 with closed.
after_call.
normalize.
 subst p1 p3.
forward. (*   i = p->a;  *)
forward. (*   j = p->b; *)
forward_call (*  freeN(p, sizeof( *p)); *)
   tt. {
  entailer.
  change 12 with (sizeof t_struct_elem).
  rewrite memory_block_typed by reflexivity.
  simpl_data_at.
  entailer!.
} after_call.
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


