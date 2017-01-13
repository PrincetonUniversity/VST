Require Import floyd.proofauto.
Require Import floyd.library.
Require Import progs.list_dt.  Import LsegSpecial.
Require Import progs.queue2.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_elem := Tstruct _elem noattr.
Definition t_struct_fifo := Tstruct _fifo noattr.

Instance QS: listspec _elem _next (fun sh => malloc_token sh (sizeof t_struct_elem)).
Proof. eapply mk_listspec; reflexivity. Defined.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Lemma field_at_list_cell:
  forall sh i v p,
  data_at sh t_struct_elem (i,v) p
  = list_cell QS sh i p *
  field_at sh t_struct_elem [StructField _next] v p.
Proof.
intros.
unfold_data_at 1%nat.
f_equal.
unfold field_at, list_cell.
autorewrite with gather_prop.
f_equal.
apply ND_prop_ext.
rewrite field_compatible_cons; simpl.
intuition.
left; auto.
Qed.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).

Definition fifo (contents: list val) (p: val) : mpred :=
  (EX ht: (val*val), let (hd,tl) := ht in
      !! is_pointer_or_null hd && !! is_pointer_or_null tl &&
      data_at Tsh t_struct_fifo (hd, tl) p * malloc_token Tsh (sizeof t_struct_fifo) p *
      if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val, EX last: val,
              !!(contents = prefix++last::nil)
            &&  (lseg QS Tsh prefix hd tl
                   * malloc_token Tsh (sizeof t_struct_elem) tl
                   * data_at Tsh t_struct_elem (last, nullval) tl)))%logic.

Definition fifo_new_spec :=
 DECLARE _fifo_new
  WITH u : unit
  PRE  [  ]
       PROP() LOCAL() SEP ()
  POST [ (tptr t_struct_fifo) ]
    EX v:val, PROP() LOCAL(temp ret_temp v) SEP (fifo nil v).

Definition fifo_put_spec :=
 DECLARE _fifo_put
  WITH q: val, contents: list val, p: val, last: val
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
          PROP () LOCAL (temp _Q q; temp _p p)
          SEP (fifo contents q;
                 malloc_token Tsh (sizeof t_struct_elem) p;
                 data_at Tsh t_struct_elem (last,Vundef) p)
  POST [ tvoid ]
          PROP() LOCAL() SEP (fifo (contents++(last :: nil)) q).

Definition fifo_empty_spec :=
 DECLARE _fifo_empty
  WITH q: val, contents: list val
  PRE  [ _Q OF (tptr t_struct_fifo) ]
     PROP() LOCAL (temp _Q q) SEP(fifo contents q)
  POST [ tint ]
      PROP ()
      LOCAL(temp ret_temp (if isnil contents then Vtrue else Vfalse))
      SEP (fifo (contents) q).

Definition fifo_get_spec :=
 DECLARE _fifo_get
  WITH q: val, contents: list val, first: val
  PRE  [ _Q OF (tptr t_struct_fifo) ]
       PROP() LOCAL (temp _Q q) SEP (fifo (first :: contents) q)
  POST [ (tptr t_struct_elem) ]
      EX p:val,
       PROP ()
       LOCAL(temp ret_temp p)
       SEP (fifo contents q;
              malloc_token Tsh (sizeof t_struct_elem) p;
              data_at Tsh t_struct_elem (first,Vundef) p).

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH i: int
  PRE  [ _data OF tint ]
        PROP() LOCAL(temp _data (Vint i)) SEP()
  POST [ (tptr t_struct_elem) ]
    EX p:val,
       PROP()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh (sizeof t_struct_elem) p;
              data_at Tsh t_struct_elem (Vint i, Vundef) p).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs :=
  ltac:(with_library prog
    [surely_malloc_spec; fifo_new_spec; fifo_put_spec;
     fifo_empty_spec; fifo_get_spec; make_elem_spec;
     main_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. inv H0.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.

Lemma memory_block_fifo:
 forall p,
  field_compatible t_struct_fifo nil p ->
  memory_block Tsh 8 p = field_at_ Tsh t_struct_fifo nil p.
Proof.
 intros.
 change 8 with (sizeof t_struct_fifo).
 rewrite memory_block_data_at_; auto.
Qed.

Lemma fifo_isptr: forall al q, fifo al q |-- !! isptr q.
Proof.
intros.
 unfold fifo.
 if_tac; entailer; destruct ht; entailer!.
Qed.

Hint Resolve fifo_isptr : saturate_local.

Lemma body_fifo_empty: semax_body Vprog Gprog f_fifo_empty fifo_empty_spec.
Proof.
start_function.
unfold fifo.
Intros ht; destruct ht as [hd tl].
Intros.
forward. (* h = Q->head; *)
forward. (* return (h == NULL); *)
unfold fifo.
Exists (hd,tl).
destruct (isnil contents).
* entailer!.
  apply andp_right; auto with valid_pointer.
* Intros prefix last.
  Exists prefix last.
  assert_PROP (isptr hd). {
    destruct prefix; entailer.
    rewrite @lseg_cons_eq by auto. Intros y.
    entailer.
 }
 destruct hd; try contradiction.
 entailer!. simpl sizeof. entailer!.
Qed.

Lemma body_fifo_new: semax_body Vprog Gprog f_fifo_new fifo_new_spec.
Proof.
  start_function.
  forward_call (* Q = surely_malloc(sizeof ( *Q)); *)
     (sizeof t_struct_fifo).
    simpl; computable.
  Intros q.
  assert_PROP (field_compatible t_struct_fifo [] q).
   entailer!.
  rewrite memory_block_fifo by auto.
  forward. (* Q->head = NULL; *)
  forward. (* Q->tail = NULL; *)
  forward. (* return Q; *)
  Exists q. unfold fifo. Exists (nullval,nullval).
  rewrite if_true by auto.
  simpl sizeof.
  entailer!.
Qed.

Lemma body_fifo_put: semax_body Vprog Gprog f_fifo_put fifo_put_spec.
Proof.
start_function.
unfold fifo at 1.
Intros ht; destruct ht as [hd tl].
Intros.
forward. (* p->next = NULL; *)
forward. (*   h = Q->head; *)
forward_if
  (PROP() LOCAL () SEP (fifo (contents ++ last :: nil) q))%assert.
* if_tac; entailer.  (* typechecking clause *)
* (* then clause *)
  subst.
  forward. (* Q->head=p; *)
  forward. (* Q->tail=p; *)
  entailer.
  unfold fifo.
  destruct (isnil contents).
  + subst. Exists (p,p).
     simpl. rewrite if_false by congruence.
     Exists (@nil val) last.
      rewrite @lseg_nil_eq by auto.
      entailer!.
   + Intros prefix last0.
      destruct prefix;
      entailer!.
      rewrite @lseg_cons_eq by auto. simpl.
      Intros y.
      entailer!.
* (* else clause *)
  forward. (*  t = Q->tail; *)
  destruct (isnil contents).
  + Intros. contradiction H; auto.
  + Intros prefix last0.
     forward. (*  t->next=p; *)
     forward. (* Q->tail=p; *)
     entailer!.
     unfold fifo. Exists (hd, p).
     rewrite if_false by (clear; destruct prefix; simpl; congruence).
     Exists  (prefix ++ last0 :: nil) last.
     entailer.
     fold (data_at Tsh t_struct_elem (last0,p) tl).
     rewrite (field_at_list_cell Tsh last0 p).
     unfold_data_at 2%nat.
     unfold_field_at 3%nat.
     simpl sizeof.
     match goal with
     | |- _ |-- _ * _ * (_ * ?AA) => remember AA as A
     end.     (* prevent it from canceling! *)
     cancel. subst A.
     eapply derives_trans;
        [ | apply (lseg_cons_right_neq QS Tsh prefix hd last0 tl nullval p ); auto].
     simpl sizeof.  cancel.
* (* after the if *)
     forward. (* return ; *)
Qed.

Lemma body_fifo_get: semax_body Vprog Gprog f_fifo_get fifo_get_spec.
Proof.
start_function.
unfold fifo at 1.
Intros ht; destruct ht as [hd tl].
rewrite if_false by congruence.
Intros prefix last.
forward.  (*   h = Q->head; *)
destruct prefix; inversion H; clear H.
+
   rewrite @lseg_nil_eq by auto.
   Intros.
   subst_any.
   forward. (*  n=h->next; *)
   forward. (* Q->head=n; *)
   forward. (* return p; *)
   unfold fifo. Exists tl (nullval, tl).
   rewrite if_true by congruence.
   entailer!. simpl sizeof. unfold_data_at 1%nat. unfold_data_at 1%nat. cancel.
+ rewrite @lseg_cons_eq by auto.
    Intros x.
    simpl @valinject. (* can we make this automatic? *)
    subst_any.
    forward. (*  n=h->next; *)
    forward. (* Q->head=n; *)
    forward. (* return p; *)
    Exists hd. unfold fifo. Exists (x, tl).
    rewrite if_false by (destruct prefix; simpl; congruence).
    Exists prefix last.
    entailer!.
    rewrite field_at_list_cell. simpl sizeof. cancel.
Qed.

Lemma body_make_elem: semax_body Vprog Gprog f_make_elem make_elem_spec.
Proof.
start_function.
forward_call (*  p = surely_malloc(sizeof ( *p));  *)
  (sizeof t_struct_elem).
 simpl; computable.
 Intros p.
 assert_PROP (field_compatible t_struct_elem [] p). entailer!.
 rewrite memory_block_data_at_ by auto.
forward.  (*  p->data=i; *)
simpl.
forward. (* return p; *)
Exists p.
entailer!.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call (* Q = fifo_new(); *)  tt.
Intros q.

forward_call  (*  p = make_elem(1); *)
     (Int.repr 1).
Intros p'.
forward_call (* fifo_put(Q,p);*)
    ((q, @nil val),p', Vint (Int.repr 1)).

forward_call  (*  p = make_elem(2); *)
     (Int.repr 2).
Intros p2.
simpl app.
 forward_call  (* fifo_put(Q,p); *)
    (((q,[Vint (Int.repr 1)]),p2), Vint (Int.repr 2)).
simpl app.
forward_call  (*   p' = fifo_get(Q); p = p'; *)
    ((q,[Vint (Int.repr 2)]), Vint (Int.repr 1)).
Intros p3.
forward. (*   i = p->data;  *)
forward_call (*  free(p); *)
   (p3, sizeof t_struct_elem).
 assert_PROP (field_compatible t_struct_elem [] p3) by entailer!.
 rewrite memory_block_data_at_ by auto.
 cancel.
 forward. (* return i; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma ret_temp_make_ext_rval:
  forall gx ret p,
   locald_denote (temp ret_temp p) (make_ext_rval gx ret) ->
    p = force_val ret.
Proof.
  intros.
  hnf in H.
  rewrite retval_ext_rval in H. auto.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
semax_func_cons body_free.
semax_func_cons body_exit.
semax_func_cons body_surely_malloc.
semax_func_cons body_fifo_new.
semax_func_cons body_fifo_put.
semax_func_cons body_fifo_empty.
semax_func_cons body_fifo_get.
semax_func_cons body_make_elem.
semax_func_cons body_main.
Qed.

