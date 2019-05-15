Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.list_dt.  Import LsegSpecial.
Require Import VST.progs.queue2.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_elem := Tstruct _elem noattr.
Definition t_struct_fifo := Tstruct _fifo noattr.

Instance QS: listspec _elem _next (fun sh => malloc_token Ews t_struct_elem).
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
unfold_data_at (data_at _ _ _ _).
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
   WITH t:type, gv: globals
   PRE [ _n OF tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp _n (Vint (Int.repr (sizeof t))); gvars gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition fifo_body (contents: list val) (hd tl : val) :=
     (if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val, EX last: val,
              !!(contents = prefix++last::nil)
            &&  (lseg QS Ews prefix hd tl
                   * malloc_token Ews t_struct_elem tl
                   * data_at Ews t_struct_elem (last, nullval) tl)))%logic.

Definition fifo (contents: list val) (p: val) : mpred :=
  EX ht: (val*val), let (hd,tl) := ht in
      !! is_pointer_or_null hd && !! is_pointer_or_null tl &&
      data_at Ews t_struct_fifo (hd, tl) p * malloc_token Ews t_struct_fifo p *
      fifo_body contents hd tl.

Definition fifo_new_spec :=
 DECLARE _fifo_new
  WITH gv: globals
  PRE  [  ]
       PROP() LOCAL(gvars gv) SEP (mem_mgr gv)
  POST [ (tptr t_struct_fifo) ]
    EX v:val, PROP() LOCAL(temp ret_temp v) SEP (mem_mgr gv; fifo nil v).

Definition fifo_put_spec :=
 DECLARE _fifo_put
  WITH q: val, contents: list val, p: val, last: val
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
          PROP () LOCAL (temp _Q q; temp _p p)
          SEP (fifo contents q;
                 malloc_token Ews t_struct_elem p;
                 data_at Ews t_struct_elem (last,Vundef) p)
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
              malloc_token Ews t_struct_elem p;
              data_at Ews t_struct_elem (first,Vundef) p).

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH i: int, gv: globals
  PRE  [ _data OF tint ]
        PROP() LOCAL(temp _data (Vint i); gvars gv) SEP(mem_mgr gv)
  POST [ (tptr t_struct_elem) ]
    EX p:val,
       PROP()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; 
              malloc_token Ews t_struct_elem p;
              data_at Ews t_struct_elem (Vint i, Vundef) p).

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]
       PROP() LOCAL (temp ret_temp (Vint (Int.repr 1))) SEP(TT).

Definition Gprog : funspecs :=
  ltac:(with_library prog
    [surely_malloc_spec; fifo_new_spec; fifo_put_spec;
     fifo_empty_spec; fifo_get_spec; make_elem_spec;
     main_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     (t,gv).
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.

Lemma fifo_isptr: forall al q, fifo al q |-- !! isptr q.
Proof.
intros.
 unfold fifo, fifo_body.
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
{
unfold fifo, fifo_body.
destruct (isnil contents).
+ normalize; auto with valid_pointer.
+ entailer!.
  destruct hd; inv PNhd; entailer!.
}
unfold fifo, fifo_body.
Exists (hd,tl).
destruct (isnil contents).
* entailer!.
* Intros prefix last.
Exists prefix last.
  assert_PROP (isptr hd).
    destruct prefix; entailer.
    rewrite @lseg_cons_eq by auto. Intros y.
    entailer.
 destruct hd; try contradiction.
 entailer!.
Qed.

Lemma body_fifo_new: semax_body Vprog Gprog f_fifo_new fifo_new_spec.
Proof.
  start_function.

  forward_call (* Q = surely_malloc(sizeof ( *Q)); *)
     (t_struct_fifo, gv).
    split3; simpl; auto; computable.
  Intros q.
  assert_PROP (field_compatible t_struct_fifo [] q).
   entailer!.
  forward. (* Q->head = NULL; *)
  forward. (* Q->tail = NULL; *)
  forward. (* return Q; *)
  Exists q. unfold fifo, fifo_body. Exists (nullval,nullval).
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
* unfold fifo_body; if_tac; entailer.  (* typechecking clause *) 
      (* TODO: In the line above, entailer works but not entailer! *)
* (* then clause *)
  subst.
  forward. (* Q->head=p; *)
  forward. (* Q->tail=p; *)
  entailer.
  unfold fifo, fifo_body.
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
  unfold fifo_body.
  destruct (isnil contents).
  + Intros. contradiction H; auto.
  + Intros prefix last0.
     forward. (*  t->next=p; *)
     forward. (* Q->tail=p; *)
     entailer!.
     unfold fifo, fifo_body. Exists (hd, p).
     rewrite if_false by (clear; destruct prefix; simpl; congruence).
     Exists  (prefix ++ last0 :: nil) last.
     entailer.
     rewrite (field_at_list_cell Ews last0 p).
     unfold_data_at (@data_at CompSpecs Ews t_struct_elem (last,nullval) p).
     unfold_data_at (data_at _ _ _ p).
     simpl sizeof.
     match goal with
     | |- _ |-- _ * _ * (_ * ?AA) => remember AA as A
     end.     (* prevent it from canceling! *)
     cancel. subst A.
     eapply derives_trans;
        [ | apply (lseg_cons_right_neq QS Ews prefix hd last0 tl nullval p ); auto].
     simpl sizeof.  cancel.
* (* after the if *)
     forward. (* return ; *)
Qed.

Lemma body_fifo_get: semax_body Vprog Gprog f_fifo_get fifo_get_spec.
Proof.
start_function.
unfold fifo at 1, fifo_body.
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
   unfold fifo, fifo_body. Exists tl (nullval, tl).
   rewrite if_true by congruence.
   entailer!. simpl sizeof.
   do 2 unfold_data_at (data_at _ _ _ _). cancel.
+ rewrite @lseg_cons_eq by auto.
    Intros x.
    simpl @valinject. (* can we make this automatic? *)
    subst_any.
    forward. (*  n=h->next; *)
    forward. (* Q->head=n; *)
    forward. (* return p; *)
    Exists hd. unfold fifo, fifo_body. Exists (x, tl).
    rewrite if_false by (destruct prefix; simpl; congruence).
    Exists prefix last.
    entailer!.
    rewrite field_at_list_cell. simpl sizeof. cancel.
Qed.

Lemma body_make_elem: semax_body Vprog Gprog f_make_elem make_elem_spec.
Proof.
start_function.
forward_call (*  p = surely_malloc(sizeof ( *p));  *)
    (t_struct_elem, gv).
 split3; simpl; auto; computable.
 Intros p.
forward.  (*  p->data=i; *)
simpl.
forward. (* return p; *)
Exists p.
entailer!.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr gv).
forward_call (* Q = fifo_new(); *)  gv.
Intros q.

forward_call  (*  p = make_elem(1); *)
     (Int.repr 1, gv).
Intros p'.
forward_call (* fifo_put(Q,p);*)
    ((q, @nil val),p', Vint (Int.repr 1)).

forward_call  (*  p = make_elem(2); *)
     (Int.repr 2, gv).
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
   (t_struct_elem, p3, gv).
assert_PROP (isptr p3); [entailer! | rewrite if_false by (intro; subst; contradiction) ]; cancel.
forward. (* return i; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
  prove_semax_prog.
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

