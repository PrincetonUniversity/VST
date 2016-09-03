Require Import floyd.proofauto.
Require Import progs.list_dt.  Import LsegSpecial.
Require Import progs.queue2.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_elem := Tstruct _elem noattr.
Definition t_struct_fifo := Tstruct _fifo noattr.


Instance QS: listspec _elem _next. 
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

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ 1%positive OF tint]
     PROP (4 <= n <= Int.max_unsigned) 
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ] 
     EX v: val,
     PROP (malloc_compatible n v) 
     LOCAL (temp ret_temp v) 
     SEP (memory_block Tsh n v).

Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]  
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]  
    PROP () LOCAL () SEP ().

Definition fifo (contents: list val) (p: val) : mpred :=
  (EX ht: (val*val), let (hd,tl) := ht in
      !! is_pointer_or_null hd && !! is_pointer_or_null tl &&
      data_at Tsh t_struct_fifo (hd, tl) p *
      if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val, EX last: val, 
              !!(contents = prefix++last::nil)
            &&  (lseg QS Tsh prefix hd tl
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
       SEP (data_at Tsh t_struct_elem (Vint i, Vundef) p).

Definition main_spec := 
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := 
  augment_funspecs prog [
    mallocN_spec; freeN_spec; fifo_new_spec; fifo_put_spec;
    fifo_empty_spec; fifo_get_spec; make_elem_spec; main_spec].

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
 entailer!. entailer!.
Qed.

Lemma body_fifo_new: semax_body Vprog Gprog f_fifo_new fifo_new_spec.
Proof.
  start_function. 
  forward_call (* Q = mallocN(sizeof ( *Q)); *)
     8.
    computable.
  Intros q.
  rewrite memory_block_fifo
   by (eapply malloc_compatible_field_compatible; try eassumption; 
      auto with typeclass_instances;
      exists 2; reflexivity).
  forward. (* Q->head = NULL; *)
  forward. (* Q->tail = NULL; *)
  forward. (* return Q; *)
  Exists q. unfold fifo. Exists (nullval,nullval).
  rewrite if_true by auto.
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
      contradiction (field_compatible_isptr _ _ _ H5).
      rewrite @lseg_cons_eq by auto. simpl.
      Intros y.
      entailer!.
      contradiction (field_compatible_isptr _ _ _ H8).
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
     match goal with
     | |- _ |-- _ * _ * (_ * ?AA) => remember AA as A
     end.     (* prevent it from canceling! *)
     cancel. subst A.
     eapply derives_trans;
        [ | apply (lseg_cons_right_neq QS Tsh prefix hd last0 tl nullval p ); auto].
     cancel.
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
   entailer!. unfold_data_at 1%nat. unfold_data_at 1%nat. cancel.
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
    rewrite field_at_list_cell. cancel.
Qed.

Lemma body_make_elem: semax_body Vprog Gprog f_make_elem make_elem_spec.
Proof.
start_function.
forward_call (*  p = mallocN(sizeof ( *p));  *) 
  (sizeof t_struct_elem).
 simpl; computable.
Intros p.
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
Time forward. (*   i = p->data;  *) 

forward_call (*  freeN(p, sizeof( *p)); *)
   (p3, sizeof t_struct_elem).
 assert_PROP (field_compatible t_struct_elem [] p3) by entailer!.
 rewrite memory_block_data_at_ by auto. cancel.
forward. (* return i; *)
Qed.

Existing Instance NullExtension.Espec.

Parameter body_mallocN:
 semax_external
  (1%positive ::nil)
  (EF_external "mallocN"
     {| sig_args := AST.Tint :: nil; sig_res := Some AST.Tint; sig_cc := cc_default |}) Z
  (fun n : Z =>
   PROP  (4 <= n <= Int.max_unsigned)  LOCAL  (temp 1%positive (Vint (Int.repr n)))  SEP())%assert
  (fun n : Z =>
   EX  v : val,
   PROP  (malloc_compatible n v)
   LOCAL  (temp ret_temp v)  SEP  (memory_block Tsh n v)).

Parameter body_freeN:
semax_external
  (1%positive::2%positive ::nil)
  (EF_external "freeN"
     {| sig_args := AST.Tint :: AST.Tint :: nil; sig_res := None; sig_cc := cc_default |}) (val*Z)
  (fun pn : val*Z => let (p,n) := pn in
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p))
  (fun pn => let (p,n) := pn in
    PROP () LOCAL () SEP ()).

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
semax_func_cons body_mallocN.
 renormalize. entailer!.
 rewrite (ret_temp_make_ext_rval gx ret _ (eq_refl _)) in Px0.
 auto.
semax_func_cons body_freeN.
  admit.  (* yuck *)
semax_func_cons body_fifo_new.
semax_func_cons body_fifo_put.
semax_func_cons body_fifo_empty.
semax_func_cons body_fifo_get.
semax_func_cons body_make_elem.
semax_func_cons body_main.
Admitted.


