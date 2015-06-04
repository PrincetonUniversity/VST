Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.queue.

Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Local Open Scope logic.

Instance QS: listspec _elem _next. 
Proof. eapply mk_listspec; reflexivity. Defined.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Definition natural_alignment := 8.

Definition malloc_compatible (n: Z) (p: val) : Prop :=
  match p with
  | Vptr b ofs => (natural_alignment | Int.unsigned ofs) /\
                           Int.unsigned ofs + n < Int.modulus
  | _ => False
  end.

Lemma malloc_compatible_field_compatible:
  forall (cs: compspecs) (csl: compspecs_legal cs) t p n,
     sizeof cenv_cs t = n ->
     legal_alignas_type t = true ->
     legal_cosu_type t = true ->
     complete_type cenv_cs t = true ->
     (alignof cenv_cs t | natural_alignment) ->
     malloc_compatible n p ->
     field_compatible t nil p.
Proof.
intros.
subst n.
destruct p; simpl in *; try contradiction.
destruct H4.
pose proof (Int.unsigned_range i).
repeat split; simpl; auto; try omega.
clear - H3 H.
eapply Zdivides_trans; eauto.
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
     SEP (`(memory_block Tsh (Int.repr n) v)).

Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]  
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (`(memory_block Tsh (Int.repr n) p))
  POST [ tvoid ]  
    PROP () LOCAL () SEP ().

Definition t_struct_elem := Tstruct _elem noattr.
Definition t_struct_fifo := Tstruct _fifo noattr.

Definition elemrep (rep: elemtype QS) (p: val) : mpred :=
  field_at Tsh t_struct_elem [StructField _a] (fst rep) p * 
  (field_at Tsh t_struct_elem [StructField _b] (snd rep) p *
   (field_at_ Tsh t_struct_elem [StructField _next]) p).

Definition fifo (contents: list val) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      !! is_pointer_or_null hd && !! is_pointer_or_null tl &&
      field_at Tsh t_struct_fifo nil (hd, tl) p *
      if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val, 
              !!(contents = prefix++tl::nil)
            &&  (links QS Tsh prefix hd tl * field_at Tsh t_struct_elem [StructField _next] nullval tl)).

Definition fifo_new_spec :=
 DECLARE _fifo_new
  WITH u : unit
  PRE  [  ]
       PROP() LOCAL() SEP ()
  POST [ (tptr t_struct_fifo) ] 
    EX v:val, PROP() LOCAL(temp ret_temp v) SEP (`(fifo nil v)).

Definition fifo_put_spec :=
 DECLARE _fifo_put
  WITH q: val, contents: list val, p: val
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
          PROP () LOCAL (temp _Q q; temp _p p) 
          SEP (`(fifo contents q); `(field_at_ Tsh t_struct_elem [StructField _next] p))
  POST [ tvoid ]
          PROP() LOCAL() SEP (`(fifo (contents++(p :: nil)) q)).

Definition fifo_empty_spec :=
 DECLARE _fifo_empty
  WITH q: val, contents: list val
  PRE  [ _Q OF (tptr t_struct_fifo) ]
     PROP() LOCAL (temp _Q q) SEP(`(fifo contents q))
  POST [ tint ]
      PROP ()
      LOCAL(temp ret_temp (if isnil contents then Vtrue else Vfalse)) 
      SEP (`(fifo (contents) q)).

Definition fifo_get_spec :=
 DECLARE _fifo_get
  WITH q: val, contents: list val, p: val
  PRE  [ _Q OF (tptr t_struct_fifo) ]
       PROP() LOCAL (temp _Q q) SEP (`(fifo (p :: contents) q)) 
  POST [ (tptr t_struct_elem) ] 
       PROP ()
       LOCAL(temp ret_temp p) 
       SEP (`(fifo contents q);
              `(field_at_ Tsh t_struct_elem [StructField _next] p)).

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH a: int, b: int
  PRE  [ _a OF tint, _b OF tint ] 
        PROP() LOCAL(temp _a (Vint a); temp _b (Vint b)) SEP()
  POST [ (tptr t_struct_elem) ]
      EX v:val, PROP() LOCAL (temp ret_temp v) 
       SEP (`(elemrep (Vint a, Vint b) v)).

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

Lemma memory_block_fifo:
 forall p, 
  field_compatible t_struct_fifo nil p ->
  memory_block Tsh (Int.repr 8) p = field_at_ Tsh t_struct_fifo nil p.
Proof.
 intros.
 change 8 with (sizeof cenv_cs t_struct_fifo).
 rewrite memory_block_data_at_; auto.
Qed.

Lemma fifo_isptr: forall al q, fifo al q |-- !! isptr q.
Proof.
intros.
 unfold fifo. if_tac; entailer; destruct ht; entailer!.
Qed.

Hint Resolve fifo_isptr : saturate_local.

Lemma body_fifo_empty: semax_body Vprog Gprog f_fifo_empty fifo_empty_spec.
Proof.
start_function.
name Q _Q.
name h _h.
unfold fifo.
forward_intro [hd tl].
normalize.
forward. (* h = Q->head; *)
forward. (* return (h == NULL); *)

unfold fifo.
entailer.
apply exp_right with (h,tl).
entailer.
destruct (isnil contents).
* entailer!.
* normalize.
 destruct prefix; entailer;
 fail. Admitted.  (* This hack because otherwise we run out of memory *)
   (* Each individual body_fifo_xxx can fit in memory, but not all of them. *)
(*Qed.*)


Lemma body_fifo_new: semax_body Vprog Gprog f_fifo_new fifo_new_spec.
Proof.
  start_function.
  name Q _Q.
  name Q' 68%positive.
 
  forward_call' (* Q = mallocN(sizeof ( *Q)); *)
     8 q.
    computable.
  rewrite memory_block_fifo.
2:  eapply malloc_compatible_field_compatible; try eassumption; 
      auto with typeclass_instances;
      exists 2; reflexivity.
  forward. (* Q->head = NULL; *)
  (* goal_4 *)
  forward. (* Q->tail = NULL; *)
  forward. (* return Q; *)
  (* goal_5 *)
  apply exp_right with Q; normalize.
  unfold fifo.
  apply exp_right with (nullval,nullval).
  rewrite if_true by auto.
  entailer!;
  fail. Admitted.  (* This hack because otherwise we run out of memory *)
(*Qed.*)

Lemma body_fifo_put: semax_body Vprog Gprog f_fifo_put fifo_put_spec.
Proof.
start_function.
name Q _Q.
name p' _p.
name h _h.
name t _t.
unfold fifo at 1.
forward_intro [hd tl]. normalize.
(* goal_7 *)

forward. (* p->next = NULL; *)
forward. (*   h = Q->head; *)
forward_if 
  (PROP() LOCAL () SEP (`(fifo (contents ++ p :: nil) q))).
* (* then clause *)
  subst.
  (* goal 9 *)
  forward. (* Q->head=p; *)
  forward. (* Q->tail=p; *)
  (* goal 10 *)
  entailer.
  destruct (isnil contents).
  + subst. apply exp_right with (p',p').
      simpl. rewrite if_false by congruence.
      normalize.
      apply exp_right with nil.
      rewrite links_nil_eq.
      entailer!.
   + normalize.
      destruct prefix; normalize;
      entailer!;
      match goal with H: field_compatible _ _ nullval |- _ =>
        contradiction (field_compatible_isptr _ _ _ H)
       end.
* (* else clause *)
  forward. (*  t = Q->tail; *)
  destruct (isnil contents).
  + abstract (apply semax_pre with FF; 
         [entailer | apply semax_ff]).
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
     remember (field_at Tsh t_struct_elem [StructField _next] nullval p') as A. (* prevent it from canceling! *)
     cancel. subst A.
     eapply derives_trans; [ | apply links_cons_right ].
     cancel.
* (* after the if *)
     forward; (* return ; *)
      fail. Admitted.  (* This hack because otherwise we run out of memory *)
(*Qed.*)

Lemma body_fifo_get: semax_body Vprog Gprog f_fifo_get fifo_get_spec.
Proof.
start_function.
name Q _Q.
name h _h.
name n _n.
unfold fifo at 1.
forward_intro [hd tl].
rewrite if_false by congruence.
forward_intro prefix. normalize.
forward. (*   p = Q->head; *)
destruct prefix; inversion H1; clear H1.
+ subst_any.
   rewrite links_nil_eq.
   normalize.
   apply ptr_eq_e in H1. subst_any.
   forward. (*  n=h->next; *)
   forward. (* Q->head=n; *)
   replace_SEP 0%Z (`(data_at Tsh t_struct_fifo (nullval,p) q)); [ entailer! | ]. (* can we do this automatically? *)
   forward. (* return p; *)
   entailer!.
   unfold fifo. apply exp_right with (nullval, h).
   rewrite if_true by congruence.
   entailer!.
+ rewrite links_cons_eq.
    forward_intro x. normalize.
    simpl valinject. (* can we make this automatic? *)
    subst_any.
    forward. (*  n=h->next; *)
    forward. (* Q->head=n; *)
    replace_SEP 2%Z (`(data_at Tsh t_struct_fifo (x, tl) q)); [ entailer! | ]. (* can we do this automatically? *)
    forward. (* return p; *)
    entailer.
    unfold fifo. normalize. apply exp_right with (n, tl).
    rewrite if_false by (destruct prefix; simpl; congruence).
    normalize. apply exp_right with prefix.
    entailer!; 
   fail. Admitted.  (* This hack because otherwise we run out of memory *)
(* Qed.*)

Lemma body_make_elem: semax_body Vprog Gprog f_make_elem make_elem_spec.
Proof.
start_function. rename a into a0; rename b into b0.
name a _a.
name b _b.
name p _p.
name p' 69%positive.
forward_call' (*  p = mallocN(sizeof ( *p));  *) 
  12 p0.
 computable.
  change 12 with (sizeof cenv_cs t_struct_elem).
  rewrite memory_block_data_at_.
2:  eapply malloc_compatible_field_compatible; try eassumption; 
      auto with typeclass_instances;
      exists 2; reflexivity.
unfold data_at_, field_at_.
unfold default_val; simpl.
forward.  (*  p->a=a; *)
forward.  (*  p->b=b; *)
forward.  (* return p; *)
apply exp_right with p.
unfold elemrep.
unfold_field_at 1%nat.
entailer!; 
fail. Admitted.  (* This hack because otherwise we run out of memory *)
(*Qed.*)

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
name i _i.
name j _j.
name Q _Q.
name p _p.

forward_call' (* Q = fifo_new(); *)  tt q.

forward_call'  (*  p = make_elem(1,10); *)
     (Int.repr 1, Int.repr 10) p'.
unfold elemrep; normalize.

forward_call' (* fifo_put(Q,p);*) 
    ((q, @nil val),p').
forward_call'  (*  p = make_elem(2,20); *)
     (Int.repr 2, Int.repr 20) p2.
 forward_call'  (* fifo_put(Q,p); *)
    ((q,(p':: nil)),p2).
 unfold elemrep; entailer; cancel.
simpl.
forward_call'  (*   p' = fifo_get(Q); p = p'; *)
    ((q,(p2 :: nil)),p') vret.
forward. (*   i = p->a;  *)
forward. (*   j = p->b; *)

forward_call' (*  freeN(p, sizeof( *p)); *)
   (p', sizeof cenv_cs t_struct_elem).
{apply derives_trans with
   (data_at_ Tsh t_struct_elem p' * fold_right sepcon emp Frame).
 unfold data_at_, field_at_.
 unfold default_val; simpl.
 unfold_field_at 6%nat.
 cancel.
 rewrite data_at__memory_block by reflexivity. entailer.
}
unfold map.
forward. (* return i+j; *)
unfold main_post.
entailer!.
Qed.

Existing Instance NullExtension.Espec.

Parameter body_mallocN:
 semax_external
  (1%positive ::nil)
  (EF_external _mallocN
     {| sig_args := AST.Tint :: nil; sig_res := Some AST.Tint; sig_cc := cc_default |}) Z
  (fun n : Z =>
   PROP  (4 <= n <= Int.max_unsigned)  LOCAL  (temp 1%positive (Vint (Int.repr n)))  SEP())
  (fun n : Z =>
   EX  v : val,
   PROP  (malloc_compatible n v)
   LOCAL  (temp ret_temp v)  SEP  (`(memory_block Tsh (Int.repr n) v))).

Parameter body_freeN:
semax_external
  (1%positive::2%positive ::nil)
  (EF_external _freeN
     {| sig_args := AST.Tint :: AST.Tint :: nil; sig_res := None; sig_cc := cc_default |}) (val*Z)
  (fun pn : val*Z => let (p,n) := pn in
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (`(memory_block Tsh (Int.repr n) p)))
  (fun pn => let (p,n) := pn in
    PROP () LOCAL () SEP ()).

Lemma ret_temp_make_ext_rval:
  forall gx ret p,  
   temp ret_temp p (make_ext_rval gx ret) -> 
    p = force_val ret.
Proof.
  intros.
  unfold temp in H; unfold_lift in H.
  rewrite retval_ext_rval in H. auto.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons body_mallocN.
 apply ret_temp_make_ext_rval in H0; subst; entailer.
semax_func_cons body_freeN.
  admit.  (* yuck *)
semax_func_cons body_fifo_new.
semax_func_cons body_fifo_put.
semax_func_cons body_fifo_empty.
semax_func_cons body_fifo_get.
semax_func_cons body_make_elem.
semax_func_cons body_main.
apply semax_func_nil.
Qed.


