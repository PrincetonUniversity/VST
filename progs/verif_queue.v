Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.queue.

Local Open Scope logic.

Instance QS: listspec t_struct_elem _next. 
Proof. eapply mk_listspec; reflexivity. Defined.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Definition natural_alignment := 8.

Lemma natural_alignment_enough: forall t,
     type_is_by_value t = true ->
     legal_alignas_type t = true -> 
     (alignof t | 8).
Proof.
  intros.
  assert (1 | 8). exists 8. reflexivity.
  assert (2 | 8). exists 4. reflexivity.
  assert (4 | 8). exists 2. reflexivity.
  assert (8 | 8). exists 1. reflexivity.
  destruct t; try inversion H; simpl;
  unfold legal_alignas_type in H0; simpl in H0;
  destruct (attr_alignas a); inversion H0; [destruct i| | destruct f|]; assumption.
Qed.

Definition natural_align_compatible p :=
  match p with
  | Vptr b ofs => (natural_alignment | Int.unsigned ofs)
  | _ => False
  end.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: int
  PRE [ 1%positive OF tint]
     PROP (4 <= Int.unsigned n) 
     LOCAL (temp 1%positive (Vint n))
     SEP ()
  POST [ tptr tvoid ] 
     EX v: val,
     PROP (natural_align_compatible v; isptr v) 
          (* the isptr is redundant, just there to test the tactics *)
     LOCAL (temp ret_temp v) 
     SEP (`(memory_block Tsh n v)).

Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : int
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]  
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint n))
      SEP (`(memory_block Tsh n p))
  POST [ tvoid ]  
    PROP () LOCAL () SEP ().

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
  align_compatible t_struct_fifo p ->
  memory_block Tsh (Int.repr 8) p = field_at_ Tsh t_struct_fifo nil p.
Proof.
 intros.
 change 8 with (sizeof t_struct_fifo).
 rewrite memory_block_data_at_; auto.
 unfold data_at_, field_at_.
 rewrite data_at_field_at.
  reflexivity.
 cbv; reflexivity.
Qed.

Lemma list_cell_eq: forall sh elem,
  list_cell QS sh elem = 
   field_at sh t_struct_elem [StructField _a] (fst elem) * 
   field_at sh t_struct_elem [StructField _b] (snd elem). 
Proof. admit. Qed.

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
normalize. intros [hd tl]. normalize.
forward. (* h = Q->head; *)
forward. (* return (h == NULL); *)

unfold fifo.
entailer.
apply exp_right with (h,tl).
entailer.
destruct (isnil contents).
* entailer!.
* normalize.
 destruct prefix; entailer; elim_hyps; simpl; apply prop_right; auto.
Qed.

(*
Lemma A: forall v, is_int v \/ isptr v -> force_val (sem_cast tint tint v) = v.
intros.
simpl sem_cast.
unfold sem_cast_neutral.
destruct v; simpl in H; try tauto.
Qed.
*)

Lemma natural_align_compatible_t_struct_fifo:
  forall q, natural_align_compatible q -> align_compatible t_struct_fifo q.
Proof.
intros; hnf in H|-*.
destruct q; auto. hnf in H|-*.
unfold natural_alignment in *.
simpl in *.
destruct H as [z ?]. exists (z*2)%Z; simpl. rewrite <- Z.mul_assoc.
auto.
Qed.
Hint Resolve natural_align_compatible_t_struct_fifo.

Lemma natural_align_compatible_isptr:
  forall p, natural_align_compatible p -> isptr p.
Proof. intros; destruct p; simpl; intuition. Qed.
Hint Resolve natural_align_compatible_isptr : norm.

Lemma body_fifo_new: semax_body Vprog Gprog f_fifo_new fifo_new_spec.
Proof.
  start_function.
  name Q _Q.
  name Q' _Q'.
 
  forward_call' (Int.repr 8). (* Q = mallocN(sizeof ( *Q)); *)
  computable.
  rename vret into q.
(*
  forward_call (* Q' = mallocN(sizeof ( *Q)); *) 
    (Int.repr 8).
  (* goal_2 *)
  entailer!.
  after_call. (* This expression was strange; better now with clean_up_app_carefully called from after_call *)
  clear Q'0.
  apply (remember_value  (eval_id _Q')); intro q.
  apply semax_pre with
    (PROP (natural_align_compatible q; isptr q) LOCAL (`(eq q) (eval_id _Q')) 
    SEP (`(memory_block Tsh (Int.repr 8) q))); [entailer | ].
  normalize.
  forward.  (* Q = (struct fifo * ) Q'; *)
*)
  rewrite memory_block_fifo by auto.
  forward. (* Q->head = NULL; *)
  (* goal_4 *)

  forward. (* Q->tail = NULL; *)
  forward. (* return Q; *)
  (* goal_5 *)
  apply exp_right with Q; normalize.
  unfold fifo.
  apply exp_right with (nullval,nullval).
  rewrite if_true by auto.
  entailer!.
Qed.

Lemma body_fifo_put: semax_body Vprog Gprog f_fifo_put fifo_put_spec.
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
forward. (*   h = Q->head; *)
forward_if 
  (PROP() LOCAL () SEP (`(fifo (contents ++ p :: nil) q))).
 simpl typeof.
* (* then clause *)
  (* goal 9 *)
  forward. (* Q->head=p; *)
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
     remember (field_at Tsh t_struct_elem [StructField _next] nullval p') as A. (* prevent it from canceling! *)
     cancel. subst A. 
     eapply derives_trans; [ | apply links_cons_right ].
     cancel.
* (* after the if *)
    forward. (* return ; *)
Qed.

Lemma body_fifo_get: semax_body Vprog Gprog f_fifo_get fifo_get_spec.
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
    normalize. intro.
    normalize.
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
    entailer!.
Qed.

Lemma body_make_elem: semax_body Vprog Gprog f_make_elem make_elem_spec.
Proof.
start_function. rename a into a0; rename b into b0.
name a _a.
name b _b.
name p _p.
name p' _p'.
forward_call' (*  p = mallocN(sizeof ( *p));  *) 
  (Int.repr 12).
computable.
rename vret into p0.
eapply semax_pre0 with (PROP  ()
      LOCAL  (temp _a (Vint a0); temp _b (Vint b0); temp _p p0)
      SEP 
      (`(data_at_ Tsh t_struct_elem p0))).
  entailer!.
  rewrite <- memory_block_data_at_;
   [auto | reflexivity  | reflexivity | reflexivity
   | apply natural_align_compatible_t_struct_fifo; auto | compute; reflexivity].
unfold data_at_.
rewrite data_at_field_at.
forward.  (*  p->a=a; *)
forward.  (*  p->b=b; *)
forward.  (* return p; *)
apply exp_right with p.
unfold elemrep.
unfold_field_at 1%nat.
entailer!.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
name i _i.
name j _j.
name Q _Q.
name p _p.

forward_call' (* Q = fifo_new(); *)  tt.
rename vret into q.
(*
forward_call (* Q = fifo_new(); *) tt.
entailer!.
auto with closed.
after_call.
apply (remember_value (eval_id _Q)); intro q.
*)

forward_call'  (*  p = make_elem(1,10); *)
     (Int.repr 1, Int.repr 10).
rename vret into p'.
(*
forward_call (*  p = make_elem(1,10); *)
   (Int.repr 1, Int.repr 10).
entailer!.
auto with closed.
after_call.
apply (remember_value (eval_id _p)); intro p'.
*)
unfold elemrep; normalize.

forward_call' (* fifo_put(Q,p);*) 
    ((q, @nil val),p').
(*
forward_call (* fifo_put(Q,p);*)
    ((q, @nil val),p').
unfold elemrep; entailer!.
after_call.
simpl.
*)
forward_call'  (*  p = make_elem(2,20); *)
     (Int.repr 2, Int.repr 20).
rename vret into p2.
(*
forward_call (*  p = make_elem(2,20); *)
    (Int.repr 2, Int.repr 20).
unfold elemrep; entailer!.
auto with closed.
after_call.
 apply (remember_value (eval_id _p)); intro p2.
*)

 forward_call'  (* fifo_put(Q,p); *)
    ((q,(p':: nil)),p2).
 unfold elemrep; entailer; cancel.
simpl.
(*
 forward_call  (* fifo_put(Q,p); *)
    ((q,(p':: nil)),p2).
 unfold elemrep; entailer!.
after_call.
simpl.
*)
forward_call'  (*   p' = fifo_get(Q); p = p'; *)
    ((q,(p2 :: nil)),p').
subst vret.
(*
forward_call (*   p' = fifo_get(Q); p = p'; *)
  ((q,(p2 :: nil)),p').
 entailer!.
 auto 50 with closed.
after_call.
normalize.
 subst p1 p3.
*)
forward. (*   i = p->a;  *)
forward. (*   j = p->b; *)

forward_call' (*  freeN(p, sizeof( *p)); *)
   (p', Int.repr (sizeof t_struct_elem)).
{apply derives_trans with
   (data_at_ Tsh t_struct_elem p' * fold_right sepcon emp Frame).
 unfold data_at_.
 unfold_data_at 1%nat.
 cancel.
 rewrite data_at__memory_block by reflexivity. entailer.
}
unfold map.
(*
forward_call (*  freeN(p, sizeof( *p)); *)
   (p', Int.repr (sizeof t_struct_elem)).
 {
  entailer.
  change 12 with (sizeof t_struct_elem).
  eapply derives_trans; [ | apply sepcon_derives; [| apply derives_refl]].

  instantiate (1:= field_at_ Tsh t_struct_elem [StructField _next] p' *
   field_at Tsh t_struct_elem [StructField _a] (Vint (Int.repr 1)) p' *
   field_at Tsh t_struct_elem [StructField _b] (Vint (Int.repr 10)) p'). cancel.

  apply derives_trans with (data_at_ Tsh t_struct_elem p'). unfold data_at_. 
  unfold_data_at 1%nat; cancel.
  rewrite data_at__memory_block by reflexivity.
  apply andp_left2; apply derives_refl.
} after_call.
*)
forward. (* return i+j; *)
unfold main_post.
entailer!.
Qed.

Existing Instance NullExtension.Espec.

Parameter body_mallocN:
 semax_external
  (1%positive ::nil)
  (EF_external _mallocN
     {| sig_args := AST.Tint :: nil; sig_res := Some AST.Tint; sig_cc := cc_default |}) int
  (fun n : int =>
   PROP  (4 <= Int.unsigned n)  LOCAL  (temp 1%positive (Vint n))  SEP())
  (fun n : int =>
   EX  v : val,
   PROP  (natural_align_compatible v; isptr v)
   LOCAL  (temp ret_temp v)  SEP  (`(memory_block Tsh n v))).

Parameter body_freeN:
semax_external
  (1%positive::2%positive ::nil)
  (EF_external _freeN
     {| sig_args := AST.Tint :: AST.Tint :: nil; sig_res := None; sig_cc := cc_default |}) (val*int)
  (fun pn : val*int => let (p,n) := pn in
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint n))
      SEP (`(memory_block Tsh n p)))
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
 apply ret_temp_make_ext_rval in H1; subst; entailer.
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


