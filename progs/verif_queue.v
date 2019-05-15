Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.list_dt. Import Links.
Require Import VST.progs.queue.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_elem := Tstruct _elem noattr.
Definition t_struct_fifo := Tstruct _fifo noattr.


Instance QS: listspec _elem _next (fun _ _ => emp).
Proof. eapply mk_listspec; reflexivity. Defined.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Definition Qsh : share := fst (Share.split extern_retainer).
Definition Qsh' := Share.lub (snd (Share.split extern_retainer)) Share.Rsh.

Lemma writable_share_Qsh': writable_share Qsh'.
Proof.
unfold writable_share, Qsh', Ews.
split.
*
rewrite Share.distrib1. rewrite glb_Lsh_Rsh, Share.lub_bot.
unfold extern_retainer.
intro. apply identity_share_bot in H.
destruct (Share.split Share.Lsh) eqn:?H.
pose proof (split_join _ _ _ H0).
simpl in *.
destruct (Share.split t) eqn:?H.
pose proof (split_join _ _ _ H2).
simpl in *.
destruct (Share.ord_spec1 t2 Share.Lsh) as [? _].
spec H4. apply leq_join_sub. apply sepalg.join_sub_trans with t; eexists; eauto.
rewrite Share.glb_commute,  <- H4 in H.
subst.
apply Share.split_nontrivial in H2; auto.
subst.
apply Share.split_nontrivial in H0; auto.
clear - H0.
unfold Share.Lsh in *.
destruct (Share.split Share.top) eqn:?H.
simpl in *; subst.
apply Share.split_nontrivial in H; auto.
apply Share.nontrivial; auto.
*
apply leq_join_sub.
apply Share.lub_upper2.
Qed.

Lemma readable_share_Qsh': readable_share Qsh'.
Proof.
apply writable_readable_share. apply writable_share_Qsh'.
Qed.

Lemma Qsh_Qsh': sepalg.join Qsh Qsh' Ews.
Proof.
unfold Qsh, Qsh', Ews.
destruct (Share.split extern_retainer) as [a b] eqn:?H.
simpl.
pose proof (split_join _ _ _ H).
destruct H0.
split.
rewrite Share.distrib1. rewrite H0.
rewrite Share.lub_commute, Share.lub_bot.
rewrite Share.glb_commute.
apply sub_glb_bot with extern_retainer.
apply leq_join_sub.
rewrite <- H1.
apply Share.lub_upper1.
unfold extern_retainer.
apply sub_glb_bot with Share.Lsh.
exists (snd (Share.split Share.Lsh)).
destruct (Share.split Share.Lsh) eqn:?H.
apply split_join; auto.
apply glb_Rsh_Lsh.
rewrite <- Share.lub_assoc.
rewrite H1.
auto.
Qed.

Lemma Qsh_not_readable: ~ readable_share Qsh.
Proof.
unfold Qsh.
apply writable_not_join_readable with Qsh';
 [ | apply writable_share_Qsh'].
exists Ews.
apply sepalg.join_comm.
apply Qsh_Qsh'.
Qed.

Hint Resolve Qsh_not_readable.


Lemma Qsh_nonempty: Qsh <> Share.bot.
Proof.
pose proof Qsh_Qsh'.
intro.
rewrite H0 in H.
apply sepalg.join_unit1_e in H; [ | apply bot_identity].
clear H0.
unfold Qsh', Ews in H.
apply (f_equal (Share.glb Share.Lsh)) in H.
rewrite !Share.distrib1 in H.
rewrite glb_Lsh_Rsh in H.
rewrite !Share.lub_bot in H.
destruct (Share.split extern_retainer) as [a b] eqn:?H.
simpl in *.
assert (Ha: a <> Share.bot). {
 intro.
 pose proof (Share.split_nontrivial _ _ _ H0).
 spec H2; auto.
 contradiction juicy_mem.extern_retainer_neq_bot.
}
apply split_join in H0.
destruct H0.
unfold extern_retainer in *.
destruct (Share.split Share.Lsh) as [c d] eqn:?H.
apply split_join in H2.
destruct H2.
rewrite <- H3 in *.
clear H3.
simpl in *.
subst c.
rewrite (Share.glb_commute _ b) in H.
rewrite Share.distrib1 in H.
rewrite Share.glb_commute in H2.
rewrite (Share.lub_commute a b) in H.
rewrite Share.glb_absorb in H.
rewrite Share.lub_absorb in H.
rewrite Share.lub_assoc in H.
rewrite <- Share.distrib2 in H.
rewrite Share.glb_commute in H.
rewrite Share.glb_absorb in H.
rewrite H in H0.
rewrite Share.lub_commute in H0.
rewrite Share.glb_absorb in H0.
contradiction.
Qed.

Hint Resolve Qsh_nonempty : valid_pointer.

Lemma Qsh_nonidentity: sepalg.nonidentity Qsh.
Proof.
  intro.
  apply identity_share_bot in H.
  apply Qsh_nonempty in H.
  auto.
Qed.

Hint Resolve Qsh_nonidentity : valid_pointer.

Lemma sub_Qsh_Ews: sepalg.join_sub Qsh Ews.
Proof.
unfold Qsh, Ews.
apply sepalg.join_sub_trans with extern_retainer.
destruct (Share.split extern_retainer) eqn:?H.
apply split_join in H. exists t0; auto.
apply leq_join_sub.
apply Share.lub_upper1.
Qed.

Hint Resolve sub_Qsh_Ews: valid_pointer.

Lemma field_at_list_cell_weak:
  forall sh i j p,
   readable_share sh ->
  field_at sh list_struct [StructField _a] i p *
  field_at sh list_struct [StructField _b] j p *
  field_at_ sh list_struct [StructField _next] p
  = list_cell QS sh (i,j) p *
  field_at_ sh list_struct [StructField _next] p.
Proof.
intros.
(* new version of proof, for constructive definition of list_cell *)
f_equal.
unfold field_at, list_cell.
autorewrite with gather_prop.
f_equal.
apply ND_prop_ext.
rewrite field_compatible_cons; simpl.
rewrite field_compatible_cons; simpl.
intuition.
+ left; auto.
+ right; left; auto.
Qed.

Lemma make_unmake:
 forall a b p,
 data_at Ews t_struct_elem (Vint a, (Vint b, Vundef)) p =
 field_at Qsh' t_struct_elem [StructField _a] (Vint a) p *
 field_at Qsh' t_struct_elem [StructField _b] (Vint b) p *
 list_cell QS Qsh (Vundef, Vundef) p *
 field_at_ Ews t_struct_elem [StructField _next] p.
Proof.
intros.
unfold_data_at (data_at _ _ _ _).
rewrite <- !sepcon_assoc.
match goal with |- ?A = _ => set (J := A) end.
unfold field_at_.
change (default_val (nested_field_type t_struct_elem [StructField _next])) with Vundef.
rewrite <- (field_at_share_join _ _ _ _ _ _ _ Qsh_Qsh').
rewrite <- !sepcon_assoc.
pull_left (field_at Qsh' t_struct_elem [StructField _next] Vundef p).
pull_left (field_at Qsh' t_struct_elem [StructField _b] (Vint b) p).
pull_left (field_at Qsh' t_struct_elem [StructField _a] (Vint a) p).
rewrite field_at_list_cell_weak  by apply readable_share_Qsh'.
match goal with |- _ = _ * _ * _ * ?A => change A
  with (field_at_ Qsh t_struct_elem [StructField _next] p)
end.
pull_left (list_cell QS Qsh (Vundef, Vundef) p).
rewrite join_cell_link with (psh:=Ews) by (auto; try apply Qsh_Qsh'; apply readable_share_Qsh').
subst J.
match goal with |- _ * _ * ?A = _ => change A
  with (field_at_ Ews t_struct_elem [StructField _next] p)
end.
rewrite field_at_list_cell_weak by auto.
rewrite sepcon_assoc.
f_equal.
unfold field_at_.
change (default_val (nested_field_type t_struct_elem [StructField _next])) with Vundef.
rewrite sepcon_comm.
symmetry.
apply (field_at_share_join _ _ _ t_struct_elem [StructField _next]
   _ p Qsh_Qsh').
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

Definition elemrep (rep: elemtype QS) (p: val) : mpred :=
  field_at Ews t_struct_elem [StructField _a] (fst rep) p *
  (field_at Ews t_struct_elem [StructField _b] (snd rep) p *
   (field_at_ Ews t_struct_elem [StructField _next]) p).

Definition fifo_body (contents: list val) (hd tl: val) :=
      (if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val,
              !!(contents = prefix++tl::nil)
            &&  (lseg QS Qsh Ews prefix hd tl
                   * list_cell QS Qsh (Vundef,Vundef) tl
                   * field_at Ews t_struct_elem [StructField _next] nullval tl)))%logic.

Definition fifo (contents: list val) (p: val) : mpred :=
  (EX ht: (val*val), let (hd,tl) := ht in
      !! is_pointer_or_null hd && !! is_pointer_or_null tl &&
      data_at Ews t_struct_fifo (hd, tl) p * malloc_token Ews t_struct_fifo p *
      fifo_body contents hd tl).

Definition fifo_new_spec :=
 DECLARE _fifo_new
  WITH gv: globals
  PRE  [  ]
       PROP() LOCAL(gvars gv) SEP (mem_mgr gv)
  POST [ (tptr t_struct_fifo) ]
    EX v:val, PROP() LOCAL(temp ret_temp v) SEP (mem_mgr gv; fifo nil v).

Definition fifo_put_spec :=
 DECLARE _fifo_put
  WITH q: val, contents: list val, p: val
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
          PROP () LOCAL (temp _Q q; temp _p p)
          SEP (fifo contents q;
                 list_cell QS Qsh (Vundef, Vundef) p;
                 field_at_ Ews t_struct_elem [StructField _next] p)
  POST [ tvoid ]
          PROP() LOCAL() SEP (fifo (contents++(p :: nil)) q).

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
  WITH q: val, contents: list val, p: val
  PRE  [ _Q OF (tptr t_struct_fifo) ]
       PROP() LOCAL (temp _Q q) SEP (fifo (p :: contents) q)
  POST [ (tptr t_struct_elem) ]
       PROP ()
       LOCAL(temp ret_temp p)
       SEP (fifo contents q;
              list_cell QS Qsh (Vundef, Vundef) p;
              field_at_ Ews t_struct_elem [StructField _next] p).

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH a: int, b: int, gv: globals
  PRE  [ _a OF tint, _b OF tint ]
        PROP() 
        LOCAL(temp _a (Vint a); temp _b (Vint b); gvars gv) 
        SEP(mem_mgr gv)
  POST [ (tptr t_struct_elem) ]
      @exp (environ->mpred) _ _ (fun p:val =>  (* EX notation doesn't work for some reason *)
       PROP()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv;
              field_at Qsh' list_struct [StructField _a] (Vint a) p;
              field_at Qsh' list_struct [StructField _b] (Vint b) p;
              list_cell QS Qsh (Vundef, Vundef) p;
              field_at_ Ews t_struct_elem [StructField _next] p;
              malloc_token Ews t_struct_elem p)).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]
       PROP() LOCAL (temp ret_temp (Vint (Int.repr (1+10)))) SEP(TT).

Definition Gprog : funspecs :=
  ltac:(with_library prog
    [surely_malloc_spec; fifo_new_spec; fifo_put_spec;
     fifo_empty_spec; fifo_get_spec; make_elem_spec;
     main_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     (t, gv).
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
entailer!.
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
* Intros prefix.
Exists prefix.
  assert_PROP (isptr hd).
    destruct prefix; entailer.
    rewrite lseg_cons_eq by auto. Intros y. subst v.
    entailer.
 destruct hd; try contradiction.
 entailer!.
Qed.

Lemma body_fifo_new: semax_body Vprog Gprog f_fifo_new fifo_new_spec.
Proof.
  start_function.
  forward_call (* Q = surely_malloc(sizeof ( *Q)); *)
      (t_struct_fifo, gv).
  split3;  simpl; auto; computable.
  Intros q.
  forward. (* Q->head = NULL; *)
  (* goal_4 *)
  forward. (* Q->tail = NULL; *)
  forward. (* return Q; *)
  (* goal_5 *)
  Exists q. unfold fifo, fifo_body. Exists (nullval,nullval).
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
  (PROP() LOCAL () SEP (fifo (contents ++ p :: nil) q))%assert.
* unfold fifo_body.
   if_tac; entailer.  (* typechecking clause *)
    (* entailer! should perhaps solve this one too *)
* (* then clause *)
  subst.
  (* goal 9 *)
  forward. (* Q->head=p; *)
  forward. (* Q->tail=p; *)
  (* goal 10 *)
  entailer.
  unfold fifo, fifo_body.
  destruct (isnil contents).
  + subst. Exists (p,p).
     simpl. rewrite if_false by congruence.
     Exists (@nil val).
      rewrite lseg_nil_eq by auto.
      entailer!.
   + Intros prefix.
      destruct prefix;
      entailer!.
      contradiction (field_compatible_isptr _ _ _ H7).
      rewrite lseg_cons_eq by auto. simpl.
      Intros y. saturate_local.
      contradiction (field_compatible_isptr _ _ _ H11).
* (* else clause *)
  forward. (*  t = Q->tail; *)
  unfold fifo_body.
  destruct (isnil contents).
  + Intros. contradiction H; auto.
  + Intros prefix.
     forward. (*  t->next=p; *)
  (* goal 12 *)
     forward. (* Q->tail=p; *)
  (* goal 13 *)
     entailer!.
     unfold fifo, fifo_body. Exists (hd, p).
     rewrite if_false by (clear; destruct prefix; simpl; congruence).
     Exists  (prefix ++ tl :: nil).
     entailer.
     match goal with
     | |- _ |-- _ * _ * ?AA => remember AA as A
     end.     (* prevent it from canceling! *)
     simpl sizeof.
     cancel. subst A.
     eapply derives_trans; [ |
       apply (lseg_cons_right_neq _ _ _ _ _ ((Vundef,Vundef) : elemtype QS));
        auto ].
     cancel.
* (* after the if *)
     forward. (* return ; *)
Qed.

Lemma body_fifo_get: semax_body Vprog Gprog f_fifo_get fifo_get_spec.
Proof.
start_function.
unfold fifo, fifo_body at 1.
Intros ht; destruct ht as [hd tl].
rewrite if_false by congruence.
Intros prefix.
forward.  (*   p = Q->head; *)
destruct prefix; inversion H; clear H.
+ subst_any.
   rewrite lseg_nil_eq by auto.
   Intros.
   subst_any.
   forward. (*  n=h->next; *)
   forward. (* Q->head=n; *)
   forward. (* return p; *)
   unfold fifo, fifo_body. Exists (nullval, tl).
   rewrite if_true by congruence.
   simpl sizeof; entailer!.
+ rewrite lseg_cons_eq by auto.
    Intros x.
    simpl @valinject. (* can we make this automatic? *)
    subst_any.
    forward. (*  n=h->next; *)
    forward. (* Q->head=n; *)
    forward. (* return p; *)
    unfold fifo, fifo_body. Exists (x, tl).
    rewrite if_false by (destruct prefix; simpl; congruence).
    Exists prefix.
    entailer!.
    apply derives_refl.
Qed.

Lemma body_make_elem: semax_body Vprog Gprog f_make_elem make_elem_spec.
Proof.
start_function. rename a into a0; rename b into b0.
forward_call (*  p = surely_malloc(sizeof ( *p));  *)
  (t_struct_elem, gv).
 split3; simpl; auto; computable.
 Intros p.
  forward.  (*  p->a=a; *)
  progress simpl.  (* this should not be necessary -- Qinxiang, please look *)
  forward.  (*  p->b=b; *)
  forward.  (* return p; *)
  Exists p.
  entailer!.
  rewrite make_unmake.
  apply derives_refl.
Qed.

Hint Resolve readable_share_Qsh'.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (create_mem_mgr gv).
forward_call (* Q = fifo_new(); *)  gv.
Intros q.

forward_call  (*  p = make_elem(1,10); *)
     (Int.repr 1, Int.repr 10, gv).
Intros p'.
forward_call (* fifo_put(Q,p);*)
    ((q, @nil val),p').

forward_call  (*  p = make_elem(2,20); *)
     (Int.repr 2, Int.repr 20, gv).
Intros p2.
simpl app.
 forward_call  (* fifo_put(Q,p); *)
    ((q,(p':: nil)),p2).
simpl app.
forward_call  (*   p' = fifo_get(Q); p = p'; *)
    ((q,(p2 :: nil)),p').
forward. (*   i = p->a;  *)
forward. (*   j = p->b; *)
forward_call (*  free(p, sizeof( *p)); *)
   (t_struct_elem, p', gv).
{
 assert_PROP (isptr p'); [entailer! | rewrite if_false by (intro; subst; contradiction) ].
 sep_apply (eq_sym (make_unmake (Int.repr 1) (Int.repr 10) p')).
 cancel.
}
forward. (* return i+j; *)
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


