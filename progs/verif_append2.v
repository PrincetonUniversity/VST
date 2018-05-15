Require Import VST.floyd.proofauto.
Require Import VST.progs.append.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.


Fixpoint listrep (sh: share)
            (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_struct_list (h,y) x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Arguments listrep sh contents x : simpl never.

Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p=nullval <-> contents=nil)).
Proof.
intros.
revert p; induction contents; unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sh contents p,
   sepalg.nonidentity sh ->
   listrep sh contents p |-- valid_pointer p.
Proof.
 destruct contents; unfold listrep; fold listrep; intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto. simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_null: forall sh contents,
    listrep sh contents nullval = !! (contents=nil) && emp.
Proof.
destruct contents; unfold listrep; fold listrep.
normalize.
apply pred_ext.
Intros y. entailer. destruct H; contradiction.
Intros.
Qed.

Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.

Definition append_spec :=
 DECLARE _append
  WITH sh : share, contents : list int, x: val, y: val, s1: list val, s2: list val
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP(writable_share sh)
     LOCAL (temp _x x; temp _y y)
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep sh (s1++s2) r).

Definition Gprog : funspecs :=   ltac:(with_library prog [ append_spec ]).

Module Proof1.

Definition lseg (sh: share) (contents: list val) (x z: val) : mpred :=
  ALL cts2:list val, listrep sh cts2 z -* listrep sh (contents++cts2) x.

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
forward_if.
*
 subst x. rewrite listrep_null. normalize.
 forward.
 Exists y.
 entailer!.
*
 forward.
 destruct s1 as [ | v s1']; unfold listrep at 1; fold listrep.
 normalize.
 Intros u.
 remember (v::s1') as s1.
 forward.
 forward_while
      ( EX a: val, EX s1b: list val, EX t: val, EX u: val,
            PROP ()
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                   data_at sh t_struct_list (a,u) t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert.
+ (* current assertion implies loop invariant *)
   Exists v s1' x u.
   subst s1. entailer!. cancel_wand.
+ (* loop test is safe to execute *)
   entailer!.
+ (* loop body preserves invariant *)
   clear v Heqs1.
   destruct s1b; unfold listrep at 3; fold listrep. Intros. contradiction.
   Intros z.
   forward.
   forward.
   Exists (v,s1b,u0,z). unfold fst, snd.
   simpl app.
   entailer!.
   rewrite sepcon_comm.
   apply RAMIF_PLAIN.trans''.
   apply wand_sepcon_adjoint.
   forget (v::s1b++s2) as s3.
   unfold listrep; fold listrep; Exists u0; auto.
+ (* after the loop *)
   clear v s1' Heqs1.
   forward.
   forward.
   rewrite (proj1 H2 (eq_refl _)).
   Exists x.
   simpl app.
   clear.
   entailer!.
   unfold listrep at 3; fold listrep. normalize.
   pull_right (listrep sh (a :: s2) t -* listrep sh (s1 ++ s2) x).
   apply modus_ponens_wand'.
   unfold listrep at 2; fold listrep. Exists y; auto.
Qed.

End Proof1.

Module Proof2.

Definition lseg (sh: share) (contents: list val) (x z: val) : mpred :=
  ALL cts2:list val, listrep sh cts2 z -* listrep sh (contents++cts2) x.

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
forward_if.
*
 subst x. rewrite listrep_null. normalize.
 forward.
 Exists y.
 entailer!.
*
 forward.
 destruct s1 as [ | v s1']; unfold listrep; fold listrep. Intros; contradiction.
 Intros u.
 remember (v::s1') as s1.
 forward.
 forward_while
      (EX s1a: list val,  EX a: val, EX s1b: list val, EX t: val, EX u: val,
            PROP (s1 = s1a ++ a :: s1b)
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (lseg sh s1a x t;
                   data_at sh t_struct_list (a,u) t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert.
+ (* current assertion implies loop invariant *)
   Exists (@nil val) v s1' x u.  entailer!.
   unfold lseg. apply allp_right; intro. simpl. cancel_wand.
+ (* loop test is safe to execute *)
   entailer!.
+ (* loop body preserves invariant *)
   clear v Heqs1. subst s1.
   destruct s1b; unfold listrep; fold listrep. Intros; contradiction.
   Intros z.
   forward.
   forward.
   Exists (s1a++[a],v,s1b,u0,z). unfold fst, snd.
   rewrite !app_ass. simpl app.
   entailer!.
   unfold lseg.
   rewrite sepcon_comm.
   clear.
   apply RAMIF_Q.trans'' with (cons a).
   extensionality cts; simpl; rewrite app_ass; reflexivity.
   apply allp_right; intro. apply wand_sepcon_adjoint.
   unfold listrep at 2; fold listrep; Exists u0.  apply derives_refl.
 + (* after the loop *)
   forward. forward.
   Exists x. entailer!.
   destruct H3 as [? _]. specialize (H3 (eq_refl _)). subst s1b.
   unfold listrep at 1. normalize. rewrite H0. rewrite app_ass. simpl app.
   unfold lseg.
   rewrite sepcon_assoc.
   eapply derives_trans; [apply allp_sepcon1 | ]. apply allp_left with (a::s2).
   rewrite sepcon_comm.
   eapply derives_trans; [ | apply modus_ponens_wand].
   apply sepcon_derives; [ | apply derives_refl].
   unfold listrep at 2; fold listrep. Exists y; auto.
Qed.

End Proof2.

Module Proof3.  (*************** inductive lseg *******************)

Fixpoint lseg (sh: share)
            (contents: list val) (x z: val) : mpred :=
 match contents with
 | h::hs => !! (x<>z) && 
              EX y:val,
                data_at sh t_struct_list (h,y) x * lseg sh hs y z
 | nil => !! (x = z /\ is_pointer_or_null x) && emp
 end.

Arguments lseg sh contents x z : simpl never.

Lemma lseg_local_facts:
  forall sh contents p q,
     lseg sh contents p q |--
     !! (is_pointer_or_null p /\ is_pointer_or_null q /\ (p=q <-> contents=nil)).
Proof.
intros.
apply derives_trans with (lseg sh contents p q && !! (is_pointer_or_null p /\
        is_pointer_or_null q /\ (p = q <-> contents = []))).
2: entailer!.
revert p; induction contents; intros; simpl; unfold lseg; fold lseg.
entailer!.
intuition.
Intros y. Exists y.
eapply derives_trans.
apply sepcon_derives.
apply derives_refl.
apply IHcontents.
entailer!.
intuition congruence.
Qed.

Hint Resolve lseg_local_facts : saturate_local.

Lemma lseg_valid_pointer:
  forall sh contents p ,
   sepalg.nonidentity sh ->
   lseg sh contents p nullval |-- valid_pointer p.
Proof.
 destruct contents; unfold lseg; fold lseg; intros; normalize;
 auto with valid_pointer.
Qed.

Hint Resolve lseg_valid_pointer : valid_pointer.

Lemma lseg_eq: forall sh contents x,
    lseg sh contents x x = !! (contents=nil /\ is_pointer_or_null x) && emp.
Proof.
intros.
destruct contents; unfold lseg; fold lseg.
f_equal. f_equal. f_equal. apply prop_ext; intuition.
normalize.
apply pred_ext.
Intros y. entailer.
Intros.
Qed.

Lemma lseg_null: forall sh contents,
    lseg sh contents nullval nullval = !! (contents=nil) && emp.
Proof.
intros.
 rewrite lseg_eq.
 apply pred_ext.
 entailer!.
 entailer!.
Qed.

Lemma lseg_cons: forall sh (v u x: val) s,
   readable_share sh ->
 data_at sh t_struct_list (v, u) x * lseg sh s u nullval
 |-- lseg sh [v] x u * lseg sh s u nullval.
Proof.
intros.
     unfold lseg at 2. Exists u. 
     entailer.
     destruct s; unfold lseg at 1; fold lseg; entailer.
Qed.

Lemma lseg_cons': forall sh (v u x a b: val) ,
   readable_share sh ->
 data_at sh t_struct_list (v, u) x * data_at sh t_struct_list (a,b) u
 |-- lseg sh [v] x u * data_at sh t_struct_list (a,b) u.
Proof.
intros.
     unfold lseg. Exists u. 
     entailer.
Qed.

Lemma lseg_app': forall sh s1 s2 (a w x y z: val),
   readable_share sh ->
   lseg sh s1 w x * lseg sh s2 x y * data_at sh t_struct_list (a,z) y |--
   lseg sh (s1++s2) w y * data_at sh t_struct_list (a,z) y.
Proof.
 intros.
 revert w; induction s1; intro; simpl.
 unfold lseg at 1. entailer!.
 unfold lseg at 1 3; fold lseg. Intros j; Exists j.
 entailer.
 sep_apply (IHs1 j).
 cancel. 
Qed.

Lemma lseg_app_null: forall sh s1 s2 (w x: val),
   readable_share sh ->
   lseg sh s1 w x * lseg sh s2 x nullval |--
   lseg sh (s1++s2) w nullval.
Proof.
 intros.
 revert w; induction s1; intro; simpl.
 unfold lseg at 1. entailer!.
 unfold lseg at 1 3; fold lseg. Intros j; Exists j.
 entailer.
 sep_apply (IHs1 j).
 cancel.
Qed.

Lemma lseg_app: forall sh s1 s2 a s3 (w x y z: val),
   readable_share sh ->
   lseg sh s1 w x * lseg sh s2 x y * lseg sh (a::s3) y z |--
   lseg sh (s1++s2) w y * lseg sh (a::s3) y z.
Proof.
 intros.
 unfold lseg at 3 5; fold lseg.
 Intros u; Exists u. rewrite prop_true_andp by auto.
 sep_apply (lseg_app' sh s1 s2 a w x y u); auto.
 cancel.
Qed.

Lemma listrep_lseg_null :
 listrep = fun sh s p => lseg sh s p nullval.
Proof.
extensionality sh s p.
revert p.
induction s; intros.
unfold lseg, listrep; apply pred_ext; entailer!.
unfold lseg, listrep; fold lseg; fold listrep.
apply pred_ext; Intros y; Exists y; rewrite IHs; entailer!.
Qed.

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
revert POSTCONDITION; rewrite listrep_lseg_null; intro.
forward_if.
*
 subst x. rewrite lseg_null. Intros. subst.
 forward.
 Exists y.
 entailer!.
*
 forward.
 destruct s1 as [ | v s1']; unfold lseg at 1; fold lseg.
 Intros. contradiction H.
 Intros u.
 clear - SH.
 remember (v::s1') as s1.
 forward.
 forward_while
      (EX s1a: list val, EX a: val, EX s1b: list val, EX t: val, EX u: val,
            PROP (s1 = s1a ++ a :: s1b)
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (lseg sh s1a x t; 
                   data_at sh t_struct_list (a,u) t;
                   lseg sh s1b u nullval; 
                   lseg sh s2 y nullval))%assert.
 + (* current assertion implies loop invariant *)
     Exists (@nil val) v s1' x u.
     subst s1. rewrite lseg_eq.
     entailer.
(*     sep_apply (lseg_cons sh v u x s1'); auto. *)
 + (* loop test is safe to execute *)
     entailer!.
 + (* loop body preserves invariant *)
    destruct s1b; unfold lseg at 2; fold lseg.
    Intros. contradiction.
    Intros z.
    forward.
    forward.
    Exists (s1a++a::nil, v0, s1b,u0,z). unfold fst, snd.
    simpl app; rewrite app_ass.
    entailer.
    sep_apply (lseg_cons' sh a u0 t v0 z); auto.
    sep_apply (lseg_app' sh s1a [a] v0 x t u0 z); auto.
    cancel.
 + (* after the loop *)
    clear v s1' Heqs1.
    subst. rewrite lseg_eq. Intros. subst. 
    forward.
    forward.
    Exists x. 
    entailer!.
    sep_apply (lseg_cons sh a y t s2); auto.
    sep_apply (lseg_app_null sh [a] s2 t y); auto.
    rewrite app_ass.
    sep_apply (lseg_app_null sh s1a ([a]++s2) x t); auto.
Qed.

End Proof3.

