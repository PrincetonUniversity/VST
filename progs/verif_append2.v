Require Import floyd.proofauto.
Require Import progs.append.
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

Definition lseg (sh: share) (contents: list val) (x z: val) : mpred :=
  ALL cts2:list val, listrep sh cts2 z -* listrep sh (contents++cts2) x.

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
      (EX s1b: list val, EX t: val, EX u: val, EX a: val,
            PROP () 
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x; 
                   data_at sh t_struct_list (a,u) t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert.
 + Exists s1' x u v.
     subst s1. entailer!. cancel_wand.
 + entailer!.
 + clear v Heqs1.
    destruct s1b; unfold listrep at 3; fold listrep. Intros. contradiction.
    Intros z.
    forward.
    forward.
    Exists (s1b,u0,z,v). unfold fst, snd.
    simpl app.
    entailer!.
    rewrite sepcon_comm.
    apply RAMIF_PLAIN.trans''.
    apply wand_sepcon_adjoint. 
    forget (v::s1b++s2) as s3. 
    unfold listrep; fold listrep; Exists u0; auto.
 +
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


Lemma body_append2: semax_body Vprog Gprog f_append append_spec.
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
      (EX s1a: list val, EX s1b: list val, EX t: val, EX u: val, EX a: val,
            PROP (s1 = s1a ++ a :: s1b) 
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (lseg sh s1a x t; 
                   data_at sh t_struct_list (a,u) t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert.
 + Exists (@nil val) s1' x u v.  entailer!.
     unfold lseg. apply allp_right; intro. simpl. cancel_wand. 
 + entailer!.
 + clear v Heqs1. subst s1. 
    destruct s1b; unfold listrep; fold listrep. Intros; contradiction.
    Intros z.
    forward.
    forward.
    Exists (s1a++[a],s1b,u0,z,v). unfold fst, snd.
    rewrite !app_ass. simpl app.
    entailer!.
    unfold lseg.
    rewrite sepcon_comm.
    clear.
   apply RAMIF_Q.trans'' with (cons a).
   extensionality cts; simpl; rewrite app_ass; reflexivity.
   apply allp_right; intro. apply wand_sepcon_adjoint. 
   unfold listrep at 2; fold listrep; Exists u0.  auto.
 +
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