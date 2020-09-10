Require Import VST.floyd.proofauto.
Require Import pile.
Require Import spec_stdlib.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Global Open Scope funspec_scope.


Definition tlist := Tstruct _list noattr.
Definition tpile := Tstruct _pile noattr.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val,
       !! (0 <= h <=  Int.max_signed) && 
      data_at Ews tlist (Vint (Int.repr h), y) x 
     * malloc_token Ews tlist x
     *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p 
      /\ (p=nullval <-> sigma=nil)
       /\ Forall (Z.le 0) sigma).
Proof.
intros.
revert p; induction sigma; 
  unfold listrep; fold listrep; intros.
  entailer!; intuition.
Intros y. entailer!.
split.
split; intro. subst p. destruct H0; contradiction. discriminate.
constructor; auto. lia.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 destruct sigma; unfold listrep; fold listrep;
 intros; entailer!; auto with valid_pointer.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Definition pilerep (sigma: list Z) (p: val) : mpred :=
  EX x:val, data_at Ews tpile x p 
             * listrep sigma x.

Definition pile_freeable (p: val) : mpred :=
            malloc_token Ews tpile p.

Lemma pilerep_local_facts:
  forall sigma p,
   pilerep sigma p |-- !! (isptr p /\ Forall (Z.le 0) sigma).
Proof.
intros.
unfold pilerep.
Intros q.
entailer!.
Qed.

Hint Resolve pilerep_local_facts : saturate_local.

Lemma pilerep_valid_pointer:
  forall sigma p,
   pilerep sigma p |-- valid_pointer p.
Proof. 
 intros.
 unfold pilerep. Intros x.
 entailer!; auto with valid_pointer.
Qed.
Hint Resolve pilerep_valid_pointer : valid_pointer.

Local Open Scope assert.

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vint (Int.repr (sizeof t))) GLOBALS(gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition Pile_new_spec :=
 DECLARE _Pile_new
 WITH gv: globals
 PRE [ ] PROP() PARAMS() GLOBALS(gv) SEP(mem_mgr gv)
 POST[ tptr tpile ]
   EX p: val,
      PROP() RETURN(p)
      SEP(pilerep nil p; pile_freeable p; mem_mgr gv).

Definition Pile_add_spec :=
 DECLARE _Pile_add
 WITH p: val, n: Z, sigma: list Z, gv: globals
 PRE [ tptr tpile, tint  ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (p; Vint (Int.repr n)) GLOBALS(gv)
    (SEP(pilerep sigma p; mem_mgr gv))
 POST[ tvoid ]
    PROP() RETURN()
    SEP(pilerep (n::sigma) p; mem_mgr gv).

Definition sumlist : list Z -> Z := List.fold_right Z.add 0.

Definition Pile_count_spec :=
 DECLARE _Pile_count
 WITH p: val, sigma: list Z
 PRE [ tptr tpile  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS (p)
    SEP (pilerep sigma p)
 POST[ tint ]
      PROP() 
      RETURN (Vint (Int.repr (sumlist sigma)))
      SEP(pilerep sigma p).

Definition Pile_free_spec :=
 DECLARE _Pile_free
 WITH p: val, sigma: list Z, gv: globals
 PRE [ tptr tpile  ]
    PROP()
    PARAMS(p) GLOBALS(gv)
    (SEP(pilerep sigma p; pile_freeable p; mem_mgr gv))
 POST[ tvoid ]
     PROP() RETURN() SEP(mem_mgr gv).

Definition ispecs := [surely_malloc_spec].
Definition specs := [Pile_new_spec; Pile_add_spec; Pile_count_spec; Pile_free_spec].

(*
(*Clients -- apile.v and onepile.v -- also need these lemmas:*)
Lemma pile_new_aux gx x ret:
(EX p : val, PROP ( )  RETURN (p)  SEP (pilerep [] p; pile_freeable p; mem_mgr x))%assert (make_ext_rval gx ret)
  |-- !! is_pointer_or_null (force_val ret).
Proof.
 rewrite exp_unfold. Intros p.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 destruct H; unfold_lift in H. rewrite retval_ext_rval in *.
 subst p. renormalize. entailer!.
Qed.

Lemma pile_count_aux gx l v ret:
  (PROP ( )  LOCAL (temp ret_temp (Vint (Int.repr (sumlist l))))  SEP (pilerep l v)) (make_ext_rval gx ret)
  |-- !! is_int I32 Signed (force_val ret).
Proof.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 destruct H; unfold_lift in H. rewrite retval_ext_rval in *.
 rewrite <- H. renormalize. 
Qed.
*)