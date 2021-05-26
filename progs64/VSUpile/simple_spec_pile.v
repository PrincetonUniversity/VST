Require Import VST.floyd.proofauto.
Require Import pile.
Instance PileCompSpecs : compspecs. make_compspecs prog. Defined.
Require Import simple_spec_stdlib.
Require Import PileModel.

Definition tlist := Tstruct _list noattr.
Definition tpile := Tstruct _pile noattr.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val,
       !! (0 <= h <=  Int.max_signed) && 
      data_at Ews tlist (Vint (Int.repr h), y) x 
     * malloc_token Ews tlist x
     * listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil) /\ Forall (Z.le 0) sigma).
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

#[export] Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 destruct sigma; unfold listrep; fold listrep;
 intros; entailer!; auto with valid_pointer.
Qed.

#[export] Hint Resolve listrep_valid_pointer : valid_pointer.

Opaque listrep.

Definition pilerep (sigma: list Z) (p: val) : mpred :=
  EX x:val, data_at Ews tpile x p * listrep sigma x.

Lemma pilerep_local_facts: forall sigma p,
    pilerep sigma p |-- !! (isptr p /\ Forall (Z.le 0) sigma).
Proof.
intros. unfold pilerep. Intros x. entailer!.
Qed.

Lemma pilerep_valid_pointer: forall sigma p,
    pilerep sigma p |-- valid_pointer p.
Proof.
intros. unfold pilerep. Intros x. entailer!.
Qed.


Definition pile_freeable (p: val) : mpred :=
            malloc_token Ews tpile p.

#[export] Hint Resolve pilerep_local_facts : saturate_local.
#[export] Hint Resolve pilerep_valid_pointer : valid_pointer.

Local Open Scope assert.

Definition Pile_new_spec :=
 DECLARE _Pile_new
 WITH gv: globals
 PRE [ ] PROP() PARAMS() GLOBALS(gv) SEP(mem_mgr gv)
 POST[ tptr tpile ]
   EX p: val,
      PROP() LOCAL(temp ret_temp p)
      SEP(pilerep nil p; pile_freeable p; mem_mgr gv).

Definition Pile_add_spec :=
 DECLARE _Pile_add
 WITH p: val, n: Z, sigma: list Z, gv: globals
 PRE [ tptr tpile, tint  ]
    PROP(0 <= n <= Int.max_signed)
    PARAMS (p; Vint (Int.repr n)) GLOBALS (gv)
    SEP(pilerep sigma p; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(pilerep (n::sigma) p; mem_mgr gv).

Definition Pile_count_spec :=
 DECLARE _Pile_count
 WITH p: val, sigma: list Z
 PRE [ tptr tpile  ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS (p) GLOBALS ()
    SEP (pilerep sigma p)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(pilerep sigma p).

Definition Pile_free_spec :=
 DECLARE _Pile_free
 WITH p: val, sigma: list Z, gv: globals
 PRE [ tptr tpile  ]
    PROP()
    PARAMS (p) (GLOBALS (gv)
    SEP(pilerep sigma p; pile_freeable p; mem_mgr gv))
 POST[ tvoid ]
     PROP() LOCAL() SEP(mem_mgr gv).

Definition PileASI:funspecs := [ Pile_new_spec; Pile_add_spec; Pile_count_spec; Pile_free_spec].

