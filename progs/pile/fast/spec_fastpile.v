Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.
Global Open Scope funspec_scope.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tpile := Tstruct _pile noattr.

Definition sumlist : list Z -> Z := List.fold_right Z.add 0.

Definition pilerep (sigma: list Z) (p: val) : mpred :=
 EX s:Z, !! (0 <= s <= Int.max_signed /\
   Forall (Z.le 0) sigma /\
  (0 <= sumlist sigma <= Int.max_signed -> s=sumlist sigma))
   &&  data_at Ews tpile (Vint (Int.repr s)) p.

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
       PARAMS (Vint (Int.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition Pile_new_spec :=
 DECLARE _Pile_new
 WITH gv: globals
 PRE [ ] PROP() PARAMS () GLOBALS (gv) SEP(mem_mgr gv)
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
 PRE [ tptr tpile ]
    PROP(0 <= sumlist sigma <= Int.max_signed)
    PARAMS (p) GLOBALS ()
    SEP(pilerep sigma p)
 POST[ tint ]
      PROP() 
      LOCAL(temp ret_temp (Vint (Int.repr (sumlist sigma))))
      SEP(pilerep sigma p).

Definition Pile_free_spec :=
 DECLARE _Pile_free
 WITH p: val, sigma: list Z, gv: globals
 PRE [ tptr tpile  ]
    PROP()
    PARAMS (p) GLOBALS (gv)
    SEP(pilerep sigma p; pile_freeable p; mem_mgr gv)
 POST[ tvoid ]
      PROP() LOCAL() SEP(mem_mgr gv).

Definition ispecs := [surely_malloc_spec].
Definition specs := [Pile_new_spec; Pile_add_spec; Pile_count_spec; Pile_free_spec].

