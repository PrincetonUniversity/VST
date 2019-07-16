Require Import VST.floyd.proofauto.
Require Import fastpile.
Require Import spec_stdlib.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Definition tlist := Tstruct _list noattr.
Definition tpile := Tstruct _pile noattr.

Definition countrep (s: Z) (p: val) : mpred :=
  EX s':Z, !! (0 <= s /\ 0 <= s' <= Int.max_signed /\
                 (s <= Int.max_signed -> s'=s)) &&
  data_at Ews tpile (Vint (Int.repr s')) p.

Definition count_freeable (p: val) :=
   malloc_token Ews tpile p.

Lemma countrep_local_facts:
  forall s p,
   countrep s p |-- !! isptr p.
Proof.
intros.
unfold countrep.
Intros s'.
entailer!.
Qed.

Hint Resolve countrep_local_facts : saturate_local.

Lemma countrep_valid_pointer:
  forall s p,
   countrep s p |-- valid_pointer p.
Proof. 
 intros.
 unfold countrep. Intros s'.
 auto with valid_pointer.
Qed.
Hint Resolve countrep_valid_pointer : valid_pointer.

Local Open Scope assert.

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

Definition Pile_new_spec :=
 DECLARE _Pile_new
 WITH gv: globals
 PRE [ ] PROP() LOCAL(gvars gv) SEP(mem_mgr gv)
 POST[ tptr tpile ]
   EX p: val,
      PROP() LOCAL(temp ret_temp p)
      SEP(countrep 0 p; count_freeable p; mem_mgr gv).

Definition Pile_add_spec :=
 DECLARE _Pile_add
 WITH p: val, n: Z, s: Z, gv: globals
 PRE [ _p OF tptr tpile, _n OF tint  ]
    PROP(0 <= n <= Int.max_signed)
    LOCAL(temp _p p; temp _n (Vint (Int.repr n)); gvars gv)
    SEP(countrep s p; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL()
    SEP(countrep (n+s) p; mem_mgr gv).

Definition Pile_count_spec :=
 DECLARE _Pile_count
 WITH p: val, s: Z
 PRE [ _p OF tptr tpile  ]
    PROP()
    LOCAL(temp _p p)
    SEP(countrep s p)
 POST[ tint ]
   EX s':Z, 
      PROP(s <= Int.max_signed -> s'=s) 
      LOCAL(temp ret_temp (Vint (Int.repr s')))
      SEP(countrep s p).

Definition Pile_free_spec :=
 DECLARE _Pile_free
 WITH p: val, s: Z, gv: globals
 PRE [ _p OF tptr tpile  ]
    PROP()
    LOCAL(temp _p p; gvars gv)
    SEP(countrep s p; count_freeable p; mem_mgr gv)
 POST[ tvoid ]
    PROP() LOCAL() SEP(mem_mgr gv).

Definition ispecs := [surely_malloc_spec].
Definition specs := [Pile_new_spec; Pile_add_spec; Pile_count_spec; Pile_free_spec].

