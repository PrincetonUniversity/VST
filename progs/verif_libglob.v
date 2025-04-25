Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.progs.libglob.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(*  The LG module has two global variables of its own:
<<
int LG_n = 3;
struct foo {  int initialized;  int m; } LG_foo = {0};
>>
From the client's point of view, these variables are hidden
away in a separating conjuct of the form [LG.data n gv],
where [LG.data] is the name of the abstraction,
[n] is a client-visible parameter, and [gv] is the
global-variables table.

In Coq, the LG module defines three things:
 - [LG.data], of type [globals -> mpred] (possibly with some other parameters, in this case [n:Z])
 - [initialized_globals : globals -> mpred]
     This definition is supposed to match the extern initialized
     global variables, as processed by CompCert clightgen,
     for the initial state of LG's variables  [LG_n] and [LG_foo].
 - [initial],  which is a lemma showing that the extern 
      initialized global variables of the C-language LG module do 
      indeed form a legitimate initial state of the [LG.data _ gv]
      abstraction.
*)

Module Type LG_TYPE.
  Parameter data: Z -> globals -> mpred.
  Parameter initialized_globals: globals -> mpred.
  Axiom initial: forall gv, 
     initialized_globals gv |-- data 3 gv.
End LG_TYPE.

(* And here is an implementation of the LG module, satisfying
   this module type. *)

Module LG <: LG_TYPE. 

(* This is an _internal_ definition, not meant to be mentioned
    in proofs about _clients_ of the LG module.  It describes
    "known to be initialized" global LG data. *)
  Definition data_ok (n: Z) (gv: globals) : mpred :=
  !! (0 <= n <= Int.max_signed) &&
  data_at Ews tint (Vint (Int.repr n)) (gv _LG_n) *
  data_at Ews (Tstruct _foo noattr) (Vint Int.one, Vint (Int.repr n)) (gv _LG_foo).

(* This is an externally visible definition, describing global
    LG data whether initialized or not. *)
Definition data (n: Z) (gv: globals) : mpred :=
  data_ok n gv || 
   (!! (n=3) && 
    data_at Ews tint (Vint (Int.repr n)) (gv _LG_n) *
    data_at Ews (Tstruct _foo noattr) (Vint Int.zero, Vundef) (gv _LG_foo)).

(*  This describes the extern global variables of the LG.c file,
    as they would appear as processed by CompCert and Floyd. *)
Definition initialized_globals (gv: globals) := 
   !! (headptr (gv _LG_n)) &&
   !! (headptr (gv _LG_foo)) &&
   mapsto Ews tuint (offset_val 4 (gv _LG_foo))
          (Vint (Int.repr 0)) *
   data_at Ews tuint (Vint (Int.repr 0)) (gv _LG_foo) *
   data_at Ews tint (Vint (Int.repr 3)) (gv _LG_n).

(*  This lemma packages up the extern global variables of LG.c
   into the client-visible [data] abstraction.  It's a bit clumsy
   and verbose; it would be better to have better proof automation
   support for this kind of thing. *)
Lemma initial:
  forall gv, initialized_globals gv |-- data 3 gv.
Proof.
intros.
unfold initialized_globals, data.
rewrite !data_at_tuint_tint.
entailer!.
rewrite <- bi.or_intro_r.
cancel.
unfold_data_at (data_at _ (Tstruct _foo _) _ _).
rewrite field_at_data_at.
simpl.
rewrite field_compatible_field_address
  by auto with field_compatible.
simpl.  autorewrite with norm. cancel.
pose (x :=
field_at Ews (Tstruct _foo noattr) [
      StructField _m] (Vint (Int.repr 0)) (gv _LG_foo)).
apply derives_trans with x; subst x.
erewrite <- mapsto_field_at
  by auto with field_compatible.
simpl.
rewrite field_compatible_field_address
  by auto with field_compatible.
simpl. cancel.
cancel.
Qed.

End LG.

(* The [init] function is not meant to be called from clients directly.
    Thus it can use an _internal_ abstraction, LG.data_ok,
    in its specification. *)
Definition init_spec :=
 DECLARE _LG_init
  WITH n: Z, gv: globals
  PRE  []
        PROP ()
        PARAMS () GLOBALS (gv)
        SEP(LG.data n gv)
  POST [ tvoid ]
         PROP()
         RETURN ()
         SEP (LG.data_ok n gv).

(* The [bump] and [get] functions are meant to be called from
    client modules.  *)
Definition bump_spec :=
 DECLARE _LG_bump
  WITH n: Z, gv: globals
  PRE  []
        PROP (n < Int.max_signed)
        PARAMS () GLOBALS (gv)
        SEP(LG.data n gv)
  POST [ tvoid ]
         PROP()
         RETURN ()
         SEP (LG.data (n+1) gv).

Definition get_spec :=
 DECLARE _LG_get
  WITH n: Z, gv: globals
  PRE  []
        PROP ()
        PARAMS () GLOBALS (gv)
        SEP(LG.data n gv)
  POST [ tint ]
         PROP()
         RETURN (Vint (Int.repr n))
         SEP (LG.data n gv).

Definition client_spec :=
 DECLARE _client
  WITH n: Z, gv: globals
  PRE  []
        PROP (n < 1000000000)
        PARAMS () GLOBALS (gv)
        SEP(LG.data n gv)
  POST [ tint ]
         PROP()
         RETURN (Vint (Int.repr (n+2)))
         SEP (LG.data (n+2) gv).

Definition main_spec :=
  DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
     PROP() 
     RETURN (Vint (Int.repr 5))
     SEP(TT).
  
Definition Gprog : funspecs :=
    ltac:(with_library prog [
    init_spec; bump_spec; get_spec; client_spec; main_spec]).

Lemma body_init:  semax_body Vprog Gprog f_LG_init init_spec.
Proof.
start_function.
unfold LG.data.
unfold LG.data_ok.
rewrite bi.or_alt.
Intros b; destruct b.
*
Intros.
forward.
forward_if.
inv H0.
forward.
unfold LG.data_ok.
entailer!.
*
Intros.
forward.
forward_if.
forward.
forward.
unfold LG.data_ok.
entailer!!.
forward.
unfold LG.data_ok.
entailer!!.
Qed.

Lemma body_bump:  semax_body Vprog Gprog f_LG_bump bump_spec.
Proof.
start_function.
forward_call (n,gv).
unfold LG.data_ok.
Intros.
forward.
forward.
forward.
forward.
entailer!!.
unfold LG.data.
rewrite <- bi.or_intro_l.
unfold LG.data_ok.
entailer!.
Qed.

Lemma body_get:  semax_body Vprog Gprog f_LG_get get_spec.
Proof.
start_function.
forward_call (n,gv).
unfold LG.data_ok.
Intros.
forward.
forward_if.
*
forward.
unfold LG.data.
rewrite <- bi.or_intro_l.
unfold LG.data_ok.
entailer!!.
*
forward.
forward.
unfold LG.data.
rewrite <- bi.or_intro_l.
unfold LG.data_ok.
entailer!!.
Qed.


Lemma body_client: semax_body Vprog Gprog f_client client_spec.
Proof.
start_function.
forward_call (n,gv).
forward_call (n+1,gv).
replace (n+1+1) with (n+2) by lia.
forward_call (n+2,gv).
forward.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
sep_apply (LG.initial gv); auto.
forward_call (3,gv).
forward.
Qed.
