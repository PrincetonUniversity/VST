Require Import veric.base.
Require Import compcert.Events.


(* A "core semantics represents" a fairly traditional,
   sequential, small step semantics of computation.  They
   are designed to cooperate with "extensions"
   which give semantics to primtive constructs not defined
   by the extensible semantics (e.g., external function calls).

   The [G] type parameter is the type of global environments,
   the type [C] is the type of core states, and the type [E]
   is the type of extension requests.  The [at_external]
   function gives a way to determine when the sequential
   execution is blocked on an extension call, and to extract
   the data necessary to execute the call.  [after_external]
   give a way to inject the extension call results back into
   the sequential state so execution can continue.
   
   [make_initial_core] produces the core state corresponding
   to an entry point of the program.  The arguments are the
   program's genv, a pointer to the function to run, and
   the arguments for that function.

   The [safely_halted] predicate indicates when a program state
   has reached a halted state, and what it's exit code is
   when it has reached such a state.

   [corestep] is the fundamental small-step relation for
   the sequential semantics.

   The remaining properties give basic sanity properties which constrain
   the behavior of programs.
    1) a state cannot be both blocked on an extension call
        and also step,
    2) a state cannot both step and be halted
    3) a state cannot both be halted and blocked on an external call
 *)
Record CoreSemantics {G C M:Type} : Type :=
  { make_initial_core : G -> val -> list val -> option C
  ; at_external : C -> option (external_function * list val)
  ; after_external : val -> C -> option C
  ; safely_halted : G -> C -> option int (*maybe delete this, too?*)
  ; corestep : G -> C -> M -> C -> M -> Prop

  ; corestep_not_at_external:
       forall ge m q m' q', corestep ge q m q' m' -> at_external q = None

  ; corestep_not_halted :
       forall ge m q m' q', corestep ge q m q' m' -> safely_halted ge q m = None

  ; at_external_halted_excl :
       forall ge q m, at_external q = None \/ safely_halted ge q m = None
  }.
Implicit Arguments CoreSemantics [].

(* Definition of multistepping. *)
Section corestepN.
  Context {G C M E:Type} (Sem:CoreSemantics G C M E) (ge:G).

  Fixpoint corestepN (n:nat) : C -> M -> C -> M -> Prop :=
    match n with
    | O => fun c m c' m' => (c,m) = (c',m')
    | S n => fun c1 m1 c3 m3 => exists c2, exists m2,
               corestep Sem ge c1 m1 c2 m2 /\
               corestepN n c2 m2 c3 m3
    end.

  Lemma corestepN_add : forall n m c1 m1 c3 m3,
    corestepN (n+m) c1 m1 c3 m3 <->
    exists c2, exists m2,
      corestepN n c1 m1 c2 m2 /\
      corestepN m c2 m2 c3 m3.
  Proof.
    induction n; simpl; intuition.
    firstorder. firstorder.
    inv H. auto.
    decompose [ex and] H. clear H.
    destruct (IHn m x x0 c3 m3).
    apply H in H2. 
    decompose [ex and] H2. clear H2.
    repeat econstructor; eauto.
    decompose [ex and] H. clear H.
    exists x1. exists x2; split; auto.
    destruct (IHn m x1 x2 c3 m3). 
    eauto.
  Qed.

  Definition corestep_plus c m c' m' :=
    exists n, corestepN (S n) c m c' m'.

  Definition corestep_star c m c' m' :=
    exists n, corestepN n c m c' m'.
End corestepN.

(* A minimal preservation property we sometimes require.
 *)
Definition mem_forward (m1 m2:mem) :=
  (forall b, Mem.valid_block m1 b ->
      Mem.valid_block m2 b /\ 
       forall ofs, Mem.perm m1 b ofs Max = Mem.perm m2 b ofs Max).

(* This predicate restricts what coresteps are allowed
   to do.  Essentially, a corestep can only store, allocacte
   and free, and must do so respecting permissions.
 *)
Definition allowed_core_modification (m1 m2:mem) :=
  mem_forward m1 m2 /\
  (forall b ofs p,
    Mem.perm m1 b ofs Cur p ->
    (Mem.perm m2 b ofs Cur p) \/
    (Mem.perm m1 b ofs Cur Freeable /\ forall p', ~Mem.perm m2 b ofs Cur p')) /\
  (forall b ofs p,
    Mem.valid_block m1 b ->
    Mem.perm m2 b ofs Cur p ->
    Mem.perm m1 b ofs Cur p) /\
  (forall b ofs' n vs,
    Mem.loadbytes m1 b ofs' n = Some vs ->
      (Mem.loadbytes m2 b ofs' n = Some vs) \/
      (exists ofs, ofs' <= ofs < ofs' + n /\ Mem.perm m1 b ofs Cur Writable)).


(* The kinds of extensible semantics used by CompCert.  Memories are
   CompCert memories and external requests must contain external functions.
 *)
Record CompcertCoreSem {G C} :=
{ csem :> CoreSemantics G C mem

; csem_corestep_fun: forall ge m q m1 q1 m2 q2, 
       corestep csem ge q m q1 m1 ->
       corestep csem ge q m q2 m2 -> 
          (q1, m1) = (q2, m2)

; csem_allowed_modifications :
    forall ge c m c' m',
      corestep csem ge c m c' m' ->
      allowed_core_modification m m'
}.
Implicit Arguments CompcertCoreSem [ ].


Lemma corestepN_fun (G C E:Type) (CSem:CompcertCoreSem G C E) :
  forall ge n c m c1 m1 c2 m2,
    corestepN CSem ge n c m c1 m1 ->
    corestepN CSem ge n c m c2 m2 ->
    (c1,m1) = (c2,m2).
Proof.
  induction n; simpl; intuition (try congruence).
  decompose [ex and] H. clear H.
  decompose [ex and] H0. clear H0.
  assert ((x,x0) = (x1,x2)).
  eapply csem_corestep_fun; eauto.
  inv H0.
  eapply IHn; eauto.
Qed.

 (* A "forward simulation structure" generalizes and axiomatizes
    what it means for memories, values and addresses to "match".
    We want to include the three matching relations used in
    CompCert (equality, extension and injection) and allow
    for composition in a natural way.

    A key techincal trick is to use a parameterized type of "data"
    which gives some witness to the match.  This generalized the
    meminj used for memory injections and is crucial to get
    composition to work.

    There is a fair amount of overlap between the axioms relating
    to matching addresses and the axioms relating to matching pointer
    values.  This is because transitioning between the two is
    nontrivial.  The transition requires translating between
    unlimited precision integers and 32-bit integers.  This is only
    sound if no addition overflow has occured, which we know only
    if the pointer value corresponts to a valid pointer in
    some appropriately matching memory.  So, similar axioms are
    required on both sides of the boundary. 

    The "big" lemmas at the end of the record give ways for
    external function implementations to perform memory operations
    in a controlled way.  Basically, the four major memory operations
    are allowed.  When the same operation is called in related
    memories with related arguments, one obtains related results.

    BUG: currently, there is no way for external calls to change
    permissions, which is necessary for, e.g., lock and unlock.
    The memory model should probably expose a "change_perm"
    operation which is intended only for use by external functions
    and initilization.
  *)

(* Matching for lists of values with their types *)
Inductive match_vals {D} (struct:ForwardSimulationStructure D) (d:D) :
  (list typ) -> (list val) -> (list val) -> Prop :=
| match_vals_nil : match_vals struct d nil nil nil
| match_vals_cons : forall t ts v vs y ys,
  match_val struct d t v y ->
  match_vals struct d ts vs ys ->
  match_vals struct d (t::ts) (v::vs) (y::ys).


Inductive entry_points_compose: list (val*val*signature) -> list (val*val*signature) -> list (val*val*signature) -> Prop :=
| EPC1: forall v1 v2 v3 sig r1 r2 r3, 
                   entry_points_compose r1 r2 r3 ->
                   entry_points_compose ((v1,v2,sig)::r1) ((v2,v3,sig)::r2) ((v1,v3,sig)::r3)
| EPC0: entry_points_compose nil nil nil.

 
(* Here we present a module type which expresses the sort of forward simulation
   lemmas we have avalaible.  The idea is that these lemmas would be used in
   the individual compiler passes and the composition lemma would be used
   to build the main lemma.
 *)
Module Type SIMULATIONS.

Axiom allowed_core_modification_refl : forall m,
  allowed_core_modification m m.

Axiom allowed_core_modification_trans : forall m1 m2 m3,
  allowed_core_modification m1 m2 ->
  allowed_core_modification m2 m3 ->
  allowed_core_modification m1 m3.

Axiom free_allowed_core_mod : forall m1 b lo hi m2,
  Mem.free m1 b lo hi = Some m2 ->
  allowed_core_modification m1 m2.

Axiom alloc_allowed_core_mod : forall m1 lo hi m2 b,
  Mem.alloc m1 lo hi = (m2,b) ->
  allowed_core_modification m1 m2.

Axiom store_allowed_core_mod : forall m1 chunk v b ofs m2,
  Mem.store chunk m1 b ofs v = Some m2 ->
  allowed_core_modification m1 m2.

Hint Resolve 
  allowed_core_modification_refl
  allowed_core_modification_trans
  free_allowed_core_mod
  alloc_allowed_core_mod
  store_allowed_core_mod : allowed_mod.

(* First a forward simulation for passes which do not alter the memory
     layout at all. *)
Section Forward_simulation_equals. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record forward_simulation_equals :=
  { core_data:Type;

    match_core : core_data -> C1 -> C2 -> Prop;
    core_ord : C1 -> C1 -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m st1' m', corestep Sem1 ge1 st1 m st1' m' ->
      forall d st2, match_core d st1 st2 ->
        exists st2', exists d',
          match_core d' st1' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            corestep_star Sem2 ge2 st2 m st2' m' /\
            core_ord st1' st1);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals,
          Forall2 (Val.has_type) vals (sig_args sig) ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals = Some c2 /\
            match_core cd c1 c2;

    core_halted : forall cd c1 c2 (v:int),
      match_core cd c1 c2 ->
      safely_halted Sem1 ge1 c1 = Some v ->
      safely_halted Sem2 ge2 c2 = Some v;

    core_at_external : 
      forall d st1 st2 args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,args) ->
        exists e2,
          at_external Sem2 st2 = Some (e,args) /\
          Forall2 Val.has_type args (sig_args (ef_sig e));

    core_after_external :
      forall d st1 st2 ret e args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e,args) ->
        at_external Sem2 st2 = Some (e,args) ->
        Forall2 Val.has_type args (sig_args (ef_sig e)) ->
        Val.has_type ret (proj_sig_res sig) ->
        exists st1', exists st2', exists d',
          after_external Sem1 ret st1 = Some st1' /\
          after_external Sem2 ret st2 = Some st2' /\
          match_core d' st1' st2'
  }.

End Forward_simulation_equals. 

(* An axiom for passes that use memory injections. *)
Section Forward_simulation_inject. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record forward_simulation_inject := {
    core_data : Type;

    match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : C1 -> C1 -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord st1' st1);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall j vals vals' m1 m2,
          Forall2 (val_inject j) vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.inject j m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd j c1 m1 c2 m2;

    core_halted : forall cd j c1 m1 c2 m2 (v1:int),
      match_state cd j c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 = Some v1 ->
        (safely_halted Sem2 ge2 c2 = Some v1 /\
         Mem.inject j m1 m2); (*conjunct Mem.inject j m1 m2 could maybe deleted here?*)

    core_at_external : 
      forall cd j st1 m1 st2 m2 e vals1,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists vals2,
          Mem.inject j m1 m2 /\
          Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);
  
    core_after_external :
      forall cd j j' st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2',
        match_state cd j st1 m1 st2 m2 ->
        Mem.inject j m1 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        at_external Sem2 st2 = Some (e,vals2) ->
        Forall2 (val_inject j) vals1 vals2 ->
      
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret1 ret2 ->

        mem_unchanged_on (loc_unmapped j) m1 m1' ->
        mem_unchanged_on (loc_out_of_reach j m1) m2 m2' ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) ->
        Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'
    }.

End ForwardSimulation_Inject.

(* Next, an axiom for passes that allow the memory to undergo extension. *)
Section Forward_simulation_extends. 
  Context {G1 C1 G2 C2:Type}
          {Sem1 : CompcertCoreSem G1 C1}
          {Sem2 : CompcertCoreSem G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Record forward_simulation_extend := {
    core_data : Type;

    match_state : core_data -> C1 -> mem -> C2 -> mem -> Prop;
    core_ord : C1 -> C1 -> Prop;
    core_ord_wf : well_founded core_ord;

    core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 m2,
        match_state cd st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd',
          match_state cd' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord st1' st1);

    core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2;

    core_halted : 
      forall cd st1 m1 st2 m2 (v:int),
        match_state cd st1 m1 st2 m2 ->
        safely_halted Sem1 ge1 st1 = Some v ->
          safely_halted Sem2 ge2 st2 = Some v /\
          Mem.extends m1 m2;

    core_at_external : 
      forall cd st1 m1 st2 m2 e vals1,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,vals2);

    core_after_external :
      forall cd st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2',
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        at_external Sem2 st2 = Some (e,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) ->
      
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->
        mem_unchanged_on (loc_out_of_bounds m1) m2 m2' ->
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res (ef_sig e)) ->

        exists st1', exists st2', exists cd',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2'
   }.
End ForwardSimulation_Extend.

  (* An axiom stating that inject forward simulations compose *)
  Axiom forward_simulation_inject_inject_compose : forall
    (G1 C1 G2 C2 G3 C3:Type)
    (Sem1 : CompcertCoreSem G1 C1)
    (Sem2 : CompcertCoreSem G2 C2)
    (Sem3 : CompcertCoreSem G3 C3)

    (ge1 : G1)
    (ge2 : G2)
    (ge3 : G3)

    (entry_points12 : list (val*val*signature))
    (entry_points23 : list (val*val*signature))

    (FSim12 : ForwardSimulation_inject Sem1 Sem2 ge1 ge2 entry_points12)
    (FSim23 : ForwardSimulation_inject Sem2 Sem3 ge2 ge3 entry_points23)

    (entry_points13: list (val*val*signature))
    (EPC: entry_points_compose entry_points12 entry_points23 entry_points13),

    ForwardSimulation_inject Sem1 Sem3 ge1 ge3 entry_points13.

  (* An axiom stating that extend_inject forward simulations compose *)
  Axiom forward_simulation_extend_inject_compose : forall
    (G1 C1 G2 C2 G3 C3:Type)
    (Sem1 : CompcertCoreSem G1 C1)
    (Sem2 : CompcertCoreSem G2 C2)
    (Sem3 : CompcertCoreSem G3 C3)

    (ge1 : G1)
    (ge2 : G2)
    (ge3 : G3)

    (entry_points12 : list (val*val*signature))
    (entry_points23 : list (val*val*signature))

    (FSim12 : ForwardSimulation_extend Sem1 Sem2 ge1 ge2 entry_points12)
    (FSim23 : ForwardSimulation_inject Sem2 Sem3 ge2 ge3 entry_points23)

    (entry_points13: list (val*val*signature))
    (EPC: entry_points_compose entry_points12 entry_points23 entry_points13),

    ForwardSimulation_inject Sem1 Sem3 ge1 ge3 entry_points13.

  (* An axiom stating that equal inject forward simulations compose *)
  Axiom forward_simulation_equal_inject_compose : forall
    (G1 C1 G2 C2 G3 C3:Type)
    (Sem1 : CompcertCoreSem G1 C1)
    (Sem2 : CompcertCoreSem G2 C2)
    (Sem3 : CompcertCoreSem G3 C3)

    (ge1 : G1)
    (ge2 : G2)
    (ge3 : G3)

    (entry_points12 : list (val*val*signature))
    (entry_points23 : list (val*val*signature))

    (FSim12 : ForwardSimulation_equal Sem1 Sem2 ge1 ge2 entry_points12)
    (FSim23 : ForwardSimulation_inject Sem2 Sem3 ge2 ge3 entry_points23)

    (entry_points13: list (val*val*signature))
    (EPC: entry_points_compose entry_points12 entry_points23 entry_points13),

    ForwardSimulation_inject Sem1 Sem3 ge1 ge3 entry_points13.

End SIMULATIONS.

(* This module type states that forward simulations are sufficent
   to imply correctness with respect to the trace model of external
   functions.  First we demonstrate how to hook up an arbitrary
   ExtSem with the trace model, then we show simulation in the
   forward and backward direction.  Finally we show that
   the compiler preserves all trace behaviors for safe input
   programs.
 *)

(* COMMENTED OUT by Andrew, until Rob can adjust it to CompCert's new-style
    "semantics" definition 

Require Import compcert.Smallstep.
Require Import compcert.Determinism.
Require Import compcert.Behaviors.

Module Type TRACE_CORRECTNESS.

  Section ExtSem_to_trace.
    Variables (F C V:Type).
    Variable (Sem:CompcertCoreSem F C V external_function).

    Let genv  := G.
    Let state := (C * mem)%type.

    Inductive step (ge:genv) : state -> trace -> state -> Prop :=
    | step_corestep : forall c m c' m',
          corestep Sem ge c m c' m' ->
          step ge (c,m) E0 (c',m')

    | step_ext_step : forall c m c' m' ef sig args tr ret,
          at_external Sem c = Some (ef,sig,args) ->
          sig = ef_sig ef ->
          external_call ef ge args m tr ret m' ->
          after_external Sem (ret::nil) c = Some c' ->
          step ge (c,m) tr (c',m').

    Variable (prog:program (fundef F) V).

    Definition main_sig : signature := 
      mksignature (Tint :: Tint :: nil) (Some Tint).

    Definition initial_state (st:state) : Prop :=
      exists b, exists vals,
        Forall2 (val_inject (Mem.flat_inj (Mem.nextblock (snd st)))) vals vals /\
        Forall2 Val.has_type vals (sig_args main_sig) /\
        Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
        make_initial_core Sem (Genv.globalenv prog) (Vptr b Int.zero) vals = Some (fst st) /\
        Genv.init_mem prog = Some (snd st).

    Definition final_state (st:state) (i:int) : Prop :=
      safely_halted Sem (Genv.globalenv prog) (fst st) (snd st) = Some (Vint i).

    Definition behaves : program_behavior -> Prop :=
      program_behaves step initial_state final_state (Genv.globalenv prog).

    Definition safe_state w ge st := 
      forall t w' st',
        star step ge st t st' ->
        possible_trace w t w' ->
          (exists i, final_state st' i) \/
          (exists t', exists st'', exists w'',
            step ge st' t' st'' /\
            possible_trace w' t' w'').

    Definition safe_prog w ge := forall st, initial_state st -> safe_state w ge st.

  End ExtSem_to_trace.

  Axiom forward_simulation_trace_forward : forall
      (F1 C1 V1 F2 C2 V2 :Type)
      (Sem1 : CompcertCoreSem F1 C1 V1 external_function)
      (Sem2 : CompcertCoreSem F2 C2 V2 external_function)

      (prog1 : program (fundef F1) V1)
      (prog2 : program (fundef F2) V2)

      (entry_points : list (ident * signature))

      (match_fun : fundef F1 -> fundef F2 -> Prop)
      (match_varinfo : V1 -> V2 -> Prop)

      (main_entry_point : In (prog_main prog1, main_sig) entry_points)
      (match_prog : match_program match_fun match_varinfo prog1 prog2)

      (fsim : ForwardSimulation Sem1 Sem2 
               (Genv.globalenv prog1) (Genv.globalenv prog2) entry_points (fun _ => eq)),

      forall beh,
        not_wrong beh ->
        behaves _ _ _ Sem1 prog1 beh ->
        behaves _ _ _ Sem2 prog2 beh.

  Axiom forward_simulation_trace_backward : forall
      (F1 C1 V1 F2 C2 V2 :Type)
      (Sem1 : CompcertCoreSem F1 C1 V1 external_function)
      (Sem2 : CompcertCoreSem F2 C2 V2 external_function)

      (prog1 : program (fundef F1) V1)
      (prog2 : program (fundef F2) V2)

      (entry_points : list (ident * signature))

      (match_fun : fundef F1 -> fundef F2 -> Prop)
      (match_varinfo : V1 -> V2 -> Prop)

      (main_entry_point : In (prog_main prog1, main_sig) entry_points)
      (match_prog : match_program match_fun match_varinfo prog1 prog2)

      (fsim : ForwardSimulation Sem1 Sem2 
               (Genv.globalenv prog1) (Genv.globalenv prog2) entry_points (fun _ => eq)),

      forall w beh,
        safe_prog _ _ _ Sem1 prog1 w (Genv.globalenv prog1) ->
        possible_behavior w beh ->
        behaves _ _ _ Sem2 prog2 beh ->
        behaves _ _ _ Sem1 prog1 beh.

  Axiom forward_simulation_trace_correct : forall
      (F1 C1 V1 F2 C2 V2 :Type)
      (Sem1 : CompcertCoreSem F1 C1 V1 external_function)
      (Sem2 : CompcertCoreSem F2 C2 V2 external_function)

      (prog1 : program (fundef F1) V1)
      (prog2 : program (fundef F2) V2)

      (entry_points : list (ident * signature))

      (match_fun : fundef F1 -> fundef F2 -> Prop)
      (match_varinfo : V1 -> V2 -> Prop)

      (main_entry_point : In (prog_main prog1, main_sig) entry_points)
      (match_prog : match_program match_fun match_varinfo prog1 prog2)

      (fsim : ForwardSimulation Sem1 Sem2 
               (Genv.globalenv prog1) (Genv.globalenv prog2) entry_points (fun _ => eq)),

      (forall w, safe_prog _ _ _ Sem1 prog1 w (Genv.globalenv prog1)) ->
      forall beh,
        (behaves _ _ _ Sem1 prog1 beh <-> behaves _ _ _ Sem2 prog2 beh).

End TRACE_CORRECTNESS.

*)
