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
Record CoreSemantics {G C M E:Type} : Type :=
  { make_initial_core : G -> val -> list val -> option C
  ; at_external : C -> option (E * signature * list val)
  ; after_external : list val -> C -> option C
  ; safely_halted : G -> C -> M -> option val
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
Record CompcertCoreSem {G C E} :=
{ csem :> CoreSemantics G C mem E

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

Record ForwardSimulationStructure {data:Type} :=
  { (* We need a notion of the relation witness "extending".
       This generalizes the "inject_incr" of meminj.
     *)
    extends_data : data -> data -> Prop

    (* What it means for two addresses to match. *)
  ; match_addr  : data -> block -> Z -> block -> Z -> Prop
  
    (* What is means for two values to match at a type. *)
  ; match_val : data -> typ -> val -> val -> Prop

    (* [match_block d b1 b2] holds when blocks b1 and b2
       are matching blocks.  This means they match for
       every offset.  Furthermore, these two blocks have
       a _unique_ matching relationship; no other blocks
       will match.
     *)
  ; match_block : data -> block -> block -> Prop

    (* [match_external_mem d d' m1 m2 m1' m2'] holds when
        (d,m1,m2) is a matching tuple which has evolved into
        the matching tuple (d',m1',m2') by allowed operations.
        This captures what external functions are allowed to do.
     *)
  ; match_external_mem :
      data -> data -> mem -> mem -> mem -> mem -> Prop

    (* data extension is a preorder *)
  ; extends_refl : forall d, extends_data d d
  ; extends_trans : forall d1 d2 d3,
      extends_data d1 d2 -> extends_data d2 d3 -> extends_data d1 d3

    (* data extension preseves the other matching relations *)
  ; extends_addr : forall d d' b1 ofs1 b2 ofs2,
      extends_data d d' ->
      match_addr d b1 ofs1 b2 ofs2 ->
      match_addr d' b1 ofs1 b2 ofs2

  ; extends_block : forall d d' b1 b2,
      extends_data d d' ->
      match_block d b1 b2 ->
      match_block d' b1 b2

  ; extends_val : forall d d' t v1 v2,
      extends_data d d' ->
      match_val d  t v1 v2 ->
      match_val d' t v1 v2

    (* properties of value matching *)
  ; match_val_type1 : forall d t v1 v2,
      match_val d t v1 v2 ->
      Val.has_type v1 t

  ; match_val_type2 : forall d t v1 v2,
      match_val d t v1 v2 ->
      Val.has_type v2 t

  ; match_val_undef : forall d t,
      match_val d t Vundef Vundef

  ; match_val_int_i : forall d i,
      match_val d AST.Tint (Vint i) (Vint i)

  ; match_val_int_e : forall d i x,
      match_val d AST.Tint (Vint i) x -> x = Vint i

  ; match_val_float_i : forall d f,
      match_val d AST.Tfloat (Vfloat f) (Vfloat f)

  ; match_val_float_e : forall d f x,
      match_val d AST.Tfloat (Vfloat f) x -> x = Vfloat f

  ; match_val_ptr_i : forall d b ofs b' ofs',
      match_addr d b ofs b' ofs' ->
      match_val d AST.Tint (Vptr b (Int.repr ofs)) (Vptr b' (Int.repr ofs'))

  ; match_val_ptr_e : forall d b ofs x,
      match_val d AST.Tint (Vptr b ofs) x ->
        exists b', exists ofs',
          x = Vptr b' ofs'

  ; match_val_ptr_addr : forall d b ofs b' ofs' dx m1x m2x m1 m2,
      match_val d AST.Tint (Vptr b ofs) (Vptr b' ofs') ->
      match_external_mem dx d m1x m2x m1 m2 ->
      Mem.valid_pointer m1 b (Int.unsigned ofs) = true ->
      match_addr d b (Int.unsigned ofs) b' (Int.unsigned ofs')

    (* Matching heap data blocks have a special relation with address matching:
         1) on matching blocks, addresses and values match directly without
             requiring pointer validity
         2) matching blocks have corresponding maching addresses, and 
         3) address matching is a partial bijection on matching heap blocks
     *)
  ; match_block_match_val_addr :
       forall d b b' i i',
         match_block d b b' ->
         match_val d AST.Tint (Vptr b i) (Vptr b' i') ->
         match_addr d b (Int.unsigned i) b' (Int.unsigned i')

  ; match_block_match_addr :
       forall d b b' ofs,
         match_block d b b' ->
         match_addr d b ofs b' ofs
    
  ; match_block_match_addr_eq1 :
       forall d b b' ofs ofs' b2,
         match_block d b b' ->
         match_addr d b ofs b2 ofs' ->
         b' = b2 /\ ofs = ofs'

  ; match_block_match_addr_eq2 :
       forall d b b' ofs ofs' b2,
         match_block d b b' ->
         match_addr d b2 ofs b' ofs' ->
         b = b2 /\ ofs = ofs'

  ; match_block_match_val_eq1 :
       forall d b b' ofs ofs' b2,
         match_block d b b' ->
         match_val d AST.Tint (Vptr b ofs) (Vptr b2 ofs') ->
         b' = b2 /\ ofs = ofs'

  ; match_block_match_val_eq2 :
       forall d b b' ofs ofs' b2,
         match_block d b b' ->
         match_val d AST.Tint (Vptr b2 ofs) (Vptr b' ofs') ->
         b = b2 /\ ofs = ofs'

    (* matching addresses are preserved by pointer aritmetic *)
  ; match_addr_offset : forall d b ofs b' ofs' delta,
      match_addr d b ofs b' ofs' ->
      match_addr d b (ofs + delta) b' (ofs' + delta)

  ; match_val_offset : forall d b ofs b' ofs' delta,
      match_val d AST.Tint (Vptr b ofs) (Vptr b' ofs') ->
      match_val d AST.Tint (Vptr b (Int.add ofs delta)) (Vptr b' (Int.add ofs' delta))

    (* Every self-injecting memory can be matched to itself by some data *)
  ; match_external_mem_self : forall m,
      Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m ->
      exists d,
        match_external_mem d d m m m m /\
        (forall b, Mem.valid_block m b -> match_block d b b)

    (* Matching imp data extension *)
  ; match_external_extends : forall dx d m1x m2x m1 m2,
      match_external_mem dx d m1x m2x m1 m2 -> extends_data dx d

    (* Parallel memory operations on matching memories with
       matching arguments yields matching results. *)
  ; match_mem_valid_block : forall dx m1x m2x d m1 m2 b1 ofs1 b2 ofs2,
      match_external_mem dx d m1x m2x m1 m2 ->
      match_addr d b1 ofs1 b2 ofs2 ->
      (Mem.valid_block m1 b1 <-> Mem.valid_block m2 b2)

  ; match_mem_perm : forall dx m1x m2x d m1 m2 b1 ofs1 b2 ofs2,
      match_external_mem dx d m1x m2x m1 m2 ->
      match_addr d b1 ofs1 b2 ofs2 ->
      (forall p, Mem.perm m1 b1 ofs1 Cur p 
              -> Mem.perm m2 b2 ofs2 Cur p)

  ; match_mem_load : forall dx m1x m2x d m1 m2 chunk b1 ofs1 b2 ofs2 v1,
      match_external_mem dx d m1x m2x m1 m2 ->
      match_addr d b1 ofs1 b2 ofs2 ->
      Mem.load chunk m1 b1 ofs1 = Some v1 ->
      exists v2,
        Mem.load chunk m2 b2 ofs2 = Some v2 /\
        match_val d (type_of_chunk chunk) v1 v2

  ; match_mem_alloc : forall dx m1x m2x d lo hi m1 m1' b1 m2,
      match_external_mem dx d m1x m2x m1 m2 ->
      Mem.alloc m1 lo hi = (m1', b1) ->
      exists m2', exists b2, exists d',
        match_block d' b1 b2 /\
        Mem.alloc m2 lo hi = (m2', b2) /\
        extends_data d d' /\
        match_external_mem dx d' m1x m2x m1' m2'

  ; match_mem_store : forall dx m1x m2x d m1 m2 chunk b1 ofs1 v1 m1' b2 ofs2 v2,
      match_external_mem dx d m1x m2x m1 m2 ->
      Mem.store chunk m1 b1 ofs1 v1 = Some m1' ->
      match_addr d b1 ofs1 b2 ofs2 ->
      match_val d (type_of_chunk chunk) v1 v2 ->
      exists m2', exists d',
        Mem.store chunk m2 b2 ofs2 v2 = Some m2' /\
        extends_data d d' /\
        match_external_mem dx d' m1x m2x m1' m2'

  ; match_mem_free : forall dx m1x m2x d m1 b1 lo b2 lo' sz m1' m2,
      match_external_mem dx d m1x m2x m1 m2 ->
      match_addr d b1 lo b2 lo' ->
      Mem.free m1 b1 lo (lo + sz) = Some m1' ->
      exists m2', exists d',
        Mem.free m2 b2 lo' (lo' + sz) = Some m2' /\
        extends_data d d' /\
        match_external_mem dx d' m1x m2x m1' m2'
  }.

Implicit Arguments ForwardSimulationStructure [].


(* Matching for lists of values with their types *)
Inductive match_vals {D} (struct:ForwardSimulationStructure D) (d:D) :
  (list typ) -> (list val) -> (list val) -> Prop :=
| match_vals_nil : match_vals struct d nil nil nil
| match_vals_cons : forall t ts v vs y ys,
  match_val struct d t v y ->
  match_vals struct d ts vs ys ->
  match_vals struct d (t::ts) (v::vs) (y::ys).


(* A "forward simulation" exists between two programs
   in two (possibly) different small step semantics when we
   can exibit a forward simulation structure which
   is preserved by parallel executions.

   The critical component of the ForwardSim record
   is the simulation diagram [fsim_diagram], which
   shows how the [match_state] relation is preserved
   by sequential execution.  The well-founded order
   is used to ensure that execution on the left eventually
   forces at least one step of related execution on the right.

   [fsim_initial] shows how the entry points of the programs
   are related when started with related arguments.
   [fsim_halted] shows that halted states are related to halted states.

   [fsim_at_external] shows how related states blocked on external function
   calls must have related external arguments and memories.  Finally,
   [fsim_after_external] shows that no matter what allowed modifications
   the external function makes, the resumed sequential states will be
   properly related.
 *)
Section ForwardSimulation.
  Context {G1 C1 E1 G2 C2 E2:Type}
          {Sem1 : CompcertCoreSem G1 C1 E1}
          {Sem2 : CompcertCoreSem G2 C2 E2}

          {ge1:G1}
          {ge2:G2}
  
          {entry_points : list (val * val * signature)}

          {match_ext : signature -> E1 -> E2 -> Prop}.

  Record ForwardSimulation :=
  { data : Type
  ; fsim_struct : ForwardSimulationStructure data

  ; match_state : data -> C1 -> mem -> C2 -> mem -> Prop

  ; fsim_order : (data*C1) -> (data*C1) -> Prop
  ; fsim_wf : well_founded fsim_order

  ; fsim_diagram :
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall d st2 m2, match_state d st1 m1 st2 m2 ->
        exists st2', exists m2', exists d',
          extends_data fsim_struct d d' /\
          match_state d' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            fsim_order (d',st1') (d,st1))

  ; fsim_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall dx d vals vals' m1x m2x m1 m2,
          match_vals fsim_struct d (sig_args sig) vals vals' ->
          match_external_mem fsim_struct dx d m1x m2x m1 m2 ->
          exists d', exists c1, exists c2,
            extends_data fsim_struct d d' /\
            make_initial_core Sem1 ge1 v1 vals  = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state d' c1 m1 c2 m2

  ; fsim_halted : forall d c1 m1 c2 m2 v1,
      match_state d c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 m1 = Some v1 ->
      exists v2,
        safely_halted Sem2 ge2 c2 m2 = Some v2 /\
        match_val fsim_struct d AST.Tint v1 v2 /\
        match_external_mem fsim_struct d d m1 m2 m1 m2

  ; fsim_at_external : forall d st1 m1 st2 m2 e1 sig vals,
      match_state d st1 m1 st2 m2 ->
      at_external Sem1 st1 = Some (e1,sig,vals) ->
      exists e2, exists vals',
        match_ext sig e1 e2 /\
        at_external Sem2 st2 = Some (e2,sig,vals') /\
        match_vals fsim_struct d (sig_args sig) vals vals' /\
        match_external_mem fsim_struct d d m1 m2 m1 m2

  ; fsim_after_external : forall d st1 m1 st2 m2 e1 e2 sig vals vals',
      match_state d st1 m1 st2 m2 ->
      at_external Sem1 st1 = Some (e1,sig,vals) ->
      at_external Sem2 st2 = Some (e2,sig,vals') ->
      match_ext sig e1 e2 ->
      match_vals fsim_struct d (sig_args sig) vals vals' ->
      forall d' ret1 ret2 m1' m2',
        match_external_mem fsim_struct d d' m1 m2 m1' m2' ->
        match_val fsim_struct d' (proj_sig_res sig) ret1 ret2 ->
        exists st1', exists st2', exists d'',
          extends_data fsim_struct d' d'' /\
          after_external Sem1 (ret1::nil) st1 = Some st1' /\
          after_external Sem2 (ret2::nil) st2 = Some st2' /\
          match_state d'' st1' m1' st2' m2'
  }.

End ForwardSimulation.

Implicit Arguments ForwardSimulation [[G1] [C1] [E1] [G2] [C2] [E2]].


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
  Axiom forward_simulation_equals : forall
    (G1 C1 E1 G2 C2 E2:Type)
    (Sem1 : CompcertCoreSem G1 C1 E1)
    (Sem2 : CompcertCoreSem G2 C2 E2)

    (ge1:G1)
    (ge2:G2)
    (entry_points : list (val * val * signature))

    (match_ext : signature -> E1 -> E2 -> Prop)

    (core_data:Type)

    (match_core : core_data -> C1 -> C2 -> Prop)
    (core_ord : C1 -> C1 -> Prop)
    (core_ord_wf : well_founded core_ord)

    (core_diagram : 
      forall st1 m st1' m', corestep Sem1 ge1 st1 m st1' m' ->
      forall d st2, match_core d st1 st2 ->
        exists st2', exists d',
          match_core d' st1' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            corestep_star Sem2 ge2 st2 m st2' m' /\
            core_ord st1' st1))

    (core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals,
          Forall2 (Val.has_type) vals (sig_args sig) ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals = Some c2 /\
            match_core cd c1 c2)

    (core_halted : forall cd c1 c2 m v,
      match_core cd c1 c2 ->
      safely_halted Sem1 ge1 c1 m = Some v ->
      safely_halted Sem2 ge2 c2 m = Some v /\
      Val.has_type v AST.Tint)

    (core_at_external : 
      forall d st1 st2 e1 sig args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e1,sig,args) ->
        exists e2,
          match_ext sig e1 e2 /\
          at_external Sem2 st2 = Some (e2,sig,args) /\
          Forall2 Val.has_type args (sig_args sig))

    (core_after_external :
      forall d st1 st2 ret e1 e2 sig args,
        match_core d st1 st2 ->
        at_external Sem1 st1 = Some (e1,sig,args) ->
        at_external Sem2 st2 = Some (e2,sig,args) ->
        match_ext sig e1 e2 ->
        Forall2 Val.has_type args (sig_args sig) ->
        Val.has_type ret (proj_sig_res sig) ->
        exists st1', exists st2', exists d',
          after_external Sem1 (ret::nil) st1 = Some st1' /\
          after_external Sem2 (ret::nil) st2 = Some st2' /\
          match_core d' st1' st2'),

    ForwardSimulation Sem1 Sem2 ge1 ge2 entry_points match_ext.

  (* Next, an axiom for passes that allow the memory to undergo extension. *)
  Axiom forward_simulation_extends : forall
    (G1 C1 E1 G2 C2 E2:Type)
    (Sem1 : CompcertCoreSem G1 C1 E1)
    (Sem2 : CompcertCoreSem G2 C2 E2)

    (ge1:G1)
    (ge2:G2)
    (entry_points : list (val * val *signature))
    (match_ext : signature -> E1 -> E2 -> Prop)

    (core_data : Type)

    (match_state : core_data -> C1 -> mem -> C2 -> mem -> Prop)
    (core_ord : C1 -> C1 -> Prop)
    (core_ord_wf : well_founded core_ord)

    (core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 m2,
        match_state cd st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd',
          match_state cd' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord st1' st1))

    (core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2)

    (core_halted : 
      forall cd st1 m1 st2 m2 v1,
        match_state cd st1 m1 st2 m2 ->
        safely_halted Sem1 ge1 st1 m1 = Some v1 ->
        exists v2,
          safely_halted Sem2 ge2 st2 m2 = Some v2 /\
          Val.lessdef v1 v2 /\
          Val.has_type v2 AST.Tint /\
          Mem.extends m1 m2)

    (core_at_external : 
      forall cd st1 m1 st2 m2 e1 sig vals,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        exists e2, exists vals',
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals vals' /\
          Forall2 (Val.has_type) vals' (sig_args sig) /\
          match_ext sig e1 e2 /\
          at_external Sem2 st2 = Some (e2,sig,vals'))

    (core_after_external :
      forall cd st1 st2 m1 m2 e1 e2 vals vals' sig ret ret' m1' m2',
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        at_external Sem2 st2 = Some (e2,sig,vals') ->
        match_ext sig e1 e2 ->

        Forall2 Val.lessdef vals vals' ->
        Forall2 (Val.has_type) vals' (sig_args sig) ->
      
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->
        mem_unchanged_on (loc_out_of_bounds m1) m2 m2' ->
        Val.lessdef ret ret' ->
        Mem.extends m1' m2' ->

        Val.has_type ret' (proj_sig_res sig) ->

        exists st1', exists st2', exists cd',
          after_external Sem1 (ret::nil) st1 = Some st1' /\
          after_external Sem2 (ret'::nil) st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2'),

    ForwardSimulation Sem1 Sem2 ge1 ge2 entry_points match_ext.

  (* An axiom for passes that use memory injections. *)
  Axiom forward_simulation_inject : forall
    (G1 C1 E1 G2 C2 E2:Type)
    (Sem1 : CompcertCoreSem G1 C1 E1)
    (Sem2 : CompcertCoreSem G2 C2 E2)

    (ge1:G1)
    (ge2:G2)
    (entry_points:list (val * val * signature))
    (match_ext : signature -> E1 -> E2 -> Prop)

    (core_data : Type)

    (match_state : core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
    (core_ord : C1 -> C1 -> Prop)
    (core_ord_wf : well_founded core_ord)

    (core_diagram : 
      forall st1 m1 st1' m1', corestep Sem1 ge1 st1 m1 st1' m1' ->
      forall cd st2 j m2,
        match_state cd j st1 m1 st2 m2 ->
        exists st2', exists m2', exists cd', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          match_state cd' j' st1' m1' st2' m2' /\
          ((corestep_plus Sem2 ge2 st2 m2 st2' m2') \/
            corestep_star Sem2 ge2 st2 m2 st2' m2' /\
            core_ord st1' st1))

    (core_initial : forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall j vals vals' m1 m2,
          Forall2 (val_inject j) vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.inject j m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd j c1 m1 c2 m2)

    (core_halted : forall cd j c1 m1 c2 m2 v1,
      match_state cd j c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 m1 = Some v1 ->
      exists v2,
        safely_halted Sem2 ge2 c2 m2 = Some v2 /\
        val_inject j v1 v2 /\
        Val.has_type v2 AST.Tint /\
        Mem.inject j m1 m2)

    (core_at_external : 
      forall cd j st1 m1 st2 m2 e1 vals sig,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        exists e2, exists vals',
          Mem.inject j m1 m2 /\
          Forall2 (val_inject j) vals vals' /\
          Forall2 (Val.has_type) vals' (sig_args sig) /\
          match_ext sig e1 e2 /\
          at_external Sem2 st2 = Some (e2,sig,vals'))
  
    (core_after_external :
      forall cd j j' st1 st2 m1 m2 e1 e2 vals vals' ret ret' m1' m2' sig,
        match_state cd j st1 m1 st2 m2 ->
        Mem.inject j m1 m2 ->
        at_external Sem1 st1 = Some (e1,sig,vals) ->
        at_external Sem2 st2 = Some (e2,sig,vals') ->
        match_ext sig e1 e2 ->
        Forall2 (val_inject j) vals vals' ->
      
        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret ret' ->

        mem_unchanged_on (loc_unmapped j) m1 m1' ->
        mem_unchanged_on (loc_out_of_reach j m1) m2 m2' ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Forall2 (Val.has_type) vals' (sig_args sig) ->
        Val.has_type ret' (proj_sig_res sig) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 (ret::nil) st1 = Some st1' /\
          after_external Sem2 (ret'::nil) st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'),

    ForwardSimulation Sem1 Sem2 ge1 ge2 entry_points match_ext.

  (* Finally an axiom stating that forward simulations compose *)
  Axiom forward_simulation_compose : forall
    (G1 C1 E1 G2 C2 E2 G3 C3 E3:Type)
    (Sem1 : CompcertCoreSem G1 C1 E1)
    (Sem2 : CompcertCoreSem G2 C2 E2)
    (Sem3 : CompcertCoreSem G3 C3 E3)

    (ge1 : G1)
    (ge2 : G2)
    (ge3 : G3)

    (entry_points12 : list (val*val*signature))
    (entry_points23 : list (val*val*signature))
    (match_ext12 : signature -> E1 -> E2 -> Prop)
    (match_ext23 : signature -> E2 -> E3 -> Prop)

    (FSim12 : ForwardSimulation Sem1 Sem2 ge1 ge2 entry_points12 match_ext12)
    (FSim23 : ForwardSimulation Sem2 Sem3 ge2 ge3 entry_points23 match_ext23)

    (entry_points13: list (val*val*signature))
    (EPC: entry_points_compose entry_points12 entry_points23 entry_points13),

    let match_ext13 sig e1 e3 := exists e2, match_ext12 sig e1 e2 /\ match_ext23 sig e2 e3 in
    ForwardSimulation Sem1 Sem3 ge1 ge3 entry_points13 match_ext13.

End SIMULATIONS.

(* This module type states that forward simulations are sufficent
   to imply correctness with respect to the trace model of external
   functions.  First we demonstrate how to hook up an arbitrary
   EXtSem with the trace model, then we show simulation in the
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

  Section EXtSem_to_trace.
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

  End EXtSem_to_trace.

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
