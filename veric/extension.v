Load loadpath.
Require Import msl.predicates_hered.
Require Import veric.sim veric.step_lemmas veric.base veric.expr veric.extspec 
               veric.juicy_extspec.
Require Import veric.Events2.
Require Import ListSet.

Set Implicit Arguments.

(** External function specifications and linking *)

Lemma extfunct_eqdec : forall ef1 ef2 : AST.external_function, 
  {ef1=ef2} + {~ef1=ef2}.
Proof. intros ef1 ef2; repeat decide equality; apply Address.EqDec_int. Qed.

Module TruePropCoercion.
Definition is_true (b: bool) := b=true.
Coercion is_true: bool >-> Sortclass.
End TruePropCoercion.

Import TruePropCoercion.

Notation IN := (ListSet.set_mem extfunct_eqdec).
Notation NOTIN := (fun ef l => ListSet.set_mem extfunct_eqdec ef l = false).
Notation DIFF := (ListSet.set_diff extfunct_eqdec).

Lemma in_diff (ef: AST.external_function) (l r: list AST.external_function) :
  IN ef l -> NOTIN ef r -> IN ef (DIFF l r).
Proof.
simpl; intros H1 H2; apply set_mem_correct2. 
apply set_mem_correct1 in H1.
apply set_mem_complete1 in H2.
apply set_diff_intro; auto.
Qed.

(** Linking external specification [Sigma] with an extension implementing
   functions in [handled] *)

Definition link_ext_spec (M Z: Type) (handled: list AST.external_function) 
  (Sigma: external_specification M AST.external_function Z) :=
  Build_external_specification M AST.external_function Z
    (ext_spec_type Sigma)
    (fun (ef: AST.external_function) (x: ext_spec_type Sigma ef)
         (tys: list typ) (args: list val) (z: Z) (m: M) => 
             if ListSet.set_mem extfunct_eqdec ef handled then False 
             else ext_spec_pre Sigma ef x tys args z m)
    (fun (ef: AST.external_function) (x: ext_spec_type Sigma ef)
         (ty: option typ) (ret: option val) (z: Z) (m: M) => 
             if ListSet.set_mem extfunct_eqdec ef handled then True
             else ext_spec_post Sigma ef x ty ret z m).

Program Definition link_juicy_ext_spec (Z: Type) (handled: list AST.external_function)
  (Sigma: juicy_ext_spec Z) :=
  Build_juicy_ext_spec Z (link_ext_spec handled Sigma) _ _.
Next Obligation.
if_tac; [unfold hereditary; auto|].
generalize JE_pre_hered; unfold hereditary; intros; eapply H; eauto.
Qed.
Next Obligation.
if_tac; [unfold hereditary; auto|].
generalize JE_post_hered; unfold hereditary; intros; eapply H; eauto.
Qed.

(** An external signature [ext_sig] is a list of handled functions together with
   an external specification. *)

Section ExtSig.
Variables M Z: Type.

Inductive ext_sig := 
  mkextsig: forall (functs: list AST.external_function)
                   (extspec: external_specification M external_function Z), 
    ext_sig.

Definition extsig2functs (Sigma: ext_sig) := 
  match Sigma with mkextsig l _ => l end.
Coercion extsig2functs : ext_sig >-> list.

Definition extsig2extspec (Sigma: ext_sig) :=
  match Sigma with mkextsig functs spec => spec end.
Coercion extsig2extspec : ext_sig >-> external_specification.

Definition spec_of (ef: AST.external_function) (Sigma: ext_sig) :=
  (ext_spec_pre Sigma ef, ext_spec_post Sigma ef).

End ExtSig.

Record juicy_ext_sig (Z: Type): Type := mkjuicyextsig {
  JE_functs:> list external_function;
  JE_extspec:> juicy_ext_spec Z
}.

Definition juicy_extsig2extsig (Z: Type) (je: juicy_ext_sig Z) :=
  mkextsig (JE_functs je) (JE_extspec je).
Coercion juicy_extsig2extsig: juicy_ext_sig >-> ext_sig.

Definition link (T Z: Type) (esig: ext_sig T Z) 
      (handled: list AST.external_function) :=
  mkextsig handled (link_ext_spec handled esig).

Definition juicy_link (Z: Type) (jesig: juicy_ext_sig Z) 
      (handled: list AST.external_function) :=
  mkjuicyextsig handled (link_juicy_ext_spec handled jesig).

(** A client signature is linkable with an extension signature when each
   extension function specification ef:{P}{Q} is a subtype of the
   specification ef:{P'}{Q'} assumed by client. *)

Definition linkable (M Z Zext: Type) (proj_zext: Z -> Zext)
      (handled: list AST.external_function) 
      (csig: ext_sig M Z) (ext_sig: ext_sig M Zext) := 
  forall ef P Q P' Q', 
    IN ef (DIFF csig handled) -> 
    spec_of ef ext_sig = (P, Q) -> 
    spec_of ef csig = (P', Q') -> 
    forall x' tys args m z, P' x' tys args z m -> 
      exists x, P x tys args (proj_zext z) m /\
      forall ty ret m' z', Q x ty ret (proj_zext z') m' -> Q' x' ty ret z' m'.

(** * Extensions *)

Module Extension. Section Extension.
 Variables
  (G: Type) (** global environments of extended semantics *)
  (xT: Type) (** corestates of extended semantics *)
  (cT: nat -> Type) (** corestates of core semantics *)
  (M: Type) (** memories *)
  (D: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)

  (esem: CoreSemantics G xT M D) (** extended semantics *)
  (csem: forall i:nat, option (CoreSemantics G (cT i) M D)) (** a set of core semantics *)

  (csig: ext_sig M Z) (** client signature *)
  (esig: ext_sig M Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Record Sig := Make {
 (** Generalized projection of core [i] from state [s] *)
   proj_core : forall i:nat, xT -> option (cT i);
   core_exists : forall ge i s c' m s' m', 
     corestep esem ge s m s' m' -> proj_core i s' = Some c' -> 
     exists c, proj_core i s = Some c;
   
 (** The active (i.e., currently scheduled) core *)
   active : xT -> nat;
   active_csem : forall s, exists CS, csem (active s) = Some CS;
   active_proj_core : forall s, exists c, proj_core (active s) s = Some c;
   
 (** Runnable=[true] when [active s] is runnable (i.e., not blocked
    waiting on an external function call and not safely halted). *)
   runnable : G -> xT -> bool;
   runnable_false : forall ge s c CS,
     runnable ge s = false -> 
     csem (active s) = Some CS -> proj_core (active s) s = Some c -> 
     (exists rv, safely_halted CS ge c = Some rv) \/
     (exists ef, exists sig, exists args, at_external CS c = Some (ef, sig, args));

 (** AtExternal cores are blocked on external functions specified by their
    external function signatures. *)
   at_external_csig: forall s i CS c ef args sig,
     csem i = Some CS -> proj_core i s = Some c -> 
     at_external CS c = Some (ef, sig, args) -> 
     IN ef csig;

 (** When a core is AtExternal but the extension is not, the function on which 
    the core is blocked is handled by the extension. *)
   notat_external_handled: forall s i CS c ef args sig,
     csem i = Some CS -> proj_core i s = Some c -> 
     at_external CS c = Some (ef, sig, args) -> 
     at_external esem s = None -> 
     IN ef handled;

 (** Functions on which the extension is blocked are not handled. *)
   at_external_not_handled: forall s ef args sig,
     at_external esem s = Some (ef, sig, args) -> 
     NOTIN ef handled;

 (** Type [xT] embeds [Zint]. *)
   proj_zint: xT -> Zint;
   proj_zext: Z -> Zext;
   zmult: Zint -> Zext -> Z;
   zmult_proj: forall zint zext, proj_zext (zmult zint zext) = zext;

 (** Implemented "external" state is unchanged after truly external calls. *)
   ext_upd_at_external : forall ef sig args ret s s',
     at_external esem s = Some (ef, sig, args) -> 
     after_external esem ret s = Some s' -> 
     proj_zint s = proj_zint s';
   
 (** [esem] and [csem] are signature linkable *)
   esem_csem_linkable: linkable proj_zext handled csig esig
 }.

End Extension. End Extension.

Implicit Arguments Extension.Make [G xT cT M D Z Zint Zext].

(** * Safe Extensions *)

Section SafeExtension.
 Variables
  (G: Type) (** global environments *)
  (xT: Type) (** corestates of extended semantics *)
  (cT: nat -> Type) (** corestates of core semantics *)
  (M: Type) (** memories *)
  (D: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)

  (esem: CoreSemantics G xT M D) (** extended semantics *)
  (csem: forall i:nat, option (CoreSemantics G (cT i) M D)) (** a set of core semantics *)

  (csig: ext_sig M Z) (** client signature *)
  (esig: ext_sig M Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

Import Extension.

(** a global invariant characterizing "safe" extensions *)
Definition all_safe (E: Sig cT Zint esem csem csig esig handled)
  (ge: G) (n: nat) (z: Z) (w: xT) (m: M) :=
     forall i CS c, csem i = Some CS -> proj_core E i w = Some c -> 
       safeN CS csig ge n z c m.

(** All-safety implies safeN. *)
Definition safe_extension (E: Sig cT Zint esem csem csig esig handled) :=
  forall ge n s m z, 
    all_safe E ge n (zmult E (proj_zint E s) z) s m -> 
    safeN esem (link esig handled) ge n z s m.

End SafeExtension.

Module SafetyInvariant. Section SafetyInvariant.
 Variables
  (G: Type) (** global environments *)
  (xT: Type) (** corestates of extended semantics *)
  (cT: nat -> Type) (** corestates of core semantics *)
  (M: Type) (** memories *)
  (D: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)

  (esem: CoreSemantics G xT M D) (** extended semantics *)
  (csem: forall i:nat, option (CoreSemantics G (cT i) M D)) (** a set of core semantics *)

  (csig: ext_sig M Z) (** client signature *)
  (esig: ext_sig M Zext) (** extension signature *)
  (handled: list AST.external_function) (** functions handled by this extension *)
  (E: Extension.Sig cT Zint esem csem csig esig handled). 

Definition proj_zint := E.(Extension.proj_zint). 
Coercion proj_zint : xT >-> Zint.

Definition proj_zext := E.(Extension.proj_zext).
Coercion proj_zext : Z >-> Zext.

Notation ALL_SAFE := (all_safe E).
Notation PROJ_CORE := E.(Extension.proj_core).
Notation "zint \o zext" := (E.(Extension.zmult) zint zext) 
  (at level 66, left associativity). 
Notation ACTIVE := (E.(Extension.active)).
Notation RUNNABLE := (E.(Extension.runnable)).
Notation "'CORE' i 'is' ( CS , c ) 'in' s" := 
  (csem i = Some CS /\ PROJ_CORE i s = Some c)
  (at level 66, no associativity).
Notation core_exists := E.(Extension.core_exists).
Notation active_csem := E.(Extension.active_csem).
Notation active_proj_core := E.(Extension.active_proj_core).
Notation notat_external_handled := E.(Extension.notat_external_handled).
Notation at_external_not_handled := E.(Extension.at_external_not_handled).
Notation ext_upd_at_external := E.(Extension.ext_upd_at_external).
Notation runnable_false := E.(Extension.runnable_false).

Inductive safety_invariant: Type := SafetyInvariant: forall 
  (** Coresteps preserve the all-safety invariant. *)
  (core_pres: forall ge n z (s: xT) c m CS s' c' m', 
    ALL_SAFE ge (S n) (s \o z) s m -> 
    CORE (ACTIVE s) is (CS, c) in s -> 
    corestep CS ge c m c' m' -> corestep esem ge s m s' m' -> 
    ALL_SAFE ge n (s' \o z) s' m')

  (** Corestates satisfying the invariant can corestep. *)
  (core_prog: forall ge n z s m c CS, 
    ALL_SAFE ge (S n) z s m -> 
    RUNNABLE ge s=true -> CORE (ACTIVE s) is (CS, c) in s -> 
    exists c', exists s', exists m', 
      corestep CS ge c m c' m' /\ corestep esem ge s m s' m' /\
      CORE (ACTIVE s) is (CS, c') in s')

  (** "Handled" steps respect function specifications. *)
  (handled_pres: forall ge s z m (c: cT (ACTIVE s)) s' m' (c': cT (ACTIVE s)) 
      (CS: CoreSemantics G (cT (ACTIVE s)) M D) ef sig args P Q x, 
    let i := ACTIVE s in CORE i is (CS, c) in s -> 
    at_external CS c = Some (ef, sig, args) -> 
    ListSet.set_mem extfunct_eqdec ef handled = true -> 
    spec_of ef csig = (P, Q) -> 
    P x (sig_args sig) args (s \o z) m -> 
    corestep esem ge s m s' m' -> 
    CORE i is (CS, c') in s' -> 
      ((at_external CS c' = Some (ef, sig, args) /\ P x (sig_args sig) args (s' \o z) m' /\
        (forall j, ACTIVE s' = j -> i <> j)) \/
      (exists ret, after_external CS ret c = Some c' /\ Q x (sig_res sig) ret (s' \o z) m')))

  (** "Handled" states satisfying the invariant can step or are safely halted;
     core states that remain "at_external" over handled steps are unchanged. *)
  (handled_prog: forall ge n (z: Zext) (s: xT) m,
    ALL_SAFE ge (S n) (s \o z) s m -> 
    RUNNABLE ge s=false -> 
    at_external esem s = None -> 
    (exists s', exists m', corestep esem ge s m s' m' /\ 
      forall i c CS, CORE i is (CS, c) in s -> 
        exists c', CORE i is (CS, c') in s' /\ 
          (forall ef args ef' args', 
            at_external CS c = Some (ef, args) -> 
            at_external CS c' = Some (ef', args') -> c=c')) \/
    (exists rv, safely_halted esem ge s = Some rv))

  (** Safely halted threads remain halted. *)
  (safely_halted_halted: forall ge s m s' m' i CS c rv,
    CORE i is (CS, c) in s -> 
    safely_halted CS ge c = Some rv -> 
    corestep esem ge s m s' m' -> 
    CORE i is (CS, c) in s')

  (** Safety of other threads is preserved when handling one step of blocked
     thread [i]. *)
  (handled_rest: forall ge s m s' m' c CS,
    CORE (ACTIVE s) is (CS, c) in s -> 
    ((exists ef, exists sig, exists args, at_external CS c = Some (ef, sig, args)) \/ 
      exists rv, safely_halted CS ge c = Some rv) -> 
    at_external esem s = None -> 
    corestep esem ge s m s' m' -> 
    (forall j (CS0: CoreSemantics G (cT j) M D) c0, ACTIVE s <> j ->  
      (CORE j is (CS0, c0) in s' -> CORE j is (CS0, c0) in s) /\
      (forall n z z', CORE j is (CS0, c0) in s -> 
                      safeN CS0 csig ge (S n) (s \o z) c0 m -> 
                      safeN CS0 csig ge n (s' \o z') c0 m')))

  (** If the extended machine is at external, then the active thread is at
     external (an extension only implements external functions, it doesn't
     introduce them). *)
  (at_extern_call: forall s ef sig args,
    at_external esem s = Some (ef, sig, args) -> 
    exists CS, exists c, 
      CORE (ACTIVE s) is (CS, c) in s /\ 
      at_external CS c = Some (ef, sig, args))

  (** Inject the results of an external call into the extended machine state. *)
  (at_extern_ret: forall z s (c: cT (ACTIVE s)) m z' m' tys args ty ret c' CS ef sig x 
      (P: ext_spec_type esig ef -> list typ -> list val -> Zext -> M -> Prop) 
      (Q: ext_spec_type esig ef -> option typ -> option val -> Zext -> M -> Prop),
    CORE (ACTIVE s) is (CS, c) in s -> 
    at_external esem s = Some (ef, sig, args) -> 
    spec_of ef esig = (P, Q) -> 
    P x tys args (s \o z) m -> Q x ty ret z' m' -> 
    after_external CS ret c = Some c' -> 
    exists s': xT, 
      z' = s' \o z' /\
      after_external esem ret s = Some s' /\ 
      CORE (ACTIVE s) is (CS, c') in s')

  (** Safety of other threads is preserved when returning from an external 
     function call. *)
  (at_extern_rest: forall z s (c: cT (ACTIVE s)) m z' s' m' tys args ty ret c' CS ef x sig
      (P: ext_spec_type esig ef -> list typ -> list val -> Zext -> M -> Prop) 
      (Q: ext_spec_type esig ef -> option typ -> option val -> Zext -> M -> Prop),
    CORE (ACTIVE s) is (CS, c) in s -> 
    at_external esem s = Some (ef, sig, args) -> 
    spec_of ef esig = (P, Q) -> 
    P x tys args (s \o z) m -> Q x ty ret z' m' -> 
    after_external CS ret c = Some c' -> 
    after_external esem ret s = Some s' -> 
    CORE (ACTIVE s) is (CS, c') in s' -> 
    (forall j (CS0: CoreSemantics G (cT j) M D) c0, ACTIVE s <> j -> 
      (CORE j is (CS0, c0) in s' -> CORE j is (CS0, c0) in s) /\
      (forall ge n, CORE j is (CS0, c0) in s -> 
                    safeN CS0 csig ge (S n) (s \o z) c0 m -> 
                    safeN CS0 csig ge n (s' \o z') c0 m'))),
  safety_invariant.

End SafetyInvariant. End SafetyInvariant.

Module EXTENSION_SAFETY. Section EXTENSION_SAFETY.
 Variables
  (G: Type) (** global environments *)
  (xT: Type) (** corestates of extended semantics *)
  (cT: nat -> Type) (** corestates of core semantics *)
  (M: Type) (** memories *)
  (D: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)

  (esem: CoreSemantics G xT M D) (** extended semantics *)
  (csem: forall i:nat, option (CoreSemantics G (cT i) M D)) (** a set of core semantics *)

  (csig: ext_sig M Z) (** client signature *)
  (esig: ext_sig M Zext) (** extension signature *)
  (handled: list AST.external_function) (** functions handled by this extension *)
  (E: Extension.Sig cT Zint esem csem csig esig handled). 

Import SafetyInvariant.

Record Sig := Make {_: safety_invariant E -> safe_extension E}.

End EXTENSION_SAFETY. End EXTENSION_SAFETY.

(**  "Compilable" Extensions *)

(*This is an [F,V]-independent definition of meminj_preserves_globals*)
Definition meminj_preserves_globals (globals: list block) f :=
  (forall b, In b globals -> f b = Some (b, 0)) /\
  (forall b1 b2 delta, In b2 globals -> f b1 = Some (b2, delta) -> b1=b2).

Definition genv2blocks {F V: Type} (g: Genv.t F V) := 
  map snd (PTree.elements (Genv.genv_symb g)).

(** Some administrative requirements on the interactions between
   extensions and inner cores. Perhaps some of these conditions could be 
   merged with those for "safe" extensions. *)

Section CoreCompatible.
Variables 
 (G xT M D Z Zint Zext: Type) (cT: nat -> Type)
 (esem: CoreSemantics G xT M D) 
 (csem: forall i:nat, option (CoreSemantics G (cT i) M D))
 (csig: ext_sig M Z)
 (esig: ext_sig M Zext)
 (handled: list AST.external_function)
 (E: Extension.Sig cT Zint esem csem csig esig handled).

Import Extension.

Inductive core_compatible: Type := CoreCompatible: forall
  (** When the active thread is runnable, a step in the extended
     semantics can be tracked back to a corestep of the active
     thread. *)
  (runnable_corestep: forall ge s m s' m' c CS,
    runnable E ge s=true -> 
    csem (active E s) = Some CS -> 
    proj_core E (active E s) s = Some c -> 
    corestep esem ge s m s' m' -> 
    exists c', 
      corestep CS ge c m c' m' /\ 
      proj_core E (active E s) s' = Some c') 

  (** After a corestep of the active inner core, the active thread's new
     corestate is appropriately injected into the extended state. *)
  (corestep_pres: forall ge s (c: cT (active E s)) m c' s' m' CS,
    csem (active E s) = Some CS -> 
    proj_core E (active E s) s = Some c -> 
    corestep CS ge c m c' m' -> 
    corestep esem ge s m s' m' -> 
    active E s = active E s' /\ 
    proj_core E (active E s) s' = Some c')
  (** A corestep of the currently active core forces a corestep of the
     extended semantics*)
  (corestep_prog: forall ge s (c: cT (active E s)) m c' m' CS,
    csem (active E s) = Some CS ->  
    proj_core E (active E s) s = Some c -> 
    corestep CS ge c m c' m' -> 
    exists s', corestep esem ge s m s' m')

  (** Other cores remain unchanged after coresteps of the active core. *)
  (corestep_others_forward: forall ge s s' (c: cT (active E s')) m c' m' CS,
    csem (active E s') = Some CS -> 
    proj_core E (active E s') s' = Some c' -> 
    corestep CS ge c m c' m' -> 
    corestep esem ge s m s' m' -> 
    forall j, (active E s)<>j -> proj_core E j s = proj_core E j s')
  (corestep_others_backward: forall ge s c m s' c' m' CS n,
    csem (active E s) = Some CS -> proj_core E (active E s) s = Some c -> 
    corestepN CS ge n c m c' m' -> corestepN esem ge n s m s' m' -> 
    forall j, (active E s)<>j -> proj_core E j s = proj_core E j s')

  (** The active core doesn't change along active coresteps. *)
  (after_ext_pres: forall s (c: cT (active E s)) c' s' CS retv,
    csem (active E s) = Some CS -> 
    proj_core E (active E s) s = Some c -> 
    after_external CS retv c = Some c' -> 
    after_external esem retv s = Some s' -> 
    active E s=active E s')
  (** The extension state can be updated to match AfterExternal on the 
     active core. *)
  (after_ext_prog: forall s (c: cT (active E s)) c' CS retv,
    csem (active E s) = Some CS -> 
    proj_core E (active E s) s = Some c -> 
    after_external CS retv c = Some c' -> 
    exists s', after_external esem retv s = Some s' /\
      proj_core E (active E s) s' = Some c')

  (** AfterExternal on extension cores leaves all but the active
     corestate unchanged. *)
  (after_ext_others: forall s s' retv,
    after_external esem retv s = Some s' -> 
    forall j, (active E s)<>j -> 
      proj_core E j s = proj_core E j s')

  (** REPEATED HERE TO GET AROUND A BUG IN PROGRAM: 
     HYP (1) NOT GENERATED WHEN PROVING OBLIGATION *)
  (at_extern_call: forall s ef sig args,
    at_external esem s = Some (ef, sig, args) -> 
    exists CS, exists c, 
      csem (active E s) = Some CS /\ proj_core E (active E s) s = Some c /\
      at_external CS c = Some (ef, sig, args)),
  core_compatible.

End CoreCompatible.

(** Rely-Guarantee Simulations *)

Module RelyGuaranteeSimulation. Section RelyGuaranteeSimulation.
 Variables (F1 V1 C1 INIT1 G2 C2 INIT2: Type).
 Variables 
  (sourceC: CoreSemantics (Genv.t F1 V1) C1 mem INIT1)
  (targetC: CoreSemantics G2 C2 mem INIT2) 
  (ge1: Genv.t F1 V1) (ge2: G2) 
  (entry_points: list (val * val * signature)).

 Import Sim_inj.

 Variable (simC: Forward_simulation_inject _ _ sourceC targetC ge1 ge2 entry_points).

 Inductive Sig: Type := Make: forall
  (rely: forall (ge1: Genv.t F1 V1) cdC m1 m1' f f' m2 m2' c1 c2,
    (** Rely *)
    Mem.inject f m1 m2 -> 
    meminj_preserves_globals (genv2blocks ge1) f -> 
    (** Plus other core guarantee*)
    Mem.inject f' m1' m2' -> 
    mem_unchanged_on (loc_unmapped f) m1 m1' ->
    mem_unchanged_on (loc_out_of_reach f m1) m2 m2' ->
    inject_incr f f' -> 
    inject_separated f f' m1 m2 -> 

    (** Match is stable *)
    match_state simC cdC f c1 m1 c2 m2 -> 
    match_state simC cdC f' c1 m1' c2 m2')
    
  (guarantee: forall ge1 ge2 cd cd' m1 m1' f f' m2 m2' c1 c2 c1' c2' n,
    (** Rely *)
    Mem.inject f m1 m2 -> 
    meminj_preserves_globals (genv2blocks ge1) f -> 

    (** Diagram *)
    match_state simC cd f c1 m1 c2 m2 -> 
    corestep sourceC ge1 c1 m1 c1' m1' -> 
    corestepN targetC ge2 n c2 m2 c2' m2' -> 
    match_state simC cd' f' c1' m1' c2' m2' -> 

    (** Guarantee *)
    Mem.inject f' m1' m2' /\ 
    mem_unchanged_on (loc_unmapped f) m1 m1' /\
    mem_unchanged_on (loc_out_of_reach f m1) m2 m2' /\
    inject_incr f f' /\
    inject_separated f f' m1 m2),
  Sig.

End RelyGuaranteeSimulation. End RelyGuaranteeSimulation.

Module CompilabilityInvariant. Section CompilabilityInvariant. 
 Variables
  (F V: Type) (** global environments *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoreSemantics (Genv.t F V) xS mem dS) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F V) xT mem dT) (** extended target semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t F V) (cS i) mem dS) (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t F V) (cT i) mem dT) (** a set of core semantics *)
  (csig: ext_sig mem Z) (** client signature *)
  (esig: ext_sig mem Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Variable (E_S: Extension.Sig cS Zint esemS (fun i:nat => Some (csemS i)) csig esig handled).
 Variable (E_T: Extension.Sig cT Zint esemT (fun i:nat => Some (csemT i)) csig esig handled).

 Variable ge: Genv.t F V.
 Variable entry_points: list (val*val*signature).

 Import Sim_inj.

 Variable core_simulations: forall i:nat, 
   Forward_simulation_inject dS dT (csemS i) (csemT i) ge ge entry_points.

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity). 
 Notation ACTIVE := (Extension.active).
 Notation RUNNABLE := (Extension.runnable).
 Notation "'CORE' i 'is' ( CS , c ) 'in' s" := 
   (csem i = Some CS /\ PROJ_CORE i s = Some c)
   (at level 66, no associativity, only parsing).
 Notation core_exists := (Extension.core_exists).
 Notation active_csem := (Extension.active_csem).
 Notation active_proj_core := (Extension.active_proj_core).
 Notation notat_external_handled := (Extension.notat_external_handled).
 Notation at_external_not_handled := (Extension.at_external_not_handled).
 Notation ext_upd_at_external := (Extension.ext_upd_at_external).
 Notation runnable_false := (Extension.runnable_false).

 Variable core_data: Type.
 Variable core_ord: core_data -> core_data -> Prop.
 Variable match_states: core_data -> meminj -> xS -> mem -> xT -> mem -> Prop.

 Inductive Sig: Type := Make: forall  
     (corestep_runnable: forall s1 c1 m1 c1' m1' s1' s2 c2 m2 c2' m2' s2' n,
       PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
       PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
       RUNNABLE E_S ge s1=RUNNABLE E_T ge s2 -> 
       corestep (csemS (ACTIVE E_S s1)) ge c1 m1 c1' m1' -> 
       corestepN (csemT (ACTIVE E_S s1)) ge n c2 m2 c2' m2' -> 
       corestep esemS ge s1 m1 s1' m1' -> 
       corestepN esemT ge n s2 m2 s2' m2' -> 
       RUNNABLE E_S ge s1'=RUNNABLE E_T ge s2')
     
     (extension_diagram: forall s1 m1 s1' m1' s2 c1 c2 m2 ef sig args1 args2 cd j,
       RUNNABLE E_S ge s1=false -> RUNNABLE E_T ge s2=false -> 
       PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
       PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
       at_external (csemS (ACTIVE E_S s1)) c1 = Some (ef, sig, args1) -> 
       at_external (csemT (ACTIVE E_S s1)) c2 = Some (ef, sig, args2) -> 
       match_states cd j s1 m1 s2 m2 -> 
       Mem.inject j m1 m2 -> 
       Events.meminj_preserves_globals ge j -> 
       Forall2 (val_inject j) args1 args2 -> 
       Forall2 Val.has_type args2 (sig_args sig) -> 
       corestep esemS ge s1 m1 s1' m1' -> 
       exists s2', exists m2', exists cd', exists j',
         inject_incr j j' /\
         Events.inject_separated j j' m1 m2 /\
         match_states cd' j' s1' m1' s2' m2' /\
         corestep esemT ge s2 m2 s2' m2')
     
     (at_external_match: forall s1 m1 s2 c1 c2 m2 ef sig args1 args2 cd j,
       ACTIVE E_S s1=ACTIVE E_T s2 -> 
       RUNNABLE E_S ge s1=RUNNABLE E_T ge s2 -> 
       PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
       PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
       at_external esemS s1 = Some (ef, sig, args1) -> 
       at_external (csemS (ACTIVE E_S s1)) c1 = Some (ef, sig, args1) -> 
       match_state (core_simulations (ACTIVE E_S s1)) cd j c1 m1 c2 m2 -> 
       Mem.inject j m1 m2 -> 
       Events.meminj_preserves_globals ge j -> 
       Forall2 (val_inject j) args1 args2 -> 
       Forall2 Val.has_type args2 (sig_args sig) -> 
       at_external (csemT (ACTIVE E_S s1)) c2 = Some (ef, sig, args2) -> 
       at_external esemT s2 = Some (ef, sig, args2))

     (after_external_runnable: forall ge s1 m1 s2 m2 retv1 retv2 s1' s2' cd j,
       RUNNABLE E_S ge s1=RUNNABLE E_T ge s2 -> 
       match_states cd j s1 m1 s2 m2 -> 
       after_external esemS retv1 s1 = Some s1' -> 
       after_external esemT retv2 s2 = Some s2' ->     
       RUNNABLE E_S ge s1'=RUNNABLE E_T ge s2')
     
     (make_initial_core_diagram: forall ge v1 vals1 s1 m1 v2 vals2 m2 j sig,
       make_initial_core esemS ge v1 vals1 = Some s1 -> 
       Mem.inject j m1 m2 -> 
       Forall2 (val_inject j) vals1 vals2 -> 
       Forall2 Val.has_type vals2 (sig_args sig) -> 
       exists cd, exists s2, 
         make_initial_core esemT ge v2 vals2 = Some s2 /\
         match_states cd j s1 m1 s2 m2)
     
     (safely_halted_step: forall cd j c1 m1 c2 m2 ge v1,
       match_states cd j c1 m1 c2 m2 -> 
       safely_halted esemS ge c1 = Some v1 -> 
       exists v2,
         val_inject j v1 v2 /\
         safely_halted esemT ge c2 = Some v2 /\ 
         Mem.inject j m1 m2)
     
     (safely_halted_diagram: forall cd j m1 m1' m2 rv s1 s2 s1' c1 c2,
       match_states cd j s1 m1 s2 m2 -> 
       PROJ_CORE E_S (ACTIVE E_S s1) s1 = Some c1 -> 
       PROJ_CORE E_T (ACTIVE E_S s1) s2 = Some c2 -> 
       safely_halted (csemS (ACTIVE E_S s1)) ge c1 = Some rv -> 
       corestep esemS ge s1 m1 s1' m1' ->  
       safely_halted (csemT (ACTIVE E_S s1)) ge c2 = Some rv /\
       exists s2', exists m2', exists cd', exists j', 
         inject_incr j j' /\
         Events.inject_separated j j' m1 m2 /\
         corestep esemT ge s2 m2 s2' m2' /\
         match_states cd' j' s1' m1' s2' m2'),
     Sig.

End CompilabilityInvariant. End CompilabilityInvariant.

Module CompilableExtension. Section CompilableExtension. 
 Variables
  (F V: Type) (** global environments *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (cS cT: nat -> Type) (** corestates of source and target core semantics *)
  (dS dT: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoreSemantics (Genv.t F V) xS mem dS) (** extended source semantics *)
  (esemT: CoreSemantics (Genv.t F V) xT mem dT) (** extended target semantics *)
  (csemS: forall i:nat, CoreSemantics (Genv.t F V) (cS i) mem dS) (** a set of core semantics *)
  (csemT: forall i:nat, CoreSemantics (Genv.t F V) (cT i) mem dT) (** a set of core semantics *)
  (csig: ext_sig mem Z) (** client signature *)
  (esig: ext_sig mem Zext) (** extension signature *)
  (handled: list AST.external_function). (** functions handled by this extension *)

 Variable (E_S: Extension.Sig cS Zint esemS (fun i:nat => Some (csemS i)) csig esig handled).
 Variable (E_T: Extension.Sig cT Zint esemT (fun i:nat => Some (csemT i)) csig esig handled).

 Variable ge: Genv.t F V.
 Variable entry_points: list (val*val*signature).

 Import Sim_inj.

 Variable core_simulations: forall i:nat, 
   Forward_simulation_inject dS dT (csemS i) (csemT i) ge ge entry_points.

 Record Sig: Type := Make {
   core_data: Type;
   core_ord: core_data -> core_data -> Prop;
   match_states: core_data -> meminj -> xS -> mem -> xT -> mem -> Prop;
   _ : (forall i: nat, RelyGuaranteeSimulation.Sig (core_simulations i)) -> 
       CompilabilityInvariant.Sig csemS csemT E_S E_T core_simulations match_states -> 
       Forward_simulation_inject dS dT esemS esemT ge ge entry_points
 }.

End CompilableExtension. End CompilableExtension.
