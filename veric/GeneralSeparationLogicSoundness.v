Require Import VST.sepcomp.semantics.

Require Import VST.veric.juicy_base. 

Require Import VST.veric.juicy_mem.  
Require Import VST.sepcomp.extspec.
Require Import VST.veric.ghost_PCM.
Require Import VST.veric.juicy_extspec.

Require Import VST.veric.res_predicates.
Require Import VST.veric.mpred.
Require Import VST.veric.seplog.

(*Require Import VST.veric.initial_world. 
Require Import VST.veric.SeparationLogic.
 *)

(*********copied from initial_world***********)
Fixpoint find_id (id: ident) (G: funspecs) : option funspec  :=
 match G with
 | (id', f)::G' => if eq_dec id id' then Some f else find_id id G'
 | nil => None
 end.

Definition cond_approx_eq n A P1 P2 :=
  (forall ts,
      fmap (dependent_type_functor_rec ts (AssertTT A)) (approx n) (approx n) (P1 ts) =
      fmap (dependent_type_functor_rec ts (AssertTT A)) (approx n) (approx n) (P2 ts)).

Definition func_at'' fsig cc A P Q :=
  pureat (SomeP (SpecTT A) (packPQ P Q)) (FUN fsig cc).
(*also copy lemmas on these from initial_world? or isolate in general file?*)

(**********************************************)


Module Type GENERAL_SEPARATION_LOGIC_SOUNDNESS.

(*Declare Module ExtSpec: EXTERNAL_SPEC. *) 
(*Declare Module CSL: CLIGHT_SEPARATION_LOGIC.
Import CSL. for semax_prog*)


Parameter F T: Type. (*Clight instantiates := fundef V:=type*)
(*Record genv : Type := Build_genv { genv_genv : @Genv.t F T;  genv_cenv : composite_env }.

Parameter genv:Type.
*)
Definition genv:Type := Genv.t F T.

(*duplicated from tycontext to prevent specialization to Clight*)
Definition filter_genv (ge: genv) : genviron := Genv.find_symbol ge.
Definition empty_environ (ge: genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

Parameter C: Type.
Parameter Sem: genv -> CoreSemantics C Memory.mem.

(*Definition genv_symb_injective {F V} (ge: Genv.t F V) : extspec.injective_PTree block.
Proof.
exists (Genv.genv_symb ge).
hnf; intros.
eapply Genv.genv_vars_inj; eauto.
Defined.*)
(*Parameter genv_symb_injective: forall {F V:Type} (ge: Genv.t F V), extspec.injective_PTree block.*)
Parameter genv_symb_injective: genv -> extspec.injective_PTree block.

Definition jsafeN {Z} (Hspec : juicy_ext_spec Z) (ge: genv) :=
  @jsafeN_ genv _ _ genv_symb_injective (*(genv_symb := fun ge: genv => Genv.genv_symb ge)*)
           (Sem ge) Hspec ge.

Definition matchfunspecs (ge : genv) (G : funspecs) (Phi : rmap) :=
forall (b : block) (fsig : compcert_rmaps.funsig)
  (cc : calling_convention) (A : TypeTree)
  (P
   Q : forall ts : list Type,
       (dependent_type_functor_rec ts (AssertTT A)) (pred rmap)),
(func_at'' fsig cc A P Q (b, 0)) Phi ->
exists
  (id : ident) (P'
                Q' : forall ts : list Type,
                     (dependent_type_functor_rec ts (AssertTT A)) mpred) 
(P'_ne : super_non_expansive P') (Q'_ne : super_non_expansive Q'),
  Genv.find_symbol ge id = Some b /\
  find_id id G = Some (mk_funspec fsig cc A P' Q' P'_ne Q'_ne) /\
  cond_approx_eq (level Phi) A P P' /\ cond_approx_eq (level Phi) A Q Q'.

Definition EPoint_sound {Espec: OracleKind} FS m (h:nat) (entryPT:ident) (g:genv) :=
     { b : block & { q : C &
       (Genv.find_symbol g entryPT = Some b) *
       (forall jm, m_dry jm = m -> exists jm', semantics.initial_core (juicy_core_sem (Sem g)) h
                    jm q jm' (Vptr b Ptrofs.zero) nil) *
       forall n z,
         { jm |
           m_dry jm = m /\ level jm = n /\
           nth_error (ghost_of (m_phi jm)) 0 = Some (Some (ext_ghost z, NoneP)) /\
           jsafeN (@OK_spec Espec) g n z q jm /\
           res_predicates.no_locks (m_phi jm) /\
           matchfunspecs g FS (m_phi jm) /\
           app_pred (funspecs_assert (make_tycontext_s FS) (empty_environ g))  (m_phi jm) } } }%type.

(*maybe generalize from single EP ("main") to multiple entry points?
Axiom module_sound: forall Espec G m h entryPT g,
      @EPoint_sound Espec G m h entryPT g.

Definition prog_sound {Espec: OracleKind} CS prog :=
     @semax_prog Espec CS prog V G ->
     forall h m,
     @Genv.init_mem F T prog = Some m ->
     @EPoint_sound Espec G m h (prog_main prog)  (globalenv prog).
                                    *)

End GENERAL_SEPARATION_LOGIC_SOUNDNESS.
