Require Import VST.sepcomp.semantics.

Require Import VST.veric.juicy_base.

Require Import VST.veric.juicy_mem.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.juicy_extspec.

Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.mpred.
Require Import VST.veric.seplog.

(*********copied from initial_world***********)
Fixpoint find_id {Σ} (id: ident) (G: funspecs) : option (@funspec Σ) :=
 match G with
 | (id', f)::G' => if eq_dec id id' then Some f else find_id id G'
 | nil => None
 end.

Definition func_at'' `{!heapGS Σ} fsig cc A P Q := func_at (mk_funspec fsig cc A P Q).
(*also copy lemmas on these from initial_world? or isolate in general file?*)

(**********************************************)


Module Type GENERAL_SEPARATION_LOGIC_SOUNDNESS.

Parameter F T: Type. (*Clight instantiates := fundef V:=type*)

Definition genv:Type := Genv.t F T.

(*duplicated from tycontext to prevent specialization to Clight*)
Definition filter_genv (ge: genv) : genviron := Genv.find_symbol ge.
Definition empty_environ (ge: genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

Parameter C: Type.
Parameter Sem: genv -> CoreSemantics C Memory.mem.
Parameter genv_symb_injective: genv -> extspec.injective_PTree block.

Section logic.

Context {Z : Type} `{!gen_heapGS address resource Σ} `{!externalGS Z Σ} `{!invGS_gen hlc Σ}.


Definition jsafeN (Hspec : ext_spec Z) (ge: genv) :=
  jsafe(Σ := Σ)(genv_symb := genv_symb_injective) (Sem ge) Hspec ge.

Definition matchfunspecs (ge : genv) (G : funspecs) (Phi : rmap) :=
forall (b : block) (fsig : funsig)
  (cc : calling_convention) (A : TypeTree)
  (P
   Q : dtfr (AssertTT A)),
(func_at'' fsig cc A P Q (b, 0)) Phi ->
exists
  (id : ident) (P'
                Q' : dtfr (AssertTT A)),
  Genv.find_symbol ge id = Some b /\
  find_id id G = Some (mk_funspec fsig cc A P' Q') /\
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

End GENERAL_SEPARATION_LOGIC_SOUNDNESS.
