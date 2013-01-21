Load loadpath.
Require Import msl.ageable msl.rmaps.
Require Import veric.sim veric.step_lemmas veric.base veric.expr 
               veric.extspec veric.extension veric.juicy_extspec veric.compcert_rmaps
               veric.semax veric.SeparationLogic veric.SeparationLogicSoundness.
Import juicy_mem.

Set Implicit Arguments.

Module SEPLOG_EXTENSION_SOUNDNESS (ExtSpec: EXTERNAL_SPEC). Import ExtSpec.
Module ExtSpec := ExtSpec.
Module SepLog := MakeSeparationLogic(ExtSpec). Import SepLog.

Section SeplogExtensionSoundness. 
Variable prog: program.
 Variables
  (xT: Type) (** corestates of extended semantics *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type). (** portion of Z external to extension *)

Definition juicy_csig: juicy_ext_spec Z := ExtSpec.Hspec.

Definition initial_cores (i: nat): 
  CoreSemantics (Genv.t fundef type) Clight_new.corestate juicy_mem
     jm_init_package := juicy_core_sem Clight_new.cl_core_sem.

 Variables
  (esem: CoreSemantics (Genv.t fundef type) xT juicy_mem jm_init_package) (** extended semantics *)
  (juicy_esig: juicy_ext_spec Zext)
  (E: @Extension.Sig juicy_mem Z Zint Zext (Genv.t fundef type) jm_init_package 
         xT esem juicy_esig (fun _ => Genv.t fundef type) 
         (fun _ => jm_init_package) (fun _ => Clight_new.corestate) 
         (fun _ => juicy_core_sem Clight_new.cl_core_sem) juicy_csig)
  (Hlinkable: linkable (Extension.proj_zext E) (Extension.handled E) juicy_csig juicy_esig)
  (Hsafe: safe_extension (Genv.globalenv prog) (fun _:nat => Genv.globalenv prog) E)
  (*This theorem will need to be generalized at some point; but the generalization may 
    require a corresponding generalization of the soundness theorem of the logic. *)
  (Hsingleton: forall i q, (i > 0)%nat -> Extension.proj_core E i q = None)
  (Hinit: forall b q0, 
   Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b -> 
   make_initial_core (juicy_core_sem Clight_new.cl_core_sem) (Genv.globalenv prog) 
          (Vptr b Int.zero) nil = Some q0 -> 
  exists q, make_initial_core esem (Genv.globalenv prog) 
          (Vptr b Int.zero) nil = Some q /\
    Extension.proj_core E 0 q = Some q0).

Lemma semax_extension_rule (z: Z) (V: varspecs) (G: funspecs) (m: mem):
  CSL.semax_prog prog V G -> 
  Genv.init_mem prog = Some m -> 
  exists b: block, exists q: xT,
    Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
    make_initial_core esem (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
    (forall n: nat,
      exists jm : juicy_mem.juicy_mem,
        juicy_mem.m_dry jm = m /\
        ageable.level jm = n /\
        safeN esem (link_ext_spec (Extension.handled E) juicy_esig) 
            (Genv.globalenv prog) n (Extension.proj_zext E z) q jm).
Proof.
intros H1 H2.
destruct (semax_prog_rule z V G prog m H1 H2) as [b [q0 [H3 [H4 H5]]]].
destruct (Hinit H3 H4) as [q [H6 H7]].
destruct (semax_prog_rule 
  (Extension.zmult E (Extension.proj_zint E q) (Extension.proj_zext E z)) 
  V G prog m H1 H2) 
 as [b' [q0' [H3' [H4' H5']]]].
rewrite H3 in H3'; inv H3'.
rewrite H4 in H4'; inv H4'.
exists b'; exists q; split3; simpl; auto.
intros n; destruct (H5' n) as [jm [H8 [H9 H10]]]; subst.
exists jm; split3; auto.
unfold safe_extension in Hsafe.
simpl.
simpl in Hsafe.
specialize (@Hsafe (@ageable.level _ ag_rmap (m_phi jm)) q jm).
eapply Hsafe.
unfold all_safe.
unfold initial_cores.
intros i ? ?.
destruct E; simpl in *.
assert (Heq: (i = 0)%nat).
 specialize (@Hsingleton i q).
 destruct i; auto.
 rewrite Hsingleton in H.
 congruence.
 omega.
rewrite Heq in *; clear Heq.
rewrite H7 in H; inv H.
unfold jsafeN in H10; simpl in H10|-*.
solve[apply H10].
Qed.

End SeplogExtensionSoundness.

End SEPLOG_EXTENSION_SOUNDNESS.
