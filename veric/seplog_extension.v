Load loadpath.
Require Import msl.ageable msl.rmaps.
Require Import veric.sim veric.step_lemmas veric.base veric.expr 
               veric.extspec veric.extension veric.juicy_extspec veric.compcert_rmaps
               veric.semax veric.SeparationLogic veric.SeparationLogicSoundness.
Import juicy_mem.

Set Implicit Arguments.

Fixpoint externals (fs: list (ident*fundef)) :=
  match fs with
  | nil => nil
  | (fid,External ef tys ty)::fs' => ef::externals fs'
  | _::fs' => externals fs'
  end.

Module SEPLOG_EXTENSION_SOUNDNESS (EXT_SPEC: EXTERNAL_SPEC). Import EXT_SPEC.

Module SepLog := MakeSeparationLogic(EXT_SPEC). Import SepLog.

Section SeplogExtensionSoundness. 
Variable prog: program.
 Variables
  (xT: Type) (** corestates of extended semantics *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type). (** portion of Z external to extension *)

Definition juicy_csig: juicy_ext_sig Z :=
  mkjuicyextsig (externals (prog_funct prog)) CSL.ExtSpec.Hspec.

Definition initial_cores (i: nat): 
  option (CoreSemantics (Genv.t fundef type) Clight_new.corestate juicy_mem
    jm_init_package) :=
  if eq_nat_dec i 1 then Some (juicy_core_sem Clight_new.cl_core_sem)
  else None.

 Variables
  (esem: CoreSemantics (Genv.t fundef type) xT juicy_mem jm_init_package) (** extended semantics *)
  (juicy_esig: juicy_ext_sig Z)
  (handled: list AST.external_function) (** functions handled by this extension *)
  (E: Extension.Sig (fun _: nat => Genv.t fundef type) (fun _:nat => Clight_new.corestate) 
    Zint esem initial_cores juicy_csig juicy_esig (externals (prog_funct prog)))
  (Hlinkable: linkable (Extension.proj_zext E) (externals (prog_funct prog)) 
    juicy_csig juicy_esig)
 (Hsafe: safe_extension (Genv.globalenv prog) (fun _:nat => Genv.globalenv prog) E)
 (Hinit: forall b q0, 
  Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b -> 
  make_initial_core (juicy_core_sem Clight_new.cl_core_sem) (Genv.globalenv prog) 
          (Vptr b Int.zero) nil = Some q0 -> 
  exists q, make_initial_core esem (Genv.globalenv prog) 
          (Vptr b Int.zero) nil = Some q /\
    Extension.proj_core E 1 q = Some q0).

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
        safeN esem (juicy_link juicy_esig (externals (prog_funct prog))) 
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
if_tac; subst.
intros H8 H9.
unfold jsafeN in H10; simpl in H10|-*.
inv H8.
unfold initial_cores in H7; rewrite H7 in H9; inv H9.
apply H10.
inversion 1.
Qed.

End SeplogExtensionSoundness.

End SEPLOG_EXTENSION_SOUNDNESS.
