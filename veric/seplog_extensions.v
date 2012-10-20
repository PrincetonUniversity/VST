Load loadpath.
Require Import msl.ageable msl.rmaps.
Require Import veric.sim veric.step_lemmas veric.base veric.expr 
               veric.extspec veric.extensions veric.juicy_extspec veric.compcert_rmaps
               veric.semax veric.SeparationLogic veric.SeparationLogicSoundness.
Import juicy_mem.

Set Implicit Arguments.

Fixpoint externals (fs: list (ident*fundef)) :=
  match fs with
  | nil => nil
  | (fid,External ef tys ty)::fs' => ef::externals fs'
  | _::fs' => externals fs'
  end.

Record juicy_extsig (Z: Type): Type := mk_juicy_extsig {
  JE_extspec:> juicy_ext_spec Z;
  JE_functs:> list external_function
}.

Definition juicy_extsig2extsig (Z: Type) (je: juicy_extsig Z) :=
  mk_extsig (JE_functs je) (JE_extspec je).
Coercion juicy_extsig2extsig: juicy_extsig >-> extsig.

(*should make juicy_linking more general; move somewhere else
   also: defn. needs to be changed to use the appropriate extspec.*)
Definition juicy_link (Z1 Z2: Type) (sigma1: juicy_extsig Z1) (sigma2: juicy_extsig Z2) :=
  mk_juicy_extsig sigma1 (ListSet.set_diff extfunc_eqdec sigma1 sigma2).

Module SEPLOG_EXTENSION_SOUNDNESS (EXT_SPEC: EXTERNAL_SPEC). Import EXT_SPEC.
Module SepLog := MakeSeparationLogic EXT_SPEC. Import SepLog.
Section seplog_extension_soundness. Variable (prog: program).

Definition juicy_Hsig: juicy_extsig Z := 
  mk_juicy_extsig Hspec (externals (prog_funct prog)).

Variables (C: Type) (je: juicy_extsig (Z*C)) (Hlinkable: linkable fst juicy_Hsig je).

Definition initial_cores (i: nat) := 
  if eq_nat_dec i 1 then Some (juicy_core_sem Clight_new.cl_core_sem)
  else None.

(*the following restrictions on the extension definition may need to be nuanced a bit*)
Let gT := Genv.t fundef type.
Variable (ext_coresem: CoreSemantics gT (Z*C) juicy_mem jm_init_package).
Variable (ext: Extension.Sig ext_coresem initial_cores juicy_Hsig je).
Variable (Hsafe: safe_extension ext).
Variable (Hinit: forall z b q0, 
  Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b -> 
  make_initial_core (juicy_core_sem Clight_new.cl_core_sem) (Genv.globalenv prog) 
          (Vptr b Int.zero) nil = Some q0 -> 
  exists q, make_initial_core ext_coresem (Genv.globalenv prog) 
          (Vptr b Int.zero) nil = Some (z, q) /\
    Extension.proj_core ext (z, q) 1 = Some q0).
Variable (Hproj_ext: forall z q, Extension.proj_ext_state ext (z,q) = z).

Theorem semax_extension_rule (z: Z) (G: funspecs) (m: mem) :
  CSL.semax_prog prog G -> 
  Genv.init_mem prog = Some m -> 
  exists b: block, exists q: Z*C,
    Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
    make_initial_core ext_coresem (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
    (forall n: nat,
      exists jm : juicy_mem.juicy_mem,
        juicy_mem.m_dry jm = m /\
        ageable.level jm = n /\
        safeN ext_coresem (juicy_link juicy_Hsig je) (Genv.globalenv prog) n z (z, snd q) jm).
Proof.
intros H1 H2.
destruct (semax_prog_rule z G prog m H1 H2) as [b [q0 [H3 [H4 H5]]]].
destruct (Hinit z H3 H4) as [q [H6 H7]].
exists b; exists (z,q); split3; simpl; auto.
intros n; destruct (H5 n) as [jm [H8 [H9 H10]]]; subst.
exists jm; split3; auto.
unfold safe_extension in Hsafe.
simpl.
simpl in Hsafe.
specialize (@Hsafe (Genv.globalenv prog) (@ageable.level _ ag_rmap (m_phi jm)) (z,q) jm).
rewrite Hproj_ext in Hsafe.
apply Hsafe.
unfold Extension.all_safe.
unfold initial_cores.
intros i ? ?.
if_tac; subst.
rewrite Hproj_ext.
intros H8 H9.
unfold jsafeN in H10; simpl in H10|-*.
inv H8.
unfold initial_cores in H7; rewrite H7 in H9; inv H9.
apply H10.
inversion 1.
Qed.

End seplog_extension_soundness. 
End SEPLOG_EXTENSION_SOUNDNESS.

