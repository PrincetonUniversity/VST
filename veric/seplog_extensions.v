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

Module SEPLOG_EXTENSION_SOUNDNESS (EXT_SPEC: EXTERNAL_SPEC). Import EXT_SPEC.
Module SepLog := MakeSeparationLogic EXT_SPEC. Import SepLog.
Section seplog_extension_soundness. Variable (prog: program).

Definition juicy_client_sig: juicy_ext_sig Z :=
  mkjuicyextsig (externals (prog_funct prog)) Hspec.

Variables (juicy_esig: juicy_ext_sig Z)
  (Hlinkable: linkable (externals (prog_funct prog)) juicy_client_sig juicy_esig).

Definition initial_cores (i: nat) := 
  if eq_nat_dec i 1 then Some (juicy_core_sem Clight_new.cl_core_sem)
  else None.

(*the following restrictions on the extension definition may need to be nuanced a bit*)
Let gT := Genv.t fundef type.
Variables (xT Zint Zext: Type).
Variable (ext_coresem: CoreSemantics gT xT juicy_mem jm_init_package).

Variable (ext: Extension.Sig Zint Zext ext_coresem initial_cores 
                 juicy_client_sig juicy_esig (externals (prog_funct prog))).
Variable (Hsafe: safe_extension ext).
Variable (Hinit: forall b q0, 
  Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b -> 
  make_initial_core (juicy_core_sem Clight_new.cl_core_sem) (Genv.globalenv prog) 
          (Vptr b Int.zero) nil = Some q0 -> 
  exists q, make_initial_core ext_coresem (Genv.globalenv prog) 
          (Vptr b Int.zero) nil = Some q /\
    Extension.proj_core ext q 1 = Some q0).

Theorem semax_extension_rule (z: Z) (G: funspecs) (m: mem) :
  CSL.semax_prog prog G -> 
  Genv.init_mem prog = Some m -> 
  exists b: block, exists q: xT,
    Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
    make_initial_core ext_coresem (Genv.globalenv prog) (Vptr b Int.zero) nil = Some q /\
    (forall n: nat,
      exists jm : juicy_mem.juicy_mem,
        juicy_mem.m_dry jm = m /\
        ageable.level jm = n /\
        safeN ext_coresem (juicy_link juicy_esig (externals (prog_funct prog))) 
            (Genv.globalenv prog) n (Extension.zmult ext (Extension.proj_zint ext q) 
               (Extension.proj_zext ext z)) q jm).
Proof.
intros H1 H2.
destruct (semax_prog_rule z G prog m H1 H2) as [b [q0 [H3 [H4 H5]]]].
destruct (Hinit H3 H4) as [q [H6 H7]].
destruct (semax_prog_rule 
  (Extension.zmult ext (Extension.proj_zint ext q) (Extension.proj_zext ext z)) 
  G prog m H1 H2) 
 as [b' [q0' [H3' [H4' H5']]]].
rewrite H3 in H3'; inv H3'.
rewrite H4 in H4'; inv H4'.
exists b'; exists q; split3; simpl; auto.
intros n; destruct (H5' n) as [jm [H8 [H9 H10]]]; subst.
exists jm; split3; auto.
unfold safe_extension in Hsafe.
simpl.
simpl in Hsafe.
specialize (@Hsafe (Genv.globalenv prog) (@ageable.level _ ag_rmap (m_phi jm)) q jm).
eapply Hsafe.
unfold Extension.all_safe.
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

End seplog_extension_soundness. 
End SEPLOG_EXTENSION_SOUNDNESS.

