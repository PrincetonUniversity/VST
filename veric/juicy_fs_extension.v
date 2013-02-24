Load loadpath.

Require Import compositional_compcert.Coqlib2.
Require Import compositional_compcert.core_semantics.
Require Import compositional_compcert.forward_simulations.
Require Import compositional_compcert.step_lemmas.
Require Import compositional_compcert.extspec.
Require Import compositional_compcert.extension.
Require Import compositional_compcert.extension_safety.
Require Import compositional_compcert.extension_simulations.
Require Import compositional_compcert.extension_proof.
Require Import compositional_compcert.fs_extension.

Require Import veric.juicy_mem.
Require Import veric.juicy_extspec.

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Ctypes.
Require Clight.

Set Implicit Arguments.

Section FSExtension.
Variables 
  (Z cT D: Type) 
  (csem: CoreSemantics genv cT mem D)
  (init_world: Z).

Definition cores := fun _:nat => csem.

Local Open Scope nat_scope.

Definition Client_FSExtSpec' :=
  Build_external_specification juicy_mem AST.external_function (fs*Z)
  (fun ef: AST.external_function => address) 
  (fun ef u typs args fsz jm => fs_pre ef u typs args fsz (m_dry jm)) 
  (fun ef u ty retval0 fsz jm => fs_post ef u ty retval0 fsz (m_dry jm)).

Program Definition Client_JuicyFSExtSpec := 
  Build_juicy_ext_spec (fs*Z) Client_FSExtSpec' _ _.
Next Obligation. 
hnf; intros a a' H. 
destruct e; auto.
destruct name; auto.
destruct name; auto.
destruct sg; auto.
destruct sig_args; auto.
destruct t0; auto.
destruct sig_args; auto.
destruct t0; auto.
destruct sig_args; auto.
destruct t0; auto.
destruct sig_args; auto.
destruct sig_res; auto.
destruct t0; auto.
destruct args; auto.
destruct args; auto.
destruct args; auto.
destruct args; auto.
destruct (val2oint v); auto.
destruct (val2oadr v0); auto.
destruct (val2oint v1); auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
apply age_jm_dry in H.
rewrite <-H.
auto.
Qed.
Next Obligation. 
hnf; intros a a' H; destruct e; auto. 
apply age_jm_dry in H.
rewrite <-H.
auto.
Qed.

Lemma empty_rmap_no (lev: nat) loc: 
  compcert_rmaps.R.resource_at (compcert_rmaps.RML.empty_rmap lev) loc = 
  compcert_rmaps.R.NO shares.Share.bot.
Proof.
unfold compcert_rmaps.RML.empty_rmap.
unfold compcert_rmaps.RML.empty_rmap'.
unfold compcert_rmaps.R.resource_at.
rewrite compcert_rmaps.R.unsquash_squash; simpl.
unfold base.compose; simpl; auto.
Qed.

Lemma exists_ok_rmap (m: mem) (lev: nat): 
  exists phi, initial_rmap_ok m phi /\ ageable.level phi=lev.
Proof.
exists (compcert_rmaps.RML.empty_rmap lev); split.
unfold initial_rmap_ok.
intros.
rewrite <-compcert_rmaps.RML.core_resource_at.
rewrite empty_rmap_no.
rewrite compcert_rmaps.RML.core_NO; auto.
apply compcert_rmaps.RML.empty_rmap_level.
Qed.

Lemma juicy_mem_exists (lev: nat) (m: mem): 
  exists jm, m_dry jm=m /\ ageable.level jm=lev.
Proof.
destruct (exists_ok_rmap m lev) as [phi [H1 H2]].
exists (initial_mem m phi H1).
split; auto.
simpl.
unfold inflate_initial_mem.
rewrite level_make_rmap.
auto.
Qed.

Lemma juicy_safeN_safeN ge n z c jm :
  safeN (juicy_core_sem csem) Client_JuicyFSExtSpec ge n z c jm -> 
  safeN csem (Client_FSExtSpec _) ge n z c (m_dry jm).
Proof.
revert jm z c; induction n; auto.
intros jm z c H1.
hnf.
hnf in H1.
case_eq (at_external (juicy_core_sem csem) c).
intros [[ef sig] args] H2.
rewrite H2 in H1.
inv H2.
rewrite H0.
case_eq (safely_halted (juicy_core_sem csem) c).
intros rv H2.
rewrite H2 in H1.
elimtype False; auto.
intros H2.
rewrite H2 in H1.
inv H2.
unfold j_safely_halted in H3.
rewrite H3.
destruct H1 as [x [H1 H2]].
exists x.
split; auto.
intros ret m' z' H4.
destruct (juicy_mem_exists (ageable.level jm) m') as [jm' [H5 H6]].
specialize (H2 ret jm' z').
spec H2; auto.
simpl in H4|-*.
rewrite H5; auto.
destruct H2 as [c' [H2 H7]].
exists c'.
split; auto.
rewrite <-H5.
eapply IHn; eauto.
intros H2.
rewrite H2 in H1.
inv H2.
rewrite H0.
case_eq (safely_halted (juicy_core_sem csem) c).
intros rv H2.
rewrite H2 in H1.
inv H2.
unfold j_safely_halted in H3.
rewrite H3; auto.
intros H2.
rewrite H2 in H1.
inv H2.
unfold j_safely_halted in H3.
rewrite H3; auto.
destruct H1 as [c' [jm' [H1 H2]]].
exists c'; exists (m_dry jm').
split; auto.
inv H1.
auto.
Qed.

Variable FSExtSpec: ext_spec Z.
Variable FSExtSpec_linkable: linkable (@proj_zext Z)
  (fun (ef: AST.external_function) => forall (s: @xT Z cT) c sig args,
    proj_core (active s) s = Some c -> 
    at_external csem c = Some (ef, sig, args) -> 
    @os_at_external Z cT D csem s = None)
  (Client_FSExtSpec Z) FSExtSpec.
Variable ge: genv.

Program Definition fs_extension := 
  @Extension.Make 
    _ _ _ _ _ _ _
    (@FSCoreSem Z cT D csem init_world) FSExtSpec
    (fun _ => genv) (fun _ => D) (fun _ => cT) (fun _ => csem)
    (Client_FSExtSpec Z)
    (const 1)
    (@proj_core Z cT) _
    (@active Z cT) _ 
    (@proj_zint Z cT)
    (@proj_zext Z)
    (@zmult Z) _ _   
    FSExtSpec_linkable
    _.
Next Obligation. unfold proj_core. if_tac; auto. unfold const in *. 
 rewrite H0 in H; elimtype False; omega. Qed.
Next Obligation. unfold proj_core, active; if_tac; try congruence; eauto. Qed.
Next Obligation.
unfold os_after_external in H0.
destruct (after_external csem ret (get_core s)); try congruence.
solve[inv H0; auto].
Qed.
Next Obligation. Admitted. (*stupid Program issue...*)

Lemma mem_range_perm_sub m b ofs sz sz' k p :
  Mem.range_perm m b ofs sz' k p -> 
  (sz <= sz')%Z -> 
  Mem.range_perm m b ofs sz k p.
Proof.
unfold Mem.range_perm.
intros H1 H2.
intros ofs' H3.
specialize (H1 ofs').
spec H1.
omega.
auto.
Qed.

Import ExtensionSafety.

Lemma fs_extension_safe (csem_fun: corestep_fun csem): 
 safe_extension ge (fun _:nat => ge) fs_extension.
Proof.
destruct (ExtensionSafety ge (fun _:nat => ge) fs_extension) as [PF00].
apply PF00; constructor.

(*1: core preservation of all-safety invariant*)
intros until m'; intros H1 (*H2*) H4 H5 H6.
assert (H3:True) by auto.
assert (get_core s'=c').
 clear -H4 H5 H6 csem_fun.
 unfold cores in H5.
 simpl in H4.
 inversion H6; subst; simpl in *.
 unfold active, proj_core in H4; simpl in H4.
 inv H4.
 generalize (csem_fun _ _ _ _ _ _ _ H5 H); inversion 1; auto.
 apply corestep_not_at_external in H5.
 unfold active, proj_core in H4.
 if_tac in H4; try congruence.
 apply corestep_not_at_external in H5.
 unfold active, proj_core in H4.
 if_tac in H4; try congruence.
 apply corestep_not_at_external in H5.
 unfold active, proj_core in H4.
 solve[if_tac in H4; try congruence].
rewrite <-H in *.
hnf.
intros i2 c2 H8.
assert (H7:True) by auto.
hnf in H1.
specialize (H1 (active s) c).
spec H1; auto.
unfold cores.
clear H3.
assert (H3: c'=c2).
 destruct s'.
 simpl in H.
 rewrite <-H.
 inversion H8.
 unfold proj_core in H2.
 if_tac in H2; try congruence.
 solve[inversion H2; auto].
rewrite <-H3 in *.
rewrite <-H.
eapply safe_corestep_forward; eauto.
assert (H2: Extension.zmult fs_extension (Extension.proj_zint fs_extension s') =
            Extension.zmult fs_extension (Extension.proj_zint fs_extension s)).
 clear - H4 H5 H6.
 inversion H4.
 inv H0.
 inv H6; auto.
 elimtype False.
  apply corestep_not_at_external in H5.
  unfold cores, Extension.active in H5.
  solve[rewrite H5 in H; congruence].
 elimtype False.
  apply corestep_not_at_external in H5.
  unfold cores, Extension.active in H5.  
  solve[rewrite H5 in H; congruence].
unfold SafetyInvariant.proj_zint.
unfold cores in H2.
solve[rewrite H2; auto].

(*2: core progress*)
intros until c; intros H1 H2 (*H3*) H5.
assert (H4:True).
hnf in H1.
specialize (H1 (active s) c).
spec H1; auto.
inversion H5.
inv H0.
simpl in H2; unfold runnable in H2.
hnf in H1.
simpl in H5.
destruct s; simpl in H2.
specialize (H1 (active (mkxT z0 c fs)) c).
simpl in H1.
unfold rg_forward_simulations.runnable in H3.
unfold active, cores in *.
spec H1; auto.
destruct (at_external csem c) as [[[ef sig] args]|]; try congruence.
destruct (safely_halted csem c); try congruence.
destruct H1 as [c' [m' [H1 H6]]].
exists c'; exists (mkxT z0 c' fs); exists m'.
split; auto.
split; auto.
unfold proj_core in H2.
if_tac in H2; try congruence.
simpl in H2.
inv H2.
simpl.
solve[apply os_corestep; auto].

(*SYS_READ/WRITE_SIG: fd, buf, count*)
Notation SYS_READ_SIG := (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation SYS_WRITE_SIG := (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint)).
(*SYS_OPEN_SIG: name*)
Notation SYS_OPEN_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).

Notation SYS_READ := (EF_external 3%positive SYS_READ_SIG).
Notation SYS_WRITE :=  (EF_external 4%positive SYS_WRITE_SIG).
Notation SYS_OPEN := (EF_external 8%positive SYS_OPEN_SIG).

(*3: handled steps respect function specs.*)
intros until x.
hnf; intros H2 H3 H4 H5 Hpre Hstep H7.
assert (H1:True) by auto.
assert (H6:True) by auto.
inv H2.
inversion Hstep.
rewrite <-H8, <-H9, <-H10 in *.
clear H8 H9 H10.
(*corestep case; impossible*)
elimtype False.
apply corestep_not_at_external in H.
simpl in H3.
unfold cores, active, get_core in H3.
destruct s; auto.
inv H2.
solve[rewrite H in H3; congruence].
(*SYS_OPEN case*)
assert (Hef: ef = SYS_OPEN).
 clear - H H3.
 unfold cores, active, get_core in H3.
 destruct s; auto.
 simpl in H.
 rewrite H in H3.
 solve[inversion H3; auto].
rewrite Hef in *.
right.
exists (Some (Vint unused_fd)).
rewrite <-H15 in H7.
split; auto.
simpl.
unfold cores, active; auto.
rewrite H11.
f_equal.
simpl in H7.
unfold proj_core, active in H7.
if_tac in H7; try congruence.
inversion H7; auto.
simpl.
unfold spec_of in H5.
clear H12.
rename H10 into H12.
clear - H5 H12.
(*inversion H5 fails to terminate in a timely fashion; instead we 
   use this ad hoc lemma*)
assert (forall {A B: Type} (P P': A) (Q Q': B), (P,Q) = (P',Q') -> P=P' /\ Q=Q').
 solve[inversion 1; auto].
apply H in H5.
destruct H5 as [H5 H6].
rewrite <-H6.
hnf; unfold fs_post; simpl; auto.
unfold fs_open in H12.
if_tac in H12.
case_eq (get_fstore fs fname).
intros f H1; rewrite H1 in H12.
inversion H12; subst.
hnf.
exists md; exists 0; exists f.
unfold get_fdtable, get_fcache, fs_open_existing; simpl.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
intros H1; rewrite H1 in H12.
inversion H12; subst.
hnf.
unfold get_fdtable, get_fcache, fs_open_existing; simpl.
exists md; exists 0; exists new_file.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
hnf.
destruct (get_fstore fs fname).
inversion H12; subst.
exists md; exists 0; exists f.
unfold get_fdtable, get_fcache; simpl.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
congruence.
(*SYS_READ case*)
assert (Hef: ef = SYS_READ).
 unfold cores, Extension.active in H3.
 solve[rewrite H in H3; inversion H3; auto].
right.
exists (Some (Vint (Int.repr (Zlength bytes)))).
split; auto.
simpl.
unfold spec_of in H5.
rewrite Hef in *.
unfold cores, active.
rewrite <-H15 in H7.
simpl in H7.
unfold proj_core, active in H7.
if_tac in H7; try congruence.
inversion H7.
rewrite H11.
solve[auto].
assert (Heq: x = adr).
 unfold cores, Extension.active in H3.
 rewrite H in H3.
 inversion H3.
 rewrite <-H20 in *.
 inversion H5; subst.
 simpl in Hpre.
 rewrite H0, H2, H8 in Hpre.
 solve[destruct Hpre; auto].
clear -Heq Hef H5 H9 H10 H11.
assert (forall {A B: Type} (P P': A) (Q Q': B), (P,Q) = (P',Q') -> P=P' /\ Q=Q').
 solve[inversion 1; auto].
apply H in H5.
destruct H5 as [H5 H6].
rewrite <-H6.
simpl; auto.
rewrite Hef.
remember (Int.repr (Zlength bytes)) as N.
simpl.
exists bytes.
split; auto.
apply Mem.loadbytes_storebytes_same in H10.
rewrite Zlength_correct in HeqN.
assert (Hlen: (0 <= Z_of_nat (length bytes) < Int.modulus)%Z).
 split.
 apply Zle_0_nat; auto.
 unfold fs_read in H9.
 destruct (get_file fs fd); try congruence.
 destruct (get_fptr fs fd); try congruence.
 unfold read_file in H9.
 inversion H9.
 generalize (read_file_aux_length f (nat_of_Z (Int.unsigned nbytes)) (get_size f) f0);
  intro H2.
 apply Zle_lt_trans with (m := Int.unsigned nbytes).
 apply inj_le in H2.
 rewrite nat_of_Z_eq in H2; auto.
 destruct nbytes as [? [Pf1 Pf2]]; simpl in *; omega.
 destruct nbytes as [? [Pf1 Pf2]]; simpl in *; omega.
 change (Int.unsigned N) with (Int.unsigned N).
 subst N x; rewrite Int.unsigned_repr; auto.
 unfold Int.max_unsigned; omega.
(*SYS_WRITE case*)
right.
exists (Some (Vint (Int.repr (Z_of_nat nbytes_written)))).
split; auto.
rewrite <-H15 in H7.
simpl in H7.
unfold proj_core, active in H7.
if_tac in H7; try congruence.
inversion H7.
unfold cores, active.
solve[rewrite H11; auto].
simpl.
unfold spec_of in H5.
assert (Hef: ef = SYS_WRITE).
 unfold cores, Extension.active in H3.
 rewrite H in H3.
 solve[inversion H3; auto].
clear - Hef H5.
rewrite Hef in *.
assert (forall {A B: Type} (P P': A) (Q Q': B), (P,Q) = (P',Q') -> P=P' /\ Q=Q').
 inversion 1; auto.
apply H in H5.
destruct H5 as [H5 H6].
rewrite <-H6.
solve[simpl; auto].

(*4: handled progress*)
intros until c; intros H1 H2 H3.
inv H2.
unfold safely_halted.
simpl.
unfold os_safely_halted.
hnf in H1.
specialize (H1 (active s) (get_core s)).
spec H1; auto.
hnf in H1.
rename H3 into H0.
unfold rg_forward_simulations.runnable in H0.
case_eq (at_external csem (get_core s)). 
intros [[ef sig] args] Hat.
(*at_external core = Some*)
unfold cores, active in H1.
rewrite Hat in *.
destruct (safely_halted csem (get_core s)).
solve[elimtype False; auto].
destruct H1 as [x [H1 H2]].
left.
destruct ef; try solve[elimtype False; simpl in H1; auto].
destruct name; try solve[elimtype False; simpl in H1; auto].
destruct name; try solve[elimtype False; simpl in H1; auto].
destruct sg; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct sig_res; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
simpl in H1.
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
case_eq (val2oint v); try solve[elimtype False; simpl in H1; auto].
case_eq (val2oadr v0); try solve[elimtype False; simpl in H1; auto].
case_eq (val2oint v1); try solve[elimtype False; simpl in H1; auto].
intros.
rewrite H3, H4, H5 in H1.

(*SYS_READ case*)
destruct H1 as [Heq [H1 [H6 H7]]].
unfold proj_zint in H6.
destruct H6 as [md [cur [f' [H6 H8]]]].
apply mem_range_perm_sub with 
 (sz := (snd a + Z_of_nat (length (read_file_aux f' (nat_of_Z (Int.unsigned i)) 
                             (get_size f') cur)))%Z)
 in H7.
destruct a as [b ofs].
simpl in H7.
apply Mem.range_perm_storebytes in H7.
destruct H7 as [m' H7].
specialize (H2 
  (Some (Vint
    (Int.repr
      (Zlength
        (read_file_aux f' (nat_of_Z (Int.unsigned i)) 
          (get_size f') cur)))))
  m'
  (get_fs s, z)).
spec H2.
 case_eq (eq_nat_dec
 (length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur))
 (nat_of_Z (Int.unsigned i))).
intros Heq'.
exists (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur).
split; auto.
apply Mem.loadbytes_storebytes_same in H7.
rewrite Zlength_correct.
rewrite Heq' in H7|-*.
destruct x; inv Heq.
rewrite Int.unsigned_repr. unfold fst, snd; auto.
rewrite nat_of_Z_eq.
 apply Int.unsigned_range_2.
 destruct (Int.unsigned_range_2 i); omega.
intros Hneq.
assert (H11: 
  length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur) <
  nat_of_Z (Int.unsigned i)).
 generalize (read_file_aux_length f' 
             (nat_of_Z (Int.unsigned i)) (get_size f') cur); intro H12.
 omega.
intros _.
exists (read_file_aux f' 
 (length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur)) 
 (get_size f') cur).
apply Mem.loadbytes_storebytes_same in H7.
repeat rewrite Zlength_correct.
destruct x; inv Heq.
rewrite <-read_file_aux_length2; auto.
split; auto.
rewrite Int.unsigned_repr. unfold fst, snd.
rewrite <- read_file_aux_id.
auto.
split. omega.
clear - H11.
forget (length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur)) as N.
apply inj_lt_iff in H11.
 destruct (Int.unsigned_range_2 i).
rewrite nat_of_Z_eq in H11; omega.

destruct H2 as [c' [H9 H10]].
exists (mkxT z c' (get_fs s)); exists m'.
split.
eapply os_read; eauto.
unfold fs_read.
unfold get_file.
unfold fs_extension.proj_zint in H6, H8.
rewrite H8.
unfold get_fptr.
rewrite H6.
eauto.
(*core stayed at_external: impossible*)
intros.
exists c'.
split; auto.
unfold proj_core in H2.
if_tac in H2; try congruence.
inv H2.
solve[auto].
intros.
elimtype False.
unfold proj_core in H2.
if_tac in H2; try congruence.
apply (after_at_external_excl csem) in H9.
unfold cores in *.
inversion H2.
rewrite H15 in *.
clear H15.
rewrite H9 in H12.
congruence.
apply Zplus_le_compat_l.
assert (H9: 
 length (read_file_aux f' (nat_of_Z (Int.unsigned i)) (get_size f') cur) <=
 nat_of_Z (Int.unsigned i)).
 apply read_file_aux_length.
assert (H10: (Z_of_nat (nat_of_Z (Int.unsigned i)) <= Int.unsigned i)%Z).
 rewrite nat_of_Z_max.
 rewrite Z.max_lub_iff.
 split; auto.
 apply Zle_refl.
 apply Int.intrange.
apply Zle_trans with (m := Z_of_nat (nat_of_Z (Int.unsigned i))); auto.
apply inj_le; auto.
(*degenerate cases*)
intros H4; rewrite H4 in H1.
intros ? H5; rewrite H5 in H1.
intros ? H6; rewrite H6 in H1.
elimtype False; auto.
intros H4; rewrite H4 in H1.
intros ? H5; rewrite H5 in H1.
elimtype False; auto.
intros H4; rewrite H4 in H1.
solve[elimtype False; auto].

destruct name; try solve[elimtype False; simpl in H1; auto].
destruct name; try solve[elimtype False; simpl in H1; auto].
destruct name; try solve[elimtype False; simpl in H1; auto].
destruct sg; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct sig_res; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].

(*SYS_OPEN case*)
hnf in H1.
case_eq (val2oint v); try solve[elimtype False; simpl in H1; auto].
case_eq (val2omode v0); try solve[elimtype False; simpl in H1; auto].
intros md H4 fname H5.
rewrite H4, H5 in H1.
destruct H1 as [H1 [H6 H7]].
apply alloc_fd_success in H6.
destruct H6 as [unused_fd H6].
case_eq (file_exists (proj_zint fs_extension s) fname).
(*file exists*)
intros H8.
generalize H8 as H8'; intro.
generalize H8 as H8''; intro.
unfold file_exists in H8'.
case_eq (get_fstore (proj_zint fs_extension s) fname).
intros f H9.
specialize (H2 (Some (Vint unused_fd)) m 
 (fs_open_existing (proj_zint fs_extension s) unused_fd fname f md, z)).
spec H2; simpl; auto.
unfold is_readable.
exists md; exists 0; exists f; split.
unfold get_fdtable, fs_open_existing; simpl.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
unfold get_fcache, fs_open_existing; simpl.
case_eq (Int.eq unused_fd unused_fd); auto.
rewrite Int.eq_true; congruence.
destruct H2 as [c' [H2 H10]].
exists (mkxT z c' (fs_open_existing (proj_zint fs_extension s) unused_fd fname f md)).
exists m.
split.
destruct H7 as [H7 H11].
eapply os_open; eauto.
unfold fs_open.
unfold proj_zint in H9.
unfold SafetyInvariant.proj_zint in H9.
simpl in H9.
unfold fs_extension.proj_zint in H9.
rewrite H9; auto.
if_tac; auto.
(*core stayed at_external: impossible*)
intros.
exists c'.
split; auto.
rename H3 into H11.
assert (H3:True) by auto.
unfold proj_core in H11.
if_tac in H11; try congruence.
inv H11.
auto.
intros.
elimtype False.
rename H3 into H14.
assert (H3:True) by auto.
unfold proj_core in H14.
if_tac in H14; try congruence.
apply after_at_external_excl in H2.
unfold cores in *.
rewrite H2 in H12.
congruence.
(*degenerate case*)
intros H9.
unfold file_exists in H8''.
rewrite H9 in H8''.
simpl in H8''; congruence.
(*file doesn't yet exist*)
intros H8.
generalize H8 as H8'; intro.
generalize H8 as H8''; intro.
case_eq (get_fstore (proj_zint fs_extension s) fname).
intros f H9.
elimtype False.
unfold file_exists in H8.
rewrite H9 in H8.
simpl in H8; congruence.
intros H9.
specialize (H2 (Some (Vint unused_fd)) m 
 (fs_open_new (proj_zint fs_extension s) unused_fd fname md, z)).
spec H2; simpl; auto.
unfold is_readable.
exists md; exists 0.
unfold get_fdtable, get_fcache, fs_open_new; simpl.
case_eq (Int.eq unused_fd unused_fd).
intros; exists new_file; split; auto.
rewrite Int.eq_true; congruence.
destruct H2 as [c' [H2 H10]].
exists (mkxT z c' (fs_open_new (proj_zint fs_extension s) unused_fd fname md)).
exists m.
split.
destruct H7 as [H7 H11].
eapply os_open; eauto.
unfold fs_open.
unfold proj_zint in H9.
unfold SafetyInvariant.proj_zint in H9.
simpl in H9.
unfold fs_extension.proj_zint in H9.
rewrite H9; auto.
case_eq (fwritable md); auto.
intros H12.
rewrite H12 in H7.
elimtype False.
spec H7.
unfold file_exists; intros H13.
unfold SafetyInvariant.proj_zint in H13.
simpl in H13.
unfold fs_extension.proj_zint in H13.
rewrite H9 in H13.
simpl in H13; congruence.
congruence.
(*core stayed at_external: impossible*)
intros.
exists c'.
split; auto.
rename H3 into H11.
assert (H3:True) by auto.
unfold proj_core in H11.
if_tac in H11; try congruence.
inv H11.
auto.
intros.
elimtype False.
rename H3 into H14.
assert (H3:True) by auto.
unfold proj_core in H14.
if_tac in H14; try congruence.
apply after_at_external_excl in H2.
unfold cores in H13.
inversion H13.
inv H14.
unfold cores in *.
rewrite H2 in H12.
congruence.
(*degenerate cases*)
intros H9 i H4.
rewrite H4, H9 in H1.
elimtype False; auto.
intros H4.
rewrite H4 in H1.
solve[elimtype False; auto].

destruct sg; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct sig_args; try solve[elimtype False; simpl in H1; auto].
destruct sig_res; try solve[elimtype False; simpl in H1; auto].
destruct t; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
simpl in H1.
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
destruct args; try solve[elimtype False; simpl in H1; auto].
case_eq (val2oint v); try solve[elimtype False; simpl in H1; auto].
case_eq (val2oadr v0); try solve[elimtype False; simpl in H1; auto].
case_eq (val2oint v1); try solve[elimtype False; simpl in H1; auto].
intros.
rewrite H3, H4, H5 in H1.

(*SYS_WRITE case*)
destruct H1 as [Heq [H1 [H6 H7]]].
unfold proj_zint in H6.
destruct H6 as [md [cur [f' [H6 [H8 H80]]]]].
destruct a as [b ofs].
simpl in H7.
apply Mem.range_perm_loadbytes in H7.
destruct H7 as [bytes H7].
assert (H9: exists nbytes_written, exists fsys', 
  fs_write (get_fs s) i0 bytes = Some (nbytes_written, fsys')).
  unfold fs_write, get_file, get_fptr, get_fmode.
  unfold fs_extension.proj_zint in H6, H80.
  rewrite H6, H8, H80.
  case_eq (write_file f' cur bytes).
  intros fsys' nbytes_written H9.
  exists nbytes_written. 
  eexists; eauto.
destruct H9 as [nbytes_written [fsys' H90]].
specialize (H2 (Some (Vint (Int.repr (Z_of_nat nbytes_written)))) m (fsys', z)).
spec H2; simpl; auto.
destruct H2 as [c' [H9 H10]].
exists (mkxT z c' fsys'); exists m.
split.
eapply os_write 
 with (nbytes := Int.repr (Z_of_nat nbytes_written)); eauto.
rewrite H3.
f_equal.
apply Mem.loadbytes_length in H7.
apply fs_write_length in H90.
rewrite H90.
rewrite H7.
rewrite nat_of_Z_eq.
generalize (Int.repr_unsigned i).
unfold Int.unsigned; auto.
destruct (Int.intrange i). destruct (Int.unsigned_range_2 i); omega.
unfold fst, snd.
generalize H7 as H7'.
apply Mem.loadbytes_length in H7.
apply fs_write_length in H90.
rewrite H90.
rewrite H7.
rewrite nat_of_Z_eq.
rewrite Int.repr_unsigned; auto.
destruct (Int.unsigned_range_2 i); omega.
(*core stayed at_external: impossible*)
intros.
exists c'.
split; auto.
rename H2 into H11.
assert (H2:True) by auto.
unfold proj_core in H11.
if_tac in H11; try congruence.
inv H11.
auto.
intros.
elimtype False.
rename H2 into H13.
assert (H2:True) by auto.
unfold proj_core in H13.
if_tac in H13; try congruence.
apply after_at_external_excl in H9.
unfold cores in H2.
unfold cores in *.
rewrite H9 in H12.
congruence.
(*degenerate cases*)
intros H4; rewrite H4 in H1.
intros ? H5; rewrite H5 in H1.
intros ? H6; rewrite H6 in H1.
elimtype False; auto.
intros H4; rewrite H4 in H1.
intros ? H5; rewrite H5 in H1.
elimtype False; auto.
intros H4; rewrite H4 in H1.
elimtype False; auto.
intros H4.
unfold cores, active in H1. 
unfold cores, Extension.active in H0.
rewrite H4 in H0, H1.
(*safely halted*)
destruct (safely_halted csem (get_core s)); try congruence.
solve[right; exists v; auto].

(*5: safely halted threads remain halted*)
intros until rv; intros H2 H3 H4.
assert (H1:True) by auto.
unfold cores in H1.
simpl in H2.
unfold proj_core in H2.
if_tac in H2; try congruence.
inv H2.
unfold cores in *.
inv H4.
apply corestep_not_halted in H.
simpl in H3.
rewrite H in H3; congruence.
destruct (at_external_halted_excl csem (get_core s)).
rewrite H4 in H; congruence.
rewrite H4 in H3; congruence.
destruct (at_external_halted_excl csem (get_core s)).
rewrite H4 in H; congruence.
rewrite H4 in H3; congruence.
destruct (at_external_halted_excl csem (get_core s)).
rewrite H4 in H; congruence.
solve[rewrite H4 in H3; congruence].

(*6: safety of other cores preserved over handled steps*)
intros until c; hnf.
intros [H1 H2].
intros H3 j c2 H6.
split.
intros H8.
simpl in H8.
unfold proj_core in H8.
if_tac in H8; try congruence.
rewrite H in H6.
simpl in H6.
unfold active in H6.
solve[elimtype False; auto].
intros n z z' H8 H9.
simpl in H8.
unfold proj_core in H8.
if_tac in H8; try congruence.
rewrite H in H6.
simpl in H6.
unfold active in H6.
solve[elimtype False; auto].

(*7: extended machine doesn't introduce new external calls*)
intros until args; intros H1.
inv H1.
case_eq (at_external csem (get_core s)).
intros [[ef' sig'] args'] H1.
exists (get_core s).
split; auto.
unfold os_at_external in H0|-*.
rewrite H1 in H0|-*.
unfold cores in *.
destruct ef'; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct sg; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_res; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct sig_args; try congruence.
destruct sig_args; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct name; try congruence.
destruct sg; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct sig_res; try congruence.
destruct t; try congruence.
destruct sg; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct t; try congruence.
destruct sig_args; try congruence.
destruct sig_res; try congruence.
destruct t; try congruence.
intros H1.
unfold os_at_external in H0.
solve[rewrite H1 in H0; congruence].

(*8: *)
intros.
simpl.
unfold os_after_external.
unfold cores in *.
inversion H.
subst.
simpl in *.
unfold proj_core in *.
if_tac in H; try congruence.
inv H.
rewrite H4.
solve[eexists; eauto].

(*9: *)
intros.
split; auto.
intros H9.
assert (H8:True) by auto.
simpl in H9.
unfold proj_core in H9.
if_tac in H9; auto.
rewrite H10 in H7.
rename H6 into H11.
simpl in H11.
unfold proj_core in H11.
if_tac in H11; try congruence.
simpl in H7.
congruence.
congruence.
rename H into H8.
simpl in H8.
unfold proj_core in H8.
if_tac in H8; try congruence.
subst.
intros ge' n H13 H14.
simpl in H13.
unfold proj_core in H13.
if_tac in H13; try congruence.
simpl in H7.
congruence.
Qed.

End FSExtension.
