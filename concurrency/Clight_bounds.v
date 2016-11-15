Require Import compcert.lib.Axioms.
Require Import compcert.lib.Maps.

Require Import concurrency.sepcomp. 
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.


Require Import Coq.ZArith.ZArith.

Require Import concurrency.permissions.
Require Import compcert.common.Memory. (*for Mem.perm_order'' *)
Require Import concurrency.bounded_maps.

Require Import sepcomp.semantics_lemmas.
Require Import Coqlib.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.

Lemma CLight_Deterministic: forall ge c m c1 m1 c2 m2,
    veric.Clight_new.cl_step ge c m c2 m2 ->
    veric.Clight_new.cl_step ge c m c1 m1 ->
    c1 = c2 /\ m1 = m2.
Proof. intros. 
specialize (cl_corestep_fun _ _ _ _ _ _ _ H H0); intros X; inversion X; subst. split; trivial.
Qed.

Definition bnd_from_init m := bounded_maps.bounded_map (snd (getMaxPerm m)) /\ (Mem.mem_access m).1 = fun z k => None.
                              
Lemma preserve_bnd: memstep_preserve (fun m m' => bnd_from_init m -> bnd_from_init m'). 
Proof. econstructor; intros; eauto.
induction H; intros.
{ destruct H0; split.
    unfold getMaxPerm in *. erewrite Mem.storebytes_access; eauto.
    erewrite Mem.storebytes_access; eauto. }
{ Transparent Mem.alloc. unfold Mem.alloc in H. Opaque Mem.alloc.
  inversion H; clear H; subst. 
  destruct H0; split; simpl in *; trivial.
  red; intros. red in H.
    rewrite (PTree.gmap1 (fun f : Z -> perm_kind -> option permission => f^~ Max)
               p (PTree.set (Mem.nextblock m)
          (fun (ofs : Z) (_ : perm_kind) => if zle lo ofs && zlt ofs hi then Some Freeable else None)
          (Mem.mem_access m).2)) in H1.
    unfold option_map in H1.
    rewrite PTree.gsspec in H1.
    destruct (peq p (Mem.nextblock m)); subst. 
    { inversion H1; clear H1; subst. clear H0 H. red.
      exists hi, lo; split; intros.
      { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; omega. }
      { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; omega. } }
    { apply (H p); clear H0. rewrite PTree.gmap1. apply H1. } }
{ generalize dependent m'. generalize dependent m. induction l; intros.
  { inversion H; clear H; subst. trivial. }
  { destruct a as [[b lo] hi]. simpl in H. remember (Mem.free m b lo hi) as q; symmetry in Heqq. 
    destruct q; try discriminate. apply (IHl m0); trivial. clear H IHl m'.
    rename m0 into m'.
    Transparent Mem.free. unfold Mem.free in Heqq. Opaque Mem.free.
    destruct (Mem.range_perm_dec m b lo hi Cur Freeable); try discriminate. 
    inversion Heqq; clear Heqq; subst.
    destruct H0 as [? INI]; split. 
    intros p f F.  simpl.
      destruct (peq p b); subst.
      { simpl in F. rewrite PTree.gmap1 in F. unfold option_map in F. rewrite PTree.gss in F. inversion F; clear F; subst.
        specialize (H b).
        remember (((getMaxPerm m).2) ! b) as g. destruct g; symmetry in Heqg.
        { assert (Some o = Some o) by trivial. specialize (H _ H0); clear H0. rename o into g.
          destruct H as [HI [LO [HHi HLo]]]. unfold getMaxPerm in Heqg. unfold PMap.get. simpl in *.
          rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg. rewrite INI.
          destruct (((Mem.mem_access m).2) ! b); try discriminate. inversion Heqg; clear Heqg; subst.
          exists  HI, LO; split; intros.
          { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; eauto. } 
          { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; eauto. } }
        { clear H. unfold getMaxPerm in Heqg.
               destruct (zlt lo hi).
               { assert (A: lo <= lo < hi) by omega. specialize (r _ A).
                 apply Mem.perm_max in r. unfold Mem.perm, PMap.get in r. 
                 rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg.
                 remember (((Mem.mem_access m).2) ! b) as q. destruct q; simpl in *. discriminate.
                 rewrite INI in r. inversion r. }
        { simpl in Heqg. rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg. unfold PMap.get.
          remember (((Mem.mem_access m).2) ! b) as w. destruct w; try discriminate. clear Heqg.
          rewrite INI.
          exists lo, lo; split; intros.
          { destruct (zle lo p); destruct (zlt p hi); simpl; trivial. }
          { destruct (zle lo p); destruct (zlt p hi); simpl; trivial. } } } }
      { apply (H p). unfold getMaxPerm in *; simpl in *.
        rewrite PTree.gmap1 in F. rewrite PTree.gmap1. unfold option_map in *.
        rewrite PTree.gso in F; trivial. }
    simpl; trivial. } }
eauto.
Qed.

Lemma CLight_step_mem_bound ge c m c' m':
    veric.Clight_new.cl_step ge c m c' m' -> bnd_from_init m -> bnd_from_init m'.
Proof.
 intros. 
 apply (memsem_preserves CLN_memsem _ preserve_bnd _ _ _ _ _ H H0).
Qed. 