Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Ctypes. (*for type and access_mode*)
Require Import mem_lemmas. (*needed for definition of valid_block_dec etc*)


Definition memcpy_Effect sz vargs m:=
       match vargs with 
          Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil =>
          fun b z => eq_block b b1 && zle (Int.unsigned ofs1) z &&
                     zlt z (Int.unsigned ofs1 + sz) && valid_block_dec m b
       | _ => fun b z => false
       end.
      
Lemma memcpy_Effect_unchOn: forall m bsrc osrc sz bytes bdst odst m'
        (LD: Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes)
        (ST: Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m')
        (SZ: sz >= 0),
    Mem.unchanged_on
      (fun b z=> memcpy_Effect sz (Vptr bdst odst :: Vptr bsrc osrc :: nil) 
                 m b z = false) m m'.
Proof. intros.
  split; intros.
    unfold Mem.perm. rewrite (Mem.storebytes_access _ _ _ _ _ ST). intuition.
  unfold memcpy_Effect in H.
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ ST).
    destruct (valid_block_dec m b); simpl in *. rewrite andb_true_r in H; clear v.
    destruct (eq_block b bdst); subst; simpl in *.
      rewrite PMap.gss. apply Mem.setN_other.
      intros. intros N; subst. 
        rewrite (Mem.loadbytes_length _ _ _ _ _ LD), nat_of_Z_eq in H1; trivial.
          destruct (zle (Int.unsigned odst) ofs); simpl in *.
            destruct (zlt ofs (Int.unsigned odst + sz)). inv H.
            omega. omega.
    clear H. rewrite PMap.gso; trivial.
  elim n. eapply Mem.perm_valid_block; eassumption.
Qed.

Lemma external_call_memcpy_unchOn:
    forall {F V:Type} (ge : Genv.t F V) m ty b1 ofs1 b2 ofs2 m' a tr vres,
    external_call (EF_memcpy (sizeof ty) a) ge 
                  (Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil) m tr vres m' -> 
    Mem.unchanged_on
      (fun b z=> memcpy_Effect (sizeof ty) (Vptr b1 ofs1 :: Vptr b2 ofs2 :: nil) 
                 m b z = false) m m'.
Proof. intros. inv H.
  eapply memcpy_Effect_unchOn; try eassumption. omega.
Qed.
 
Lemma memcpy_Effect_validblock:
    forall {F V:Type} (ge : Genv.t F V) m sz vargs b z,
    memcpy_Effect sz vargs m b z = true ->
    Mem.valid_block m b.
Proof. intros.
 unfold memcpy_Effect in H.  
  destruct vargs; try discriminate.
  destruct v; try discriminate.
  destruct vargs; try discriminate.
  destruct v; try discriminate.
  destruct vargs; try discriminate.
  destruct (valid_block_dec m b); simpl in *. trivial. 
  rewrite andb_false_r in H. inv H. 
Qed.
                                                          
Definition BuiltinEffect  {F V: Type} (ge: Genv.t F V) (ef: external_function)
          (vargs:list val) (m:mem): block -> Z -> bool :=
  match ef with
    EF_memcpy sz a => memcpy_Effect sz vargs m
  | _ => fun b z => false
  end.

Lemma BuiltinEffect_unchOn:
    forall {F V:Type} ef (g : Genv.t F V) vargs m t vres m',
    external_call ef g vargs m t vres m' -> 
    Mem.unchanged_on
      (fun b z=> BuiltinEffect g ef vargs m b z = false) m m'.
Proof. intros.
  destruct ef.
    admit. (*case EF_external*)
    admit. (*case EF_builtin*)
    admit. (*case EF_vload*)
    admit. (*case EF_vstore*)
    admit. (*case EF_vload_global*)
    admit. (*case EF_vstore_global*)
    admit. (*case EF_malloc*)
    admit. (*case EF_free*)
    simpl. (*case EE_memcpy*)
           inv H. clear - H1 H6 H7.
           eapply memcpy_Effect_unchOn; try eassumption. omega.
    admit. (*case EF_annot1*)
    admit. (*case EF_annot2*)
    admit. (*case EF_inline_asm*)
Qed.

Lemma BuiltinEffect_valid_block:
    forall {F V:Type} ef (g : Genv.t F V) vargs m b z,
     BuiltinEffect g ef vargs m b z = true -> Mem.valid_block m b. 
Proof. intros. unfold BuiltinEffect in H. 
  destruct ef; try discriminate.
    eapply memcpy_Effect_validblock; eassumption.
Qed.