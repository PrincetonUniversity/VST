Set Implicit Arguments.

Require Import Bvector.
Require Import List.
Require Import Arith.
Require Import hmacfcf.HMAC_spec. (*The abstract spec*)
Require Import hmac_pure_lemmas.
Require Import HMAC_common_defs.
Require Import HMAC_spec_list.

Lemma split_eq: forall m (v2 : Bvector m) n (v1 : Bvector n),
      splitVector n m (Vector.append v1 v2)  = (v1, v2).
Proof.
  intros m v2.
  eapply Vector.t_rec.
  reflexivity.
  intros. simpl. rewrite H. trivial.
Qed.

Section HMAC_AbstractEQ.
(*Definition b := hmacfcf.HMAC_spec.b c p.*)

(* *** TODO: need to prove that the list equivalents have this type *** *)
Variable h_v : Bvector c -> Bvector b -> Bvector c.
Variable iv_v : Bvector c.
Variable P : Blist -> Prop. (*example: P m := NPeano.divide 8 (length m)*)
Definition Message : Set := {m: Blist | P m}.
Definition Message2Blist(msg:Message):Blist := let (m,_) := msg in m.

Variable splitAndPad_v : Blist -> list (Bvector b).
Definition wrappedSAP (msg:Message): list (Bvector b) :=
  splitAndPad_v (Message2Blist msg).

Variable splitAndPad_inj: forall b1 b2, splitAndPad_v b1 = splitAndPad_v b2 ->
  P b1 -> P b2 -> b1=b2.

Definition wrappedSAP_1_1: forall msg1 msg2, wrappedSAP msg1=wrappedSAP msg2 -> msg1=msg2.
Proof. intros. unfold wrappedSAP in H. destruct msg1. destruct msg2.
unfold Message2Blist in H.
apply splitAndPad_inj in H; trivial.
apply Extensionality.exist_ext. trivial.
Qed.

Variable fpad_v : Bvector c -> Bvector p. 
Variable opad_v ipad_v : Bvector b.

(* TODO: prove fpad has right type *)
Hypothesis fpad_eq : forall (v : Bvector c) (l : Blist),
                  l = Vector.to_list v ->
                  fpad l = Vector.to_list (fpad_v v).

Lemma app_fpad_eq : forall (v : Bvector c) (l : Blist),
                      l = Vector.to_list v ->
                      HMAC_List.app_fpad fpad l =
                      Vector.to_list (app_fpad fpad_v v).
Proof.
  intros v l inputs_eq.
  subst.
  unfold HMAC_List.app_fpad. unfold app_fpad. 
  rewrite <- VectorToList_append. erewrite fpad_eq; reflexivity. 
Qed.     

(* iv *)
Hypothesis iv_eq : sha_iv = Vector.to_list iv_v.

(* h *)
Hypothesis h_eq : forall (block_v : Bvector b) (block_l : Blist)
               (HVL: block_l = Vector.to_list block_v)
               ivA ivB (IV: ivA = Vector.to_list ivB),
               sha_h ivA block_l = Vector.to_list (h_v ivB block_v).

(* h_star *) 
Lemma hash_words_eq : forall (v : list (Bvector b)) (l : list Blist)
                      (HVL: Forall2 (fun bv bl => bl = Vector.to_list bv) v l)
                      ivA ivB (IV: ivA = Vector.to_list ivB),
                      HMAC_List.hash_words sha_h ivA l =
                      Vector.to_list (hash_words p h_v ivB v).
Proof.
  intros v l.
  unfold HMAC_List.hash_words. unfold hash_words.
  unfold HMAC_List.h_star. unfold h_star.
  generalize dependent v.
  induction l as [ | bl bls].
  * simpl; intros. inversion HVL; clear HVL. subst v. simpl. assumption.
  * intros. inversion HVL; clear HVL. subst.
    rewrite fold_left_cons.
    specialize (IHbls _ H3); clear H3.
    rewrite fold_left_cons. apply IHbls. apply h_eq; trivial.
Qed.

(* TODO: Here, need lemma relating sha_splitandpad_blocks and sha_splitandpad_inc
such that the below is true *)

Hypothesis length_splitandpad_inner : forall (m : Blist),
   Forall2
     (fun (bv : Vector.t bool b) bl => bl = Vector.to_list bv)
     (splitAndPad_v m) (sha_splitandpad_blocks m).

Definition wrappedSAP_inner (msg: Message):
Forall2
  (fun (bv : Vector.t bool b) (bl : list bool) => bl = Vector.to_list bv)
  (wrappedSAP msg) (sha_splitandpad_blocks (Message2Blist msg)).
Proof. destruct msg as [m LM]. apply length_splitandpad_inner. Qed.

(* TODO: opad and ipad should be in HMAC_common_parameters (factor out of all spec) *)
(* also, op and opad_v, etc. are related -- make explicit *)

Theorem HMAC_abstract_list : forall (kv : Bvector b) (kl:Blist) (msg:Message) (op ip : Blist),
                    kl = Vector.to_list kv ->
                    op = Vector.to_list opad_v ->
                    ip = Vector.to_list ipad_v ->
                    HMAC_List.HMAC sha_h sha_iv sha_splitandpad_blocks fpad op ip kl (Message2Blist msg)
                    = Vector.to_list
                        (HMAC_spec.HMAC h_v iv_v wrappedSAP
                                            fpad_v opad_v ipad_v kv msg).
Proof.
  intros kv kl msg op ip keys_eq op_eq ip_eq.
  unfold HMAC_List.HMAC. unfold hmacfcf.HMAC_spec.HMAC.
  unfold HMAC_List.HMAC_2K. unfold hmacfcf.HMAC_spec.HMAC_2K.
  unfold HMAC_List.GHMAC_2K. unfold hmacfcf.HMAC_spec.GHMAC_2K.
  subst.
  rewrite split_eq.
  (* rewrite -> split_append_id. *) (* could use this instead of firstn and splitn *)
  apply hash_words_eq. 
  constructor.
    rewrite firstn_exact.
    apply xor_eq. 
    apply BLxor_length.
    (*unfold HMAC_List.b. unfold b in *.*)
    apply VectorToList_length.
    apply VectorToList_length.
  rewrite skipn_exact. 
       2: apply BLxor_length.
          2: apply VectorToList_length.
          2: apply VectorToList_length.
       2: apply iv_eq.
  constructor. 2: constructor.
  apply app_fpad_eq.
  apply hash_words_eq.
    constructor.
      apply xor_eq. 
      apply wrappedSAP_inner. (*apply length_splitandpad_inner.*)
    apply iv_eq.
Qed.

End HMAC_AbstractEQ.


