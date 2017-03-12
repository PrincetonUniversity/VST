Set Implicit Arguments.

Require Import Bvector.
Require Import List.
Require Import Arith.
Require Import hmacfcf.HMAC_spec. (*The abstract spec*)
Require Import sha.hmac_pure_lemmas.
Require Import sha.ByteBitRelations.
Require Import sha.HMAC_common_defs.
Require Import sha.HMAC_spec_list.

Lemma split_eq: forall m (v2 : Bvector m) n (v1 : Bvector n),
      splitVector n m (Vector.append v1 v2)  = (v1, v2).
Proof.
  intros m v2.
  eapply Vector.t_rec.
  reflexivity.
  intros. simpl. rewrite H. trivial.
Qed.

Module HMAC_Abstract.
Section HMAC_AbstractEQ.
  Variable c:nat.
  Variable p:nat.
  Definition b := (c+p)%nat.
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
(*End HMAC_AbstractEQ.

Section HMAC_Abstract_List.
  Variable c:nat.
  Variable p:nat.
  Variable h_v : Bvector c -> Bvector (b c p) -> Bvector c.
  Variable iv_v : Bvector c.
  Variable P : Blist -> Prop. (*example: P m := NPeano.divide 8 (length m)*)
  Variable splitAndPad_v : Blist -> list (Bvector (b c p)).

  Variable splitAndPad_inj: forall b1 b2, splitAndPad_v b1 = splitAndPad_v b2 ->
    P b1 -> P b2 -> b1=b2.
Variable fpad_v : Bvector c -> Bvector p.
Variable opad_v ipad_v : Bvector (b c p).
*)
(* h *)
Variable h: Blist -> Blist -> Blist.
Hypothesis h_eq : forall block_v block_l
               (HVL: block_l = Vector.to_list block_v)
               ivA ivB (IV: ivA = Vector.to_list ivB),
               h ivA block_l = Vector.to_list (h_v ivB block_v).

Variable iv: Blist.
Hypothesis iv_eq: iv=Vector.to_list iv_v.

(* h_star *)
Lemma hash_words_eq: forall l v
                   (HVL: Forall2 (fun bv bl => bl = Vector.to_list bv) v l)
                   ivA ivB (IV: ivA = Vector.to_list ivB),
      HMAC_List.hash_words h ivA l
      = Vector.to_list (hash_words p h_v ivB v).
Proof.
  unfold HMAC_List.hash_words. unfold hash_words.
  unfold HMAC_List.h_star. unfold h_star.
  induction l as [ | bl bls].
  * simpl; intros. inversion HVL; clear HVL. subst v. simpl. assumption.
  * intros. inversion HVL; clear HVL. subst.
    rewrite fold_left_cons.
    specialize (IHbls _ H3); clear H3.
    rewrite fold_left_cons. apply IHbls. apply h_eq; trivial.
Qed.

Variable fpad : Blist -> Blist.

Hypothesis fpad_eq: forall v l, l = Vector.to_list v ->
                    fpad l = Vector.to_list (fpad_v v).

Lemma app_fpad_eq v l (L:l = Vector.to_list v):
      HMAC_List.app_fpad fpad l = Vector.to_list (app_fpad fpad_v v).
Proof.
  subst.
  unfold HMAC_List.app_fpad. unfold app_fpad.
  rewrite <- VectorToList_append. erewrite fpad_eq; reflexivity.
Qed.

Variable splitandpad_blocks: Blist -> list Blist.
Hypothesis length_splitandpad_inner : forall m,
   Forall2
     (fun bv bl => bl = Vector.to_list bv)
     (splitAndPad_v m) (splitandpad_blocks m).

Definition wrappedSAP_inner msg:
Forall2
  (fun bv bl => bl = Vector.to_list bv)
  (wrappedSAP msg) (splitandpad_blocks (Message2Blist msg)).
Proof. destruct msg as [m LM]. apply length_splitandpad_inner. Qed.

Theorem HMAC_abstract_list kv msg:
        HMAC_List.HMAC c p h iv splitandpad_blocks fpad
          (Vector.to_list opad_v) (Vector.to_list ipad_v) (Vector.to_list kv)
          (Message2Blist msg) =
        Vector.to_list (HMAC h_v iv_v wrappedSAP fpad_v opad_v ipad_v kv msg).
Proof.
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
       2: reflexivity.
  constructor. 2: constructor.
  apply app_fpad_eq.
  apply hash_words_eq.
    constructor.
      apply xor_eq.
      apply wrappedSAP_inner. (*apply length_splitandpad_inner.*)
    reflexivity. (*apply iv_eq.*)
Qed.

End HMAC_AbstractEQ.
End HMAC_Abstract.
(*
Require Import ShaInstantiation.
Require Import HMAC256_spec_list.
Check HMAC.
Theorem HMAC_abstract_list_explicit h_v iv_v kv Message msg opad ipad:
        HMAC_List.HMAC c p sha_h sha_iv sha_splitandpad_blocks fpad
          (Vector.to_list opad) (Vector.to_list ipad) (Vector.to_list kv)
          (Message2Blist msg) =
        Vector.to_list (@HMAC c p h_v iv_v Message (wrappedSAP c p sha_splitandpad) opad ipad kv msg).
Proof.


*)