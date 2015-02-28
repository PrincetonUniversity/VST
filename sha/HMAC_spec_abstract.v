(* This spec was written by Adam Petcher.
Subsequent modifications and proofs are by Katherine Ye and Lennart Beringer. *)

Set Implicit Arguments.


Require Import Bvector.
Require Import List.
Require Import Arith.
Require Import hmac_pure_lemmas.
Require Import HMAC_common_defs.
Require Import HMAC_spec_list.

Require Import HMAC_spec. (*Adam's abstract spec*)

Lemma fold_left_cons {A B} (f: A -> B -> A) l b x: 
      fold_left f (x :: l) b = fold_left f l (f b x).
Proof. reflexivity. Qed.

Definition Vector_0_is_nil (T : Type) (v : Vector.t T 0) : v = Vector.nil T := 
  match v with Vector.nil => eq_refl end.

Lemma VectorToList_cons A n: forall (a:A) l,
      Vector.to_list (Vector.cons A a n l) =
      cons a (Vector.to_list l).
Proof. intros. reflexivity. Qed. 

Lemma VectorToList_length {A}: forall n (v: Vector.t A n), length (Vector.to_list v) = n.
Proof.
  apply Vector.t_rec. reflexivity.
  intros. rewrite VectorToList_cons. simpl. rewrite H. trivial.
Qed.

Lemma VectorToList_combine A n: forall (a:A) b v1 v2,
     combine (Vector.to_list (Vector.cons A a n v1))
             (Vector.to_list (Vector.cons A b n v2))
   = (a,b) :: combine (Vector.to_list v1) (Vector.to_list v2).
Proof. intros. simpl. f_equal. Qed.
   
(*Module HMAC_Abstract.

(*Definition Blist := list bool. already in HMAC_common_defs*)

Fixpoint splitVector (A : Set) (n m : nat) :
  Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
  match n with
    | 0 => 
      fun (v : Vector.t A (O + m)) => (@Vector.nil A, v)
    | S n' => 
      fun (v : Vector.t A (S n' + m)) => 
        let (v1, v2) := splitVector _ _ (Vector.tl v) in
          (Vector.cons _ (Vector.hd v) _ v1, v2)
  end.

Section HMAC.

  (* c is the output size, b is the block size (larger than the output size),
     and p is the difference between them *)
  Variable c p : nat.
  Definition b := c + p.
  
  (* The compression function *)
  Variable h : Bvector c -> Bvector b -> Bvector c.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Bvector c.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star (k : Bvector c) (m : list (Bvector b)) : Bvector c :=
    fold_left h m k.

  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words : list (Bvector b) -> Bvector c :=
    h_star iv.

  Variable splitAndPad : Blist -> list (Bvector b).
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.
  
  Variable fpad : Bvector c -> Bvector p. 
  Definition app_fpad (x : Bvector c) : Bvector b :=
    (Vector.append x (fpad x)).

  Definition h_star_pad (k : Bvector c) (x : list (Bvector b)) : Bvector b :=
    app_fpad (h_star k x).

  Definition GNMAC (k : Bvector (c + c)) (m : list (Bvector b)) : Bvector c :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Bvector (b + b)) (m : list (Bvector b)) : Bvector c :=
    let (k_Out, k_In) := splitVector b b k in
      let h_in := (hash_words (k_In :: m)) in 
        hash_words (k_Out :: (app_fpad h_in) :: nil).
  
  Definition HMAC_2K (k : Bvector (b + b)) (m : Blist) : Bvector c :=
    GHMAC_2K k (splitAndPad m).

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Bvector b.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Bvector b) : list (Bvector b) -> Bvector c :=
    GHMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

  Definition HMAC (k : Bvector b) : Blist -> Bvector c :=
    HMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

End HMAC.

End HMAC_Abstract.
*)


Theorem xor_eq' : forall (n : nat) (v1 v2 : Bvector n),
                   BLxor (Vector.to_list v1) (Vector.to_list v2) = 
                   Vector.to_list (BVxor n v1 v2).
Proof.
  eapply Vector.rect2.
  reflexivity.
  intros. simpl. rewrite (VectorToList_cons (xorb a b)).
   rewrite <- H. clear H. unfold BLxor. 
   rewrite VectorToList_combine. reflexivity.
Qed. 

Theorem xor_eq : forall (n : nat) (v1 v2 : Bvector n) (l1 l2 : Blist),
                   l1 = Vector.to_list v1 ->
                   l2 = Vector.to_list v2 ->
                   BLxor l1 l2 = Vector.to_list (BVxor n v1 v2).
Proof. intros; subst. apply xor_eq'. Qed.

Theorem app_eq' : forall (m:nat) (v2:Bvector m) (n : nat) (v1 : Bvector n),
                   (Vector.to_list v1) ++ (Vector.to_list v2) = 
                   Vector.to_list (Vector.append v1 v2).
Proof. intros m v2.
  eapply Vector.t_rec.
  reflexivity.
  intros. simpl. rewrite (VectorToList_cons h). f_equal. rewrite <- H. f_equal.
Qed.

Theorem app_eq : forall (n : nat) (v1 v2 : Bvector n),
                   (Vector.to_list v1) ++ (Vector.to_list v2) = 
                   Vector.to_list (Vector.append v1 v2).
Proof.
  intros. apply app_eq'.
Qed. 

Lemma split_eq: forall m (v2 : Bvector m) n (v1 : Bvector n),
      splitVector n m (Vector.append v1 v2)  = (v1, v2).
Proof.
  intros m v2.
  eapply Vector.t_rec.
  reflexivity.
  intros. simpl. rewrite H. trivial.
Qed.


Section HMAC_AbstractEQ.

Definition c := sha.HMAC_common_defs.c.
Definition p := sha.HMAC_common_defs.p.
Definition b := hmacfcf.HMAC_spec.b c p.

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
  rewrite <- app_eq. erewrite fpad_eq; reflexivity. 
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

Theorem HMAC_eq : forall (kv : Bvector b) (kl:Blist) (msg:Message) (op ip : Blist),
                    kl = Vector.to_list kv ->
                    op = Vector.to_list opad_v ->
                    ip = Vector.to_list ipad_v ->
                    HMAC_List.HMAC c p sha_h sha_iv sha_splitandpad_blocks fpad op ip kl (Message2Blist msg)
                    = Vector.to_list
                        (HMAC_spec.HMAC h_v iv_v wrappedSAP(*splitAndPad_v*)
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
    apply xor_eq. trivial. reflexivity. 
    apply BLxor_length.
    unfold HMAC_List.b. unfold b in *.
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
      apply xor_eq. trivial.
      reflexivity.
      apply wrappedSAP_inner. (*apply length_splitandpad_inner.*)
    apply iv_eq.
Qed.

End HMAC_AbstractEQ.

(* Framework for abstract:

v2l (V.append a b) = v2l a ++ v2l b
keep composing these functions, and the v2ls should "pop out"

Lifting a function on lists to a function on vectors? or the other way around?

mkVector : forall (l : list A), length l = n -> Vector.t A n.

Vector ?= {list, proof it's the right length}
no, it's defined inductively 

(creates a proof)
v2l_length : forall A n (v : Vector.t A n),
  length (v2l v) = n.

Definition h_sha (iv : Bvector 256) (block: Bvector 512) : Bvector 256 :=
   (mkVector (f_sha (v2l iv) (v2l block))
   (f_sha_lemma (v2l iv) (v2l block)
   (v2l_length 256 iv) (v2l_length 512 block)) <-- proofs

^ may have misplaced parens. unclear on what f_sha and f_sha_lemma are
 *)


