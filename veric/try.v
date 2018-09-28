Require Import NPeano.
Require Import Coq.Program.Wf.
Require Import Omega.
Require Import Recdef.


(** *Even length*)
Inductive even : nat -> Prop :=
| EvenO : even 0
| EvenS : forall n, even n -> even (S (S n)). 

Function length_of_even (ls:list nat) : option nat :=
  match ls with
  | nil => Some 0
  | cons x1 (cons x2 ls') =>
    match length_of_even ls' with
    | Some n' => Some ( 2 + n')
    | _ => None
    end
  | cons x nil => None 
  end.

Lemma LOE_correct:
  forall ls n,
    length_of_even ls = Some n ->
    even (length ls).
Proof.
  intros.
  induction ls;
    try constructor; simpl.
  simpl in H.
  destruct ls; try solve[inversion H].
  simpl; constructor. 

  Restart.
  
  intros ls.
  functional induction (length_of_even ls).
  - constructor. 
  - simpl; constructor.
    eapply IHo; eassumption.
  - intros ? HH; inversion HH.
  - intros ? HH; inversion HH.
Qed.


(** * Perm_of_sh *)
Require Import VST.veric.juicy_mem.
Require Import compcert.common.Memory.

Print perm_of_sh.
Lemma perm_of_sh_readable:
  forall sh P,
    shares.readable_share_dec sh = left P ->
    Mem.perm_order'' (perm_of_sh sh) (Some Readable).
Proof.
  intros.
  unfold perm_of_sh.
  destruct (shares.writable_share_dec sh).
  Restart.
  
  Functional Scheme perm_of_sh_ind := Induction for perm_of_sh Sort Prop.

  intros.
  functional induction (perm_of_sh sh);
    try congruence; (* Discard the impossible cases *)
    try solve[constructor]. (* Discard the rest of the cases *)
Qed.



(** * Merge *)


Definition double_measure (lss: list nat * list nat):= (length (fst lss) + length (snd lss)).

Function merge (lss: list nat * list nat)
         {measure double_measure}:=
  match lss with
    | (ls1, ls2) =>
  match ls1 with
    nil => ls2
  | cons n ls1' =>
    match ls2 with
      nil => ls1
    | cons m ls2' =>
      if n <? m then
        cons n (merge (ls1', ls2))
      else
        cons m (merge (ls1, ls2'))
    end
  end
    end.
- intros; simpl.
  unfold double_measure; simpl.
  omega.
- intros; simpl.
  unfold double_measure; simpl.
  omega.
Defined.

Lemma merge_length: forall lss,
    length (merge lss) = length (fst lss) + length (snd lss).
Proof.
  intros.
  
  functional induction (merge lss);
    auto; (*Trivial cases*)
    simpl; f_equal.
  - apply IHl.
  - rewrite IHl; simpl; omega.
Qed.
  

(** *Mutual recursion*)

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Function elength (el : even_list) : nat :=
  match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
    | OCons _ el => S (elength el)
  end.

Function eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
    | OCons n el' => OCons n (eapp el' el)
  end.

Functional Scheme eapp_mut := Induction for eapp Sort Prop
with oapp_mut := Induction for oapp Sort Prop.

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
  intros.
  
  functional induction (eapp el1 el2) using eapp_mut
  with (P0:= (fun (ol: odd_list)( el : even_list)( ol': odd_list) =>
         olength ol' = plus (olength ol) (elength el))).
  - intros; reflexivity.
  - intros. simpl; f_equal; apply IHe.
  - intros. simpl; f_equal; apply IHe.
Qed.








































Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Test.

Variable A : Type.

Theorem counterexample P : (exists x : A, ~P x) -> ~(forall x, P x).
Proof.
by case=>x H1 H2; apply: H1 (H2 x).
Qed.

Print counterexample.

End Test.


Require Import List.
Fixpoint add_list l:=
  match l with
    | nil => 0
    | h::tl => h + (add_list tl)
  end.



Inductive subseq {A: Type}: list A -> list A -> Prop :=
  | nil_subseq : subseq nil nil
  | hd_subseq: forall a l1 l2, subseq l1 l2 -> subseq (a :: l1) (a :: l2)
  | tl_subseq: forall a l1 l2, subseq l1 l2 -> subseq l1 (a :: l2)
  .

Inductive subseq' {A: Type}: list A -> list A -> Prop :=
  | nilss : forall l, subseq' nil l
  | hdss: forall a l l1 l2, subseq' l l2 -> subseq' (a :: l) (l1 ++ a :: l2)
  .

Theorem ssss: forall A (l1 l2: list A), subseq l1 l2 <-> subseq' l1 l2.
split.
+ intros H; induction H; try constructor.
  replace (a::l2) with (nil ++ a::l2) by auto; constructor; auto.
  replace (cons a l2) with (app (cons a nil) l2) by auto. 
  inversion IHsubseq. constructor. rewrite app_assoc. constructor.
  auto.
+ intros. induction H.
  induction l; constructor; auto.
  induction l1.
  simpl; constructor; auto.
  simpl. 
  constructor; auto.
Qed.

Lemma subseq_trans: forall {A} (l1 l2 l3: list A), subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof. 
intros A l1 l2 l3 H H0. 
generalize dependent l3. induction H.
intros. 
+ inversion H0; constructor. exact H.
+ intros. 
  induction l3. inversion H0.
  constructor. apply IHl3.
  

apply ssss; apply ssss in H; apply ssss in H0.
generalize dependent l3.
induction H.
+ constructor.
+ 

induction l1; intros l3 H0; inversion H0.
  -  constructor; apply IHsubseq'; exact H4.
  - subst. apply IHl1. 
    inversion H4. destruct l1; inversion H2.
    replace (l4 ++ a0 :: l3 ++ a1 :: l6) with ((l4 ++ a0 :: l3) ++ a1 :: l6 ).
    constructor. exact H2.
    rewrite app_comm_cons.
    rewrite app_assoc. reflexivity.
Qed.


+ constructor.
+ inversion H. subst l2. inversion H0.
  - destruct l0; simpl in H5; inversion H5.
  - clear H6. destruct l0; inversion H5.
    * subst. simpl in *. inversion H2. subst; inversion H4.
       
      constructor.
    

constructor.
subst l3; auto.
  -  auto.
  


revert l3.
induction H; intros l3 H0.
+ admit.
+ inversion H0.
  - constructor.
    apply IHsubseq; auto.
  - constructor. apply 


Inductive foo: Type :=
   bar: foo -> foo.

Theorem blah: forall (x: foo), False.
  Proof. 
    
    

Lemma and_or: forall (a b: bool),
             a = b ->
             andb a b = orb a b.
Proof.
destruct a; intros b H.
+ destruct b.
  - reflexivity.
  - inversion H.
+ destruct b.
  - inversion H.
  - reflexivity.
Qed.

Lemma blah: forall x, x=O -> ~ exists y, x = S y .
intros x H H0; destruct x.
+ destruct H0; inversion H0.
+ inversion H.
Qed.

Lemma zero_no_succ: forall n, O<>S n.
unfold not; intros n H.

Definition Is_S (n:nat) := match n with (*This is a hint!!!*)
                            | O => False
                            | S p => True
                            end.
Lemma Zero_not_Succ: forall n:nat, 0 <> S n.
	unfold not; intros n H.
        assert (HH: Is_S O = False) by reflexivity.
        rewrite <- HH.
        rewrite H. simpl.

Inductive bin:=
   OO: bin
  | SS: bin -> bin
  | TT: bin -> bin.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = plus (bin_to_nat b) 1.

Lemma blah': forall x, x=0 -> 

unfold not in H.


Require Import ssreflect.

Require Import ssrbool.
Require Import ssrnat.
Require Import ssrfun.

Require Import eqtype.
Require Import seq.
Require Import fintype.
