Require Import Coqlib.

Require Import sepcomp.Coqlib2.

Require Import Coq.Wellfounded.Inclusion.
Require Import Coq.Wellfounded.Inverse_Image.

Section lex_ord.
 Variables types: nat -> Type.
 Variable max: nat.
 Variable ords: forall n: nat, types n -> types n -> Prop.

 Definition gen_lex_ord: (forall n, types n) -> (forall n, types n) -> Prop :=
   fun data1 data2 => 
   exists i: nat, 
     (i < max)%nat /\
     @ords i (data1 i) (data2 i) /\
     (forall j, (j < i)%nat -> data1 j = data2 j).

 Fixpoint data_ty' (n max: nat): Type :=
   match n with 
   | O => unit
   | S n' => (types (max - S n') * data_ty' n' max)%type
   end.

 Fixpoint data_prod' (n max: nat) (data: forall n: nat, types n): data_ty' n max  :=
   match n as m in nat return data_ty' m max with 
   | O => tt
   | S n' => (data (max - S n')%nat, data_prod' n' max data)
   end.

 Fixpoint prod_ord' (n max: nat): data_ty' n max -> data_ty' n max -> Prop :=
   match n as m in nat return data_ty' m max -> data_ty' m max -> Prop with
   | O => fun d1 d2 => False
   | S n' => fun d1 d2 => lex_ord (@ords (max - S n')) (prod_ord' n' max) d1 d2
   end.

 Lemma wf_eta {A: Type}{f: A -> A -> Prop}: 
   well_founded f -> well_founded (fun a1 a2 => f a1 a2).
 Proof.
 intros H1; solve[assert ((fun a1 a2 => f a1 a2) = f) as -> 
  by (do 2 extensionality; auto); auto].
 Qed.

 Lemma wf_eta' {A: Type}{f: A -> A -> Prop}: 
   well_founded (fun a1 a2 => f a1 a2) -> well_founded f.
 Proof.
 intros H1; solve[assert ((fun a1 a2 => f a1 a2) = f) as -> 
  by (do 2 extensionality; auto); auto].
 Qed.

 Lemma wf_funct {A B: Type}{R: B -> B -> Prop}(f: A -> B): 
   well_founded R -> well_founded (fun a1 a2 => R (f a1) (f a2)).
 Proof. 
 intros H1.
 set (F := fun a b => f a = b).
 apply wf_incl with (R2 := (fun x y: A => 
   exists2 b : B, F x b & forall c : B, F y c -> R b c)).
 intros a1 a2 HR.
 exists (f a1); unfold F; auto.
 intros b H2.
 solve[subst b; auto].
 solve[apply wf_inverse_rel; auto].
 Qed.

 Lemma wf_prod_ord n (wf_ords: forall i: nat, well_founded (@ords i)): 
   well_founded (prod_ord' n max).
 Proof.
 unfold prod_ord'.
 revert wf_ords.
 revert dependent ords.
 clear ords.
 induction n; intros.
 solve[constructor; intros; elimtype False; auto].
 apply wf_eta.
 apply wf_lex_ord; auto.
 specialize (IHn ords).
 solve[spec IHn; auto].
 Qed.

 Definition data_upd i (new_i: types i) (data: forall i:nat, types i): 
  forall i:nat, types i := fun j: nat => 
     match eq_nat_dec i j as pf in sumbool _ _ return types j with
     | left pf => match pf with
                  | eq_refl => new_i 
                  end
     | right pf => data j
     end.
 Implicit Arguments data_upd [].

 Lemma data_upd_same i new_i data: (data_upd i new_i data) i = new_i.
 Proof.
 unfold data_upd.
 destruct (eq_nat_dec i i).
 rewrite (UIP_refl _ _ e); auto.
 elimtype False; auto.
 Qed.

 Lemma data_upd_other i j new_i data: i<>j -> (data_upd i new_i data) j = data j.
 Proof.
 unfold data_upd.
 destruct (eq_nat_dec i j).
 intros; elimtype False; auto.
 auto.
 Qed.

 Local Open Scope nat_scope.

 Lemma prod_ord_upd': forall i data1 data2 num_cores, 
   @ords i (data2 i) (data1 i) -> 
   (max - num_cores <= i < max)%nat -> (num_cores <= max)%nat -> 
   (forall j, j < i -> data1 j=data2 j) -> 
   prod_ord' num_cores max 
    (data_prod' num_cores max data2) (data_prod' num_cores max data1).
 Proof.
 intros until num_cores.
 intros H1 H2 H3 H4.
 induction num_cores as [|n].
 solve[simpl; intros; elimtype False; omega].
 simpl; intros.
 destruct (eq_nat_dec i (max - S n)).
 solve[subst; apply lex_ord_left; auto]. 
 assert (max - S n < i) by (destruct H2; omega).
 rewrite H4; auto.
 apply lex_ord_right.
 assert (n <> 0) by omega.
 apply IHn; try omega.
 Qed.

 Lemma prod_ord_upd: forall i new_i data,
   @ords i new_i (data i) -> (O <= i < max) -> 
   prod_ord' max max (data_prod' max max (data_upd i new_i data)) 
     (data_prod' max max data).
 Proof.
 intros.
 apply prod_ord_upd' with (i := i); try solve[auto|omega].
 rewrite data_upd_same; auto.
 intros j Hlt.
 rewrite data_upd_other; try solve[auto|omega].
 Qed.

End lex_ord.
