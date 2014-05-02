Require Import compcert.lib.Coqlib.
Require Import sepcomp.Coqlib2.

(* deliberately imported here *)
Require Import Coq.Wellfounded.Inclusion.
Require Import Coq.Wellfounded.Inverse_Image.

Require Import ssreflect ssrbool ssrnat ssrfun fintype.
Set Implicit Arguments.

Require Import linking.pos.
Require Import linking.cast.

(* This file defines a generalized lexicographic order on dependently     *)
(* typed products.  It exposes the following interface:                   *)
(*                                                                        *)
(* Assumptions:                                                           *)
(* Variable N : nat.                                                      *)
(* Variable N_pos : (0 < N)%coq_nat.                                      *)
(* Variable types : 'I_N -> Type.                                         *)
(* Variable ords  : forall i : 'I_N, types i -> types i -> Prop.          *)
(* Variable wf_ords : forall i : 'I_N, well_founded (@ords i).            *)
(*                                                                        *)
(* Exported:                                                              *)
(* t        : Type                                                        *)
(* mk       : (forall i : 'I_N, types i) -> t                             *)
(* get      : (i : 'I_N) (d : t), types i                                 *)
(* set      : {i : 'I_N} (d : t) (x : types i), t                         *)
(*                                                                        *)
(* ord      : t -> t -> Prop                                              *)
(* wf_ord   : well_founded ord                                            *)
(* ord_set  : (i : 'I_N) (d : t) (x : types i),                           *)
(*            ords i x (get i d) -> ord (set d x) d                       *)
(* gss      : (i : 'I_N) (x : types i) (d : t), get i (set i x d) = x     *)
(* gso      : (i j : 'I_N) (x : types i) (d : t),                         *)
(*            i <> j -> get j (set i x d) = get j d                       *)
(*                                                                        *)
(* In addition, it defines a WF order on the \Sigma-type                  *)
(*   \Sigma ix : 'I_N. T ix                                               *)


Lemma ord_dec (N : nat) (i j : 'I_N) : {i=j} + {~i=j}.
Proof. 
case: i; case: j=> m pf n pf'; move: pf pf'; case: (eq_nat_dec n m). 
by move=> -> pf pf'; left; f_equal; apply: proof_irr.
by move=> neq pf pf'; right; case.
Qed.

Lemma wf_eta {A: Type}{f: A -> A -> Prop} : 
  well_founded f -> well_founded (fun a1 a2 => f a1 a2).
Proof. 
by move=> H1; have ->: ((fun a1 a2 => f a1 a2) = f) by do 2 extensionality. 
Qed.

Lemma wf_eta' {A: Type}{f: A -> A -> Prop} : 
  well_founded (fun a1 a2 => f a1 a2) -> well_founded f.
Proof. 
by move=> H1; have <-: ((fun a1 a2 => f a1 a2) = f) by do 2 extensionality. 
Qed.

Lemma wf_funct {A B: Type}{R: B -> B -> Prop}(f: A -> B) : 
  well_founded R -> well_founded (fun a1 a2 => R (f a1) (f a2)).
Proof. 
move=> H1; set (F := fun a b => f a = b).
apply: (wf_incl _ _ 
 (fun x y: A => exists2 b : B, F x b & forall c : B, F y c -> R b c)).
by move=> a1 a2 HR; exists (f a1); rewrite/F=> //; move=> b <-.
by apply: wf_inverse_rel.
Qed.

Module Type LEX. 

Parameter t : forall (N : pos) (types : 'I_N -> Type), Type.

Arguments t {N} types.

Parameter ord : forall (N : pos)  
  (types : 'I_N -> Type) (ords : forall i : 'I_N, types i -> types i -> Prop),
  t types -> t types -> Prop.

Parameter wf_ord : forall (N : pos) 
  (types : 'I_N -> Type) (ords : forall i : 'I_N, types i -> types i -> Prop)
  (wf_ords : forall i : 'I_N, well_founded (ords i)),
  well_founded (ord ords).

Section lex.

Variable N : pos.
Variable types : 'I_N -> Type.
Variable ords  : forall i : 'I_N, types i -> types i -> Prop.
Variable wf_ords : forall i : 'I_N, well_founded (@ords i).

Notation t   := (t types).
Notation ord := (@ord N types ords).

Parameter mk  : (forall i : 'I_N, types i) -> t.
Parameter get : forall i : 'I_N, t -> types i.
Parameter set : forall (i : 'I_N) (x : types i), t -> t.
Parameter ord_upd : 
  forall (i : 'I_N) (x : types i) (d : t),
  ords x (get i d) -> ord (set x d) d.
Parameter gss : 
  forall (i : 'I_N) (x : types i) (d : t), get i (set x d) = x.
Parameter gso : 
  forall (i j : 'I_N) (x : types i) (d : t), i <> j -> 
    get j (set x d) = get j d.

End lex. End LEX.

Module Lex : LEX. Section lex.

Variable N : pos.
Variable types : 'I_N -> Type.
Variable ords  : forall i : 'I_N, types i -> types i -> Prop.
Variable wf_ords : forall i : 'I_N, well_founded (@ords i).

Lemma N_minus_lt (n : nat) : ((N - S n) < N)%N.
Proof. case: N=> m pf; rewrite -minusE; apply/ltP=> /=; omega. Qed.

Definition t : Type := forall i : 'I_N, types i.

Definition mk : t -> t := id.

Fixpoint ty' (n : nat) : Type :=
  match n with 
    | O => unit
    | S n' => (types (Ordinal (N_minus_lt n')) * ty' n')%type
  end.

Fixpoint ty_intro' (n : nat) (data : t) : ty' n :=
  match n as m in nat return ty' m with 
    | O => tt
    | S n' => (data (Ordinal (N_minus_lt n')), ty_intro' n' data)
  end.

Definition ty := ty' N.

Definition ty_intro := ty_intro' N.

Fixpoint ord' (n : nat) : ty' n -> ty' n -> Prop :=
  match n as m in nat return ty' m -> ty' m -> Prop with
    | O => fun d1 d2 => False
    | S n' => fun d1 d2 => 
        lex_ord (@ords (Ordinal (N_minus_lt n'))) (ord' n') d1 d2
  end.

Lemma wf_ord' n : well_founded (ord' n).
Proof.
rewrite/ord'; move: wf_ords; move: ords; clear ords wf_ords.
induction n=> ords WF; first by constructor.
apply: wf_eta; apply: wf_lex_ord; first by [].
by apply: (IHn ords).
Qed.

Definition ord (d1 d2 : t) := ord' N (ty_intro d1) (ty_intro d2).

Lemma wf_ord : well_founded ord.
Proof. by rewrite/ord; apply: wf_funct; apply: wf_ord'. Qed.

Definition cast_ty (T1 T2: Type) (pf: T1=T2) (x : T1) : T2.
rewrite pf in x; refine x.
Defined. 

Lemma types_eq (i j : 'I_N) : i=j -> types i=types j.
Proof. by move=> ->. Defined.

Definition get i (d : t) : types i := d i.

Definition set i (new_i : types i) (d : t) : t := 
  fun j : 'I_N => 
    match ord_dec i j with 
      | left pf => cast_ty (types_eq pf) new_i
      | right _ => d j
    end.
Implicit Arguments set [].

Lemma gss i x d : get i (set i x d) = x.
Proof.
rewrite/get/set; case: (ord_dec i i)=> //.
rewrite/cast_ty/eq_rect_r/eq_rect/types_eq/eq_ind_r/eq_ind/eq_rect=> e. 
by rewrite (UIP_refl _ _ e).
Qed.

Lemma gso i j x d : i<>j -> get j (set i x d) = get j d.
Proof. by rewrite/get/set; case: (ord_dec i j). Qed.

Local Open Scope nat_scope.

Lemma ord_upd' : forall i data1 data2 num_cores, 
  @ords i (get i data2) (get i data1) -> 
  (N - num_cores <= i < N)%nat -> (num_cores <= N)%nat -> 
  (forall j : 'I_N, j < i -> get j data1=get j data2) -> 
  ord' num_cores (ty_intro' num_cores data2) (ty_intro' num_cores data1).
Proof.
move=> [i pf] d1 d2 num_cores H1; move/andP=> []; move/leP=> H2; move/ltP.
induction num_cores as [|n]; first by rewrite -minusE /= in H2=> /= H3; omega.
move=> /= H3 H4 H5; case: (ord_dec (Ordinal pf) (Ordinal (N_minus_lt n))).
by move=> EQ; apply: lex_ord_left; rewrite -EQ.
rewrite/get in H5; move=> NEQ; rewrite -H5; have NEQ2: (i <> N - n.+1)
  by move=> H6; apply: NEQ; subst; f_equal; apply: proof_irr.
have: (N - S n < i) by apply/ltP; simpl in H2; omega. 
move/ltP=> H6; apply lex_ord_right; apply: IHn=> //=.
by move: H6; rewrite -minusE=> H6; omega.
by move: (ltP H4)=> H7; apply/leP; omega.
have H6: (i <> N - n.+1)
  by move=> H6; apply: NEQ; subst; f_equal; apply: proof_irr.
by move: H2=> /= H2; apply/ltP; omega.
Qed.

Lemma ord_upd i x d : ords x (get i d) -> ord (set i x d) d.
Proof.
move=> A; apply ord_upd' with (i := i)=> //. 
rewrite gss=> //. 
have B: (O <= i < N) by apply/andP; split.
rewrite -minusE; move: (andP B)=> {A B}[]A B. 
move: (leP A)=> A'; move: (ltP B)=> B'; apply/andP; split. 
- by apply/leP; omega.
- by apply/ltP; omega. 
move=> j Hlt; rewrite gso=> //.
case: i x A Hlt; case: j=> /= i pf new_i A Hlt j pf'=> H1.
by move: pf'; case: H1=> ->; move/ltP=> ?; omega.
Qed.

End lex. 

End Lex.

(* The following defines a wf-order on the type                           *)
(*   \Sigma ix : 'I_N. T ix                                               *)

Section sig_ord.

Variable N : pos.

Variable T : 'I_N -> Type.

Variable ords : forall ix : 'I_N, T ix -> T ix -> Prop.

Variable ords_wf : forall ix, well_founded (@ords ix).

Definition sig_data := {ix : 'I_N & T ix}.

Definition sig_ord (x y : sig_data) :=
  exists pf : projT1 x = projT1 y,
    (@ords (projT1 x))
      (projT2 x) 
      (cast_ty (lift_eq _ (sym_eq pf)) (projT2 y)).

Lemma wf_sig_ord : well_founded sig_ord.
Proof.
move=> []i.
apply (well_founded_induction (@ords_wf i)).
move=> x IH.
apply: Acc_intro=> []j []/=pf H2.

have H3: @ords i (cast _ pf (projT2 j)) x.
{ move: pf H2; case: j=> /= ix j pf; subst ix.
  by rewrite !cast_ty_erefl. }

case: (IH _ H3)=> H4.

apply: Acc_intro=> y H5; apply: H4.

have pf2: projT1 y = i.
{ by case: H5=> pf0 _; rewrite pf0. }

exists pf2=> /=.

move: pf2; set r := projT1 y; subst i.
rewrite cast_ty_erefl.

move=> pf2; move: H5; subst r; case=> pf3. 
by have ->: sym_eq pf3 = sym_eq pf2 by apply: proof_irr.
Qed.

End sig_ord.
