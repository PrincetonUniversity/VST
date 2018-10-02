Require Export Coq.Arith.EqNat.
Require Export Coq.Relations.Relations.

Require Export compcert.lib.Axioms.
Require Export compcert.lib.Coqlib.
Require Export compcert.lib.Integers.
Require Export compcert.lib.Floats.
Require Export compcert.lib.Maps.
Require Export compcert.common.AST.
Require Export compcert.common.Values.
Require Export compcert.common.Memdata.
Require Export compcert.common.Memtype.
Require Export compcert.common.Memory.
Require Export compcert.common.Globalenvs.


Require Export VST.msl.Coqlib2. 
Require Export VST.veric.coqlib4.

(* Lemmas about ident lists *)

Fixpoint id_in_list (id: ident) (ids: list ident) : bool :=
 match ids with i::ids' => orb (Pos.eqb id i) (id_in_list id ids') | _ => false end.

Fixpoint compute_list_norepet (ids: list ident) : bool :=
 match ids with
 | id :: ids' => if id_in_list id ids' then false else compute_list_norepet ids'
 | nil => true
 end.

Lemma id_in_list_true: forall i ids, id_in_list i ids = true -> In i ids.
Proof.
 induction ids; simpl; intros. inv H. apply orb_true_iff in H; destruct H; auto.
 apply Peqb_true_eq in H. subst; auto.
Qed.

Lemma id_in_list_false: forall i ids, id_in_list i ids = false -> ~In i ids.
Proof.
 induction ids; simpl; intros; auto.
 apply orb_false_iff in H. destruct H.
 intros [?|?]. subst.
 rewrite Pos.eqb_refl in H; inv H.
 apply IHids; auto.
Qed.

Lemma compute_list_norepet_e: forall ids,
     compute_list_norepet ids = true -> list_norepet ids.
Proof.
 induction ids; simpl; intros.
 constructor.
 revert H; case_eq (id_in_list a ids); intros.
 inv H0.
 constructor; auto.
 apply id_in_list_false in H.
 auto.
Qed.

Lemma list_norepet_rev:
  forall A (l: list A), list_norepet (rev l) = list_norepet l.
Proof.
induction l; simpl; auto.
apply prop_ext; split; intros.
apply list_norepet_app in H.
destruct H as [? [? ?]].
rewrite IHl in H.
constructor; auto.
eapply list_disjoint_notin with (a::nil).
apply list_disjoint_sym; auto.
intros x y ? ? ?; subst.
contradiction (H1 y y); auto.
rewrite <- In_rev; auto.
simpl; auto.
rewrite list_norepet_app.
inv H.
split3; auto.
rewrite IHl; auto.
repeat constructor.
intro Hx. inv Hx.
intros x y ? ? ?; subst.
inv H0.
rewrite <- In_rev in H; contradiction.
auto.
Qed.

Lemma block_eq_dec: forall b1 b2: block, {b1 = b2} + {b1 <> b2}.
Proof. exact (Coqlib.peq). Qed.

Lemma rev_if_be_singleton:
  forall x, rev_if_be (x::nil) = (x::nil).
Proof. intro. unfold rev_if_be; destruct Archi.big_endian; auto. Qed.

Lemma rev_if_be_1: forall i, rev_if_be (i::nil) = (i::nil).
Proof. unfold rev_if_be; intros. destruct Archi.big_endian; reflexivity.
Qed.

Lemma decode_byte_val:
  forall m, decode_val Mint8unsigned (Byte m :: nil) =
              Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned m))).
Proof.
intros.
unfold decode_val. simpl.
f_equal.
unfold decode_int.
rewrite rev_if_be_singleton.
unfold int_of_bytes. f_equal. f_equal. apply Z.add_0_r.
Qed.

Lemma Vint_inj: forall x y, Vint x = Vint y -> x=y.
Proof. congruence. Qed.

Definition nullval : val := 
  if Archi.ptr64 then Vlong Int64.zero else Vint Int.zero.

Definition val_to_bool (v: val) : option bool :=
  match v with
    | Vint n => Some (negb (Int.eq n Int.zero))
    | Vptr _ _ => Some true
    | _ => None
  end.

Definition bool_of_valf (v: val): option bool :=
match v with
  | Vint i => Some (negb (Int.eq i Int.zero))
  | Vlong i => Some (negb (Int64.eq i Int64.zero))
  | Vfloat _ => None
  | Vsingle _ => None
  | Vptr _ _ => Some true
  | Vundef => None
end.