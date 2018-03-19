Require Import VST.floyd.base2.
Require Import VST.floyd.val_lemmas.
Require Import VST.floyd.sublist.

Instance Inhabitant_val : Inhabitant val := Vundef.
Instance Inhabitant_int: Inhabitant int := Int.zero.
Instance Inhabitant_byte: Inhabitant byte := Byte.zero.
Instance Inhabitant_int64: Inhabitant Int64.int := Int64.zero.
Instance Inhabitant_ptrofs: Inhabitant Ptrofs.int := Ptrofs.zero.
Instance Inhabitant_float : Inhabitant float := Float.zero.
Instance Inhabitant_float32 : Inhabitant float32 := Float32.zero.

Definition Vbyte (c: Byte.int) : val :=
  Vint (Int.repr (Byte.signed c)).

Lemma Znth_map_Vbyte: forall (i : Z) (l : list byte),
  0 <= i < Zlength l -> Znth i (map Vbyte l)  = Vbyte (Znth i l).
Proof.
  intros i l.
  apply Znth_map.
Qed.
Hint Rewrite Znth_map_Vbyte using list_solve : norm entailer_rewrite.

Lemma is_int_Vbyte: forall c, is_int I8 Signed (Vbyte c).
Proof.
intros. simpl. normalize. rewrite Int.signed_repr by rep_omega. rep_omega.
Qed.
Hint Resolve is_int_Vbyte.

Ltac fold_Vbyte :=
 repeat match goal with |- context [Vint (Int.repr (Byte.signed ?c))] =>
      fold (Vbyte c)
end.

Hint Rewrite 
   (@Znth_map val _) (@Znth_map int _) (@Znth_map byte _)
   (@Znth_map int64 _) (@Znth_map ptrofs _) (@Znth_map float _)
   (@Znth_map float32 _)
    using (auto; rewrite ?Zlength_map in *; omega) : sublist entailer_rewrite.

