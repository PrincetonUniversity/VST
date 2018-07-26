Require Import compcert.common.Memory.

Inductive permjoin : option permission -> option permission -> option permission -> Prop :=
  | permjoin_None_l x : permjoin None x x
  | permjoin_None_r x : permjoin x None x
  (* NE + NE = NE *)
  | permjoin_NNN : permjoin (Some Nonempty) (Some Nonempty) (Some Nonempty)
  (* NE + R = R *)
  | permjoin_NRR : permjoin (Some Nonempty) (Some Readable) (Some Readable)
  | permjoin_RNR : permjoin (Some Readable) (Some Nonempty) (Some Readable)
  (* NE + W = W or F *)
  | permjoin_NWW : permjoin (Some Nonempty) (Some Writable) (Some Writable)
  | permjoin_NWF : permjoin (Some Nonempty) (Some Writable) (Some Freeable)
  | permjoin_WNW : permjoin (Some Writable) (Some Nonempty) (Some Writable)
  | permjoin_WNF : permjoin (Some Writable) (Some Nonempty) (Some Freeable)
  (* R + R = R or W or F *)
  | permjoin_RRR : permjoin (Some Readable) (Some Readable) (Some Readable)
  | permjoin_RRW : permjoin (Some Readable) (Some Readable) (Some Writable)
  | permjoin_RRF : permjoin (Some Readable) (Some Readable) (Some Freeable)
  (* R + W = W or F *)
  | permjoin_RWW : permjoin (Some Readable) (Some Writable) (Some Writable)
  | permjoin_WRW : permjoin (Some Writable) (Some Readable) (Some Writable)
  | permjoin_RWF : permjoin (Some Readable) (Some Writable) (Some Freeable)
  | permjoin_WRF : permjoin (Some Writable) (Some Readable) (Some Freeable).

  Lemma permjoin_comm:
    forall p1 p2 p3,
      permjoin p1 p2 p3 <-> permjoin p2 p1 p3.
  Proof.
    intros.
    split; intros;
      inversion H; subst;
        eauto using permjoin.
  Qed.

  Lemma permjoin_readable_if:
    forall p1 p2 p3
      (Hjoin: permjoin p1 p2 p3)
      (Hp1: Mem.perm_order' p1 Readable),
      Mem.perm_order' p3 Readable.
  Proof.
    intros.
    destruct p1 as [p1|]; simpl in Hp1; try (exfalso; now eauto);
      destruct p1; inversion Hp1; subst;
      inversion Hjoin; subst;
      simpl;
      now eauto using perm_order.
  Qed.

  Lemma permjoin_readable_iff:
    forall p1 p2 p3
      (Hjoin: permjoin p1 p2 p3),
      Mem.perm_order' p3 Readable <-> Mem.perm_order' p1 Readable \/ Mem.perm_order' p2 Readable.
  Proof.
    intros.
    split; intros Hreadable.
    - destruct p3 as [p3|]; simpl in Hreadable; try (exfalso; now eauto);
        destruct p3; inversion Hreadable; subst;
          inversion Hjoin; subst; simpl;
            eauto using perm_order.
    - destruct Hreadable;
        [| apply permjoin_comm in Hjoin];
        eauto using permjoin_readable_if.
  Qed.

   Lemma permjoin_order:
    forall p1 p2 p3
      (Hjoin: permjoin p1 p2 p3),
      Mem.perm_order'' p3 p1 /\ Mem.perm_order'' p3 p2.
  Proof.
    intros.
    destruct p1 as [p1|];
      destruct p2 as [p2|];
      inversion Hjoin; simpl;
      split; constructor.
  Qed.

