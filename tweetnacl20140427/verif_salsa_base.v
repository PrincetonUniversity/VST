Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.
(*Require Import fragments.*)
Require Import ZArith. 
Require Import Salsa20.

Require Import tweetnaclVerifiableC.
Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

Lemma data_at_ext sh t v v' p: v=v' -> data_at sh t v p |-- data_at sh t v' p.
Proof. intros; subst. trivial. Qed.

(*
Definition EightWord (q:QuadWord * QuadWord) (v:val) : mpred :=
  match q with ((q0, q1, q2, q3),(q4, q5, q6, q7)) =>
    data_at Tsh (Tarray tuchar 4 noattr) (map Vint [q0; q1; q2; q3; q4; q5; q6; q7]) v
  end.*)
Definition QuadByte2ValList B : list val :=
  match B with (b0, b1, b2, b3) => 
   map Vint (map Int.repr (map Byte.unsigned [b0; b1; b2; b3]))
  end.

Lemma QuadByteValList_length q: length (QuadByte2ValList q) = 4%nat.
  destruct q as [[[? ?] ?] ?]. reflexivity. Qed.

Definition EightByte (q:QuadByte * QuadByte) (v:val) : mpred :=
  match q with (q1, q2) =>
    data_at Tsh (Tarray tuchar 8 noattr) ((QuadByte2ValList q1) ++ (QuadByte2ValList q2)) v
  end.

Definition SixteenByte2ValList (B:SixteenByte) : list val :=
  match B with (q0, q1, q2, q3) => 
   QuadByte2ValList q0 ++ QuadByte2ValList q1 ++ QuadByte2ValList q2 ++ QuadByte2ValList q3
  end.

Definition ThirtyTwoByte (q:SixteenByte * SixteenByte) (v:val) : mpred :=
  match q with (q1, q2) =>
    @data_at CompSpecs Tsh (Tarray tuchar 32 noattr) ((SixteenByte2ValList q1) ++ (SixteenByte2ValList q2)) v
  end.

Definition QByte (q:QuadByte) (v:val) : mpred :=
  data_at Tsh (Tarray tuchar 4 noattr) (QuadByte2ValList q) v.

Definition QuadChunks2ValList (l: list QuadByte) : list val :=
  List.fold_right (fun q vals => QuadByte2ValList q ++ vals) nil l.

Definition flatten16 (B:SixteenByte) : list QuadByte :=
  match B with (q0, q1, q2, q3) => [q0; q1; q2; q3] end.
Lemma SixteenByte2ValList_flatten B:
  QuadChunks2ValList (flatten16 B) = SixteenByte2ValList B.
  destruct B as (((q0, q1), q2), q3). simpl. rewrite app_nil_r. trivial.
Qed.

Lemma QuadByteValList_ZLength q: 4 = Zlength (QuadByte2ValList q).
  destruct q as (((q0, q1), q2), q3). simpl. reflexivity. Qed.

Lemma SixteenByte2ValList_Zlength C: 16 = Zlength (SixteenByte2ValList C).
  destruct C as (((q0, q1), q2), q3). simpl.
  repeat rewrite Zlength_app. repeat rewrite <- QuadByteValList_ZLength.
  reflexivity. Qed.

Definition SByte (q:SixteenByte) (v:val) : mpred :=
  @data_at CompSpecs Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList q) v.

Lemma ThirtyTwoByte_split16 q v:
  field_compatible (Tarray tuchar 32 noattr) [] v ->
  ThirtyTwoByte q v = 
  (SByte (fst q) v * SByte (snd q) (offset_val (Int.repr 16) v))%logic.
Proof. destruct q as [s1 s2]. simpl; intros.
  erewrite append_split2_data_at_Tarray_at_tuchar; try reflexivity;
  try rewrite Zlength_app; repeat rewrite <- SixteenByte2ValList_Zlength; trivial.
Qed.

Lemma QuadByte2ValList_firstn4 q l: 
         firstn 4 (QuadByte2ValList q ++ l) = QuadByte2ValList q.
   Proof. destruct q as (((b0, b1), b2), b3); trivial. Qed.

Lemma QuadByte2ValList_skipn4 q l: 
         skipn 4 (QuadByte2ValList q ++ l) = l.
   Proof. destruct q as (((b0, b1), b2), b3); trivial. Qed.

Definition Select16Q (Q:SixteenByte) i :QuadByte :=
  match Q with (((b0, b1), b2), b3) =>
    if zeq i 0 then b0 else
    if zeq i 1 then b1 else
    if zeq i 2 then b2 else b3
  end.
Definition UnSelect16Q (Q:SixteenByte) i : list QuadByte :=
  match Q with (((b0, b1), b2), b3) =>
    if zeq i 0 then [b1;b2;b3] else
    if zeq i 1 then [b0;b2;b3] else
    if zeq i 2 then [b0;b1;b3] else [b0;b1;b2]
  end.
Definition SplitSelect16Q (Q:SixteenByte) i : (list QuadByte * list QuadByte) :=
  match Q with (((b0, b1), b2), b3) =>
    if zeq i 0 then ([], [b1;b2;b3]) else
    if zeq i 1 then ([b0], [b2;b3]) else
    if zeq i 2 then ([b0;b1], [b3]) else ([b0;b1;b2], [])
  end.
Lemma Select_SplitSelect16Q Q i front back:
    (front, back) = SplitSelect16Q Q i ->
    SixteenByte2ValList Q = 
    QuadChunks2ValList front ++ QuadChunks2ValList [Select16Q Q i] ++ QuadChunks2ValList back.
Proof.
  unfold Select16Q, SplitSelect16Q; intros.
  destruct Q as (((q0, q1), q2), q3). simpl.
  destruct (zeq i 0); simpl. inv H; simpl. repeat rewrite app_nil_r; trivial.
  destruct (zeq i 1); simpl. inv H; simpl. repeat rewrite app_nil_r; trivial.
  destruct (zeq i 2); simpl. inv H; simpl. repeat rewrite app_nil_r. repeat rewrite app_assoc. trivial.
  destruct (zeq i 3); simpl; inv H; simpl. repeat rewrite app_nil_r. repeat rewrite app_assoc. trivial.
  repeat rewrite app_nil_r. repeat rewrite app_assoc. trivial.
Qed.

Lemma QuadChunk2ValList_ZLength: forall l, Zlength (QuadChunks2ValList l) = (4 * Zlength l)%Z.
Proof. Opaque Z.mul.
  unfold QuadChunks2ValList. induction l; simpl. reflexivity.
  rewrite Zlength_app, IHl, <- QuadByteValList_ZLength.
  rewrite Zlength_cons; omega.
  Transparent Z.mul.
Qed.

Lemma Select_SplitSelect16Q_Zlength Q i front back:
    (front, back) = SplitSelect16Q Q i -> 0<= i < 4 ->
    Zlength front = i /\ Zlength back = 3-i.
Proof.
  unfold SplitSelect16Q; intros.
  destruct Q as (((q0, q1), q2), q3).
  destruct (zeq i 0). inv H. split; reflexivity.
  destruct (zeq i 1). inv H. split; reflexivity.
  destruct (zeq i 2). inv H. split; reflexivity. 
  destruct (zeq i 3). inv H. split; reflexivity. omega.
Qed.

Definition QBytes (l:list QuadByte) (v:val) : mpred :=
  data_at Tsh (Tarray tuchar (4*Zlength l) noattr) (QuadChunks2ValList l) v.

Lemma QBytes16 s: SByte s = QBytes (flatten16 s).
Proof. 
  destruct s as (((q0, q1), q2), q3). simpl. 
  unfold SByte, QBytes. simpl. rewrite app_nil_r.
  trivial.
Qed. 

Definition QuadWordRep (q:QuadWord):list val :=
  match q with (q0, q1, q2, q3) => map Vint [q0;q1;q2;q3] end.
Definition SixteenWordRep (w:SixteenWord):list val :=
  match w with (q0, q1, q2, q3) => QuadWordRep q0 ++ QuadWordRep q1 ++ QuadWordRep q2 ++ QuadWordRep q3 end.

Definition littleendian_of_SixteenByte (x:SixteenByte): QuadWord :=
  match x with (q0, q1, q2, q3) => (littleendian q0, littleendian q1, littleendian q2, littleendian q3) end.


     Lemma QuadWR_length q: length (QuadWordRep q) = 4%nat.
        destruct q as [[[? ?] ?] ?]. simpl. reflexivity. Qed.
     Lemma QuadWR_zlength q: Zlength (QuadWordRep q) = 4. 
        rewrite Zlength_correct, QuadWR_length. trivial. Qed.
     Lemma SixteenWR_length s: length (SixteenWordRep s) = 16%nat.
        destruct s as [[[? ?] ?] ?]. simpl.
        repeat rewrite app_length. repeat rewrite  QuadWR_length. reflexivity. Qed. 
     Lemma SixteenWR_zlength s: Zlength (SixteenWordRep s) = 16. 
        rewrite Zlength_correct, SixteenWR_length. trivial. Qed.

Lemma QuadWR_int q i: (0<=i<4)%nat -> exists ii, nth i (QuadWordRep q) Vundef = Vint ii.
  intros. destruct q as [[[? ?] ?] ?]. simpl.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity. omega. Qed. 

Lemma SixteenWR_int s i: (0<=i<16)%nat -> exists ii, nth i (SixteenWordRep s) Vundef = Vint ii.
  intros. destruct s as [[[? ?] ?] ?]. simpl.
  destruct q as [[[? ?] ?] ?]. destruct q0 as [[[? ?] ?] ?].
  destruct q1 as [[[? ?] ?] ?]. destruct q2 as [[[? ?] ?] ?]. simpl. 
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity.
  destruct i. eexists; reflexivity. omega.
Qed.

Lemma SixteenWR_Znth_int i s: (0 <= i < 16) ->
       exists ii : int, Znth i (SixteenWordRep s) Vundef = Vint ii.
Proof. intros. unfold Znth. if_tac; try omega.
   apply SixteenWR_int. destruct H. apply Z2Nat.inj_lt in H1; simpl in *; omega.
Qed.

Lemma QuadWR_Z_int: forall (q : QuadWord) (i : Z),
               0 <= i < 4 -> exists ii : int, Znth i (QuadWordRep q) Vundef = Vint ii.
Proof. intros. unfold Znth. if_tac. omega.
       apply QuadWR_int. destruct H.
       split. 
         apply Z2Nat.inj_le in H. apply H. omega. omega.
         apply Z2Nat.inj_lt in H1. apply H1. omega. omega.
Qed.



Lemma SixteenWordRep_MapVint ss: exists l, SixteenWordRep ss = map Vint l.
Proof.
destruct ss as [[[s0 s1] s2] s3]. 
destruct s0 as [[[x0 x1] x2] x3].
destruct s1 as [[[x4 x5] x6] x7].
destruct s2 as [[[x8 x9] x10] x11].
destruct s3 as [[[x12 x13] x14] x15]. simpl.
exists [x0; x1; x2; x3; x4; x5; x6; x7;
    x8; x9; x10; x11; x12; x13; x14; x15].
reflexivity. 
Qed. 

Definition QuadWordRepI (q : QuadWord) :=
  match q with (q0, q1, q2, q3) => [q0; q1; q2; q3] end.
Lemma QuadWordRepI_QuadWordRep q: QuadWordRep q = map Vint  (QuadWordRepI q).
Proof. destruct q as [[[q0 q1] q2] q3]. reflexivity. Qed.

Definition SixteenWordRepI (w : SixteenWord) :=
  match w with (q0, q1, q2, q3) => 
    QuadWordRepI q0 ++ QuadWordRepI q1 ++ QuadWordRepI q2 ++ QuadWordRepI q3
  end.
Lemma SixteenWordRepI_SixteenWordRep w: SixteenWordRep w = map Vint (SixteenWordRepI w).
Proof. destruct w as [[[q0 q1] q2] q3]. simpl.
   repeat rewrite QuadWordRepI_QuadWordRep. repeat rewrite map_app. reflexivity.
Qed.

    Lemma QuadWordRepI_length s: length (QuadWordRepI s) = 4%nat.
    Proof. destruct s as [[[q0 q1] q2] q3]. reflexivity. Qed.
    Lemma SixteenWordRepI_length s: length (SixteenWordRepI s) = 16%nat.
    Proof. destruct s as [[[q0 q1] q2] q3]. simpl.
      repeat rewrite app_length. repeat rewrite QuadWordRepI_length. reflexivity.
    Qed.

Lemma QuadByte2ValList_ints q: exists ints, length ints = 4%nat /\
      QuadByte2ValList q = map Vint ints.
Proof. destruct q as [[[b0 b1] b2] b3]. unfold QuadByte2ValList; simpl.
  exists [Int.repr (Byte.unsigned b0); Int.repr (Byte.unsigned b1);
          Int.repr (Byte.unsigned b2); Int.repr (Byte.unsigned b3)].
  split; trivial.
Qed. 

Lemma SixteenByte2ValList_ints N: exists ints, length ints = 16%nat /\
      SixteenByte2ValList N = map Vint ints.
Proof. destruct N as [[[q0 q1] q2] q3]. unfold SixteenByte2ValList.
  destruct (QuadByte2ValList_ints q0) as [ints0 [L0 Q0]]; rewrite Q0.
  destruct (QuadByte2ValList_ints q1) as [ints1 [L1 Q1]]; rewrite Q1.
  destruct (QuadByte2ValList_ints q2) as [ints2 [L2 Q2]]; rewrite Q2.
  destruct (QuadByte2ValList_ints q3) as [ints3 [L3 Q3]]; rewrite Q3.
  exists (ints0 ++ ints1 ++ ints2 ++ ints3).
  repeat rewrite map_app. repeat rewrite app_length. rewrite L0, L1, L2, L3.
  split; trivial.
Qed.

Lemma QuadByte2ValList_bytes q: exists bytes, length bytes = 4%nat /\
      QuadByte2ValList q = map Vint (map Int.repr (map Byte.unsigned bytes)).
Proof. destruct q as [[[b0 b1] b2] b3]. unfold QuadByte2ValList; simpl.
  exists [b0;b1;b2;b3]. split; trivial.
Qed. 

Lemma SixteenByte2ValList_bytes N: exists bytes, length bytes = 16%nat /\
      SixteenByte2ValList N =  map Vint (map Int.repr (map Byte.unsigned bytes)).
Proof. destruct N as [[[q0 q1] q2] q3]. unfold SixteenByte2ValList.
  destruct (QuadByte2ValList_bytes q0) as [bytes0 [L0 Q0]]; rewrite Q0.
  destruct (QuadByte2ValList_bytes q1) as [bytes1 [L1 Q1]]; rewrite Q1.
  destruct (QuadByte2ValList_bytes q2) as [bytes2 [L2 Q2]]; rewrite Q2.
  destruct (QuadByte2ValList_bytes q3) as [bytes3 [L3 Q3]]; rewrite Q3.
  exists (bytes0 ++ bytes1 ++ bytes2 ++ bytes3).
  repeat rewrite map_app. repeat rewrite app_length. rewrite L0, L1, L2, L3.
  split; trivial.
Qed.

Lemma QuadChunks2ValList_bytes: forall l, 
        exists bytes, length bytes = (4*length l)%nat /\
        QuadChunks2ValList l = map Vint (map Int.repr (map Byte.unsigned bytes)).
  Proof. unfold QuadChunks2ValList.
    induction l; simpl; intros. exists nil; split; trivial. 
    destruct IHl as [? [X1 X2]]; rewrite X2; clear X2.
    destruct (QuadByte2ValList_bytes a) as [? [Y1 Y2]]; rewrite Y2; clear Y2.
    repeat rewrite <- map_app. exists (x0 ++ x); split; trivial.
    rewrite app_length, X1, Y1. omega.
  Qed.