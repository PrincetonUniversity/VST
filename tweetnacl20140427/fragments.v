Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.

Require Import split_array_lemmas.

(*Folding data_at's over the same C (rep)type*)
Definition datas_at sh t (l: list ((reptype t) * val)) :=
  List.fold_right (fun dv P => P * match dv with (data,v) => data_at sh t data v end) emp l. 

Lemma datas_at_nil sh t:
      datas_at sh t nil = emp.
Proof. reflexivity. Qed.

Lemma datas_at_cons sh t x l:
      datas_at sh t (cons x l) = datas_at sh t l * match x with (data,v) => data_at sh t data v end.
Proof.
  destruct x. unfold datas_at. rewrite fold_right_cons. trivial. 
Qed. 
Lemma datas_at_cons' sh t x l:
      datas_at sh t (cons x l) = datas_at sh t l * datas_at sh t [x].
Proof.
  unfold datas_at. simpl. rewrite emp_sepcon. trivial. 
Qed. 

Require Import Permutation.
Lemma datas_at_Permutation sh t: forall l l' (Perm: Permutation l l'),
      datas_at sh t l = datas_at sh t l'.
Proof. intros.
  induction Perm. reflexivity.
  do 2 rewrite datas_at_cons. rewrite IHPerm. trivial.
  do 4 rewrite datas_at_cons. destruct x as [data1 v1]. destruct y as [data2 v2].
    do 2 rewrite sepcon_assoc. f_equal. apply sepcon_comm.
  rewrite IHPerm1; trivial.
Qed.

Lemma datas_at_app sh t: forall l l', 
      datas_at sh t (l ++ l') = datas_at sh t l * datas_at sh t l'.
Proof.
  induction l; intros. simpl. rewrite emp_sepcon. trivial.
  simpl. rewrite IHl; clear IHl.
    do 2 rewrite sepcon_assoc. f_equal. apply sepcon_comm. 
Qed. 

Lemma data_at_datas_at t sh data v:
  data_at sh t data v = datas_at sh t [(data,v)].
Proof. simpl. rewrite emp_sepcon; trivial. Qed.

Lemma datas_at_split2 t (A:legal_alignas_type t = true) sh data data1 data2 n v:
  Zlength data1 = n -> Zlength data2 = n -> data1++data2 = data->
  datas_at sh (Tarray t (2*n) noattr) [(data,v)] = 
  (!!offset_in_range (sizeof t * 0) v &&
   !!offset_in_range (sizeof t * Zlength data) v &&
    datas_at sh (Tarray t n noattr) [(data1,v); (data2,offset_val (Int.repr (sizeof t * n)) v)]).
Proof.
  intros. fold reptype in *. 
  assert ((2*n)%Z = Zlength data). subst. rewrite Zlength_app. omega.
  rewrite H2. simpl. 
  erewrite append_split_Tarray_at; eauto.
  do 2 rewrite emp_sepcon. repeat rewrite H, H0. rewrite sepcon_comm; trivial.
Qed. 

Lemma datas_at_split2' t (A:legal_alignas_type t = true) sh data data1 data2 n v:
      Zlength data1 = n -> Zlength data2 = n -> data1++data2 = data->
      offset_in_range (sizeof t * 0) v /\
        offset_in_range (sizeof t * Zlength data) v ->
  datas_at sh (Tarray t (2*n) noattr) [(data,v)] = 
  datas_at sh (Tarray t n noattr) [(data1,v); (data2,offset_val (Int.repr (sizeof t * n)) v)].
Proof.
  intros. fold reptype in *. 
  assert ((2*n)%Z = Zlength data). subst. rewrite Zlength_app. omega.
  rewrite H3. simpl. 
  erewrite append_split_Tarray_at; eauto.
  do 2 rewrite emp_sepcon. repeat rewrite H, H0. rewrite sepcon_comm. normalize.
Qed.

Fixpoint count_offsets t (data: list (list (reptype t))) (v:val) : list ((list (reptype t)) * val) :=
  match data with
    nil => nil
  | (cons d ds) => (d, v) :: count_offsets t ds (offset_val (Int.repr (sizeof t * Zlength d)) v)
  end. 

Definition flatten {A} (l: list (list A)): list A :=
  List.fold_right (@List.app A) nil l.

Lemma flatten_Zlength_simple {A} n: forall (l:list (list A))
      (P: forall p, In p l -> Zlength p = n),
  (Zlength (flatten l) = n * Zlength l)%Z.
Proof.
  induction l; simpl; intros. do 2 rewrite Zlength_nil. rewrite Zmult_0_r. reflexivity.
  rewrite Zlength_app, Zlength_cons. rewrite IHl; clear IHl. 
  rewrite P. rewrite <- Zmult_succ_r_reverse. omega.
    left; trivial.
  intros. apply P. right; trivial.
Qed.
(*
Lemma datas_at_partition t (A:legal_alignas_type t = true) 
      sh n  (N: 0 <= n):
      forall (parts: list (list (reptype t)))
             (P: forall p, In p parts -> Zlength p = n) data v 
             (D: flatten parts = data)
             k (K: k = (Zlength parts * n)%Z)
             (Off: offset_in_range (sizeof t * 0) v /\
                   offset_in_range (sizeof t * Zlength data) v),
  datas_at sh (Tarray t k noattr) [(data,v)] = 
  datas_at sh (Tarray t n noattr) (count_offsets t parts v).
Proof. 
  induction parts; intros.
    subst; simpl in *. unfold data_at, data_at', array_at', rangespec, rangespec'. simpl.
     admit. (*OK in comment*)
  subst; simpl.
  assert (ZL: (Zlength (a :: parts) * n= Zlength (a ++ flatten parts))%Z).
    clear -P. rewrite Zlength_cons, Zlength_app. erewrite (flatten_Zlength_simple n).
              rewrite P.  rewrite <- Zmult_succ_l_reverse. rewrite Z.mul_comm. omega. left; trivial.
         intros. apply P. right; trivial.
  rewrite ZL. simpl in *. erewrite append_split_Tarray_at. 2: trivial. 2: reflexivity.
  normalize.
  rewrite P; auto.
  rewrite sepcon_comm. f_equal.
  erewrite <- IHparts; clear IHparts. 3: reflexivity.
   rewrite (flatten_Zlength_simple n), Z.mul_comm, emp_sepcon; trivial.
  intros; apply P; auto.
  intros; apply P; auto.
  trivial.
  rewrite Z.mul_0_r in *. 
  split. apply offset_in_range_0.
  rewrite <- ZL in *.  clear ZL. rewrite (flatten_Zlength_simple n). 2: intros; apply P; auto.
  rewrite <- (Z.mul_comm n) in Off. rewrite Z.mul_assoc in *.
  assert (Zlength (a :: parts) = 1 + Zlength parts). rewrite Zlength_cons; omega.
  rewrite H, Z.mul_add_distr_l, Z.mul_1_r in Off; clear H. destruct Off as [_ Off].
  assert (NN1: 0 <= (sizeof t * n)%Z).
    apply Z.mul_nonneg_nonneg. specialize (sizeof_pos t). intros; omega. omega.
  apply offset_in_range_offset_val; trivial.
    apply Z.mul_nonneg_nonneg; trivial. specialize (Zlength_nonneg parts). intros; omega. 
Qed. 

Lemma datas_at_split2'' t (A:legal_alignas_type t = true) sh data data1 data2 n v:
      Zlength data1 = n -> Zlength data2 = n -> data1++data2 = data->
      offset_in_range (sizeof t * 0) v /\
        offset_in_range (sizeof t * Zlength data) v ->
  datas_at sh (Tarray t (2*n) noattr) [(data,v)] = 
  datas_at sh (Tarray t n noattr) [(data1,v); (data2,offset_val (Int.repr (sizeof t * n)) v)].
Proof.
  intros. fold reptype in *. 
  erewrite (datas_at_partition _ A sh n) with (parts:= [data1; data2]); subst n; simpl; trivial.
    apply Zlength_nonneg.
    intros. destruct H; subst; trivial. destruct H; subst; trivial. contradiction.
    rewrite app_nil_r; trivial.
Qed. 
*)
(*Fragments are datas-at where all items are located at offsets from a single base address*)
Definition fragments_at sh t (l: list ((reptype t) * int)) (v:val) :=
  datas_at sh t (map (fun ui => match ui with (u,i) => (u, offset_val i v) end) l).

Lemma fragments_at_cons sh t x l:
      fragments_at sh t (cons x l) = fragments_at sh t l * fragments_at sh t [x].
Proof. 
  unfold fragments_at. extensionality v. 
  rewrite map_cons, datas_at_cons'. reflexivity.
Qed. 

Lemma fragments_at_Permutation sh t l l' (Perm: Permutation l l'):
      fragments_at sh t l = fragments_at sh t l'.
Proof.
  unfold fragments_at. extensionality v. 
  apply datas_at_Permutation. apply Permutation_map. trivial.
Qed.

Lemma fragments_at_app sh t l l':
      fragments_at sh t (l ++ l') = fragments_at sh t l * fragments_at sh t l'.
Proof.
  unfold fragments_at. extensionality v. rewrite map_app.
  apply datas_at_app.
Qed.