Zlength_nil: forall A : Type, Zlength [] = 0
Zlength_rev: forall (T : Type) (vl : list T), Zlength (rev vl) = Zlength vl
initial_world.Zlength_rev: forall (T : Type) (vl : list T), Zlength (rev vl) = Zlength vl
Zlength_correct: forall (A : Type) (l : list A), Zlength l = Z.of_nat (Datatypes.length l)
Zlength_list_repeat': forall (A : Type) (n : nat) (v : A), Zlength (list_repeat n v) = Z.of_nat n
Zlength_map: forall (A B : Type) (f : A -> B) (l : list A), Zlength (map f l) = Zlength l
initial_world.Zlength_map: forall (A B : Type) (f : A -> B) (l : list A), Zlength (map f l) = Zlength l
Zlength_cons: forall (A : Type) (x : A) (l : list A), Zlength (x :: l) = Z.succ (Zlength l)
Zlength_list_repeat: forall (A : Type) (n : Z) (x : A), 0 <= n -> Zlength (list_repeat (Z.to_nat n) x) = n
initial_world.Zlength_app: forall (T : Type) (al bl : list T), Zlength (al ++ bl) = Zlength al + Zlength bl
Zlength_app: forall (T : Type) (al bl : list T), Zlength (al ++ bl) = Zlength al + Zlength bl
mem_lemmas.Forall2_Zlength:
  forall (A B : Type) (f : A -> B -> Prop) (l1 : list A) (l2 : list B), Forall2 f l1 l2 -> Zlength l1 = Zlength l2
Zlength_firstn: forall (A : Type) (n : Z) (v : list A), Zlength (firstn (Z.to_nat n) v) = Z.min (Z.max 0 n) (Zlength v)
Zlength_skipn: forall (A : Type) (n : Z) (v : list A), Zlength (skipn (Z.to_nat n) v) = Z.max 0 (Zlength v - Z.max 0 n)
upd_Znth_Zlength: forall (A : Type) (i : Z) (l : list A) (v : A), 0 <= i < Zlength l -> Zlength (upd_Znth i l v) = Zlength l
replist_Zlength:
  forall (cs : compspecs) (t : type) (lo hi : Z) (al : list (reptype t)), lo <= hi -> Zlength (replist t lo hi al) = hi - lo
Zlength_sublist: forall (A : Type) (lo hi : Z) (al : list A), 0 <= lo <= hi -> hi <= Zlength al -> Zlength (sublist lo hi al) = hi - lo
Zlength_sublist_correct:
  forall (A : Type) (l : list A) (lo hi : Z), 0 <= lo <= hi -> hi <= Zlength l -> Zlength (sublist lo hi l) = hi - lo
array_pred_ext_derives:
  forall (A B : Type) (dA : Inhabitant A) (dB : Inhabitant B) (lo hi : Z) (P0 : Z -> A -> val -> mpred) (P1 : Z -> B -> val -> mpred)
    (v0 : list A) (v1 : list B) (p : val),
  (Zlength v0 = hi - lo -> Zlength v1 = hi - lo) ->
  (forall i : Z, lo <= i < hi -> P0 i (Znth (i - lo) v0) p |-- P1 i (Znth (i - lo) v1) p) ->
  array_pred lo hi P0 v0 p |-- array_pred lo hi P1 v1 p
aggregate_pred.array_pred_ext_derives:
  forall (A B : Type) (dA : Inhabitant A) (dB : Inhabitant B) (lo hi : Z) (P0 : Z -> A -> val -> mpred) (P1 : Z -> B -> val -> mpred)
    (v0 : list A) (v1 : list B) (p : val),
  (Zlength v0 = hi - lo -> Zlength v1 = hi - lo) ->
  (forall i : Z, lo <= i < hi -> P0 i (Znth (i - lo) v0) p |-- P1 i (Znth (i - lo) v1) p) ->
  aggregate_pred.array_pred lo hi P0 v0 p |-- aggregate_pred.array_pred lo hi P1 v1 p
Zlength_default_val_Tarray_tuchar: forall (cs : compspecs) (n : Z) (a : attr), 0 <= n -> Zlength (default_val (Tarray tuchar n a)) = n