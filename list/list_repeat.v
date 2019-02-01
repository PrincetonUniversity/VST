length_list_repeat: forall (A : Type) (n : nat) (x : A), Datatypes.length (list_repeat n x) = n
Forall_list_repeat: forall (A : Type) (P : A -> Prop) (n : nat) (a : A), P a -> Forall P (list_repeat n a)
nth_list_repeat: forall (A : Type) (i n : nat) (x : A), nth i (list_repeat n x) x = x
in_list_repeat: forall (A : Type) (n : nat) (x y : A), In y (list_repeat n x) -> y = x
list_repeat_0: forall (A : Type) (x : A), list_repeat (Z.to_nat 0) x = []
Zlength_list_repeat': forall (A : Type) (n : nat) (v : A), Zlength (list_repeat n v) = Z.of_nat n
Zlist_repeat_fold: forall (A : Type) (n : Z) (x : A), list_repeat (Z.to_nat n) x = Zlist_repeat n x
repeat_Undef_inject_self: forall (f : meminj) (n : nat), list_forall2 (memval_inject f) (list_repeat n Undef) (list_repeat n Undef)
nth_list_repeat': forall (A : Type) (i n : nat) (x y : A), (i < n)%nat -> nth i (list_repeat n x) y = x
repeat_Undef_inject_any:
  forall (f : meminj) (vl : list memval), list_forall2 (memval_inject f) (list_repeat (Datatypes.length vl) Undef) vl
Zlength_list_repeat: forall (A : Type) (n : Z) (x : A), 0 <= n -> Zlength (list_repeat (Z.to_nat n) x) = n
map_list_repeat: forall (A B : Type) (f : A -> B) (n : nat) (x : A), map f (list_repeat n x) = list_repeat n (f x)
firstn_list_repeat: forall (A : Type) (v : A) (i k : nat), (i <= k)%nat -> firstn i (list_repeat k v) = list_repeat i v
list_repeat_app: forall (A : Type) (a b : nat) (x : A), list_repeat a x ++ list_repeat b x = list_repeat (a + b) x
repeat_Undef_inject_encode_val:
  forall (f : meminj) (chunk : memory_chunk) (v : val),
  list_forall2 (memval_inject f) (list_repeat (size_chunk_nat chunk) Undef) (encode_val chunk v)
skipn_list_repeat: forall (A : Type) (k n : nat) (a : A), (k <= n)%nat -> skipn k (list_repeat n a) = list_repeat (n - k) a
Znth_list_repeat_inrange: forall (A : Type) (d : Inhabitant A) (i n : Z) (a : A), 0 <= i < n -> Znth i (list_repeat (Z.to_nat n) a) = a
list_repeat_app':
  forall (A : Type) (a b : Z) (x : A),
  0 <= a -> 0 <= b -> list_repeat (Z.to_nat a) x ++ list_repeat (Z.to_nat b) x = list_repeat (Z.to_nat (a + b)) x
sublist_list_repeat:
  forall (A : Type) (i j k : Z) (v : A),
  0 <= i -> i <= j <= k -> sublist i j (list_repeat (Z.to_nat k) v) = list_repeat (Z.to_nat (j - i)) v