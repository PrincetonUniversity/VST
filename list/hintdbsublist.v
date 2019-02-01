
Database sublist
rewrite -> @Znth_map float32 Inhabitant_float32 of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : float32 -> B)
                                                          (al : list float32), 0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @Znth_map float Inhabitant_float of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : float -> B) (al : list float),
                                                    0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @Znth_map ptrofs Inhabitant_ptrofs of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : ptrofs -> B) (al : list ptrofs),
                                                      0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @Znth_map int64 Inhabitant_int64 of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : int64 -> B) (al : list int64),
                                                    0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @Znth_map byte Inhabitant_byte of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : byte -> B) (al : list byte),
                                                  0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @Znth_map int Inhabitant_int of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : int -> B) (al : list int),
                                                0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @Znth_map val Inhabitant_val of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : val -> B) (al : list val),
                                                0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @map_list_repeat of type forall (A B : Type) (f : A -> B) (n : nat) (x : A), map f (list_repeat n x) = list_repeat n (f x)
rewrite -> @upd_Znth_app2 of type forall (A : Type) (l1 l2 : list A) (i : Z) (v : A),
                                  Zlength l1 <= i <= Zlength l1 + Zlength l2 ->
                                  upd_Znth i (l1 ++ l2) v = l1 ++ upd_Znth (i - Zlength l1) l2 v then use tactic list_solve
rewrite -> @upd_Znth_app1 of type forall (A : Type) (i : Z) (l1 l2 : list A),
                                  0 <= i < Zlength l1 -> forall v : A, upd_Znth i (l1 ++ l2) v = upd_Znth i l1 v ++ l2 then use tactic list_solve
rewrite -> @sublist_nil of type forall (A : Type) (lo : Z) (al : list A), sublist lo lo al = []
rewrite -> @upd_Znth_Zlength of type forall (A : Type) (i : Z) (l : list A) (v : A),
                                     0 <= i < Zlength l -> Zlength (upd_Znth i l v) = Zlength l then use tactic list_solve
rewrite -> @Znth_sublist of type forall (A : Type) (d : Inhabitant A) (lo i hi : Z) (al : list A),
                                 0 <= lo -> 0 <= i < hi - lo -> Znth i (sublist lo hi al) = Znth (i + lo) al then use tactic list_solve
rewrite -> app_Znth2 of type forall (A : Type) (a : Inhabitant A) (l l' : list A) (i : Z),
                             i >= Zlength l -> Znth i (l ++ l') = Znth (i - Zlength l) l' then use tactic list_solve
rewrite -> app_Znth1 of type forall (A : Type) (a : Inhabitant A) (l l' : list A) (i : Z), i < Zlength l -> Znth i (l ++ l') = Znth i l then use tactic list_solve
rewrite -> Z.add_0_r of type forall n : Z, n + 0 = n
rewrite -> Z.add_add_simpl_r_r of type forall n m p : Z, n + m - (p + m) = n - p
rewrite -> Z.add_add_simpl_r_l of type forall n m p : Z, n + m - (m + p) = n - p
rewrite -> Z.add_add_simpl_l_r of type forall n m p : Z, n + m - (p + n) = m - p
rewrite -> Z.add_add_simpl_l_l of type forall n m p : Z, n + m - (n + p) = m - p
rewrite -> Z.add_simpl_l of type forall n m : Z, n + m - n = m
rewrite -> @sublist_same of type forall (A : Type) (lo hi : Z) (al : list A), lo = 0 -> hi = Zlength al -> sublist lo hi al = al then use tactic list_solve
rewrite -> @sublist_list_repeat of type forall (A : Type) (i j k : Z) (v : A),
                                        0 <= i ->
                                        i <= j <= k -> sublist i j (list_repeat (Z.to_nat k) v) = list_repeat (Z.to_nat (j - i)) v then use tactic list_solve
rewrite -> @sublist_app2 of type forall (A : Type) (i j : Z) (al bl : list A),
                                 0 <= Zlength al <= i -> sublist i j (al ++ bl) = sublist (i - Zlength al) (j - Zlength al) bl then use tactic list_solve
rewrite -> sublist_app1 of type forall (A : Type) (k i : Z) (al bl : list A),
                                0 <= k <= i -> i <= Zlength al -> sublist k i (al ++ bl) = sublist k i al then use tactic list_solve
rewrite -> @sublist_sublist of type forall (A : Type) (i j k m : Z) (l : list A),
                                    0 <= m -> 0 <= k <= i -> i <= j - m -> sublist k i (sublist m j l) = sublist (k + m) (i + m) l then use tactic list_solve
rewrite -> Z.sub_diag of type forall n : Z, n - n = 0
rewrite -> Z.sub_add of type forall n m : Z, m - n + n = m
rewrite -> Z.add_simpl_r of type forall n m : Z, n + m - m = n
rewrite -> Z.min_l of type forall n m : Z, n <= m -> Z.min n m = n then use tactic omega
rewrite -> Z.min_r of type forall n m : Z, m <= n -> Z.min n m = m then use tactic omega
rewrite -> Z.max_l of type forall n m : Z, m <= n -> Z.max n m = n then use tactic omega
rewrite -> Z.max_r of type forall n m : Z, n <= m -> Z.max n m = m then use tactic omega
rewrite -> @Zlength_sublist of type forall (A : Type) (lo hi : Z) (al : list A),
                                    0 <= lo <= hi -> hi <= Zlength al -> Zlength (sublist lo hi al) = hi - lo then use tactic list_solve
rewrite -> Z.add_0_r of type forall n : Z, n + 0 = n
rewrite -> Z.add_0_l of type forall n : Z, 0 + n = n
rewrite -> Z.sub_0_r of type forall n : Z, n - 0 = n
rewrite -> @Zlength_list_repeat of type forall (A : Type) (n : Z) (x : A), 0 <= n -> Zlength (list_repeat (Z.to_nat n) x) = n then use tactic list_solve
rewrite -> Zlength_map of type forall (A B : Type) (f : A -> B) (l : list A), Zlength (map f l) = Zlength l
rewrite -> Zlength_app of type forall (T : Type) (al bl : list T), Zlength (al ++ bl) = Zlength al + Zlength bl
rewrite <- app_nil_end of type forall (A : Type) (l : list A), l = l ++ []
rewrite -> @list_repeat_0 of type forall (A : Type) (x : A), list_repeat (Z.to_nat 0) x = []
rewrite -> Zlength_nil of type forall A : Type, Zlength [] = 0
rewrite -> Zlength_cons of type forall (A : Type) (x : A) (l : list A), Zlength (x :: l) = Z.succ (Zlength l)
rewrite -> @Znth_list_repeat_inrange of type forall (A : Type) (d : Inhabitant A) (i n : Z) (a : A),
                                             0 <= i < n -> Znth i (list_repeat (Z.to_nat n) a) = a
rewrite -> subsub1 of type forall a b : Z, a - (a - b) = b
rewrite -> @sublist_rejoin' of type forall (A : Type) (lo mid mid' hi : Z) (al : list A),
                                    mid = mid' ->
                                    0 <= lo <= mid ->
                                    mid' <= hi <= Zlength al -> sublist lo mid al ++ sublist mid' hi al = sublist lo hi al then use tactic list_solve
rewrite -> Zlength_rev of type forall (T : Type) (vl : list T), Zlength (rev vl) = Zlength vl
rewrite -> app_nil_l of type forall (A : Type) (l : list A), [] ++ l = l
rewrite -> sublist_nil' of type forall (A : Type) (lo lo' : Z) (al : list A), lo = lo' -> sublist lo lo' al = [] then use tactic list_solve
rewrite -> app_nil_r of type forall (A : Type) (l : list A), l ++ [] = l
rewrite -> app_nil_l of type forall (A : Type) (l : list A), [] ++ l = l
rewrite -> @Znth_0_cons of type forall (A : Type) (a : Inhabitant A) (l : list A) (v : A), Znth 0 (v :: l) = v
rewrite -> @Znth_map positive Inhabitant_positive of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : positive -> B)
                                                            (al : list positive),
                                                          0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @Znth_map nat Inhabitant_nat of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : nat -> B) (al : list nat),
                                                0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
rewrite -> @Znth_map Z Inhabitant_Z of type forall (B : Type) (db : Inhabitant B) (i : Z) (f : Z -> B) (al : list Z),
                                            0 <= i < Zlength al -> Znth i (map f al) = f (Znth i al) then use tactic (
auto; rewrite ?Zlength_map in *; omega)
