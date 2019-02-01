
Database sublist2
rewrite -> @sublist_sublist of type forall (A : Type) (i j k m : Z) (l : list A),
                                    0 <= m -> 0 <= k <= i -> i <= j - m -> sublist k i (sublist m j l) = sublist (k + m) (i + m) l then use tactic Zlength_solve
rewrite <- app_assoc of type forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n
rewrite -> app_nil_r of type forall (A : Type) (l : list A), l ++ [] = l
rewrite -> app_nil_l of type forall (A : Type) (l : list A), [] ++ l = l
rewrite -> @sublist_app' of type forall (A : Type) (lo hi : Z) (al bl : list A),
                                 0 <= lo <= Zlength al ->
                                 0 <= hi - Zlength al <= Zlength bl ->
                                 sublist lo hi (al ++ bl) = sublist lo (Zlength al) al ++ sublist 0 (hi - Zlength al) bl then use tactic Zlength_solve
rewrite -> @sublist_app2 of type forall (A : Type) (i j : Z) (al bl : list A),
                                 0 <= Zlength al <= i -> sublist i j (al ++ bl) = sublist (i - Zlength al) (j - Zlength al) bl then use tactic Zlength_solve
rewrite -> sublist_app1 of type forall (A : Type) (k i : Z) (al bl : list A),
                                0 <= k <= i -> i <= Zlength al -> sublist k i (al ++ bl) = sublist k i al then use tactic Zlength_solve
rewrite -> map_app of type forall (A B : Type) (f : A -> B) (l l' : list A), map f (l ++ l') = map f l ++ map f l'
rewrite -> @map_sublist of type forall (A B : Type) (F : A -> B) (lo hi : Z) (al : list A),
                                map F (sublist lo hi al) = sublist lo hi (map F al)
rewrite -> map_Zlist_repeat of type forall (A B : Type) (f : A -> B) (n : Z) (x : A), map f (Zlist_repeat n x) = Zlist_repeat n (f x)
rewrite -> Znth_Zlist_repeat of type forall (A : Type) (d : Inhabitant A) (i n : Z) (x : A), 0 <= i < n -> Znth i (Zlist_repeat n x) = x then use tactic Zlength_solve
rewrite -> sublist_Zlist_repeat of type forall (A : Type) (lo hi n : Z) (x : A),
                                        0 <= lo <= hi -> hi <= n -> sublist lo hi (Zlist_repeat n x) = Zlist_repeat (hi - lo) x then use tactic Zlength_solve
