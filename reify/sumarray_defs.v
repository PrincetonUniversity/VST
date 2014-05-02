Require Import floyd.proofauto.
Require Export progs.sumarray.

Definition add_elem (f: Z -> val) (i: Z) := Int.add (force_int (f i)).


Definition Delta := 
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf (Some (tint, true)) PTree.Leaf)) None
            (PTree.Node
               (PTree.Node PTree.Leaf (Some (tptr tint, true)) PTree.Leaf)
               None (PTree.Node PTree.Leaf (Some (tint, false)) PTree.Leaf)))
         None
         (PTree.Node
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf (Some (tint, true)) PTree.Leaf)) None
            (PTree.Node
               (PTree.Node PTree.Leaf (Some (tint, true)) PTree.Leaf) None
               PTree.Leaf)), PTree.empty type, tint,
      PTree.Node
        (PTree.Node
           (PTree.Node
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some (Global_var (Tarray tint 4 noattr))) PTree.Leaf)
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tptr tvoid), (3%positive, tuint),
                        (4%positive, tuint)](fun _ : environ => !!False)
                        POST  [tvoid](fun _ : environ => !!False))))
                 PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
        (PTree.Node
           (PTree.Node
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH u : unit PRE  []main_pre prog u POST  [tint]
                           main_post prog u))) PTree.Leaf)
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tschar),
                        (2%positive, tint)](fun _ : environ => !!False) POST 
                        [tint](fun _ : environ => !!False)))) PTree.Leaf)
              None PTree.Leaf) None
           (PTree.Node PTree.Leaf
              (Some
                 (Global_func
                    (WITH _ : unit PRE  [(1%positive, tdouble)]
                     (fun _ : environ => !!False) POST  [tdouble]
                     (fun _ : environ => !!False))))
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH  p : val * share * (Z -> val), size0 : Z PRE 
                        [(_a, tptr tint), (_n, tint)]
                        (let (p0, contents0) := p in
                         let (a1, sh0) := p0 in
                         PROP  (0 <= size0 <= Int.max_signed;
                         forall i0 : Z,
                         0 <= i0 < size0 -> is_int (contents0 i0))
                         LOCAL  (`(eq a1) (eval_id _a);
                         `(eq (Vint (Int.repr size0))) (eval_id _n);
                         `isptr (eval_id _a))
                         SEP 
                         (`(array_at tint sh0 contents0 0 size0) (eval_id _a)))
                        POST  [tint]
                        (let (p0, contents0) := p in
                         let (a1, sh0) := p0 in
                         fun x1 : environ =>
                         local
                           (`(eq
                                (Vint
                                   (fold_range (add_elem contents0) Int.zero
                                      0 size0))) retval) x1 &&
                         `(array_at tint sh0 contents0 0 size0 a1) x1))))
                 PTree.Leaf)))).