Require Import floyd.proofauto.
Require Export progs.reverse.
Require Export progs.list_dt.
Local Open Scope logic.

(*Some definitions needed from the example file (verif_reverse.v) *)
Instance LS: listspec t_struct_list _tail.
Proof. eapply mk_listspec; reflexivity. Defined. 

Definition sum_int := fold_right Int.add Int.zero.
Check var_types.
Definition Delta : tycontext := 
(PTree.Node
          (PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                      PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
             (PTree.Node PTree.Leaf None
                (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                   PTree.Leaf))) None
          (PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf (Some (tint, false)) PTree.Leaf)
                   None PTree.Leaf) None PTree.Leaf) None
             (PTree.Node PTree.Leaf None
                (PTree.Node PTree.Leaf (Some (tint, true)) PTree.Leaf))),
       PTree.empty type, tint,
       PTree.Node
         (PTree.Node
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                         (2%positive, tptr tvoid), 
                         (3%positive, tuint), (4%positive, tuint)]
                         (fun _ : environ => !!False) POST  [tvoid]
                         (fun _ : environ => !!False)))) PTree.Leaf) None
               PTree.Leaf) None
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH x : share * list int PRE 
                            [(_p, tptr t_struct_list)]
                            (let (sh0, contents0) := x in
                             `(lseg LS sh0 (map Vint contents0)) 
                               (eval_id _p) `nullval) POST  [tint]
                            (let (_, contents0) := x in
                             local (`(eq (Vint (sum_int contents0))) retval)))))
                     PTree.Leaf) None PTree.Leaf) None PTree.Leaf)) None
         (PTree.Node
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tptr tschar),
                         (2%positive, tint)](fun _ : environ => !!False)
                         POST  [tint](fun _ : environ => !!False))))
                  PTree.Leaf) None
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH x : share * list val PRE 
                            [(_p, tptr t_struct_list)]
                            (let (sh0, contents0) := x in
                             fun x0 : environ =>
                             !!writable_share sh0 &&
                             `(lseg LS sh0 contents0) 
                               (eval_id _p) `nullval x0) POST 
                            [tptr t_struct_list]
                            (let (sh0, contents0) := x in
                             `(lseg LS sh0 (rev contents0)) retval `nullval))))
                     PTree.Leaf)
                  (Some (Global_var (Tarray t_struct_list 3 noattr)))
                  PTree.Leaf)) None
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tdouble)]
                      (fun _ : environ => !!False) POST  [tdouble]
                      (fun _ : environ => !!False))))
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH u : unit PRE  []main_pre prog u POST  [tint]
                            main_post prog u))) PTree.Leaf) None PTree.Leaf)))).

Definition Delta2 : tycontext :=
(PTree.Node
           (PTree.Node
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf (Some (tptr t_struct_list, false))
                       PTree.Leaf) None PTree.Leaf) None
                 (PTree.Node
                    (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                       PTree.Leaf) None PTree.Leaf)) None
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                    PTree.Leaf))) None
           (PTree.Node PTree.Leaf None
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                       PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
        PTree.empty type, tptr t_struct_list, PTree.empty _).
(*        PTree.Node
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                          (2%positive, tptr tvoid), 
                          (3%positive, tuint), (4%positive, tuint)]
                          (fun _ : environ => !!False) POST  [tvoid]
                          (fun _ : environ => !!False)))) PTree.Leaf) None
                PTree.Leaf) None
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH x : share * list int * val PRE 
                             [(_p, tptr t_struct_list)]
                             (let (p0, p) := x in
                              let (sh0, contents0) := p0 in
                              PROP  ()
                              LOCAL  (`(eq p) (eval_id _p))
                              SEP 
                              (`(lseg LS sh0 (map Vint contents0) p nullval)))
                             POST  [tint]
                             (let (p0, _) := x in
                              let (_, contents0) := p0 in
                              local (`(eq (Vint (sum_int contents0))) retval)))))
                      PTree.Leaf) None PTree.Leaf) None PTree.Leaf)) None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tschar),
                          (2%positive, tint)](fun _ : environ => !!False)
                          POST  [tint](fun _ : environ => !!False))))
                   PTree.Leaf) None
                (PTree.Node
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH x : share * list val * val PRE 
                             [(_p, tptr t_struct_list)]
                             (let (p0, p) := x in
                              let (sh0, contents0) := p0 in
                              PROP  (writable_share sh0)
                              LOCAL  (`(eq p) (eval_id _p))
                              SEP  (`(lseg LS sh0 contents0 p nullval)))
                             POST  [tptr t_struct_list]
                             (let (p0, _) := x in
                              let (sh0, contents0) := p0 in
                              `(lseg LS sh0 (rev contents0)) retval `nullval))))
                      PTree.Leaf)
                   (Some (Global_var (Tarray t_struct_list 3 noattr)))
                   PTree.Leaf)) None
             (PTree.Node PTree.Leaf
                (Some
                   (Global_func
                      (WITH _ : unit PRE  [(1%positive, tdouble)]
                       (fun _ : environ => !!False) POST  [tdouble]
                       (fun _ : environ => !!False))))
                (PTree.Node
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH u : unit PRE  []main_pre prog u POST 
                             [tint]main_post prog u))) PTree.Leaf) None
                   PTree.Leaf)))).*)
