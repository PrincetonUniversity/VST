Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.queue.
Local Open Scope logic.

Instance QS: listspec t_struct_elem _next. 
Proof. eapply mk_listspec; reflexivity. Defined.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Definition fifo (contents: list val) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      !! is_pointer_or_null hd && !! is_pointer_or_null tl &&
      field_at Tsh t_struct_fifo [_head] hd p *
      field_at Tsh t_struct_fifo [_tail] tl p *
      if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val, 
              !!(contents = prefix++tl::nil)
            &&  (links QS Tsh prefix hd tl * field_at Tsh t_struct_elem [_next] nullval tl)).

Definition elemrep (rep: elemtype QS) (p: val) : mpred :=
  field_at Tsh t_struct_elem [_a]  (fst rep) p * 
  (field_at Tsh t_struct_elem [_b] (snd rep) p *
  (field_at_ Tsh t_struct_elem [_next] p)).

Lemma goal_1 :
forall (Q: name _Q)
  (h: name _h)
   (q : val) (contents : list val) (hd tl : val),
is_pointer_or_null hd ->
is_pointer_or_null tl ->
forall rho : environ,
let Delta :=
  (fun (A : Type) (x : A) => x) tycontext
    (PTree.Node
       (PTree.Node PTree.Leaf None
          (PTree.Node PTree.Leaf None
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, true))
                   PTree.Leaf) None PTree.Leaf))) None
       (PTree.Node PTree.Leaf None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, true))
                   PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
    var_types
      (PTree.Node
         (PTree.Node PTree.Leaf None
            (PTree.Node PTree.Leaf None
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, false))
                     PTree.Leaf) None PTree.Leaf))) None
         (PTree.Node PTree.Leaf None
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, true))
                     PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
      PTree.empty type, tint,
      PTree.Node
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tptr tvoid), (3%positive, tuint),
                        (4%positive, tuint)](fun _ : environ => !!False)
                        POST  [tvoid](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p : val PRE 
                           [(_Q, tptr t_struct_fifo),
                           (_p, tptr t_struct_elem)]
                           (let (q0, contents0) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q0) (eval_id _Q);
                            `(eq p) (eval_id _p))
                            SEP  (`(fifo contents0 q0);
                            `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                           [tvoid]
                           (let (q0, contents0) := p0 in
                            `(fifo (contents0 ++ p :: nil) q0))))) PTree.Leaf))
              None
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH _ : unit PRE  [](fun _ : environ => emp)
                           POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                    PTree.Leaf) None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  a : int, b : int PRE  [(_a, tint),
                           (_b, tint)]
                           PROP  ()
                           LOCAL  (`(eq (Vint a)) (eval_id _a);
                           `(eq (Vint b)) (eval_id _b))  SEP() POST 
                           [tptr t_struct_elem]
                           `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
           None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH n : int PRE  [(1%positive, tint)]
                        PROP  (4 <= Int.signed n)
                        LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                        POST  [tptr tvoid]`(memory_block Tsh n) retval)))
                 PTree.Leaf) None PTree.Leaf)) None
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tschar),
                        (2%positive, tint)](fun _ : environ => !!False) POST 
                        [tint](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  q0 : val, contents0 : list val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           PROP  ()
                           LOCAL  (`(eq q0) (eval_id _Q))
                           SEP  (`(fifo contents0 q0)) POST  [tint]
                           (fun x0 : environ =>
                            local
                              (`(eq
                                   (if isnil contents0 then Vtrue else Vfalse))
                                 retval) x0 && `(fifo contents0 q0) x0))))
                    PTree.Leaf)) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tint)]
                        PROP  ()
                        LOCAL ()
                        SEP 
                        (`(memory_block Tsh)
                           (`force_int (eval_id 2%positive))
                           (eval_id 1%positive)) POST  [tvoid]
                        (fun _ : environ => emp))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p : val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           (let (q0, contents0) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q0) (eval_id _Q))
                            SEP  (`(fifo (p :: contents0) q0))) POST 
                           [tptr t_struct_elem]
                           (let (q0, contents0) := p0 in
                            fun rho0 : environ =>
                            local (`(eq p) retval) rho0 &&
                            `(fifo contents0 q0) rho0 *
                            `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                    PTree.Leaf))
              (Some
                 (Global_func
                    (WITH _ : unit PRE  [(1%positive, tdouble)]
                     (fun _ : environ => !!False) POST  [tdouble]
                     (fun _ : environ => !!False))))
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH u : unit PRE  []main_pre prog u POST  [tint]
                           main_post prog u))) PTree.Leaf))))), tint,
    PTree.Node
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tptr tvoid), (3%positive, tuint),
                      (4%positive, tuint)](fun _ : environ => !!False) POST 
                      [tvoid](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p : val PRE 
                         [(_Q, tptr t_struct_fifo), (_p, tptr t_struct_elem)]
                         (let (q0, contents0) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q0) (eval_id _Q);
                          `(eq p) (eval_id _p))
                          SEP  (`(fifo contents0 q0);
                          `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                         [tvoid]
                         (let (q0, contents0) := p0 in
                          `(fifo (contents0 ++ p :: nil) q0))))) PTree.Leaf))
            None
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [](fun _ : environ => emp) POST 
                         [tptr t_struct_fifo]`(fifo nil) retval))) PTree.Leaf)
               None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  a : int, b : int PRE  [(_a, tint), (_b, tint)]
                         PROP  ()
                         LOCAL  (`(eq (Vint a)) (eval_id _a);
                         `(eq (Vint b)) (eval_id _b))  SEP() POST 
                         [tptr t_struct_elem]
                         `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
         None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH n : int PRE  [(1%positive, tint)]
                      PROP  (4 <= Int.signed n)
                      LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                      POST  [tptr tvoid]`(memory_block Tsh n) retval)))
               PTree.Leaf) None PTree.Leaf)) None
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tschar),
                      (2%positive, tint)](fun _ : environ => !!False) POST 
                      [tint](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  q0 : val, contents0 : list val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         PROP  ()
                         LOCAL  (`(eq q0) (eval_id _Q))
                         SEP  (`(fifo contents0 q0)) POST  [tint]
                         (fun x0 : environ =>
                          local
                            (`(eq (if isnil contents0 then Vtrue else Vfalse))
                               retval) x0 && `(fifo contents0 q0) x0))))
                  PTree.Leaf)) None PTree.Leaf) None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tint)]
                      PROP  ()
                      LOCAL ()
                      SEP 
                      (`(memory_block Tsh) (`force_int (eval_id 2%positive))
                         (eval_id 1%positive)) POST  [tvoid]
                      (fun _ : environ => emp))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p : val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         (let (q0, contents0) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q0) (eval_id _Q))
                          SEP  (`(fifo (p :: contents0) q0))) POST 
                         [tptr t_struct_elem]
                         (let (q0, contents0) := p0 in
                          fun rho0 : environ =>
                          local (`(eq p) retval) rho0 &&
                          `(fifo contents0 q0) rho0 *
                          `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                  PTree.Leaf))
            (Some
               (Global_func
                  (WITH _ : unit PRE  [(1%positive, tdouble)]
                   (fun _ : environ => !!False) POST  [tdouble]
                   (fun _ : environ => !!False))))
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH u : unit PRE  []main_pre prog u POST  [tint]
                         main_post prog u))) PTree.Leaf))))) in
tc_environ Delta rho ->
!!True &&
(!!(hd = eval_id _h rho /\ q = eval_id _Q rho /\ True) &&
 (field_at Tsh t_struct_fifo [_head] hd q *
  (field_at Tsh t_struct_fifo [_tail] tl q *
   ((if isnil contents
     then !!(hd = nullval) && emp
     else
      EX  prefix : list val,
      !!(contents = prefix ++ tl :: nil) &&
      (links QS Tsh prefix hd tl *
       field_at Tsh t_struct_elem [_next] nullval tl)) * (emp * emp)))))
|-- !!(denote_tc_iszero (eval_id _h rho) \/
       is_true (Int.eq (Int.repr 0) Int.zero)) &&
    (!!is_int
         (force_val
            (sem_cast_neutral
               (force_val
                  (sem_cmp_pp Ceq true2 (eval_id _h rho) (Vint (Int.repr 0)))))) &&
     (!!((if isnil contents then Vtrue else Vfalse) =
         eval_id ret_temp
           (env_set (globals_only (id rho)) ret_temp
              (force_val
                 (sem_cast_neutral
                    (force_val
                       (sem_cmp_pp Ceq true2 (eval_id _h rho)
                          (Vint (Int.repr 0)))))))) &&
      (EX  ht : val * val,
       (let (hd0, tl0) := ht in
        !!is_pointer_or_null hd0 && !!is_pointer_or_null tl0 &&
        field_at Tsh t_struct_fifo [_head] hd0 q *
        field_at Tsh t_struct_fifo [_tail] tl0 q *
        (if isnil contents
         then !!(hd0 = nullval) && emp
         else
          EX  prefix : list val,
          !!(contents = prefix ++ tl0 :: nil) &&
          (links QS Tsh prefix hd0 tl0 *
           field_at Tsh t_struct_elem [_next] nullval tl0)))))).
Proof.
ungather_entail.
findvars.
entailer.
apply exp_right with (h, tl).
entailer.
if_tac. entailer.
entailer.
destruct prefix; entailer.
destruct tl; try contradiction; simpl.
entailer.
destruct v; try contradiction; simpl; entailer.
Qed.

Lemma goal_2 :
name _Q ->
name _Q' ->
EVAR
  (forall Frame : list (environ -> mpred),
   let Delta :=
     (fun (A : Type) (x : A) => x) tycontext
       (PTree.Node
          (PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf (Some (tptr tvoid, false))
                         PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
                PTree.Leaf) None PTree.Leaf) None
          (PTree.Node PTree.Leaf None
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, false))
                      PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
       PTree.empty type, tptr t_struct_fifo,
       PTree.Node
         (PTree.Node
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                         (2%positive, tptr tvoid), (3%positive, tuint),
                         (4%positive, tuint)](fun _ : environ => !!False)
                         POST  [tvoid](fun _ : environ => !!False))))
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH  p0 : val * list val, p : val PRE 
                            [(_Q, tptr t_struct_fifo),
                            (_p, tptr t_struct_elem)]
                            (let (q, contents) := p0 in
                             PROP  ()
                             LOCAL  (`(eq q) (eval_id _Q);
                             `(eq p) (eval_id _p))
                             SEP  (`(fifo contents q);
                             `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                            [tvoid]
                            (let (q, contents) := p0 in
                             `(fifo (contents ++ p :: nil) q))))) PTree.Leaf))
               None
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH _ : unit PRE  [](fun _ : environ => emp)
                            POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                     PTree.Leaf) None
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH  a : int, b : int PRE  [(_a, tint),
                            (_b, tint)]
                            PROP  ()
                            LOCAL  (`(eq (Vint a)) (eval_id _a);
                            `(eq (Vint b)) (eval_id _b))  SEP() POST 
                            [tptr t_struct_elem]
                            `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
            None
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH n : int PRE  [(1%positive, tint)]
                         PROP  (4 <= Int.signed n)
                         LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                         POST  [tptr tvoid]`(memory_block Tsh n) retval)))
                  PTree.Leaf) None PTree.Leaf)) None
         (PTree.Node
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tptr tschar),
                         (2%positive, tint)](fun _ : environ => !!False)
                         POST  [tint](fun _ : environ => !!False))))
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH  q : val, contents : list val PRE 
                            [(_Q, tptr t_struct_fifo)]
                            PROP  ()
                            LOCAL  (`(eq q) (eval_id _Q))
                            SEP  (`(fifo contents q)) POST  [tint]
                            (fun x0 : environ =>
                             local
                               (`(eq
                                    (if isnil contents then Vtrue else Vfalse))
                                  retval) x0 && `(fifo contents q) x0))))
                     PTree.Leaf)) None PTree.Leaf) None
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                         (2%positive, tint)]
                         PROP  ()
                         LOCAL ()
                         SEP 
                         (`(memory_block Tsh)
                            (`force_int (eval_id 2%positive))
                            (eval_id 1%positive)) POST  [tvoid]
                         (fun _ : environ => emp))))
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH  p0 : val * list val, p : val PRE 
                            [(_Q, tptr t_struct_fifo)]
                            (let (q, contents) := p0 in
                             PROP  ()
                             LOCAL  (`(eq q) (eval_id _Q))
                             SEP  (`(fifo (p :: contents) q))) POST 
                            [tptr t_struct_elem]
                            (let (q, contents) := p0 in
                             fun rho : environ =>
                             local (`(eq p) retval) rho &&
                             `(fifo contents q) rho *
                             `(field_at_ Tsh t_struct_elem [_next]) retval rho))))
                     PTree.Leaf))
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tdouble)]
                      (fun _ : environ => !!False) POST  [tdouble]
                      (fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf None
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH u : unit PRE  []main_pre prog u POST  [tint]
                            main_post prog u))) PTree.Leaf))))) in
   let witness := Int.repr 8 in
   PROP  ()  LOCAL  (tc_environ Delta)  SEP()
   |-- PROP  ()
       LOCAL 
       (tc_exprlist Delta
          (snd (split (fst ((1%positive, tint) :: nil, tptr tvoid))))
          (Econst_int (Int.repr 8) tuint :: nil))
       (SEPx
          (`(PROP  (4 <= Int.signed witness)
             LOCAL  (`(eq (Vint witness)) (eval_id 1%positive))  SEP())
             (make_args' ((1%positive, tint) :: nil, tptr tvoid)
                (eval_exprlist
                   (snd (split (fst ((1%positive, tint) :: nil, tptr tvoid))))
                   (Econst_int (Int.repr 8) tuint :: nil))) :: Frame))).
Proof. intros Q Q'; ungather_entail.
entailer1.
Qed.

Lemma goal_3 :
name _Q ->
name _Q' ->
forall rho : environ,
let Delta :=
  (fun (A : Type) (x : A) => x) tycontext
    (PTree.Node
       (PTree.Node
          (PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf (Some (tptr tvoid, true))
                      PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
             PTree.Leaf) None PTree.Leaf) None
       (PTree.Node PTree.Leaf None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, true))
                   PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
    var_types
      (PTree.Node
         (PTree.Node
            (PTree.Node
               (PTree.Node
                  (PTree.Node
                     (PTree.Node PTree.Leaf (Some (tptr tvoid, true))
                        PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
               PTree.Leaf) None PTree.Leaf) None
         (PTree.Node PTree.Leaf None
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, false))
                     PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
      var_types
        (PTree.Node
           (PTree.Node
              (PTree.Node
                 (PTree.Node
                    (PTree.Node
                       (PTree.Node PTree.Leaf (Some (tptr tvoid, false))
                          PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
                 PTree.Leaf) None PTree.Leaf) None
           (PTree.Node PTree.Leaf None
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, false))
                       PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
        PTree.empty type, tptr t_struct_fifo,
        PTree.Node
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                          (2%positive, tptr tvoid), (3%positive, tuint),
                          (4%positive, tuint)](fun _ : environ => !!False)
                          POST  [tvoid](fun _ : environ => !!False))))
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  p0 : val * list val, p : val PRE 
                             [(_Q, tptr t_struct_fifo),
                             (_p, tptr t_struct_elem)]
                             (let (q, contents) := p0 in
                              PROP  ()
                              LOCAL  (`(eq q) (eval_id _Q);
                              `(eq p) (eval_id _p))
                              SEP  (`(fifo contents q);
                              `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                             [tvoid]
                             (let (q, contents) := p0 in
                              `(fifo (contents ++ p :: nil) q))))) PTree.Leaf))
                None
                (PTree.Node
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH _ : unit PRE  [](fun _ : environ => emp)
                             POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                      PTree.Leaf) None
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  a : int, b : int PRE  [(_a, tint),
                             (_b, tint)]
                             PROP  ()
                             LOCAL  (`(eq (Vint a)) (eval_id _a);
                             `(eq (Vint b)) (eval_id _b))  SEP() POST 
                             [tptr t_struct_elem]
                             `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
             None
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH n : int PRE  [(1%positive, tint)]
                          PROP  (4 <= Int.signed n)
                          LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                          POST  [tptr tvoid]`(memory_block Tsh n) retval)))
                   PTree.Leaf) None PTree.Leaf)) None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tschar),
                          (2%positive, tint)](fun _ : environ => !!False)
                          POST  [tint](fun _ : environ => !!False))))
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  q : val, contents : list val PRE 
                             [(_Q, tptr t_struct_fifo)]
                             PROP  ()
                             LOCAL  (`(eq q) (eval_id _Q))
                             SEP  (`(fifo contents q)) POST  [tint]
                             (fun x0 : environ =>
                              local
                                (`(eq
                                     (if isnil contents
                                      then Vtrue
                                      else Vfalse)) retval) x0 &&
                              `(fifo contents q) x0)))) PTree.Leaf)) None
                PTree.Leaf) None
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                          (2%positive, tint)]
                          PROP  ()
                          LOCAL ()
                          SEP 
                          (`(memory_block Tsh)
                             (`force_int (eval_id 2%positive))
                             (eval_id 1%positive)) POST  [tvoid]
                          (fun _ : environ => emp))))
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  p0 : val * list val, p : val PRE 
                             [(_Q, tptr t_struct_fifo)]
                             (let (q, contents) := p0 in
                              PROP  ()
                              LOCAL  (`(eq q) (eval_id _Q))
                              SEP  (`(fifo (p :: contents) q))) POST 
                             [tptr t_struct_elem]
                             (let (q, contents) := p0 in
                              fun rho0 : environ =>
                              local (`(eq p) retval) rho0 &&
                              `(fifo contents q) rho0 *
                              `(field_at_ Tsh t_struct_elem [_next]) retval
                                rho0)))) PTree.Leaf))
                (Some
                   (Global_func
                      (WITH _ : unit PRE  [(1%positive, tdouble)]
                       (fun _ : environ => !!False) POST  [tdouble]
                       (fun _ : environ => !!False))))
                (PTree.Node PTree.Leaf None
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH u : unit PRE  []main_pre prog u POST 
                             [tint]main_post prog u))) PTree.Leaf))))),
      tptr t_struct_fifo,
      PTree.Node
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tptr tvoid), (3%positive, tuint),
                        (4%positive, tuint)](fun _ : environ => !!False)
                        POST  [tvoid](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p : val PRE 
                           [(_Q, tptr t_struct_fifo),
                           (_p, tptr t_struct_elem)]
                           (let (q, contents) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q) (eval_id _Q);
                            `(eq p) (eval_id _p))
                            SEP  (`(fifo contents q);
                            `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                           [tvoid]
                           (let (q, contents) := p0 in
                            `(fifo (contents ++ p :: nil) q))))) PTree.Leaf))
              None
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH _ : unit PRE  [](fun _ : environ => emp)
                           POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                    PTree.Leaf) None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  a : int, b : int PRE  [(_a, tint),
                           (_b, tint)]
                           PROP  ()
                           LOCAL  (`(eq (Vint a)) (eval_id _a);
                           `(eq (Vint b)) (eval_id _b))  SEP() POST 
                           [tptr t_struct_elem]
                           `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
           None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH n : int PRE  [(1%positive, tint)]
                        PROP  (4 <= Int.signed n)
                        LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                        POST  [tptr tvoid]`(memory_block Tsh n) retval)))
                 PTree.Leaf) None PTree.Leaf)) None
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tschar),
                        (2%positive, tint)](fun _ : environ => !!False) POST 
                        [tint](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  q : val, contents : list val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           PROP  ()
                           LOCAL  (`(eq q) (eval_id _Q))
                           SEP  (`(fifo contents q)) POST  [tint]
                           (fun x0 : environ =>
                            local
                              (`(eq
                                   (if isnil contents then Vtrue else Vfalse))
                                 retval) x0 && `(fifo contents q) x0))))
                    PTree.Leaf)) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tint)]
                        PROP  ()
                        LOCAL ()
                        SEP 
                        (`(memory_block Tsh)
                           (`force_int (eval_id 2%positive))
                           (eval_id 1%positive)) POST  [tvoid]
                        (fun _ : environ => emp))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p : val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           (let (q, contents) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q) (eval_id _Q))
                            SEP  (`(fifo (p :: contents) q))) POST 
                           [tptr t_struct_elem]
                           (let (q, contents) := p0 in
                            fun rho0 : environ =>
                            local (`(eq p) retval) rho0 &&
                            `(fifo contents q) rho0 *
                            `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                    PTree.Leaf))
              (Some
                 (Global_func
                    (WITH _ : unit PRE  [(1%positive, tdouble)]
                     (fun _ : environ => !!False) POST  [tdouble]
                     (fun _ : environ => !!False))))
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH u : unit PRE  []main_pre prog u POST  [tint]
                           main_post prog u))) PTree.Leaf))))),
    tptr t_struct_fifo,
    PTree.Node
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tptr tvoid), (3%positive, tuint),
                      (4%positive, tuint)](fun _ : environ => !!False) POST 
                      [tvoid](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p : val PRE 
                         [(_Q, tptr t_struct_fifo), (_p, tptr t_struct_elem)]
                         (let (q, contents) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q) (eval_id _Q); `(eq p) (eval_id _p))
                          
                          SEP  (`(fifo contents q);
                          `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                         [tvoid]
                         (let (q, contents) := p0 in
                          `(fifo (contents ++ p :: nil) q))))) PTree.Leaf))
            None
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [](fun _ : environ => emp) POST 
                         [tptr t_struct_fifo]`(fifo nil) retval))) PTree.Leaf)
               None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  a : int, b : int PRE  [(_a, tint), (_b, tint)]
                         PROP  ()
                         LOCAL  (`(eq (Vint a)) (eval_id _a);
                         `(eq (Vint b)) (eval_id _b))  SEP() POST 
                         [tptr t_struct_elem]
                         `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
         None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH n : int PRE  [(1%positive, tint)]
                      PROP  (4 <= Int.signed n)
                      LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                      POST  [tptr tvoid]`(memory_block Tsh n) retval)))
               PTree.Leaf) None PTree.Leaf)) None
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tschar),
                      (2%positive, tint)](fun _ : environ => !!False) POST 
                      [tint](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  q : val, contents : list val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         PROP  ()
                         LOCAL  (`(eq q) (eval_id _Q))
                         SEP  (`(fifo contents q)) POST  [tint]
                         (fun x0 : environ =>
                          local
                            (`(eq (if isnil contents then Vtrue else Vfalse))
                               retval) x0 && `(fifo contents q) x0))))
                  PTree.Leaf)) None PTree.Leaf) None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tint)]
                      PROP  ()
                      LOCAL ()
                      SEP 
                      (`(memory_block Tsh) (`force_int (eval_id 2%positive))
                         (eval_id 1%positive)) POST  [tvoid]
                      (fun _ : environ => emp))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p : val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         (let (q, contents) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q) (eval_id _Q))
                          SEP  (`(fifo (p :: contents) q))) POST 
                         [tptr t_struct_elem]
                         (let (q, contents) := p0 in
                          fun rho0 : environ =>
                          local (`(eq p) retval) rho0 &&
                          `(fifo contents q) rho0 *
                          `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                  PTree.Leaf))
            (Some
               (Global_func
                  (WITH _ : unit PRE  [(1%positive, tdouble)]
                   (fun _ : environ => !!False) POST  [tdouble]
                   (fun _ : environ => !!False))))
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH u : unit PRE  []main_pre prog u POST  [tint]
                         main_post prog u))) PTree.Leaf))))) in
tc_environ Delta rho ->
!!True &&
(!!(eval_id _Q rho = force_val (sem_cast_neutral (eval_id _Q' rho)) /\ True) &&
 (memory_block Tsh (Int.repr 8)
    (eval_id ret_temp (env_set (globals_only rho) ret_temp (eval_id _Q' rho))) *
  (emp * emp)))
|-- !!True &&
    (!!True && (memory_block Tsh (Int.repr 8) (eval_id _Q rho) * emp)).
Proof. intros Q Q'; ungather_entail.
rewrite memory_block_isptr.
entailer.
rewrite H0.
destruct (eval_id _Q' rho); try (contradiction H1); auto.
Qed.

Lemma goal_4 :
name _Q ->
name _Q' ->
EVAR
  (forall n : nat,
   EVAR
     (forall (sh : share) (rho : environ),
      let Delta :=
        (fun (A : Type) (x : A) => x) tycontext
          (PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node
                      (PTree.Node
                         (PTree.Node PTree.Leaf (Some (tptr tvoid, true))
                            PTree.Leaf) None PTree.Leaf) None PTree.Leaf)
                   None PTree.Leaf) None PTree.Leaf) None
             (PTree.Node PTree.Leaf None
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf
                         (Some (tptr t_struct_fifo, true)) PTree.Leaf) None
                      PTree.Leaf) None PTree.Leaf)),
          var_types
            (PTree.Node
               (PTree.Node
                  (PTree.Node
                     (PTree.Node
                        (PTree.Node
                           (PTree.Node PTree.Leaf (Some (tptr tvoid, true))
                              PTree.Leaf) None PTree.Leaf) None PTree.Leaf)
                     None PTree.Leaf) None PTree.Leaf) None
               (PTree.Node PTree.Leaf None
                  (PTree.Node
                     (PTree.Node
                        (PTree.Node PTree.Leaf
                           (Some (tptr t_struct_fifo, false)) PTree.Leaf)
                        None PTree.Leaf) None PTree.Leaf)),
            var_types
              (PTree.Node
                 (PTree.Node
                    (PTree.Node
                       (PTree.Node
                          (PTree.Node
                             (PTree.Node PTree.Leaf
                                (Some (tptr tvoid, false)) PTree.Leaf) None
                             PTree.Leaf) None PTree.Leaf) None PTree.Leaf)
                    None PTree.Leaf) None
                 (PTree.Node PTree.Leaf None
                    (PTree.Node
                       (PTree.Node
                          (PTree.Node PTree.Leaf
                             (Some (tptr t_struct_fifo, false)) PTree.Leaf)
                          None PTree.Leaf) None PTree.Leaf)),
              PTree.empty type, tptr t_struct_fifo,
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
                                (fun _ : environ => !!False))))
                         (PTree.Node PTree.Leaf
                            (Some
                               (Global_func
                                  (WITH  p0 : val * list val, p : val PRE 
                                   [(_Q, tptr t_struct_fifo),
                                   (_p, tptr t_struct_elem)]
                                   (let (q, contents) := p0 in
                                    PROP  ()
                                    LOCAL  (`(eq q) (eval_id _Q);
                                    `(eq p) (eval_id _p))
                                    SEP  (`(fifo contents q);
                                    `(field_at_ Tsh t_struct_elem [_next] p)))
                                   POST  [tvoid]
                                   (let (q, contents) := p0 in
                                    `(fifo (contents ++ p :: nil) q)))))
                            PTree.Leaf)) None
                      (PTree.Node
                         (PTree.Node PTree.Leaf
                            (Some
                               (Global_func
                                  (WITH _ : unit PRE  []
                                   (fun _ : environ => emp) POST 
                                   [tptr t_struct_fifo]`(fifo nil) retval)))
                            PTree.Leaf) None
                         (PTree.Node PTree.Leaf
                            (Some
                               (Global_func
                                  (WITH  a : int, b : int PRE  [(_a, tint),
                                   (_b, tint)]
                                   PROP  ()
                                   LOCAL  (`(eq (Vint a)) (eval_id _a);
                                   `(eq (Vint b)) (eval_id _b))  SEP() POST 
                                   [tptr t_struct_elem]
                                   `(elemrep (Vint a, Vint b)) retval)))
                            PTree.Leaf))) None
                   (PTree.Node
                      (PTree.Node PTree.Leaf
                         (Some
                            (Global_func
                               (WITH n0 : int PRE  [(1%positive, tint)]
                                PROP  (4 <= Int.signed n0)
                                LOCAL  (`(eq (Vint n0)) (eval_id 1%positive))
                                  SEP() POST  [tptr tvoid]
                                `(memory_block Tsh n0) retval))) PTree.Leaf)
                      None PTree.Leaf)) None
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf
                         (Some
                            (Global_func
                               (WITH _ : unit PRE 
                                [(1%positive, tptr tschar),
                                (2%positive, tint)]
                                (fun _ : environ => !!False) POST  [tint]
                                (fun _ : environ => !!False))))
                         (PTree.Node PTree.Leaf
                            (Some
                               (Global_func
                                  (WITH  q : val, contents : list val PRE 
                                   [(_Q, tptr t_struct_fifo)]
                                   PROP  ()
                                   LOCAL  (`(eq q) (eval_id _Q))
                                   SEP  (`(fifo contents q)) POST  [tint]
                                   (fun x0 : environ =>
                                    local
                                      (`(eq
                                           (if isnil contents
                                            then Vtrue
                                            else Vfalse)) retval) x0 &&
                                    `(fifo contents q) x0)))) PTree.Leaf))
                      None PTree.Leaf) None
                   (PTree.Node
                      (PTree.Node PTree.Leaf
                         (Some
                            (Global_func
                               (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                                (2%positive, tint)]
                                PROP  ()
                                LOCAL ()
                                SEP 
                                (`(memory_block Tsh)
                                   (`force_int (eval_id 2%positive))
                                   (eval_id 1%positive)) POST  [tvoid]
                                (fun _ : environ => emp))))
                         (PTree.Node PTree.Leaf
                            (Some
                               (Global_func
                                  (WITH  p0 : val * list val, p : val PRE 
                                   [(_Q, tptr t_struct_fifo)]
                                   (let (q, contents) := p0 in
                                    PROP  ()
                                    LOCAL  (`(eq q) (eval_id _Q))
                                    SEP  (`(fifo (p :: contents) q))) POST 
                                   [tptr t_struct_elem]
                                   (let (q, contents) := p0 in
                                    fun rho0 : environ =>
                                    local (`(eq p) retval) rho0 &&
                                    `(fifo contents q) rho0 *
                                    `(field_at_ Tsh t_struct_elem [_next])
                                      retval rho0)))) PTree.Leaf))
                      (Some
                         (Global_func
                            (WITH _ : unit PRE  [(1%positive, tdouble)]
                             (fun _ : environ => !!False) POST  [tdouble]
                             (fun _ : environ => !!False))))
                      (PTree.Node PTree.Leaf None
                         (PTree.Node PTree.Leaf
                            (Some
                               (Global_func
                                  (WITH u : unit PRE  []main_pre prog u POST 
                                   [tint]main_post prog u))) PTree.Leaf))))),
            tptr t_struct_fifo,
            PTree.Node
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf
                       (Some
                          (Global_func
                             (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                              (2%positive, tptr tvoid), (3%positive, tuint),
                              (4%positive, tuint)]
                              (fun _ : environ => !!False) POST  [tvoid]
                              (fun _ : environ => !!False))))
                       (PTree.Node PTree.Leaf
                          (Some
                             (Global_func
                                (WITH  p0 : val * list val, p : val PRE 
                                 [(_Q, tptr t_struct_fifo),
                                 (_p, tptr t_struct_elem)]
                                 (let (q, contents) := p0 in
                                  PROP  ()
                                  LOCAL  (`(eq q) (eval_id _Q);
                                  `(eq p) (eval_id _p))
                                  SEP  (`(fifo contents q);
                                  `(field_at_ Tsh t_struct_elem [_next] p)))
                                 POST  [tvoid]
                                 (let (q, contents) := p0 in
                                  `(fifo (contents ++ p :: nil) q)))))
                          PTree.Leaf)) None
                    (PTree.Node
                       (PTree.Node PTree.Leaf
                          (Some
                             (Global_func
                                (WITH _ : unit PRE  []
                                 (fun _ : environ => emp) POST 
                                 [tptr t_struct_fifo]`(fifo nil) retval)))
                          PTree.Leaf) None
                       (PTree.Node PTree.Leaf
                          (Some
                             (Global_func
                                (WITH  a : int, b : int PRE  [(_a, tint),
                                 (_b, tint)]
                                 PROP  ()
                                 LOCAL  (`(eq (Vint a)) (eval_id _a);
                                 `(eq (Vint b)) (eval_id _b))  SEP() POST 
                                 [tptr t_struct_elem]
                                 `(elemrep (Vint a, Vint b)) retval)))
                          PTree.Leaf))) None
                 (PTree.Node
                    (PTree.Node PTree.Leaf
                       (Some
                          (Global_func
                             (WITH n0 : int PRE  [(1%positive, tint)]
                              PROP  (4 <= Int.signed n0)
                              LOCAL  (`(eq (Vint n0)) (eval_id 1%positive))
                              SEP() POST  [tptr tvoid]
                              `(memory_block Tsh n0) retval))) PTree.Leaf)
                    None PTree.Leaf)) None
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf
                       (Some
                          (Global_func
                             (WITH _ : unit PRE  [(1%positive, tptr tschar),
                              (2%positive, tint)](fun _ : environ => !!False)
                              POST  [tint](fun _ : environ => !!False))))
                       (PTree.Node PTree.Leaf
                          (Some
                             (Global_func
                                (WITH  q : val, contents : list val PRE 
                                 [(_Q, tptr t_struct_fifo)]
                                 PROP  ()
                                 LOCAL  (`(eq q) (eval_id _Q))
                                 SEP  (`(fifo contents q)) POST  [tint]
                                 (fun x0 : environ =>
                                  local
                                    (`(eq
                                         (if isnil contents
                                          then Vtrue
                                          else Vfalse)) retval) x0 &&
                                  `(fifo contents q) x0)))) PTree.Leaf)) None
                    PTree.Leaf) None
                 (PTree.Node
                    (PTree.Node PTree.Leaf
                       (Some
                          (Global_func
                             (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                              (2%positive, tint)]
                              PROP  ()
                              LOCAL ()
                              SEP 
                              (`(memory_block Tsh)
                                 (`force_int (eval_id 2%positive))
                                 (eval_id 1%positive)) POST  [tvoid]
                              (fun _ : environ => emp))))
                       (PTree.Node PTree.Leaf
                          (Some
                             (Global_func
                                (WITH  p0 : val * list val, p : val PRE 
                                 [(_Q, tptr t_struct_fifo)]
                                 (let (q, contents) := p0 in
                                  PROP  ()
                                  LOCAL  (`(eq q) (eval_id _Q))
                                  SEP  (`(fifo (p :: contents) q))) POST 
                                 [tptr t_struct_elem]
                                 (let (q, contents) := p0 in
                                  fun rho0 : environ =>
                                  local (`(eq p) retval) rho0 &&
                                  `(fifo contents q) rho0 *
                                  `(field_at_ Tsh t_struct_elem [_next]) retval
                                    rho0)))) PTree.Leaf))
                    (Some
                       (Global_func
                          (WITH _ : unit PRE  [(1%positive, tdouble)]
                           (fun _ : environ => !!False) POST  [tdouble]
                           (fun _ : environ => !!False))))
                    (PTree.Node PTree.Leaf None
                       (PTree.Node PTree.Leaf
                          (Some
                             (Global_func
                                (WITH u : unit PRE  []main_pre prog u POST 
                                 [tint]main_post prog u))) PTree.Leaf))))),
          tptr t_struct_fifo,
          PTree.Node
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tptr tvoid), (3%positive, tuint),
                            (4%positive, tuint)](fun _ : environ => !!False)
                            POST  [tvoid](fun _ : environ => !!False))))
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH  p0 : val * list val, p : val PRE 
                               [(_Q, tptr t_struct_fifo),
                               (_p, tptr t_struct_elem)]
                               (let (q, contents) := p0 in
                                PROP  ()
                                LOCAL  (`(eq q) (eval_id _Q);
                                `(eq p) (eval_id _p))
                                SEP  (`(fifo contents q);
                                `(field_at_ Tsh t_struct_elem [_next] p)))
                               POST  [tvoid]
                               (let (q, contents) := p0 in
                                `(fifo (contents ++ p :: nil) q)))))
                        PTree.Leaf)) None
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH _ : unit PRE  [](fun _ : environ => emp)
                               POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                        PTree.Leaf) None
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH  a : int, b : int PRE  [(_a, tint),
                               (_b, tint)]
                               PROP  ()
                               LOCAL  (`(eq (Vint a)) (eval_id _a);
                               `(eq (Vint b)) (eval_id _b))  SEP() POST 
                               [tptr t_struct_elem]
                               `(elemrep (Vint a, Vint b)) retval)))
                        PTree.Leaf))) None
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH n0 : int PRE  [(1%positive, tint)]
                            PROP  (4 <= Int.signed n0)
                            LOCAL  (`(eq (Vint n0)) (eval_id 1%positive))
                            SEP() POST  [tptr tvoid]
                            `(memory_block Tsh n0) retval))) PTree.Leaf) None
                  PTree.Leaf)) None
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tschar),
                            (2%positive, tint)](fun _ : environ => !!False)
                            POST  [tint](fun _ : environ => !!False))))
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH  q : val, contents : list val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               PROP  ()
                               LOCAL  (`(eq q) (eval_id _Q))
                               SEP  (`(fifo contents q)) POST  [tint]
                               (fun x0 : environ =>
                                local
                                  (`(eq
                                       (if isnil contents
                                        then Vtrue
                                        else Vfalse)) retval) x0 &&
                                `(fifo contents q) x0)))) PTree.Leaf)) None
                  PTree.Leaf) None
               (PTree.Node
                  (PTree.Node PTree.Leaf
                     (Some
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tint)]
                            PROP  ()
                            LOCAL ()
                            SEP 
                            (`(memory_block Tsh)
                               (`force_int (eval_id 2%positive))
                               (eval_id 1%positive)) POST  [tvoid]
                            (fun _ : environ => emp))))
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH  p0 : val * list val, p : val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               (let (q, contents) := p0 in
                                PROP  ()
                                LOCAL  (`(eq q) (eval_id _Q))
                                SEP  (`(fifo (p :: contents) q))) POST 
                               [tptr t_struct_elem]
                               (let (q, contents) := p0 in
                                fun rho0 : environ =>
                                local (`(eq p) retval) rho0 &&
                                `(fifo contents q) rho0 *
                                `(field_at_ Tsh t_struct_elem [_next]) retval
                                  rho0)))) PTree.Leaf))
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tdouble)]
                         (fun _ : environ => !!False) POST  [tdouble]
                         (fun _ : environ => !!False))))
                  (PTree.Node PTree.Leaf None
                     (PTree.Node PTree.Leaf
                        (Some
                           (Global_func
                              (WITH u : unit PRE  []main_pre prog u POST 
                               [tint]main_post prog u))) PTree.Leaf))))) in
      tc_environ Delta rho ->
      !!True &&
      (!!True &&
       (numbd 0 (field_at_ Tsh t_struct_fifo [_head]) (eval_id _Q rho) *
        (numbd 1 (field_at_ Tsh t_struct_fifo [_tail]) (eval_id _Q rho) * emp)))
      |-- numbd n (field_at_ sh t_struct_fifo [_head])
            (force_ptr (eval_id _Q rho)) * !!True)).
Proof. intros Q Q'; ungather_entail.
unfold sh,n; entailer; cancel.
Qed.

Lemma goal_5 :
name _Q ->
name _Q' ->
forall rho : environ,
let Delta :=
  (fun (A : Type) (x : A) => x) tycontext
    (PTree.Node
       (PTree.Node
          (PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node PTree.Leaf (Some (tptr tvoid, true))
                      PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
             PTree.Leaf) None PTree.Leaf) None
       (PTree.Node PTree.Leaf None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, true))
                   PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
    var_types
      (PTree.Node
         (PTree.Node
            (PTree.Node
               (PTree.Node
                  (PTree.Node
                     (PTree.Node PTree.Leaf (Some (tptr tvoid, true))
                        PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
               PTree.Leaf) None PTree.Leaf) None
         (PTree.Node PTree.Leaf None
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, false))
                     PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
      var_types
        (PTree.Node
           (PTree.Node
              (PTree.Node
                 (PTree.Node
                    (PTree.Node
                       (PTree.Node PTree.Leaf (Some (tptr tvoid, false))
                          PTree.Leaf) None PTree.Leaf) None PTree.Leaf) None
                 PTree.Leaf) None PTree.Leaf) None
           (PTree.Node PTree.Leaf None
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, false))
                       PTree.Leaf) None PTree.Leaf) None PTree.Leaf)),
        PTree.empty type, tptr t_struct_fifo,
        PTree.Node
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                          (2%positive, tptr tvoid), (3%positive, tuint),
                          (4%positive, tuint)](fun _ : environ => !!False)
                          POST  [tvoid](fun _ : environ => !!False))))
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  p0 : val * list val, p : val PRE 
                             [(_Q, tptr t_struct_fifo),
                             (_p, tptr t_struct_elem)]
                             (let (q, contents) := p0 in
                              PROP  ()
                              LOCAL  (`(eq q) (eval_id _Q);
                              `(eq p) (eval_id _p))
                              SEP  (`(fifo contents q);
                              `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                             [tvoid]
                             (let (q, contents) := p0 in
                              `(fifo (contents ++ p :: nil) q))))) PTree.Leaf))
                None
                (PTree.Node
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH _ : unit PRE  [](fun _ : environ => emp)
                             POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                      PTree.Leaf) None
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  a : int, b : int PRE  [(_a, tint),
                             (_b, tint)]
                             PROP  ()
                             LOCAL  (`(eq (Vint a)) (eval_id _a);
                             `(eq (Vint b)) (eval_id _b))  SEP() POST 
                             [tptr t_struct_elem]
                             `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
             None
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH n : int PRE  [(1%positive, tint)]
                          PROP  (4 <= Int.signed n)
                          LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                          POST  [tptr tvoid]`(memory_block Tsh n) retval)))
                   PTree.Leaf) None PTree.Leaf)) None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tschar),
                          (2%positive, tint)](fun _ : environ => !!False)
                          POST  [tint](fun _ : environ => !!False))))
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  q : val, contents : list val PRE 
                             [(_Q, tptr t_struct_fifo)]
                             PROP  ()
                             LOCAL  (`(eq q) (eval_id _Q))
                             SEP  (`(fifo contents q)) POST  [tint]
                             (fun x0 : environ =>
                              local
                                (`(eq
                                     (if isnil contents
                                      then Vtrue
                                      else Vfalse)) retval) x0 &&
                              `(fifo contents q) x0)))) PTree.Leaf)) None
                PTree.Leaf) None
             (PTree.Node
                (PTree.Node PTree.Leaf
                   (Some
                      (Global_func
                         (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                          (2%positive, tint)]
                          PROP  ()
                          LOCAL ()
                          SEP 
                          (`(memory_block Tsh)
                             (`force_int (eval_id 2%positive))
                             (eval_id 1%positive)) POST  [tvoid]
                          (fun _ : environ => emp))))
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH  p0 : val * list val, p : val PRE 
                             [(_Q, tptr t_struct_fifo)]
                             (let (q, contents) := p0 in
                              PROP  ()
                              LOCAL  (`(eq q) (eval_id _Q))
                              SEP  (`(fifo (p :: contents) q))) POST 
                             [tptr t_struct_elem]
                             (let (q, contents) := p0 in
                              fun rho0 : environ =>
                              local (`(eq p) retval) rho0 &&
                              `(fifo contents q) rho0 *
                              `(field_at_ Tsh t_struct_elem [_next]) retval
                                rho0)))) PTree.Leaf))
                (Some
                   (Global_func
                      (WITH _ : unit PRE  [(1%positive, tdouble)]
                       (fun _ : environ => !!False) POST  [tdouble]
                       (fun _ : environ => !!False))))
                (PTree.Node PTree.Leaf None
                   (PTree.Node PTree.Leaf
                      (Some
                         (Global_func
                            (WITH u : unit PRE  []main_pre prog u POST 
                             [tint]main_post prog u))) PTree.Leaf))))),
      tptr t_struct_fifo,
      PTree.Node
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tptr tvoid), (3%positive, tuint),
                        (4%positive, tuint)](fun _ : environ => !!False)
                        POST  [tvoid](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p : val PRE 
                           [(_Q, tptr t_struct_fifo),
                           (_p, tptr t_struct_elem)]
                           (let (q, contents) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q) (eval_id _Q);
                            `(eq p) (eval_id _p))
                            SEP  (`(fifo contents q);
                            `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                           [tvoid]
                           (let (q, contents) := p0 in
                            `(fifo (contents ++ p :: nil) q))))) PTree.Leaf))
              None
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH _ : unit PRE  [](fun _ : environ => emp)
                           POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                    PTree.Leaf) None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  a : int, b : int PRE  [(_a, tint),
                           (_b, tint)]
                           PROP  ()
                           LOCAL  (`(eq (Vint a)) (eval_id _a);
                           `(eq (Vint b)) (eval_id _b))  SEP() POST 
                           [tptr t_struct_elem]
                           `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
           None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH n : int PRE  [(1%positive, tint)]
                        PROP  (4 <= Int.signed n)
                        LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                        POST  [tptr tvoid]`(memory_block Tsh n) retval)))
                 PTree.Leaf) None PTree.Leaf)) None
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tschar),
                        (2%positive, tint)](fun _ : environ => !!False) POST 
                        [tint](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  q : val, contents : list val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           PROP  ()
                           LOCAL  (`(eq q) (eval_id _Q))
                           SEP  (`(fifo contents q)) POST  [tint]
                           (fun x0 : environ =>
                            local
                              (`(eq
                                   (if isnil contents then Vtrue else Vfalse))
                                 retval) x0 && `(fifo contents q) x0))))
                    PTree.Leaf)) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tint)]
                        PROP  ()
                        LOCAL ()
                        SEP 
                        (`(memory_block Tsh)
                           (`force_int (eval_id 2%positive))
                           (eval_id 1%positive)) POST  [tvoid]
                        (fun _ : environ => emp))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p : val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           (let (q, contents) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q) (eval_id _Q))
                            SEP  (`(fifo (p :: contents) q))) POST 
                           [tptr t_struct_elem]
                           (let (q, contents) := p0 in
                            fun rho0 : environ =>
                            local (`(eq p) retval) rho0 &&
                            `(fifo contents q) rho0 *
                            `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                    PTree.Leaf))
              (Some
                 (Global_func
                    (WITH _ : unit PRE  [(1%positive, tdouble)]
                     (fun _ : environ => !!False) POST  [tdouble]
                     (fun _ : environ => !!False))))
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH u : unit PRE  []main_pre prog u POST  [tint]
                           main_post prog u))) PTree.Leaf))))),
    tptr t_struct_fifo,
    PTree.Node
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tptr tvoid), (3%positive, tuint),
                      (4%positive, tuint)](fun _ : environ => !!False) POST 
                      [tvoid](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p : val PRE 
                         [(_Q, tptr t_struct_fifo), (_p, tptr t_struct_elem)]
                         (let (q, contents) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q) (eval_id _Q); `(eq p) (eval_id _p))
                          
                          SEP  (`(fifo contents q);
                          `(field_at_ Tsh t_struct_elem [_next] p))) POST 
                         [tvoid]
                         (let (q, contents) := p0 in
                          `(fifo (contents ++ p :: nil) q))))) PTree.Leaf))
            None
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [](fun _ : environ => emp) POST 
                         [tptr t_struct_fifo]`(fifo nil) retval))) PTree.Leaf)
               None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  a : int, b : int PRE  [(_a, tint), (_b, tint)]
                         PROP  ()
                         LOCAL  (`(eq (Vint a)) (eval_id _a);
                         `(eq (Vint b)) (eval_id _b))  SEP() POST 
                         [tptr t_struct_elem]
                         `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
         None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH n : int PRE  [(1%positive, tint)]
                      PROP  (4 <= Int.signed n)
                      LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                      POST  [tptr tvoid]`(memory_block Tsh n) retval)))
               PTree.Leaf) None PTree.Leaf)) None
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tschar),
                      (2%positive, tint)](fun _ : environ => !!False) POST 
                      [tint](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  q : val, contents : list val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         PROP  ()
                         LOCAL  (`(eq q) (eval_id _Q))
                         SEP  (`(fifo contents q)) POST  [tint]
                         (fun x0 : environ =>
                          local
                            (`(eq (if isnil contents then Vtrue else Vfalse))
                               retval) x0 && `(fifo contents q) x0))))
                  PTree.Leaf)) None PTree.Leaf) None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tint)]
                      PROP  ()
                      LOCAL ()
                      SEP 
                      (`(memory_block Tsh) (`force_int (eval_id 2%positive))
                         (eval_id 1%positive)) POST  [tvoid]
                      (fun _ : environ => emp))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p : val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         (let (q, contents) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q) (eval_id _Q))
                          SEP  (`(fifo (p :: contents) q))) POST 
                         [tptr t_struct_elem]
                         (let (q, contents) := p0 in
                          fun rho0 : environ =>
                          local (`(eq p) retval) rho0 &&
                          `(fifo contents q) rho0 *
                          `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                  PTree.Leaf))
            (Some
               (Global_func
                  (WITH _ : unit PRE  [(1%positive, tdouble)]
                   (fun _ : environ => !!False) POST  [tdouble]
                   (fun _ : environ => !!False))))
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH u : unit PRE  []main_pre prog u POST  [tint]
                         main_post prog u))) PTree.Leaf))))) in
tc_environ Delta rho ->
!!True &&
(!!True &&
 (field_at Tsh
    (Tstruct _struct_fifo
       (Fcons _head
          (tptr
             (Tstruct _struct_elem
                (Fcons _a tint
                   (Fcons _b tint
                      (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                noattr))
          (Fcons _tail
             (tptr
                (Tstruct _struct_elem
                   (Fcons _a tint
                      (Fcons _b tint
                         (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                   noattr)) Fnil)) noattr) [_head] (Vint (Int.repr 0))
    (force_ptr (eval_id _Q rho)) *
  (field_at Tsh
     (Tstruct _struct_fifo
        (Fcons _head
           (tptr
              (Tstruct _struct_elem
                 (Fcons _a tint
                    (Fcons _b tint
                       (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                 noattr))
           (Fcons _tail
              (tptr
                 (Tstruct _struct_elem
                    (Fcons _a tint
                       (Fcons _b tint
                          (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                    noattr)) Fnil)) noattr) [_tail] (Vint (Int.repr 0))
     (force_ptr (eval_id _Q rho)) * emp)))
|-- !!True &&
    (!!is_pointer_or_null (force_val (sem_cast_neutral (eval_id _Q rho))) &&
     fifo nil
       (eval_id ret_temp
          (env_set (globals_only (id rho)) ret_temp
             (force_val (sem_cast_neutral (eval_id _Q rho)))))).
Proof. intros Q Q'; ungather_entail.
  unfold fifo.
  entailer.
  apply exp_right with (nullval,nullval).
  if_tac; [ | congruence].
 entailer!.
Qed.

Lemma goal_6 :
name _Q ->
name _p ->
name _h ->
name _t ->
forall q p : val,
let Delta :=
  @abbreviate tycontext
    (@PTree.Node (type * bool)
       (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
          (@None (type * bool))
          (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
             (@None (type * bool))
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@Some (type * bool) (tptr t_struct_elem, false))
                   (@PTree.Leaf (type * bool))) (@None (type * bool))
                (@PTree.Leaf (type * bool))))) (@None (type * bool))
       (@PTree.Node (type * bool)
          (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
             (@None (type * bool))
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@Some (type * bool) (tptr t_struct_elem, true))
                   (@PTree.Leaf (type * bool))) (@None (type * bool))
                (@PTree.Leaf (type * bool)))) (@None (type * bool))
          (@PTree.Node (type * bool)
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@Some (type * bool) (tptr t_struct_fifo, true))
                   (@PTree.Leaf (type * bool))) (@None (type * bool))
                (@PTree.Leaf (type * bool))) (@None (type * bool))
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@Some (type * bool) (tptr t_struct_elem, false))
                   (@PTree.Leaf (type * bool))) (@None (type * bool))
                (@PTree.Leaf (type * bool))))), PTree.empty type, tvoid,
    @PTree.Node global_spec
      (@PTree.Node global_spec
         (@PTree.Node global_spec
            (@PTree.Node global_spec (@PTree.Leaf global_spec)
               (@Some global_spec
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tptr tvoid), (3%positive, tuint),
                      (4%positive, tuint)](fun _ : environ => !!False) POST 
                      [tvoid](fun _ : environ => !!False))))
               (@PTree.Node global_spec (@PTree.Leaf global_spec)
                  (@Some global_spec
                     (Global_func
                        (WITH  p0 : val * list val, p1 : val PRE 
                         [(_Q, tptr t_struct_fifo), (_p, tptr t_struct_elem)]
                         (let (q0, contents) := p0 in
                          PROP  ()
                          LOCAL  (`(@eq val q0) (eval_id _Q);
                          `(@eq val p1) (eval_id _p))
                          SEP  (`(fifo contents q0); `((field_at_ Tsh t_struct_elem [_next]) p1))) POST 
                         [tvoid]
                         (let (q0, contents) := p0 in
                          `(fifo (contents ++ p1 :: @nil val) q0)))))
                  (@PTree.Leaf global_spec))) (@None global_spec)
            (@PTree.Node global_spec
               (@PTree.Node global_spec (@PTree.Leaf global_spec)
                  (@Some global_spec
                     (Global_func
                        (WITH _ : unit PRE  []
                         (fun _ : environ => @emp mpred Nveric Sveric) POST 
                         [tptr t_struct_fifo]`(fifo (@nil val)) retval)))
                  (@PTree.Leaf global_spec)) (@None global_spec)
               (@PTree.Node global_spec (@PTree.Leaf global_spec)
                  (@Some global_spec
                     (Global_func
                        (WITH  a : int, b : int PRE  [(_a, tint), (_b, tint)]
                         PROP  ()
                         LOCAL  (`(@eq val (Vint a)) (eval_id _a);
                         `(@eq val (Vint b)) (eval_id _b))  SEP() POST 
                         [tptr t_struct_elem]`(elemrep (Vint a, Vint b)) retval)))
                  (@PTree.Leaf global_spec)))) (@None global_spec)
         (@PTree.Node global_spec
            (@PTree.Node global_spec (@PTree.Leaf global_spec)
               (@Some global_spec
                  (Global_func
                     (WITH n : int PRE  [(1%positive, tint)]
                      PROP  (4 <= Int.signed n)
                      LOCAL  (`(@eq val (Vint n)) (eval_id 1%positive))
                      SEP() POST  [tptr tvoid]`(memory_block Tsh n) retval)))
               (@PTree.Leaf global_spec)) (@None global_spec)
            (@PTree.Leaf global_spec))) (@None global_spec)
      (@PTree.Node global_spec
         (@PTree.Node global_spec
            (@PTree.Node global_spec (@PTree.Leaf global_spec)
               (@Some global_spec
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tschar),
                      (2%positive, tint)](fun _ : environ => !!False) POST 
                      [tint](fun _ : environ => !!False))))
               (@PTree.Node global_spec (@PTree.Leaf global_spec)
                  (@Some global_spec
                     (Global_func
                        (WITH  q0 : val, contents : list val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         PROP  ()
                         LOCAL  (`(@eq val q0) (eval_id _Q))
                         SEP  (`(fifo contents q0)) POST  [tint]
                         (fun x0 : environ =>
                          local
                            (`(@eq val
                                 (if @isnil val contents
                                  then Vtrue
                                  else Vfalse)) retval) x0 &&
                          `(fifo contents q0) x0))))
                  (@PTree.Leaf global_spec))) (@None global_spec)
            (@PTree.Leaf global_spec)) (@None global_spec)
         (@PTree.Node global_spec
            (@PTree.Node global_spec (@PTree.Leaf global_spec)
               (@Some global_spec
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tint)]
                      PROP  ()
                      LOCAL ()
                      SEP 
                      (`(memory_block Tsh) (`force_int (eval_id 2%positive))
                         (eval_id 1%positive)) POST  [tvoid]
                      (fun _ : environ => @emp mpred Nveric Sveric))))
               (@PTree.Node global_spec (@PTree.Leaf global_spec)
                  (@Some global_spec
                     (Global_func
                        (WITH  p0 : val * list val, p1 : val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         (let (q0, contents) := p0 in
                          PROP  ()
                          LOCAL  (`(@eq val q0) (eval_id _Q))
                          SEP  (`(fifo (p1 :: contents) q0))) POST 
                         [tptr t_struct_elem]
                         (let (q0, contents) := p0 in
                          fun rho : environ =>
                          local (`(@eq val p1) retval) rho &&
                          `(fifo contents q0) rho * `(field_at_ Tsh t_struct_elem [_next]) retval rho))))
                  (@PTree.Leaf global_spec)))
            (@Some global_spec
               (Global_func
                  (WITH _ : unit PRE  [(1%positive, tdouble)]
                   (fun _ : environ => !!False) POST  [tdouble]
                   (fun _ : environ => !!False))))
            (@PTree.Node global_spec (@PTree.Leaf global_spec)
               (@None global_spec)
               (@PTree.Node global_spec (@PTree.Leaf global_spec)
                  (@Some global_spec
                     (Global_func
                        (WITH u : unit PRE  []main_pre prog u POST  [tint]
                         main_post prog u))) (@PTree.Leaf global_spec)))))) in
PROP  ()
LOCAL  (tc_environ Delta; `(@eq val q) (eval_id _Q);
`(@eq val p) (eval_id _p))  SEP  (`((field_at_ Tsh t_struct_elem [_next] p))) |-- `(field_at_ Tsh t_struct_elem [_next]) (eval_id _p)
.
Proof. intros Q p h t; ungather_entail.
entailer.
Qed.

Lemma goal_7 :
name _Q ->
name _p ->
name _h ->
name _t ->
EVAR
  (forall n : nat,
   EVAR
     (forall (sh : share) (q : val) (contents : list val) (p hd tl : val),
      let Delta :=
        @abbreviate tycontext
          (@PTree.Node (type * bool)
             (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                (@None (type * bool))
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))))) (@None (type * bool))
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, true))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool)))) (@None (type * bool))
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_fifo, true))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))) (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))))), PTree.empty type,
          tvoid,
          @PTree.Node global_spec
            (@PTree.Node global_spec
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tptr tvoid), (3%positive, tuint),
                            (4%positive, tuint)](fun _ : environ => !!False)
                            POST  [tvoid](fun _ : environ => !!False))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  p0 : val * list val, p1 : val PRE 
                               [(_Q, tptr t_struct_fifo),
                               (_p, tptr t_struct_elem)]
                               (let (q0, contents0) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q0) (eval_id _Q);
                                `(@eq val p1) (eval_id _p))
                                SEP  (`(fifo contents0 q0); `((field_at_ Tsh t_struct_elem [_next]) p1)))
                               POST  [tvoid]
                               (let (q0, contents0) := p0 in
                                `(fifo (contents0 ++ p1 :: @nil val) q0)))))
                        (@PTree.Leaf global_spec))) (@None global_spec)
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH _ : unit PRE  []
                               (fun _ : environ => @emp mpred Nveric Sveric)
                               POST  [tptr t_struct_fifo]
                               `(fifo (@nil val)) retval)))
                        (@PTree.Leaf global_spec)) (@None global_spec)
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  a : int, b : int PRE  [(_a, tint),
                               (_b, tint)]
                               PROP  ()
                               LOCAL  (`(@eq val (Vint a)) (eval_id _a);
                               `(@eq val (Vint b)) (eval_id _b))  SEP() POST 
                               [tptr t_struct_elem]`(elemrep (Vint a, Vint b)) retval)))
                        (@PTree.Leaf global_spec)))) (@None global_spec)
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH n0 : int PRE  [(1%positive, tint)]
                            PROP  (4 <= Int.signed n0)
                            LOCAL 
                            (`(@eq val (Vint n0)) (eval_id 1%positive))
                            SEP() POST  [tptr tvoid]
                            `(memory_block Tsh n0) retval)))
                     (@PTree.Leaf global_spec)) (@None global_spec)
                  (@PTree.Leaf global_spec))) (@None global_spec)
            (@PTree.Node global_spec
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tschar),
                            (2%positive, tint)](fun _ : environ => !!False)
                            POST  [tint](fun _ : environ => !!False))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  q0 : val, contents0 : list val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               PROP  ()
                               LOCAL  (`(@eq val q0) (eval_id _Q))
                               SEP  (`(fifo contents0 q0)) POST  [tint]
                               (fun x0 : environ =>
                                local
                                  (`(@eq val
                                       (if @isnil val contents0
                                        then Vtrue
                                        else Vfalse)) retval) x0 &&
                                `(fifo contents0 q0) x0))))
                        (@PTree.Leaf global_spec))) (@None global_spec)
                  (@PTree.Leaf global_spec)) (@None global_spec)
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tint)]
                            PROP  ()
                            LOCAL ()
                            SEP 
                            (`(memory_block Tsh)
                               (`force_int (eval_id 2%positive))
                               (eval_id 1%positive)) POST  [tvoid]
                            (fun _ : environ => @emp mpred Nveric Sveric))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  p0 : val * list val, p1 : val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               (let (q0, contents0) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q0) (eval_id _Q))
                                SEP  (`(fifo (p1 :: contents0) q0))) POST 
                               [tptr t_struct_elem]
                               (let (q0, contents0) := p0 in
                                fun rho : environ =>
                                local (`(@eq val p1) retval) rho &&
                                `(fifo contents0 q0) rho * `(field_at_ Tsh t_struct_elem [_next]) retval rho))))
                        (@PTree.Leaf global_spec)))
                  (@Some global_spec
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tdouble)]
                         (fun _ : environ => !!False) POST  [tdouble]
                         (fun _ : environ => !!False))))
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@None global_spec)
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH u : unit PRE  []main_pre prog u POST 
                               [tint]main_post prog u)))
                        (@PTree.Leaf global_spec)))))) in
      PROP  ()
      LOCAL  (tc_environ Delta; `(@eq val q) (eval_id _Q);
      `(@eq val p) (eval_id _p))
      SEP 
      (@numbd (LiftEnviron mpred) 0
         `(field_at Tsh t_struct_fifo [_head] q hd);
      @numbd (LiftEnviron mpred) 1
        `(field_at Tsh t_struct_fifo [_tail] q tl);
      @numbd (LiftEnviron mpred) 2
        `(if @isnil val contents
          then !!(hd = nullval) && @emp mpred Nveric Sveric
          else
           EX  prefix : list val,
           !!(contents = prefix ++ tl :: @nil val) &&
           (@links t_struct_elem _next QS Tsh prefix hd tl * field_at Tsh t_struct_elem [_next] nullval tl));
      `(@numbd (lift_T (Tarrow val (LiftEnviron mpred))) 3
          (field_at_ Tsh t_struct_elem [_next])) (eval_id _p))
      |-- `(@numbd (val -> mpred) n
              (field_at_ sh
                 (typeof
                    (Ederef (Etempvar _p (tptr t_struct_elem)) t_struct_elem))
                 [_next]))
            (eval_lvalue
               (Ederef (Etempvar _p (tptr t_struct_elem)) t_struct_elem)) *
          @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)))
. Proof. intros Q p h t; ungather_entail.
unfold sh,n; entailer; cancel.
Qed.

Lemma goal_8 :
name _Q ->
name _p ->
name _h ->
name _t ->
forall (q : val) (contents : list val) (p hd tl : val),
is_pointer_or_null hd ->
is_pointer_or_null tl ->
forall rho : environ,
let Delta :=
  (fun (A : Type) (x : A) => x) tycontext
    (PTree.Node
       (PTree.Node PTree.Leaf None
          (PTree.Node PTree.Leaf None
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, true))
                   PTree.Leaf) None PTree.Leaf))) None
       (PTree.Node
          (PTree.Node PTree.Leaf None
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, true))
                   PTree.Leaf) None PTree.Leaf)) None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, true))
                   PTree.Leaf) None PTree.Leaf) None
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, false))
                   PTree.Leaf) None PTree.Leaf))),
    var_types
      (PTree.Node
         (PTree.Node PTree.Leaf None
            (PTree.Node PTree.Leaf None
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, false))
                     PTree.Leaf) None PTree.Leaf))) None
         (PTree.Node
            (PTree.Node PTree.Leaf None
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, true))
                     PTree.Leaf) None PTree.Leaf)) None
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, true))
                     PTree.Leaf) None PTree.Leaf) None
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, false))
                     PTree.Leaf) None PTree.Leaf))), PTree.empty type, tvoid,
      PTree.Node
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tptr tvoid), (3%positive, tuint),
                        (4%positive, tuint)](fun _ : environ => !!False)
                        POST  [tvoid](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p1 : val PRE 
                           [(_Q, tptr t_struct_fifo),
                           (_p, tptr t_struct_elem)]
                           (let (q0, contents0) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q0) (eval_id _Q);
                            `(eq p1) (eval_id _p))
                            SEP  (`(fifo contents0 q0);
                            `(field_at_ Tsh t_struct_elem [_next] p1))) POST 
                           [tvoid]
                           (let (q0, contents0) := p0 in
                            `(fifo (contents0 ++ p1 :: nil) q0)))))
                    PTree.Leaf)) None
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH _ : unit PRE  [](fun _ : environ => emp)
                           POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                    PTree.Leaf) None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  a : int, b : int PRE  [(_a, tint),
                           (_b, tint)]
                           PROP  ()
                           LOCAL  (`(eq (Vint a)) (eval_id _a);
                           `(eq (Vint b)) (eval_id _b))  SEP() POST 
                           [tptr t_struct_elem]
                           `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
           None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH n : int PRE  [(1%positive, tint)]
                        PROP  (4 <= Int.signed n)
                        LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                        POST  [tptr tvoid]`(memory_block Tsh n) retval)))
                 PTree.Leaf) None PTree.Leaf)) None
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tschar),
                        (2%positive, tint)](fun _ : environ => !!False) POST 
                        [tint](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  q0 : val, contents0 : list val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           PROP  ()
                           LOCAL  (`(eq q0) (eval_id _Q))
                           SEP  (`(fifo contents0 q0)) POST  [tint]
                           (fun x0 : environ =>
                            local
                              (`(eq
                                   (if isnil contents0 then Vtrue else Vfalse))
                                 retval) x0 && `(fifo contents0 q0) x0))))
                    PTree.Leaf)) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tint)]
                        PROP  ()
                        LOCAL ()
                        SEP 
                        (`(memory_block Tsh)
                           (`force_int (eval_id 2%positive))
                           (eval_id 1%positive)) POST  [tvoid]
                        (fun _ : environ => emp))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p1 : val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           (let (q0, contents0) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q0) (eval_id _Q))
                            SEP  (`(fifo (p1 :: contents0) q0))) POST 
                           [tptr t_struct_elem]
                           (let (q0, contents0) := p0 in
                            fun rho0 : environ =>
                            local (`(eq p1) retval) rho0 &&
                            `(fifo contents0 q0) rho0 *
                            `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                    PTree.Leaf))
              (Some
                 (Global_func
                    (WITH _ : unit PRE  [(1%positive, tdouble)]
                     (fun _ : environ => !!False) POST  [tdouble]
                     (fun _ : environ => !!False))))
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH u : unit PRE  []main_pre prog u POST  [tint]
                           main_post prog u))) PTree.Leaf))))), tvoid,
    PTree.Node
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tptr tvoid), (3%positive, tuint),
                      (4%positive, tuint)](fun _ : environ => !!False) POST 
                      [tvoid](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p1 : val PRE 
                         [(_Q, tptr t_struct_fifo), (_p, tptr t_struct_elem)]
                         (let (q0, contents0) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q0) (eval_id _Q);
                          `(eq p1) (eval_id _p))
                          SEP  (`(fifo contents0 q0);
                          `(field_at_ Tsh t_struct_elem [_next] p1))) POST 
                         [tvoid]
                         (let (q0, contents0) := p0 in
                          `(fifo (contents0 ++ p1 :: nil) q0))))) PTree.Leaf))
            None
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [](fun _ : environ => emp) POST 
                         [tptr t_struct_fifo]`(fifo nil) retval))) PTree.Leaf)
               None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  a : int, b : int PRE  [(_a, tint), (_b, tint)]
                         PROP  ()
                         LOCAL  (`(eq (Vint a)) (eval_id _a);
                         `(eq (Vint b)) (eval_id _b))  SEP() POST 
                         [tptr t_struct_elem]
                         `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
         None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH n : int PRE  [(1%positive, tint)]
                      PROP  (4 <= Int.signed n)
                      LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                      POST  [tptr tvoid]`(memory_block Tsh n) retval)))
               PTree.Leaf) None PTree.Leaf)) None
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tschar),
                      (2%positive, tint)](fun _ : environ => !!False) POST 
                      [tint](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  q0 : val, contents0 : list val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         PROP  ()
                         LOCAL  (`(eq q0) (eval_id _Q))
                         SEP  (`(fifo contents0 q0)) POST  [tint]
                         (fun x0 : environ =>
                          local
                            (`(eq (if isnil contents0 then Vtrue else Vfalse))
                               retval) x0 && `(fifo contents0 q0) x0))))
                  PTree.Leaf)) None PTree.Leaf) None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tint)]
                      PROP  ()
                      LOCAL ()
                      SEP 
                      (`(memory_block Tsh) (`force_int (eval_id 2%positive))
                         (eval_id 1%positive)) POST  [tvoid]
                      (fun _ : environ => emp))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p1 : val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         (let (q0, contents0) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q0) (eval_id _Q))
                          SEP  (`(fifo (p1 :: contents0) q0))) POST 
                         [tptr t_struct_elem]
                         (let (q0, contents0) := p0 in
                          fun rho0 : environ =>
                          local (`(eq p1) retval) rho0 &&
                          `(fifo contents0 q0) rho0 *
                          `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                  PTree.Leaf))
            (Some
               (Global_func
                  (WITH _ : unit PRE  [(1%positive, tdouble)]
                   (fun _ : environ => !!False) POST  [tdouble]
                   (fun _ : environ => !!False))))
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH u : unit PRE  []main_pre prog u POST  [tint]
                         main_post prog u))) PTree.Leaf))))) in
tc_environ Delta rho ->
!!True &&
(!!(hd = eval_id _h rho /\ q = eval_id _Q rho /\ p = eval_id _p rho /\ True) &&
 (field_at Tsh t_struct_fifo [_head] hd q *
  (field_at Tsh t_struct_fifo [_tail] tl q *
   ((if isnil contents
     then !!(hd = nullval) && emp
     else
      EX  prefix : list val,
      !!(contents = prefix ++ tl :: nil) &&
      (links QS Tsh prefix hd tl *
       field_at Tsh t_struct_elem [_next] nullval tl)) *
    (field_at Tsh t_struct_elem [_next] (Vint (Int.repr 0))
       (force_ptr (eval_id _p rho)) * emp)))))
|-- !!True &&
    (!!((denote_tc_iszero (eval_id _h rho) \/
         is_true (Int.eq (Int.repr 0) Int.zero)) /\
        hd = eval_id _h rho /\
        q = eval_id _Q rho /\ p = eval_id _p rho /\ True) &&
     (field_at Tsh t_struct_fifo [_head] hd q *
      (field_at Tsh t_struct_fifo [_tail] tl q *
       ((if isnil contents
         then !!(hd = nullval) && emp
         else
          EX  prefix : list val,
          !!(contents = prefix ++ tl :: nil) &&
          (links QS Tsh prefix hd tl *
           field_at Tsh t_struct_elem [_next] nullval tl)) *
        (field_at Tsh t_struct_elem [_next] (Vint (Int.repr 0))
           (force_ptr (eval_id _p rho)) * emp))))).
Proof.  intros Q p h t; ungather_entail.
entailer!.
Qed.

Lemma goal_9 :
name _Q ->
name _p ->
name _h ->
name _t ->
EVAR
  (forall n : nat,
   EVAR
     (forall (sh : share) (q : val) (contents : list val) (p hd tl : val),
      let Delta :=
        @abbreviate tycontext
          (initialized _h
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@None (type * bool))
                   (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                      (@None (type * bool))
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Leaf (type * bool))
                            (@Some (type * bool) (tptr t_struct_elem, false))
                            (@PTree.Leaf (type * bool)))
                         (@None (type * bool)) (@PTree.Leaf (type * bool)))))
                (@None (type * bool))
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                      (@None (type * bool))
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Leaf (type * bool))
                            (@Some (type * bool) (tptr t_struct_elem, true))
                            (@PTree.Leaf (type * bool)))
                         (@None (type * bool)) (@PTree.Leaf (type * bool))))
                   (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Leaf (type * bool))
                            (@Some (type * bool) (tptr t_struct_fifo, true))
                            (@PTree.Leaf (type * bool)))
                         (@None (type * bool)) (@PTree.Leaf (type * bool)))
                      (@None (type * bool))
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Leaf (type * bool))
                            (@Some (type * bool) (tptr t_struct_elem, false))
                            (@PTree.Leaf (type * bool)))
                         (@None (type * bool)) (@PTree.Leaf (type * bool))))),
             PTree.empty type, tvoid,
             @PTree.Node global_spec
               (@PTree.Node global_spec
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                               (2%positive, tptr tvoid), (3%positive, tuint),
                               (4%positive, tuint)]
                               (fun _ : environ => !!False) POST  [tvoid]
                               (fun _ : environ => !!False))))
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH  p0 : val * list val, p1 : val PRE 
                                  [(_Q, tptr t_struct_fifo),
                                  (_p, tptr t_struct_elem)]
                                  (let (q0, contents0) := p0 in
                                   PROP  ()
                                   LOCAL  (`(@eq val q0) (eval_id _Q);
                                   `(@eq val p1) (eval_id _p))
                                   SEP  (`(fifo contents0 q0); `((field_at_ Tsh t_struct_elem [_next]) p1)))
                                  POST  [tvoid]
                                  (let (q0, contents0) := p0 in
                                   `(fifo (contents0 ++ p1 :: @nil val) q0)))))
                           (@PTree.Leaf global_spec))) (@None global_spec)
                     (@PTree.Node global_spec
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH _ : unit PRE  []
                                  (fun _ : environ =>
                                   @emp mpred Nveric Sveric) POST 
                                  [tptr t_struct_fifo]
                                  `(fifo (@nil val)) retval)))
                           (@PTree.Leaf global_spec)) (@None global_spec)
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH  a : int, b : int PRE  [(_a, tint),
                                  (_b, tint)]
                                  PROP  ()
                                  LOCAL  (`(@eq val (Vint a)) (eval_id _a);
                                  `(@eq val (Vint b)) (eval_id _b))  
                                  SEP() POST  [tptr t_struct_elem]
                                  `(elemrep (Vint a, Vint b)) retval)))
                           (@PTree.Leaf global_spec)))) (@None global_spec)
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH n0 : int PRE  [(1%positive, tint)]
                               PROP  (4 <= Int.signed n0)
                               LOCAL 
                               (`(@eq val (Vint n0)) (eval_id 1%positive))
                               SEP() POST  [tptr tvoid]
                               `(memory_block Tsh n0) retval)))
                        (@PTree.Leaf global_spec)) (@None global_spec)
                     (@PTree.Leaf global_spec))) (@None global_spec)
               (@PTree.Node global_spec
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH _ : unit PRE  [(1%positive, tptr tschar),
                               (2%positive, tint)]
                               (fun _ : environ => !!False) POST  [tint]
                               (fun _ : environ => !!False))))
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH  q0 : val, contents0 : list val PRE 
                                  [(_Q, tptr t_struct_fifo)]
                                  PROP  ()
                                  LOCAL  (`(@eq val q0) (eval_id _Q))
                                  SEP  (`(fifo contents0 q0)) POST  [tint]
                                  (fun x0 : environ =>
                                   local
                                     (`(@eq val
                                          (if @isnil val contents0
                                           then Vtrue
                                           else Vfalse)) retval) x0 &&
                                   `(fifo contents0 q0) x0))))
                           (@PTree.Leaf global_spec))) (@None global_spec)
                     (@PTree.Leaf global_spec)) (@None global_spec)
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                               (2%positive, tint)]
                               PROP  ()
                               LOCAL ()
                               SEP 
                               (`(memory_block Tsh)
                                  (`force_int (eval_id 2%positive))
                                  (eval_id 1%positive)) POST  [tvoid]
                               (fun _ : environ => @emp mpred Nveric Sveric))))
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH  p0 : val * list val, p1 : val PRE 
                                  [(_Q, tptr t_struct_fifo)]
                                  (let (q0, contents0) := p0 in
                                   PROP  ()
                                   LOCAL  (`(@eq val q0) (eval_id _Q))
                                   SEP  (`(fifo (p1 :: contents0) q0))) POST 
                                  [tptr t_struct_elem]
                                  (let (q0, contents0) := p0 in
                                   fun rho : environ =>
                                   local (`(@eq val p1) retval) rho &&
                                   `(fifo contents0 q0) rho *
                                   `(field_at_ Tsh t_struct_elem [_next]) retval rho))))
                           (@PTree.Leaf global_spec)))
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tdouble)]
                            (fun _ : environ => !!False) POST  [tdouble]
                            (fun _ : environ => !!False))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@None global_spec)
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH u : unit PRE  []main_pre prog u POST 
                                  [tint]main_post prog u)))
                           (@PTree.Leaf global_spec))))))) in
      PROP  ()
      LOCAL  (tc_environ Delta;
      `(typed_true
          (typeof
             (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)))
        (eval_expr
           (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint));
      `(@eq val hd) (eval_id _h); `(@eq val q) (eval_id _Q);
      `(@eq val p) (eval_id _p))
      SEP 
      (@numbd (LiftEnviron mpred) 0
         `(field_at Tsh t_struct_fifo [_head] hd q);
      @numbd (LiftEnviron mpred) 1
        `(field_at Tsh t_struct_fifo [_tail] tl q);
      @numbd (LiftEnviron mpred) 2
        `(if @isnil val contents
          then !!(hd = nullval) && @emp mpred Nveric Sveric
          else
           EX  prefix : list val,
           !!(contents = prefix ++ tl :: @nil val) &&
           (@links t_struct_elem _next QS Tsh prefix hd tl * field_at Tsh t_struct_elem [_next] nullval tl));
      `(@numbd (lift_T (Tarrow val (Tarrow val (LiftEnviron mpred)))) 3
          (field_at Tsh t_struct_elem [_next]))
         (`force_val
          (`(sem_cast (tptr tvoid) (tptr t_struct_elem))
           (`(force_val1 sem_cast_neutral) `(Vint (Int.repr 0)))))
              (`force_ptr (eval_id _p)))
      |-- `(@numbd (val -> mpred) n
              (field_at_ sh
                 (typeof
                    (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
                 [_head]))
            (eval_lvalue
               (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)) *
          @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)))
. Proof. intros Q p h t; ungather_entail.
unfold n, sh; entailer. cancel.
Qed.

Lemma goal_10 :name _Q ->
name _p ->
name _h ->
name _t ->
forall (q : val) (contents : list val) (p hd tl : val),
is_pointer_or_null hd ->
is_pointer_or_null tl ->
forall rho : environ,
let Delta :=
  (fun (A : Type) (x : A) => x) tycontext
    (PTree.Node
       (PTree.Node PTree.Leaf None
          (PTree.Node PTree.Leaf None
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, true))
                   PTree.Leaf) None PTree.Leaf))) None
       (PTree.Node
          (PTree.Node PTree.Leaf None
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, true))
                   PTree.Leaf) None PTree.Leaf)) None
          (PTree.Node
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, true))
                   PTree.Leaf) None PTree.Leaf) None
             (PTree.Node
                (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, false))
                   PTree.Leaf) None PTree.Leaf))),
    var_types
      (PTree.Node
         (PTree.Node PTree.Leaf None
            (PTree.Node PTree.Leaf None
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, false))
                     PTree.Leaf) None PTree.Leaf))) None
         (PTree.Node
            (PTree.Node PTree.Leaf None
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, true))
                     PTree.Leaf) None PTree.Leaf)) None
            (PTree.Node
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_fifo, true))
                     PTree.Leaf) None PTree.Leaf) None
               (PTree.Node
                  (PTree.Node PTree.Leaf (Some (tptr t_struct_elem, false))
                     PTree.Leaf) None PTree.Leaf))), PTree.empty type, tvoid,
      PTree.Node
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tptr tvoid), (3%positive, tuint),
                        (4%positive, tuint)](fun _ : environ => !!False)
                        POST  [tvoid](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p1 : val PRE 
                           [(_Q, tptr t_struct_fifo),
                           (_p, tptr t_struct_elem)]
                           (let (q0, contents0) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q0) (eval_id _Q);
                            `(eq p1) (eval_id _p))
                            SEP  (`(fifo contents0 q0);
                            `(field_at_ Tsh t_struct_elem [_next] p1))) POST 
                           [tvoid]
                           (let (q0, contents0) := p0 in
                            `(fifo (contents0 ++ p1 :: nil) q0)))))
                    PTree.Leaf)) None
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH _ : unit PRE  [](fun _ : environ => emp)
                           POST  [tptr t_struct_fifo]`(fifo nil) retval)))
                    PTree.Leaf) None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  a : int, b : int PRE  [(_a, tint),
                           (_b, tint)]
                           PROP  ()
                           LOCAL  (`(eq (Vint a)) (eval_id _a);
                           `(eq (Vint b)) (eval_id _b))  SEP() POST 
                           [tptr t_struct_elem]
                           `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
           None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH n : int PRE  [(1%positive, tint)]
                        PROP  (4 <= Int.signed n)
                        LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                        POST  [tptr tvoid]`(memory_block Tsh n) retval)))
                 PTree.Leaf) None PTree.Leaf)) None
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tschar),
                        (2%positive, tint)](fun _ : environ => !!False) POST 
                        [tint](fun _ : environ => !!False))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  q0 : val, contents0 : list val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           PROP  ()
                           LOCAL  (`(eq q0) (eval_id _Q))
                           SEP  (`(fifo contents0 q0)) POST  [tint]
                           (fun x0 : environ =>
                            local
                              (`(eq
                                   (if isnil contents0 then Vtrue else Vfalse))
                                 retval) x0 && `(fifo contents0 q0) x0))))
                    PTree.Leaf)) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                        (2%positive, tint)]
                        PROP  ()
                        LOCAL ()
                        SEP 
                        (`(memory_block Tsh)
                           (`force_int (eval_id 2%positive))
                           (eval_id 1%positive)) POST  [tvoid]
                        (fun _ : environ => emp))))
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  p0 : val * list val, p1 : val PRE 
                           [(_Q, tptr t_struct_fifo)]
                           (let (q0, contents0) := p0 in
                            PROP  ()
                            LOCAL  (`(eq q0) (eval_id _Q))
                            SEP  (`(fifo (p1 :: contents0) q0))) POST 
                           [tptr t_struct_elem]
                           (let (q0, contents0) := p0 in
                            fun rho0 : environ =>
                            local (`(eq p1) retval) rho0 &&
                            `(fifo contents0 q0) rho0 *
                            `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                    PTree.Leaf))
              (Some
                 (Global_func
                    (WITH _ : unit PRE  [(1%positive, tdouble)]
                     (fun _ : environ => !!False) POST  [tdouble]
                     (fun _ : environ => !!False))))
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH u : unit PRE  []main_pre prog u POST  [tint]
                           main_post prog u))) PTree.Leaf))))), tvoid,
    PTree.Node
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tptr tvoid), (3%positive, tuint),
                      (4%positive, tuint)](fun _ : environ => !!False) POST 
                      [tvoid](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p1 : val PRE 
                         [(_Q, tptr t_struct_fifo), (_p, tptr t_struct_elem)]
                         (let (q0, contents0) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q0) (eval_id _Q);
                          `(eq p1) (eval_id _p))
                          SEP  (`(fifo contents0 q0);
                          `(field_at_ Tsh t_struct_elem [_next] p1))) POST 
                         [tvoid]
                         (let (q0, contents0) := p0 in
                          `(fifo (contents0 ++ p1 :: nil) q0))))) PTree.Leaf))
            None
            (PTree.Node
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH _ : unit PRE  [](fun _ : environ => emp) POST 
                         [tptr t_struct_fifo]`(fifo nil) retval))) PTree.Leaf)
               None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  a : int, b : int PRE  [(_a, tint), (_b, tint)]
                         PROP  ()
                         LOCAL  (`(eq (Vint a)) (eval_id _a);
                         `(eq (Vint b)) (eval_id _b))  SEP() POST 
                         [tptr t_struct_elem]
                         `(elemrep (Vint a, Vint b)) retval))) PTree.Leaf)))
         None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH n : int PRE  [(1%positive, tint)]
                      PROP  (4 <= Int.signed n)
                      LOCAL  (`(eq (Vint n)) (eval_id 1%positive))  SEP()
                      POST  [tptr tvoid]`(memory_block Tsh n) retval)))
               PTree.Leaf) None PTree.Leaf)) None
      (PTree.Node
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tschar),
                      (2%positive, tint)](fun _ : environ => !!False) POST 
                      [tint](fun _ : environ => !!False))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  q0 : val, contents0 : list val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         PROP  ()
                         LOCAL  (`(eq q0) (eval_id _Q))
                         SEP  (`(fifo contents0 q0)) POST  [tint]
                         (fun x0 : environ =>
                          local
                            (`(eq (if isnil contents0 then Vtrue else Vfalse))
                               retval) x0 && `(fifo contents0 q0) x0))))
                  PTree.Leaf)) None PTree.Leaf) None
         (PTree.Node
            (PTree.Node PTree.Leaf
               (Some
                  (Global_func
                     (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                      (2%positive, tint)]
                      PROP  ()
                      LOCAL ()
                      SEP 
                      (`(memory_block Tsh) (`force_int (eval_id 2%positive))
                         (eval_id 1%positive)) POST  [tvoid]
                      (fun _ : environ => emp))))
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH  p0 : val * list val, p1 : val PRE 
                         [(_Q, tptr t_struct_fifo)]
                         (let (q0, contents0) := p0 in
                          PROP  ()
                          LOCAL  (`(eq q0) (eval_id _Q))
                          SEP  (`(fifo (p1 :: contents0) q0))) POST 
                         [tptr t_struct_elem]
                         (let (q0, contents0) := p0 in
                          fun rho0 : environ =>
                          local (`(eq p1) retval) rho0 &&
                          `(fifo contents0 q0) rho0 *
                          `(field_at_ Tsh t_struct_elem [_next]) retval rho0))))
                  PTree.Leaf))
            (Some
               (Global_func
                  (WITH _ : unit PRE  [(1%positive, tdouble)]
                   (fun _ : environ => !!False) POST  [tdouble]
                   (fun _ : environ => !!False))))
            (PTree.Node PTree.Leaf None
               (PTree.Node PTree.Leaf
                  (Some
                     (Global_func
                        (WITH u : unit PRE  []main_pre prog u POST  [tint]
                         main_post prog u))) PTree.Leaf))))) in
tc_environ
  (update_tycon Delta
     (Sassign
        (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)
           _tail (tptr t_struct_elem)) (Etempvar _p (tptr t_struct_elem))))
  rho ->
!!True &&
(!!(typed_true tint
      (force_val (sem_cmp_pp Ceq true2 (eval_id _h rho) (Vint (Int.repr 0)))) /\
    hd = eval_id _h rho /\ q = eval_id _Q rho /\ p = eval_id _p rho /\ True) &&
 (field_at Tsh
    (Tstruct _struct_fifo
       (Fcons _head
          (tptr
             (Tstruct _struct_elem
                (Fcons _a tint
                   (Fcons _b tint
                      (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                noattr))
          (Fcons _tail
             (tptr
                (Tstruct _struct_elem
                   (Fcons _a tint
                      (Fcons _b tint
                         (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                   noattr)) Fnil)) noattr) [_head]
    (force_val (sem_cast_neutral (eval_id _p rho)))
    (force_ptr (eval_id _Q rho)) *
  (field_at Tsh
     (Tstruct _struct_fifo
        (Fcons _head
           (tptr
              (Tstruct _struct_elem
                 (Fcons _a tint
                    (Fcons _b tint
                       (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                 noattr))
           (Fcons _tail
              (tptr
                 (Tstruct _struct_elem
                    (Fcons _a tint
                       (Fcons _b tint
                          (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                    noattr)) Fnil)) noattr) [_tail]
     (force_val (sem_cast_neutral (eval_id _p rho)))
     (force_ptr (eval_id _Q rho)) *
   ((if isnil contents
     then !!(hd = nullval) && emp
     else
      EX  prefix : list val,
      !!(contents = prefix ++ tl :: nil) &&
      (links QS Tsh prefix hd tl *
       field_at Tsh t_struct_elem [_next] nullval tl)) *
    (field_at Tsh t_struct_elem [_next] (Vint (Int.repr 0))
       (force_ptr (eval_id _p rho)) * emp)))))
|--
    (!!True && (!!True && (fifo (contents ++ p :: nil) q * emp))).
Proof. intros Q p' h t; ungather_entail.
entailer.
  destruct (@isnil val contents).
  + subst. unfold fifo. apply exp_right with (eval_id _p rho, eval_id _p rho).  
      simpl.
      destruct (isnil (eval_id _p rho ::nil)); [ congruence | ].
      normalize.
      apply exp_right with nil.
      simpl. rewrite links_nil_eq.
      entailer!.
  +  normalize.
      destruct prefix.
      - rewrite links_nil_eq. fold t_struct_elem.
         entailer.
         elim_hyps. destruct (eval_id _h rho); try contradiction; inv  H2.
      - rewrite links_cons_eq.
         normalize.   (* should this really be necessary here? *)
         entailer.
         elim_hyps.
         destruct (eval_id _h rho); try contradiction; inv  H2.
Qed.

Lemma goal_11 :
name _Q ->
name _p ->
name _h ->
name _t ->
forall (q : val) (contents : list val) (p hd tl : val),
contents = @nil val ->
let Delta :=
  @abbreviate tycontext
    (initialized _t
       (initialized _h
          (@PTree.Node (type * bool)
             (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                (@None (type * bool))
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))))) (@None (type * bool))
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, true))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool)))) (@None (type * bool))
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_fifo, true))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))) (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))))), PTree.empty type,
          tvoid,
          @PTree.Node global_spec
            (@PTree.Node global_spec
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tptr tvoid), (3%positive, tuint),
                            (4%positive, tuint)](fun _ : environ => !!False)
                            POST  [tvoid](fun _ : environ => !!False))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  p0 : val * list val, p1 : val PRE 
                               [(_Q, tptr t_struct_fifo),
                               (_p, tptr t_struct_elem)]
                               (let (q0, contents0) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q0) (eval_id _Q);
                                `(@eq val p1) (eval_id _p))
                                SEP  (`(fifo contents0 q0); `((field_at_ Tsh t_struct_elem [_next]) p1)))
                               POST  [tvoid]
                               (let (q0, contents0) := p0 in
                                `(fifo (contents0 ++ p1 :: @nil val) q0)))))
                        (@PTree.Leaf global_spec))) (@None global_spec)
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH _ : unit PRE  []
                               (fun _ : environ => @emp mpred Nveric Sveric)
                               POST  [tptr t_struct_fifo]
                               `(fifo (@nil val)) retval)))
                        (@PTree.Leaf global_spec)) (@None global_spec)
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  a : int, b : int PRE  [(_a, tint),
                               (_b, tint)]
                               PROP  ()
                               LOCAL  (`(@eq val (Vint a)) (eval_id _a);
                               `(@eq val (Vint b)) (eval_id _b))  SEP() POST 
                               [tptr t_struct_elem]`(elemrep (Vint a, Vint b)) retval)))
                        (@PTree.Leaf global_spec)))) (@None global_spec)
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH n : int PRE  [(1%positive, tint)]
                            PROP  (4 <= Int.signed n)
                            LOCAL  (`(@eq val (Vint n)) (eval_id 1%positive))
                              SEP() POST  [tptr tvoid]
                            `(memory_block Tsh n) retval)))
                     (@PTree.Leaf global_spec)) (@None global_spec)
                  (@PTree.Leaf global_spec))) (@None global_spec)
            (@PTree.Node global_spec
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tschar),
                            (2%positive, tint)](fun _ : environ => !!False)
                            POST  [tint](fun _ : environ => !!False))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  q0 : val, contents0 : list val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               PROP  ()
                               LOCAL  (`(@eq val q0) (eval_id _Q))
                               SEP  (`(fifo contents0 q0)) POST  [tint]
                               (fun x0 : environ =>
                                local
                                  (`(@eq val
                                       (if @isnil val contents0
                                        then Vtrue
                                        else Vfalse)) retval) x0 &&
                                `(fifo contents0 q0) x0))))
                        (@PTree.Leaf global_spec))) (@None global_spec)
                  (@PTree.Leaf global_spec)) (@None global_spec)
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tint)]
                            PROP  ()
                            LOCAL ()
                            SEP 
                            (`(memory_block Tsh)
                               (`force_int (eval_id 2%positive))
                               (eval_id 1%positive)) POST  [tvoid]
                            (fun _ : environ => @emp mpred Nveric Sveric))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  p0 : val * list val, p1 : val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               (let (q0, contents0) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q0) (eval_id _Q))
                                SEP  (`(fifo (p1 :: contents0) q0))) POST 
                               [tptr t_struct_elem]
                               (let (q0, contents0) := p0 in
                                fun rho : environ =>
                                local (`(@eq val p1) retval) rho &&
                                `(fifo contents0 q0) rho * `(field_at_ Tsh t_struct_elem [_next]) retval rho))))
                        (@PTree.Leaf global_spec)))
                  (@Some global_spec
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tdouble)]
                         (fun _ : environ => !!False) POST  [tdouble]
                         (fun _ : environ => !!False))))
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@None global_spec)
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH u : unit PRE  []main_pre prog u POST 
                               [tint]main_post prog u)))
                        (@PTree.Leaf global_spec)))))))) in
PROP  ()
LOCAL  (tc_environ Delta; `(@eq val tl) (eval_id _t);
`(typed_false
    (typeof
       (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)))
  (eval_expr
     (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint));
`(@eq val hd) (eval_id _h); `(@eq val q) (eval_id _Q);
`(@eq val p) (eval_id _p))
SEP  (`(field_at Tsh t_struct_fifo [_head] q hd);
`(field_at Tsh t_struct_fifo [_tail] q tl);
`(!!(hd = nullval) && @emp mpred Nveric Sveric);
`(field_at Tsh
    (Tstruct _struct_elem
       (Fcons _a tint
          (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
       noattr) [_next]) (`force_ptr (eval_id _p)) `(Vint (Int.repr 0)))
|-- @FF (environ -> mpred) (@LiftNatDed' mpred Nveric)
. Proof. intros Q p' h t; ungather_entail.
entailer.
Qed.

Lemma goal_12 :
name _Q ->
name _p ->
name _h ->
name _t ->
EVAR
  (forall n0 : nat,
   EVAR
     (forall (sh : share) (q : val) (contents : list val) (p hd tl : val),
      contents <> @nil val ->
      forall prefix : list val,
      contents = prefix ++ tl :: @nil val ->
      let Delta :=
        @abbreviate tycontext
          (initialized _t
             (initialized _h
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                      (@None (type * bool))
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@None (type * bool))
                         (@PTree.Node (type * bool)
                            (@PTree.Node (type * bool)
                               (@PTree.Leaf (type * bool))
                               (@Some (type * bool)
                                  (tptr t_struct_elem, false))
                               (@PTree.Leaf (type * bool)))
                            (@None (type * bool)) (@PTree.Leaf (type * bool)))))
                   (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@None (type * bool))
                         (@PTree.Node (type * bool)
                            (@PTree.Node (type * bool)
                               (@PTree.Leaf (type * bool))
                               (@Some (type * bool)
                                  (tptr t_struct_elem, true))
                               (@PTree.Leaf (type * bool)))
                            (@None (type * bool)) (@PTree.Leaf (type * bool))))
                      (@None (type * bool))
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Node (type * bool)
                               (@PTree.Leaf (type * bool))
                               (@Some (type * bool)
                                  (tptr t_struct_fifo, true))
                               (@PTree.Leaf (type * bool)))
                            (@None (type * bool)) (@PTree.Leaf (type * bool)))
                         (@None (type * bool))
                         (@PTree.Node (type * bool)
                            (@PTree.Node (type * bool)
                               (@PTree.Leaf (type * bool))
                               (@Some (type * bool)
                                  (tptr t_struct_elem, false))
                               (@PTree.Leaf (type * bool)))
                            (@None (type * bool)) (@PTree.Leaf (type * bool))))),
                PTree.empty type, tvoid,
                @PTree.Node global_spec
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH _ : unit PRE 
                                  [(1%positive, tptr tvoid),
                                  (2%positive, tptr tvoid),
                                  (3%positive, tuint), (4%positive, tuint)]
                                  (fun _ : environ => !!False) POST  [tvoid]
                                  (fun _ : environ => !!False))))
                           (@PTree.Node global_spec (@PTree.Leaf global_spec)
                              (@Some global_spec
                                 (Global_func
                                    (WITH  p0 : val * list val, p1 : val PRE 
                                     [(_Q, tptr t_struct_fifo),
                                     (_p, tptr t_struct_elem)]
                                     (let (q0, contents0) := p0 in
                                      PROP  ()
                                      LOCAL  (`(@eq val q0) (eval_id _Q);
                                      `(@eq val p1) (eval_id _p))
                                      SEP  (`(fifo contents0 q0);
                                      `((field_at_ Tsh t_struct_elem [_next]) p1))) POST  [tvoid]
                                     (let (q0, contents0) := p0 in
                                      `(fifo (contents0 ++ p1 :: @nil val) q0)))))
                              (@PTree.Leaf global_spec))) (@None global_spec)
                        (@PTree.Node global_spec
                           (@PTree.Node global_spec (@PTree.Leaf global_spec)
                              (@Some global_spec
                                 (Global_func
                                    (WITH _ : unit PRE  []
                                     (fun _ : environ =>
                                      @emp mpred Nveric Sveric) POST 
                                     [tptr t_struct_fifo]
                                     `(fifo (@nil val)) retval)))
                              (@PTree.Leaf global_spec)) (@None global_spec)
                           (@PTree.Node global_spec (@PTree.Leaf global_spec)
                              (@Some global_spec
                                 (Global_func
                                    (WITH  a : int, b : int PRE  [(_a, tint),
                                     (_b, tint)]
                                     PROP  ()
                                     LOCAL 
                                     (`(@eq val (Vint a)) (eval_id _a);
                                     `(@eq val (Vint b)) (eval_id _b))  
                                     SEP() POST  [tptr t_struct_elem]
                                     `(elemrep (Vint a, Vint b)) retval)))
                              (@PTree.Leaf global_spec))))
                     (@None global_spec)
                     (@PTree.Node global_spec
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH n1 : int PRE  [(1%positive, tint)]
                                  PROP  (4 <= Int.signed n1)
                                  LOCAL 
                                  (`(@eq val (Vint n1)) (eval_id 1%positive))
                                    SEP() POST  [tptr tvoid]
                                  `(memory_block Tsh n1) retval)))
                           (@PTree.Leaf global_spec)) (@None global_spec)
                        (@PTree.Leaf global_spec))) (@None global_spec)
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH _ : unit PRE 
                                  [(1%positive, tptr tschar),
                                  (2%positive, tint)]
                                  (fun _ : environ => !!False) POST  [tint]
                                  (fun _ : environ => !!False))))
                           (@PTree.Node global_spec (@PTree.Leaf global_spec)
                              (@Some global_spec
                                 (Global_func
                                    (WITH  q0 : val, contents0 : list val
                                     PRE  [(_Q, tptr t_struct_fifo)]
                                     PROP  ()
                                     LOCAL  (`(@eq val q0) (eval_id _Q))
                                     SEP  (`(fifo contents0 q0)) POST  [tint]
                                     (fun x0 : environ =>
                                      local
                                        (`(@eq val
                                             (if @isnil val contents0
                                              then Vtrue
                                              else Vfalse)) retval) x0 &&
                                      `(fifo contents0 q0) x0))))
                              (@PTree.Leaf global_spec))) (@None global_spec)
                        (@PTree.Leaf global_spec)) (@None global_spec)
                     (@PTree.Node global_spec
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@Some global_spec
                              (Global_func
                                 (WITH _ : unit PRE 
                                  [(1%positive, tptr tvoid),
                                  (2%positive, tint)]
                                  PROP  ()
                                  LOCAL ()
                                  SEP 
                                  (`(memory_block Tsh)
                                     (`force_int (eval_id 2%positive))
                                     (eval_id 1%positive)) POST  [tvoid]
                                  (fun _ : environ =>
                                   @emp mpred Nveric Sveric))))
                           (@PTree.Node global_spec (@PTree.Leaf global_spec)
                              (@Some global_spec
                                 (Global_func
                                    (WITH  p0 : val * list val, p1 : val PRE 
                                     [(_Q, tptr t_struct_fifo)]
                                     (let (q0, contents0) := p0 in
                                      PROP  ()
                                      LOCAL  (`(@eq val q0) (eval_id _Q))
                                      SEP  (`(fifo (p1 :: contents0) q0)))
                                     POST  [tptr t_struct_elem]
                                     (let (q0, contents0) := p0 in
                                      fun rho : environ =>
                                      local (`(@eq val p1) retval) rho &&
                                      `(fifo contents0 q0) rho *
                                      `(field_at_ Tsh t_struct_elem [_next]) retval rho))))
                              (@PTree.Leaf global_spec)))
                        (@Some global_spec
                           (Global_func
                              (WITH _ : unit PRE  [(1%positive, tdouble)]
                               (fun _ : environ => !!False) POST  [tdouble]
                               (fun _ : environ => !!False))))
                        (@PTree.Node global_spec (@PTree.Leaf global_spec)
                           (@None global_spec)
                           (@PTree.Node global_spec (@PTree.Leaf global_spec)
                              (@Some global_spec
                                 (Global_func
                                    (WITH u : unit PRE  []main_pre prog u
                                     POST  [tint]main_post prog u)))
                              (@PTree.Leaf global_spec)))))))) in
      PROP  ()
      LOCAL  (tc_environ Delta; `(@eq val tl) (eval_id _t);
      `(typed_false
          (typeof
             (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)))
        (eval_expr
           (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint));
      `(@eq val hd) (eval_id _h); `(@eq val q) (eval_id _Q);
      `(@eq val p) (eval_id _p))
      SEP 
      (@numbd (LiftEnviron mpred) 0
         `(@links t_struct_elem _next QS Tsh prefix hd tl);
      `(@numbd (lift_T (Tarrow val (Tarrow val (LiftEnviron mpred)))) 1
          (field_at Tsh
             (Tstruct _struct_elem
                (Fcons _a tint
                   (Fcons _b tint
                      (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                noattr) [_next]))
        (eval_lvalue
           (Ederef (Etempvar _t (tptr t_struct_elem)) t_struct_elem))
        (`force_val (`(sem_cast (typeof (Etempvar _p (tptr t_struct_elem)))
             (tptr t_struct_elem))
           (eval_expr (Etempvar _p (tptr t_struct_elem)))));
      @numbd (LiftEnviron mpred) 2
        `(field_at Tsh t_struct_fifo [_head] q hd);
      @numbd (LiftEnviron mpred) 3
        `(field_at Tsh t_struct_fifo [_tail] tl q);
      `(@numbd (lift_T (Tarrow val (Tarrow val (LiftEnviron mpred)))) 4
          (field_at Tsh
             (Tstruct _struct_elem
                (Fcons _a tint
                   (Fcons _b tint
                      (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                noattr) [_next]))
        `(Vint (Int.repr 0))  (`force_ptr (eval_id _p)))
      |-- `(@numbd (val -> mpred) n0
              (field_at_ sh
                 (typeof
                    (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
                 [_tail]))
            (eval_lvalue
               (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)) *
          @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)))
. Proof. intros Q p' h t; ungather_entail.
unfold sh,n0; entailer!; cancel.
Qed.

Lemma goal_13 :
name _Q ->
name _p ->
name _h ->
name _t ->
forall (q : val) (contents : list val) (p hd tl : val),
contents <> @nil val ->
forall prefix : list val,
contents = prefix ++ tl :: @nil val ->
let Delta :=
  @abbreviate tycontext
    (initialized _t
       (initialized _h
          (@PTree.Node (type * bool)
             (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                (@None (type * bool))
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))))) (@None (type * bool))
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                   (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, true))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool)))) (@None (type * bool))
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_fifo, true))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))) (@None (type * bool))
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_elem, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))))), PTree.empty type,
          tvoid,
          @PTree.Node global_spec
            (@PTree.Node global_spec
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tptr tvoid), (3%positive, tuint),
                            (4%positive, tuint)](fun _ : environ => !!False)
                            POST  [tvoid](fun _ : environ => !!False))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  p0 : val * list val, p1 : val PRE 
                               [(_Q, tptr t_struct_fifo),
                               (_p, tptr t_struct_elem)]
                               (let (q0, contents0) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q0) (eval_id _Q);
                                `(@eq val p1) (eval_id _p))
                                SEP  (`(fifo contents0 q0); `((field_at_ Tsh t_struct_elem [_next]) p1)))
                               POST  [tvoid]
                               (let (q0, contents0) := p0 in
                                `(fifo (contents0 ++ p1 :: @nil val) q0)))))
                        (@PTree.Leaf global_spec))) (@None global_spec)
                  (@PTree.Node global_spec
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH _ : unit PRE  []
                               (fun _ : environ => @emp mpred Nveric Sveric)
                               POST  [tptr t_struct_fifo]
                               `(fifo (@nil val)) retval)))
                        (@PTree.Leaf global_spec)) (@None global_spec)
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  a : int, b : int PRE  [(_a, tint),
                               (_b, tint)]
                               PROP  ()
                               LOCAL  (`(@eq val (Vint a)) (eval_id _a);
                               `(@eq val (Vint b)) (eval_id _b))  SEP() POST 
                               [tptr t_struct_elem]`(elemrep (Vint a, Vint b)) retval)))
                        (@PTree.Leaf global_spec)))) (@None global_spec)
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH n0 : int PRE  [(1%positive, tint)]
                            PROP  (4 <= Int.signed n0)
                            LOCAL 
                            (`(@eq val (Vint n0)) (eval_id 1%positive))
                            SEP() POST  [tptr tvoid]
                            `(memory_block Tsh n0) retval)))
                     (@PTree.Leaf global_spec)) (@None global_spec)
                  (@PTree.Leaf global_spec))) (@None global_spec)
            (@PTree.Node global_spec
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tschar),
                            (2%positive, tint)](fun _ : environ => !!False)
                            POST  [tint](fun _ : environ => !!False))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  q0 : val, contents0 : list val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               PROP  ()
                               LOCAL  (`(@eq val q0) (eval_id _Q))
                               SEP  (`(fifo contents0 q0)) POST  [tint]
                               (fun x0 : environ =>
                                local
                                  (`(@eq val
                                       (if @isnil val contents0
                                        then Vtrue
                                        else Vfalse)) retval) x0 &&
                                `(fifo contents0 q0) x0))))
                        (@PTree.Leaf global_spec))) (@None global_spec)
                  (@PTree.Leaf global_spec)) (@None global_spec)
               (@PTree.Node global_spec
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH _ : unit PRE  [(1%positive, tptr tvoid),
                            (2%positive, tint)]
                            PROP  ()
                            LOCAL ()
                            SEP 
                            (`(memory_block Tsh)
                               (`force_int (eval_id 2%positive))
                               (eval_id 1%positive)) POST  [tvoid]
                            (fun _ : environ => @emp mpred Nveric Sveric))))
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH  p0 : val * list val, p1 : val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               (let (q0, contents0) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q0) (eval_id _Q))
                                SEP  (`(fifo (p1 :: contents0) q0))) POST 
                               [tptr t_struct_elem]
                               (let (q0, contents0) := p0 in
                                fun rho : environ =>
                                local (`(@eq val p1) retval) rho &&
                                `(fifo contents0 q0) rho * `(field_at_ Tsh t_struct_elem [_next]) retval rho))))
                        (@PTree.Leaf global_spec)))
                  (@Some global_spec
                     (Global_func
                        (WITH _ : unit PRE  [(1%positive, tdouble)]
                         (fun _ : environ => !!False) POST  [tdouble]
                         (fun _ : environ => !!False))))
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@None global_spec)
                     (@PTree.Node global_spec (@PTree.Leaf global_spec)
                        (@Some global_spec
                           (Global_func
                              (WITH u : unit PRE  []main_pre prog u POST 
                               [tint]main_post prog u)))
                        (@PTree.Leaf global_spec)))))))) in
PROP  ()
LOCAL  (tc_environ Delta; `(@eq val tl) (eval_id _t);
`(typed_false
    (typeof
       (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)))
  (eval_expr
     (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint));
`(@eq val hd) (eval_id _h); `(@eq val q) (eval_id _Q);
`(@eq val p) (eval_id _p))
SEP  (`(@links t_struct_elem _next QS Tsh prefix hd tl);
`(field_at Tsh
    (Tstruct _struct_elem
       (Fcons _a tint
          (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
       noattr) [_next])
  (`force_val (`(sem_cast (typeof (Etempvar _p (tptr t_struct_elem)))
       (tptr t_struct_elem)) (eval_expr (Etempvar _p (tptr t_struct_elem)))))
  (eval_lvalue (Ederef (Etempvar _t (tptr t_struct_elem)) t_struct_elem));
`(field_at Tsh t_struct_fifo [_head] hd q);
`(field_at Tsh
    (Tstruct _struct_fifo
       (Fcons _head
          (tptr
             (Tstruct _struct_elem
                (Fcons _a tint
                   (Fcons _b tint
                      (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                noattr))
          (Fcons _tail
             (tptr
                (Tstruct _struct_elem
                   (Fcons _a tint
                      (Fcons _b tint
                         (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                   noattr)) Fnil)) noattr) [_tail])
  (`force_val (`(sem_cast (typeof (Etempvar _p (tptr t_struct_elem)))
       (tptr t_struct_elem)) (eval_expr (Etempvar _p (tptr t_struct_elem)))))
  (eval_lvalue (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo));
`(field_at Tsh
    (Tstruct _struct_elem
       (Fcons _a tint
          (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
       noattr) [_next])`(Vint (Int.repr 0)) (`force_ptr (eval_id _p)) )
|-- overridePost
      (PROP  ()  LOCAL ()  SEP  (`(fifo (contents ++ p :: @nil val) q)))
      (function_body_ret_assert tvoid `(fifo (contents ++ p :: @nil val) q))
      EK_normal (@None val)
. Proof. intros Q p' h t; ungather_entail.
     entailer.
     unfold fifo.
     apply exp_right with (h, p').
     destruct (isnil ((prefix ++ t :: nil) ++ p' :: nil)).
     destruct prefix; inv e.
     normalize.
     apply exp_right with (prefix ++ t :: nil).
     entailer.
     remember (field_at Tsh t_struct_elem [_next] nullval p') as A. (* prevent it from canceling! *)
     cancel. subst. 
     eapply derives_trans; [ | apply links_cons_right ].
     cancel.
Qed.


