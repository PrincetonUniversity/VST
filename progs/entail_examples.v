Load loadpath.
Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.queue.
Local Open Scope logic.

Instance QS: listspec t_struct_elem _next. 
Proof. eapply mk_listspec; reflexivity. Defined.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Definition link := field_mapsto Tsh t_struct_elem _next.
Definition link_ := field_mapsto_ Tsh t_struct_elem _next.

Definition fifo (contents: list val) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      field_mapsto Tsh t_struct_fifo _head p hd *
      field_mapsto Tsh t_struct_fifo _tail p tl *
      if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val, 
              !!(contents = prefix++tl::nil)
            &&  (links QS Tsh prefix hd tl * link tl nullval)).

Definition elemrep (rep: elemtype QS) (p: val) : mpred :=
  field_mapsto Tsh t_struct_elem _a p (Vint (fst rep)) * 
  (field_mapsto Tsh t_struct_elem _b p (Vint (snd rep)) *
   (field_mapsto_ Tsh t_struct_elem _next p)).


Lemma link_local_facts:
 forall x y, link x y |-- !! (isptr x /\ is_pointer_or_null y).
Proof.
 intros. unfold link.
 eapply derives_trans; [eapply field_mapsto_local_facts; reflexivity |].
 apply prop_derives.
 simpl. intuition.
Qed.

Hint Resolve link_local_facts : saturate_local.

Lemma link__local_facts:
 forall x, link_ x |-- !! isptr x.
Proof.
intros.
unfold link_.
eapply derives_trans; [eapply field_mapsto__local_facts; reflexivity | ].
apply prop_derives; intuition.
Qed.

Hint Resolve link__local_facts : saturate_local.

Lemma goal_1 :
name _Q ->
name _h ->
forall (q : val) (contents : list val) (hd tl : val),
let Delta :=
  @abbreviate tycontext
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
          (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
             (@None (type * bool))
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                      (@Some (type * bool) (tptr t_struct_fifo, true))
                      (@PTree.Leaf (type * bool))) (@None (type * bool))
                   (@PTree.Leaf (type * bool))) (@None (type * bool))
                (@PTree.Leaf (type * bool)))), PTree.empty type, tint,
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
                           (WITH  p0 : val * list val, p : val PRE 
                            [(_Q, tptr t_struct_fifo),
                            (_p, tptr t_struct_elem)]
                            (let (q0, contents0) := p0 in
                             PROP  ()
                             LOCAL  (`(@eq val q0) (eval_id _Q);
                             `(@eq val p) (eval_id _p))
                             SEP  (`(fifo contents0 q0); `(link_ p))) POST 
                            [tvoid]
                            (let (q0, contents0) := p0 in
                             `(fifo (contents0 ++ p :: @nil val) q0)))))
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
                            [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                           (WITH  p0 : val * list val, p : val PRE 
                            [(_Q, tptr t_struct_fifo)]
                            (let (q0, contents0) := p0 in
                             PROP  ()
                             LOCAL  (`(@eq val q0) (eval_id _Q))
                             SEP  (`(fifo (p :: contents0) q0))) POST 
                            [tptr t_struct_elem]
                            (let (q0, contents0) := p0 in
                             fun rho : environ =>
                             local (`(@eq val p) retval) rho &&
                             `(fifo contents0 q0) rho * `link_ retval rho))))
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
                            main_post prog u))) (@PTree.Leaf global_spec))))))) in
PROP  ()
LOCAL  (tc_environ Delta; `(@eq val hd) (eval_id _h);
`(@eq val q) (eval_id _Q))
SEP  (`(field_mapsto Tsh t_struct_fifo _head q hd);
`(field_mapsto Tsh t_struct_fifo _tail q tl);
`(if @isnil val contents
  then !!(hd = nullval) && @emp mpred Nveric Sveric
  else
   EX  prefix : list val,
   !!(contents = prefix ++ tl :: @nil val) &&
   (@links t_struct_elem _next QS Tsh prefix hd tl * link tl nullval)))
|-- local
      (tc_expropt Delta
         (@Some expr
            (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))
         (ret_type Delta)) &&
    `(function_body_ret_assert tint
        (local
           (`(@eq val (if @isnil val contents then Vtrue else Vfalse)) retval) &&
         `(fifo contents q)) EK_return)
      (cast_expropt
         (@Some expr
            (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))
         (ret_type Delta)) (@id environ)
. Proof. intros Q h. ungather_entail.
unfold fifo.
entailer.
apply exp_right with (h,tl).
entailer.
if_tac; entailer; elim_hyps; simpl; auto.
destruct prefix; entailer1.
Qed.

Lemma goal_2 :
name _Q ->
name _Q' ->
EVAR
  (forall Frame : list (environ -> mpred),
   let Delta :=
     @abbreviate tycontext
       (@PTree.Node (type * bool)
          (@PTree.Node (type * bool)
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr tvoid, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))) (@None (type * bool))
                   (@PTree.Leaf (type * bool))) (@None (type * bool))
                (@PTree.Leaf (type * bool))) (@None (type * bool))
             (@PTree.Leaf (type * bool))) (@None (type * bool))
          (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
             (@None (type * bool))
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                      (@Some (type * bool) (tptr t_struct_fifo, false))
                      (@PTree.Leaf (type * bool))) (@None (type * bool))
                   (@PTree.Leaf (type * bool))) (@None (type * bool))
                (@PTree.Leaf (type * bool)))), PTree.empty type,
       tptr t_struct_fifo,
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
                           (WITH  p0 : val * list val, p : val PRE 
                            [(_Q, tptr t_struct_fifo),
                            (_p, tptr t_struct_elem)]
                            (let (q, contents) := p0 in
                             PROP  ()
                             LOCAL  (`(@eq val q) (eval_id _Q);
                             `(@eq val p) (eval_id _p))
                             SEP  (`(fifo contents q); `(link_ p))) POST 
                            [tvoid]
                            (let (q, contents) := p0 in
                             `(fifo (contents ++ p :: @nil val) q)))))
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
                            [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                         (2%positive, tint)](fun _ : environ => !!False)
                         POST  [tint](fun _ : environ => !!False))))
                  (@PTree.Node global_spec (@PTree.Leaf global_spec)
                     (@Some global_spec
                        (Global_func
                           (WITH  q : val, contents : list val PRE 
                            [(_Q, tptr t_struct_fifo)]
                            PROP  ()
                            LOCAL  (`(@eq val q) (eval_id _Q))
                            SEP  (`(fifo contents q)) POST  [tint]
                            (fun x0 : environ =>
                             local
                               (`(@eq val
                                    (if @isnil val contents
                                     then Vtrue
                                     else Vfalse)) retval) x0 &&
                             `(fifo contents q) x0))))
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
                           (WITH  p0 : val * list val, p : val PRE 
                            [(_Q, tptr t_struct_fifo)]
                            (let (q, contents) := p0 in
                             PROP  ()
                             LOCAL  (`(@eq val q) (eval_id _Q))
                             SEP  (`(fifo (p :: contents) q))) POST 
                            [tptr t_struct_elem]
                            (let (q, contents) := p0 in
                             fun rho : environ =>
                             local (`(@eq val p) retval) rho &&
                             `(fifo contents q) rho * `link_ retval rho))))
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
   let witness := Int.repr 8 in
   PROP  ()  LOCAL  (tc_environ Delta)  SEP()
   |-- PROP  ()
       LOCAL 
       (tc_exprlist Delta
          (@snd (list ident) (list type)
             (@split ident type
                (@fst (list (ident * type)) type
                   ((1%positive, tint) :: @nil (positive * type), tptr tvoid))))
          (Econst_int (Int.repr 8) tuint :: @nil expr))
       (SEPx
          (`(PROP  (4 <= Int.signed witness)
             LOCAL  (`(@eq val (Vint witness)) (eval_id 1%positive))  SEP())
             (make_args'
                ((1%positive, tint) :: @nil (positive * type), tptr tvoid)
                (eval_exprlist
                   (@snd (list ident) (list type)
                      (@split ident type
                         (@fst (list (ident * type)) type
                            ((1%positive, tint) :: @nil (positive * type),
                            tptr tvoid))))
                   (Econst_int (Int.repr 8) tuint :: @nil expr))) :: Frame)))
. Proof. intros Q Q'; ungather_entail.
entailer1.
Qed.

Lemma goal_3 :
name _Q ->
name _Q' ->
let Delta :=
  @abbreviate tycontext
    (initialized _Q
       (initialized _Q'
          (@PTree.Node (type * bool)
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Leaf (type * bool))
                            (@Some (type * bool) (tptr tvoid, false))
                            (@PTree.Leaf (type * bool)))
                         (@None (type * bool)) (@PTree.Leaf (type * bool)))
                      (@None (type * bool)) (@PTree.Leaf (type * bool)))
                   (@None (type * bool)) (@PTree.Leaf (type * bool)))
                (@None (type * bool)) (@PTree.Leaf (type * bool)))
             (@None (type * bool))
             (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                (@None (type * bool))
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_fifo, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))) (@None (type * bool))
                   (@PTree.Leaf (type * bool)))), PTree.empty type,
          tptr t_struct_fifo,
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
                              (WITH  p0 : val * list val, p : val PRE 
                               [(_Q, tptr t_struct_fifo),
                               (_p, tptr t_struct_elem)]
                               (let (q, contents) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q) (eval_id _Q);
                                `(@eq val p) (eval_id _p))
                                SEP  (`(fifo contents q); `(link_ p))) POST 
                               [tvoid]
                               (let (q, contents) := p0 in
                                `(fifo (contents ++ p :: @nil val) q)))))
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
                               [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                              (WITH  q : val, contents : list val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               PROP  ()
                               LOCAL  (`(@eq val q) (eval_id _Q))
                               SEP  (`(fifo contents q)) POST  [tint]
                               (fun x0 : environ =>
                                local
                                  (`(@eq val
                                       (if @isnil val contents
                                        then Vtrue
                                        else Vfalse)) retval) x0 &&
                                `(fifo contents q) x0))))
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
                              (WITH  p0 : val * list val, p : val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               (let (q, contents) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q) (eval_id _Q))
                                SEP  (`(fifo (p :: contents) q))) POST 
                               [tptr t_struct_elem]
                               (let (q, contents) := p0 in
                                fun rho : environ =>
                                local (`(@eq val p) retval) rho &&
                                `(fifo contents q) rho * `link_ retval rho))))
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
LOCAL  (tc_environ Delta;
`(@eq val) (eval_id _Q)
  (eval_expr (Ecast (Etempvar _Q' (tptr tvoid)) (tptr t_struct_fifo))))
SEP  (`(memory_block Tsh (Int.repr 8)) (eval_id _Q'))
|-- PROP  ()  LOCAL ()  SEP  (`(memory_block Tsh (Int.repr 8)) (eval_id _Q))
. Proof. intros Q Q'; ungather_entail.
entailer.
Qed.

Lemma goal_4 :
name _Q ->
name _Q' ->
EVAR
  (forall n : nat,
   EVAR
     (forall sh : share,
      let Delta :=
        @abbreviate tycontext
          (initialized _Q
             (initialized _Q'
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Node (type * bool)
                               (@PTree.Node (type * bool)
                                  (@PTree.Leaf (type * bool))
                                  (@Some (type * bool) (tptr tvoid, false))
                                  (@PTree.Leaf (type * bool)))
                               (@None (type * bool))
                               (@PTree.Leaf (type * bool)))
                            (@None (type * bool)) (@PTree.Leaf (type * bool)))
                         (@None (type * bool)) (@PTree.Leaf (type * bool)))
                      (@None (type * bool)) (@PTree.Leaf (type * bool)))
                   (@None (type * bool))
                   (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                      (@None (type * bool))
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Node (type * bool)
                               (@PTree.Leaf (type * bool))
                               (@Some (type * bool)
                                  (tptr t_struct_fifo, false))
                               (@PTree.Leaf (type * bool)))
                            (@None (type * bool)) (@PTree.Leaf (type * bool)))
                         (@None (type * bool)) (@PTree.Leaf (type * bool)))),
                PTree.empty type, tptr t_struct_fifo,
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
                                    (WITH  p0 : val * list val, p : val PRE 
                                     [(_Q, tptr t_struct_fifo),
                                     (_p, tptr t_struct_elem)]
                                     (let (q, contents) := p0 in
                                      PROP  ()
                                      LOCAL  (`(@eq val q) (eval_id _Q);
                                      `(@eq val p) (eval_id _p))
                                      SEP  (`(fifo contents q); `(link_ p)))
                                     POST  [tvoid]
                                     (let (q, contents) := p0 in
                                      `(fifo (contents ++ p :: @nil val) q)))))
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
                                     `(elemrep (a, b)) retval)))
                              (@PTree.Leaf global_spec))))
                     (@None global_spec)
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
                                 (WITH _ : unit PRE 
                                  [(1%positive, tptr tschar),
                                  (2%positive, tint)]
                                  (fun _ : environ => !!False) POST  [tint]
                                  (fun _ : environ => !!False))))
                           (@PTree.Node global_spec (@PTree.Leaf global_spec)
                              (@Some global_spec
                                 (Global_func
                                    (WITH  q : val, contents : list val PRE 
                                     [(_Q, tptr t_struct_fifo)]
                                     PROP  ()
                                     LOCAL  (`(@eq val q) (eval_id _Q))
                                     SEP  (`(fifo contents q)) POST  [tint]
                                     (fun x0 : environ =>
                                      local
                                        (`(@eq val
                                             (if @isnil val contents
                                              then Vtrue
                                              else Vfalse)) retval) x0 &&
                                      `(fifo contents q) x0))))
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
                                    (WITH  p0 : val * list val, p : val PRE 
                                     [(_Q, tptr t_struct_fifo)]
                                     (let (q, contents) := p0 in
                                      PROP  ()
                                      LOCAL  (`(@eq val q) (eval_id _Q))
                                      SEP  (`(fifo (p :: contents) q))) POST 
                                     [tptr t_struct_elem]
                                     (let (q, contents) := p0 in
                                      fun rho : environ =>
                                      local (`(@eq val p) retval) rho &&
                                      `(fifo contents q) rho *
                                      `link_ retval rho))))
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
      LOCAL  (tc_environ Delta)
      SEP 
      (`(@numbd (lift_T (Tarrow val (Tarrow val (LiftEnviron mpred)))) 0
           (field_mapsto Tsh
              (Tstruct _struct_fifo
                 (Fcons _head
                    (tptr
                       (Tstruct _struct_elem
                          (Fcons _a tint
                             (Fcons _b tint
                                (Fcons _next (Tcomp_ptr _struct_elem noattr)
                                   Fnil))) noattr))
                    (Fcons _tail
                       (tptr
                          (Tstruct _struct_elem
                             (Fcons _a tint
                                (Fcons _b tint
                                   (Fcons _next
                                      (Tcomp_ptr _struct_elem noattr) Fnil)))
                             noattr)) Fnil)) noattr) _head))
         (eval_lvalue
            (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
         (`(eval_cast
              (typeof (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
              (tptr t_struct_elem))
            (eval_expr (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))));
      `(@numbd (lift_T (Tarrow val (LiftEnviron mpred))) 1
          (field_mapsto_ Tsh t_struct_fifo _tail)) (eval_id _Q))
      |-- `(@numbd (val -> mpred) n
              (field_mapsto_ sh
                 (typeof
                    (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
                 _tail))
            (eval_lvalue
               (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)) *
          @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)))
. Proof. intros Q Q'; ungather_entail.
unfold sh,n; entailer; cancel.
Qed.

Lemma goal_5 :
name _Q ->
name _Q' ->
let Delta :=
  @abbreviate tycontext
    (initialized _Q
       (initialized _Q'
          (@PTree.Node (type * bool)
             (@PTree.Node (type * bool)
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool)
                         (@PTree.Node (type * bool)
                            (@PTree.Leaf (type * bool))
                            (@Some (type * bool) (tptr tvoid, false))
                            (@PTree.Leaf (type * bool)))
                         (@None (type * bool)) (@PTree.Leaf (type * bool)))
                      (@None (type * bool)) (@PTree.Leaf (type * bool)))
                   (@None (type * bool)) (@PTree.Leaf (type * bool)))
                (@None (type * bool)) (@PTree.Leaf (type * bool)))
             (@None (type * bool))
             (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                (@None (type * bool))
                (@PTree.Node (type * bool)
                   (@PTree.Node (type * bool)
                      (@PTree.Node (type * bool) (@PTree.Leaf (type * bool))
                         (@Some (type * bool) (tptr t_struct_fifo, false))
                         (@PTree.Leaf (type * bool))) (@None (type * bool))
                      (@PTree.Leaf (type * bool))) (@None (type * bool))
                   (@PTree.Leaf (type * bool)))), PTree.empty type,
          tptr t_struct_fifo,
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
                              (WITH  p0 : val * list val, p : val PRE 
                               [(_Q, tptr t_struct_fifo),
                               (_p, tptr t_struct_elem)]
                               (let (q, contents) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q) (eval_id _Q);
                                `(@eq val p) (eval_id _p))
                                SEP  (`(fifo contents q); `(link_ p))) POST 
                               [tvoid]
                               (let (q, contents) := p0 in
                                `(fifo (contents ++ p :: @nil val) q)))))
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
                               [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                              (WITH  q : val, contents : list val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               PROP  ()
                               LOCAL  (`(@eq val q) (eval_id _Q))
                               SEP  (`(fifo contents q)) POST  [tint]
                               (fun x0 : environ =>
                                local
                                  (`(@eq val
                                       (if @isnil val contents
                                        then Vtrue
                                        else Vfalse)) retval) x0 &&
                                `(fifo contents q) x0))))
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
                              (WITH  p0 : val * list val, p : val PRE 
                               [(_Q, tptr t_struct_fifo)]
                               (let (q, contents) := p0 in
                                PROP  ()
                                LOCAL  (`(@eq val q) (eval_id _Q))
                                SEP  (`(fifo (p :: contents) q))) POST 
                               [tptr t_struct_elem]
                               (let (q, contents) := p0 in
                                fun rho : environ =>
                                local (`(@eq val p) retval) rho &&
                                `(fifo contents q) rho * `link_ retval rho))))
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
LOCAL  (tc_environ Delta)
SEP 
(`(field_mapsto Tsh
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
                    noattr)) Fnil)) noattr) _head)
   (eval_lvalue (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
   (`(eval_cast (typeof (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (tptr t_struct_elem))
      (eval_expr (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))));
`(field_mapsto Tsh
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
                   noattr)) Fnil)) noattr) _tail)
  (eval_lvalue (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
  (`(eval_cast (typeof (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
       (tptr t_struct_elem))
     (eval_expr (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))
|-- local
      (tc_expropt Delta (@Some expr (Etempvar _Q (tptr t_struct_fifo)))
         (ret_type Delta)) &&
    `(function_body_ret_assert (tptr t_struct_fifo)
        (`(fifo (@nil val)) retval) EK_return)
      (cast_expropt (@Some expr (Etempvar _Q (tptr t_struct_fifo)))
         (ret_type Delta)) (@id environ)
. Proof. intros Q Q'; ungather_entail.
  unfold fifo.
  entailer.
  apply exp_right with (nullval,nullval).
  if_tac; [ | congruence].
 entailer.
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
                          SEP  (`(fifo contents q0); `(link_ p1))) POST 
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
                         [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                          `(fifo contents q0) rho * `link_ retval rho))))
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
`(@eq val p) (eval_id _p))  SEP  (`(link_ p)) |-- `link_ (eval_id _p)
. Proof. intros Q p h t; ungather_entail.
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
                                SEP  (`(fifo contents0 q0); `(link_ p1)))
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
                               [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                                `(fifo contents0 q0) rho * `link_ retval rho))))
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
         `(field_mapsto Tsh t_struct_fifo _head q hd);
      @numbd (LiftEnviron mpred) 1
        `(field_mapsto Tsh t_struct_fifo _tail q tl);
      @numbd (LiftEnviron mpred) 2
        `(if @isnil val contents
          then !!(hd = nullval) && @emp mpred Nveric Sveric
          else
           EX  prefix : list val,
           !!(contents = prefix ++ tl :: @nil val) &&
           (@links t_struct_elem _next QS Tsh prefix hd tl * link tl nullval));
      `(@numbd (lift_T (Tarrow val (LiftEnviron mpred))) 3
          (field_mapsto_ Tsh t_struct_elem _next)) (eval_id _p))
      |-- `(@numbd (val -> mpred) n
              (field_mapsto_ sh
                 (typeof
                    (Ederef (Etempvar _p (tptr t_struct_elem)) t_struct_elem))
                 _next))
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
let Delta :=
  @abbreviate tycontext
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
                   (@PTree.Leaf (type * bool))))), PTree.empty type, tvoid,
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
                             SEP  (`(fifo contents0 q0); `(link_ p1))) POST 
                            [tvoid]
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
                            [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                             `(fifo contents0 q0) rho * `link_ retval rho))))
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
                            main_post prog u))) (@PTree.Leaf global_spec))))))) in
PROP  ()
LOCAL  (tc_environ Delta; `(@eq val hd) (eval_id _h);
`(@eq val q) (eval_id _Q); `(@eq val p) (eval_id _p))
SEP  (`(field_mapsto Tsh t_struct_fifo _head q hd);
`(field_mapsto Tsh t_struct_fifo _tail q tl);
`(if @isnil val contents
  then !!(hd = nullval) && @emp mpred Nveric Sveric
  else
   EX  prefix : list val,
   !!(contents = prefix ++ tl :: @nil val) &&
   (@links t_struct_elem _next QS Tsh prefix hd tl * link tl nullval));
`(field_mapsto Tsh
    (Tstruct _struct_elem
       (Fcons _a tint
          (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
       noattr) _next) (`force_ptr (eval_id _p)) `(Vint (Int.repr 0)))
|-- PROP  ()
    LOCAL 
    (tc_expr Delta
       (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint);
    `(@eq val hd) (eval_id _h); `(@eq val q) (eval_id _Q);
    `(@eq val p) (eval_id _p))
    SEP  (`(field_mapsto Tsh t_struct_fifo _head q hd);
    `(field_mapsto Tsh t_struct_fifo _tail q tl);
    `(if @isnil val contents
      then !!(hd = nullval) && @emp mpred Nveric Sveric
      else
       EX  prefix : list val,
       !!(contents = prefix ++ tl :: @nil val) &&
       (@links t_struct_elem _next QS Tsh prefix hd tl * link tl nullval));
    `(field_mapsto Tsh
        (Tstruct _struct_elem
           (Fcons _a tint
              (Fcons _b tint
                 (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil))) noattr)
        _next) (`force_ptr (eval_id _p)) `(Vint (Int.repr 0)))
. Proof.  intros Q p h t; ungather_entail.
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
                                   SEP  (`(fifo contents0 q0); `(link_ p1)))
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
                                  `(elemrep (a, b)) retval)))
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
                                   `link_ retval rho))))
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
         `(field_mapsto Tsh t_struct_fifo _head q hd);
      @numbd (LiftEnviron mpred) 1
        `(field_mapsto Tsh t_struct_fifo _tail q tl);
      @numbd (LiftEnviron mpred) 2
        `(if @isnil val contents
          then !!(hd = nullval) && @emp mpred Nveric Sveric
          else
           EX  prefix : list val,
           !!(contents = prefix ++ tl :: @nil val) &&
           (@links t_struct_elem _next QS Tsh prefix hd tl * link tl nullval));
      `(@numbd (lift_T (Tarrow val (Tarrow val (LiftEnviron mpred)))) 3
          (field_mapsto Tsh
             (Tstruct _struct_elem
                (Fcons _a tint
                   (Fcons _b tint
                      (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                noattr) _next)) (`force_ptr (eval_id _p))
        `(Vint (Int.repr 0)))
      |-- `(@numbd (val -> mpred) n
              (field_mapsto_ sh
                 (typeof
                    (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
                 _head))
            (eval_lvalue
               (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)) *
          @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)))
. Proof. intros Q p h t; ungather_entail.
unfold n,sh. entailer. cancel.
Qed.

Lemma goal_10 :
name _Q ->
name _p ->
name _h ->
name _t ->
forall (q : val) (contents : list val) (p hd tl : val),
let Delta :=
  @abbreviate tycontext
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
                   (@PTree.Leaf (type * bool))))), PTree.empty type, tvoid,
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
                             SEP  (`(fifo contents0 q0); `(link_ p1))) POST 
                            [tvoid]
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
                            [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                             `(fifo contents0 q0) rho * `link_ retval rho))))
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
                            main_post prog u))) (@PTree.Leaf global_spec))))))) in
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
(`(field_mapsto Tsh
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
                    noattr)) Fnil)) noattr) _head)
   (eval_lvalue (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
   (`(eval_cast (typeof (Etempvar _p (tptr t_struct_elem)))
        (tptr t_struct_elem)) (eval_expr (Etempvar _p (tptr t_struct_elem))));
`(field_mapsto Tsh
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
                   noattr)) Fnil)) noattr) _tail)
  (eval_lvalue (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
  (`(eval_cast (typeof (Etempvar _p (tptr t_struct_elem)))
       (tptr t_struct_elem)) (eval_expr (Etempvar _p (tptr t_struct_elem))));
`(if @isnil val contents
  then !!(hd = nullval) && @emp mpred Nveric Sveric
  else
   EX  prefix : list val,
   !!(contents = prefix ++ tl :: @nil val) &&
   (@links t_struct_elem _next QS Tsh prefix hd tl * link tl nullval));
`(field_mapsto Tsh
    (Tstruct _struct_elem
       (Fcons _a tint
          (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
       noattr) _next) (`force_ptr (eval_id _p)) `(Vint (Int.repr 0)))
|-- overridePost
      (PROP  ()  LOCAL ()  SEP  (`(fifo (contents ++ p :: @nil val) q)))
      (function_body_ret_assert tvoid `(fifo (contents ++ p :: @nil val) q))
      EK_normal (@None val)
. Proof. intros Q p' h t; ungather_entail.
entailer.
  destruct (@isnil val contents).
  + subst. unfold fifo. apply exp_right with (p',p').  
      simpl.
      destruct (isnil (p' ::nil)); [ congruence | ].
      normalize.
      apply exp_right with nil.
      simpl. rewrite links_nil_eq.
      entailer!.
  + unfold link.
      normalize.
      destruct prefix.
      - rewrite links_nil_eq.
         entailer.
         elim_hyps. inv H0.
      - rewrite links_cons_eq.
         normalize.   (* should this really be necessary here? *)
         entailer.
         elim_hyps. inv H0.
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
                                SEP  (`(fifo contents0 q0); `(link_ p1)))
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
                               [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                                `(fifo contents0 q0) rho * `link_ retval rho))))
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
SEP  (`(field_mapsto Tsh t_struct_fifo _head q hd);
`(field_mapsto Tsh t_struct_fifo _tail q tl);
`(!!(hd = nullval) && @emp mpred Nveric Sveric);
`(field_mapsto Tsh
    (Tstruct _struct_elem
       (Fcons _a tint
          (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
       noattr) _next) (`force_ptr (eval_id _p)) `(Vint (Int.repr 0)))
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
                                      `(link_ p1))) POST  [tvoid]
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
                                     `(elemrep (a, b)) retval)))
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
                                      `link_ retval rho))))
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
          (field_mapsto Tsh
             (Tstruct _struct_elem
                (Fcons _a tint
                   (Fcons _b tint
                      (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                noattr) _next))
        (eval_lvalue
           (Ederef (Etempvar _t (tptr t_struct_elem)) t_struct_elem))
        (`(eval_cast (typeof (Etempvar _p (tptr t_struct_elem)))
             (tptr t_struct_elem))
           (eval_expr (Etempvar _p (tptr t_struct_elem))));
      @numbd (LiftEnviron mpred) 2
        `(field_mapsto Tsh t_struct_fifo _head q hd);
      @numbd (LiftEnviron mpred) 3
        `(field_mapsto Tsh t_struct_fifo _tail q tl);
      `(@numbd (lift_T (Tarrow val (Tarrow val (LiftEnviron mpred)))) 4
          (field_mapsto Tsh
             (Tstruct _struct_elem
                (Fcons _a tint
                   (Fcons _b tint
                      (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                noattr) _next)) (`force_ptr (eval_id _p))
        `(Vint (Int.repr 0)))
      |-- `(@numbd (val -> mpred) n0
              (field_mapsto_ sh
                 (typeof
                    (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
                 _tail))
            (eval_lvalue
               (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)) *
          @TT (LiftEnviron mpred) (@LiftNatDed' mpred Nveric)))
. Proof. intros Q p' h t; ungather_entail.
unfold sh,n0; entailer; cancel.
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
                                SEP  (`(fifo contents0 q0); `(link_ p1)))
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
                               [tptr t_struct_elem]`(elemrep (a, b)) retval)))
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
                                `(fifo contents0 q0) rho * `link_ retval rho))))
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
`(field_mapsto Tsh
    (Tstruct _struct_elem
       (Fcons _a tint
          (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
       noattr) _next)
  (eval_lvalue (Ederef (Etempvar _t (tptr t_struct_elem)) t_struct_elem))
  (`(eval_cast (typeof (Etempvar _p (tptr t_struct_elem)))
       (tptr t_struct_elem)) (eval_expr (Etempvar _p (tptr t_struct_elem))));
`(field_mapsto Tsh t_struct_fifo _head q hd);
`(field_mapsto Tsh
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
                   noattr)) Fnil)) noattr) _tail)
  (eval_lvalue (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo))
  (`(eval_cast (typeof (Etempvar _p (tptr t_struct_elem)))
       (tptr t_struct_elem)) (eval_expr (Etempvar _p (tptr t_struct_elem))));
`(field_mapsto Tsh
    (Tstruct _struct_elem
       (Fcons _a tint
          (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
       noattr) _next) (`force_ptr (eval_id _p)) `(Vint (Int.repr 0)))
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
     remember (link p' nullval) as A. (* prevent it from canceling! *)
     cancel. subst. 
     eapply derives_trans; [ | apply links_cons_right ].
     cancel.
Qed.


