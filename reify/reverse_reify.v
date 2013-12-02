Require Import floyd.proofauto.
Require Import types.
Require Import functions.
Require Import progs.reverse.
Require Import progs.list_dt.
Require Import sep.
Local Open Scope logic.

Instance LS: listspec t_struct_list _tail.
Proof. eapply mk_listspec; reflexivity. Defined.

Definition sum_int := fold_right Int.add Int.zero.


(*types we need that aren't defined yet... 
this is just an example, we don't really need this one*)
Definition LS_type := cons (no_eqb_type (listspec t_struct_list _tail)) nil.

Module uk_types <: unknown_types.
Definition unknown_types := LS_type.
End uk_types.

Module funcs := funcs uk_types.
Import funcs.
Import all_types.

Definition list_spec_tv := Expr.tvType (length our_types).
Compute (elemtype LS).


(*Separation logic predicate just for this file *)
Definition lseg_signature :=
Sep.PSig all_types (cons share_tv
                   (cons list_int_tv (cons val_tv (cons val_tv nil))))
(lseg LS).

Definition predicates := lseg_signature :: nil.
Check predicates.
Definition lseg_p := length sep_predicates.

(*Functions just for this file. These three represent variables
  that are above the line. *)
Definition more_funcs rho contents sh :=
make_environ_signature rho ::
make_list_int_signature contents ::
make_share_signature sh :: nil.

Definition rho_fv := length functions.
Definition contents_fv := S rho_fv.
Definition sh_fv := S contents_fv.

Definition rho_f := nullary_func rho_fv.
Definition contents_f := nullary_func contents_fv.
Definition sh_f := nullary_func sh_fv.

(*Some constants we will use *)

Definition true_c := prop_const True.
Definition zero_c := val_const (Vint (Int.repr 0)).
Definition _p_c := id_const _p.
Definition _t_c := id_const _t.
Definition _s_c := id_const _s.
Definition nullval_c := val_const nullval.


(*Put it together with functions and stars *)
Definition eval_id_p := eval_id_func _p_c rho_f.
Definition eval_id_t := eval_id_func _t_c rho_f.
Definition eval_id_s := eval_id_func _s_c rho_f.
Definition eq1 := val_eq eval_id_t eval_id_p.
Definition eq2 := val_eq eval_id_s zero_c.


Definition pure := and_func eq1 (and_func eq2 true_c).
Definition our_inj e := Sep.Star (Sep.Inj e) (Sep.Emp all_types).
Definition TT_s := our_inj true_c.

Definition lseg_func := @Sep.Func all_types lseg_p
(sh_f :: contents_f :: eval_id_p :: nullval_c :: nil).

Definition left_side :=
Sep.Star TT_s 
(Sep.Star (our_inj pure)
(Sep.Star lseg_func (Sep.Emp all_types))).

Definition Delta :=
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
      var_types
        (PTree.Node
           (PTree.Node
              (PTree.Node
                 (PTree.Node
                    (PTree.Node PTree.Leaf (Some (tptr t_struct_list, false))
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
        var_types
          (PTree.Node
             (PTree.Node
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf
                         (Some (tptr t_struct_list, false)) PTree.Leaf) None
                      PTree.Leaf) None PTree.Leaf) None
                (PTree.Node PTree.Leaf None
                   (PTree.Node PTree.Leaf (Some (tptr t_struct_list, true))
                      PTree.Leaf))) None
             (PTree.Node
                (PTree.Node
                   (PTree.Node
                      (PTree.Node PTree.Leaf (Some (tint, false)) PTree.Leaf)
                      None PTree.Leaf) None PTree.Leaf) None
                (PTree.Node PTree.Leaf None
                   (PTree.Node PTree.Leaf (Some (tint, false)) PTree.Leaf))),
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
                                `(lseg LS sh0 contents0) 
                                  (eval_id _p) `nullval) POST  [tint]
                               (let (_, contents0) := x in
                                local
                                  (`(eq (Vint (sum_int contents0))) retval)))))
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
                              (WITH  sh0 : share, contents0 : 
                               list int PRE  [(_p, tptr t_struct_list)]
                               (fun x0 : environ =>
                                !!writable_share sh0 &&
                                `(lseg LS sh0 contents0) 
                                  (eval_id _p) `nullval x0) POST 
                               [tptr t_struct_list]
                               `(lseg LS sh0 (rev contents0)) retval `nullval)))
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
                              (WITH u : unit PRE  []
                               main_pre prog u POST  [tint]
                               main_post prog u))) PTree.Leaf) None
                     PTree.Leaf)))), tint,
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
                              `(lseg LS sh0 contents0) (eval_id _p) `nullval)
                             POST  [tint]
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
                            (WITH  sh0 : share, contents0 : 
                             list int PRE  [(_p, tptr t_struct_list)]
                             (fun x0 : environ =>
                              !!writable_share sh0 &&
                              `(lseg LS sh0 contents0) 
                                (eval_id _p) `nullval x0) POST 
                             [tptr t_struct_list]
                             `(lseg LS sh0 (rev contents0)) retval `nullval)))
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
                   PTree.Leaf)))), tint,
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
                 PTree.Leaf) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH x : share * list int PRE 
                           [(_p, tptr t_struct_list)]
                           (let (sh0, contents0) := x in
                            `(lseg LS sh0 contents0) (eval_id _p) `nullval)
                           POST  [tint]
                           (let (_, contents0) := x in
                            local (`(eq (Vint (sum_int contents0))) retval)))))
                    PTree.Leaf) None PTree.Leaf) None PTree.Leaf)) None
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf
                 (Some
                    (Global_func
                       (WITH _ : unit PRE  [(1%positive, tptr tschar),
                        (2%positive, tint)](fun _ : environ => !!False) POST 
                        [tint](fun _ : environ => !!False)))) PTree.Leaf)
              None
              (PTree.Node
                 (PTree.Node PTree.Leaf
                    (Some
                       (Global_func
                          (WITH  sh0 : share, contents0 : 
                           list int PRE  [(_p, tptr t_struct_list)]
                           (fun x0 : environ =>
                            !!writable_share sh0 &&
                            `(lseg LS sh0 contents0) (eval_id _p) `nullval x0)
                           POST  [tptr t_struct_list]
                           `(lseg LS sh0 (rev contents0)) retval `nullval)))
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

Lemma while_entail1 :
  name _t ->
  name _p ->
  name _s ->
  name _h ->
  forall (sh : share) (contents : list int),
   PROP  ()
   LOCAL 
   (tc_environ
      Delta;
   `eq (eval_id _t) (eval_expr (Etempvar _p (tptr t_struct_list)));
   `eq (eval_id _s) (eval_expr (Econst_int (Int.repr 0) tint)))
   SEP  (`(lseg LS sh contents) (eval_id _p) `nullval)
   |-- PROP  ()
       LOCAL 
       (`(eq (Vint (Int.sub (sum_int contents) (sum_int contents))))
          (eval_id _s))
       SEP  (TT; `(lseg LS sh contents) (eval_id _t) `nullval).
Proof.
intros.
go_lower0.
assert 
(( !!True &&
   (!!(eval_id _t rho = eval_id _p rho /\
       eval_id _s rho = Vint (Int.repr 0) /\ True) &&
    (lseg LS sh contents (eval_id _p rho) nullval * emp))) 
=
@Sep.sexprD all_types (functions ++ (more_funcs rho contents sh))  
predicates nil nil (left_side)).
simpl.
unfold VericSepLogic.star.
unfold VericSepLogic.inj.
unfold VericSepLogic.emp.
(*close, but not exactly equal because of emp in reified version*)
Admitted.
