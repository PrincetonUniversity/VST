Require Import MirrorShard.SepExpr.
Require Import veric.SeparationLogic.
Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.queue.
Local Open Scope logic.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Instance QS: listspec t_struct_elem _next. 
Proof. eapply mk_listspec; reflexivity. Defined.

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


Definition Delta := 
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
                            main_post prog u))) (@PTree.Leaf global_spec))))))).

Parameter tycontext_eq : tycontext -> tycontext -> bool.
Axiom typecontext_eq_correct : forall x y, tycontext_eq x y = true -> x = y.


Definition tycontext_type :=
 ({| Expr.Impl := tycontext
       ; Expr.Eqb := tycontext_eq
       ; Expr.Eqb_correct := typecontext_eq_correct
   |}).

Parameter expr_eq : option expr -> option expr -> bool.
Axiom expr_eq_correct : forall x y, expr_eq x y = true -> x = y.

Definition c_option_expr_type :=
 ({| Expr.Impl := option expr
     ; Expr.Eqb := expr_eq
     ; Expr.Eqb_correct := expr_eq_correct |}).

SearchAbout type.
Definition c_type_type :=
 ({| Expr.Impl := type
     ; Expr.Eqb := type_eq
     ; Expr.Eqb_correct := environ_lemmas.type_eq_true |}).

Parameter environ_eq : environ -> environ -> bool.
Axiom environ_eq_correct : forall x y, environ_eq x y = true -> x = y.

Definition environ_type :=
 ({| Expr.Impl := environ
     ; Expr.Eqb := environ_eq
     ; Expr.Eqb_correct := environ_eq_correct |}).

Definition environ2prop_type : Expr.type.
  refine ({| Expr.Impl := environ -> Prop
           ; Expr.Eqb := fun _ _ => false
           ; Expr.Eqb_correct := _
          |}).
  intros. congruence.
Defined.

Definition our_types := cons tycontext_type
                       (cons c_option_expr_type 
                       (cons c_type_type 
                       (cons environ_type 
                       (cons Expr.Prop_type
                       (cons environ2prop_type nil))))).

Definition tycontext_type_var := Expr.tvType 0.

Definition c_option_expr_type_var := Expr.tvType 1.

Definition c_type_type_var := Expr.tvType 2.

Definition environ_type_var := Expr.tvType 3.

Definition prop_type_var := Expr.tvType 4.

Definition environ2prop_type_var := Expr.tvType 5.

Definition delta_const := @Expr.Const our_types tycontext_type_var Delta.

Definition c_option_expr_const := @Expr.Const our_types c_option_expr_type_var 
(@Some expr
            (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)).

Definition ret_type_signature := 
Expr.Sig our_types (cons tycontext_type_var nil)
  c_type_type_var ret_type.

Definition tc_expropt_signature_lifted : Expr.signature our_types :=
Expr.Sig our_types (cons tycontext_type_var (cons c_option_expr_type_var (cons c_type_type_var nil))) environ2prop_type_var tc_expropt.

Definition tc_expropt_signature : Expr.signature our_types :=
Expr.Sig our_types (cons tycontext_type_var (cons c_option_expr_type_var (cons c_type_type_var (cons environ_type_var nil)))) prop_type_var tc_expropt.

Definition functions := cons ret_type_signature
                       (cons tc_expropt_signature
                       (cons tc_expropt_signature_lifted nil)).

Definition ret_type_delta : Expr.expr our_types.
eapply Expr.Func. apply 0%nat. apply (cons delta_const nil).
Defined.

Compute (Expr.exprD (functions) nil nil  ret_type_delta c_type_type_var).

Check tc_expropt.

Print Expr.tvar.


Check tc_expropt_signature.

Definition tc_expropt_application_lifted : Expr.expr our_types.
eapply Expr.Func.
apply 2%nat.
apply (cons delta_const (cons c_option_expr_const (cons ret_type_delta nil))).
Defined.

Definition tc_expropt_application_unlifted : Expr.expr our_types.
eapply Expr.Func.
apply 1%nat.
apply (cons delta_const (cons c_option_expr_const (cons ret_type_delta 
                                                       (cons (Expr.Var 0%nat) nil)))).
Defined.

Definition vars : Expr.env our_types.
unfold Expr.env.
apply cons; [ | apply nil].
unfold Expr.tvarD.
Set Printing All.
SearchAbout sigT.
exists environ_type_var. simpl.
apply empty_environ.
apply semax_lemmas.empty_genv.
Qed.

Print vars. Check projT1.

Definition reflected_tc_expropt :=
(tc_expropt Delta
         (@Some expr
            (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))
         (ret_type Delta)).

Definition reflected_tc_expropt_unlifted :=
forall rho,
(tc_expropt Delta
         (@Some expr
            (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))
         (ret_type Delta) rho).


Lemma tc_expropt_reify_reflect_unlifted : (Expr.exprD functions nil vars tc_expropt_application_unlifted 
prop_type_var) = Some reflected_tc_expropt_unlifted.
simpl. unfold Expr.lookupAs. simpl.
Check vars.
Check projT1.
Locate value
Print vars.
unfold tc_expropt_application_unlifted.
unfold Expr.exprD.
simpl (nth_error functions 1).
unfold value.
unfold Expr.Range.
unfold tc_expropt_signature.
intros. simpl. auto.
Qed.

Lemma tc_expropt_reify_reflect : (Expr.exprD functions nil nil tc_expropt_application_lifted 
environ2prop_type_var) = Some reflected_tc_expropt.
intros. simpl. auto.
Qed.







(* 
*** Local Variables: ***
*** coq-load-path: (("../coq-ext-lib/theories" "ExtLib") ("." "MirrorShard") "../../../work/vst/" "../../../work/floyd" "../../../work/progs") ***
*** End: ***
*)