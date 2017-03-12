Require Import MirrorShard.SepExpr.
Require Import veric.SeparationLogic.
Require Import floyd.proofauto.
Require Import progs.list_dt.
Require Import progs.queue.
Local Open Scope logic.


Module VericSepLogic <: SepTheory.SepTheory.

Definition hprop := mpred.
Definition himp := derives.
Definition heq := fun p1 p2 => derives p1 p2 /\ derives p2 p1.
Definition Refl_himp := derives_refl.
Definition Trans_himp := derives_trans.

Lemma Refl_heq : Reflexive heq.
Proof.
intros.
unfold heq; split; apply derives_refl; auto.
Qed.

Lemma Sym_heq : Symmetric heq.
Proof.
unfold heq, Symmetric. intros.
info intuition.
Qed.

Lemma Trans_heq : Transitive heq.
Proof.
unfold heq, Transitive; intros.
intuition; eapply derives_trans; eauto.
Qed.

Local Notation "a ===> b" := (himp a b) (at level 60).
Local Notation "a <===> b" := (heq a b) (at level 60).


Lemma heq_defn : forall a b, (a ===> b /\ b ===> a) <-> a <===> b.
Proof.
intros. unfold heq, himp; intuition.
Qed.

Lemma heq_himp : forall a b, a <===> b -> a ===> b.
Proof. intros.
unfold heq, himp in *; intuition.
Qed.

Definition emp := emp.


Definition inj := fun p => (prop p && emp).

Definition star := sepcon.

Definition ex := @exp mpred Nveric.

Lemma himp_star_comm : forall P Q,
    (star P Q) ===> (star Q P).
Proof.
intros. unfold star, himp. cancel.
Qed.

Lemma heq_star_comm : forall P Q,
    (star P Q) <===> (star Q P).
Proof.
intros. split; unfold star; cancel.
Qed.

Lemma heq_star_assoc : forall P Q R,
  (star (star P Q) R) <===> (star P (star Q R)).
Proof.
split; unfold star; cancel.
Qed.

Lemma heq_star_emp_l : forall P, (star emp P) <===> P.
Proof.
split; unfold star; cancel.
Qed.

Lemma heq_star_emp_r : forall P, (star P emp) <===> P.
Proof.
split; unfold star; cancel.
Qed.

Lemma himp_star_frame : forall P Q R S,
  P ===> Q -> R ===> S -> (star P R) ===> (star Q S).
Proof.
intros. unfold star. unfold himp in *. apply sepcon_derives; auto.
Qed.

Ltac sep_solve :=
  unfold star, himp, heq, emp, inj, ex in *; intuition; cancel; auto.

Lemma heq_star_frame : forall P Q R S,
  P <===> Q -> R <===> S -> (star P R) <===> (star Q S).
Proof.
intros; sep_solve.
Qed.

Lemma himp_subst_p : forall P Q R S,
  P ===> S -> (star S Q) ===> R ->
  (star P Q) ===> R.
Proof.
sep_solve.
eapply derives_trans in H0. apply H0. cancel.
Qed.

Lemma himp_subst_c : forall P Q R S,
  S ===> Q -> P ===> (star S R) ->
  P ===> (star Q R).
Proof.
sep_solve.
eapply derives_trans; eauto; cancel.
Qed.

Lemma heq_subst : forall P Q R S,
  P <===> S -> (star S Q) <===> R ->
  (star P Q) <===> R.
Proof.
sep_solve.
eapply derives_trans in H; eauto; cancel.
eapply derives_trans; eauto; cancel.
Qed.

Lemma himp_star_cancel : forall P Q R,
  Q ===> R -> (star P Q) ===> (star P R).
Proof.
sep_solve.
Qed.

Lemma heq_star_cancel : forall P Q R,
  Q <===> R -> (star P Q) <===> (star P R).
Proof.
sep_solve.
Qed.


(** pure lemmas **)
Lemma himp_star_pure_p : forall P Q F,
  (star (inj F) P) ===> Q -> (F -> P ===> Q).
Proof.
sep_solve.
eapply derives_trans in H; eauto; entailer!.
Qed.

Lemma himp_star_pure_c : forall P Q (F : Prop),
  (F -> P ===> Q) -> (star (inj F) P) ===> Q.
Proof.
intros.
sep_solve. entailer!.
Qed.

  Lemma himp_star_pure_cc : forall P Q (p : Prop),
    p ->
    P ===> Q ->
    P ===> (star (inj p) Q).
Proof.
sep_solve. entailer!.
Qed.

  (** ex lemmas **)
  Lemma himp_ex_p : forall T (P : T -> _) Q,
            (forall v, (P v) ===> Q) -> (ex T P) ===> Q.
  Proof. sep_solve. apply exp_left. auto.
Qed.

  Lemma himp_ex_c : forall T (P : T -> _) Q,
    (exists v, Q ===> (P v)) -> Q ===> (ex T P).
  Proof.
 sep_solve. destruct H. eapply exp_right.  apply H.
Qed.

  Lemma heq_ex : forall T (P Q : T -> _),
    (forall v, P v <===> Q v) ->
    ex T P <===> ex T Q.
Proof.
sep_solve; apply exp_left;  intros;
specialize (H x); destruct H; apply (exp_right x);
auto.
Qed.

  Lemma himp_ex : forall T (P Q : T -> _),
    (forall v, P v ===> Q v) ->
    ex T P ===> ex T Q.
Proof.
sep_solve. apply exp_left. intros.
specialize (H x). apply (exp_right x). auto.
Qed.

  Lemma heq_ex_star : forall T (P : T -> _) Q,
    (star (ex T P) Q) <===> (ex T (fun x => star (P x) Q)).
Proof.
sep_solve. entailer!.
entailer!. apply (exp_right x). auto.
Qed.

  Lemma himp_ex_star : forall T (P : T -> _) Q,
    (star (ex T P) Q) ===> (ex T (fun x => star (P x) Q)).
Proof.
sep_solve. entailer!.
Qed.

End VericSepLogic.

Check derives_extract_prop.
Print SepExpr.SepExpr.
Module Sep := SepExpr.Make VericSepLogic.


(*Definition if_then_else_isnil (b : forall (s: list val), {s=nil}+{s<>nil})
(m1 m2 : mpred) := if b then m1 else m2.
*)
Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Check (isnil nil).


Instance QS: listspec t_struct_elem _next.
Proof. eapply mk_listspec; reflexivity. Defined.

Definition link := field_at Tsh t_struct_elem _next.
Definition link_ := field_at_ Tsh t_struct_elem _next.


Definition fifo (contents: list val) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      field_at Tsh t_struct_fifo _head p hd *
      field_at Tsh t_struct_fifo _tail p tl *
      if isnil contents
      then (!!(hd=nullval) && emp)
      else (EX prefix: list val,
              !!(contents = prefix++tl::nil)
            &&  (links QS Tsh prefix hd tl * link tl nullval)).

Definition elemrep (rep: elemtype QS) (p: val) : mpred :=
  field_at Tsh t_struct_elem _a p (Vint (fst rep)) *
  (field_at Tsh t_struct_elem _b p (Vint (snd rep)) *
   (field_at_ Tsh t_struct_elem _next p)).


Lemma link_local_facts:
 forall x y, link x y |-- !! (isptr x /\ is_pointer_or_null y).
Proof.
 intros. unfold link.
 eapply derives_trans; [eapply field_at_local_facts; reflexivity |].
 apply prop_derives.
 simpl. intuition.
Qed.

Hint Resolve link_local_facts : saturate_local.

Lemma link__local_facts:
 forall x, link_ x |-- !! isptr x.
Proof.
intros.
unfold link_.
eapply derives_trans; [eapply field_at__local_facts; reflexivity | ].
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


(*above preconstructed, below constructed by entailer *)

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


Definition environ_signature (rho: environ) : Expr.signature our_types :=
Expr.Sig our_types (nil) (environ_type_var) (rho).

Definition functions (rho:environ) := cons ret_type_signature
                       (cons tc_expropt_signature
                       (cons tc_expropt_signature_lifted
                       (cons (environ_signature rho) nil))).

Definition ret_type_delta : Expr.expr our_types.
eapply Expr.Func. apply 0%nat. apply (cons delta_const nil).
Defined.

Definition tc_expropt_application_lifted : Expr.expr our_types.
eapply Expr.Func.
apply 2%nat.
apply (cons delta_const (cons c_option_expr_const (cons ret_type_delta nil))).
Defined.

Definition tc_expropt_application_unlifted : Expr.expr our_types.
eapply Expr.Func.
apply 1%nat.
apply (cons delta_const (cons c_option_expr_const (cons ret_type_delta
                                                       (cons (Expr.Func 3%nat nil) nil)))).
Defined.

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

Lemma tc_expropt_true :
forall rho,
tc_environ Delta rho ->
(tc_expropt Delta
         (@Some expr
            (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))
         (ret_type Delta) rho).
Proof.
intros. simpl.
unfold tc_expr. simpl. super_unfold_lift.
pose (funcs := functions rho).
assert  (Some (tc_expropt Delta
     (Some
        (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
           (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))
     (ret_type Delta) rho) =
Expr.exprD funcs nil nil tc_expropt_application_unlifted prop_type_var).
auto.

Definition prove_goal (exp : Expr.expr our_types) := false.

Definition work_on_goal (exp : Expr.expr our_types) := exp.

Lemma work_on_goal_sound :
forall exp exp2 f p p2,
work_on_goal exp = exp2 ->
Expr.exprD f nil nil exp prop_type_var = Some p ->
(Expr.exprD f nil nil exp2 prop_type_var = Some p2 /\ (p2 -> p)).
Proof. admit.
Qed.

Lemma prove_goal_sound :
forall exp f p,
prove_goal exp = true ->
Expr.exprD f nil nil exp prop_type_var = Some p ->
p.
Proof.
intros. inv H.
Qed.


assert ((prove_goal tc_expropt_application_unlifted = true)) by admit.
eapply prove_goal_sound.
apply H1.
symmetry in H0. apply H0.
Qed.


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
SEP  (`(field_at Tsh t_struct_fifo _head q hd);
`(field_at Tsh t_struct_fifo _tail q tl);
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
. Proof. intros Q h.
 ungather_entail.
unfold fifo.
go_lower.

Check Expr.Func.

Definition saturate (exps: ((list Expr.expr) * Expr.expr)) : bool :=
let exps := (assumptions, goal) in
match with
 ...
| Exps.Func n exps =>
     if eqb_nat n 5 then
             sat
     else
         ....


entailer.
apply exp_right with (h,tl).
entailer.
if_tac; entailer; elim_hyps; simpl; auto.
destruct prefix; entailer1.
Qed.




(*
*** Local Variables: ***
*** coq-load-path: (("../../../GitHub/coq-ext-lib/theories" "ExtLib") ("../../../GitHub/mirror-shard/src" "MirrorShard") ("../veric/" "veric") ("../floyd" "floyd") ("../progs" "progs") ("../compcert" "compcert") ("../msl" "msl") ("../sepcomp" "sepcomp")) ***
*** End: ***
*)
