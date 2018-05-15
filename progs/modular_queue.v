Require Import VST.floyd.proofauto.
Require Import VST.progs.list_dt.
Require Import VST.progs.queue.

Local Open Scope logic.


Record module {reptype: Type} :=  {
   mf_rep: reptype;
   mf_Gimport: list (ident*funspec);
   mf_Gexport :  list (reptype -> ident*funspec);
   mf_Gintern :  list (reptype -> ident*funspec);
   mf_G' :=  map (fun f => f mf_rep)
                  (mf_Gexport ++ mf_Gintern);
   mf_G := mf_Gimport ++ mf_G';
   mf_V : varspecs;
   mf_funs: list (ident * fundef);
   mf_funs_correct: forall (Espec: OracleKind),
     semax_func mf_V mf_G mf_funs mf_G'
}.

Definition builtins:  list (ident * globdef fundef type) :=
  ((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)))
     (Tcons tdouble Tnil) tdouble)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid)) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint)))
     (Tcons (tptr tschar) (Tcons tint Tnil)) tint)) :: nil).

Definition Gbuiltins := do_builtins builtins.

Lemma builtins_correct:
  forall (Espec: OracleKind) V,
  semax_func V Gbuiltins (prog_funct' builtins) Gbuiltins.
Proof.
  intros.
  repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
  apply semax_func_nil.
Qed.

Fixpoint varspecs_sub (al bl: varspecs) : bool :=
match al, bl with
| (a,v)::al', (b,w)::bl' =>
    match Pos.compare a b
    with Lt => false
         | Eq => if eqb_type v w then varspecs_sub al' bl' else false
         | Gt => varspecs_sub al' bl
     end
| nil, _ => true
| _::_, _ => false
end.


Fixpoint funspecs_sub (al bl: funspecs) : Prop :=
match al, bl with
| (a,v)::al', (b,w)::bl' =>
    match Pos.compare a b
    with Lt => False
         | Eq => v=w /\ funspecs_sub al' bl'
         | Gt => funspecs_sub al' bl
     end
| nil, _ => True
| _::_, _ => False
end.


Lemma semax_func_app:
  forall V1 V2 V F1 F2 F G1 G2 G G1' G2' G' (Espec: OracleKind),
  semax_func V1 G1 F1 G1' ->
  semax_func V2 G2 F2 G2' ->
  F = F1++F2 ->
  G' = G1'++G2' ->
  varspecs_sub V1 V = true ->
  varspecs_sub V2 V = true ->
  funspecs_sub G1 G ->
  funspecs_sub G2 G ->
  semax_func V G F G'.
Admitted.

Lemma varspecs_sub_refl: forall vl, varspecs_sub vl vl = true.
Proof.
induction vl; simpl; auto.
destruct a.
rewrite Pos.compare_refl.
rewrite eqb_type_refl. auto.
Qed.

Lemma funspecs_sub_refl: forall g, funspecs_sub g g.
Proof.
induction g; simpl; auto.
destruct a. rewrite Pos.compare_refl.
split; auto.
Qed.

Ltac next_module H :=
  first
  [ apply semax_func_cons; [ reflexivity | apply H | ]
  | eapply semax_func_app;
     [apply H | | reflexivity | reflexivity
     |   try apply varspecs_sub_refl; try reflexivity
     |   try apply varspecs_sub_refl; try reflexivity
     |   try apply funspecs_sub_refl; try (repeat split; simpl; auto)
     |   try apply funspecs_sub_refl; try (repeat split; simpl; auto)
     ]
   ].


(**************************************************************)

Instance QS: listspec t_struct_elem _next.
Proof. eapply mk_listspec; reflexivity. Defined.

Lemma isnil: forall {T: Type} (s: list T), {s=nil}+{s<>nil}.
Proof. intros. destruct s; [left|right]; auto. intro Hx; inv Hx. Qed.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: int
  PRE [ 1%positive OF tint]
     PROP (4 <= Int.signed n) LOCAL (`(eq (Vint n)) (eval_id 1%positive)) SEP ()
  POST [ tptr tvoid ] `(memory_block Tsh n) retval.

Definition freeN_spec :=
 DECLARE _freeN
  WITH u: unit
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]
      PROP() LOCAL () SEP (`(memory_block Tsh) (`force_int (eval_id 2%positive)) (eval_id 1%positive))
  POST [ tvoid ]  emp.

Definition elemrep (rep: elemtype QS) (p: val) : mpred :=
  field_at Tsh t_struct_elem _a p (Vint (fst rep)) *
  (field_at Tsh t_struct_elem _b p (Vint (snd rep)) *
   (field_at_ Tsh t_struct_elem _next p)).

Definition fifotype := forall  (contents: list (elemtype QS)) (p: val), mpred.

Definition fifo_new_spec (fifo: fifotype) :=
 DECLARE _fifo_new
  WITH u : unit
  PRE  [  ] emp
  POST [ (tptr t_struct_fifo) ] `(fifo nil) retval.

Definition fifo_put_spec (fifo: fifotype) :=
 DECLARE _fifo_put
  WITH q: val, contents: list (elemtype QS), elem: elemtype QS
  PRE  [ _Q OF (tptr t_struct_fifo) , _p OF (tptr t_struct_elem) ]
          PROP () LOCAL (`(eq q) (eval_id _Q))
          SEP (`(fifo contents q); `(elemrep elem) (eval_id _p))
  POST [ tvoid ] `(fifo (contents++(elem :: nil)) q).

Definition fifo_empty_spec (fifo: fifotype) :=
 DECLARE _fifo_empty
  WITH q: val, contents: list (elemtype QS)
  PRE  [ _Q OF (tptr t_struct_fifo) ]
     PROP() LOCAL (`(eq q) (eval_id _Q)) SEP(`(fifo contents q))
  POST [ tint ] local (`(eq (if isnil contents then Vtrue else Vfalse)) retval) && `(fifo (contents) q).

Definition fifo_get_spec  (fifo: fifotype) :=
 DECLARE _fifo_get
  WITH q: val, contents: list (elemtype QS), elem: elemtype QS
  PRE  [ _Q OF (tptr t_struct_fifo) ]
       PROP() LOCAL (`(eq q) (eval_id _Q)) SEP (`(fifo (elem :: contents) q))
  POST [ (tptr t_struct_elem) ] `(fifo contents q) * `(elemrep elem) retval.

Definition fifo (contents: list (elemtype QS)) (p: val) : mpred:=
  EX ht: (val*val), let (hd,tl) := ht in
      field_at Tsh t_struct_fifo _head p hd *
      field_at Tsh t_struct_fifo _tail p tl *
      if isnil contents
      then (!!(tl=p) && emp)
      else (EX prefix: list (elemtype QS), EX ult:val, EX elem: elemtype QS,
              !!(tl=offset_val (Int.repr 8)  ult
                  /\ contents = prefix++(elem::nil))
            &&  (lseg QS Tsh prefix hd ult *
                   elemrep elem ult)).

Definition Gimport := mallocN_spec :: freeN_spec :: nil.
Definition Gexport :=  fifo_new_spec :: fifo_put_spec
    :: fifo_empty_spec :: fifo_get_spec :: nil.
Definition Gintern : list (fifotype -> ident*funspec) := nil.
Definition G := Gimport ++
               (map (fun f => f fifo) (Gexport ++ Gintern)).
Definition V: varspecs := nil.

Lemma body_fifo_new: semax_body V G f_fifo_new (fifo_new_spec fifo).
Admitted.

Lemma body_fifo_put: semax_body V G f_fifo_put (fifo_put_spec fifo).
Admitted.

Lemma body_fifo_empty: semax_body V G f_fifo_empty (fifo_empty_spec fifo).
Admitted.

Lemma body_fifo_get: semax_body V G f_fifo_get (fifo_get_spec fifo).
Admitted.

Definition funcs := ((_fifo_new, Internal f_fifo_new) ::
   (_fifo_put, Internal f_fifo_put) ::
   (_fifo_empty, Internal f_fifo_empty) ::
   (_fifo_get, Internal f_fifo_get) :: nil).

Lemma funcs_correct:
 forall (Espec: OracleKind),
  semax_func V G  funcs  (map (fun f => f fifo) (Gexport ++ Gintern)).
Proof.
intro.
next_module body_fifo_new.
next_module body_fifo_put.
next_module body_fifo_empty.
next_module body_fifo_get.
apply semax_func_nil.
Qed.

Definition module_fifo : module := {|
   mf_rep := fifo;
   mf_Gimport := (mallocN_spec :: freeN_spec :: nil);
   mf_Gexport := (fifo_new_spec :: fifo_put_spec
    :: fifo_empty_spec :: fifo_get_spec :: nil);
   mf_Gintern := nil;
   mf_V := nil;
   mf_funs := ((_fifo_new, Internal f_fifo_new) ::
   (_fifo_put, Internal f_fifo_put) ::
   (_fifo_empty, Internal f_fifo_empty) ::
   (_fifo_get, Internal f_fifo_get) :: nil);
   mf_funs_correct := funcs_correct
|}.

(***************************************************)

Definition make_elem_spec :=
 DECLARE _make_elem
  WITH a: int, b: int
  PRE  [ _a OF tint, _b OF tint ]
        PROP() LOCAL(`(eq (Vint a)) (eval_id _a); `(eq (Vint b)) (eval_id _b)) SEP()
  POST [ (tptr t_struct_elem) ] `(elemrep (a,b)) retval.

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs :=   ltac:(with_library prog
  (mallocN_spec :: freeN_spec ::
    (map (fun f => f module_fifo.(mf_rep)) module_fifo.(mf_Gexport))
   ++ make_elem_spec :: main_spec::nil)).

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Lemma body_make_elem: semax_body Vprog Gtot f_make_elem make_elem_spec.
Admitted.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Admitted.

Existing Instance NullExtension.Espec.

Lemma two_correct:
  semax_func Vprog Gtot
    ((_make_elem, Internal f_make_elem) :: (_main, Internal f_main) :: nil)
     (make_elem_spec::main_spec::nil).
Proof.
next_module body_make_elem.
next_module body_main.
apply semax_func_nil.
Qed.

Parameter body_mallocN:
 semax_external
  (EF_external _mallocN
     {| sig_args := AST.Tint :: nil; sig_res := Some AST.Tint |}) int
  (fun n : int => PROP (4 <= Int.signed n) LOCAL (`(eq (Vint n)) (eval_id 1%positive)) SEP ())
  (fun n : int => `(memory_block Tsh n) retval).

Parameter body_freeN:
semax_external
  (EF_external _freeN
     {| sig_args := AST.Tint :: AST.Tint :: nil; sig_res := None |}) unit
  (fun _ : unit =>
      PROP() LOCAL () SEP (`(memory_block Tsh) (`force_int (eval_id 2%positive)) (eval_id 1%positive)))
 (fun _ : unit => emp).


Lemma extern_correct:
  semax_func Vprog Gtot
 ((_mallocN,(External (EF_external _mallocN
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)))
     (Tcons tint Tnil) (tptr tvoid))) ::
 (_freeN,
   (External (EF_external _freeN
                   (mksignature (AST.Tint :: AST.Tint :: nil) None))
     (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid)) :: nil)
  (mallocN_spec::freeN_spec::nil).
Proof.
 apply semax_func_cons_ext; [ reflexivity | apply body_mallocN | ].
 apply semax_func_cons_ext; [ reflexivity | apply body_freeN | ].
apply semax_func_nil.
Qed.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
 next_module builtins_correct.
 next_module extern_correct.
 next_module (module_fifo.(mf_funs_correct)).
 next_module two_correct.
 apply semax_func_nil.
Qed.

