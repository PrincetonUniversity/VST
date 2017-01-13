Add LoadPath "..".
Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.call_lemmas.
Require Import veric.ghost.
Require Import ssreflect ssrbool ssrnat ssrfun.
Set Implicit Arguments.

Local Open Scope logic.

(** A representation predicate.  Two things:
    -We assert the existence of an abstract representation [x] of the module state
    using [ghostp sh loc x].
    -This abstract representation is related to the heap layout via the
    representation invariant [R]. *)

Definition rep {A: Type} (r: ident) (x: A) (R: ident -> A -> environ -> mpred) : environ -> mpred :=
  fun rho => (EX sh: Share.t, EX loc: address, ghostp sh loc x) * R r x rho.

(** An abstract specification in usual Hoare style. *)

Record aspec {A: Type} := mk_aspec
  { Pspec: A -> environ -> Prop
  ; Qspec: A -> environ -> val -> Prop }.

(** Rspecs: lift rep-style predicates above to operate on sets of abstract states (given
    by some predicate P,Q,...).

    In addition to (P,Q), we specify a module initialization function that establishes
    the representation invariant at the outset. [r] is a "root pointer" into the data
    structure.  E.g., in a linked list [r] is a pointer to the first cons cell. *)

Section rspec.
Context {A: Type} (argsig: list (ident*type)) (retty: type).
Context (R: ident -> A -> environ -> mpred) (p: @aspec A).

Definition rspec_init (r: ident) (init: A) : unit -> environ -> mpred :=
  fun tt rho => rep r init R rho.

Definition rspec_pre (r: ident) : unit -> environ -> mpred :=
  fun tt rho => EX x: A, rep r x R rho && !!p.(Pspec) x rho.

Definition rspec_post (r: ident) : unit -> environ -> mpred :=
  fun tt rho => EX x: A, rep r x R rho && !!p.(Qspec) x rho (retval rho).

Definition init_rspec (r: ident) (init: A) : funspec :=
  mk_funspec (argsig,Tvoid) cc_default unit TT (rspec_init r init * TT).

Definition rspec (r: ident) : funspec :=
  mk_funspec (argsig,retty) cc_default unit (rspec_pre r) (rspec_post r).

End rspec.

Definition nonvoid (ty: type) := match ty with Tvoid => False | _ => True end.

Definition nonvoidty := {ty: type | nonvoid ty}.

Definition get_nonvoidty : nonvoidty -> type := @proj1_sig _ nonvoid.

Infix "$" := (fun f => [eta f]) (at level 50).

Lemma nonvoid_nonvoidty ty : nonvoid $ get_nonvoidty ty.
Proof. by case: ty. Qed.

Coercion get_nonvoidty : nonvoidty >-> type.

(** RFuns: For a single function, put the various pieces together. *)

Section rfun.
Context (Delta: tycontext).
Context {A: Type} (R: ident -> A -> environ -> mpred) (r: ident).

Record init_rfun := mk_init_rfun
  { init_id: ident
  ; init_argsig: list (ident*type)
  ; init: A
  ; init_spec := init_rspec init_argsig R r init
  ; init_ok: (glob_types Delta) ! init_id = Some (Global_func init_spec) }.

Record rfun := mk_rfun
  { f_id: ident
  ; argsig: list (ident*type)
  ; retty: nonvoidty
  ; a_spec: aspec
  ; f_spec := rspec argsig retty R a_spec r
  ; ok: (glob_types Delta) ! f_id = Some (Global_func f_spec) }.

End rfun.

(** A module is:
    -An existentially quantified representation invariant
    -A module initialization function, for establishing the invariant initially, and
    -A set of rfuns. *)

Record module (Delta: tycontext) (A: Type) (r: ident) := mk_module
  { Rinv: ident -> A -> environ -> mpred
  ; module_init: init_rfun Delta Rinv r
  ; methods: list (rfun Delta Rinv r) }.

Section module_defs.
Context {Delta: tycontext} {A r} (my_module: module Delta A r).

Definition identlist_of_module : list ident :=
  map (fun x => f_id (R:=Rinv my_module) x) my_module.(methods).

Definition exported (id: ident) := id_in_list id identlist_of_module.

Definition xident := {id: ident | exported id=true}.

Definition get_ident : xident -> ident := @proj1_sig _ (fun id => exported id=true).

Coercion get_ident : xident >-> ident.

Fixpoint rfun_of_ident (id: ident) (l: list (rfun Delta my_module.(Rinv) r))
  : option (rfun Delta my_module.(Rinv) r) :=
  match l with
    nil   => None
  | f::l' => if eq_dec id f.(f_id) then Some f else rfun_of_ident id l'
  end.

Definition rfun_of_xident (id: xident) := rfun_of_ident id my_module.(methods).

Lemma rfun_of_xident_some id : exists f, rfun_of_xident id = Some f.
Proof.
case: id=> id; rewrite/rfun_of_xident/exported/=.
move/(id_in_list_true _ _); rewrite/identlist_of_module=> H.
apply list_in_map_inv in H; move: H=>[x [->]].
move: (methods my_module); elim=>// a l IH [->/=|/=H].
by exists x; case EQ: (eq_dec (f_id x) (f_id x)).
move: (IH H)=>{IH} [p IH]; case EQ: (eq_dec (f_id x) (f_id a)); first by exists a.
by exists p.
Qed.

Lemma rfun_of_xident_eq {id f} : rfun_of_xident id = Some f -> f.(f_id) = id.
Proof.
rewrite/rfun_of_xident; move: (methods my_module)=> l; elim: l=> // a l /=.
elim H: (eq_dec (get_ident id) (f_id a))=>//= H1; case=> <- //.
Qed.

End module_defs.

(********************************************************)

Section client_lemmas.
Context {Delta A r} (my_module: module Delta A r).

(** Assume my_module. Then the following holds about calls to functions [f_id]
    exported by the module: *)

Lemma client_call:
 forall Espec P Q R ret (f_id: xident my_module) bl x f
        (GLBL: (var_types Delta) ! (get_ident f_id) = None)
        (SPEC: rfun_of_xident f_id = Some f),
 let Pre  := rspec_pre  my_module.(Rinv) f.(a_spec) r in
 let Post := rspec_post my_module.(Rinv) f.(a_spec) r in
 @semax Espec Delta
 (PROPx P
  (LOCALx (tc_exprlist Delta (snd (split f.(argsig))) bl :: Q)
  (SEPx (`(Pre x) (make_args' (f.(argsig),Tvoid) (eval_exprlist
                          (snd (split f.(argsig))) bl)) :: R))))
             (Scall (Some ret)
                    (Evar f_id (Tfunction (type_of_params f.(argsig)) f.(retty)))
                    bl)
 (normal_ret_assert (EX old:val,
  PROPx P
   (LOCALx (map (subst ret (`old)) Q)
   (SEPx (`(Post x) (get_result1 ret) :: map (subst ret (`old)) R))))).
Proof.
move=> ? ? ? ? ? ? ? ? f H1 H2; apply: semax_call_id1=>//.
by move: (rfun_of_xident_eq H2)=> <-; move: (f.(ok))=> ->.
by apply: (nonvoid_nonvoidty $ retty f).
Qed.

End client_lemmas.




