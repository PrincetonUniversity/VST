Require Import VST.floyd.proofauto.
Require Import VSTlib.threads.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation vint z := (Vint (Int.repr z)).

Definition spawn_arg_type := ProdType (ConstType (val * val)) (SigType Type (fun A => ProdType (ProdType
  (DiscreteFunType A (ConstType globals)) (ConstType A))
  (DiscreteFunType A (DiscreteFunType val Mpred)))).

Local Unset Program Cases.


Section mpred.
Context `{!VSTGS OK_ty Σ}.

Program Definition spawn_pre : dtfr (ArgsTT spawn_arg_type) := λne x,
  let '(f, b, fs) := x in
  PROP (tc_val (tptr Tvoid) b)
    PARAMS (f; b)
    GLOBALS (let 'existT A ((gv, w), _) := fs in gv w)
    SEP (let 'existT A ((gv, w), pre) := fs in
         (func_ptr
           (WITH y : val, x : A
             PRE [ tptr tvoid ]
               PROP ()
               PARAMS (y)
               GLOBALS (gv x)
               SEP (pre x y)
             POST [ tint ]
               PROP  ()
               RETURN (Vint Int.zero) (* spawned functions must return 0 for now *)
               SEP   ())
           f);
         let 'existT A ((gv, w), pre) := fs in (*valid_pointer b ∧*) pre w b) (* Do we need the valid_pointer here? *).
Next Obligation.
Proof.
  intros ? ((f, b), (?, ((gv, ?), pre))) ((?, ?), (?, ((?, w), ?))) ([=] & ? & Hfs) rho; simpl in *; subst; simpl in *.
  destruct Hfs as ((Hgv & [=]) & Hpre); simpl in *; subst.
  rewrite (Hgv _).
  do 6 f_equiv.
  - apply func_ptr_si_nonexpansive; last done.
    split; last split; [done..|].
    exists eq_refl; simpl.
    split3; intros (?, ?); simpl; try done.
    intros ?; rewrite Hgv (Hpre _ _) //.
  - rewrite (Hpre _ _) //.
Defined.

Program Definition spawn_post : @dtfr Σ (AssertTT spawn_arg_type) := λne x,
  let '(f, b, fs) := x in PROP () LOCAL () SEP ().
Next Obligation.
Proof.
  intros ? ((f, b), ?) ((?, ?), ?) ?.
  reflexivity.
Qed.


Definition spawned_funtype := Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default.

Definition spawn_spec := mk_funspec ([tptr spawned_funtype; tptr tvoid], tvoid) cc_default
  spawn_arg_type (λne _, ⊤) spawn_pre spawn_post.

Definition exit_thread_spec : ident * @funspec Σ :=
  DECLARE _exit_thread
  WITH v : val
  PRE [ tint ]
    PROP ()
    PARAMS (v)
    SEP ()
  POST [ tvoid ]
    PROP (False)
    RETURN ()
    SEP ().

Definition ThreadsASI:funspecs := [
    (_spawn, spawn_spec); exit_thread_spec
 ].

End mpred.


