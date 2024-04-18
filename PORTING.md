# Porting VST developments from VST 2.x to VST 3.x

VST 3.0 has quite a few changes from VST 2.x: the separation logic uses Iris-style notations, and predicates such as `data_at` and `semax` have different implicit arguments.

The *simplest* method to port is called "naive oracle-monomorphic", and you start by,

```
Require Import VST.floyd.compat.  Import NoOracle.
```

Even in compatibility mode, there are a few things that cannot be made backwards-compatible. Here are some tips on making the minimum necessary changes to port your proofs to 3.0.

* The scope `logic` no longer exists, and has been replaced by the Iris scope `I`, which is open by default. Remove `Open Scope logic` and `%logic` throughout.
* The implicit arguments of almost every definition have changed, so references to `@data_at`, `@semax`, etc. will break. We strongly recommend naming implicit arguments explicitly instead (e.g., `data_at(cs := cs)` instead of `@data_at cs`).
* `semax` also takes an extra explicit argument, an invariant mask `E`. This is automatically instantiated by `semax_body`, but it will affect the statement of lemmas that are stated directly on `semax`. For almost all purposes, you can use the default value `⊤`.
* Assertions with explicit type annotations of `environ -> mpred` should be changed to `assert`. More generally, the transition between `assert`s and `mpred`s is not as automatic as in VST 2.x, and you may run into trouble with proofs that rely heavily on automatic lifting.
* The `Espec`/`OracleKind` mechanism has been refactored. `Existing Instance NullExtension.Espec` is no longer necessary to state `semax_prog` lemmas, and should be removed.
* `mpred`s are not extensional by default: i.e., you cannot prove `P = Q` by proving `P |-- Q` and `Q |-- P`. You can, however, prove `P ⊣⊢ Q`, which can be given to `rewrite` and generally functions the same as equality in most cases. If you really want equality rather than equivalence, you can prove it by rewriting with equalities, and many useful lemmas hav already been proved as equalities.
* Proofs that rely on rewriting with `sepcon_assoc` and `sepcon_comm` may break, for several reasons: most notably, `*` is now right-associative instead of left-associative, and several tactics now associate this way by default. The best way to handle these proofs is to use Iris Proof Mode, which you can still use in compatibility mode. It should also still be possible to do these proofs with rewrites, but you may have to adjust their order and direction.
* Coq sometimes has trouble inferring the type of `funspec`s. You can fix this by adding a type annotation as appropriate (`: funspec`, `: ident * funspec`, etc.).
* When a postcondition has multiple existentials, the order in which `normalize` and `entailer` rearrange them is sometimes different from 2.x. You may find that you need to swap the order of two successive `Exists` tactics.
* `Funspec_old_Notation` is no longer supported. We strongly recommend updating to the new, more convenient funspec notation (using `PARAMS` instead of `LOCAL` in the function precondition). You can uncomment the contents of `floyd/Funspec_old_Notation.v` if you really want to use it, but do so at your own risk: in the worst case, functions declared with it may cause `start_function` to run forever.

If you encounter a porting problem you're unsure how to solve, or a bug in the new version, please contact [mansky1@uic.edu](mailto:mansky1@uic.edu).

## Oracle polymorphism

A *more sophisticated* method is to omit the `Import NoOracle`.

`Require Import VST.floyd.compat.`  `(*` ~~Import NoOracle.~~ `*)`

Predicates and judgments such as `data_at`, `semax`, and others have an implicit argument `Σ: gFunctors`, along with other implicit arguments about properties of Σ.  These are generally instantiated by typeclass resolution.  This argument represents the "ghost world" or "external environment" or "oracle", the things that your C program might touch that are _outside_ the ordinary memory filled with structs and arrays.  In different verifications, you may use different types of ghost world, which is why we need a parameter Σ.

But many functions you write can be proved correct without any reference to the ghost world.  These verifications should work no matter what kind of oracle there is.  We call these functions "oracle-polymorphic".  If your function doesn't do I/O and doesn't syncronize on locks or atomics, then probably it can be oracle-polymorphic.

The "naive oracle-monomorphic" method described above, when you `Import NoOracle`, makes visible a typeclass that provides an instance of Σ that has a trivial (unit-value) oracle.  This works for proving these "simple in-memory" functions.  But the problem arises when you call such a function from a place that is oracle-relevant.  That is, if your function that does concurrent synchronization or I/O (and needs a particular type Σ) calls your simple in-memory function, that you have proved correct with the default Σ, then you will have a type mismatch.

The solution is to make your entire specification and verification, of those functions that don't care about the type of Σ, actually polymorphic in Σ.  You can do this as follows:

```
Section GFUNCTORS.
Context `{VSTGS_OK: !VSTGS OK_ty Σ}.
(* . . . funspecs and semax_body proofs for oracle-polymorphic functions *)
Definition f1_spec := DECLARE ... WITH ... PRE ... POST.
Definition f2_spec := DECLARE ... WITH ... PRE ... POST.
Definition Gprog_poly : funspecs := [f1_spec; f2_spec].

Lemma body_f1: semax_body Vprog Gprog_poly f_f1 f1_spec.
Proof. ... Qed.
Lemma body_f2: semax_body Vprog Gprog_poly f_f2 f2_spec.
Proof. ... Qed.

End GFUNCTORS.
```

### Verifying `main` with `main_pre`

Even if most of your program is oracle-polymorphic, the `main` function is not quite.  VST's default precondition for `main`, called `main_pre`, requires you to specify an initial value for the oracle.  In a typical simple verification, where the oracle type is `unit`, then the initial value is simply `tt`.  For that to work, you have to use some
Σ whose `OK_ty` is unit.

The solution is to `Import NoOracle`; what that does is exactly to make available a `VST_default` typeclass with a `VSTΣ` whose oracle-type is unit.  In order to limit the use of this Import to those places where you really want it---to avoid polluting your namespace when reasoning about oracle-polymorphic functions---you might put the Import into a Section that limits its scope:

```
Section LimitImport. Import NoOracle.
 Definition main_spec :=
   DECLARE _main
   WITH gv : globals
   PRE  [] main_pre prog tt gv
   POST [ tint ] main_post prog gv.
End LimitImport.
```
You have to be careful not to put `main_spec` into your `Gprog_poly` that's used for the `semax_body` proofs of your oracle-polymorphic functions.

The example program `progs64/verif_revarray.v` in the VST repo illustrates this method.  
But really, if you are being sophisticated about abstraction and modularity in this way, keeping track of which Gprog you use for each semax_body proof,
then you should be using the [VSU](https://softwarefoundations.cis.upenn.edu/vc-current/VSU_intro.html) system.




