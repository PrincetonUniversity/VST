Require Import VST.veric.base.
Require Import VST.veric.res_predicates.
Require Export compcert.common.AST.
Require Export compcert.cfrontend.Ctypes.

Require Import VST.veric.composite_compute.
Require Import VST.veric.align_mem.
Require Import VST.veric.val_lemmas.

Require Export VST.veric.compspecs.

Open Scope Z_scope.

Definition strict_bool_val (v: val) (t: type) : option bool :=
   match v, t with
   | Vint n, Tint _ _ _ => Some (negb (Int.eq n Int.zero))
   | Vlong n, Tlong _ _ => Some (negb (Int64.eq n Int64.zero))
   | (Vint n), (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
            if Archi.ptr64 then None else if Int.eq n Int.zero then Some false else None
   | Vlong n, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) =>
            if Archi.ptr64 then if Int64.eq n Int64.zero then Some false else None else None
   | Vptr b ofs, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ ) => Some true
   | Vfloat f, Tfloat F64 _ => Some (negb(Float.cmp Ceq f Float.zero))
   | Vsingle f, Tfloat F32 _ => Some (negb(Float32.cmp Ceq f Float32.zero))
   | _, _ => None
   end.

Definition type_is_by_value (t:type) : bool :=
  match t with
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tpointer _ _ => true
  | _ => false
  end.

Definition type_is_by_reference t : bool :=
  match t with
  | Tarray _ _ _
  | Tfunction _ _ _ => true
  | _ => false
  end.

Section FUNSPEC.

Context `{!heapGS Σ}.

(*Definition AssertTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType environ) Mpred).

Definition ArgsTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType argsEnviron) Mpred).

Definition SpecTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType bool) (ArrowType (ConstType environ) Mpred)).

Definition SpecArgsTT (A: TypeTree): TypeTree :=
  ArrowType A 
  (PiType bool (fun b => ArrowType (ConstType 
                                         (if b 
                                          then argsEnviron
                                          else environ))
                                    Mpred)).

Definition super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): Prop :=
  forall n ts
    (x: functors.MixVariantFunctor._functor
                         (rmaps.dependent_type_functor_rec ts A) mpred)
    (rho: environ),
  approx n (P ts x rho) = approx n (P ts (fmap _ (approx n) (approx n) x) rho).

Definition args_super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred): Prop :=
  forall n ts
    (x: functors.MixVariantFunctor._functor
                         (rmaps.dependent_type_functor_rec ts A) mpred)
    (gargs: argsEnviron),
  @eq mpred (approx n (P ts x gargs)) (approx n (P ts (fmap _ (approx n) (approx n) x) gargs)).

Definition const_super_non_expansive: forall (T: Type) P,
  @super_non_expansive (ConstType T) P :=
  fun _ _ _ _ _ _ => eq_refl.

Definition AssertListTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType environ) (ListType Mpred)).

Definition super_non_expansive_list {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertListTT A) mpred): Prop :=
  forall n ts
    (x: functors.MixVariantFunctor._functor
                         (rmaps.dependent_type_functor_rec ts A) mpred)
    (rho: environ),
  Forall2 (fun a b => approx n a = approx n b) (P ts x rho) (P ts (fmap _ (approx n) (approx n) x) rho).

Definition args_const_super_non_expansive: forall (T: Type) P,
  @args_super_non_expansive (ConstType T) P :=
  fun _ _ _ _ _ _ => eq_refl.*)

(*Potential alternative that does not use Ctypes
Inductive funspec :=
   mk_funspec: AST.signature -> forall (A: TypeTree)
     (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: super_non_expansive P) (Q_ne: super_non_expansive Q),
    funspec.
 *)

(* Do we need -n> here?. *)
Inductive funspec :=
   mk_funspec: typesig -> calling_convention -> forall (A: Type)
     (P: A -> argsEnviron -> mpred) (Q: A -> environ -> mpred),
     funspec.

(*Inductive funspec :=
   mk_funspec: typesig -> calling_convention -> forall (A: TypeTree)
     (P: forall ts, dependent_type_functor_rec ts (ArgsTT A) mpred)
     (Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: args_super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.*)

Definition varspecs : Type := list (ident * type).

Definition funspecs := list (ident * funspec).

Definition assert := environ -> mpred.  (* Unfortunately
   can't export this abbreviation through SeparationLogic.v because
  it confuses the Lift system *)

Definition argsassert := argsEnviron -> mpred.

(*plays role of type_of_params *)
Fixpoint typelist_of_type_list (params : list type) : typelist :=
  match params with
  | nil => Tnil
  | ty :: rem => Tcons ty (typelist_of_type_list rem)
  end.

Definition type_of_funspec (fs: funspec) : type :=
  match fs with mk_funspec fsig cc _ _ _ => 
     Tfunction (typelist_of_type_list (fst fsig)) (snd fsig) cc end.

Fixpoint make_tycontext_s (G: funspecs) :=
 match G with
 | nil => Maps.PTree.empty funspec
 | (id,f)::r => Maps.PTree.set id f (make_tycontext_s r)
 end.

End FUNSPEC.

Definition int_range (sz: intsize) (sgn: signedness) (i: int) :=
 match sz, sgn with
 | I8, Signed => -128 <= Int.signed i < 128
 | I8, Unsigned => 0 <= Int.unsigned i < 256
 | I16, Signed => -32768 <= Int.signed i < 32768
 | I16, Unsigned => 0 <= Int.unsigned i < 65536
 | I32, Signed => -2147483648 <= Int.signed i < 2147483648
 | I32, Unsigned => 0 <= Int.unsigned i < 4294967296
 | IBool, _ => 0 <= Int.unsigned i < 256
 end.

Lemma size_chunk_sizeof: forall env t ch, access_mode t = By_value ch -> sizeof env t = Memdata.size_chunk ch.
Proof.
  intros.
  destruct t; inversion H.
  - destruct i, s; inversion H1; reflexivity.
  - destruct s; inversion H1; reflexivity.
  - destruct f; inversion H1; reflexivity.
  - inversion H1; reflexivity.
Qed.

Arguments sizeof {env} !t / .
Arguments alignof {env} !t / .

Arguments sizeof_pos {env} t _.
Arguments alignof_pos {env} t.

Arguments complete_legal_cosu_type {cenv} !t / .

(* TODO: handle other part of compspecs like this. *)
Goal forall {cs: compspecs} t, sizeof t >= 0.
Proof. intros. apply sizeof_pos.
Abort.

(*same definition as in Clight_core?*)
Fixpoint typelist2list (tl: typelist) : list type :=
 match tl with Tcons t r => t::typelist2list r | Tnil => nil end.

Lemma TTL1 l: typelist_of_type_list (map snd l) = type_of_params l.
Proof. induction l; simpl; trivial. destruct a. f_equal; trivial. Qed.

Lemma TTL2 l: (typlist_of_typelist (typelist_of_type_list l)) = map typ_of_type l.
Proof. induction l; simpl; trivial. f_equal; trivial . Qed.

Lemma TTL4 l: map snd l = typelist2list (type_of_params l).
Proof. induction l; simpl; trivial. destruct a. simpl. f_equal; trivial. Qed.

Lemma TTL5 {l}: typelist2list (typelist_of_type_list l) = l.
Proof. induction l; simpl; trivial. f_equal; trivial. Qed.

Definition idset := Maps.PTree.t unit.

Definition idset0 : idset := Maps.PTree.empty _.
Definition idset1 (id: ident) : idset := Maps.PTree.set id tt idset0.
Definition insert_idset (id: ident) (S: idset) : idset :=
  Maps.PTree.set id tt S.

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).

Definition env_set (rho: environ) (x: ident) (v: val) : environ :=
  mkEnviron (ge_of rho) (ve_of rho) (Map.set x v (te_of rho)).

Lemma eval_id_same: forall rho id v, eval_id id (env_set rho id v) = v.
Proof. unfold eval_id; intros; simpl. unfold force_val. rewrite Map.gss. auto.
Qed.

Lemma eval_id_other: forall rho id id' v,
   id<>id' -> eval_id id' (env_set rho id v) = eval_id id' rho.
Proof.
 unfold eval_id, force_val; intros. simpl. rewrite Map.gso; auto.
Qed.

#[export] Hint Rewrite eval_id_same : normalize norm.
#[export] Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : normalize norm.

(* TWO ALTERNATE WAYS OF DOING LIFTING *)
(* LIFTING METHOD ONE: *)
Definition lift0 {B} (P: B) : environ -> B := fun _ => P.
Definition lift1 {A1 B} (P: A1 -> B) (f1: environ -> A1) : environ -> B := fun rho => P (f1 rho).
Definition lift2 {A1 A2 B} (P: A1 -> A2 -> B) (f1: environ -> A1) (f2: environ -> A2):
   environ -> B := fun rho => P (f1 rho) (f2 rho).
Definition lift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B)
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3) :  environ -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho).
Definition lift4 {A1 A2 A3 A4 B} (P: A1 -> A2 -> A3 -> A4 -> B)
     (f1: environ -> A1) (f2: environ -> A2) (f3: environ -> A3)(f4: environ -> A4):  environ -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho) (f4 rho).

Definition alift0 {B} (P: B) : argsEnviron -> B := fun _ => P.
Definition alift1 {A1 B} (P: A1 -> B) (f1: argsEnviron -> A1) : argsEnviron -> B := fun rho => P (f1 rho).
Definition alift2 {A1 A2 B} (P: A1 -> A2 -> B) (f1: argsEnviron -> A1) (f2: argsEnviron -> A2):
   argsEnviron -> B := fun rho => P (f1 rho) (f2 rho).
Definition alift3 {A1 A2 A3 B} (P: A1 -> A2 -> A3 -> B)
     (f1: argsEnviron -> A1) (f2: argsEnviron -> A2) (f3: argsEnviron -> A3) :  argsEnviron -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho).
Definition alift4 {A1 A2 A3 A4 B} (P: A1 -> A2 -> A3 -> A4 -> B)
     (f1: argsEnviron -> A1) (f2: argsEnviron -> A2) (f3: argsEnviron -> A3)(f4: argsEnviron -> A4):  argsEnviron -> B :=
     fun rho => P (f1 rho) (f2 rho) (f3 rho) (f4 rho).

(* LIFTING METHOD TWO: *)
Require Import VST.veric.lift.
Set Warnings "-projection-no-head-constant,-redundant-canonical-projection".
Canonical Structure LiftEnviron := Tend environ.
Set Warnings "projection-no-head-constant,redundant-canonical-projection".

Set Warnings "-projection-no-head-constant,-redundant-canonical-projection".
Canonical Structure LiftAEnviron := Tend argsEnviron.
Set Warnings "projection-no-head-constant,redundant-canonical-projection".

Ltac super_unfold_lift :=
  cbv delta [liftx LiftEnviron LiftAEnviron Tarrow Tend lift_S lift_T lift_prod
  lift_last lifted lift_uncurry_open lift_curry lift lift0 lift1 lift2 lift3 alift0 alift1 alift2 alift3] beta iota in *.
