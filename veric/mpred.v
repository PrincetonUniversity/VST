From iris.bi Require Export monpred.
Require Import VST.veric.base.
Require Import VST.veric.gmap_view.
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

(** GENERAL KV-Maps **)

Set Implicit Arguments.

Module Map. Section map.
Context (B : Type).

Definition t := positive -> option B.

Definition get (h: t) (a:positive) : option B := h a.

Definition set (a:positive) (v: B) (h: t) : t :=
  fun i => if ident_eq i a then Some v else h i.

Definition remove (a: positive) (h: t) : t :=
  fun i => if ident_eq i a then None else h i.

Definition empty : t := fun _ => None.

(** MAP Axioms **)

Lemma gss h x v : get (set x v h) x = Some v.
unfold get, set; if_tac; intuition.
Qed.

Lemma gso h x y v : x<>y -> get (set x v h) y = get h y.
unfold get, set; intros; if_tac; intuition; subst; contradiction.
Qed.

Lemma grs h x : get (remove x h) x = None.
unfold get, remove; intros; if_tac; intuition.
Qed.

Lemma gro h x y : x<>y -> get (remove x h) y = get h y.
unfold get, remove; intros; if_tac; intuition; subst; contradiction.
Qed.

Lemma ext h h' : (forall x, get h x = get h' x) -> h=h'.
Proof.
intros. extensionality x. apply H.
Qed.

Lemma override (a: positive) (b b' : B) h : set a b' (set a b h) = set a b' h.
Proof.
apply ext; intros; unfold get, set; if_tac; intuition. Qed.

Lemma gsspec:
    forall (i j: positive) (x: B) (m: t),
    get (set j x m) i = if ident_eq i j then Some x else get m i.
Proof.
intros. unfold get; unfold set; if_tac; intuition.
Qed.

Lemma override_same : forall id t (x:B), get t id = Some x -> set id x t = t.
Proof.
intros. unfold set. unfold get in H.  apply ext. intros. unfold get.
if_tac; subst; auto.
Qed.

End map.

End Map.

Unset Implicit Arguments.

Global Instance EqDec_calling_convention: EqDec calling_convention.
Proof.
  hnf. decide equality.
  destruct cc_structret, cc_structret0; subst; try tauto; right; congruence.
  destruct cc_unproto, cc_unproto0;  subst; try tauto; right; congruence.
  destruct cc_vararg, cc_vararg0; subst; try tauto.
  destruct (zeq z0 z); subst; [left|right]; congruence.
  right; congruence.
  right; congruence.
Qed.

(** Environment Definitions **)
Section FUNSPEC.

Definition genviron := Map.t block.

Definition venviron := Map.t (block * type).

Definition tenviron := Map.t val.

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: venviron) (te: tenviron), environ.

Definition ge_of (rho: environ) : genviron :=
  match rho with mkEnviron ge ve te => ge end.

Definition ve_of (rho: environ) : venviron :=
  match rho with mkEnviron ge ve te => ve end.

Definition te_of (rho: environ) : tenviron :=
  match rho with mkEnviron ge ve te => te end.

Definition any_environ : environ :=
  mkEnviron (fun _ => None)  (Map.empty _) (Map.empty _).

Definition argsEnviron:Type := genviron * (list val).

Global Instance EqDec_type: EqDec type := type_eq.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)

Definition typesig := (list type * type)%type. (*funsig without the identifiers*)

Definition typesig_of_funsig (f:funsig):typesig := (map snd (fst f), snd f).

(* We define a generic funspec OFE with pre- and postconditions of arbitrary types, then specialize
   it to argsassert and assert. *)

Section ofe.

Context {PO QO : Type -> ofe}.

Inductive funspec_ :=
   mk_funspec (sig : typesig) (cc : calling_convention) (A : Type) (P : PO A) (Q : QO A).

(* funspec OFE -- needed to store funspecs in ghost state
   If we put funspecs in the FUN resource, we'd need an OFE for resource instead. *)
Local Instance funspec_dist : Dist funspec_ := λ n f1 f2,
  match f1, f2 with
  | mk_funspec sig1 cc1 A1 P1 Q1, mk_funspec sig2 cc2 A2 P2 Q2 =>
      sig1 = sig2 /\ cc1 = cc2 /\ existT A1 P1 ≡{n}≡ existT A2 P2 /\ existT A1 Q1 ≡{n}≡ existT A2 Q2
  end.

Local Instance funspec_equiv : Equiv funspec_ := λ f1 f2,
  match f1, f2 with
  | mk_funspec sig1 cc1 A1 P1 Q1, mk_funspec sig2 cc2 A2 P2 Q2 =>
      sig1 = sig2 /\ cc1 = cc2 /\ (existT A1 P1 ≡ existT A2 P2 /\ existT A1 Q1 ≡ existT A2 Q2)%stdpp
  end.

Lemma funspec_ofe_mixin : OfeMixin funspec_.
Proof.
  apply (iso_ofe_mixin (fun x => match x with mk_funspec sig cc A P Q =>
    (sig, cc, (existT A P, existT A Q)) : prodO (leibnizO _) _ end)).
  - intros [] []; split.
    + intros (? & ? & ?); subst; split; auto.
    + intros ([=] & ?); split3; auto.
  - intros ? [] []; split.
    + intros (? & ? & ?); subst; split; auto.
    + intros ([=] & ?); split3; auto.
Qed.
Canonical Structure funspecO := Ofe funspec_ funspec_ofe_mixin.

End ofe.
Global Arguments funspecO : clear implicits.

Section ofunctor.

Program Definition funspec_map {P1 P2 Q1 Q2 : Type → ofe} :
  (prodO (discrete_funO (λ A, P1 A -n> P2 A)) (discrete_funO (λ A, Q1 A -n> Q2 A))) -n>
  @funspecO P1 Q1 -n> @funspecO P2 Q2 :=
  λne '(Pf, Qf) fs, match fs with mk_funspec sig cc A P Q => mk_funspec sig cc A (Pf A P) (Qf A Q) end.
Next Obligation.
  intros ???? (PF, QF) ?? [=] n x y Heq; subst; simpl.
  destruct x, y as [?? A2 ??], Heq as (? & ? & HP & HQ); simpl in *.
  split3; auto; split; hnf; simpl.
  - destruct HP as (Heq & HP); exists Heq; simpl in *; subst; simpl in *; rewrite HP //.
  - destruct HQ as (Heq & HQ); exists Heq; simpl in *; subst; simpl in *; rewrite HQ //.
Qed.
Next Obligation.
  intros ???? n (PF, QF) (PF2, QF2) [HP HQ] [?????]; simpl in *.
  split3; auto.
  split; exists eq_refl; simpl; [apply HP | apply HQ].
Qed.

Program Definition funspecOF (POF QOF : Type -> oFunctor) : oFunctor := {|
    oFunctor_car A CA B CB := @funspecO (fun C => oFunctor_car (POF C) A B) (fun C => oFunctor_car (QOF C) A B);
    oFunctor_map A1 _ A2 _ B1 _ B2 _ fg := funspec_map (λ a, oFunctor_map (POF a) fg, λ a, oFunctor_map (QOF a) fg)
  |}.
Next Obligation.
  intros ?????????????? [?????]; simpl.
  split3; auto; split; exists eq_refl; solve_proper.
Qed.
Next Obligation.
  simpl; intros. destruct x as [?????].
  split3; auto; split; apply (existT_proper eq_refl), oFunctor_map_id.
Qed.
Next Obligation.
  simpl; intros. destruct x as [?????].
  split3; auto; split; apply (existT_proper eq_refl), oFunctor_map_compose.
Qed.

Global Instance funspecOF_contractive {POF QOF} :
    (∀ a, oFunctorContractive (POF a)) → (∀ a, oFunctorContractive (QOF a)) → oFunctorContractive (funspecOF POF QOF).
Proof.
  repeat intro. apply funspec_map; split; intros ?; exact: oFunctor_map_contractive.
Qed.

End ofunctor.
Global Arguments funspecOF _%OF _%OF.

Context {Σ : gFunctors}.

Lemma funspec_equivI PO QO (f1 f2 : @funspec_ PO QO) : (f1 ≡ f2 : iProp Σ) ⊣⊢ ∃ sig cc A P1 P2 Q1 Q2,
  ⌜f1 = mk_funspec sig cc A P1 Q1 ∧ f2 = mk_funspec sig cc A P2 Q2⌝ ∧ P1 ≡ P2 ∧ Q1 ≡ Q2.
Proof.
  ouPred.unseal; split=> n x ?.
  destruct f1, f2; split.
  - intros (<- & <- & HP & HQ).
    destruct HP as (HeqP & HP), HQ as (HeqQ & HQ); simpl in *.
    exists sig, cc, A, P, (eq_rect _ (fun A => PO A) P0 _ (eq_sym HeqP)), Q, (eq_rect _ (fun A => QO A) Q0 _ (eq_sym HeqQ)); repeat split.
    + subst; simpl in *. rewrite -eq_rect_eq //.
    + by subst.
    + clear dependent HeqP; by subst.
  - intros (? & ? & ? & ? & ? & ? & ? & ([=] & [=]) & ? & ?); subst.
    repeat match goal with H : existT _ _ = existT _ _ |- _ => apply inj_pair2 in H end; subst.
    split3; auto; split; exists eq_refl; done.
Qed.

(*Potential alternative that does not use Ctypes
Inductive funspec :=
   mk_funspec: AST.signature -> forall (A: TypeTree)
     (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: super_non_expansive P) (Q_ne: super_non_expansive Q),
    funspec.
 *)

(* assertions (environ -> mpred as pred) *)
Global Instance environ_inhabited : Inhabited environ := {| inhabitant := any_environ |}.

Definition environ_index : biIndex := {| bi_index_type := environ |}.

Definition assert' := environ -> iProp Σ.
Definition assert := monPred environ_index (iPropI Σ).

Program Definition assert_of (P : assert') : assert := {| monPred_at := P |}.

(* Does this do anything? *)
Global Coercion assert_of : assert' >-> assert.

(* Ideally, this would work. *)
Fail Lemma test : forall (P Q : assert'), P ∗ Q ⊢ Q ∗ P.

Global Instance argsEnviron_inhabited : Inhabited argsEnviron := {| inhabitant := (Map.empty _, nil) |}.

Definition argsEnviron_index : biIndex := {| bi_index_type := argsEnviron |}.

Definition argsassert' := argsEnviron -> iProp Σ.
Definition argsassert := monPred argsEnviron_index (iPropI Σ).

Program Definition argsassert_of (P : argsassert') : argsassert := {| monPred_at := P |}.

Coercion argsassert_of : argsassert' >-> argsassert.

Definition funspec := @funspec_ (fun A => A -d> argsassert) (fun A => A -d> assert).
Definition funspecO' := funspecO (fun A => A -d> argsEnviron -d> laterO (iProp Σ)) (fun A => A -d> environ -d> laterO (iProp Σ)).
Definition funspecOF' := funspecOF (fun A => A -d> argsEnviron -d> laterOF idOF)%OF (fun A => A -d> environ -d> laterOF idOF)%OF.

Definition funspec_unfold (f : funspec) : funspecO' :=
  match f with mk_funspec sig cc A P Q =>
    @mk_funspec (fun A => A -d> argsEnviron -d> laterO (iProp Σ)) (fun A => A -d> environ -d> laterO (iProp Σ)) sig cc A (fun x rho => Next (P x rho)) (fun x rho => Next (Q x rho))
  end.

Definition varspecs : Type := list (ident * type).

Definition funspecs := list (ident * funspec).


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

(* collect up all the ghost state required for the logic
   Should this include external state as well? *)
Class funspecGS Σ := FunspecG {
    funspec_inG :> inG Σ (gmap_viewR address (@funspecO' Σ));
    funspec_name : gname
}.

Class heapGS Σ := HeapGS {
  heapGS_wsatGS :> wsatGS Σ;
  heapGS_gen_heapGS :> gen_heapGS resource Σ;
  heapGS_funspecGS :> funspecGS Σ
}.

(* To use the heap, do Context `{!heapGS Σ}. *)

Definition rmap `{heapGS Σ} := iResUR Σ.
Definition mpred `{heapGS Σ} := iProp Σ.

Definition mem_auth `{heapGS Σ} m := resource_map.resource_map_auth(H0 := gen_heapGpreS_heap(gen_heapGpreS := gen_heap_inG)) (gen_heap_name heapGS_gen_heapGS) 1 m.


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
