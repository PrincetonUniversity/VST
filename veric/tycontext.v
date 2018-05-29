Require Import VST.msl.msl_standard.
Require Import VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.composite_compute.
Require Import VST.veric.align_mem.
Require Export VST.veric.lift.

Definition type_is_by_value t : bool :=
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
Variables (B : Type).

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
unfold get, set; intros; if_tac; intuition.
Qed.

Lemma grs h x : get (remove x h) x = None.
unfold get, remove; intros; if_tac; intuition.
Qed.

Lemma gro h x y : x<>y -> get (remove x h) y = get h y.
unfold get, remove; intros; if_tac; intuition.
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

(** Environment Definitions **)

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

Definition opt2list (A: Type) (x: option A) :=
  match x with Some a => a::nil | None => nil end.
Arguments opt2list [A] _.

Fixpoint typelist2list (tl: typelist) : list type :=
 match tl with Tcons t r => t::typelist2list r | Tnil => nil end.

Definition idset := PTree.t unit.

Definition idset0 : idset := PTree.empty _.
Definition idset1 (id: ident) : idset := PTree.set id tt idset0.
Definition insert_idset (id: ident) (S: idset) : idset :=
         PTree.set id tt S.

Fixpoint modifiedvars' (c: statement) (S: idset) : idset :=
 match c with
 | Sset id e => insert_idset id S
 | Sifthenelse _ c1 c2 => modifiedvars' c1 (modifiedvars' c2 S)
 | Scall (Some id) _ _ => insert_idset id S
 | Sbuiltin (Some id) _ _ _ => insert_idset id S
 | Ssequence c1 c2 =>  modifiedvars' c1 (modifiedvars' c2 S)
 | Sloop c1 c2 => modifiedvars' c1 (modifiedvars' c2 S)
 | Sswitch e cs => modifiedvars_ls cs S
 | Slabel _ c => modifiedvars' c S
 | _ => S
 end
 with
 modifiedvars_ls (cs: labeled_statements) (S: idset) : idset :=
 match cs with
 | LSnil => S
 | LScons _ c ls => modifiedvars' c (modifiedvars_ls ls S)
 end.

Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.
Definition isOK {A} (P: Errors.res A) := match P with Errors.OK _ => true | _ => false end.

Definition isSome_dec: forall {A} (P: option A), isSome P + ~ isSome P.
Proof.
  intros.
  destruct P; simpl; auto.
Defined.

Lemma modifiedvars'_union:
 forall id c S,
  isSome ((modifiedvars' c S) ! id) <->
  (isSome ((modifiedvars' c idset0) ! id ) \/ isSome (S ! id))
with modifiedvars_ls_union:
 forall id c S,
  isSome ((modifiedvars_ls c S) ! id) <->
  (isSome ((modifiedvars_ls c idset0) ! id ) \/ isSome (S ! id)).
Proof.
intro id.
 assert (IS0: ~ isSome (idset0 ! id)). unfold idset0, isSome.
 rewrite PTree.gempty; auto.
 induction c; try destruct o; simpl; intros;
 try solve [clear - IS0; intuition];
 try solve [unfold insert_idset; destruct (eq_dec i id);
  [subst; repeat rewrite PTree.gss; simpl; clear; intuition
  |  repeat rewrite PTree.gso by auto; simpl; clear - IS0; intuition ]];
 try solve [rewrite IHc1; rewrite IHc1 with (S := modifiedvars' c2 idset0);
                rewrite IHc2; clear - IS0; intuition].
 apply modifiedvars_ls_union.
 apply IHc.

intro id.
 assert (IS0: ~ isSome (idset0 ! id)). unfold idset0, isSome.
 rewrite PTree.gempty; auto.
 induction c; simpl; intros.
 clear - IS0; intuition.
 rewrite modifiedvars'_union.
 rewrite modifiedvars'_union with (S := modifiedvars_ls _ _).
 rewrite IHc. clear; intuition.
Qed.

Definition modifiedvars (c: statement) (id: ident) :=
   isSome ((modifiedvars' c idset0) ! id).

Definition type_of_global (ge: Clight.genv) (b: block) : option type :=
  match Genv.find_var_info ge b with
  | Some gv => Some gv.(gvar_info)
  | None =>
      match Genv.find_funct_ptr ge b with
      | Some fd => Some(type_of_fundef fd)
      | None => None
      end
  end.

Definition filter_genv (ge: Clight.genv) : genviron :=
    Genv.find_symbol ge.

Definition make_tenv (te : Clight.temp_env) : tenviron := fun id => PTree.get id te.

Definition make_venv (te : Clight.env) : venviron := fun id => PTree.get id te.

Definition construct_rho ge ve te:= mkEnviron ge (make_venv ve) (make_tenv te) .

Definition empty_environ (ge: Clight.genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).

Definition test := true.
Definition any_environ : environ :=
  mkEnviron (fun _ => None)  (Map.empty _) (Map.empty _).

(** Definitions related to function specifications and return assertions **)
Inductive exitkind : Type := EK_normal | EK_break | EK_continue | EK_return.

Instance EqDec_exitkind: EqDec exitkind.
Proof.
hnf. intros.
decide equality.
Defined.

Definition mpred := pred rmap.

Definition AssertTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType environ) Mpred).

Definition SpecTT (A: TypeTree): TypeTree :=
  ArrowType A (ArrowType (ConstType bool) (ArrowType (ConstType environ) Mpred)).

Definition super_non_expansive {A: TypeTree}
  (P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred): Prop :=
  forall n ts
    (x: functors.MixVariantFunctor._functor
                         (rmaps.dependent_type_functor_rec ts A) mpred)
    (rho: environ),
  approx n (P ts x rho) = approx n (P ts (fmap _ (approx n) (approx n) x) rho).

Definition const_super_non_expansive: forall (T: Type) P,
  @super_non_expansive (ConstType T) P :=
  fun _ _ _ _ _ _ => eq_refl.

Inductive funspec :=
   mk_funspec: funsig -> calling_convention -> forall (A: TypeTree)
     (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred)
     (P_ne: super_non_expansive P) (Q_ne: super_non_expansive Q),
     funspec.

(* Causes a universe inconsistency in seplog.v!
Definition example_f_spec :=
  (mk_funspec (nil,Tvoid) mpred (fun (x: mpred) rho => emp) (fun x rho => emp)).
*)

Definition varspecs : Type := list (ident * type).

Definition funspecs := list (ident * funspec).

Definition in_members i (m: members): Prop :=
  In i (map fst m).

Definition members_no_replicate (m: members) : bool :=
  compute_list_norepet (map fst m).

Definition compute_in_members id (m: members): bool :=
  id_in_list id (map fst m).

Lemma compute_in_members_true_iff: forall i m, compute_in_members i m = true <-> in_members i m.
Proof.
  intros.
  unfold compute_in_members.
  destruct (id_in_list i (map fst m)) eqn:HH;
  [apply id_in_list_true in HH | apply id_in_list_false in HH].
  + unfold in_members.
    tauto.
  + unfold in_members; split; [congruence | tauto].
Qed.

Lemma compute_in_members_false_iff: forall i m,
  compute_in_members i m = false <-> ~ in_members i m.
Proof.
  intros.
  pose proof compute_in_members_true_iff i m.
  rewrite <- H; clear H.
  destruct (compute_in_members i m); split; congruence.
Qed.

Ltac destruct_in_members i m :=
  let H := fresh "H" in
  destruct (compute_in_members i m) eqn:H;
    [apply compute_in_members_true_iff in H |
     apply compute_in_members_false_iff in H].

Lemma in_members_dec: forall i m, {in_members i m} + {~ in_members i m}.
Proof.
  intros.
  destruct_in_members i m; [left | right]; auto.
Qed.

Lemma size_chunk_sizeof: forall env t ch, access_mode t = By_value ch -> sizeof env t = Memdata.size_chunk ch.
Proof.
  intros.
  destruct t; inversion H.
  - destruct i, s; inversion H1; reflexivity.
  - destruct s; inversion H1; reflexivity.
  - destruct f; inversion H1; reflexivity.
  - inversion H1; reflexivity.
Qed.

Definition composite_legal_fieldlist (co: composite): Prop :=
  members_no_replicate (co_members co) = true.

Definition composite_env_legal_fieldlist env :=
  forall (id : positive) (co : composite),
    env ! id = Some co -> composite_legal_fieldlist co.

Class compspecs := mkcompspecs {
  cenv_cs : composite_env;
  cenv_consistent: composite_env_consistent cenv_cs;
  cenv_legal_fieldlist: composite_env_legal_fieldlist cenv_cs;
  cenv_legal_su: composite_env_complete_legal_cosu_type cenv_cs;
  ha_env_cs: PTree.t Z;
  ha_env_cs_consistent: hardware_alignof_env_consistent cenv_cs ha_env_cs;
  ha_env_cs_complete: hardware_alignof_env_complete cenv_cs ha_env_cs;
  la_env_cs: PTree.t legal_alignas_obs;
  la_env_cs_consistent: legal_alignas_env_consistent cenv_cs ha_env_cs la_env_cs;
  la_env_cs_complete: legal_alignas_env_complete cenv_cs la_env_cs;
  la_env_cs_sound: legal_alignas_env_sound cenv_cs ha_env_cs la_env_cs
}.

Existing Class composite_env.
Existing Instance cenv_cs.

Arguments sizeof {env} !t / .
Arguments alignof {env} !t / .

Arguments sizeof_pos {env} t _.
Arguments alignof_pos {env} t.

Arguments complete_legal_cosu_type {cenv} !t / .

(* TODO: handle other part of compspecs like this. *)
Goal forall {cs: compspecs} t, sizeof t >= 0.
Proof. intros. apply sizeof_pos.
Abort.

(*
Definition compspecs_program (p: program): compspecs.
  apply (mkcompspecs (prog_comp_env p)).
  eapply build_composite_env_consistent.
  apply (prog_comp_env_eq p).
Defined.
*)

Definition type_of_funspec (fs: funspec) : type :=
  match fs with mk_funspec fsig cc _ _ _ _ _ => Tfunction (type_of_params (fst fsig)) (snd fsig) cc end.

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

(** Declaration of type context for typechecking **)
Inductive tycontext : Type :=
  mk_tycontext : forall (tyc_temps: PTree.t (type * bool))
                        (tyc_vars: PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: PTree.t type)
                        (tyc_globsp: PTree.t funspec)
                        (tyc_annot: PTree.t Annotation),
                             tycontext.


Definition empty_tycontext : tycontext :=
  mk_tycontext (PTree.empty _) (PTree.empty _) Tvoid
         (PTree.empty _)  (PTree.empty _) (PTree.empty _).

Definition temp_types (Delta: tycontext): PTree.t (type*bool) :=
  match Delta with mk_tycontext a _ _ _ _ _ => a end.
Definition var_types (Delta: tycontext) : PTree.t type :=
  match Delta with mk_tycontext _ a _ _ _ _ => a end.
Definition ret_type (Delta: tycontext) : type :=
  match Delta with mk_tycontext _ _ a _ _ _ => a end.
Definition glob_types (Delta: tycontext) : PTree.t type :=
  match Delta with mk_tycontext _ _ _ a _ _ => a end.
Definition glob_specs (Delta: tycontext) : PTree.t funspec :=
  match Delta with mk_tycontext _ _ _ _ a _ => a end.
Definition annotations (Delta: tycontext) : PTree.t Annotation :=
  match Delta with mk_tycontext _ _ _ _ _ a => a end.

(** Functions that modify type environments **)
Definition initialized id (Delta: tycontext) : tycontext :=
match (temp_types Delta) ! id with
| Some (ty, _) => mk_tycontext (PTree.set id (ty,true) (temp_types Delta))
                       (var_types Delta) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta)
| None => Delta (*Shouldn't happen *)
end.

Definition join_te'  (te2 te : PTree.t (type * bool)) (id: positive) (val: type * bool) :=
   let (ty, assn) := val in
        match (te2 ! id) with
        | Some (ty2, assn2) => PTree.set id (ty, assn && assn2) te
        | None => te
        end.

Definition join_te te1 te2 : PTree.t (type * bool):=
PTree.fold (join_te' te2) te1 (PTree.empty (type * bool)).

Definition join_tycon (tycon1: tycontext) (tycon2 : tycontext) : tycontext :=
match tycon1 with  mk_tycontext te1 ve1 r vl1 g1 ann1 =>
match tycon2 with  mk_tycontext te2 _ _ _ _ _ =>
  mk_tycontext (join_te te1 te2) ve1 r vl1 g1 ann1
end end.
(*Print Clight.statement.*)
(** Strictly for updating the type context... no typechecking here **)
Fixpoint update_tycon (Delta: tycontext) (c: Clight.statement) {struct c} : tycontext :=
 match c with
 | Sskip | Scontinue | Sbreak => Delta
 | Sassign e1 e2 => Delta (*already there?*)
 | Sset id e2 => (initialized id Delta)
 | Ssequence s1 s2 => let Delta' := update_tycon Delta s1 in
                      update_tycon Delta' s2
 | Sifthenelse b s1 s2 => join_tycon (update_tycon Delta s1) (update_tycon Delta s2)
 | Sloop _ _ => Delta
 | Sswitch e ls => join_tycon_labeled ls Delta
 | Scall (Some id) _ _ => (initialized id Delta)
 | Slabel _ s => update_tycon Delta s
 | _ => Delta  (* et cetera *)
end

with join_tycon_labeled ls Delta :=
match ls with
| LSnil => Delta
| LScons int s ls' => join_tycon (update_tycon Delta s)
                      (join_tycon_labeled ls' Delta)
end.


(** Creates a typecontext from a function definition **)
(* NOTE:  params start out initialized, temps do not! *)

Definition make_tycontext_t (params: list (ident*type)) (temps : list(ident*type)) :=
fold_right (fun (param: ident*type) => PTree.set (fst param) (snd param, true))
 (fold_right (fun (temp : ident *type) tenv => let (id,ty):= temp in PTree.set id (ty,false) tenv)
  (PTree.empty (type * bool)) temps) params.

Definition make_tycontext_v (vars : list (ident * type)) :=
 fold_right (fun (var : ident * type) venv => let (id, ty) := var in PTree.set id ty venv)
   (PTree.empty type) vars.

Definition make_tycontext_g (V: varspecs) (G: funspecs) :=
 (fold_right (fun (var : ident * funspec) => PTree.set (fst var) (type_of_funspec (snd var)))
      (fold_right (fun (v: ident * type) => PTree.set (fst v) (snd v))
         (PTree.empty _) V)
            G).

(* Define it this way to have more control over unfolding *)
  Fixpoint ptree_set {A : Type} (i : positive) (v : A) (m : PTree.t A) {struct i} : PTree.t A :=
    match m with
    | PTree.Leaf =>
        match i with
        | xH => PTree.Node PTree.Leaf (Some v) PTree.Leaf
        | xO ii => PTree.Node (ptree_set ii v PTree.Leaf) None PTree.Leaf
        | xI ii => PTree.Node PTree.Leaf None (ptree_set ii v PTree.Leaf)
        end
    | PTree.Node l o r =>
        match i with
        | xH => PTree.Node l (Some v) r
        | xO ii => PTree.Node (ptree_set ii v l) o r
        | xI ii => PTree.Node l o (ptree_set ii v r)
        end
    end.

Goal forall A, @ptree_set A = @PTree.set _.  reflexivity. Qed.

(*Definition make_tycontext_s (G: funspecs) :=
 (fold_right (fun (var : ident * funspec) => PTree.set (fst var) (snd var))
            (PTree.empty _) G).
*)

(* Define it this way to have finer control over unfolding *)
Fixpoint make_tycontext_s (G: funspecs) :=
 match G with
 | nil => @PTree.Leaf funspec
 | b::r => let (id,f) := b in ptree_set id f (make_tycontext_s r)
 end.

Definition make_tycontext_a (anns : list (ident * Annotation)) :=
 fold_right (fun (ia : ident * Annotation) aenv => let (id, a) := ia in PTree.set id a aenv)
   (PTree.empty Annotation) anns.

Definition make_tycontext (params: list (ident*type)) (temps: list (ident*type)) (vars: list (ident*type))
                       (return_ty: type)
                       (V: varspecs) (G: funspecs) (A: list (ident*Annotation)):  tycontext :=
 mk_tycontext
   (make_tycontext_t params temps)
   (make_tycontext_v vars)
   return_ty
   (make_tycontext_g V G)
   (make_tycontext_s G)
   (make_tycontext_a A).

Definition func_tycontext' (func: function) (Delta: tycontext) : tycontext :=
 mk_tycontext
   (make_tycontext_t (fn_params func) (fn_temps func))
   (make_tycontext_v (fn_vars func))
   (fn_return func)
   (glob_types Delta)
   (glob_specs Delta)
   (annotations Delta).

Definition func_tycontext (func: function) (V: varspecs) (G: funspecs) (A:list (ident * Annotation)): tycontext :=
  make_tycontext (func.(fn_params)) (func.(fn_temps)) (func.(fn_vars)) (func.(fn_return)) V G A.

Definition nofunc_tycontext (V: varspecs) (G: funspecs) : tycontext :=
   make_tycontext nil nil nil Tvoid V G nil.

Definition exit_tycon (c: statement) (Delta: tycontext) (ek: exitkind) : tycontext :=
  match ek with
  | EK_normal => update_tycon Delta c
  | _ => Delta
  end.

Lemma join_te_eqv :forall te1 te2 id b1 b2 t1,
te1 ! id = Some (t1, b1) -> te2 ! id = Some (t1, b2) ->
(join_te te1 te2) ! id = Some (t1,andb b1 b2).
Proof.
intros.
unfold join_te. rewrite PTree.fold_spec. rewrite <- fold_left_rev_right.
assert (forall t : type * bool, In (id, t) (rev (PTree.elements te1)) -> te1 ! id = Some t).
intros. apply PTree.elements_complete. apply in_rev. auto.
assert (forall t, te1 ! id = Some t -> In (id, t) (rev (PTree.elements te1))).
intros. apply In_rev. rewrite rev_involutive. apply PTree.elements_correct.
auto.

induction (rev (PTree.elements te1)). simpl in *.
apply H2 in H. inv H.

simpl in *. destruct a. simpl in *. destruct p0. simpl.
remember (te2 ! p). destruct o. destruct p0.
(* destruct (eq_dec t t0).
 subst. *)
rewrite PTree.gsspec. if_tac. subst. specialize (H1 (t,b)).
spec H1; [solve [auto] | ].
inversion2  H H1.
rewrite H0 in Heqo; inv Heqo. auto.
apply IHl; auto.
intros. inversion2 H H4. specialize (H2 _ H).
destruct H2. inv H2. congruence.  auto.
apply IHl; auto; intros. rewrite H in *. inv H3. specialize (H2 (t1, b1)).
intuition. inv H2. congruence.
Qed.

Lemma temp_types_same_type : forall id i t b Delta,
(temp_types Delta) ! id = Some (t, b) ->
exists b0 : bool,
  (temp_types (initialized i Delta)) ! id = Some (t, b || b0).
Proof.
intros.
unfold initialized.
remember ((temp_types Delta) ! i). destruct o.
destruct p. unfold temp_types in *. simpl. rewrite PTree.gsspec.
if_tac. subst. rewrite H in *. inv Heqo. exists true.   rewrite orb_true_r.
eauto. exists false.   rewrite orb_false_r. eauto. exists false. rewrite orb_false_r.
auto.
Qed.

Lemma temp_types_update_dist : forall d1 d2 ,
(temp_types (join_tycon (d1) (d2))) =
join_te (temp_types (d1)) (temp_types (d2)).
Proof.
intros.
destruct d1; destruct d2.
simpl. unfold temp_types. simpl. auto.
Qed.

Lemma var_types_update_dist : forall d1 d2 ,
(var_types (join_tycon (d1) (d2))) =
(var_types (d1)).
Proof.
intros.
destruct d1; destruct d2.
simpl. unfold var_types. simpl. auto.
Qed.

Lemma ret_type_update_dist : forall d1 d2,
(ret_type (join_tycon (d1) (d2))) =
(ret_type (d1)).
Proof.
intros.
destruct d1; destruct d2.
simpl. unfold var_types. simpl. auto.
Qed.

Lemma glob_types_update_dist :
forall d1 d2,
(glob_types (join_tycon (d1) (d2))) =
(glob_types (d1)).
Proof.
intros. destruct d1. destruct d2.  simpl. auto.
Qed.

Lemma glob_specs_update_dist :
forall d1 d2,
(glob_specs (join_tycon (d1) (d2))) =
(glob_specs (d1)).
Proof.
intros. destruct d1. destruct d2.  simpl. auto.
Qed.

Lemma func_tycontext'_update_dist :
forall f d1 d2,
(func_tycontext' f (join_tycon (d1) (d2))) =
(func_tycontext' f (d1)).
Proof.
  intros. destruct d1. destruct d2.  simpl. auto.
Qed.

Lemma var_types_update_tycon:
  forall c Delta, var_types (update_tycon Delta c) = var_types Delta
with
var_types_join_labeled : forall l Delta,
var_types (join_tycon_labeled l Delta) = var_types Delta.
Proof.
assert (forall i Delta, var_types (initialized i Delta) = var_types Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); try destruct p; reflexivity.
destruct c; intros; simpl; try reflexivity.
apply H.
destruct o. apply H. auto.
rewrite var_types_update_tycon. apply var_types_update_tycon.

rewrite var_types_update_dist. apply var_types_update_tycon.
apply var_types_join_labeled.

apply var_types_update_tycon.

intros. destruct l. simpl. auto.

simpl. rewrite var_types_update_dist.
rewrite var_types_update_tycon. reflexivity.
Qed.

Lemma glob_types_update_tycon:
  forall c Delta, glob_types (update_tycon Delta c) = glob_types Delta
 with
glob_types_join_labeled : forall Delta e l,
glob_types (update_tycon Delta (Sswitch e l)) = glob_types Delta.
Proof.
clear glob_types_update_tycon.
assert (forall i Delta, glob_types (initialized i Delta) = glob_types Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); try destruct p; reflexivity.
induction c; intros; try apply H; try reflexivity.
simpl. destruct o. apply H. auto.
simpl.
rewrite IHc2.
auto.

simpl.  rewrite glob_types_update_dist. auto.

auto.

simpl; auto.

clear glob_types_join_labeled.
intros. simpl.
destruct l. simpl. auto.
simpl in *. rewrite glob_types_update_dist.
auto.
Qed.

Lemma glob_specs_update_tycon:
  forall c Delta, glob_specs (update_tycon Delta c) = glob_specs Delta
 with
glob_specs_join_labeled : forall Delta e l,
glob_specs (update_tycon Delta (Sswitch e l)) = glob_specs Delta.
Proof.
clear glob_specs_update_tycon.
assert (forall i Delta, glob_specs (initialized i Delta) = glob_specs Delta).
intros; unfold initialized.
destruct ((temp_types Delta)!i); try destruct p; reflexivity.
induction c; intros; try apply H; try reflexivity.
simpl. destruct o. apply H. auto.
simpl.
rewrite IHc2.
auto.

simpl.  rewrite glob_specs_update_dist. auto.

auto.

simpl; auto.

clear glob_specs_join_labeled.
intros. simpl.
destruct l. simpl. auto.
simpl in *. rewrite glob_specs_update_dist.
auto.
Qed.

Lemma ret_type_join_tycon:
  forall Delta Delta', ret_type (join_tycon Delta Delta') = ret_type Delta.
Proof.
 intros; destruct Delta, Delta'; reflexivity.
Qed.

Lemma ret_type_update_tycon:
  forall Delta c, ret_type (update_tycon Delta c) = ret_type Delta
with ret_type_join_tycon_labeled: forall l Delta,
  ret_type (join_tycon_labeled l Delta) = ret_type Delta.
Proof.
  intros. revert Delta; induction c; simpl; intros; try destruct o; auto;
 try (unfold initialized;  destruct ((temp_types Delta)!i); try destruct p; auto).
 rewrite IHc2; auto.
 rewrite ret_type_join_tycon. auto.

 induction l; simpl; intros; auto. rewrite ret_type_join_tycon. auto.
Qed.

Lemma func_tycontext'_update_tycon: forall Delta c f,
  func_tycontext' f (update_tycon Delta c) = func_tycontext' f Delta
with func_tycontext'_join_labeled: forall Delta l f,
  func_tycontext' f (join_tycon_labeled l Delta) = func_tycontext' f Delta.
Proof.
+ clear func_tycontext'_update_tycon.
  assert (forall i f Delta, func_tycontext' f (initialized i Delta) = func_tycontext' f Delta).
  intros; unfold initialized.
  destruct ((temp_types Delta)!i); try destruct p; reflexivity.
  intros; revert Delta; induction c; intros; try apply H; try reflexivity.
  simpl. destruct o. apply H. auto.
  simpl.
  rewrite IHc2.
  auto.
  simpl.  rewrite func_tycontext'_update_dist. auto.
  apply func_tycontext'_join_labeled.
  simpl; auto.
+ clear func_tycontext'_join_labeled.
  intros. simpl.
  destruct l. simpl. auto.
  simpl in *. rewrite func_tycontext'_update_dist.
  auto.
Qed.

Lemma ret_type_exit_tycon:
  forall c Delta ek, ret_type (exit_tycon c Delta ek) = ret_type Delta.
Proof.
 destruct ek; try reflexivity. unfold exit_tycon. apply ret_type_update_tycon.
Qed.

Ltac try_false :=
try  solve[exists false; rewrite orb_false_r; eauto].

Lemma update_tycon_te_same : forall c Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b2, (temp_types (update_tycon Delta c)) ! id = Some (t,b || b2)

with update_labeled_te_same : forall ls Delta id t b,
(temp_types Delta) ! id = Some (t,b) ->
exists b2, (temp_types (join_tycon_labeled ls Delta)) ! id = Some (t,b || b2) .
Focus 1.
destruct c; intros; simpl; try_false.

simpl. eapply temp_types_same_type; eauto.

simpl. destruct o; eauto. simpl. eapply temp_types_same_type; eauto.
try_false; eauto.

assert (forall (c : statement) (Delta : tycontext)
                         (id : positive) (t : type) (b : bool),
                       (temp_types Delta) ! id = Some (t, b) ->
                       exists b2 : bool,
                         (temp_types (update_tycon Delta c)) ! id =
                         Some (t, b || b2)) by auto.
edestruct update_tycon_te_same. apply H.
specialize (update_tycon_te_same c2 _ _ _ _ H1).
destruct (update_tycon_te_same). exists (x || x0). rewrite orb_assoc. eauto.


simpl. rewrite temp_types_update_dist.

edestruct (update_tycon_te_same c1). apply H.
edestruct (update_tycon_te_same c2). apply H.
erewrite join_te_eqv;
eauto. exists (x && x0). rewrite orb_andb_distrib_r.  auto.

apply update_labeled_te_same.  exact H.  (*these are the problem if it won't qed*)

simpl; auto.

intros. destruct ls. simpl. exists false.
rewrite H. f_equal. f_equal. destruct b; reflexivity.

simpl. rewrite temp_types_update_dist.
edestruct update_tycon_te_same. apply H.
edestruct update_labeled_te_same. apply H.
exists (x && x0).
erewrite join_te_eqv. rewrite <- orb_andb_distrib_r. auto.
eauto. eauto. Qed.

Lemma set_temp_ve : forall Delta i,
var_types (initialized i Delta) = var_types (Delta).
Proof.
intros. destruct Delta. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (tyc_temps ! i); auto. destruct p; auto.
Qed.

Lemma set_temp_ge : forall Delta i,
glob_types (initialized i Delta) = glob_types (Delta).
Proof.
intros. destruct Delta. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (tyc_temps ! i); auto. destruct p; auto.
Qed.

Lemma set_temp_gs : forall Delta i,
glob_specs (initialized i Delta) = glob_specs (Delta).
Proof.
intros. destruct Delta. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (tyc_temps ! i); auto. destruct p; auto.
Qed.

Lemma set_temp_ret : forall Delta i,
ret_type (initialized i Delta) = ret_type (Delta).
intros.
destruct Delta. unfold var_types. unfold initialized.
simpl. unfold temp_types. simpl. destruct (tyc_temps ! i); auto. destruct p; auto.
Qed.

Lemma update_tycon_eqv_ve : forall Delta c id,
(var_types (update_tycon Delta c)) ! id = (var_types (Delta)) ! id

with update_le_eqv_ve : forall (l : labeled_statements) (id : positive) Delta,
(var_types (join_tycon_labeled l Delta)) ! id =
(var_types Delta) ! id.
Proof.
intros;
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ve. auto.
destruct o. rewrite set_temp_ve. auto.
auto.
rewrite update_tycon_eqv_ve. apply update_tycon_eqv_ve.

rewrite var_types_update_dist.
rewrite update_tycon_eqv_ve. auto.

erewrite update_le_eqv_ve. auto.

auto.
 
intros.
 destruct l. simpl in *. auto.
 simpl in *. rewrite var_types_update_dist.
rewrite update_tycon_eqv_ve. auto.
Qed.

Lemma update_tycon_eqv_ret : forall Delta c,
(ret_type (update_tycon Delta c)) = (ret_type (Delta))

with update_le_eqv_ret : forall (l : labeled_statements)  Delta,
(ret_type (join_tycon_labeled l Delta)) =
(ret_type Delta).
Proof.
intros;
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ret. auto.
destruct o. rewrite set_temp_ret. auto.
auto.
rewrite update_tycon_eqv_ret. apply update_tycon_eqv_ret.

rewrite ret_type_update_dist.
rewrite update_tycon_eqv_ret. auto.

rewrite update_le_eqv_ret. auto.

auto.

intros.
 destruct l. simpl in *.
reflexivity.
 simpl in *. rewrite ret_type_update_dist.
rewrite update_tycon_eqv_ret. auto.
Qed.


Lemma update_tycon_same_ve : forall Delta c id v,
(var_types (update_tycon Delta c)) ! id = Some v <->
(var_types (Delta)) ! id = Some v


with update_le_same_ve : forall (l : labeled_statements) (id : positive) (v : type) Delta,
(var_types (join_tycon_labeled l Delta)) ! id = Some v <->
(var_types Delta) ! id = Some v.
Proof.
intros; split; intros;
rewrite update_tycon_eqv_ve in *; auto.
intros; split; intros;
rewrite update_le_eqv_ve in *; auto.
Qed.


Lemma update_tycon_eqv_ge : forall Delta c id,
(glob_types (update_tycon Delta c)) ! id = (glob_types (Delta)) ! id

with update_le_eqv_ge : forall (l : labeled_statements) (id : positive)  Delta,
(glob_types (join_tycon_labeled l Delta)) ! id =
(glob_types Delta) ! id.
Proof.
intros;
destruct c; simpl in *; try reflexivity.
rewrite set_temp_ge. auto.
destruct o. rewrite set_temp_ge. auto.
auto.
rewrite update_tycon_eqv_ge. apply update_tycon_eqv_ge.

rewrite glob_types_update_dist.
rewrite update_tycon_eqv_ge. auto.
erewrite update_le_eqv_ge. auto.

auto. 

intros.
 destruct l. simpl in *.
auto.
simpl in *. rewrite glob_types_update_dist.
rewrite update_tycon_eqv_ge. auto.
Qed.


Lemma update_tycon_eqv_gs : forall Delta c id,
(glob_specs (update_tycon Delta c)) ! id = (glob_specs (Delta)) ! id

with update_le_eqv_gs : forall (l : labeled_statements) (id : positive)  Delta,
(glob_specs (join_tycon_labeled l Delta)) ! id =
(glob_specs Delta) ! id.
Proof.
intros;
destruct c; simpl in *; try reflexivity.
rewrite set_temp_gs. auto.
destruct o. rewrite set_temp_gs. auto.
auto.
rewrite update_tycon_eqv_gs. apply update_tycon_eqv_gs.

rewrite glob_specs_update_dist.
rewrite update_tycon_eqv_gs. auto.
erewrite update_le_eqv_gs. auto.

auto.

intros.
 destruct l. simpl in *.
auto.
simpl in *. rewrite glob_specs_update_dist.
rewrite update_tycon_eqv_gs. auto.
Qed.


Lemma update_tycon_same_ge : forall Delta c id v,
(glob_types (update_tycon Delta c)) ! id = Some v <->
(glob_types (Delta)) ! id = Some v


with update_le_same_ge : forall (l : labeled_statements) (id : positive) (v : type) Delta,
(glob_types (join_tycon_labeled l Delta)) ! id = Some v <->
(glob_types Delta) ! id = Some v.
Proof.
intros; split; intros;
rewrite update_tycon_eqv_ge in *; auto.
intros; split; intros;
rewrite update_le_eqv_ge in *; auto.
Qed.

Lemma update_tycon_same_gs : forall Delta c id v,
(glob_specs (update_tycon Delta c)) ! id = Some v <->
(glob_specs (Delta)) ! id = Some v


with update_le_same_gs : forall (l : labeled_statements) (id : positive) v  Delta,
(glob_specs (join_tycon_labeled l Delta)) ! id = Some v <->
(glob_specs Delta) ! id = Some v.
Proof.
intros; split; intros;
rewrite update_tycon_eqv_gs in *; auto.
intros; split; intros;
rewrite update_le_eqv_gs in *; auto.
Qed.

Lemma list_norepet_rev:
  forall A (l: list A), list_norepet (rev l) = list_norepet l.
Proof.
induction l; simpl; auto.
apply prop_ext; split; intros.
apply list_norepet_app in H.
destruct H as [? [? ?]].
rewrite IHl in H.
constructor; auto.
eapply list_disjoint_notin with (a::nil).
apply list_disjoint_sym; auto.
intros x y ? ? ?; subst.
contradiction (H1 y y); auto.
rewrite <- In_rev; auto.
simpl; auto.
rewrite list_norepet_app.
inv H.
split3; auto.
rewrite IHl; auto.
repeat constructor.
intro Hx. inv Hx.
intros x y ? ? ?; subst.
inv H0.
rewrite <- In_rev in H; contradiction.
auto.
Qed.

Definition sub_option {A} (x y: option A) :=
 match x with Some x' => y = Some x' | None => True end.

Lemma sub_option_eqv: forall {A} (x y: option A),
  x = y <-> sub_option x y /\ sub_option y x.
Proof.
  intros.
  destruct x, y; split; intros; try congruence.
  + inversion H.
    simpl.
    split; reflexivity.
  + simpl in H; destruct H.
    inversion H.
    reflexivity.
  + simpl in H; destruct H.
    inversion H.
  + simpl in H; destruct H.
    inversion H0.
  + simpl.
    tauto.
Qed.

Lemma sub_option_refl: forall {A} (x: option A), sub_option x x.
Proof.
  intros.
  destruct x; simpl.
  + reflexivity.
  + exact I.
Qed.

Lemma sub_option_trans: forall {A} (x y z: option A), sub_option x y -> sub_option y z -> sub_option x z.
Proof.
  intros.
  destruct x, y, z;
  inversion H;
  subst;
  inversion H0;
  subst.
  + reflexivity.
  + exact I.
  + exact I.
  + exact I.
Qed.

Lemma sub_option_spec: forall {A} (T1 T2: PTree.t A),
  (forall id, sub_option (T1 ! id) (T2 ! id)) ->
  forall id co, T1 ! id = Some co -> T2 ! id = Some co.
Proof.
  intros.
  specialize (H id).
  destruct (T1 ! id), (T2 ! id); inversion H; inversion H0.
  reflexivity.
Qed.

Definition Annotation_sub (A1 A2: option Annotation):Prop := 
  match A1, A2 with
    _, None => True
  | Some (StrongAnnotation _), Some (WeakAnnotation _) => True
  | Some (StrongAnnotation X), Some (StrongAnnotation Y) => X=Y (*maybe have entailment here?*)
  | X, Y => X=Y 
  end.

Lemma Annotation_sub_trans a1 a2 a3: Annotation_sub a1 a2 -> 
      Annotation_sub a2 a3 -> Annotation_sub a1 a3.
Proof. unfold Annotation_sub.
  destruct a1; destruct a2.
+ destruct a; destruct a0; simpl; intros.
  - inv H; trivial.
  - inv H. 
  - destruct a3; trivial. inv H0; trivial.
  - subst. trivial.
+ destruct a; trivial; intros; destruct a3; trivial; discriminate.
+ discriminate.
+ trivial.
Qed.

Lemma Annotation_sub_refl a: Annotation_sub a a. 
Proof. unfold Annotation_sub. destruct a; trivial. destruct a; trivial. Qed.

Lemma Annotation_sub_antisymm a b: Annotation_sub a b -> Annotation_sub b a -> a=b.
Proof. intros.
destruct a; destruct b; simpl in *; trivial; try discriminate.
destruct a; destruct a0; subst; trivial. inv H0; trivial. 
Qed.

Definition tycontext_sub (Delta Delta' : tycontext) : Prop :=
 (forall id, match (temp_types Delta) ! id,  (temp_types Delta') ! id with
                 | None, _ => True
                 | Some (t,b), None => False
                 | Some (t,b), Some (t',b') => t=t' /\ orb (negb b) b' = true
                end)
 /\ (forall id, (var_types Delta) ! id = (var_types Delta') ! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, sub_option ((glob_types Delta) ! id) ((glob_types Delta') ! id))
 /\ (forall id, sub_option ((glob_specs Delta) ! id) ((glob_specs Delta') ! id))
 /\ (forall id, Annotation_sub ((annotations Delta) ! id) ((annotations Delta') ! id)).

Definition tycontext_eqv (Delta Delta' : tycontext) : Prop :=
 (forall id, (temp_types Delta) ! id = (temp_types Delta') ! id)
 /\ (forall id, (var_types Delta) ! id = (var_types Delta') ! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, (glob_types Delta) ! id = (glob_types Delta') ! id)
 /\ (forall id, (glob_specs Delta) ! id = (glob_specs Delta') ! id)
 /\ (forall id, (annotations Delta) ! id = (annotations Delta') ! id).

Lemma join_tycon_same: forall Delta, tycontext_eqv (join_tycon Delta Delta) Delta.
Proof.
 intros.
 destruct Delta.
 unfold join_tycon.
 repeat split; auto.
 intros. unfold temp_types. simpl.
 unfold join_te.
 rewrite PTree.fold_spec.
 rewrite <- fold_left_rev_right.
 case_eq (tyc_temps ! id); intros.
 pose proof (PTree.elements_correct _ _ H).
 pose proof (PTree.elements_keys_norepet tyc_temps).
 rewrite in_rev in H0.
 rewrite <- list_norepet_rev in H1. rewrite <- map_rev in H1.
 change PTree.elt with positive in *.
 revert H0 H1; induction (rev (PTree.elements tyc_temps)); intros.
 inv H0.
 inv H1.
 simpl in H0. destruct H0. subst a.
 simpl. unfold join_te'. destruct p. rewrite H. rewrite andb_diag.
 rewrite PTree.gss.
 destruct b; simpl ;auto.
 simpl. unfold join_te' at 1. destruct a. simpl. destruct p1. simpl in H4.
 case_eq (tyc_temps ! p0);intros. destruct p1.
 rewrite PTree.gso. auto.
 intro; subst p0. apply H4. change id with (fst (id,p)). apply in_map; auto.
 auto.
 assert (~ In id (map fst (PTree.elements tyc_temps))).
 intro. apply in_map_iff in H0. destruct H0 as [[id' v] [? ?]]. simpl in *; subst id'.
 apply PTree.elements_complete in H1. congruence.
 rewrite in_rev in H0. rewrite <- map_rev in H0.
 revert H0; induction (rev (PTree.elements tyc_temps)); intros. simpl. rewrite PTree.gempty; auto.
 simpl. destruct a. simpl. unfold join_te' at 1. destruct p0.
 destruct (eq_dec p id). subst p. rewrite  H. apply IHl; auto.
 contradict H0; simpl; auto.
 case_eq (tyc_temps ! p); intros. destruct p0.
 rewrite PTree.gso.
 apply IHl. contradict H0;simpl; auto.
 intro; subst p; congruence.
 apply IHl. contradict H0;simpl; auto.
Qed.

Lemma tycontext_eqv_spec: forall Delta Delta',
  tycontext_eqv Delta Delta' <-> tycontext_sub Delta Delta' /\ tycontext_sub Delta' Delta.
Proof.
  intros.
  unfold tycontext_sub, tycontext_eqv.
  split; [intros [? [? [? [? [? ?]]]]] | intros [[? [? [? [? [? ?]]]]] [? [? [? [? [? ?]]]]]]];
  repeat split; intros;
  try assumption;
  try (symmetry; assumption);
  try
  solve [
    apply sub_option_eqv;
    try split;
    try rewrite H; try rewrite H0; try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4;
    try apply sub_option_refl; try reflexivity;
    auto
    ].
  + clear - H.
    specialize (H id).
    destruct ((temp_types Delta) ! id) as [[? ?] |], ((temp_types Delta') ! id) as [[? ?] |];
    inversion H.
    destruct b0; split; simpl; auto.
    exact I.
  + rewrite H4. apply Annotation_sub_refl.
  + clear - H.
    specialize (H id).
    destruct ((temp_types Delta) ! id) as [[? ?] |], ((temp_types Delta') ! id) as [[? ?] |];
    inversion H.
    destruct b0; split; simpl; auto.
    exact I.
  + rewrite H4. apply Annotation_sub_refl. 
  + clear - H H5.
    specialize (H id).
    specialize (H5 id).
    destruct ((temp_types Delta) ! id) as [[? ?] |], ((temp_types Delta') ! id) as [[? ?] |];
    inversion H; inversion H5.
    - clear H2; subst.
      destruct b, b0; try inversion H1; try inversion H3; reflexivity.
    - reflexivity.
  + clear - H4 H10. apply Annotation_sub_antisymm; auto.
Qed.

Lemma tycontext_sub_refl:
 forall Delta, tycontext_sub Delta Delta.
Proof.
  intros. destruct Delta as [T V r G S].
  unfold tycontext_sub.
  intuition.
  + unfold sub_option. unfold temp_types. simpl.
    destruct (T ! id) as [[? ?]|]; split; auto; destruct b; auto.
  + apply sub_option_refl.
  + apply sub_option_refl.
  + apply Annotation_sub_refl.
Qed.

Lemma tycontext_sub_trans:
 forall Delta1 Delta2 Delta3,
  tycontext_sub Delta1 Delta2 -> tycontext_sub Delta2 Delta3 ->
  tycontext_sub Delta1 Delta3.
Proof.
  intros ? ? ? [G1 [G2 [G3 [G4 [G5 G6]]]]] [H1 [H2 [H3 [H4 [H5 H6]]]]].
  repeat split.
  * intros. specialize (G1 id); specialize (H1 id).
    destruct ((temp_types Delta1) ! id); auto.
    destruct p. destruct ((temp_types Delta2) ! id);
      try contradiction. destruct p.
    destruct ((temp_types Delta3) ! id); try contradiction.
    destruct p. destruct G1, H1; split; subst; auto.
    destruct (negb  b); inv H0; simpl; auto.
    destruct b0; inv H; simpl in H4. auto.
  * intros. specialize (G2 id); specialize (H2 id); congruence.
  * congruence.
  * intros. eapply sub_option_trans; eauto.
  * intros. eapply sub_option_trans; eauto.
  * intros. eapply Annotation_sub_trans; eauto.
Qed.

Lemma initialized_ne : forall Delta id1 id2,
id1 <> id2 ->
(temp_types Delta) ! id1 = (temp_types (initialized id2 Delta)) ! id1.

intros.
destruct Delta. unfold temp_types; simpl.
unfold initialized. simpl. unfold temp_types; simpl.
destruct (tyc_temps ! id2). destruct p. simpl.  rewrite PTree.gso; auto.
auto.
Qed.

Definition te_one_denote (v1 v2 : option (type * bool)):=
match v1, v2 with
| Some (t1,b1),Some (t2, b2) =>  Some (t1, andb b1 b2)
| _, _ => None
end.

Lemma join_te_denote2:
forall d1 d2 id,
  ((join_te d1 d2) ! id) = te_one_denote (d1 ! id) (d2 ! id).
Proof.
intros.
unfold join_te. rewrite PTree.fold_spec.
remember (PTree.elements d1) as el eqn:?H.
unfold te_one_denote.
 rewrite <- fold_left_rev_right.
 pose proof (PTree.elements_keys_norepet d1).
 rewrite <- list_norepet_rev in H0.
  rewrite <- map_rev in H0.

destruct (d1 ! id) as [[t b] | ] eqn:?; auto.
*
 apply PTree.elements_correct in Heqo.
 rewrite <- H in *.
  apply in_rev in Heqo. unfold PTree.elt in *.
   forget (rev el) as al.  clear H el d1.
 set (f := (fun (y : positive * (type * bool)) (x : PTree.t (type * bool)) =>
    join_te' d2 x (fst y) (snd y))).
 induction al; destruct Heqo.
 + subst a. simpl in H0.
   unfold f; simpl. destruct (d2 ! id) as [[t2 b2] | ] eqn:?H.
   fold f. rewrite PTree.gss. auto.
   fold f. inv H0.
   clear - H H3; induction al; simpl. apply PTree.gempty.
  unfold f at 1. unfold join_te'.
  destruct a as [? [? ?]]. simpl.
  destruct (d2 ! p) as [[? ?] |]. rewrite PTree.gso. apply IHal.
 contradict H3. right; auto.
 contradict H3. left; auto.
 apply IHal.
 contradict H3; right; auto.
 + inv H0. specialize (IHal H4 H).
 simpl. unfold f at 1. unfold join_te'.
 destruct a as [? [? ?]]; simpl. destruct (d2 ! p) as [[? ?] | ].
  rewrite PTree.gso. apply IHal.
 contradict H3. subst p; clear - H. simpl.
 change id with (fst (id,(t,b))).
 apply in_map; auto.
 auto.
*
 assert (~ In id (map fst (rev el))).
 intro. rewrite map_rev in H1. rewrite <- In_rev in H1. subst el.
 apply list_in_map_inv in H1. destruct H1 as [[? ?] [? ?]].
 simpl in H. subst p. destruct p0 as [? ?].
 pose proof (PTree.elements_complete d1 id (t,b) H1). congruence.
 clear - H1.
 induction (rev el); simpl. apply PTree.gempty.
 unfold join_te' at 1. destruct a. simpl. destruct p0.
 destruct (d2 ! p). destruct p0. rewrite PTree.gso. apply IHl.
 contradict H1. right; auto.
 contradict H1. left; auto.
 apply IHl. contradict H1. right; auto.
Qed.

Lemma temp_types_same_type' : forall i (Delta: tycontext),
 (temp_types (initialized i Delta)) ! i =
  match (temp_types Delta) ! i with
   | Some (t, b) => Some (t, true)
  | None => None
  end.
Proof.
intros.
unfold initialized.
destruct ((temp_types Delta) ! i) as [[? ?]|] eqn:?.
unfold temp_types at 1. simpl. rewrite PTree.gss. auto.
auto.
Qed.

Definition binop_stable cenv op a1 a2 : bool :=
match op with
  | Cop.Oadd => match Cop.classify_add (typeof a1) (typeof a2) with
                    | Cop.add_case_pi t _ => complete_type cenv t
                    | Cop.add_case_ip _ t => complete_type cenv t
                    | Cop.add_case_pl t => complete_type cenv t
                    | Cop.add_case_lp t => complete_type cenv t
                    | Cop.add_default => true
            end
  | Cop.Osub => match Cop.classify_sub (typeof a1) (typeof a2) with
                    | Cop.sub_case_pi t _ => complete_type cenv t
                    | Cop.sub_case_pl t => complete_type cenv t
                    | Cop.sub_case_pp t => complete_type cenv t
                    | Cop.sub_default => true
            end
  | _ => true
  end.

Section STABILITY.

Variables env env': composite_env.
Hypothesis extends: forall id co, env!id = Some co -> env'!id = Some co.

Lemma binop_stable_stable: forall b e1 e2,
  binop_stable env b e1 e2 = true ->
  binop_stable env' b e1 e2 = true.
Proof.
  intros.
  destruct b; unfold binop_stable in H |- *; auto.
  + destruct (Cop.classify_add (typeof e1) (typeof e2));
    try (eapply (complete_type_stable env env'); eauto).
     auto.
  + destruct (Cop.classify_sub (typeof e1) (typeof e2));
    try (eapply (complete_type_stable env env'); eauto).
     auto.
Qed.

Lemma Cop_Sem_add_ptr_int_stable ty si u v (H:complete_type env ty = true):
  Cop.sem_add_ptr_int env ty si u v =
  Cop.sem_add_ptr_int env' ty si u v.
Proof. unfold Cop.sem_add_ptr_int.
  destruct u; destruct v; trivial; erewrite <- sizeof_stable; eauto.
Qed.

Lemma Cop_Sem_add_ptr_long_stable ty u v (H:complete_type env ty = true):
  Cop.sem_add_ptr_long env ty u v =
  Cop.sem_add_ptr_long env' ty u v.
Proof. unfold Cop.sem_add_ptr_long.
  destruct u; destruct v; trivial; erewrite <- sizeof_stable; eauto.
Qed.

Lemma Cop_sem_binary_operation_stable:
  forall b v1 e1 v2 e2 m,
  binop_stable env b e1 e2 = true ->
  Cop.sem_binary_operation env b v1 (typeof e1) v2 (typeof e2) m =
    Cop.sem_binary_operation env' b v1 (typeof e1) v2 (typeof e2) m.
Proof.
  intros.
  unfold binop_stable in H.
  destruct b; try auto.
  + simpl.
    unfold Cop.sem_add.
    destruct (Cop.classify_add (typeof e1) (typeof e2)), v1, v2;
    try (erewrite <- Cop_Sem_add_ptr_int_stable; eauto);
    try (erewrite <- Cop_Sem_add_ptr_long_stable; eauto);
(*    try (eapply (complete_type_stable env env'); eauto);*)
    try erewrite <- sizeof_stable; eauto.
  + simpl.
    unfold Cop.sem_sub.
    destruct (Cop.classify_sub (typeof e1) (typeof e2)), v1, v2;
    try erewrite <- sizeof_stable; eauto.
Qed.

Lemma field_offset_stable: forall i id co ofs,
  composite_env_consistent env ->
  env ! i = Some co ->
  field_offset env id (co_members co) = Errors.OK ofs ->
  field_offset env' id (co_members co) = Errors.OK ofs.
Proof.
  unfold field_offset.
  generalize 0.
  intros.
  destruct (H i co H0) as [HH _ _ _].
  revert z H1.
  clear H H0.
  induction (co_members co); intros.
  + simpl in H1 |- *.
    inversion H1.
  + simpl in H1 |- *.
    destruct a.
    simpl in HH.
    rewrite andb_true_iff in HH.
    if_tac.
    - rewrite alignof_stable with (env := env) by tauto. assumption.
    - rewrite alignof_stable with (env := env) by tauto.
      rewrite sizeof_stable with (env := env) by tauto.
      apply IHm; try tauto.
Qed.

End STABILITY.

Lemma annotations_initialized i Delta:
   annotations (initialized i Delta) = annotations Delta.
Proof. destruct Delta. simpl. unfold initialized. simpl.
  destruct (tyc_temps ! i); trivial. destruct p; trivial.
Qed.

Section TYCON_SUB.
Variables Delta Delta': tycontext.
Hypothesis extends: tycontext_sub Delta Delta'.

Lemma initialized_sub: forall i,
  tycontext_sub (initialized i Delta) (initialized i Delta').
Proof.
intros.
unfold tycontext_sub in *.
destruct extends as [? [? [? [? [? ?]]]]].
repeat split; intros.
 + specialize (H id); clear - H.
        destruct (eq_dec  i id).
        -  unfold initialized. subst.
           destruct ((temp_types Delta)!id) as [[? ?] |] eqn:?.
         unfold temp_types at 1; simpl; rewrite PTree.gss.
        destruct ((temp_types Delta')!id) as [[? ?] |]. destruct H; subst t0.
         unfold temp_types at 1. simpl. rewrite PTree.gss. auto. contradiction.
         rewrite Heqo. auto.
        -   rewrite <- initialized_ne by auto.
           destruct ((temp_types Delta)!id) as [[? ?] |] eqn:?; auto.
           rewrite <- initialized_ne by auto.
        destruct ((temp_types Delta')!id) as [[? ?] |]; [| contradiction].
         auto.
 + repeat rewrite set_temp_ve; auto.
 + repeat rewrite set_temp_ret; auto.
 + repeat rewrite set_temp_ge; auto.
 + repeat rewrite set_temp_gs; auto.
 + rewrite 2 annotations_initialized; trivial.
Qed.

Lemma func_tycontext'_sub: forall f,
  tycontext_sub (func_tycontext' f Delta) (func_tycontext' f Delta').
Proof.
  intros.
  unfold func_tycontext'.
  unfold tycontext_sub in *.
  destruct extends as [? [? [? [? [? ?]]]]].
  repeat split; simpl.
  + intros.
    destruct ((make_tycontext_t (fn_params f) (fn_temps f)) ! id) as [[? ?] |].
    - destruct b; split; reflexivity.
    - exact I.
  + auto.
  + auto.
  + auto.
Qed.

End TYCON_SUB.

Lemma tycontext_sub_join:
 forall Delta1 Delta2 Delta1' Delta2',
  tycontext_sub Delta1 Delta1' -> tycontext_sub Delta2 Delta2' ->
  tycontext_sub (join_tycon Delta1 Delta2) (join_tycon Delta1' Delta2').
Proof.
intros [A1 B1 C1 D1 E1] [A2 B2 C2 D2 E2]
          [A1' B1' C1' D1' E1'] [A2' B2' C2' D2' E2']
  [? [? [? ?]]] [? [? [? ?]]].
simpl in *.
unfold join_tycon.
split; [ | split; [ | split]]; simpl; auto.
intro id; specialize (H id); specialize (H3 id).
unfold temp_types in *.
simpl in *.
clear - H H3.
unfold sub_option in *.
repeat rewrite join_te_denote2.
unfold te_one_denote.
destruct (A1 ! id) as [[? b1] |].
destruct (A1' ! id) as [[? b1'] |]; [ | contradiction].
destruct H; subst t0.
destruct (A2 ! id) as [[? b2] |].
destruct (A2' ! id) as [[? b2'] |]; [ | contradiction].
destruct H3; subst t1.
split; auto. destruct b1,b1'; inv H0; simpl; auto.
destruct (A2' ! id) as [[? b2'] |]; split; auto.
auto.
Qed.

Lemma update_tycon_sub:
  forall Delta Delta', tycontext_sub Delta Delta' ->
   forall h, tycontext_sub (update_tycon Delta h) (update_tycon Delta' h)
with join_tycon_labeled_sub:
 forall Delta Delta', tycontext_sub Delta Delta' ->
    forall ls, tycontext_sub (join_tycon_labeled ls Delta)
                         (join_tycon_labeled ls Delta').
Proof.
* clear update_tycon_sub.
  rename join_tycon_labeled_sub into J.
  intros.
 revert Delta Delta' H; induction h; intros;
   try (apply H); simpl update_tycon; auto.
 + apply initialized_sub; auto.
 + destruct o; auto. apply initialized_sub; auto.
 + apply tycontext_sub_join; auto.
* clear join_tycon_labeled_sub.
 intros.
 revert Delta Delta' H; induction ls; simpl; intros; auto.
 apply tycontext_sub_join; auto.
Qed.

Lemma exit_tycon_sub: forall c ek,
  forall Delta Delta', tycontext_sub Delta Delta' ->
  tycontext_sub (exit_tycon c Delta ek) (exit_tycon c Delta' ek).
Proof.
intros.
destruct ek; simpl; auto.
apply update_tycon_sub; auto.
Qed.

Section TYCON_EQUIV.

Variable Delta Delta': tycontext.
Hypothesis equiv: tycontext_eqv Delta Delta'.

Lemma func_tycontext'_eqv: forall f,
  tycontext_eqv (func_tycontext' f Delta) (func_tycontext' f Delta').
Proof.
  intro.
  rewrite tycontext_eqv_spec in *.
  split; apply func_tycontext'_sub; tauto.
Qed.

Lemma initialized_tycontext_eqv: forall i,
  tycontext_eqv (initialized i Delta) (initialized i Delta').
Proof.
  intro.
  rewrite tycontext_eqv_spec in *.
  split; apply initialized_sub; tauto.
Qed.

Lemma update_tycontext_eqv: forall c,
  tycontext_eqv (update_tycon Delta c) (update_tycon Delta' c).
Proof.
  intro.
  rewrite tycontext_eqv_spec in *.
  split; apply update_tycon_sub; tauto.
Qed.

Lemma join_tycon_labeled_eqv: forall l,
  tycontext_eqv (join_tycon_labeled l Delta) (join_tycon_labeled l Delta').
Proof.
  intros.
  rewrite tycontext_eqv_spec in *.
  split; apply join_tycon_labeled_sub; tauto.
Qed.

Lemma exit_tycontext_eqv: forall c b,
  tycontext_eqv (exit_tycon c Delta b) (exit_tycon c Delta' b).
Proof.
  intros.
  rewrite tycontext_eqv_spec in *.
  split; apply exit_tycon_sub; tauto.
Qed.

End TYCON_EQUIV.

Lemma join_tycontext_eqv:
  forall Delta1 Delta1' Delta2 Delta2',
     tycontext_eqv Delta1 Delta1' ->
     tycontext_eqv Delta2 Delta2' ->
    tycontext_eqv (join_tycon Delta1 Delta2)  (join_tycon Delta1' Delta2').
Proof.
  intros ? ? ? ?.
  rewrite ! tycontext_eqv_spec.
  intros [? ?] [? ?].
  split; apply tycontext_sub_join; auto.
Qed.

Lemma tycontext_eqv_symm:
  forall Delta Delta', tycontext_eqv Delta Delta' ->  tycontext_eqv Delta' Delta.
Proof.
intros.
destruct H as [? [? [? [? [? ?]]]]]; repeat split; auto.
Qed.

Lemma tycontext_eqv_sub:
  forall Delta Delta', tycontext_eqv Delta Delta' ->
         tycontext_sub Delta Delta'.
Proof.
intros.
destruct H as [? [? [? [? [? ?]]]]].
repeat split; intros; auto.
rewrite H; auto.
destruct ((temp_types Delta') ! id); auto.
destruct p. split; auto. destruct b; reflexivity.
rewrite H2. destruct ((glob_types Delta') ! id); simpl; auto.
rewrite H3. destruct ((glob_specs Delta') ! id); simpl; auto.
rewrite H4. apply Annotation_sub_refl.
Qed.

Record ret_assert : Type := {
 RA_normal: environ->mpred;
 RA_break: environ->mpred;
 RA_continue: environ->mpred;
 RA_return: option val -> environ->mpred
}.

Lemma update_tycon_Slabel Delta l c: update_tycon Delta (Slabel l c) = update_tycon Delta c.
Proof. reflexivity. Qed. 

Lemma modifiedvars_Slabel l c: modifiedvars (Slabel l c) = modifiedvars c.
Proof. reflexivity. Qed.

Lemma modifiedvars_computable: forall c (te1 te2: Map.t val), exists te,
  (forall i, modifiedvars c i -> Map.get te1 i = Map.get te i) /\
  (forall i, modifiedvars c i \/ Map.get te2 i = Map.get te i).
Proof.
  intros.
  unfold modifiedvars.
  exists (fun i => match (modifiedvars' c idset0) ! i with Some _ => Map.get te1 i | None => Map.get te2 i end).
  split; intros.
  + unfold Map.get.
    destruct ((modifiedvars' c idset0) ! i); simpl; [auto | inv H].
  + unfold Map.get.
    destruct ((modifiedvars' c idset0) ! i); simpl; [left; apply I | auto].
Qed.

Lemma modifiedvars_Sifthenelse b c1 c2 id: modifiedvars (Sifthenelse b c1 c2) id <-> modifiedvars c1 id \/ modifiedvars c2 id.
Proof.
  unfold modifiedvars.
  simpl.
  rewrite modifiedvars'_union.
  reflexivity.
Qed.

Lemma modifiedvars_Sloop c1 c2 id: modifiedvars (Sloop c1 c2) id <-> modifiedvars c1 id \/ modifiedvars c2 id.
Proof.
  unfold modifiedvars.
  simpl.
  rewrite modifiedvars'_union.
  reflexivity.
Qed.

Lemma modifiedvars_Ssequence c1 c2 id: modifiedvars (Ssequence c1 c2) id <-> modifiedvars c1 id \/ modifiedvars c2 id.
Proof.
  unfold modifiedvars.
  simpl.
  rewrite modifiedvars'_union.
  reflexivity.
Qed.

Lemma modifiedvars_ls_eq: forall sl, modifiedvars_ls sl = modifiedvars' (seq_of_labeled_statement sl).
Proof.
  intros.
  induction sl; auto.
  destruct o; simpl;
  rewrite IHsl; auto.
Qed.  

Lemma modifiedvars_Sswitch e sl n id: modifiedvars (seq_of_labeled_statement (select_switch (Int.unsigned n) sl)) id -> modifiedvars (Sswitch e sl) id.
Proof.
  unfold modifiedvars.
  simpl.
  unfold select_switch.
  destruct (select_switch_case (Int.unsigned n) sl) eqn:?H.
  + revert l H; induction sl; simpl; intros.
    - inv H.
    - rewrite modifiedvars'_union.
      destruct o; [| right; eapply IHsl; eauto].
      if_tac in H; [| right; eapply IHsl; eauto].
      inv H.
      simpl in H0.
      rewrite modifiedvars'_union in H0; auto.
      rewrite modifiedvars_ls_eq; auto.
  + revert H; induction sl; simpl; intros.
    - auto.
    - rewrite modifiedvars'_union.
      destruct o; [if_tac in H |].
      * inv H.
      * right; apply IHsl; auto.
      * simpl in H0.
        rewrite modifiedvars'_union in H0; auto.
        rewrite modifiedvars_ls_eq; auto.
Qed.

Lemma exit_tycon_Slabel l c Delta b: 
   exit_tycon (Slabel l c) Delta b = exit_tycon c Delta b.
Proof. unfold exit_tycon. destruct b; trivial. Qed.

Lemma exit_typcon_Slabel' l c Delta: 
   exit_tycon (Slabel l c) Delta = exit_tycon c Delta.
Proof. extensionality b. rewrite exit_tycon_Slabel. trivial. Qed.


Lemma annotations_update_dist:
  forall d1 d2 : tycontext, annotations (join_tycon d1 d2) = annotations d1.
Proof.
intros.
unfold annotations.
unfold join_tycon.
destruct d1; auto. destruct d2; auto.
Qed.


Lemma annotations_update_tycon: forall c Delta, 
   (annotations Delta) = (annotations (update_tycon Delta c))
 with annotations_update_tycon_le: forall cl Delta,
   (annotations Delta) = (annotations (join_tycon_labeled cl Delta)).
Proof.
* clear annotations_update_tycon.
induction c; intros; simpl; unfold initialized; simpl; auto.
destruct ((temp_types Delta) ! i) as [[? ?] |]; auto.
destruct o; auto.
destruct ((temp_types Delta) ! i) as [[? ?] |]; auto.
rewrite IHc2.
rewrite <- !IHc2. auto.
rewrite annotations_update_dist.
auto.
*
clear annotations_update_tycon_le.
induction cl; intros; simpl; auto.
rewrite annotations_update_dist.
auto.
Qed.

Lemma tycontext_sub_update: 
forall Delta c, tycontext_sub Delta (update_tycon Delta c).
Proof.
intros.
hnf.
repeat split; intros; simpl.
destruct ((temp_types Delta) ! id) eqn:?; auto. destruct p.
apply update_tycon_te_same with (c:=c) in Heqo.
destruct Heqo. rewrite H. split; auto. destruct b; reflexivity.
rewrite var_types_update_tycon; auto.
rewrite ret_type_update_tycon; auto.
rewrite glob_types_update_tycon; auto.
apply sub_option_refl.
rewrite glob_specs_update_tycon; auto.
apply sub_option_refl.
rewrite <- annotations_update_tycon.
apply Annotation_sub_refl.
Qed.
