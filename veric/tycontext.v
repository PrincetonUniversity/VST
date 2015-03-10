Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Export veric.lift.

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
Implicit Arguments opt2list.

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

Inductive funspec :=
   mk_funspec: funsig -> forall A: Type, (A -> environ->mpred) -> (A -> environ->mpred) -> funspec.

Definition funspecs := list (ident * funspec).

Definition type_of_funspec (fs: funspec) : type :=  
  match fs with mk_funspec fsig _ _ _ => Tfunction (type_of_params (fst fsig)) (snd fsig) cc_default end.

(** Declaration of type context for typechecking **)
Inductive tycontext : Type := 
  mk_tycontext : forall (tyc_temps: PTree.t (type * bool))
                        (tyc_vars: PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: PTree.t type)
                        (tyc_globsp: PTree.t funspec)
                        (cenv: composite_env)
                        (cenv_consistent: composite_env_consistent cenv),
                             tycontext.

Definition empty_tycontext cenv cc : tycontext :=
  mk_tycontext (PTree.empty _) (PTree.empty _) Tvoid  (PTree.empty _)  (PTree.empty _) cenv cc.

Definition temp_types (Delta: tycontext): PTree.t (type*bool) := 
  match Delta with mk_tycontext a _ _ _ _ _ _=> a end.
Definition var_types (Delta: tycontext) : PTree.t type := 
  match Delta with mk_tycontext _ a _ _ _ _ _ => a end.
Definition ret_type (Delta: tycontext) : type := 
  match Delta with mk_tycontext _ _ a _ _ _ _ => a end.
Definition glob_types (Delta: tycontext) : PTree.t type := 
  match Delta with mk_tycontext _ _ _ a _ _ _ => a end.
Definition glob_specs (Delta: tycontext) : PTree.t funspec := 
  match Delta with mk_tycontext _ _ _ _ a _ _ => a end.
Definition composite_types (Delta: tycontext) : composite_env := 
  match Delta with mk_tycontext _ _ _ _ _ a _ => a end.
Definition composite_types_consistent (Delta: tycontext) : composite_env_consistent (composite_types Delta) := 
  match Delta with mk_tycontext _ _ _ _ _ _ a => a end.

(** Functions that modify type environments **)
Definition initialized id (Delta: tycontext) : tycontext :=
match (temp_types Delta) ! id with
| Some (ty, _) => mk_tycontext (PTree.set id (ty,true) (temp_types Delta))
                       (var_types Delta) (ret_type Delta) (glob_types Delta) (glob_specs Delta)
                       (composite_types Delta) (composite_types_consistent Delta)
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
match tycon1 with  mk_tycontext te1 ve1 r vl1 g1 cenv cc  =>
match tycon2 with  mk_tycontext te2 _ _ _ _ _ _ =>
  mk_tycontext (join_te te1 te2) ve1 r vl1 g1 cenv cc
end end.              

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

Definition varspecs : Type := list (ident * type).

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

Definition make_tycontext_s (G: funspecs) :=
 (fold_right (fun (var : ident * funspec) => PTree.set (fst var) (snd var)) 
            (PTree.empty _) G).

Definition make_tycontext (params: list (ident*type)) (temps: list (ident*type)) (vars: list (ident*type))
                       (return_ty: type)
                       (V: varspecs) (G: funspecs) cenv cc :  tycontext :=
 mk_tycontext 
   (make_tycontext_t params temps)
   (make_tycontext_v vars)
   return_ty
   (make_tycontext_g V G)
   (make_tycontext_s G) cenv cc.

Definition func_tycontext (func: function) (V: varspecs) (G: funspecs) cenv cc : tycontext :=
  make_tycontext (func.(fn_params)) (func.(fn_temps)) (func.(fn_vars)) (func.(fn_return)) V G cenv cc.

Definition nofunc_tycontext (V: varspecs) (G: funspecs) cenv cc : tycontext :=
   make_tycontext nil nil nil Tvoid V G cenv cc.


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

clear glob_specs_join_labeled.
intros. simpl. 
destruct l. simpl. auto. 
simpl in *. rewrite glob_specs_update_dist. 
auto. 
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

Lemma set_temp_ct : forall Delta i,
composite_types (initialized i Delta) = composite_types (Delta).
intros. 
destruct Delta. unfold composite_types. unfold initialized.
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
 /\ (forall id, sub_option ((composite_types Delta) ! id) ((composite_types Delta') ! id)).               

Definition tycontext_eqv (Delta Delta' : tycontext) : Prop :=
 (forall id, (temp_types Delta) ! id = (temp_types Delta') ! id)
 /\ (forall id, (var_types Delta) ! id = (var_types Delta') ! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, (glob_types Delta) ! id = (glob_types Delta') ! id)
 /\ (forall id, (glob_specs Delta) ! id = (glob_specs Delta') ! id)
 /\ (forall id, (composite_types Delta) ! id = (composite_types Delta') ! id).
                
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

Lemma tycontext_eqv_symm:
  forall Delta Delta', tycontext_eqv Delta Delta' ->  tycontext_eqv Delta' Delta.
Proof.
intros.
destruct H as [? [? [? [? [? ?]]]]]; repeat split; auto.
Qed.

Lemma tycontext_sub_refl:
 forall Delta, tycontext_sub Delta Delta.
Proof.
intros. destruct Delta as [T V r G S].
unfold tycontext_sub.
intuition.
 + unfold sub_option. unfold temp_types. simpl. 
   destruct (T ! id) as [[? ?]|]; split; auto; destruct b; auto.
 + unfold sub_option, glob_types. simpl. 
   destruct (G ! id); auto.
 + unfold sub_option, glob_specs. simpl. 
   destruct (S ! id); auto.
 + unfold sub_option, composite_types. simpl. 
   destruct (cenv ! id); auto. 
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

Lemma initialized_sub :
  forall Delta Delta' i ,
    tycontext_sub Delta Delta' ->
    tycontext_sub (initialized i Delta) (initialized i Delta').
Proof.
intros.
unfold tycontext_sub in *. 
destruct H as [? [? [? [? [? ?]]]]].
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
 + repeat rewrite set_temp_ct; auto.
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

Section STABILITY.
Variables Delta Delta': tycontext.
Hypothesis extends: tycontext_sub Delta Delta'.

Lemma composite_types_get_sub: forall i co,
  (composite_types Delta) ! i = Some co ->
  (composite_types Delta') ! i = Some co.
Proof.
  intros.
  destruct extends as [_ [_ [_ [_ [_ ?]]]]].
  specialize (H0 i).
  destruct ((composite_types Delta) ! i); inversion H.
  destruct ((composite_types Delta') ! i); inversion H0.
  subst; reflexivity.
Qed.

Lemma complete_type_sub: forall t,
  complete_type (composite_types Delta) t = true ->
  complete_type (composite_types Delta') t = true.
Proof.
  intros.
  destruct extends as [_ [_ [_ [_ [_ ?]]]]].
  induction t; simpl in H |- *; auto.
  + specialize (H0 i).
    destruct ((composite_types Delta) ! i); inversion H.
    destruct ((composite_types Delta') ! i); inversion H0.
    reflexivity.
  + specialize (H0 i).
    destruct ((composite_types Delta) ! i); inversion H.
    destruct ((composite_types Delta') ! i); inversion H0.
    reflexivity.
Qed.

Lemma sizeof_sub: forall t,
  complete_type (composite_types Delta) t = true ->
  sizeof (composite_types Delta) t = sizeof (composite_types Delta') t.
Proof.
  intros.
  destruct extends as [_ [_ [_ [_ [_ ?]]]]].
  induction t; simpl in H |- *; auto.
  + rewrite (IHt H); reflexivity.
  + specialize (H0 i).
    destruct ((composite_types Delta) ! i); inversion H.
    destruct ((composite_types Delta') ! i); inversion H0.
    reflexivity.
  + specialize (H0 i).
    destruct ((composite_types Delta) ! i); inversion H.
    destruct ((composite_types Delta') ! i); inversion H0.
    reflexivity.
Qed.

Lemma alignof_sub: forall t,
  complete_type (composite_types Delta) t = true ->
  alignof (composite_types Delta) t = alignof (composite_types Delta') t.
Proof.
  intros.
  destruct extends as [_ [_ [_ [_ [_ ?]]]]].
  induction t; simpl in H |- *; auto.
  + rewrite (IHt H); reflexivity.
  + specialize (H0 i).
    destruct ((composite_types Delta) ! i); inversion H.
    destruct ((composite_types Delta') ! i); inversion H0.
    reflexivity.
  + specialize (H0 i).
    destruct ((composite_types Delta) ! i); inversion H.
    destruct ((composite_types Delta') ! i); inversion H0.
    reflexivity.
Qed.

Lemma field_offset_sub: forall i id co ofs,
  (composite_types Delta) ! i = Some co ->
  field_offset (composite_types Delta) id (co_members co) = Errors.OK ofs ->
  field_offset (composite_types Delta') id (co_members co) = Errors.OK ofs.
Proof.
  unfold field_offset.
  generalize 0.
  intros.
  pose proof composite_types_get_sub _ _ H.
  destruct (composite_types_consistent _ _ _ H) as [HH _ _ _].
  revert z H0.
  clear H H1.
  induction (co_members co); intros.
  + simpl in H0 |- *.
    inversion H0.
  + simpl in H0 |- *.
    destruct a.
    simpl in HH.
    rewrite andb_true_iff in HH.
    if_tac.
    - rewrite <- alignof_sub by tauto. assumption.
    - rewrite <- alignof_sub by tauto.
      rewrite <- sizeof_sub by tauto.
      apply IHm; try tauto.
Qed.
  
End STABILITY.
