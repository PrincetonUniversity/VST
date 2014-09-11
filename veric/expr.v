Require Import msl.msl_standard.
Require Import veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_lemmas.
Require Export veric.lift.
Require Export veric.Cop2.

Definition is_true (b: bool) :=
  match b with true => True | false => False end.

Definition force_val (v: option val) : val :=
 match v with Some v' => v' | None => Vundef end.

Definition force_val1 (f: val -> option val) (v: val) := force_val (f v).
Definition force_val2 (f: val -> val -> option val) (v1 v2: val) := force_val (f v1 v2).

Arguments force_val1 f v /.
Arguments force_val2 f v1 v2 /.

Definition force_int (v: val) := 
 match v with
 | Vint i => i | _ => Int.zero 
 end.
Arguments force_int !v / .

Definition force_signed_int v := Int.signed (force_int v).
Arguments force_signed_int !v / .

Lemma force_Vint:  forall i, force_int (Vint i) = i.
Proof.  reflexivity. Qed.
Hint Rewrite force_Vint : norm.

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

Lemma isSome_dec: forall {A} (P: option A), isSome P \/ ~ isSome P.
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

(* LIFTING METHOD TWO: *)
Canonical Structure LiftEnviron := Tend environ.

Ltac super_unfold_lift :=
  cbv delta [liftx LiftEnviron Tarrow Tend lift_S lift_T lift_prod 
  lift_last lifted lift_uncurry_open lift_curry lift lift0 lift1 lift2 lift3] beta iota in *.

(** Computational version of type_eq **)

Definition eqb_option {A} (f: A -> A -> bool) (x y: option A) : bool :=
  match x, y with
  | None, None => true
  | Some x' , Some y' => f x' y'
 | _, _ => false
  end.

Definition eqb_attr (a b: attr) : bool :=
 match a, b with
 | mk_attr av an, mk_attr bv bn => eqb av bv && eqb_option N.eqb an bn
 end.

Definition eqb_floatsize (a b: floatsize) : bool :=
 match a , b with
 | F32, F32 => true
 | F64, F64 => true
 | _, _ => false
 end.

Definition eqb_ident : ident -> ident -> bool := Peqb.

Definition eqb_intsize (a b: intsize) : bool :=
 match a , b with
 | I8, I8 => true
 | I16, I16 => true
 | I32, I32 => true
 | IBool, IBool => true
 | _, _ => false
 end.

Definition eqb_signedness (a b : signedness) :=
 match a, b with
 | Signed, Signed => true
 | Unsigned, Unsigned => true
 | _, _ => false
 end.

Definition eqb_calling_convention (a b: calling_convention) :=
 andb (eqb (cc_vararg a) (cc_vararg b)) 
     (eqb (cc_structret a) (cc_structret b)) .

Fixpoint eqb_type (a b: type) {struct a} : bool :=
 match a, b with
 | Tvoid, Tvoid => true
 | Tint ia sa aa, Tint ib sb ab => andb (eqb_intsize ia ib) 
                                                    (andb (eqb_signedness sa sb) (eqb_attr aa ab))
 | Tlong sa aa, Tlong sb ab => andb (eqb_signedness sa sb) (eqb_attr aa ab)
 | Tfloat sa aa, Tfloat sb ab => andb (eqb_floatsize sa sb) (eqb_attr aa ab)
 | Tpointer ta aa, Tpointer tb ab => andb (eqb_type ta tb) (eqb_attr aa ab)
 | Tarray ta sa aa, Tarray tb sb ab => andb (eqb_type ta tb) 
                                                                   (andb (Zeq_bool sa sb) (eqb_attr aa ab))
 | Tfunction sa ta ca, Tfunction sb tb cb => 
       andb (andb (eqb_typelist sa sb) (eqb_type ta tb)) (eqb_calling_convention ca cb)
 | Tstruct ia fa aa, Tstruct ib fb ab => andb (eqb_ident ia ib) 
                                                                  (andb (eqb_fieldlist fa fb) (eqb_attr aa ab))
 | Tunion ia fa aa, Tunion ib fb ab => andb (eqb_ident ia ib) 
                                                                  (andb (eqb_fieldlist fa fb) (eqb_attr aa ab))
 | Tcomp_ptr ia aa, Tcomp_ptr ib ab => andb (eqb_ident ia ib) (eqb_attr aa ab)
 | _, _ => false
 end
with eqb_typelist (a b: typelist)  {struct a}: bool :=
  match a, b with
  | Tcons ta ra, Tcons tb rb => andb (eqb_type ta tb) (eqb_typelist ra rb)
  | Tnil, Tnil => true
  | _ , _ => false
  end
with eqb_fieldlist (a b: fieldlist)  {struct a}: bool :=
  match a, b with
  | Fcons ia ta ra, Fcons ib tb rb =>  andb (eqb_ident ia ib) 
                                                             (andb (eqb_type ta tb) (eqb_fieldlist ra rb))
  | Fnil, Fnil => true
  | _ , _ => false
  end.

Lemma eqb_intsize_spec: forall i j, eqb_intsize i j = true <-> i=j.
Proof. destruct i,j; simpl; split; intro; congruence. Qed.
Lemma eqb_floatsize_spec: forall i j, eqb_floatsize i j = true <-> i=j.
Proof. destruct i,j; simpl; split; intro; congruence. Qed.
Lemma eqb_signedness_spec: forall i j, eqb_signedness i j = true <-> i=j.
Proof. destruct i,j; simpl; split; intro; congruence. Qed.
Lemma eqb_attr_spec: forall i j, eqb_attr i j = true <-> i=j.
Proof.
  destruct i as [[ | ] [ | ]]; destruct j as [[ | ] [ | ]];
   simpl; split; intro; try rewrite N.eqb_eq in *; try congruence.
Qed.
Lemma eqb_ident_spec: forall i j, eqb_ident i j = true <-> i=j.
Proof.
 intros. unfold eqb_ident. 
 apply Pos.eqb_eq.
Qed.


Scheme eqb_type_sch := Induction for type Sort Prop
  with eqb_typelist_sch := Induction for  typelist Sort Prop
  with eqb_fieldlist_sch := Induction for  fieldlist Sort Prop.

Lemma eqb_type_spec: forall a b, eqb_type a b = true <-> a=b.
Proof.
apply (eqb_type_sch 
           (fun a => forall b, eqb_type a b = true <-> a=b)
          (fun a => forall b, eqb_typelist a b = true <-> a=b)
           (fun a => forall b, eqb_fieldlist a b = true <-> a=b));
  destruct b; simpl;
   split; intro; 
   repeat rewrite andb_true_iff in *;
   try rewrite eqb_intsize_spec in *;
   try rewrite eqb_floatsize_spec in *;
   try rewrite eqb_signedness_spec in *; 
   try rewrite eqb_attr_spec in *; 
   try rewrite eqb_ident_spec in *; 
   try rewrite <- Zeq_is_eq_bool in *;
   repeat match goal with H: _ /\ _ |- _  => destruct H end;
   repeat split; subst; f_equal; try  congruence.
   apply H; auto.
   inv H0; apply H; auto.
   apply H; auto.
   inv H0; apply H; auto.
   apply H; auto. apply H0; auto.
   clear - H2; destruct c as [[|] [|]]; destruct c0 as [[|] [|]]; inv H2; auto.
   inv H1; apply H; auto.
   inv H1; apply H0; auto.
   inv H1; destruct c0 as [[|] [|]]; reflexivity.
   apply H; auto.
   inv H0; apply H; auto.
   inv H1; apply H; auto.
   apply H; auto.
   inv H0; apply H; auto.
   apply H; auto.
   inv H1; apply H; auto.
   inv H2; apply H0; auto.
   inv H1; apply H; auto.
   inv H1; apply H0; auto.
   inv H2; apply H; auto.
   inv H3; apply H0; auto.
   inv H1; apply H; auto.
   inv H1; apply H0; auto.
Qed.

Lemma eqb_type_true: forall a b, eqb_type a b = true -> a=b.
Proof.
intros. apply eqb_type_spec; auto.
Qed.

Lemma eqb_type_false: forall a b, eqb_type a b = false <-> a<>b.
Proof.
intros.
pose proof (eqb_type_spec a b).
destruct (eqb_type a b);
split; intro; try congruence.
destruct H. rewrite H in H0 by auto. congruence.
intro; subst.
destruct H; try congruence.
spec H1; auto. congruence.
Qed.

Lemma eqb_type_refl: forall a, eqb_type a a = true. 
Proof.
intros. apply eqb_type_spec; auto.
Qed.

(** Functions for evaluating expressions in environments, 
these return vundef if something goes wrong, meaning they always return some value **)

Definition strict_bool_val (v: val) (t: type) : option bool :=
   match v, t with
   | Vint n, Tint _ _ _ => Some (negb (Int.eq n Int.zero))
   | Vlong n, Tlong _ _ => Some (negb (Int64.eq n Int64.zero))
   | (Vint n), (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tcomp_ptr _ _) =>
             if Int.eq n Int.zero then Some false else None
   | Vptr b ofs, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tcomp_ptr _ _) => Some true
   | Vfloat f, Tfloat sz _ => Some (negb(Float.cmp Ceq f Float.zero))
   | _, _ => None
   end.

Definition eval_id (id: ident) (rho: environ) := force_val (Map.get (te_of rho) id).

Definition eval_unop (op: Cop.unary_operation) (t1 : type) :=
       force_val1 (Cop2.sem_unary_operation op t1).

Definition op_to_cmp cop :=
match cop with 
| Cop.Oeq => Ceq | Cop.One =>  Cne
| Cop.Olt => Clt | Cop.Ogt =>  Cgt 
| Cop.Ole => Cle | Cop.Oge =>  Cge 
| _ => Ceq (*doesn't matter*)
end.

Definition is_comparison op :=
match op with 
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => true              
  | _ => false
end.

Definition true2 (b : block) (i : Z) := true.

Definition eval_binop (op: Cop.binary_operation) (t1 t2 : type) :=
       force_val2 (Cop2.sem_binary_operation' op t1 t2 true2).
Arguments eval_binop op t1 t2 / v1 v2.

Definition eval_cast (t1 t2 : type) :=
  force_val1 (sem_cast t1 t2).
Arguments eval_cast t1 t2 / v.

Definition force_ptr (v: val) : val :=
              match v with Vptr l ofs => v | _ => Vundef  end.

Definition always {A B: Type} (b: B) (a: A) := b.

Definition offset_val (ofs: int) (v: val) : val :=
  match v with
  | Vptr b z => Vptr b (Int.add z ofs)
  | _ => Vundef
 end.

Definition eval_field (ty: type) (fld: ident) : val -> val :=
          match ty with
             | Tstruct id fList att =>
                         match field_offset fld fList with 
                         | Errors.OK delta => offset_val (Int.repr delta)
                         | _ => always Vundef
                        end
             | Tunion id fList att => force_ptr
             | _ => always Vundef
          end.

Definition eval_var (id:ident) (ty: type) (rho: environ) : val := 
                         match Map.get (ve_of rho) id with
                         | Some (b,ty') => if eqb_type ty ty'
                                                    then Vptr b Int.zero
                                                    else Vundef
                         | None => 
                            match (ge_of rho) id with
                            | Some b => Vptr b Int.zero
                            | None => Vundef
                            end
                        end.

Definition deref_noload (ty: type) : val -> val :=
 match access_mode ty with
 | By_reference => Datatypes.id
 | _ => always Vundef
 end.

Fixpoint eval_expr (e: expr) : environ -> val :=
 match e with
 | Econst_int i ty => `(Vint i)
 | Econst_long i ty => `(Vlong i)
 | Econst_float f ty => `(Vfloat f)
 | Etempvar id ty => eval_id id 
 | Eaddrof a ty => eval_lvalue a 
 | Eunop op a ty =>  `(eval_unop op (typeof a)) (eval_expr a) 
 | Ebinop op a1 a2 ty =>  
                  `(eval_binop op (typeof a1) (typeof a2)) (eval_expr a1) (eval_expr a2)
 | Ecast a ty => `(eval_cast (typeof a) ty) (eval_expr a)
 | Evar id ty => `(deref_noload ty) (eval_var id ty)
 | Ederef a ty => `(deref_noload ty) (`force_ptr (eval_expr a))
 | Efield a i ty => `(deref_noload ty) (`(eval_field (typeof a) i) (eval_lvalue a))
 end

 with eval_lvalue (e: expr) : environ -> val := 
 match e with 
 | Evar id ty => eval_var id ty
 | Ederef a ty => `force_ptr (eval_expr a)
 | Efield a i ty => `(eval_field (typeof a) i) (eval_lvalue a)
 | _  => `Vundef
 end.

Fixpoint eval_exprlist (et: list type) (el:list expr) : environ -> list val :=
 match et, el with
 | t::et', e::el' => `(@cons val) (`force_val (`(sem_cast (typeof e) t) (eval_expr e))) (eval_exprlist et' el')
 | _, _ => `nil
 end.

Definition eval_expropt (e: option expr) : environ -> option val :=
 match e with Some e' => `(@Some val) (eval_expr e')  | None => `None end.

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

Inductive global_spec :=
| Global_func : forall fs: funspec, global_spec
| Global_var:  forall gv: type, global_spec.

(** Declaration of type context for typechecking **)

(*Temps, vars, function return, list of variables that are not vars
 (meaning they can be looked up as globals)*)
Definition tycontext: Type := (PTree.t (type * bool) * (PTree.t type) * type 
                                  * (PTree.t global_spec))%type.

Definition empty_tycontext : tycontext := (PTree.empty (type * bool), PTree.empty type, Tvoid, PTree.empty _).

Definition temp_types (Delta: tycontext): PTree.t (type*bool) := fst (fst (fst Delta)).
Definition var_types (Delta: tycontext) : PTree.t type := snd (fst (fst Delta)).
Definition ret_type (Delta: tycontext) : type := snd (fst Delta).
Definition glob_types (Delta: tycontext) : PTree.t global_spec := snd Delta.

(** Beginning of typechecking **)

Definition bool_type (t: type) : bool :=
  match t with
  | Tint _ _ _ | Tlong _ _ | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tfloat _ _ => true
  | _ => false
  end.

Definition is_scalar_type (ty:type) : bool :=
match ty with
| Tint _ _ _ => true
| Tfloat _ _ => true
| _ => false
end.

Definition unOp_result_type op a := 
match op with 
  | Cop.Onotbool => (Tint IBool Signed noattr) 
  | Cop.Onotint => (Tint I32 Signed noattr) 
  | Cop.Oneg => (typeof a)
  | Cop.Oabsfloat => (typeof a)
end.

Definition is_int_type ty := 
match ty with
| Tint _ _ _ => true
| _ => false
end.


Definition is_long_type ty := 
match ty with
| Tlong _ _ => true
| _ => false
end.

Definition is_float_type ty := 
match ty with
| Tfloat _ _ => true
| _ => false
end.

Definition is_pointer_type ty :=
match ty with
| (Tpointer _ _ | Tarray _ _ _ 
                   | Tfunction _ _ _ | Tstruct _ _ _ 
                   | Tunion _ _ _) => true
| _ => false
end.

Definition isUnOpResultType op a ty := 
match op with 
  | Cop.Onotbool => match Cop.classify_bool (typeof a) with
                        | Cop.bool_default => false
                        | _ => is_int_type ty 
                        end
  | Cop.Onotint => match Cop.classify_notint (typeof a) with
                        | Cop.notint_default => false
                        | Cop.notint_case_i _ => is_int_type ty 
                        | Cop.notint_case_l _ => is_long_type ty 
                        end
  | Cop.Oneg => match Cop.classify_neg (typeof a) with
                    | Cop.neg_case_i sg => is_int_type ty
                    | Cop.neg_case_f _ => is_float_type ty
                    | _ => false
                    end
  | Cop.Oabsfloat =>match Cop.classify_neg (typeof a) with
                    | Cop.neg_case_i sg => is_float_type ty
                    | Cop.neg_case_l _ => is_float_type ty
                    | Cop.neg_case_f _ => is_float_type ty
                    | _ => false
                    end
end.

Inductive tc_error :=
| op_result_type : expr -> tc_error
| arg_type : expr -> tc_error
| pp_compare_size_0 : type -> tc_error
| invalid_cast : type -> type -> tc_error
| invalid_cast_result : type -> type -> tc_error
| invalid_expression : expr -> tc_error
| var_not_in_tycontext : tycontext -> positive  -> tc_error
| mismatch_context_type : type -> type -> tc_error
| deref_byvalue : type -> tc_error
| volatile_load : type -> tc_error
| invalid_field_access : expr -> tc_error
| invalid_struct_field : ident -> fieldlist -> tc_error
| invalid_lvalue : expr -> tc_error
| wrong_signature : tc_error.

Inductive tc_assert :=
| tc_FF: tc_error -> tc_assert
| tc_noproof : tc_assert
| tc_TT : tc_assert
| tc_andp': tc_assert -> tc_assert -> tc_assert
| tc_orp' : tc_assert -> tc_assert -> tc_assert
| tc_nonzero': expr -> tc_assert
| tc_iszero': expr -> tc_assert
| tc_isptr: expr -> tc_assert
| tc_ilt': expr -> int -> tc_assert
| tc_Zle: expr -> Z -> tc_assert
| tc_Zge: expr -> Z -> tc_assert
| tc_samebase: expr -> expr -> tc_assert
| tc_nodivover': expr -> expr -> tc_assert
| tc_initialized: PTree.elt -> type -> tc_assert.

Definition tc_iszero (e: expr) : tc_assert :=
  match eval_expr e any_environ with
  | Vint i => if Int.eq i Int.zero then tc_TT else tc_FF (pp_compare_size_0 Tvoid)
  | Vlong i => if Int.eq (Int.repr (Int64.unsigned i)) Int.zero then tc_TT else tc_FF (pp_compare_size_0 Tvoid)
  | _ => tc_iszero' e
  end.

Definition tc_nonzero (e: expr) : tc_assert :=
  match eval_expr e any_environ with
   | Vint i => if negb (Int.eq i Int.zero) then tc_TT else tc_nonzero' e
   | _ => tc_nonzero' e
   end.

Definition tc_nodivover (e1 e2: expr) : tc_assert :=
 match eval_expr e1 any_environ, eval_expr e2 any_environ with
                           | Vint n1, Vint n2 => if (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone))
                                     then tc_TT else tc_nodivover' e1 e2
                           | _ , _ => tc_nodivover' e1 e2
                          end.

Definition tc_andp (a1: tc_assert) (a2 : tc_assert) : tc_assert :=
match a1 with
| tc_TT => a2
| tc_FF e => tc_FF e
| _ => match a2 with
      | tc_TT => a1 
      | tc_FF e => tc_FF e
      | _ => tc_andp' a1 a2
      end
end. 

Definition tc_orp (a1: tc_assert) (a2 : tc_assert) : tc_assert :=
match a1 with 
| tc_TT => tc_TT
| tc_FF _ => a2
| _ => match a2 with
       | tc_TT => tc_TT
       | tc_FF _ => a1
       | _ => tc_orp' a1 a2
       end
end.

Definition tc_bool (b : bool) (e: tc_error) :=
if b then tc_TT else tc_FF e.

Definition check_pp_int e1 e2 op t e :=
match op with 
| Cop.Oeq | Cop.One => tc_andp 
                         (tc_orp (tc_iszero e1) (tc_iszero e2))
                         (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.


Definition check_pl_long e2 op t e :=
match op with 
| Cop.Oeq | Cop.One => tc_andp 
                         (tc_iszero e2)
                         (tc_bool (is_int_type t) (op_result_type e))
| _ => tc_noproof
end.


Definition binarithType t1 t2 ty deferr reterr : tc_assert :=
 match Cop.classify_binarith t1 t2 with
  | Cop.bin_case_i sg =>  tc_bool (is_int_type ty) reterr 
  | Cop.bin_case_l sg => tc_bool (is_long_type ty) reterr 
  | Cop.bin_case_f _   => tc_bool (is_float_type ty) reterr
 | Cop.bin_default => tc_FF deferr
 end.

Definition is_numeric_type t :=
match t with Tint _ _ _ | Tlong _ _ | Tfloat _ _ => true | _ => false end.

Definition tc_ilt (e: expr) (j: int) :=
    match eval_expr e any_environ with
    | Vint i => if Int.ltu i j then tc_TT else tc_ilt' e j
    | _ => tc_ilt' e j
    end.

Definition isBinOpResultType op a1 a2 ty : tc_assert :=
let e := (Ebinop op a1 a2 ty) in
let reterr := op_result_type e in
let deferr := arg_type e in 
match op with
  | Cop.Oadd => match Cop.classify_add (typeof a1) (typeof a2) with 
                    | Cop.add_case_pi _ => tc_andp (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr) 
                    | Cop.add_case_ip _ => tc_andp (tc_isptr a2) (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_case_pl _ => tc_andp (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr) 
                    | Cop.add_case_lp _ => tc_andp (tc_isptr a2) (tc_bool (is_pointer_type ty) reterr)
                    | Cop.add_default => binarithType (typeof a1) (typeof a2) ty deferr reterr
            end
  | Cop.Osub => match Cop.classify_sub (typeof a1) (typeof a2) with 
                    | Cop.sub_case_pi _ => tc_andp (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pl _ => tc_andp (tc_isptr a1) (tc_bool (is_pointer_type ty) reterr)
                    | Cop.sub_case_pp ty2 =>  (*tc_isptr may be redundant here*)
                             tc_andp (tc_andp (tc_andp (tc_andp (tc_samebase a1 a2)
                             (tc_isptr a1)) (tc_isptr a2)) (tc_bool (is_int_type ty) reterr))
			     (tc_bool (negb (Int.eq (Int.repr (sizeof ty2)) Int.zero)) 
                                      (pp_compare_size_0 ty2) )
                    | Cop.sub_default => binarithType (typeof a1) (typeof a2) ty deferr reterr
            end 
  | Cop.Omul => binarithType (typeof a1) (typeof a2) ty deferr reterr
  | Cop.Omod => match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i Unsigned => 
                           tc_andp (tc_nonzero a2) 
                           (tc_bool (is_int_type ty) reterr)
                    | Cop.bin_case_l Unsigned => 
                           tc_andp (tc_nonzero a2) 
                           (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_i Signed => tc_andp (tc_andp (tc_nonzero a2) 
                                                      (tc_nodivover a1 a2))
                                                     (tc_bool (is_int_type ty) reterr)
                    | Cop.bin_case_l Signed => tc_andp (tc_andp (tc_nonzero a2) 
                                                      (tc_nodivover a1 a2))
                                                     (tc_bool (is_long_type ty) reterr)
                    | _ => tc_FF deferr
            end
  | Cop.Odiv => match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i Unsigned => tc_andp (tc_nonzero a2) (tc_bool (is_int_type ty) reterr)
                    | Cop.bin_case_l Unsigned => tc_andp (tc_nonzero a2) (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_i Signed => tc_andp (tc_andp (tc_nonzero a2) (tc_nodivover a1 a2)) 
                                                        (tc_bool (is_int_type ty) reterr)
                    | Cop.bin_case_l Signed => tc_andp (tc_andp (tc_nonzero a2) (tc_nodivover a1 a2)) 
                                                        (tc_bool (is_long_type ty) reterr)
                    | Cop.bin_case_f _  =>  tc_bool (is_float_type ty) reterr 
                    | Cop.bin_default => tc_FF deferr
            end
  | Cop.Oshl | Cop.Oshr => match Cop.classify_shift (typeof a1) (typeof a2) with
                    | Cop.shift_case_ii _ =>  tc_andp (tc_ilt a2 Int.iwordsize) (tc_bool (is_int_type ty) 
                                                                                         reterr)
                    (* NEED TO HANDLE OTHER SHIFT CASES *)
                    | _ => tc_FF deferr
                   end
  | Cop.Oand | Cop.Oor | Cop.Oxor => 
                   match Cop.classify_binarith (typeof a1) (typeof a2) with
                    | Cop.bin_case_i _ =>tc_bool (is_int_type ty) reterr
                    (* NEED TO HANDLE OTHER BIN CASES *)
                    | _ => tc_FF deferr
                   end   
  | Cop.Oeq | Cop.One | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge => 
                   match Cop.classify_cmp (typeof a1) (typeof a2) with
                    | Cop.cmp_default => 
                           tc_bool (is_numeric_type (typeof a1) 
                                         && is_numeric_type (typeof a2)
                                          && is_int_type ty)
                                             deferr
		    | Cop.cmp_case_pp => check_pp_int a1 a2 op ty e
                    | Cop.cmp_case_pl => check_pl_long a2 op ty e
                    | Cop.cmp_case_lp => check_pl_long a1 op ty e
                   end
  end.


Definition isCastResultType tfrom tto ty a : tc_assert :=
match Cop.classify_cast tfrom tto with
| Cop.cast_case_default => tc_FF (invalid_cast tfrom tto)
| Cop.cast_case_f2i _ Signed => tc_andp (tc_Zge a Int.min_signed ) (tc_Zle a Int.max_signed) 
| Cop.cast_case_f2i _ Unsigned => tc_andp (tc_Zge a 0) (tc_Zle a Int.max_unsigned)
| Cop.cast_case_neutral  => if eqb_type tfrom ty then tc_TT else 
                            (if orb  (andb (is_pointer_type ty) (is_pointer_type tfrom)) (andb (is_int_type ty) (is_int_type tfrom)) then tc_TT
                                else tc_iszero a)
| Cop.cast_case_l2l => tc_bool (is_long_type tfrom && is_long_type tto) (invalid_cast_result tto ty)
| Cop.cast_case_void => tc_noproof
| _ => match tto with 
      | Tint _ _ _  => tc_bool (is_int_type ty) (invalid_cast_result tto ty) 
      | Tfloat _ _  => tc_bool (is_float_type ty) (invalid_cast_result tto ty)
      | _ => tc_FF (invalid_cast tfrom tto)
      end
end.

Definition is_int (v: val) := 
 match v with Vint i => True | _ => False end.
Definition is_long (v: val) := 
 match v with Vlong i => True | _ => False end.
Definition is_float (v: val) := 
 match v with Vfloat i => True | _ => False end.
Definition is_pointer_or_null (v: val) := 
 match v with 
 | Vint i => i = Int.zero
 | Vptr _ _ => True
 | _ => False
 end.
 
Definition isptr v := 
   match v with | Vptr _ _ => True | _ => False end.

Definition tc_val (ty: type) : val -> Prop :=
 match ty with 
 | Tint _ _ _ => is_int
 | Tlong _ _ => is_long 
 | Tfloat _ _ => is_float
 | Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tcomp_ptr _ _ => is_pointer_or_null
 | Tstruct _ _ _ => isptr
 | Tunion _ _ _ => isptr
 | _ => fun _ => False
 end.

(* A "neutral cast" from t1 to t2 is such that
  it satisfies the neutral_cast_lemma, i.e. if v already typechecks as t1
  then it will not be modified by casting to t2. *)
Definition is_neutral_cast t1 t2 :=
 match t1, t2 with
 | Tint _ _ _, Tint I32 _ _ => true
 | Tlong _ _, Tlong _ _ => true
 | Tfloat _ _, Tfloat F64 _ => true
 | Tpointer _ _, Tpointer _ _ => true
 | _, _ => false
 end.

Lemma neutral_cast_lemma: forall t1 t2 v,
  is_neutral_cast t1 t2 = true -> 
  tc_val t1 v -> eval_cast t1 t2 v = v.
Proof.
intros.
 destruct t1, t2;
 inv H;
 try solve [destruct i; inv H2].
 * destruct i,i0; inv H2; destruct v; inv H0; reflexivity.
 * destruct v; inv H0; reflexivity.
 * destruct f0; inv H2; destruct v; inv H0; reflexivity.
 * destruct v; inv H0; reflexivity.
Qed. 

Definition globtype (g: global_spec) : type :=
match g with 
 | Global_func fs => type_of_funspec fs
 | Global_var gv => gv end.

Definition get_var_type (Delta : tycontext) id : option type :=
match (var_types Delta) ! id with
| Some ty => Some ty
| None => match (glob_types Delta) ! id with
         | Some g => Some (globtype g)
         | None => None
           end
end.

(*

Definition is_neutral_cast tfrom tto : bool :=
match Cop.classify_cast tfrom tto with
| Cop.cast_case_neutral => true
| _ => false
end. 
*)


Definition same_base_type t1 t2 : bool :=
match t1, t2 with
  Tint _ _ _, Tint _ _ _ 
| Tlong _ _, Tlong _ _
| Tfloat _ _, Tfloat _ _  => true
| (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _), 
   (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _) => true
| (Tstruct _ _ _ | Tunion _ _ _), (Tstruct _ _ _ | Tunion _ _ _ ) => true
| _, _ => false
end.


(** Main typechecking function, with work will typecheck both pure
and non-pure expressions, for now mostly just works with pure expressions **)
Fixpoint typecheck_expr (Delta : tycontext) (e: expr) : tc_assert :=
let tcr := typecheck_expr Delta in
match e with
 | Econst_int _ (Tint _ _ _) => tc_TT 
 | Econst_float _ (Tfloat _ _) => tc_TT
 | Etempvar id ty => 
                       match (temp_types Delta)!id with 
                         | Some ty' => if same_base_type ty (fst ty') then 
                                         if (snd ty') then tc_TT else (tc_initialized id ty)
                                       else tc_FF (mismatch_context_type ty (fst ty'))
		         | None => tc_FF (var_not_in_tycontext Delta id)
                       end
 | Eaddrof a ty => tc_andp (typecheck_lvalue Delta a) (tc_bool (is_pointer_type ty)
                                                      (op_result_type e))
 | Eunop op a ty => tc_andp (tc_bool (isUnOpResultType op a ty) (op_result_type e)) (tcr a)
 | Ebinop op a1 a2 ty => tc_andp (tc_andp (isBinOpResultType op a1 a2 ty)  (tcr a1)) (tcr a2)
 | Ecast a ty => tc_andp (tcr a) (isCastResultType (typeof a) ty ty a)
 | Evar id ty => match access_mode ty with
                         | By_reference => 
                            match get_var_type Delta id with 
                            | Some ty' => tc_bool (eqb_type ty ty') 
                                                           (mismatch_context_type ty ty') 
                            | None => tc_FF (var_not_in_tycontext Delta id)
                            end 
                         | _ => tc_FF (deref_byvalue ty)
                        end
 | Efield a i ty => match access_mode ty with
                         | By_reference => 
                            tc_andp (typecheck_lvalue Delta a) (match typeof a with
                            | Tstruct id fList att =>
                                  match field_offset i fList with 
                                  | Errors.OK delta => tc_TT
                                  | _ => tc_FF (invalid_struct_field i fList)
                                  end
                            | Tunion id fList att => tc_TT
                            | _ => tc_FF (invalid_field_access e)
                            end)
                         | _ => tc_FF (deref_byvalue ty)
                        end
 | _ => tc_FF (invalid_expression e)
end

with typecheck_lvalue (Delta: tycontext) (e: expr) : tc_assert :=
match e with
 | Evar id ty => match get_var_type Delta id with 
                  | Some ty' => tc_bool (eqb_type ty ty') 
                                           (mismatch_context_type ty ty')        
                  | None => tc_FF (var_not_in_tycontext Delta id)
                 end
 | Ederef a ty => tc_andp 
                       (tc_andp 
                          (typecheck_expr Delta a) 
                          (tc_bool (is_pointer_type (typeof a))(op_result_type e)))
                       (tc_isptr a)
 | Efield a i ty => tc_andp 
                         (typecheck_lvalue Delta a) 
                         (match typeof a with
                            | Tstruct id fList att =>
                              match field_offset i fList with 
                                | Errors.OK delta => tc_TT
                                | _ => tc_FF (invalid_struct_field i fList)
                              end
                            | Tunion id fList att => tc_TT
                            | _ => tc_FF (invalid_field_access e)
                          end)
 | _  => tc_FF (invalid_lvalue e)
end.

Definition implicit_deref (t: type) : type :=
  match t with
  | Tarray t' _ _ => Tpointer t' noattr
  | _ => t
  end.

Definition typecheck_temp_id id ty Delta a : tc_assert :=
  match (temp_types Delta)!id with
  | Some (t,_) => 
      tc_andp (tc_bool (is_neutral_cast (implicit_deref ty) t) (invalid_cast ty t)) 
                  (isCastResultType (implicit_deref ty) t t a)
  | None => tc_FF (var_not_in_tycontext Delta id)
 end.

Fixpoint tc_might_be_true (asn : tc_assert) :=
match asn with
 | tc_FF _ => false
 | tc_andp' a1 a2 => tc_might_be_true a1 && tc_might_be_true a2
 | _ => true
end.

Fixpoint tc_always_true (asn : tc_assert) := 
match asn with
 | tc_TT => true
 | tc_andp' a1 a2 => tc_always_true a1 && tc_always_true a2
 | _ => false
end.



(* A more standard typechecker, should approximate the c typechecker,
might need to add a tc_noproof for nested loads*)
Definition typecheck_b Delta e :=  tc_might_be_true (typecheck_expr Delta e).

(*Definition of the original *pure* typechecker where true means the expression
will always evaluate, may not be useful since tc_denote will just compute to true
on these assertions*)
Definition typecheck_pure_b Delta e := tc_always_true (typecheck_expr Delta e). 

Fixpoint typecheck_exprlist (Delta : tycontext) (tl : list type) (el : list expr) : tc_assert :=
match tl,el with
| t::tl', e:: el' => tc_andp (typecheck_expr Delta (Ecast e t)) 
                      (typecheck_exprlist Delta tl' el')
| nil, nil => tc_TT
| _, _ => tc_FF wrong_signature
end.


Definition typecheck_val (v: val) (ty: type) : bool :=
 match v, ty with
 | Vint i, Tint _ _ _ => true  
 | Vlong i, Tlong _ _ => true
 | Vfloat v, Tfloat _ _ => true  
 | Vint i, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tcomp_ptr _ _) => 
                    (Int.eq i Int.zero) 
(* | Vlong i, (Tpointer _ _ | Tarray _ _ _ | Tfunction _ _ _ | Tcomp_ptr _ _) => 
                    (Int64.eq i Int64.zero)  *)
 | Vptr b z,  (Tpointer _ _ | Tarray _ _ _ 
                   | Tfunction _ _ _ | Tstruct _ _ _ 
                   | Tunion _ _ _ | Tcomp_ptr _ _) => true
 | Vundef, _ => false
 | _, _ => false
 end.

Fixpoint typecheck_vals (v: list val) (ty: list type) : bool :=
 match v, ty with
 | v1::vs , t1::ts => typecheck_val v1 t1 && typecheck_vals vs ts
 | nil, nil => true
 | _, _ => false
end.


(** Environment typechecking functions **)

Definition typecheck_temp_environ
(te: tenviron) (tc: PTree.t (type * bool)) :=
forall id b ty , tc ! id = Some (ty,b) -> exists v, (Map.get te id = Some v /\ ((is_true (negb b)) \/ (typecheck_val v ty) = true)). 

Definition typecheck_var_environ
(ve: venviron) (tc: PTree.t type) :=
forall id ty, tc ! id = Some (ty) ->
exists v, Map.get ve id = Some(v,ty).

Definition typecheck_glob_environ 
(ge: genviron) (tc: PTree.t global_spec) :=
forall id  t,  tc ! id = Some t -> 
((exists b, 
(ge id = Some b /\ typecheck_val (Vptr b Int.zero) (globtype t) = true))).

Definition same_env (rho:environ) (Delta:tycontext)  :=
forall id t, (glob_types Delta) ! id = Some t ->
(ve_of rho) id = None \/ exists t,  (var_types Delta) ! id = Some t. 

(*
Definition same_mode (ge: genviron) (ve:venviron) 
                     (gt : PTree.t global_spec) (vt : PTree.t type) id  :=
match (vt ! id), (gt ! id), ve id  with
| None, Some _, Some _ => false
| _, _, _  => true
end.

Fixpoint same_env  (rho : environ) (Delta : tycontext) (ids : list positive) : bool :=
match ids with
| h::t => same_mode (ge_of rho) (ve_of rho) (glob_types Delta) (var_types Delta) h && same_env rho Delta t
| nil => true
end. 

Definition all_var_ids (Delta : tycontext) : list positive :=
(fst (split (PTree.elements (glob_types Delta)))). 
*)

Definition typecheck_environ (Delta: tycontext)  (rho : environ) :=
typecheck_temp_environ (te_of rho) (temp_types Delta) /\
typecheck_var_environ  (ve_of rho) (var_types Delta) /\
typecheck_glob_environ (ge_of rho) (glob_types Delta) /\
same_env rho Delta.
 

(** Denotation functions for each of the assertions that can be produced by the typechecker **)

Definition denote_tc_iszero v :=
         match v with Vint i => is_true (Int.eq i Int.zero) 
                            | Vlong i => is_true (Int.eq (Int.repr (Int64.unsigned i)) Int.zero)
                            | _ => False 
         end.

Definition denote_tc_nonzero v := 
         match v with Vint i => if negb (Int.eq i Int.zero) then True else False
                                               | _ => False end.

Definition denote_tc_igt i v :=
     match v with | Vint i1 => is_true (Int.ltu i1 i)
                     | _ => False
                  end.

Definition denote_tc_Zge z v := 
          match v with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => is_true (Zge_bool z n)
                                    | None => False
                                   end
                     | _ => False 
                  end.

Definition denote_tc_Zle z v := 
          match v with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => is_true (Zle_bool z n)
                                    | None => False
                                   end
                     | _ => False 
                  end.

Definition denote_tc_samebase v1 v2 :=
                         match v1, v2 with
                           | Vptr b1 _, Vptr b2 _ => is_true (peq b1 b2)
                           | _, _ => False 
                         end.

(** Case for division of int min by -1, which would cause overflow **)
Definition denote_tc_nodivover v1 v2 :=
match v1, v2 with
                           | Vint n1, Vint n2 => is_true (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone))
                           | _ , _ => False
                          end.

Definition denote_tc_initialized id ty rho := exists v, Map.get (te_of rho) id = Some v
                                            /\ is_true (typecheck_val v ty).

Fixpoint denote_tc_assert (a: tc_assert) : environ -> Prop :=
  match a with
  | tc_FF _ => `False
  | tc_noproof => `False
  | tc_TT => `True
  | tc_andp' b c => `and (denote_tc_assert b) (denote_tc_assert c)
  | tc_orp' b c => `or (denote_tc_assert b) (denote_tc_assert c)
  | tc_nonzero' e => `denote_tc_nonzero (eval_expr e)
  | tc_isptr e => `isptr (eval_expr e)
  | tc_ilt' e i => `(denote_tc_igt i) (eval_expr e)
  | tc_Zle e z => `(denote_tc_Zge z) (eval_expr e)
  | tc_Zge e z => `(denote_tc_Zle z) (eval_expr e)
  | tc_samebase e1 e2 => `denote_tc_samebase (eval_expr e1) (eval_expr e2)
  | tc_nodivover' v1 v2 => `denote_tc_nodivover (eval_expr v1) (eval_expr v2)
  | tc_initialized id ty => denote_tc_initialized id ty
  | tc_iszero' e => `denote_tc_iszero (eval_expr e)
 end.

Lemma and_False: forall x, (x /\ False) = False.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma and_True: forall x, (x /\ True) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma True_and: forall x, (True /\ x) = x.
Proof.
intros; apply prop_ext; intuition.
Qed.

Lemma False_and: forall x, (False /\ x) = False.
Proof.
intros; apply prop_ext; intuition.
Qed.


Lemma tc_andp_sound : forall a1 a2 rho, denote_tc_assert (tc_andp a1 a2) rho <->  denote_tc_assert (tc_andp' a1 a2) rho. 
Proof.
intros.
 unfold tc_andp.
 destruct a1; simpl; unfold_lift;
 repeat first [rewrite False_and | rewrite True_and | rewrite and_False | rewrite and_True];
  try apply iff_refl;
  destruct a2; simpl in *; unfold_lift;
 repeat first [rewrite False_and | rewrite True_and | rewrite and_False | rewrite and_True];
  try apply iff_refl.
Qed. 

Lemma denote_tc_assert_andp: 
  forall a b rho, denote_tc_assert (tc_andp a b) rho =
             (denote_tc_assert a rho /\ denote_tc_assert b rho).
Proof.
 intros. apply prop_ext. rewrite tc_andp_sound.
 simpl; apply iff_refl.
Qed.

(** Functions that modify type environments **)
Definition initialized id (Delta: tycontext) : tycontext :=
match (temp_types Delta) ! id with
| Some (ty, _) => ( PTree.set id (ty,true) (temp_types Delta)  
                    , var_types Delta, ret_type Delta, glob_types Delta)
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
match tycon1 with  (te1, ve1, r, vl1)  =>
match tycon2 with  (te2, _, _, _)  =>
  ((join_te te1 te2), ve1, r, vl1)
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
(fold_right (fun (var : ident * funspec) => PTree.set (fst var) (Global_func (snd var))) 
      (fold_right (fun (v: ident * type) => PTree.set (fst v) (Global_var (snd v)))
         (PTree.empty _) V)
            G). 

Definition make_tycontext (params: list (ident*type)) (temps: list (ident*type)) (vars: list (ident*type))
                       (return_ty: type)
                       (V: varspecs) (G: funspecs) :  tycontext :=
(make_tycontext_t params temps, (make_tycontext_v vars), return_ty,
   make_tycontext_g V G). 

Definition func_tycontext (func: function) (V: varspecs) (G: funspecs) : tycontext :=
  make_tycontext (func.(fn_params)) (func.(fn_temps)) (func.(fn_vars)) (func.(fn_return)) V G.

Definition nofunc_tycontext (V: varspecs) (G: funspecs) : tycontext :=
   make_tycontext nil nil nil Tvoid V G.

(** Type-checking of function parameters **)

Fixpoint match_fsig_aux (bl: list expr) (tl: list (ident*type)) : bool :=
 match bl, tl with
 | b::bl', (_,t'):: tl' => if eqb_type (typeof b) t' then match_fsig_aux bl' tl' else false
 | nil, nil => true
 | nil, _::_ => false
 | _::_, nil => false
 end.

Definition match_fsig (fsig: funsig) (bl: list expr) (ret: option ident) : bool :=
  andb (match_fsig_aux bl (fst fsig))
          (match snd fsig, ret with 
            | Tvoid , None => true 
            | Tvoid, Some _ => false
            | _, None => false
            | _, Some _ => true
            end).

Lemma match_fsig_e: forall fsig bl ret,
  match_fsig fsig bl ret = true ->
  map typeof bl = map (@snd _ _) (fst fsig) /\ (snd fsig=Tvoid <-> ret=None).
Proof.
 intros.
 apply andb_true_iff in H.
 destruct H.
 split. clear H0.
 forget (fst fsig) as tl.
 revert tl H; induction bl; destruct tl; intros; inv H.
  reflexivity.
 destruct p.
 revert H1; case_eq (eqb_type (typeof a) t); intros.
 apply eqb_type_true in H. subst; simpl in *. f_equal; auto.
 inv H1.
 clear H.
 destruct (snd fsig); destruct ret; intuition congruence.
Qed.

Fixpoint id_in_list (id: ident) (ids: list ident) : bool :=
 match ids with i::ids' => orb (Peqb id i) (id_in_list id ids') | _ => false end. 

Fixpoint compute_list_norepet (ids: list ident) : bool :=
 match ids with
 | id :: ids' => if id_in_list id ids' then false else compute_list_norepet ids'
 | nil => true
 end.

Lemma id_in_list_true: forall i ids, id_in_list i ids = true -> In i ids.
Proof.
 induction ids; simpl; intros. inv H. apply orb_true_iff in H; destruct H; auto.
 apply Peqb_true_eq in H. subst; auto.
Qed.

Lemma id_in_list_false: forall i ids, id_in_list i ids = false -> ~In i ids.
Proof.
 induction ids; simpl; intros; auto.
 apply orb_false_iff in H. destruct H.
 intros [?|?]. subst.
 rewrite Peqb_refl in H; inv H.
 apply IHids; auto.
Qed.

Lemma compute_list_norepet_e: forall ids, 
     compute_list_norepet ids = true -> list_norepet ids.
Proof.
 induction ids; simpl; intros.
 constructor.
 revert H; case_eq (id_in_list a ids); intros.
 inv H0.
 constructor; auto.
 apply id_in_list_false in H.
 auto.
Qed.


Definition expr_closed_wrt_vars (S: ident -> Prop) (e: expr) : Prop := 
  forall rho te',  
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     eval_expr e rho = eval_expr e (mkEnviron (ge_of rho) (ve_of rho) te').

Definition lvalue_closed_wrt_vars (S: ident -> Prop) (e: expr) : Prop := 
  forall rho te',  
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     eval_lvalue e rho = eval_lvalue e (mkEnviron (ge_of rho) (ve_of rho) te').

Definition env_set (rho: environ) (x: ident) (v: val) : environ :=
  mkEnviron (ge_of rho) (ve_of rho) (Map.set x v (te_of rho)).


Lemma eval_id_same: forall rho id v, eval_id id (env_set rho id v) = v.
Proof. unfold eval_id; intros; simpl. unfold force_val. rewrite Map.gss. auto.
Qed.
Hint Rewrite eval_id_same : normalize.

Lemma eval_id_other: forall rho id id' v,
   id<>id' -> eval_id id' (env_set rho id v) = eval_id id' rho.
Proof.
 unfold eval_id, force_val; intros. simpl. rewrite Map.gso; auto.
Qed.
Hint Rewrite eval_id_other using solve [clear; intro Hx; inversion Hx] : normalize.


Definition typecheck_store e1 := 
(is_int_type (typeof e1) = true -> typeof e1 = Tint I32 Signed noattr) /\
(is_float_type (typeof e1) = true -> typeof e1 = Tfloat F64 noattr).

(*Typechecking facts to help semax_store go through until it gets generalized*)

Ltac tc_assert_ext := 
repeat match goal with
| [H : _ /\ _ |- _] => destruct H
end.

Ltac of_bool_destruct :=
match goal with
  | [ |- context[Val.of_bool ?X] ] => destruct X
end.

Lemma orb_if : forall {D} b c (d:D) (e:D), (if (b || c) then d else e) = if b then d else if c then d else e.
intros.
remember (b || c). destruct b0; auto. symmetry in Heqb0. rewrite orb_true_iff in Heqb0.
intuition; subst; auto. destruct b; auto. symmetry in Heqb0; rewrite orb_false_iff in Heqb0.
intuition; subst; auto.
Qed.

Lemma andb_if : forall {D} b c (d:D) (e:D), (if (b && c) then d else e) = if b then (if c then d else e) else e.
Proof.
intros.
remember (b&&c). destruct b0; symmetry in Heqb0; try rewrite andb_true_iff in *; try rewrite andb_false_iff in *; if_tac; auto; intuition;
destruct c; auto; intuition.
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
 /\ (forall id, sub_option ((glob_types Delta) ! id) ((glob_types Delta') ! id)).               

Definition tycontext_eqv (Delta Delta' : tycontext) : Prop :=
 (forall id, (temp_types Delta) ! id = (temp_types Delta') ! id)
 /\ (forall id, (var_types Delta) ! id = (var_types Delta') ! id)
 /\ ret_type Delta = ret_type Delta'
 /\ (forall id, (glob_types Delta) ! id = (glob_types Delta') ! id).
                
Lemma join_tycon_same: forall Delta, tycontext_eqv (join_tycon Delta Delta) Delta.
Proof.
 intros.
 destruct Delta as [[[? ?] ?] ?].
 unfold join_tycon.
 repeat split; auto.
 intros. unfold temp_types. simpl.
 unfold join_te.
 rewrite PTree.fold_spec.
 rewrite <- fold_left_rev_right.
 case_eq (t ! id); intros.
 pose proof (PTree.elements_correct _ _ H).
 pose proof (PTree.elements_keys_norepet t).
 rewrite in_rev in H0.
 rewrite <- list_norepet_rev in H1. rewrite <- map_rev in H1.
 change PTree.elt with positive in *.
 revert H0 H1; induction (rev (PTree.elements t)); intros.
 inv H0.
 inv H1.
 simpl in H0. destruct H0. subst a.
 simpl. unfold join_te'. destruct p. rewrite H. rewrite andb_diag.
 rewrite PTree.gss.
 destruct b; simpl ;auto.
 simpl. unfold join_te' at 1. destruct a. simpl. destruct p1. simpl in H4.
 case_eq (t ! p0);intros. destruct p1.
 rewrite PTree.gso. auto.
 intro; subst p0. apply H4. change id with (fst (id,p)). apply in_map; auto.
 auto.
 assert (~ In id (map fst (PTree.elements t))).
 intro. apply in_map_iff in H0. destruct H0 as [[id' v] [? ?]]. simpl in *; subst id'.
 apply PTree.elements_complete in H1. congruence.
 rewrite in_rev in H0. rewrite <- map_rev in H0.
 revert H0; induction (rev (PTree.elements t)); intros. simpl. rewrite PTree.gempty; auto.
 simpl. destruct a. simpl. unfold join_te' at 1. destruct p0.
 destruct (eq_dec p id). subst p. rewrite  H. apply IHl; auto.
 contradict H0; simpl; auto.
 case_eq (t ! p); intros. destruct p0. 
 rewrite PTree.gso.
 apply IHl. contradict H0;simpl; auto.
 intro; subst p; congruence.
 apply IHl. contradict H0;simpl; auto.
Qed.

Lemma tycontext_eqv_symm:
  forall Delta Delta', tycontext_eqv Delta Delta' ->  tycontext_eqv Delta' Delta.
Proof.
intros.
destruct H as [? [? [? ?]]]; repeat split; auto.
Qed.

Lemma int_eq_e: forall i j, Int.eq i j = true -> i=j.
Proof. intros. pose proof (Int.eq_spec i j); rewrite H in H0; auto. Qed.

Lemma tc_val_eq: tc_val = fun t v => typecheck_val v t = true.
Proof.
extensionality t v.
unfold tc_val.
destruct t,v; try reflexivity;
apply prop_ext; intuition; try apply I;
simpl in *; subst;
try apply Int.eq_true;
try solve [apply int_eq_e; auto].
Qed.


Lemma neutral_isCastResultType:
  forall t t' v rho,
   is_neutral_cast t' t = true ->
   denote_tc_assert (isCastResultType t' t t v) rho.
Proof.
intros.
  unfold isCastResultType;
  destruct t',t; inv H; try apply I.
* destruct i,i0; inv H1; simpl; try apply I; if_tac; apply I.
* simpl. if_tac; apply I.
Qed.

(*A boolean denote_tc_assert *)

Definition denote_tc_iszero_b v :=
         match v with Vint i => (Int.eq i Int.zero) 
                            | Vlong i =>  (Int.eq (Int.repr (Int64.unsigned i)) Int.zero)
                            | _ => false 
         end.

Definition denote_tc_nonzero_b v := 
         match v with Vint i => if negb (Int.eq i Int.zero) then true else false
                                               | _ => false end.

Definition denote_tc_igt_b i v :=
     match v with | Vint i1 => (Int.ltu i1 i)
                     | _ => false
                  end.

Definition denote_tc_Zge_b z v := 
          match v with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => (Zge_bool z n)
                                    | None => false
                                   end
                     | _ => false 
                  end.

Definition denote_tc_Zle_b z v := 
          match v with
                     | Vfloat f => match Float.Zoffloat f with
                                    | Some n => (Zle_bool z n)
                                    | None => false
                                   end
                     | _ => false 
                  end.

Definition denote_tc_samebase_b v1 v2 :=
                         match v1, v2 with
                           | Vptr b1 _, Vptr b2 _ => (peq b1 b2)
                           | _, _ => false 
                         end.

(** Case for division of int min by -1, which would cause overflow **)
Definition denote_tc_nodivover_b v1 v2 :=
match v1, v2 with
                           | Vint n1, Vint n2 => (negb 
                                   (Int.eq n1 (Int.repr Int.min_signed) 
                                    && Int.eq n2 Int.mone))
                           | _ , _ => false
                          end.

Definition denote_tc_initialized_b id ty rho := 
match Map.get (te_of rho) id with 
| Some v => typecheck_val v ty
| None => false
end.

Definition isptr_b v := 
   match v with | Vptr _ _ => true | _ => false end.

Fixpoint denote_tc_assert_b (a: tc_assert) : environ -> bool :=
  match a with
  | tc_FF _ => `false
  | tc_noproof => `false
  | tc_TT => `true
  | tc_andp' b c => `andb (denote_tc_assert_b b) (denote_tc_assert_b c)
  | tc_orp' b c => `orb (denote_tc_assert_b b) (denote_tc_assert_b c)
  | tc_nonzero' e => `denote_tc_nonzero_b (eval_expr e)
  | tc_isptr e => `isptr_b (eval_expr e)
  | tc_ilt' e i => `(denote_tc_igt_b i) (eval_expr e)
  | tc_Zle e z => `(denote_tc_Zge_b z) (eval_expr e)
  | tc_Zge e z => `(denote_tc_Zle_b z) (eval_expr e)
  | tc_samebase e1 e2 => `denote_tc_samebase_b (eval_expr e1) (eval_expr e2)
  | tc_nodivover' v1 v2 => `denote_tc_nodivover_b (eval_expr v1) (eval_expr v2)
  | tc_initialized id ty => denote_tc_initialized_b id ty
  | tc_iszero' e => `denote_tc_iszero_b (eval_expr e)
 end.

Lemma false_true : False <-> false=true.
intuition.
Qed.

Lemma true_false : False <-> true=false.
intuition.
Qed.

Lemma true_true : True <-> true = true.
intuition.
Qed.

Lemma false_false : True <-> false = false.
intuition.
Qed. 

Hint Rewrite <- false_true : bool.
Hint Rewrite <- true_false : bool.
Hint Rewrite <- false_false : bool.
Hint Rewrite <- true_true : bool.
Hint Rewrite andb_true_iff : bool.
Hint Rewrite orb_true_iff : bool.
Hint Rewrite andb_false_iff : bool.
Hint Rewrite orb_false_iff : bool.
Hint Rewrite andb_false_r : bool.
Hint Rewrite andb_true_r : bool.
Hint Rewrite orb_false_r : bool.
Hint Rewrite orb_true_r : bool.

Ltac bool_r:=
try unfold is_true; autorewrite with bool; try symmetry; autorewrite with bool; auto.

Ltac bool_n H := 
try unfold is_true in H; autorewrite with bool in H; try symmetry in H; autorewrite with bool in H; auto.

Ltac bool_s :=
try unfold is_true in *; autorewrite with bool in *; try symmetry in *; autorewrite with bool in *; auto.


Tactic Notation "bool_r" "in" ident(H) :=
bool_n H.

Tactic Notation "bool_r" "in" "*" :=
bool_s.

Definition denote_te_assert_b_eq : forall a rho, 
denote_tc_assert a rho <-> is_true (denote_tc_assert_b a rho).
Proof. intros. split; intros.
induction a; simpl in *; super_unfold_lift; bool_r in *; intuition;
simpl in *;
try destruct (eval_expr e); simpl in *;
try match goal with 
| [ H : if ?e then True else False |- _ ] => destruct e; simpl; inv H
| [ H : match ?e with | _ => _  end |- _ ] => destruct e; simpl in *; inv H
end; auto; try congruence;
unfold denote_tc_initialized, denote_tc_initialized_b in *.
destruct (denote_tc_assert_b a1 rho); try contradiction; apply I.
destruct (denote_tc_assert_b a1 rho); try contradiction; apply I.
destruct (Float.Zoffloat f); try contradiction.
destruct (z >=? z0); try contradiction; auto.
destruct (Float.Zoffloat f); try contradiction.
destruct (z <=? z0); try contradiction; auto.
destruct (eval_expr e0 rho); try contradiction.
destruct (peq b b0); try contradiction; auto.
destruct (eval_expr e0 rho); try contradiction.
destruct (negb (Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone)); try contradiction; auto.
destruct H. destruct H; rewrite H. auto.

induction a; simpl in *; super_unfold_lift; bool_r in *; intuition; try congruence;
simpl in *;
try destruct (eval_expr e); simpl in *; try congruence;
try match goal with 
| [ H : (if ?e then true else false) = true |- _ ] => destruct e; simpl; inv H
| [ H : (match ?e with | _ => _ end) = true |- _ ] => destruct e; simpl in *; inv H
end; auto; try congruence.
unfold denote_tc_initialized, denote_tc_initialized_b in *.
destruct (denote_tc_assert_b a1 rho); try contradiction; auto.
destruct (denote_tc_assert_b a1 rho); try contradiction; auto.
destruct (denote_tc_assert_b a1 rho); try contradiction; auto.
destruct (negb (Int.eq i Int.zero)); try contradiction; auto.
destruct (Float.Zoffloat f); try contradiction.
destruct (z >=? z0); try contradiction; auto.
destruct (Float.Zoffloat f); try contradiction.
destruct (z <=? z0); try contradiction; auto.
destruct (eval_expr e0 rho); try contradiction.
destruct (peq b b0); try contradiction; auto.
destruct (eval_expr e0 rho); try contradiction.
destruct (negb (Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone)); try contradiction; auto.
unfold denote_tc_initialized_b in H.
destruct (Map.get (te_of rho) e) eqn:?; try contradiction.
exists v; split; auto.
Qed.
