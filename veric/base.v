Load loadpath.
Require Export Axioms.
Require Export Coqlib.
Require Export AST.
Require Export Integers.
Require Export Floats.
Require Export Values.
Require Export Maps.
Require Export Memdata.
Require Export Memtype.
Require Export Memory.
Require Export Globalenvs.
Require Export Ctypes.
Require Export Clight.

Require Export EqNat.
Require Export veric.Coqlib2.
Require Export Relations.

Set Implicit Arguments.

(***** GENERAL KV-Maps *****)

Module Map. Section map.
Variables (B : Type).

Definition t := positive -> option B.

Definition get (h: t) (a:positive) : option B := h a.

Definition set (a:positive) (v: B) (h: t) : t :=
  fun i => if ident_eq i a then Some v else h i.   

Definition remove (a: positive) (h: t) : t :=
  fun i => if ident_eq i a then None else h i.

Definition empty : t := fun _ => None.

(* MAP Axioms 
 *)

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


Definition genviron := Map.t (val*type).

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

Definition force_val (v: option val) : val :=
 match v with Some v' => v' | None => Vundef end.

Fixpoint typelist2list (tl: typelist) : list type :=
 match tl with Tcons t r => t::typelist2list r | Tnil => nil end.

Definition funsig := (list (ident*type) * type)%type. (* argument and result signature *)

Definition modified0 : ident -> Prop := fun _ => False.
Definition modified1 id : ident -> Prop := fun i => i=id.
Definition modified2 (s1 s2: ident -> Prop) := fun i => s1 i \/ s2 i.

Fixpoint modifiedvars (c: statement) : ident -> Prop :=
 match c with
 | Sset id e => modified1 id
 | Sifthenelse _ c1 c2 => modified2 (modifiedvars c1) (modifiedvars c2)
 | Scall (Some id) _ _ => modified1 id
 | Sbuiltin (Some id) _ _ _ => modified1 id
 | Ssequence c1 c2 =>  modified2 (modifiedvars c1) (modifiedvars c2)
 | Sloop c1 c2 => modified2 (modifiedvars c1) (modifiedvars c2)
 | Sswitch e cs => modifiedvars_ls cs
 | Slabel _ c => modifiedvars c
 | _ => modified0
 end
 with
 modifiedvars_ls (cs: labeled_statements) : ident -> Prop := 
 match cs with
 | LSdefault _ => modified0
 | LScase _ c ls => modified2 (modifiedvars c) (modifiedvars_ls ls)
 end.


Definition filter_genv (ge: Clight.genv) : genviron :=
  fun id => match Genv.find_symbol ge id with
                   | Some b => match Clight.type_of_global ge b with
                                        | Some t => Some (Vptr b Int.zero, t)
                                        | None => Some (Vptr b Int.zero, Tvoid)
                                        end
                   | None => None
                   end. 

Definition make_tenv (te : Clight.temp_env) : tenviron := fun id => PTree.get id te.

Definition make_venv (te : Clight.env) : venviron := fun id => PTree.get id te.

Definition construct_rho ge ve te:= mkEnviron ge (make_venv ve) (make_tenv te) . 

Definition empty_environ (ge: Clight.genv) := mkEnviron (filter_genv ge) (Map.empty _) (Map.empty _).
