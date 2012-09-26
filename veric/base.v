Require Export compcert.Axioms.
Require Export compcert.Coqlib.
Require Export compcert.AST.
Require Export compcert.Integers.
Require Export compcert.Floats.
Require Export compcert.Values.
Require Export compcert.Maps.
Require Export compcert.Memdata.
Require Export compcert.Memtype.
Require Export compcert.Memory.
Require Export compcert.Globalenvs.
Require Export compcert.Ctypes.
Require Export compcert.Clight.

Require Export EqNat.
Require Export veric.Coqlib2.
Require Export Relations.


Definition genviron := ident -> option (val*type).

Inductive environ : Type :=
 mkEnviron: forall (ge: genviron) (ve: Clight.env) (te: Clight.temp_env), environ.

Definition ge_of (rho: environ) : genviron :=
  match rho with mkEnviron ge ve te => ge end.

Definition ve_of (rho: environ) : Clight.env :=
  match rho with mkEnviron ge ve te => ve end.

Definition te_of (rho: environ) : Clight.temp_env :=
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
 | Ssequence c1 c2 =>  modified2 (modifiedvars c1) (modifiedvars c2)
 | Swhile e c => modifiedvars c
 | Sdowhile e c => modifiedvars c
 | Sfor' e c1 c2 => modified2 (modifiedvars c1) (modifiedvars c2)
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

Definition empty_environ (ge: Clight.genv) := mkEnviron (filter_genv ge) (Maps.PTree.empty _) (Maps.PTree.empty _).
