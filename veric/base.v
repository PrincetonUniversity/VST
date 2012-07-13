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

Definition filter_genv (ge: Clight.genv) : genviron :=
  fun id => match Genv.find_symbol ge id with
                   | Some b => match Clight.type_of_global ge b with
                                        | Some t => Some (Vptr b Int.zero, t)
                                        | None => Some (Vptr b Int.zero, Tvoid)
                                        end
                   | None => None
                   end. 

Definition ge_of (rho: environ) : genviron :=
  match rho with mkEnviron ge ve te => ge end.

Definition ve_of (rho: environ) : Clight.env :=
  match rho with mkEnviron ge ve te => ve end.

Definition te_of (rho: environ) : Clight.temp_env :=
  match rho with mkEnviron ge ve te => te end.

Definition mkEnviron' (ge: Clight.genv) (ve: Clight.env) (te: Clight.temp_env) :=
  mkEnviron (filter_genv ge) ve te.

Definition empty_environ (ge: Clight.genv) := mkEnviron (filter_genv ge) (Maps.PTree.empty _) (Maps.PTree.empty _).

Definition opt2list (A: Type) (x: option A) :=
  match x with Some a => a::nil | None => nil end.
Implicit Arguments opt2list.

Definition force_val (v: option val) : val :=
 match v with Some v' => v' | None => Vundef end.

Definition arguments := list (val* type).
Definition funsig := (typelist * type)%type. (* argument and result signature *)

