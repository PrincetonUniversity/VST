Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.
Locate expr.
Definition as_tree (e : expr typ func) : option
  ((typ * expr typ func * expr typ func * expr typ func) + typ) :=
match e with
  | (App (App (App (Inj (inr (Data (fnode t)))) l) o) r) =>
    Some (inl (t, l, o, r))
  | (Inj (inr (Data (fleaf t)))) =>
    Some (inr t)
  | _ => None
end.

Fixpoint set_reif (i : positive) (v : expr typ func) (m : expr typ func) (ty : typ) :  expr typ func :=
match (as_tree m) with
  | Some (inl (t,l,o,r)) (* Node l o r *)=>
    match i with
      | xH => node l (some_reif v t) r ty
      | xO ii => node (set_reif ii v l ty) o r t
      | xI ii => node l o (set_reif ii v r ty) t
    end
  | Some (inr t) =>
    match i with
      | xH => node (leaf t) (some_reif v t) (leaf t) ty
      | xO ii => node (set_reif ii v (leaf t) ty) (none_reif t) (leaf t) t
      | xI ii => node (leaf t) (none_reif t) (set_reif ii v (leaf t) ty) t
    end
  | _ => (App (App (Inj (inr (Data (fset ty i)))) v) m)
end.


Fixpoint get_reif (i : positive) (m : expr typ func) ty :  expr typ func :=
match (as_tree m) with
  | Some (inl (t,l,o,r)) (* Node l o r *)=>
    match i with
      | xH => o
      | xO ii => get_reif ii l ty
      | xI ii => get_reif ii r ty
    end
  | Some (inr t) => none_reif t
  | _ => (App (Inj (inr (Data (fget ty i))))  m)
end.

