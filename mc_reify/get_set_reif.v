Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.

Definition DEAD : expr typ func := Inj (typ:=typ) (inr (Other fFalse)).

Definition as_tree (e : expr typ func) : option
  ((typ * expr typ func * expr typ func * expr typ func) + typ) := 
match e with
  | (App (App (App (Inj (inr (Data (fnode t)))) l) o) r) =>
    Some (inl (t, l, o, r))
  | (Inj (inr (Data (fleaf t)))) =>
    Some (inr t)
  | _ => None
end.

Fixpoint set_reif (i : positive) (v : expr typ func) (m : expr typ func) :  expr typ func :=
match (as_tree m) with
  | Some (inl (t,l,o,r)) (* Node l o r *)=>
    match i with 
      | xH => node l (some_reif v t) r t
      | xO ii => node (set_reif ii v l) o r t
      | xI ii => node l o (set_reif ii v r) t
    end
  | Some (inr t) => 
    match i with
      | xH => node (leaf t) (some_reif v t) (leaf t) t
      | xO ii => node (set_reif ii v (leaf t)) (none_reif t) (leaf t) t
      | xI ii => node (leaf t) (none_reif t) (set_reif ii v (leaf t)) t
    end
  | _ => DEAD
end.


Fixpoint get_reif (i : positive) (m : expr typ func) :  expr typ func :=
match (as_tree m) with
  | Some (inl (t,l,o,r)) (* Node l o r *)=>
    match i with 
      | xH => some_reif o t
      | xO ii => get_reif ii l 
      | xI ii => get_reif ii r 
    end
  | Some (inr t) => none_reif t
  | _ => DEAD
end.

