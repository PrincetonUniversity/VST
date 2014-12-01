Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.

Fixpoint set_reif (i : positive) (v : expr typ func) (m : expr typ func) :  expr typ func :=
match m with
  | (App (App (App (Inj (inr (Data (fnode t)))) l) o) r) (* Node l o r *)=>
    match i with 
      | xH => node l (some_reif v t) r t
      | xO ii => node (set_reif ii v l) o r t
      | xI ii => node l o (set_reif ii v r) t
    end
  | (Inj (inr (Data (fleaf t)))) => 
    match i with
      | xH => node (leaf t) (some_reif v t) (leaf t) t
      | xO ii => node (set_reif ii v (leaf t)) (none_reif t) (leaf t) t
      | xI ii => node (leaf t) (none_reif t) (set_reif ii v (leaf t)) t
    end
  | _ => Inj (inr (Other fFalse))
end.
Locate PTree.set.
Lemma set_reif_eq :
forall typ i v vr t tr tbl , 
Some v = reflect tbl nil nil vr typ ->
Some t = reflect tbl nil nil tr (typtree typ) ->
Some (PTree.set i v t) = reflect tbl nil nil (set_reif i vr vr) (typtree typ).
Admitted.

Lemma set_reif_eq2 :
forall typ i vr tr tbl,
reflect tbl nil nil (App (App (Inj (inr (Data (fset typ i)))) vr) tr) (typtree typ) =
reflect tbl nil nil (set_reif i vr tr) (typtree typ).
Proof.
Admitted.

Fixpoint get_reif (i : positive) (m : expr typ func) :  expr typ func :=
match m with
  | (App (App (App (Inj (inr (Data (fnode t)))) l) o) r) (* Node l o r *)=>
    match i with 
      | xH => some_reif o t
      | xO ii => get_reif ii l 
      | xI ii => get_reif ii r 
    end
  | (Inj (inr (Data (fleaf t)))) => none_reif t
  | _ => Inj (inr (Other fFalse))
end.

Lemma get_reif_eq :
forall typ i  t tr tbl , 
Some t = reflect tbl nil nil tr (typtree typ) ->
Some (PTree.get i t) = reflect tbl nil nil (get_reif i tr) (tyoption typ).
Admitted.

Lemma get_reif_eq2 :
forall typ i tr tbl,
reflect tbl nil nil (App (Inj (inr (Data (fget typ i)))) tr) (tyoption typ) =
reflect tbl nil nil (get_reif i tr) (tyoption typ).
Proof.
Admitted.