Require Import Arith.
Require Import List.
Require Import msl.eq_dec.

Definition table (A B : Type) := list (A*B).

Fixpoint table_get {A B}{H: EqDec A} (rho: table A B) (x: A) : option B :=
  match rho with
  | (y,v)::ys => if eq_dec x y then Some v else table_get ys x
  | nil => None
 end.

Definition table_set {A B}{H: EqDec A} (x: A) (v: B) (rho: table A B)  : table A B := (x,v)::rho.

Lemma table_gss {A B}{H: EqDec A}: forall rho x (v: B), table_get (table_set x v rho) x = Some v.
Proof.
intros.
simpl. destruct (eq_dec x x); auto. contradiction n; auto.
Qed.

Lemma table_gso {A B}{H: EqDec A}: forall rho x y (v:B), x<>y -> table_get (table_set x v rho) y = table_get rho y.
Proof.
intros.
simpl. destruct (eq_dec y x); auto.  contradiction H0; auto.
Qed.


Definition var := nat.
Definition adr := nat.
Definition stack := table var adr.
Definition heap := table adr adr.
Definition state := (stack * heap)%type.

Definition bind_option (A B: Type) (f: option A) (g: A -> option B) : option B :=
  match f with None => None | Some x => g x end.

Implicit Arguments bind_option [A B].

Notation "'do1' X '<-' A ';' B" := (bind_option A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).

Inductive command := 
| Assign: var -> var -> command
| Load : var -> var -> command
| Store: var -> var -> command
| Seq: command -> command -> command.

Fixpoint exec (c: command) (s: state) := 
 match c , s with
 | Assign x y , (stk,hp) => 
                           do1 v <- table_get stk y; 
                           Some (table_set x v stk, hp)
 | Load x y , (stk, hp) => 
                           do1 v <- table_get stk y;
                           do1 v' <- table_get hp v;
                           Some (table_set x v' stk, hp)
 | Store x y, (stk, hp) => 
                           do1 v <- table_get stk y;
                           do1 p <- table_get stk x;
                           Some (stk, table_set p v hp)
 | Seq c1 c2, s => do1 s' <- exec c1 s; exec c2 s'
 end.
