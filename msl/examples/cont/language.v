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
Instance EqDec_var: EqDec var := _.
Opaque var.

Definition adr := nat.
Instance EqDec_adr : EqDec adr := _.
Opaque adr.

Definition locals := table var adr.
Definition heap := adr -> option adr.

Inductive expr := 
 | Const: adr -> expr
 | Var: var -> expr
 | Offset: expr -> nat -> expr
 | Mem: expr -> expr.

Coercion Var : var >-> expr.
Coercion Const: adr >-> expr.
Notation " a '.+' n " := (Offset a n) (at level 87, no associativity).

Inductive control := 
| Assign: expr -> expr -> control -> control
| If: expr -> control -> control -> control
| Go: expr -> list expr -> control.

Definition program := table adr (list var * control).

Definition bind_option (A B: Type) (f: option A) (g: A -> option B) : option B :=
  match f with None => None | Some x => g x end.

Implicit Arguments bind_option [A B].

Notation "'do1' X '<-' A ';' B" := (bind_option A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).

Definition emptyheap : heap := fun _ => None.
Definition heap_get (h: heap) (a: adr) : option adr := h a.
Definition heap_set (a v: adr) (h: heap) := 
   fun i => if eq_dec i a then Some v else h i.

Lemma heap_gss: forall h x v, heap_get (heap_set x v h) x = Some v.
Proof.
unfold heap_get, heap_set; intros. destruct (eq_dec x x); auto. contradiction n; auto.
Qed.

Lemma heap_gso: forall h x y v, x<>y -> heap_get (heap_set x v h) y = heap_get h y.
Proof.
unfold heap_get, heap_set;  intros.
simpl. destruct (eq_dec y x); auto.  contradiction H; auto.
Qed.

Opaque heap.

Fixpoint expr_get (s: locals)(h: heap) (e: expr) : option adr :=
 match e with
 | Const n => Some n
 | Var x => table_get s x
 | Offset e n => do1 v <- expr_get s h e; Some (v+n)
 | Mem e => do1 v <- expr_get s h e; heap_get h v
 end.

Fixpoint get_list s h (xs: list expr) : option (list adr) :=
  match xs with 
  | nil => Some nil 
  | e :: es => do1 v <- expr_get s h e; do1 vs <- get_list s h es; Some (v::vs)
 end.

Definition mk_locals  (xs: list var) (ys: list adr) : locals := combine xs ys.

Definition state := (locals * heap * control)%type.


Definition step (p: program) (sk: state) : option state := 
 match sk with
 | ((stk,hp), Assign (Var x) y c) => 
                           do1 v <- expr_get stk hp y; 
                           Some ((table_set x v stk, hp), c)
 | ((stk,hp), Assign (Mem x) y c) => 
                           do1 v <- expr_get stk hp y;
                           do1 p <- expr_get stk hp x;
                           Some ((stk, heap_set p v hp), c)
 | (_, Assign _ y c) => None
 | ((stk,hp), If x c1 c2) => 
                           do1 v <- expr_get stk hp x;
                           Some (if eq_dec v 0 then ((stk,hp), c2) else ((stk,hp), c1))
 | ((stk, hp), Go x ys) =>   
                           do1 v <- expr_get stk hp x;
                           do1 k <- table_get p v;
                           do1 vs <- get_list stk hp ys;
                           Some ((mk_locals (fst k) vs, hp), snd k)
 end.

Fixpoint stepN (p: program) (sk: state) (n: nat) : option state :=
  match n with O => Some sk 
  | S n' => match step p sk with Some sk' => stepN p sk' n' | _ => None end
  end.

Fixpoint boundary (p: program) : nat :=
  match p with (n, _)::p' => Max.max (S n) (boundary p') | nil => 2 end.

Definition initial_locals (p: program) : locals := (0, boundary p)::nil.

Definition initial_heap (p: program) : heap :=
    fun i => if lt_dec i (boundary p) then None else Some 0.

Definition run (p: program) (n: nat) : option state := 
    stepN p (nil, initial_heap p, Go (Const 0) (Const (boundary p) :: nil)) n.

Notation "'Do' x ':=' v ';' c" := (Assign x v c) (at level 200, x at level 1, v at level 90, c at level 200).
Notation "'If' x 'Then' c1 'Else' c2" := (If x c1 c2)  (at level 200, x at level 90, c1 at level 200, c2 at level 200).

Definition safe (p: program) : Prop :=  forall n, exists sk', run p n = Some sk'.
