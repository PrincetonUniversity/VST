Require Import Arith.
Require Import List.
Require Import msl.base.
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
| IfThenElse: expr -> control -> control -> control
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
 | ((stk,hp), IfThenElse x c1 c2) =>
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
Notation "'If' x 'Then' c1 'Else' c2" := (IfThenElse x c1 c2)  (at level 200, x at level 90, c1 at level 200, c2 at level 200).

Definition safe (p: program) : Prop :=  forall n, exists sk', run p n = Some sk'.

(* LOCAL VARIABLE ENVIRONMENTS *)

Definition env := var -> adr.

Definition env_set (f: env) (x: var) (y: adr) :=
   fun i => if eq_dec i x then y else f i.

Lemma env_gss : forall s x y, env_set s x y x = y.
Proof. unfold env_set; intros.  destruct (eq_dec x x); auto. congruence.
Qed.
Lemma env_gso: forall s x y z, x<>z -> env_set s x y z = s z.
Proof. unfold env_set; intros. destruct (eq_dec z x); auto. congruence.
Qed.

Definition locals2env (s: locals) : env :=
   fun x => match table_get s x with Some a => a | None => 0 end.

Fixpoint eval (e: expr) : env -> adr :=
 fun s =>
 match e with
 | Const n => n
 | Var x => s x
 | Offset e n => n + eval e s
 | Mem e => 0
 end.

Definition eval_list (xs: list expr) : env -> (list adr) := fun s => map (fun e => eval e s) xs.

Lemma offset_zero:  forall a, eval (a .+ 0) = eval a.
Proof. intros. extensionality s; simpl; destruct (eval a s); simpl; f_equal; auto.
Qed.

Lemma offset_offset: forall a n m,
  eval ((a .+ n) .+ m) = eval (a .+ (n+m)).
Proof.
 intros.
 extensionality s. simpl.
Transparent adr. unfold adr; omega.
Opaque adr.
Qed.

Definition arguments (vars: list var) (vl: list adr) : env :=
      locals2env (mk_locals vars vl).
Opaque arguments.


Lemma locals2env_table_set:
  forall x y s, locals2env (table_set x y s) = env_set (locals2env s) x y.
Proof. intros; extensionality i. unfold locals2env, env_set, table_set.
  simpl. destruct (eq_dec i x); auto.
Qed.

Definition subst{A} (x: var) (v: adr) (P: env -> A) : env -> A :=
   fun s => P (env_set s x v).


(* TYPE-CHECKING OF LOCAL VARIABLES *)
Require Import msl.Coqlib2.

Require ListSet.
Definition varset : Type := ListSet.set var.
Definition vs_mem: var -> varset -> bool := ListSet.set_mem EqDec_var.
Definition vs_add: var -> varset -> varset := ListSet.set_add EqDec_var.

Definition varcompat (vars: varset) (s: locals) :=
   forall i, vs_mem i vars = true -> table_get s i <> None.

Fixpoint expcheck (vars: varset) (e: expr) :=
  match e with
  | Const _ => true
  | Var v => vs_mem v vars
  | Offset e n => expcheck vars e
  | Mem _ => false
  end.

Fixpoint typecheck (vars: varset) (c: control) : bool :=
 match c with
  | Assign (Var v) (Mem e) c' => andb (expcheck vars e)
                                         (typecheck (vs_add v vars) c')
  | Assign (Var v) e c' => andb (expcheck vars e)
                                         (typecheck (vs_add v vars) c')
  | Assign (Mem e1) e2 c' => andb (andb (expcheck vars e1)  (expcheck vars e2))
                                         (typecheck vars c')
  | IfThenElse e c1 c2 => andb (expcheck vars e)
                                            (andb (typecheck vars c1) (typecheck vars c2))
  | Go e el => andb (expcheck vars e)  (forallb (expcheck vars) el)
  | _ => false
  end.

Lemma eval_expr_get:
  forall vars s h e,
              expcheck vars e = true ->
              varcompat vars s ->
              expr_get s h e = Some (eval e (locals2env s)).
Proof. induction e; simpl; auto; intros.
  apply H0 in H. unfold locals2env.
 destruct (table_get s v); auto. congruence.
  specialize (IHe H H0). rewrite IHe. simpl.   f_equal; omega.
  inv H.
Qed.

Lemma eval_expr_get_list:
  forall vars s h el,
              forallb (expcheck vars) el = true ->
              varcompat vars s ->
              get_list s h el = Some (eval_list el (locals2env s)).
Proof. induction el; simpl; auto; intros.
 rewrite andb_true_iff in H; destruct H.
  rewrite (eval_expr_get vars s h a); auto. simpl.
  rewrite (IHel H1 H0); auto.
Qed.

Lemma varcompat_add:
  forall x vars z s, varcompat vars s -> varcompat (vs_add x vars) (table_set x z s).
Proof.
 intros. intros i ?. specialize (H i).
 unfold vs_mem, vs_add in *.
 apply ListSet.set_mem_correct1 in H0.
 destruct (eq_dec i x).
 subst. rewrite table_gss. congruence.
 rewrite table_gso; auto. apply H.
 apply ListSet.set_add_elim2 in H0; auto.
 apply ListSet.set_mem_correct2; auto.
Qed.

Lemma varcompat_mk_locals:
  forall xl vl, length xl <= length vl -> varcompat xl (mk_locals xl vl).
Proof.
 unfold varcompat, vs_mem, mk_locals. intros.
 revert vl H H0; induction xl; destruct vl; intros.
 apply ListSet.set_mem_correct1 in H0. inv H0.
 apply ListSet.set_mem_correct1 in H0. inv H0.
 inv H. simpl in H.
 specialize (IHxl vl). spec IHxl ; [ omega |].
 apply ListSet.set_mem_correct1 in H0. simpl in H0. destruct H0.
 subst. simpl.
destruct (eq_dec i i); auto. congruence.
 simpl. destruct (eq_dec i a). congruence.
 apply IHxl.
 apply ListSet.set_mem_correct2. auto.
Qed.

Definition inlist {A: Type}{EA: EqDec A} (x: A) (vl: list A) : bool :=
   existsb (fun y => if eq_dec x y then true else false) vl.

Lemma inlist_notIn {A: Type}{EA: EqDec A}:
  forall (x: A) (vl: list A), inlist x vl = false -> ~ In x vl.
Proof.
  induction vl; simpl; intros; intuition.
  subst. destruct (eq_dec x x); auto. inv H.
  destruct (eq_dec x a). inv H. simpl in H. auto.
Qed.

Fixpoint list_nodups {A: Type}{EA: EqDec A} (vl: list A) : bool :=
  match vl with
  | nil => true
  | x::xl => andb (negb (inlist x xl)) (list_nodups xl)
  end.

Inductive list_norepet {A: Type} : list A -> Prop :=
  | list_norepet_nil:
      list_norepet nil
  | list_norepet_cons:
      forall hd tl,
      ~(In hd tl) -> list_norepet tl -> list_norepet (hd :: tl).

Lemma nodups_norepet  {A: Type}{EA: EqDec A} :
    forall l, list_nodups l = true -> list_norepet l.
Proof. induction l; intros.
  constructor.
  simpl in H. apply andb_true_iff in H.
  destruct H.
  constructor; auto.
  apply inlist_notIn. destruct (inlist a l); auto; inv H.
Qed.

(* SAFE FOR N STEPS *)

Definition safeN (p: program) (sk: state) (n: nat) : Prop :=
   exists sk', stepN p sk n = Some sk'.

Lemma stepN_plus: forall p sk1 n1 n2 sk3,
   stepN p sk1 (n1+n2) = Some sk3 <->
   (exists sk2, stepN p sk1 n1 = Some sk2 /\ stepN p sk2 n2 = Some sk3).
Proof.
 induction n1; intros.
 simpl; split; eauto. intros [sk2 [? ?]]. inv H; auto.
 replace (S n1 + n2) with (n1 + S n2) by omega.
 rewrite (IHn1 (S n2) sk3).
 split; intros [sk2 [? ?]].
 simpl in H0; invSome.
 exists s. split; auto.
 replace (S n1) with (n1 + 1) by omega.
 rewrite (IHn1 1). exists sk2; split; simpl; auto. rewrite H0; auto.
 replace (S n1) with (n1 + 1) in H by omega.
 rewrite (IHn1 1) in H. destruct H as [sk4 [? ?]].
 exists sk4; split; simpl; auto. simpl in H1.  invSome. auto.
Qed.

Lemma safeN_less: forall p sk n1 n2, n1 <= n2 -> safeN p sk n2 -> safeN p sk n1.
Proof.
 intros.
 assert (n2 = n1 + (n2-n1)) by omega.
 rewrite H1 in H,H0.
 forget (n2-n1) as k.
 clear n2 H1 H.
 destruct H0 as [sk' ?].
 rewrite stepN_plus in H.
 destruct H as [sk2 [? ?]]; exists sk2; auto.
Qed.

Lemma safeN_step:
  forall p sk sk' n, step p sk = Some sk' -> (safeN p sk (S n) <-> safeN p sk' n).
Proof.
  unfold safeN; intros.
  split; intros [sk2 ?].
  exists sk2.
 simpl in H0. rewrite H in H0. auto.
  exists sk2; simpl.  rewrite H; auto.
Qed.

