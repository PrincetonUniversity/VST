Require Import language.
Require Import msl.base.
Require Import msl.seplog.
Require Import msl.alg_seplog.

Local Open Scope logic.

Module Type SEMAX.

  Parameter mpred : Type.
  Parameter Nm: NatDed mpred.  Existing Instance Nm.
  Parameter Sm: SepLog mpred.  Existing Instance Sm.
  Parameter Cm: ClassicalSep mpred.  Existing Instance Cm.
  Parameter Im: Indir mpred.  Existing Instance Im.
  Parameter Rm: RecIndir mpred.  Existing Instance Rm.
  Parameter SIm: SepIndir mpred.  Existing Instance SIm.
  Parameter SRm: SepRec mpred.  Existing Instance SRm.

  Parameter mapsto: forall (v1 v2: adr), mpred.

  Axiom mapsto_conflict:  forall a b c, mapsto a b  *  mapsto a c |-- FF.

  Definition assert := env -> mpred.
  Bind Scope logic with assert.

  Definition funspec := (list var * assert)%type.
  Definition funspecs := table adr funspec.

  Definition call (P: list var * assert) (vl: list adr) : mpred :=
     (!! (length vl = length (fst P)) && snd P (arguments (fst P) vl)).
  Parameter cont: forall (nP: funspec)  (v: adr), mpred.

Definition funassert (G: funspecs) : mpred :=
   (ALL  i:_, ALL P:_,  !! (table_get G i = Some P) --> cont P i)  &&
   (ALL  i:_, ALL P:_,  cont P i --> !! exists P', table_get G i = Some P').


  Axiom funassert_get:
  forall G v nP,  funassert  G && cont nP v |--
                      EX P':assert, (ALL vl:list adr, |> ! (call nP vl <=> call (fst nP,P') vl)) && !! (table_get G v = Some (fst nP,P')).

  Parameter allocpool: forall (b: adr), mpred.
  Axiom alloc: forall b, allocpool b = ((!! (b > 0) && mapsto b 0) * allocpool (S b)).

  Parameter semax : varset -> funspecs -> assert -> control -> Prop.
  Parameter semax_func: forall (G: funspecs) (p: program) (G': funspecs), Prop.

  Axiom semax_func_nil: forall G, semax_func G nil nil.
  Axiom semax_func_cons:
   forall  fs id f vars P (G G': funspecs),
      inlist id (map (@fst adr (list var * control)) fs) = false ->
      list_nodups vars = true ->
      length vars = length (fst P) ->
      semax vars G (fun s => call P (map s vars)) f ->
      semax_func G fs G' ->
      semax_func G ((id, (vars,f))::fs) ((id, P) :: G').

  Definition program_proved (p: program) :=
   exists G, semax_func G p G
                            /\ table_get G 0 = Some  (0::nil, fun s => allocpool (eval (Var 0) s)).

  Axiom semax_sound:
  forall p, program_proved p -> forall n, run p n <> None.

  Axiom semax_go:  forall vars G (P: funspec) x ys,
    typecheck vars (Go x ys) = true ->
    semax vars G (fun s => cont P (eval x s) && call P (eval_list ys s)) (Go x ys) .

Axiom semax_assign: forall x y c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c ->
    semax vars G (fun s => |> subst x (eval y s) P s) (Do x := y ; c).

Axiom semax_if: forall x c1 c2 vars G (P: assert),
    expcheck vars x = true ->
    semax vars G (fun s => !!(eval x s <> 0) && P s) c1 ->
    semax vars G (fun s => !! (eval x s = 0) && P s) c2 ->
    semax vars G P (If x Then c1 Else c2).

Axiom semax_load:  forall x y z c vars G P,
    expcheck vars y = true ->
    semax (vs_add x vars) G P c ->
    semax vars G (fun s => (mapsto (eval y s) z * TT) && |> subst x z P s)
               (Do x := Mem y ; c).

Axiom semax_store: forall x y v c vars G (P: assert),
    expcheck vars x = true ->
    expcheck vars y = true ->
    semax vars G (fun s => mapsto (eval x s) (eval y s) * P s) c ->
    semax vars G (fun s => mapsto (eval x s) v  * P s)  (Do Mem x  := y ; c).

Axiom semax_pre:
  forall P P' vars G c, (forall s, P s |-- P' s) -> semax vars G P' c -> semax vars G P c.

Axiom semax_exp: forall A vars G (P: A -> assert) c,
    typecheck vars c = true ->
    (forall v:A, semax vars G (P v) c) ->
    semax vars G (fun s => EX v:A, (P v s)) c.

Axiom semax_exp': forall A (any: A) vars G (P: A -> assert) c,
    (forall v:A, semax vars G (P v) c) ->
    semax vars G (fun s => EX v:A, (P v s)) c.

Axiom semax_prop:
  forall (R: Prop) vars G P c,
      typecheck vars c = true ->
      (R -> semax vars G P c) ->
      semax vars G (fun s => !! R && P s) c.

Axiom semax_G:
   forall vars G P c, semax vars G (fun s => P s && funassert G) c -> semax vars G P c.


End SEMAX.




