Require Import AST.
Require Import Coqlib.
Require Import sepcomp.Memory.
Require Import Values.
Require Import Integers.
Require Import sepcomp.Events.

Require Import sepcomp.extspec.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.mem_lemmas.

Definition is_ptr (v: val) := exists b ofs, v = Vptr b ofs.

(* can't define as a fixpoint because there may be cycles *)

Inductive ptr_closure (b: block) (ofs: Z) (m: mem): block -> Z -> Prop :=
| ptr_closure_base: forall ofs', ptr_closure b ofs m b ofs'
| ptr_closure_trans: forall b'' ofs'' b' ofs',
  Mem.load Mint32 m b ofs = Some (Vptr b'' ofs'') -> 
  ptr_closure b'' (Int.intval ofs'') m b' ofs' -> 
  ptr_closure b ofs m b' ofs'.

Definition closure (v: val) (m: mem): val -> Prop :=
  fun v': val => match v, v' with 
                   | Vptr b ofs, Vptr b' ofs' => 
                     ptr_closure b (Int.intval ofs) m b' (Int.intval ofs')
                   | _, _ => False
                 end.

Definition val_not_reserved (v: option val) (m: mem) :=
  match v with Some v' => 
    forall b ofs, closure v' m (Vptr b ofs) -> ~reserved m b (Int.intval ofs)
  | None => True
  end.

Lemma val_not_reserved_base: 
  forall b ofs m,
  val_not_reserved (Some (Vptr b ofs)) m -> 
  ~reserved m b (Int.intval ofs).
Proof.
intros b ofs m NR.
hnf in NR.
specialize (NR b ofs).
intros CONTRA.
destruct NR.
solve[econstructor].
solve[auto].
Qed.

(*TODO: move elsewhere*)
Definition val_valid_opt (v: option val) (m: mem) :=
  match v with
  | None => True
  | Some v' => val_valid v' m
  end.

Section compile_safety.
  Context {G C D Z: Type}.
  Context (Hcore: EffectfulSemantics G C D).

  Variable ge: G.

  CoInductive compile_safe: Z -> C -> mem -> Prop :=
  | compile_safe_halt: 
    forall z c m ret, 
      safely_halted Hcore c = Some ret -> 
      val_not_reserved (Some ret) m -> 
      val_valid ret m -> 
      compile_safe z c m
  | compile_safe_external: 
    forall z c m e sig args, 
      at_external Hcore c = Some (e, sig, args) -> 
      (forall v, In v args -> val_not_reserved (Some v) m /\ val_valid v m) -> 
      (forall (z': Z) m' ret c',
        mem_forward m m' -> 
        val_not_reserved ret m' -> 
        val_valid_opt ret m' -> 
        after_external Hcore ret c = Some c' -> 
        compile_safe z' c' m') ->  
    compile_safe z c m.
    
End compile_safety.


