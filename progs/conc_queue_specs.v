Require Import progs.conclib.
Require Import progs.conc_queue.
Require Import SetoidList.
Require Import floyd.library.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tqueue := Tstruct _queue noattr.
Definition tqueue_t := Tstruct _queue_t noattr.

Definition MAX := 10.

(* Ghost histories in the style of
   History-based Verification of Functional Behaviour of Concurrent Programs,
   Blom, Huisman, and Zharieva-Stojanovski (VerCors)
   Twente tech report, 2015 *)

Inductive hist_el {t} := QAdd (p : val) (v : reptype t) | QRem (p : val) (v : reptype t).
Notation hist t := (list (@hist_el t)).
Fixpoint consistent {t} (h : hist t) a b :=
  match h with
  | [] => a = b
  | QAdd p v :: h' => consistent h' (a ++ [(p, v)]) b
  | QRem p v :: h' => match a with [] => False | v' :: q' => v' = (p, v) /\ consistent h' q' b end
  end.

Parameter ghost : forall (sh : share) {t} (f : share * hist t) (p : val), mpred.
(*Parameter ghost_factory : mpred.

Axiom ghost_alloc : forall Espec D P Q R C P',
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost_factory :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx R))) C P'.
Axiom new_ghost : forall Espec D P Q R C P' t v,
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost_factory ::
    (EX p : val, ghost Tsh t v p) :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost_factory :: R)))) C P'.
Axiom alloc_conflict : ghost_factory * ghost_factory |-- FF.*)

(* In effect, we want two different ways of splitting/combining history shares.
   One combines the histories as well; the other guarantees injectivity on histories. *)

(* This is definitely unsound, since we can repeat it. *)
Axiom new_ghost : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' t' t v p,
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, ([] : hist t')) p :: data_at Tsh t v p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (data_at Tsh t v p :: R)))) C P'.

Inductive list_incl {A} : list A -> list A -> Prop :=
| incl_nil l : list_incl [] l
| incl_skip l1 a l2 (Hincl : list_incl l1 l2) : list_incl l1 (a :: l2)
| incl_cons a l1 l2 (Hincl : list_incl l1 l2) : list_incl (a :: l1) (a :: l2).
Hint Constructors list_incl.

Axiom ghost_share_join : forall sh1 sh2 sh t (h1 h2 : hist t) p, sepalg.join sh1 sh2 Tsh -> list_incl h1 h2 ->
  ghost sh1 (sh, h1) p * ghost sh2 (Tsh, h2) p = ghost Tsh (Tsh, h2) p.
Axiom hist_share_join : forall sh sh1 sh2 sh' t (h1 h2 : hist t) p, sepalg.join sh1 sh2 sh' ->
  ghost sh (sh1, h1) p * ghost sh (sh2, h2) p = ghost sh (sh', h1 ++ h2) p.
Axiom hist_add : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' t (h : hist t) e p,
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, h ++ [e]) p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, h) p :: R)))) C P'.
Axiom ghost_inj : forall sh1 sh2 sh t (h1 h2 : hist t) p, ghost sh1 (sh, h1) p * ghost sh2 (Tsh, h2) p
  |-- !!(list_incl h1 h2).
Axiom ghost_inj_Tsh : forall sh1 sh2 t (h1 h2 : hist t) p, ghost sh1 (Tsh, h1) p * ghost sh2 (Tsh, h2) p
  |-- !!(h1 = h2).

(*Axiom ghost_conflict : forall sh1 sh2 t1 t2 v1 v2 p,
  ghost sh1 t1 v1 p * ghost sh2 t2 v2 p |-- !!sepalg.joins sh1 sh2.*)

Definition q_lock_pred' t P p vals head (addc remc : val) lock gsh h :=
  !!(Zlength vals <= MAX /\ 0 <= head < MAX /\ consistent h [] vals) &&
  (data_at Tsh tqueue (rotate (complete MAX (map fst vals)) head MAX, (vint (Zlength vals),
                      (vint head, (vint ((head + Zlength vals) mod MAX), (addc, remc))))) p *
   cond_var Tsh addc * cond_var Tsh remc * malloc_token Tsh (sizeof tqueue_t) p *
   malloc_token Tsh (sizeof tcond) addc * malloc_token Tsh (sizeof tcond) remc *
   malloc_token Tsh (sizeof tlock) lock * ghost gsh (Tsh, h) p *
   fold_right sepcon emp (map (fun x => let '(p, v) := x in 
     !!(P v) && (data_at Tsh t v p * malloc_token Tsh (sizeof t) p)) vals)).

Definition q_lock_pred t P p lock gsh := EX vals : list (val * reptype t), EX head : Z,
  EX addc : val, EX remc : val, EX h : hist t, q_lock_pred' t P p vals head addc remc lock gsh h.

Definition lqueue lsh t P p lock gsh1 gsh2 (h : hist t) :=
  !!(sepalg.join gsh1 gsh2 Tsh /\ field_compatible tqueue_t [] p) &&
  (field_at lsh tqueue_t [StructField _lock] lock p *
   lock_inv lsh lock (q_lock_pred t P p lock gsh2) * ghost gsh1 (lsh, h) p).

Definition q_new_spec' :=
  WITH Q : {t : type & reptype t -> Prop}, gsh1 : share, gsh2 : share
  PRE [ ]
   PROP (sepalg.join gsh1 gsh2 Tsh)
   LOCAL ()
   SEP ()
  POST [ tptr tqueue_t ]
   let (t, P) := Q in
   EX newq : val, EX lock : val,
   PROP () LOCAL (temp ret_temp newq)
   SEP (lqueue Tsh t P newq lock gsh1 gsh2 []).
Definition q_new_spec prog := DECLARE (ext_link_prog prog "q_new") q_new_spec'.

Definition q_del_spec' :=
  WITH Q : {t : type & ((reptype t -> Prop) * hist t)%type}, p : val, lock : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t) ]
   let (t, R) := Q in let (P, h) := R in
   PROP (consistent h [] [])
   LOCAL (temp _tgt p)
   SEP (lqueue Tsh t P p lock gsh1 gsh2 h)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP ().
Definition q_del_spec prog := DECLARE (ext_link_prog prog "q_del") q_del_spec'.

Definition q_add_spec' :=
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist t * reptype t)%type}, p : val, lock : val,
       e : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t), _r OF (tptr tvoid) ]
   let (t, R) := Q in let (S, v) := R in let (P, h) := S in
   PROP (readable_share sh; P v)
   LOCAL (temp _tgt p; temp _r e)
   SEP (lqueue sh t P p lock gsh1 gsh2 h; data_at Tsh t v e; malloc_token Tsh (sizeof t) e)
  POST [ tvoid ]
   let (t, R) := Q in let (S, v) := R in let (P, h) := S in
   PROP ()
   LOCAL ()
   SEP (lqueue sh t P p lock gsh1 gsh2 (h ++ [QAdd e v])).
Definition q_add_spec prog := DECLARE (ext_link_prog prog "q_add") q_add_spec'.

Definition q_remove_spec' :=
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist t)%type}, p : val, lock : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t) ]
   let (t, R) := Q in let (P, h) := R in
   PROP (readable_share sh)
   LOCAL (temp _tgt p)
   SEP (lqueue sh t P p lock gsh1 gsh2 h)
  POST [ tptr tvoid ]
   let (t, R) := Q in let (P, h) := R in
   EX e : val, EX v : reptype t,
   PROP (P v)
   LOCAL (temp ret_temp e)
   SEP (lqueue sh t P p lock gsh1 gsh2 (h ++ [QRem e v]); data_at Tsh t v e; malloc_token Tsh (sizeof t) e).
Definition q_remove_spec prog := DECLARE (ext_link_prog prog "q_remove") q_remove_spec'.

Definition q_tryremove_spec' :=
  WITH sh : share, Q : {t : type & ((reptype t -> Prop) * hist t)%type}, p : val, lock : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t) ]
   let (t, R) := Q in let (P, h) := R in
   PROP (readable_share sh)
   LOCAL (temp _tgt p)
   SEP (lqueue sh t P p lock gsh1 gsh2 h)
  POST [ tptr tvoid ]
   let (t, R) := Q in let (P, h) := R in
   EX e : val,
   PROP ()
   LOCAL (temp ret_temp e)
   SEP (if eq_dec e nullval then lqueue sh t P p lock gsh1 gsh2 h else
        (EX v : reptype t, !!(P v) &&
         (lqueue sh t P p lock gsh1 gsh2 (h ++ [QRem e v]) * data_at Tsh t v e * malloc_token Tsh (sizeof t) e))).
Definition q_tryremove_spec prog := DECLARE (ext_link_prog prog "q_tryremove") q_tryremove_spec'.
