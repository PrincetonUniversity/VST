Require Import VST.floyd.proofauto.
Require Import VST.progs.int_or_ptr.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Inductive tree := 
| LEAF: forall i, 0 <= i <= Int.max_signed -> tree
| NODE: tree -> tree -> tree.

Fixpoint treerep (t: tree) (p: val) : mpred :=
  match t with
  | LEAF i _ => !! (p = Vint (Int.repr (i+i+1))) && emp
  | NODE t1 t2 => EX p1:val, EX p2: val,
               data_at Tsh (Tstruct _tree noattr) (p1,p2) p
              * treerep t1 p1 * treerep t2 p2
  end.

Definition POINTER_BOUNDARY : Z := 1024.

Definition valid_int_or_ptr (x: val) :=
 match x with
 | Vint i => Int.testbit i 0 = true
              \/ Int.unsigned i < POINTER_BOUNDARY
 | Vptr b z => Ptrofs.testbit z 0 = false
 | _ => False
 end.

Lemma valid_int_or_ptr_ii1:
 forall i, valid_int_or_ptr (Vint (Int.repr (i + i + 1))).
Proof.
intros.
simpl.
left.
rewrite Int.unsigned_repr_eq.
rewrite Zodd_mod.
apply Zeq_is_eq_bool.
replace (i+i) with (2*i)%Z by omega.
rewrite <- Zmod_div_mod; try omega.
rewrite Z.mul_comm, Z.add_comm.
rewrite Z_mod_plus_full.
reflexivity.
compute; reflexivity.
exists (Z.div Int.modulus 2).
reflexivity.
Qed.


Lemma valid_int_or_ptr_i2:
 forall i, 0 <= i < POINTER_BOUNDARY ->
   valid_int_or_ptr (Vint (Int.repr i)).
Proof.
intros.
simpl.
right.
unfold POINTER_BOUNDARY in *.
rewrite Int.unsigned_repr by rep_omega.
rep_omega.
Qed.

Lemma field_compatible_valid_int_or_ptr:
  forall p, 
  field_compatible (Tstruct _tree noattr) [] p ->
  valid_int_or_ptr p.
Proof.
intros.
destruct H as [H1 [_ [_ [H2 _]]]].
destruct p; try contradiction.
clear - H2; simpl in *.
    rewrite Zodd_even_bool.
    apply negb_false_iff.
    apply Zeven_bool_iff.
    inv H2.
    1: inv H.
    inv H1.
    specialize (H4 _left _ _ eq_refl eq_refl).
    inv H4.
    inv H.
    simpl in H0.
    destruct H0 as [j H].
    rewrite Z.add_0_r in H.
    rewrite H; clear.
    replace (j*4)%Z with (2*(2*j))%Z by omega.
    apply Zeven_2p.
Qed.

Lemma treerep_local_facts:
  forall t p,
   treerep t p |--
   !! (valid_int_or_ptr p).
Proof.
intros.
destruct t; simpl.
entailer!.
apply valid_int_or_ptr_ii1.
Intros p1 p2.
entailer!.
apply field_compatible_valid_int_or_ptr; auto.
Qed.

Hint Resolve treerep_local_facts : saturate_local.

Definition test_int_or_ptr_spec :=
 DECLARE _test_int_or_ptr
 WITH x : val
 PRE [ _x OF int_or_ptr_type ]
   PROP(valid_int_or_ptr x) LOCAL(temp _x x) SEP()
 POST [ tint ]
   PROP() 
   LOCAL(temp ret_temp 
          (Vint (Int.repr (match x with
                    | Vint _ => 1
                    | _ => 0
                    end))))
   SEP().

Definition int_or_ptr_to_int_spec :=
 DECLARE _int_or_ptr_to_int
 WITH x : val
 PRE [ _x OF int_or_ptr_type ]
   PROP(is_int I32 Signed x) LOCAL(temp _x x) SEP()
 POST [ tint ]
   PROP() LOCAL (temp ret_temp x) SEP().

Definition int_or_ptr_to_ptr_spec :=
 DECLARE _int_or_ptr_to_ptr
 WITH x : val
 PRE [ _x OF int_or_ptr_type ]
   PROP(isptr x) LOCAL(temp _x x) SEP()
 POST [ tptr tvoid ]
   PROP() LOCAL (temp ret_temp x) SEP().

Definition int_to_int_or_ptr_spec :=
 DECLARE _int_to_int_or_ptr
 WITH x : val
 PRE [ _x OF tint ]
   PROP(valid_int_or_ptr x)
   LOCAL(temp _x x) SEP()
 POST [ int_or_ptr_type ]
   PROP() LOCAL (temp ret_temp x) SEP().

Definition ptr_to_int_or_ptr_spec :=
 DECLARE _ptr_to_int_or_ptr
 WITH x : val
 PRE [ _x OF tptr tvoid ]
   PROP(valid_int_or_ptr x) LOCAL(temp _x x) SEP()
 POST [ int_or_ptr_type ]
   PROP() LOCAL (temp ret_temp x) SEP().

Definition makenode_spec :=
 DECLARE _makenode 
  WITH p: val, q: val
  PRE [ _left OF int_or_ptr_type, _right OF int_or_ptr_type ]
    PROP() LOCAL(temp _left p; temp _right q) SEP()
  POST [ tptr (Tstruct _tree noattr) ]
    EX r:val, 
    PROP() LOCAL(temp ret_temp r) 
    SEP (data_at Tsh (Tstruct _tree noattr) (p,q) r).

Definition copytree_spec :=
 DECLARE _copytree
  WITH t: tree, p : val
  PRE  [ _t OF int_or_ptr_type ]
    PROP() LOCAL(temp _t p) SEP (treerep t p)
  POST [ int_or_ptr_type ]
    EX v:val,
    PROP() LOCAL(temp ret_temp v) 
    SEP (treerep t p; treerep t v).

Definition Gprog : funspecs :=
    ltac:(with_library prog [
    test_int_or_ptr_spec;
    int_or_ptr_to_int_spec;
    int_or_ptr_to_ptr_spec;
    int_to_int_or_ptr_spec;
    ptr_to_int_or_ptr_spec;
    makenode_spec; copytree_spec
  ]).

Lemma body_copytree: semax_body Vprog Gprog f_copytree copytree_spec.
Proof.
  start_function.
  assert_PROP (valid_int_or_ptr p) by entailer!.
  destruct t.
* (* LEAF *)
 unfold treerep.
 Intros. subst p.
 forward_call (Vint (Int.repr (i+i+1))).
 forward_if.
 - (* then clause *)
   forward.
   Exists (Vint (Int.repr(i+i+1))).
   entailer!.
 - (* else clause *)
  inv H0.
* (* NODE *) 
  unfold treerep; fold treerep.
  rename p into t.
  Intros p q.
  forward_call t.
  assert_PROP (isptr t) by entailer!.
  destruct t; try contradiction. clear H0.
  forward_if.
  - (* then clause *)
    contradiction.
  - (* else clause *)
   clear H0. simpl in H.
   forward_call (Vptr b i).
   apply I.
   forward.
     entailer!.
     destruct p; try contradiction; apply I.
   forward_call (t1,p).
   Intros p1.
   deadvars.
   forward.
   forward.
    entailer!.
     destruct q; try contradiction; apply I.
   forward_call (t2,q).
   Intros p2.
   forward.
   deadvars.
   forward_call (p1,p2).
  Intros r.
  assert_PROP (valid_int_or_ptr r). {
    entailer!.
    apply field_compatible_valid_int_or_ptr; auto.
  }
  forward_call r.
  forward.
  Exists r p q p1 p2.
  entailer!.
Qed.


