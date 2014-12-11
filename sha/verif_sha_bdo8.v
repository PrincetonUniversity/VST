Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Local Open Scope logic.

Lemma semax_seq_congr:  (* not provable *)
 forall (Espec: OracleKind) s1 s1' s2 s2',
  (forall Delta P R, semax Delta P s1 R <-> semax Delta P s1' R) ->
  (forall Delta P R, semax Delta P s2 R <-> semax Delta P s2' R) ->
 (forall Delta P R, 
    semax Delta P (Ssequence s1 s2) R <->
    semax Delta P (Ssequence s1' s2') R).
Abort.

Definition load8 id ofs :=
 (Sset id
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _h (tarray tuint 8))
          (Econst_int (Int.repr ofs) tint) (tptr tuint)) tuint)).

Lemma Znth_is_int:
 forall i r,
  0 <=  i < Zlength r ->
  is_int I32 Unsigned (Znth i (map Vint r) Vundef).
Proof.
intros.
unfold Znth.
rewrite if_false by omega.
rewrite (nth_map' Vint Vundef Int.zero).
apply I.
destruct H as [H0 H]; rewrite Zlength_correct in H.
rewrite <- (Z2Nat.id i) in H; auto.
apply Nat2Z.inj_lt in H; auto.
Qed.

Lemma sha256_block_load8:
  forall (Espec : OracleKind) 
     (data: val) (r_h: list int) (ctx: val) kv
   (H5 : length r_h = 8%nat),
     semax  
      (initialized _data
         (func_tycontext f_sha256_block_data_order Vprog Gtot))
  (PROP  ()
   LOCAL  (temp _data data; temp _ctx ctx; temp _in data; 
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(field_at Tsh t_struct_SHA256state_st  [StructField _h] (map Vint r_h) ctx)))
   (Ssequence (load8 _a 0)
     (Ssequence (load8 _b 1)
     (Ssequence (load8 _c 2)
     (Ssequence (load8 _d 3)
     (Ssequence (load8 _e 4)
     (Ssequence (load8 _f 5)
     (Ssequence (load8 _g 6)
     (Ssequence (load8 _h 7)
         Sskip))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (temp _a (Vint (nthi r_h 0));
                temp _b (Vint (nthi r_h 1));
                temp _c (Vint (nthi r_h 2));
                temp _d (Vint (nthi r_h 3));
                temp _e (Vint (nthi r_h 4));
                temp _f (Vint (nthi r_h 5));
                temp _g (Vint (nthi r_h 6));
                temp _h (Vint (nthi r_h 7));
                temp _data data; temp _ctx ctx; temp _in data; 
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(field_at Tsh t_struct_SHA256state_st  [StructField _h] (map Vint r_h) ctx)))).
Proof.
intros.
unfold load8.
abbreviate_semax.
normalize.
simpl.
normalize.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
abbreviate_semax.
assert (H5': Zlength r_h = 8%Z).
rewrite Zlength_correct; rewrite H5; reflexivity.
do 8 (forward; [ entailer!; apply Znth_is_int; omega | ]).
forward.  (* skip; *)
entailer. apply prop_right.
revert H0 H1 H2 H3 H4 H6 H7 H8.
clear - H5.
unfold Znth.
repeat rewrite if_false by (apply Zle_not_lt; computable).
simpl.
repeat (rewrite nth_map' with (d':=Int.zero); [ | omega]).
intros.
 inv H0; inv H1; inv H2; inv H3; inv H4; inv H6; inv H7; inv H8.
repeat split; auto.
Qed.

Definition get_h (n: Z) :=
    Sset _t
        (Ederef
           (Ebinop Oadd
              (Efield
                 (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _h (tarray tuint 8))
              (Econst_int (Int.repr n) tint) (tptr tuint)) tuint).

Definition add_h (n: Z) (i: ident) :=
   Sassign
       (Ederef
          (Ebinop Oadd
             (Efield
                (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                   t_struct_SHA256state_st) _h (tarray tuint 8))
             (Econst_int (Int.repr n) tint) (tptr tuint)) tuint)
       (Ebinop Oadd (Etempvar _t tuint) (Etempvar i tuint) tuint).

Definition add_them_back :=
 [get_h 0; add_h 0 _a;
  get_h 1; add_h 1 _b;
  get_h 2; add_h 2 _c;
  get_h 3; add_h 3 _d;
  get_h 4; add_h 4 _e;
  get_h 5; add_h 5 _f;
  get_h 6; add_h 6 _g;
  get_h 7; add_h 7 _h].

Fixpoint add_upto (k: nat) (u v: list int) {struct k} :=
 match k with
 | O => u
 | S k' => match u,v with
                | u1::us, v1::vs => Int.add u1 v1 :: add_upto k' us vs
                | _, _ => u
                end
 end.

Lemma length_add_upto:
  forall i r s,
   length r = length s  -> 
   length (add_upto i r s) = length r.
Proof.
induction i; destruct r,s; intros;
 inv H; simpl; auto.
Qed.


Lemma temp_types_init_same:
  forall (Delta : tycontext) (id : positive) (t : type),
  typeof_temp Delta id = Some t ->
  (temp_types (initialized id Delta)) ! id = Some (t, true).
Proof.
intros.
unfold typeof_temp in H.
destruct ((temp_types Delta) ! id) eqn:?; inv H.
destruct p; inv H1.
rewrite (temp_types_init_same  _ _ _ _ Heqo); auto.
Qed.


Lemma temp_types_init_any:
  forall i Delta j t,
  (temp_types Delta) ! j = Some (t,true) ->
  (temp_types (initialized i Delta)) ! j = Some (t, true).
Proof.
intros.
destruct Delta. 
unfold temp_types, initialized in *; simpl in *.
unfold temp_types; simpl. 
destruct (tyc_temps!i) eqn:?; simpl; auto.
destruct p. simpl.
destruct (ident_eq i j). subst. 
rewrite PTree.gss. congruence.
rewrite PTree.gso by auto.
auto.
Qed.

Lemma force_lengthn_short:
  forall {A} i (b: list A) v, 
     (i <= length b)%nat -> force_lengthn i b v = firstn i b.
Proof.
induction i; destruct b; intros.
reflexivity.
reflexivity.
inv H.
simpl. f_equal. apply IHi. simpl in H. omega.
Qed.

Lemma add_one_back:
 forall Espec Delta Post atoh regs ctx kv (i: nat) more i'
  (i'EQ: i' = (nth i [_a;_b;_c;_d;_e;_f;_g;_h] 1%positive)),
  length atoh = 8%nat ->
  length regs = 8%nat ->
  (forall j, (j<8)%nat -> (temp_types Delta) ! ( nth j [_a; _b; _c; _d; _e; _f; _g; _h] 1%positive) = Some (tuint, true)) ->
  (temp_types Delta) ! _ctx = Some (tptr t_struct_SHA256state_st, true) ->
  (typeof_temp Delta _t) = Some tuint ->
  (i < 8)%nat ->
  @semax Espec (initialized _t Delta)
   (PROP ()
   LOCAL  (temp _ctx ctx;
                temp _a  (Vint (nthi atoh 0));
                temp _b  (Vint (nthi atoh 1));
                temp _c  (Vint (nthi atoh 2));
                temp _d  (Vint (nthi atoh 3));
                temp _e  (Vint (nthi atoh 4));
                temp _f  (Vint (nthi atoh 5));
                temp _g  (Vint (nthi atoh 6));
                temp _h  (Vint (nthi atoh 7));
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(field_at Tsh t_struct_SHA256state_st  [StructField _h]
                      (map Vint (add_upto (S i) regs atoh)) ctx)))
    more
   Post ->
  @semax Espec Delta
   (PROP ()
   LOCAL  (temp _ctx ctx;
                temp _a  (Vint (nthi atoh 0));
                temp _b  (Vint (nthi atoh 1));
                temp _c  (Vint (nthi atoh 2));
                temp _d  (Vint (nthi atoh 3));
                temp _e  (Vint (nthi atoh 4));
                temp _f  (Vint (nthi atoh 5));
                temp _g  (Vint (nthi atoh 6));
                temp _h  (Vint (nthi atoh 7));
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP  (`(field_at Tsh t_struct_SHA256state_st  [StructField _h]
                 (map Vint (add_upto i regs atoh)) ctx)))
   (Ssequence (get_h (Z.of_nat i)) (Ssequence (add_h (Z.of_nat i) i') more))
   Post.
Proof.
intros.
subst i'.
unfold get_h.
assert (LENADD: forall k, length (add_upto k regs atoh) = 8%nat). {
clear - H H0.
intro.
forget 8%nat as n.
revert n regs atoh H0 H;
induction k; simpl; intros; auto.
destruct regs as [|r regs]; destruct atoh as [|a atoh]; auto.
destruct n; inv H0; inv H.
simpl. f_equal; auto.
}
eapply semax_seq'.
*
 ensure_normal_ret_assert;
 hoist_later_in_pre.

change  (Ederef
        (Ebinop Oadd
           (Efield
              (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                 t_struct_SHA256state_st) _h (tarray tuint 8))
           (Econst_int (Int.repr (Z.of_nat i)) tint) (tptr tuint)) tuint)
  with (nested_efield  (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                 t_struct_SHA256state_st)
             [eArraySubsc (Econst_int (Int.repr (Z.of_nat i)) tint);
              eStructField _h]
             [tuint; tarray tuint 8]).
eapply (semax_SC_field_load Delta Tsh type_id_env.empty_ti
      0 _t _ _ _ _ _ tuint t_struct_SHA256state_st 
     [eStructField _h]
     [eArraySubsc (Econst_int (Int.repr (Z.of_nat i)) tint)]
     [StructField _h]
     [ArraySubsc (Z.of_nat i)]
     [tarray tuint 8] [tuint]
     ctx (Znth (Z.of_nat i) (map Vint (add_upto i regs atoh)) Vundef)
     (map Vint (add_upto i regs atoh))  LLLL
 );
 try reflexivity; auto.
 +
    entailer!.
 + simpl efield_denote.
    entailer!.
 + entailer!.
 + 
   simpl typeof; simpl tc_LR.
   pose proof (Znth_is_int (Z.of_nat i) (add_upto i regs atoh)).
   spec H6.
   split; [ omega |].
   clear - H H0 H4.
   rewrite Zlength_correct.
    rewrite length_add_upto by congruence. rewrite H0.
    apply Nat2Z.inj_lt. auto.
   set (zz :=  (Znth (Z.of_nat i) (map Vint (add_upto i regs atoh)) Vundef)) in *.
   go_lowerx.
   saturate_local.
   normalize.
   apply prop_right; auto.
   repeat split; auto.
   hnf. unfold typecheck_lvalue.  rewrite H2.
  simpl. unfold_lift. rewrite <- H9. auto.
+
   entailer!. constructor. apply I.
   constructor. omega.
   constructor.
*
 simpl update_tycon.
 apply extract_exists_pre; intro old.
 autorewrite with subst. clear old.

assert (H6: (i < length (add_upto i regs atoh))%nat)
  by (rewrite length_add_upto; [ rewrite H0; auto | congruence]).

 unfold add_h.
eapply semax_seq'.
ensure_normal_ret_assert;
 hoist_later_in_pre.
{
eapply (semax_SC_field_store (initialized _t Delta) Tsh type_id_env.empty_ti
              0  _ _ _ _ 
      (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                 t_struct_SHA256state_st)
      (Ebinop Oadd (Etempvar _t tuint)
        (Etempvar (nth i [_a; _b; _c; _d; _e; _f; _g; _h] 1%positive) tuint)
        tuint)
     tuint t_struct_SHA256state_st 
     [eStructField _h]
     [eArraySubsc (Econst_int (Int.repr (Z.of_nat i)) tint)]
     [StructField _h]
     [ArraySubsc (Z.of_nat i)]
     [tarray tuint 8] [tuint]
     ctx 
     (Vint (Int.add (nthi (add_upto i regs atoh) (Z.of_nat i)) (nthi atoh (Z.of_nat i))))
     (map Vint (add_upto i regs atoh))
     LLLL); try reflexivity; auto.
*
 entailer!.
*
 set (i' := nth i [_a; _b; _c; _d; _e; _f; _g; _h] 1%positive).
 go_lowerx.
 apply prop_right.
 unfold_lift. rewrite <- H9.
 specialize (H1 _ H4).
 fold i' in H1.
 replace (eval_id i' rho)  with (Vint (nthi atoh (Z.of_nat i))).
 unfold Znth.
 rewrite Nat2Z.id.
 rewrite (@nth_map' int val _ _ Int.zero).
 rewrite if_false by omega.
 simpl.    
 unfold nthi. rewrite Nat2Z.id. reflexivity.
 auto.
 unfold i'.
 destruct i as [ | [ | [ | [ | [ | [ | [ | [ | ]]]]]]]]; try assumption.
 clear - H4; omega.
*
 unfold app, efield_denote.
 entailer!.
*
  entailer!.
*
 simpl tc_LR.
 set (i' := nth i [_a; _b; _c; _d; _e; _f; _g; _h] 1%positive).
 go_lowerx.
 apply andp_right. entailer!.
 hnf. unfold typecheck_lvalue.
 replace ((temp_types (initialized _t Delta)) ! _ctx) with (Some (tptr t_struct_SHA256state_st, true)).
  Focus 2. {
    clear - H3 H2.
    unfold typeof_temp in H3.
    unfold initialized.
    destruct ((temp_types Delta) ! _t) eqn:?; inversion H3.
    destruct p; inv H0. unfold temp_types.
    destruct Delta.
    unfold fst, snd. rewrite PTree.gso. auto.
    cbv. intros. inversion H.
  } Unfocus.
 simpl.
 hnf in H10. unfold_lift. rewrite <- H10. auto.
 apply andp_right; apply prop_right;
 hnf; auto.
 unfold typecheck_expr.

rewrite (temp_types_init_same _ _ _ H3).
specialize (H1 _ H4).
fold i' in H1.
rewrite (temp_types_init_any _t _ _ _ H1).
apply I.
*
unfold app. apply prop_right. constructor. apply I.
split; auto. omega.
apply I.
}
unfold replace_nth.
simpl update_tycon.
simpl upd_reptype.
 eapply semax_pre; try apply H5.
 apply (drop_LOCAL' 0); unfold delete_nth.
 intros rho.
 normalize.
 apply derives_refl'. symmetry.
 f_equal.
 unfold upd_reptype_array.
 rewrite Nat2Z.id.

rewrite force_lengthn_short by (rewrite map_length; omega).
rewrite Z2Nat.inj_add by omega.
 rewrite Nat2Z.id.
 change (Z.to_nat 1) with 1%nat.

assert (length regs = length atoh) by congruence.
assert (i < length regs)%nat by omega.
clear - H18 H19.
revert regs atoh H18 H19; induction i; destruct regs,atoh; intros;
try solve [inv H19]; inv H18.
simpl.
reflexivity.
change (map Vint (add_upto (S (S i)) (i0 :: regs) (i1 :: atoh)))
  with (Vint (Int.add i0 i1) :: map Vint (add_upto (S i) regs atoh)).
change (firstn (S i) (map Vint (add_upto (S i) (i0 :: regs) (i1 :: atoh))))
 with (Vint (Int.add i0 i1) :: firstn i (map Vint (add_upto i regs atoh))).
rewrite <- app_comm_cons.
f_equal.
simpl in H19.
rewrite (IHi regs atoh); auto; [ | omega].
clear IHi.
f_equal.
f_equal.
f_equal.
simpl add_upto.
unfold nthi.
repeat rewrite Nat2Z.id.
simpl nth.
auto.
Qed.

Lemma add_them_back_proof:
  forall (Espec : OracleKind)
     (regs regs': list int) (ctx: val) kv,
     length regs = 8%nat ->
     length regs' = 8%nat ->
     semax  Delta_loop1
   (PROP  ()
   LOCAL  (temp _ctx ctx;
                temp _a  (Vint (nthi regs' 0));
                temp _b  (Vint (nthi regs' 1));
                temp _c  (Vint (nthi regs' 2));
                temp _d  (Vint (nthi regs' 3));
                temp _e  (Vint (nthi regs' 4));
                temp _f  (Vint (nthi regs' 5));
                temp _g  (Vint (nthi regs' 6));
                temp _h  (Vint (nthi regs' 7));
                var  _K256 (tarray tuint CBLOCKz) kv)
   SEP 
   (`(field_at Tsh t_struct_SHA256state_st  [StructField _h] (map Vint regs) ctx)))
   (sequence add_them_back Sskip)
  (normal_ret_assert
   (PROP() LOCAL(temp _ctx ctx; var _K256 (tarray tuint CBLOCKz) kv)
    SEP (`(field_at Tsh t_struct_SHA256state_st  [StructField _h]
                (map Vint (map2 Int.add regs regs')) ctx)))).
Proof.
intros.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name t_ _t.
name ctx_ _ctx.
rename regs' into atoh.

assert (forall j : nat,
   (j < 8)%nat ->
   (temp_types Delta_loop1)
    ! (nth j [_a; _b; _c; _d; _e; _f; _g; _h] 1%positive) = Some (tuint, true)).
 intros; destruct j as [ | [ | [ | [ | [ | [ | [ | [ | ]]]]]]]]; try reflexivity; omega.

assert (forall j : nat,
   (j < 8)%nat ->
   (temp_types (initialized _t Delta_loop1))
    ! (nth j [_a; _b; _c; _d; _e; _f; _g; _h] 1%positive) = Some (tuint, true)).
 intros; destruct j as [ | [ | [ | [ | [ | [ | [ | [ | ]]]]]]]]; try reflexivity; omega.

unfold sequence, add_them_back.
change regs with  (add_upto 0 regs atoh) at 1.
do 8 (simple apply add_one_back; auto; try (clear; omega)).

forward.
apply (drop_LOCAL' 0); unfold delete_nth.
do 8 (apply (drop_LOCAL' 1); unfold delete_nth).
replace (add_upto 8 regs atoh) with  (map2 Int.add regs atoh).
auto.
unfold registers in *.
destruct atoh as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; inv H0.
destruct regs as [ | a' [ | b' [ | c' [ | d' [ | e' [ | f' [ | g' [ | h' [ | ]]]]]]]]]; inv H.
reflexivity.
Qed.



