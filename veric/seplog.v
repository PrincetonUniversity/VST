Require Import msl.log_normalize.
Require Import msl.alg_seplog.
Require Export veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.slice.
Require Import veric.res_predicates.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.binop_lemmas2.
Require Import veric.address_conflict.
Require Export veric.shares.

Definition assert := environ -> mpred.  (* Unfortunately
   can't export this abbreviation through SeparationLogic.v because
  it confuses the Lift system *)

Lemma address_mapsto_exists:
  forall ch v rsh (sh: pshare) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot),
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) rsh (pshare_sh sh) loc w 
                    /\ core w = core w0.
Proof.  exact address_mapsto_exists. Qed.

Open Local Scope pred.

Definition func_at (f: funspec): address -> pred rmap :=
  match f with
   | mk_funspec fsig A P Q => pureat (SomeP (A::boolT::environ::nil) (packPQ P Q)) (FUN fsig)
  end.

Definition func_at' (f: funspec) (loc: address) : pred rmap :=
  match f with
   | mk_funspec fsig _ _ _ => EX pp:_, pureat pp (FUN fsig) loc
  end.

(* Definition assert: Type := environ -> pred rmap. *)

Bind Scope pred with assert.
Local Open Scope pred.

Definition closed_wrt_vars {B} (S: ident -> Prop) (F: environ -> B) : Prop := 
  forall rho te',  
     (forall i, S i \/ Map.get (te_of rho) i = Map.get te' i) ->
     F rho = F (mkEnviron (ge_of rho) (ve_of rho) te').

Definition closed_wrt_lvars {B} (S: ident -> Prop) (F: environ -> B) : Prop := 
  forall rho ve',  
     (forall i, S i \/ Map.get (ve_of rho) i = Map.get ve' i) ->
     F rho = F (mkEnviron (ge_of rho) ve' (te_of rho)).

Definition not_a_param (params: list (ident * type)) (i : ident) : Prop :=
  ~ In i (map (@fst _ _) params).

Definition is_a_local (vars: list (ident * type)) (i: ident) : Prop :=
  In  i (map (@fst _ _) vars) .

Definition precondition_closed (f: function) {A: Type} (P: A -> assert) : Prop :=
 forall x: A,
  closed_wrt_vars (not_a_param (fn_params f)) (P x) /\ 
  closed_wrt_lvars (is_a_local (fn_vars f)) (P x).

(*Definition expr_true (e: Clight.expr) (rho: environ): Prop := 
  bool_val (eval_expr e rho) (Clight.typeof e) = Some true.*)

Definition typed_true (t: type) (v: val)  : Prop := strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t =
Some false.

Definition expr_true {CS: compspecs} e := lift1 (typed_true (typeof e)) (eval_expr e).

Definition expr_false {CS: compspecs} e := lift1 (typed_false (typeof e)) (eval_expr e).

Definition subst {A} (x: ident) (v: val) (P: environ -> A) : environ -> A :=
   fun s => P (env_set s x v).

Definition permission_block (sh: Share.t)  (v: val) (t: type) : mpred :=
    match access_mode t with
         | By_value ch => 
            match v with 
            | Vptr b ofs => 
                 nonlock_permission_bytes sh (b, Int.unsigned ofs)
                       (size_chunk ch)
            | _ => FF
            end
         | _ => FF
         end.

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch => 
   match type_is_volatile t with
   | false =>
    match v1 with
     | Vptr b ofs => 
       if readable_share_dec sh
       then (!!tc_val t v2 &&
             address_mapsto ch v2
              (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs)) ||
            (!! (v2 = Vundef) &&
             EX v2':val, address_mapsto ch v2'
              (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs))
       else nonlock_permission_bytes sh (b, Int.unsigned ofs) (size_chunk ch)
     | _ => FF
    end
    | _ => FF
    end
  | _ => FF
  end. 

Definition mapsto_ sh t v1 := mapsto sh t v1 Vundef.

Definition int_range (sz: intsize) (sgn: signedness) (i: int) :=
 match sz, sgn with
 | I8, Signed => -128 <= Int.signed i < 128
 | I8, Unsigned => 0 <= Int.unsigned i < 256
 | I16, Signed => -32768 <= Int.signed i < 32768
 | I16, Unsigned => 0 <= Int.unsigned i < 65536
 | I32, Signed => -2147483648 <= Int.signed i < 2147483648
 | I32, Unsigned => 0 <= Int.unsigned i < 4294967296
 | IBool, _ => 0 <= Int.unsigned i < 256
end.

Lemma mapsto_value_range:
 forall sh v sz sgn i, 
   readable_share sh ->
   mapsto sh (Tint sz sgn noattr) v (Vint i) =
    !! int_range sz sgn i && mapsto sh (Tint sz sgn noattr) v (Vint i).
Proof.
intros.
rename H into Hsh.
assert (GG: forall a b, (a || !!(Vint i = Vundef) && b) = a). {
intros. apply pred_ext; intros ? ?. hnf in H.
destruct H; auto; hnf in H; destruct H; discriminate.
left; auto.
}
apply pred_ext; [ | apply andp_left2; auto].
assert (MAX: Int.max_signed = 2147483648 - 1) by reflexivity.
assert (MIN: Int.min_signed = -2147483648) by reflexivity.
assert (Byte.min_signed = -128) by reflexivity.
assert (Byte.max_signed = 128-1) by reflexivity.
assert (Byte.max_unsigned = 256-1) by reflexivity.
destruct (Int.unsigned_range i).
assert (Int.modulus = Int.max_unsigned + 1) by reflexivity.
assert (Int.modulus = 4294967296) by reflexivity.
apply andp_right; auto.
unfold mapsto; intros.
replace (type_is_volatile (Tint sz sgn noattr)) with false
  by (destruct sz,sgn; reflexivity).
simpl.
destruct (readable_share_dec sh); [| tauto].
destruct sz, sgn, v; (try rewrite FF_and; auto);
 repeat rewrite GG;
 apply prop_andp_left; intros ? ? _; hnf; try omega.
 destruct H6; split; try assumption; omega.
 pose proof (Int.signed_range i); omega.
 destruct H6; subst; 
  try rewrite Int.unsigned_zero; try rewrite Int.unsigned_one; omega.
 destruct H6; subst; 
  try rewrite Int.unsigned_zero; try rewrite Int.unsigned_one; omega.
Qed.

Definition writable_block (id: ident) (n: Z): assert :=
   fun rho => 
        EX b: block,  EX rsh: Share.t,
          !! (ge_of rho id = Some b) && VALspec_range n rsh Share.top (b, 0).

Fixpoint writable_blocks (bl : list (ident*Z)) : assert :=
 match bl with
  | nil =>  fun rho => emp 
  | (b,n)::bl' =>  fun rho => writable_block b n rho * writable_blocks bl' rho
 end.

Fixpoint address_mapsto_zeros (sh: share) (n: nat) (adr: address) : mpred :=
 match n with
 | O => emp
 | S n' => address_mapsto Mint8unsigned (Vint Int.zero)
                (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) adr 
               * address_mapsto_zeros sh n' (fst adr, Zsucc (snd adr))
end.

Definition address_mapsto_zeros' (n: Z) : spec :=
     fun (rsh sh: Share.t) (l: address) =>
          allp (jam (adr_range_dec l (Zmax n 0))
                                  (fun l' => yesat NoneP (VAL (Byte Byte.zero)) rsh sh l')
                                  noat).

Lemma Z_of_nat_ge_O: forall n, Z.of_nat n >= 0.
Proof. intros. 
change 0 with (Z.of_nat O).
apply inj_ge. clear; omega.
Qed.

Lemma rev_if_be_singleton:
  forall x, rev_if_be (x::nil) = (x::nil).
Proof. intro. unfold rev_if_be; destruct Archi.big_endian; auto. Qed.

Lemma resource_fmap_core:
  forall w loc, resource_fmap (approx (level w)) (core (w @ loc)) = core (w @ loc).
Proof.
intros.
case_eq (w @ loc); intros;
 [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; auto.
rewrite <- H. apply resource_at_approx.
Qed.

Lemma decode_byte_val:
  forall m, decode_val Mint8unsigned (Byte m :: nil) =
              Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned m))).
Proof.
intros.
unfold decode_val. simpl.
f_equal.
unfold decode_int.
rewrite rev_if_be_singleton.
unfold int_of_bytes. f_equal. f_equal. apply Z.add_0_r.
Qed.

Lemma address_mapsto_zeros_eq:
  forall sh n,
   address_mapsto_zeros sh n =
   address_mapsto_zeros' (Z_of_nat n) 
            (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh).
Proof.
induction n;
extensionality adr; destruct adr as [b i].
* (* base case *)
simpl.
unfold address_mapsto_zeros'.
apply pred_ext.
intros w ?.
intros [b' i'].
hnf.
rewrite if_false.
simpl. apply resource_at_identity; auto.
intros [? ?]. unfold Zmax in H1;  simpl in H1. omega.
intros w ?.
simpl.
apply all_resource_at_identity.
intros [b' i'].
specialize (H (b',i')).
hnf in H.
rewrite if_false in H. apply H.
clear; intros [? ?]. unfold Zmax in H0; simpl in H0. omega.
* (* inductive case *)
rewrite inj_S.
simpl.
rewrite IHn; clear IHn.
apply pred_ext; intros w ?.
 - (* forward case *)
destruct H as [w1 [w2 [? [? ?]]]].
intros [b' i'].
hnf.
if_tac.
destruct H0 as [bl [[? [? ?]] ?]].
specialize (H5 (b',i')).
hnf in H5.
if_tac in H5.
destruct H5 as [p ?]; exists p.
hnf in H5.
specialize (H1 (b',i')). hnf in H1. rewrite if_false in H1.
assert (LEV := join_level _ _ _ H).
apply (resource_at_join _ _ _ (b',i')) in H.
apply join_comm in H; apply H1 in H.
rewrite H in H5.
hnf. rewrite H5. f_equal. f_equal.
simpl. destruct H6. simpl in H7. replace (i'-i) with 0 by omega.
unfold size_chunk_nat in H0. simpl in H0. 
unfold nat_of_P in H0. simpl in H0.
destruct bl; try solve [inv H0].
destruct bl; inv H0.
simpl.
clear - H3.
 {
destruct m; try solve [inv H3].
rewrite decode_byte_val in H3.
f_equal.
assert (Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.repr 0).
forget (Int.zero_ext 8 (Int.repr (Byte.unsigned i))) as j; inv H3; auto.
clear H3.
assert (Int.unsigned (Int.zero_ext 8 (Int.repr (Byte.unsigned i))) =
    Int.unsigned Int.zero).
f_equal; auto. rewrite Int.unsigned_zero in H0.
clear H.
rewrite Int.zero_ext_mod in H0 by (compute; split; congruence).
rewrite Int.unsigned_repr in H0.
rewrite Zdiv.Zmod_small in H0.
assert (Byte.repr (Byte.unsigned i) = Byte.zero).
apply f_equal; auto.
rewrite Byte.repr_unsigned in H. auto.
apply Byte.unsigned_range.
clear.
pose proof (Byte.unsigned_range i).
destruct H; split; auto.
apply Z.le_trans with Byte.modulus.
omega.
clear.
compute; congruence.
}
f_equal. f_equal.
destruct LEV; auto.
destruct H2.
intros [? ?].
destruct H6.
clear - H7 H9 H10. simpl in H10. omega.
assert (LEV := join_level _ _ _ H).
apply (resource_at_join _ _ _ (b',i')) in H.
apply H5 in H.
specialize (H1 (b',i')).
hnf in H1.
if_tac in H1.
destruct H1 as [p ?]; exists p.
hnf in H1|-*.
rewrite H in H1; rewrite H1.
f_equal. f_equal. f_equal. destruct LEV; auto.
contradiction H6.
destruct H2.
split; auto.
simpl.
subst b'.
clear - H7 H8.
assert (~ (Zsucc i <= i' < (Zsucc i + Zmax (Z_of_nat n) 0))).
contradict H7; split; auto.
clear H7.
replace (Zmax (Zsucc (Z_of_nat n)) 0) with (Zsucc (Z_of_nat n)) in H8.
replace (Zmax (Z_of_nat n) 0) with (Z_of_nat n) in H.
omega.
symmetry; apply Zmax_left.
apply Z_of_nat_ge_O.
symmetry; apply Zmax_left.
clear.
pose proof (Z_of_nat_ge_O n). omega.
apply (resource_at_join _ _ _ (b',i')) in H.
destruct H0 as [bl [[? [? ?]] ?]].
specialize (H5 (b',i')); specialize (H1 (b',i')).
hnf in H1,H5.
rewrite if_false in H5.
rewrite if_false in H1.
apply H5 in H.
simpl in H1|-*.
rewrite <- H; auto.
clear - H2; contradict H2.
destruct H2; split; auto.
destruct H0.
split; try omega.
pose proof (Z_of_nat_ge_O n). 
rewrite Zmax_left in H1 by omega.
rewrite Zmax_left by omega.
omega.
clear - H2; contradict H2; simpl in H2.
destruct H2; split; auto.
rewrite Zmax_left by omega.
omega.

- (* backward direction *)
forget (Share.unrel Share.Lsh sh) as rsh.
forget (Share.unrel Share.Rsh sh) as sh'. clear sh; rename sh' into sh.
assert (H0 := H (b,i)).
hnf in H0.
rewrite if_true in H0
  by (split; auto; pose proof (Z_of_nat_ge_O n); rewrite Zmax_left; omega).
destruct H0 as [H0 H1].
assert (AV.valid (res_option oo (fun loc => if eq_dec loc (b,i) then 
 YES rsh (mk_pshare _ H0) (VAL (Byte Byte.zero)) NoneP 
    else core (w @ loc)))).
 {intros b' z'; unfold res_option, compose; if_tac; simpl; auto.
  destruct (w @ (b',z')); [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; auto.  
 }
destruct (make_rmap _ H2 (level w)) as [w1 [? ?]].
extensionality loc. unfold compose.
if_tac; [unfold resource_fmap; f_equal; apply preds_fmap_NoneP 
           | apply resource_fmap_core].
assert (AV.valid (res_option oo 
  fun loc => if adr_range_dec (b, Zsucc i) (Z.max (Z.of_nat n) 0) loc
                     then YES rsh (mk_pshare _ H0) (VAL (Byte Byte.zero)) NoneP 
    else core (w @ loc))).
 {intros b' z'; unfold res_option, compose; if_tac; simpl; auto. 
  case_eq (w @ (b',z')); intros;
   [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; auto.
 }
destruct (make_rmap _ H5 (level w)) as [w2 [? ?]].
extensionality loc. unfold compose.
if_tac; [unfold resource_fmap; f_equal; apply preds_fmap_NoneP 
           | apply resource_fmap_core].
exists w1; exists w2; split3; auto.
+apply resource_at_join2; try congruence.
  intro loc; rewrite H4; rewrite H7.
 clear - H.
 specialize (H loc).  unfold jam in H. hnf in H.
 rewrite Zmax_left by (pose proof (Z_of_nat_ge_O n); omega).
 rewrite Zmax_left in H by (pose proof (Z_of_nat_ge_O n); omega).
 if_tac. rewrite if_false.
 subst. rewrite if_true in H.
  destruct H as [H' H]; rewrite H. rewrite core_YES.
 rewrite preds_fmap_NoneP.
 apply join_unit2.
 constructor. auto.
 repeat f_equal.
 apply mk_lifted_refl1.
 split; auto; omega.
 subst. intros [? ?]; omega.
 if_tac in H.
 rewrite if_true.
 destruct H as [H' H]; rewrite H; clear H. rewrite core_YES.
 rewrite preds_fmap_NoneP.
 apply join_unit1.
 constructor; auto.
 f_equal.
 apply mk_lifted_refl1.
 destruct loc;
 destruct H2; split; auto.
 assert (z<>i) by congruence.
 omega.
 rewrite if_false.
 unfold noat in H. simpl in H.
 apply join_unit1; [apply core_unit | ].
 clear - H.
 apply H. apply join_unit2. apply core_unit. auto.
 destruct loc. intros [? ?]; subst. apply H2; split; auto; omega.
+ exists (Byte Byte.zero :: nil); split.
 split. reflexivity. split.
 unfold decode_val. simpl. f_equal.
 apply Z.divide_1_l.
 intro loc. hnf. if_tac. exists H0.
 destruct loc as [b' i']. destruct H8; subst b'.
 simpl in H9. assert (i=i') by omega; subst i'.
 rewrite Zminus_diag. hnf. rewrite preds_fmap_NoneP.
  rewrite H4. rewrite if_true by auto. f_equal.
 unfold noat. simpl. rewrite H4. rewrite if_false. apply core_identity.
  contradict H8. subst. split; auto. simpl; omega.
+ intro loc. hnf. 
 if_tac. exists H0. hnf. rewrite H7.
 rewrite if_true by auto. rewrite preds_fmap_NoneP. auto.
 unfold noat. simpl. rewrite H7.
 rewrite if_false by auto. apply core_identity.
Qed.

Definition mapsto_zeros (n: Z) (sh: share) (a: val) : mpred :=
 match a with
  | Vptr b z => address_mapsto_zeros sh (nat_of_Z n)
                          (b, Int.unsigned z)
  | _ => TT
  end.

Definition fun_assert: 
  forall (fml: funsig) (A: Type) (P Q: A -> environ -> pred rmap)  (v: val) , pred rmap :=
  res_predicates.fun_assert.

Fixpoint memory_block' (sh: share) (n: nat) (b: block) (i: Z) : mpred :=
  match n with
  | O => emp
  | S n' => mapsto_ sh (Tint I8 Unsigned noattr) (Vptr b (Int.repr i))
         * memory_block' sh n' b (i+1)
 end.

Definition memory_block'_alt (sh: share) (n: nat) (b: block) (ofs: Z) : mpred :=
 if readable_share_dec sh 
 then VALspec_range (Z_of_nat n)
               (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, ofs)
 else nonlock_permission_bytes sh (b,ofs) (Z.of_nat n).

Lemma memory_block'_eq: 
 forall sh n b i,
  0 <= i ->
  Z_of_nat n + i <= Int.modulus ->
  memory_block' sh n b i = memory_block'_alt sh n b i.
Proof.
  intros.
  unfold memory_block'_alt.
  revert i H H0; induction n; intros.
  + unfold memory_block'.
    simpl.
    rewrite VALspec_range_0, nonlock_permission_bytes_0.
    if_tac; auto.
  + unfold memory_block'; fold memory_block'.
    rewrite (IHn (i+1)) by (rewrite inj_S in H0; omega).
    symmetry.
    rewrite (VALspec_range_split2 1 (Z_of_nat n)) by (try rewrite inj_S; omega).
    rewrite VALspec1.
    unfold mapsto_, mapsto.
    simpl access_mode. cbv beta iota.
    change (type_is_volatile (Tint I8 Unsigned noattr)) with false. cbv beta iota.
    destruct (readable_share_dec sh).
    - f_equal.
      assert (i < Int.modulus) by (rewrite Nat2Z.inj_succ in H0; omega).
      rewrite Int.unsigned_repr by (unfold Int.max_unsigned; omega); clear H1.
      forget (Share.unrel Share.Lsh sh) as rsh.
      forget (Share.unrel Share.Rsh sh) as sh'.
      clear.

      assert (EQ: forall loc, jam (adr_range_dec loc (size_chunk Mint8unsigned)) = jam (eq_dec loc)).
      intros [b' z']; unfold jam; extensionality P Q loc;
       destruct loc as [b'' z'']; apply exist_ext; extensionality w;
       if_tac; [rewrite if_true | rewrite if_false]; auto;
        [destruct H; subst; f_equal;  simpl in H0; omega 
        | contradict H; inv H; split; simpl; auto; omega].
      apply pred_ext.
      * intros w ?.
        right; split; hnf; auto.
        assert (H':= H (b,i)).
        hnf in H'. rewrite if_true in H' by auto.
        destruct H' as [v H'].
        pose (l := v::nil).
        destruct v; [exists Vundef | exists (Vint (Int.zero_ext 8 (Int.repr (Byte.unsigned i0)))) | exists Vundef];
        exists l; (split; [ split3; [reflexivity |unfold l; (reflexivity || apply decode_byte_val) |  apply Z.divide_1_l ] | ]);
          rewrite EQ; intro loc; specialize (H loc);
         hnf in H|-*; if_tac; auto; subst loc; rewrite Zminus_diag;
         unfold l; simpl nth; auto.
      * apply orp_left.
        apply andp_left2.
        Focus 1. {
          intros w [l [[? [? ?]] ?]].
           intros [b' i']; specialize (H2 (b',i')); rewrite EQ in H2;
           hnf in H2|-*;  if_tac; auto. symmetry in H3; inv H3.
           destruct l; inv H. exists m.
           destruct H2 as [H2' H2]; exists H2'; hnf in H2|-*; rewrite H2.
           f_equal. f_equal. rewrite Zminus_diag. reflexivity.
        } Unfocus.
        Focus 1. {
          rewrite prop_true_andp by auto.
          intros w [v2' [l [[? [? ?]] ?]]].
           intros [b' i']; specialize (H2 (b',i')); rewrite EQ in H2;
           hnf in H2|-*;  if_tac; auto. symmetry in H3; inv H3.
           destruct l; inv H. exists m.
           destruct H2 as [H2' H2]; exists H2'; hnf in H2|-*; rewrite H2.
           f_equal. f_equal. rewrite Zminus_diag. reflexivity.
        } Unfocus.
    - rewrite Int.unsigned_repr by (rewrite Nat2Z.inj_succ in H0; unfold Int.max_unsigned; omega).
      change (size_chunk Mint8unsigned) with 1.
      apply nonlock_permission_bytes_split2.
      * rewrite Nat2Z.inj_succ; omega.
      * omega.
      * omega.
Qed.

Definition memory_block (sh: share) (n: Z) (v: val) : mpred :=
 match v with 
 | Vptr b ofs => (!!(Int.unsigned ofs + n <= Int.modulus)) && memory_block' sh (nat_of_Z n) b (Int.unsigned ofs)
 | _ => FF
 end.

Lemma mapsto__exp_address_mapsto: forall sh t b i_ofs ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  readable_share sh ->
  mapsto_ sh t (Vptr b i_ofs) = EX  v2' : val,
            address_mapsto ch v2' (Share.unrel Share.Lsh sh)
              (Share.unrel Share.Rsh sh) (b, (Int.unsigned i_ofs)).
Proof.
  pose proof (@FF_orp (pred rmap) (algNatDed _)) as HH0.
  change seplog.orp with orp in HH0.
  change seplog.FF with FF in HH0.
  pose proof (@ND_prop_ext (pred rmap) (algNatDed _)) as HH1.
  change seplog.prop with prop in HH1.

  intros. rename H1 into RS.
  unfold mapsto_, mapsto.
  rewrite H, H0.
  rewrite if_true by auto.
  assert (!!(tc_val t Vundef) = FF)
    by (destruct t as [ | | | [ | ] |  | | | | ]; reflexivity).
  rewrite H1.
  
  rewrite FF_and, HH0.
  assert (!!(Vundef = Vundef) = TT) by (apply HH1; tauto).
  rewrite H2.
  rewrite TT_and.
  reflexivity.
Qed.

Lemma exp_address_mapsto_VALspec_range_eq:
  forall ch rsh sh l,
    EX v: val, address_mapsto ch v rsh sh l = !! (align_chunk ch | snd l) && VALspec_range (size_chunk ch) rsh sh l.
Proof.
  intros.
  apply pred_ext.
  + apply exp_left; intro.
    apply andp_right; [| apply address_mapsto_VALspec_range].
    unfold address_mapsto.
    apply exp_left; intro.
    apply andp_left1.
    apply (@prop_derives (pred rmap) (algNatDed _)); tauto.
  + apply prop_andp_left; intro.
    apply VALspec_range_exp_address_mapsto; auto.
Qed.

Lemma VALspec_range_exp_address_mapsto_eq:
  forall ch rsh sh l,
    (align_chunk ch | snd l) ->
    VALspec_range (size_chunk ch) rsh sh l = EX v: val, address_mapsto ch v rsh sh l.
Proof.
  intros.
  apply pred_ext.
  + apply VALspec_range_exp_address_mapsto; auto.
  + apply exp_left; intro; apply address_mapsto_VALspec_range.
Qed.

Lemma mapsto__memory_block: forall sh b ofs t ch, 
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Int.unsigned ofs) ->
  Int.unsigned ofs + size_chunk ch <= Int.modulus ->
  mapsto_ sh t (Vptr b ofs) = memory_block sh (size_chunk ch) (Vptr b ofs).
Proof.
  intros.
  unfold memory_block.
  rewrite memory_block'_eq.
  2: pose proof Int.unsigned_range ofs; omega.
  2: rewrite Coqlib.nat_of_Z_eq by (pose proof size_chunk_pos ch; omega); omega.
  destruct (readable_share_dec sh).
 *
  rewrite mapsto__exp_address_mapsto with (ch := ch); auto.
  unfold memory_block'_alt. rewrite if_true by auto.
  rewrite Coqlib.nat_of_Z_eq by (pose proof size_chunk_pos ch; omega).
  rewrite VALspec_range_exp_address_mapsto_eq by (exact H1).
  rewrite <- (TT_and (EX  v2' : val,
   address_mapsto ch v2' (Share.unrel Share.Lsh sh)
     (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs))) at 1.
  f_equal.
  pose proof (@ND_prop_ext (pred rmap) _).
  simpl in H3.
  change TT with (!! True).
  apply H3.
  tauto.
 * unfold mapsto_, mapsto, memory_block'_alt.
   rewrite prop_true_andp by auto.
   rewrite H, H0.
  rewrite !if_false by auto.
   rewrite Z2Nat.id by (pose proof (size_chunk_pos ch); omega).
   auto.
Qed.

Lemma tc_val_Vundef:
  forall t, ~tc_val t Vundef.
Proof.
intros.
intro. hnf in H.
destruct t; try contradiction.
destruct f; try contradiction.
Qed.

Lemma mapsto_share_join:
 forall sh1 sh2 sh t p v,
   join sh1 sh2 sh ->
   mapsto sh1 t p v * mapsto sh2 t p v = mapsto sh t p v.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t) eqn:?; try solve [rewrite FF_sepcon; auto].
  destruct (type_is_volatile t) eqn:?; try solve [rewrite FF_sepcon; auto].
  destruct p; try solve [rewrite FF_sepcon; auto].
  destruct (readable_share_dec sh1), (readable_share_dec sh2).
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eauto | auto]).
    pose proof (@guarded_sepcon_orp_distr (pred rmap) (algNatDed _) (algSepLog _)).
    simpl in H0; rewrite H0 by (intros; subst; pose proof tc_val_Vundef t; tauto); clear H0.
    f_equal; f_equal.
    - apply address_mapsto_share_join.
      1: apply join_unrel; auto.
      1: apply join_unrel; auto.
    - rewrite exp_sepcon1.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H0; apply H0; clear H0; intro.
      rewrite exp_sepcon2.
      transitivity
       (address_mapsto m v0 (Share.unrel Share.Lsh sh1) (Share.unrel Share.Rsh sh1) (b, Int.unsigned i) *
        address_mapsto m v0 (Share.unrel Share.Lsh sh2) (Share.unrel Share.Rsh sh2) (b, Int.unsigned i)).
      * apply pred_ext; [| apply (exp_right v0); auto].
        apply exp_left; intro.
        pose proof (fun rsh1 sh0 rsh2 sh3 a => (@add_andp (pred rmap) (algNatDed _) _ _ (address_mapsto_value_cohere m v0 x rsh1 sh0 rsh2 sh3 a))).
        simpl in H0; rewrite H0; clear H0.
        apply normalize.derives_extract_prop'; intro; subst; auto.
      * apply address_mapsto_share_join.
        1: apply join_unrel; auto.
        1: apply join_unrel; auto.
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eauto | auto]).
    rewrite distrib_orp_sepcon.
    f_equal; rewrite sepcon_comm, sepcon_andp_prop; f_equal.
    - apply nonlock_permission_bytes_address_mapsto_join; auto.
    - rewrite exp_sepcon2.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H0; apply H0; clear H0; intro.
      apply nonlock_permission_bytes_address_mapsto_join; auto.
  + rewrite if_true by (eapply join_sub_readable; [unfold join_sub; eexists; apply join_comm in H; eauto | auto]).
    rewrite sepcon_comm, distrib_orp_sepcon.
    f_equal; rewrite sepcon_comm, sepcon_andp_prop; f_equal.
    - apply nonlock_permission_bytes_address_mapsto_join; auto.
    - rewrite exp_sepcon2.
      pose proof (@exp_congr (pred rmap) (algNatDed _) val); simpl in H0; apply H0; clear H0; intro.
      apply nonlock_permission_bytes_address_mapsto_join; auto.
  + rewrite if_false by (eapply join_unreadable_shares; eauto).
    apply nonlock_permission_bytes_share_join; auto.
Qed.

Lemma mapsto_mapsto_: forall sh t v v', mapsto sh t v v' |-- mapsto_ sh t v.
Proof. unfold mapsto_; intros.
  unfold mapsto.
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); auto.
  destruct v; auto.
  if_tac; [| auto].
  apply orp_left.
  apply orp_right2.
  apply andp_left2.
  apply andp_right.
  + intros ? _; simpl; auto.
  + apply exp_right with v'; auto.
  + apply andp_left2. apply exp_left; intro v2'.
  apply orp_right2. apply andp_right; [intros ? _; simpl; auto |]. apply exp_right with v2'.
  auto.
Qed.

Lemma mapsto_not_nonunit: forall sh t p v, ~ nonunit sh -> mapsto sh t p v |-- emp.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try solve [apply FF_derives].
  destruct (type_is_volatile t); try solve [apply FF_derives].
  destruct p; try solve [apply FF_derives].
  if_tac.
  + apply readable_nonidentity in H0.
    apply nonidentity_nonunit in H0; tauto.
  + apply nonlock_permission_bytes_not_nonunit; auto.
Qed.

Lemma mapsto_pure_facts: forall sh t p v,
  mapsto sh t p v |-- !! ((exists ch, access_mode t = By_value ch) /\ isptr p).
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try solve [apply FF_derives].
  destruct (type_is_volatile t); try solve [apply FF_derives].
  destruct p; try solve [apply FF_derives].

  pose proof (@seplog.prop_right (pred rmap) (algNatDed _)).
  simpl in H; apply H; clear H.
  split.
  + eauto.
  + simpl; auto.
Qed.

Lemma mapsto_overlap: forall sh env t1 t2 p1 p2 v1 v2,
  nonunit sh ->
  pointer_range_overlap p1 (sizeof env t1) p2 (sizeof env t2) ->
  mapsto sh t1 p1 v1 * mapsto sh t2 p2 v2 |-- FF.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t1) eqn:AM1; try (rewrite FF_sepcon; auto).
  destruct (access_mode t2) eqn:AM2; try (rewrite normalize.sepcon_FF; auto).
  destruct (type_is_volatile t1); try (rewrite FF_sepcon; auto).
  destruct (type_is_volatile t2); try (rewrite normalize.sepcon_FF; auto).
  destruct p1; try (rewrite FF_sepcon; auto).
  destruct p2; try (rewrite normalize.sepcon_FF; auto).
  if_tac.
  + apply derives_trans with ((EX  v : val,
          address_mapsto m v (Share.unrel Share.Lsh sh)
            (Share.unrel Share.Rsh sh) (b, Int.unsigned i)) *
      (EX  v : val,
          address_mapsto m0 v (Share.unrel Share.Lsh sh)
            (Share.unrel Share.Rsh sh) (b0, Int.unsigned i0))).
    - apply sepcon_derives; apply orp_left.
      * apply andp_left2, (exp_right v1).
        auto.
      * apply andp_left2; auto.
      * apply andp_left2, (exp_right v2).
        auto.
      * apply andp_left2; auto.
    - clear v1 v2.
      rewrite exp_sepcon1.
      apply exp_left; intro v1.
      rewrite exp_sepcon2.
      apply exp_left; intro v2.
      clear H H1; rename H0 into H.
      destruct H as [? [? [? [? ?]]]].
      inversion H; subst.
      inversion H0; subst.
      erewrite !size_chunk_sizeof in H1 by eauto.
      apply address_mapsto_overlap; auto.
  + apply nonlock_permission_bytes_overlap; auto.
    clear H H1; rename H0 into H.
    erewrite !size_chunk_sizeof in H by eauto.
    destruct H as [? [? [? [? ?]]]].
    inversion H; subst.
    inversion H0; subst.
    auto.
Qed.

Lemma memory_block_overlap: forall sh p1 n1 p2 n2, nonunit sh -> pointer_range_overlap p1 n1 p2 n2 -> memory_block sh n1 p1 * memory_block sh n2 p2 |-- FF.
Proof.
  intros.
  unfold memory_block.
  destruct p1; try solve [rewrite FF_sepcon; auto].
  destruct p2; try solve [rewrite normalize.sepcon_FF; auto].
  rewrite sepcon_andp_prop1.
  rewrite sepcon_andp_prop2.
  apply normalize.derives_extract_prop; intros.
  apply normalize.derives_extract_prop; intros.
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i; omega | apply Clight_lemmas.Nat2Z_add_le; auto].
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i0; omega | apply Clight_lemmas.Nat2Z_add_le; auto].
  unfold memory_block'_alt.
  if_tac.
  + clear H2.
    apply VALspec_range_overlap.
    pose proof pointer_range_overlap_non_zero _ _ _ _ H0.
    rewrite !Coqlib.nat_of_Z_eq by omega.
    destruct H0 as [[? ?] [[? ?] [? [? ?]]]].
    inversion H0; inversion H4.
    subst.
    auto.
  + apply nonlock_permission_bytes_overlap; auto.
    pose proof pointer_range_overlap_non_zero _ _ _ _ H0.
    rewrite !Coqlib.nat_of_Z_eq by omega.
    destruct H0 as [[? ?] [[? ?] [? [? ?]]]].
    inversion H0; inversion H5.
    subst.
    auto.
Qed.

Lemma mapsto_conflict:
  forall sh t v v2 v3,
  nonunit sh ->
  mapsto sh t v v2 * mapsto sh t v v3 |-- FF.
Proof.
  intros.
  rewrite (@add_andp (pred rmap) (algNatDed _) _ _ (mapsto_pure_facts sh t v v3)).
  simpl.
  rewrite andp_comm.
  rewrite sepcon_andp_prop.
  apply prop_andp_left; intros [[? ?] ?].
  apply mapsto_overlap with (env := PTree.empty _); auto.
  apply pointer_range_overlap_refl; auto.
  + erewrite size_chunk_sizeof by eauto.
    apply size_chunk_pos.
  + erewrite size_chunk_sizeof by eauto.
    apply size_chunk_pos.
Qed.

Lemma memory_block_conflict: forall sh n m p,
  nonunit sh ->
  0 < n <= Int.max_unsigned -> 0 < m <= Int.max_unsigned ->
  memory_block sh n p * memory_block sh m p |-- FF.
Proof.
  intros.
  unfold memory_block.
  destruct p; try solve [rewrite FF_sepcon; auto].
  rewrite sepcon_andp_prop1.
  apply prop_andp_left; intro.
  rewrite sepcon_comm.
  rewrite sepcon_andp_prop1.
  apply prop_andp_left; intro.
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i; omega | rewrite Z2Nat.id; omega].
  rewrite memory_block'_eq; [| pose proof Int.unsigned_range i; omega | rewrite Z2Nat.id; omega].
  unfold memory_block'_alt.
  if_tac.
  + apply VALspec_range_overlap.
    exists (b, Int.unsigned i).
    simpl; repeat split; auto; try omega;
    rewrite Z2Nat.id; omega.
  + apply nonlock_permission_bytes_overlap; auto.
    exists (b, Int.unsigned i).
    repeat split; auto; try rewrite Z2Nat.id; omega.
Qed.

Definition eval_lvar (id: ident) (ty: type) (rho: environ) :=
 match Map.get (ve_of rho) id with
| Some (b, ty') => if eqb_type ty ty' then Vptr b Int.zero else Vundef
| None => Vundef
end.

Definition var_block (sh: Share.t) {cs: compspecs} (idt: ident * type) (rho: environ): mpred :=
  !! (sizeof cenv_cs (snd idt) <= Int.max_unsigned) &&
  (memory_block sh (sizeof cenv_cs (snd idt))) (eval_lvar (fst idt) (snd idt) rho).

Fixpoint sepcon_list {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A} {AgeA: Age_alg A}
   (p: list (pred A)) : pred A :=
 match p with nil => emp | h::t => h * sepcon_list t end.

Definition stackframe_of {cs: compspecs} (f: Clight.function) : assert :=
  fold_right (fun P Q rho => P rho * Q rho) (fun rho => emp) (map (fun idt => var_block Share.top idt) (Clight.fn_vars f)).

Lemma stackframe_of_eq : forall {cs: compspecs}, stackframe_of = 
        fun f rho => fold_right sepcon emp (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).
Proof.
  intros.
 extensionality f rho.
 unfold stackframe_of.
 forget (fn_vars f) as vl.
 induction vl; simpl; auto.
 rewrite IHvl; auto.
Qed.

(*
Definition stackframe_of (f: Clight.function) : assert :=
  fun rho => sepcon_list (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).
*)

Lemma  subst_extens: 
 forall a v P Q, (forall rho, P rho |-- Q rho) -> forall rho, subst a v P rho |-- subst a v Q rho.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Definition tc_formals (formals: list (ident * type)) : environ -> Prop :=
     fun rho => typecheck_vals (map (fun xt => (eval_id (fst xt) rho)) formals) (map (@snd _ _) formals) = true.

Program Definition close_precondition (params vars: list (ident * type)) (P: environ -> pred rmap) (rho: environ) : pred rmap :=
 fun phi =>
   exists ve', exists te',
   (forall i, In i (map (@fst _ _) params) -> Map.get te' i = Map.get (te_of rho) i) /\
   (forall i, In i (map (@fst _ _) vars) \/ Map.get ve' i = Map.get (ve_of rho) i) /\
   app_pred (P (mkEnviron (ge_of rho) ve' te')) phi.
Next Obligation.
intros.
intro; intros.
destruct H0 as [ve' [te' [? [? ?]]]]; exists ve',te'; split3; auto.
eapply pred_hereditary; eauto.
Qed.

Lemma close_precondition_i:
  forall params vars P rho,
  P rho |-- close_precondition params vars P rho.
Proof.
intros.
intros ? ?.
hnf. exists (ve_of rho), (te_of rho).
split3; auto.
destruct rho; apply H.
Qed.

Lemma close_precondition_e:
   forall f A (P: A -> environ -> mpred),
    precondition_closed f P ->
  forall x rho,
   close_precondition (fn_params f) (fn_vars f) (P x) rho |-- P x rho.
Proof.
intros.
intros ? ?.
destruct H0 as [ve' [te' [? [? ?]]]].
destruct (H x).
rewrite (H3 _ te').
rewrite (H4 _ ve').
simpl.
apply H2.
intros.
simpl.
destruct (H1 i); auto.
intros.
unfold not_a_param.
destruct (In_dec ident_eq i (map (@fst _ _) (fn_params f))); auto.
right; symmetry; apply H0; auto.
Qed.

Definition bind_args (formals vars: list (ident * type)) (P: environ -> pred rmap) : assert :=
          fun rho => !! tc_formals formals rho && close_precondition formals vars P rho.

Definition globals_only (rho: environ) : environ := (mkEnviron (ge_of rho) (Map.empty _) (Map.empty _)).

Definition ret_temp : ident := 1%positive.

Fixpoint make_args (il: list ident) (vl: list val) (rho: environ)  :=
  match il, vl with 
  | nil, nil => globals_only rho
  | i::il', v::vl' => env_set (make_args il' vl' rho) i v
   | _ , _ => rho 
 end.

Definition get_result1 (ret: ident) (rho: environ) : environ :=
   make_args (ret_temp::nil) (eval_id ret rho :: nil) rho.

Definition get_result (ret: option ident) : environ -> environ :=
 match ret with 
 | None => make_args nil nil
 | Some x => get_result1 x
 end.

Definition bind_ret (vl: option val) (t: type) (Q: assert) : assert :=
     match vl, t with
     | None, Tvoid => fun rho => Q (make_args nil nil rho)
     | Some v, _ => fun rho => !! (tc_val t v) && 
                               Q (make_args (ret_temp::nil) (v::nil) rho)
     | _, _ => fun rho => FF
     end.

Definition funassert (Delta: tycontext): assert := 
 fun rho => 
   (ALL  id: ident, ALL fs:funspec,  !! ((glob_specs Delta)!id = Some fs) -->
              EX b:block, 
                   !! (ge_of rho id = Some b) && func_at fs (b,0))
   && 
   (ALL  b: block, ALL fs:funspec, func_at' fs (b,0) --> 
             EX id:ident, !! (ge_of rho id = Some b) 
               && !! exists fs, (glob_specs Delta)!id = Some fs).

(* Unfortunately, we need core_load in the interface as well as address_mapsto,
  because the converse of 'mapsto_core_load' lemma is not true.  The reason is
  that core_load could imply partial ownership of the four bytes of the word
  using different shares that don't have a common core, whereas address_mapsto
  requires the same share on all four bytes. *)

Definition ret_assert := exitkind -> option val -> assert.

Definition overridePost  (Q: assert)  (R: ret_assert) := 
     fun ek vl => if eq_dec ek EK_normal then (fun rho => !! (vl=None) && Q rho) else R ek vl.

Definition existential_ret_assert {A: Type} (R: A -> ret_assert) := 
  fun ek vl rho => EX x:A, R x ek vl rho.

Definition normal_ret_assert (Q: assert) : ret_assert := 
   fun ek vl rho => !!(ek = EK_normal) && (!! (vl = None) && Q rho).

Definition frame_ret_assert (R: ret_assert) (F: assert) : ret_assert := 
      fun ek vl rho => R ek vl rho * F rho.

Require Import msl.normalize.

Lemma normal_ret_assert_derives:
 forall P Q rho,
  P rho |-- Q rho ->
  forall ek vl, normal_ret_assert P ek vl rho |-- normal_ret_assert Q ek vl rho.
Proof.
 intros.
 unfold normal_ret_assert; intros; normalize.
Qed.
Hint Resolve normal_ret_assert_derives.

Lemma normal_ret_assert_FF:
  forall ek vl rho, normal_ret_assert (fun rho => FF) ek vl rho = FF.
Proof.
unfold normal_ret_assert. intros. normalize.
Qed.

Lemma frame_normal:
  forall P F, 
   frame_ret_assert (normal_ret_assert P) F = normal_ret_assert (fun rho => P rho * F rho).
Proof.
intros.
extensionality ek vl rho.
unfold frame_ret_assert, normal_ret_assert.
normalize.
Qed.

Definition loop1_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
 fun ek vl =>
 match ek with
 | EK_normal => Inv
 | EK_break => R EK_normal None
 | EK_continue => Inv
 | EK_return => R EK_return vl
 end.

Definition loop2_ret_assert (Inv: assert) (R: ret_assert) : ret_assert :=
 fun ek vl =>
 match ek with
 | EK_normal => Inv
 | EK_break => fun _ => FF
 | EK_continue => fun _ => FF 
 | EK_return => R EK_return vl
 end.

Lemma frame_for1:
  forall Q R F, 
   frame_ret_assert (loop1_ret_assert Q R) F = 
   loop1_ret_assert (fun rho => Q rho * F rho) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl rho.
unfold frame_ret_assert, loop1_ret_assert.
destruct ek; normalize.
Qed.

Lemma frame_loop1:
  forall Q R F, 
   frame_ret_assert (loop2_ret_assert Q R) F = 
   loop2_ret_assert (fun rho => Q rho * F rho) (frame_ret_assert R F).
Proof.
intros.
extensionality ek vl rho.
unfold frame_ret_assert, loop2_ret_assert.
destruct ek; normalize.
Qed.

Lemma overridePost_normal:
  forall P Q, overridePost P (normal_ret_assert Q) = normal_ret_assert P.
Proof.
intros; unfold overridePost, normal_ret_assert.
extensionality ek vl rho.
if_tac; normalize.
subst ek.
apply pred_ext; normalize.
apply pred_ext; normalize.
Qed.

Hint Rewrite normal_ret_assert_FF frame_normal frame_for1 frame_loop1 
                 overridePost_normal: normalize.

Definition function_body_ret_assert (ret: type) (Q: assert) : ret_assert := 
   fun (ek : exitkind) (vl : option val) =>
     match ek with
     | EK_return => bind_ret vl ret Q 
     | _ => fun rho => FF
     end.


Lemma same_glob_funassert:
  forall Delta1 Delta2,
     (forall id, (glob_specs Delta1) ! id = (glob_specs Delta2) ! id) ->
              funassert Delta1 = funassert Delta2.
Proof.
assert (forall Delta Delta' rho, 
             (forall id, (glob_specs Delta) ! id = (glob_specs Delta') ! id) ->
             funassert Delta rho |-- funassert Delta' rho).
intros.
unfold funassert.
intros w [? ?]; split.
clear H1; intro id. rewrite <- (H id); auto.
intros loc fs w' Hw' H4; destruct (H1 loc fs w' Hw' H4)  as [id H3].
exists id; rewrite <- (H id); auto.
intros.
extensionality rho.
apply pred_ext; apply H; intros; auto.
Qed.

Lemma funassert_exit_tycon: forall c Delta ek,
     funassert (exit_tycon c Delta ek) = funassert Delta.
Proof.
intros.
apply same_glob_funassert.
intro.
unfold exit_tycon; simpl. destruct ek; auto.
rewrite glob_specs_update_tycon. auto.
Qed.

(*
Lemma strict_bool_val_sub : forall v t b, 
 strict_bool_val v t = Some b ->
  Cop.bool_val v t = Some b.
Proof.
  intros. destruct v; destruct t; simpl in *; auto; try congruence; 
   unfold Cop.bool_val, Cop.classify_bool; simpl.
  destruct i0; auto.
  f_equal. destruct (Int.eq i Int.zero); try congruence. inv H. reflexivity.
  f_equal. destruct (Int.eq i Int.zero); try congruence. inv H. reflexivity.
  f_equal. destruct (Int.eq i Int.zero); try congruence. inv H. reflexivity.
  destruct f0; inv  H; auto.
  destruct f0; inv  H; auto.
Qed.
*)



