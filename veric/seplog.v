Require Export veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.slice.
Require Import veric.res_predicates.
Require Import veric.expr.

Definition assert := environ -> mpred.  (* Unfortunately
   can't export this abbreviation through SeparationLogic.v because
  it confuses the Lift system *)

Definition writable_share (sh: share) := Share.unrel Share.Rsh sh = Share.top.

Lemma writable_share_right: forall sh, writable_share sh -> Share.unrel Share.Rsh sh = Share.top.
Proof. (* apply Share.contains_Rsh_e.*) auto. Qed.

Lemma address_mapsto_exists:
  forall ch v rsh (sh: pshare) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot),
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) rsh (pshare_sh sh) loc w 
                    /\ core w = core w0.
Proof.  exact address_mapsto_exists. Qed.

Lemma address_mapsto_VALspec_range: 
  forall (ch : memory_chunk) (v : val) rsh (sh : Share.t) (l : address),
       address_mapsto ch v rsh sh l
       |-- VALspec_range (size_chunk ch) rsh sh l.
Proof.  exact address_mapsto_VALspec_range. Qed.

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

(*Definition expr_true (e: Clight.expr) (rho: environ): Prop := 
  bool_val (eval_expr e rho) (Clight.typeof e) = Some true.*)

Definition typed_true (t: type) (v: val)  : Prop := strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t =
Some false.

Definition expr_true e := lift1 (typed_true (typeof e)) (eval_expr e).

Definition expr_false e := lift1 (typed_false (typeof e)) (eval_expr e).

Definition subst {A} (x: ident) (v: val) (P: environ -> A) : environ -> A :=
   fun s => P (env_set s x v).

(* "umapsto" stands for "untyped mapsto", i.e. it does not
   enforce that v2 belongs to type t *)
Definition umapsto (sh: Share.t) (t: type) (v1 v2 : val): pred rmap :=
  match access_mode t with
  | By_value ch => 
    match v1 with
     | Vptr b ofs => 
          address_mapsto ch v2 (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs)
        || !!(v2=Vundef) && EX v2':val, address_mapsto ch v2' (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs)
     | _ => FF
    end
  | _ => FF
  end. 

Definition mapsto sh t v1 v2 := 
             !! (tc_val t v2)  && umapsto sh t v1 v2.

Definition mapsto_ sh t v1 := umapsto sh t v1 Vundef.

Definition writable_block (id: ident) (n: Z): assert :=
   fun rho => 
        EX v: val*type,  EX a: address, EX rsh: Share.t,
          !! (ge_of rho id = Some v /\ val2adr (fst v) a) && VALspec_range n rsh Share.top a.

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
Proof. intro. unfold rev_if_be; destruct big_endian; auto. Qed.

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
 unfold decode_int. rewrite rev_if_be_singleton. simpl.
 reflexivity.
 apply Z.divide_1_l.
 intro loc. hnf. if_tac. exists H0.
 destruct loc as [b' i']. destruct H8; subst b'.
 simpl in H9. assert (i=i') by omega; subst i'.
 rewrite Zminus_diag. hnf. rewrite preds_fmap_NoneP.
  rewrite H4. rewrite if_true by auto. f_equal.
 unfold noat. simpl. rewrite H4. rewrite if_false. apply core_identity.
  swap H8. subst. split; auto. simpl; omega.
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
 VALspec_range (Z_of_nat n)
               (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, ofs).

Lemma memory_block'_eq: 
 forall sh n b i,
  0 <= i ->
  Z_of_nat n + i <= Int.max_unsigned ->
  memory_block' sh n b i = memory_block'_alt sh n b i.
Proof.
intros.
unfold memory_block'_alt.
revert i H H0; induction n; intros;
 [symmetry; apply VALspec_range_0 | ].
unfold memory_block'; fold memory_block'.
rewrite (IHn (i+1))
 by (rewrite inj_S in H0; omega).
symmetry.
rewrite (VALspec_range_split2 1 (Z_of_nat n))
 by (try rewrite inj_S; omega).
f_equal.
rewrite VALspec1.
unfold mapsto_.
unfold umapsto.
simpl access_mode. cbv beta iota.
rewrite Int.unsigned_repr by (pose proof (Zle_0_nat (S n)); omega).
forget (Share.unrel Share.Lsh sh) as rsh.
forget (Share.unrel Share.Rsh sh) as sh'.
clear.
assert (EQ: forall loc, jam (adr_range_dec loc (size_chunk Mint8unsigned)) = jam (eq_dec loc)).
intros [b' z']; unfold jam; extensionality P Q loc;
 destruct loc as [b'' z'']; apply exist_ext; extensionality w;
 if_tac; [rewrite if_true | rewrite if_false]; auto;
  [destruct H; subst; f_equal;  simpl in H0; omega 
  | swap H; inv H0; split; simpl; auto; omega].
apply pred_ext.
intros w ?.
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
rewrite prop_true_andp by auto.
apply orp_left.
intros w [l [[? [? ?]] ?]].
 intros [b' i']; specialize (H2 (b',i')); rewrite EQ in H2;
 hnf in H2|-*;  if_tac; auto. symmetry in H3; inv H3.
 destruct l; inv H. exists m.
 destruct H2 as [H2' H2]; exists H2'; hnf in H2|-*; rewrite H2.
 f_equal. f_equal. rewrite Zminus_diag. reflexivity.
intros w [v2' [l [[? [? ?]] ?]]].
 intros [b' i']; specialize (H2 (b',i')); rewrite EQ in H2;
 hnf in H2|-*;  if_tac; auto. symmetry in H3; inv H3.
 destruct l; inv H. exists m.
 destruct H2 as [H2' H2]; exists H2'; hnf in H2|-*; rewrite H2.
 f_equal. f_equal. rewrite Zminus_diag. reflexivity.
Qed.

Definition memory_block (sh: share) (n: int) (v: val) : mpred :=
 match v with 
 | Vptr b ofs => memory_block' sh (nat_of_Z (Int.unsigned n)) b (Int.unsigned ofs)
 | _ => FF
 end.

Definition lvalue_block (sh: Share.t) (e: Clight.expr) (rho: environ) : mpred :=
  !! (sizeof  (Clight.typeof e) <= Int.max_unsigned) &&
  (memory_block sh (Int.repr (sizeof (Clight.typeof e))))
             (eval_lvalue e rho).

Definition var_block (rsh: Share.t) (idt: ident * type) : assert :=
         lvalue_block rsh (Clight.Evar (fst idt) (snd idt)).

Fixpoint sepcon_list {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A} {AgeA: Age_alg A}
   (p: list (pred A)) : pred A :=
 match p with nil => emp | h::t => h * sepcon_list t end.


Definition stackframe_of (f: Clight.function) : assert :=
  fold_right (fun P Q rho => P rho * Q rho) (fun rho => emp) (map (fun idt => var_block Share.top idt) (Clight.fn_vars f)).

Lemma stackframe_of_eq : stackframe_of = 
        fun f rho => fold_right sepcon emp (map (fun idt => var_block Share.top idt rho) (Clight.fn_vars f)).
Proof.
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

Definition bind_args (formals: list (ident * type)) (P: environ -> pred rmap) : assert :=
          fun rho => !! tc_formals formals rho && P rho.

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
   (ALL  id: ident, ALL fs:funspec,  !! ((glob_types Delta)!id = Some (Global_func fs)) -->
              EX v:val, EX loc:address, 
                   !! (ge_of rho id = Some (v, type_of_funspec fs)
                                 /\ val2adr v loc) && func_at fs loc)
   && 
   (ALL  loc: address, ALL fs:funspec, func_at' fs loc --> 
             EX id:ident,EX v:val,  !! (ge_of rho id = Some (v, type_of_funspec fs)
                                 /\ val2adr v loc) 
               && !! exists fs, (glob_types Delta)!id = Some (Global_func fs)).

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

Definition with_ge (ge: genviron) (G: assert) : pred rmap :=
     G (mkEnviron ge (Map.empty _) (Map.empty _)).

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

Definition tc_expr (Delta: tycontext) (e: expr) : assert:= 
  fun rho => !! denote_tc_assert (typecheck_expr Delta e) rho.

Definition tc_exprlist (Delta: tycontext) (t : list type) (e: list expr) : assert := 
      fun rho => !! denote_tc_assert (typecheck_exprlist Delta t e) rho.

Definition tc_lvalue (Delta: tycontext) (e: expr) : assert := 
     fun rho => !! denote_tc_assert (typecheck_lvalue Delta e) rho.


Definition tc_temp_id (id : positive) (ty : type) 
  (Delta : tycontext) (e : expr) : assert  :=
     fun rho => !! denote_tc_assert (typecheck_temp_id id ty Delta e) rho.  

Definition tc_temp_id_load id tfrom Delta v : assert  :=
fun rho => !! (exists tto, exists x, (temp_types Delta) ! id = Some (tto, x) /\ (allowedValCast (v rho) (tfrom) tto)= true).

Lemma extend_prop: forall P, boxy extendM (prop P).
Proof.
intros.
hnf.
apply pred_ext. intros ? ?. apply H; auto. apply extendM_refl.
repeat intro. apply H.
Qed.

Hint Resolve extend_prop.

Lemma extend_tc_temp_id_load :  forall id tfrom Delta v rho, boxy extendM (tc_temp_id_load id tfrom Delta v rho).
Proof. 
intros. unfold tc_temp_id_load. auto.
Qed. 

Lemma extend_tc_temp_id: forall id ty Delta e rho, boxy extendM (tc_temp_id id ty Delta e rho). 
Proof. 
intros. unfold tc_temp_id. induction e; simpl; destruct t; simpl; auto. 
Qed. 

Lemma extend_tc_expr: forall Delta e rho, boxy extendM (tc_expr Delta e rho).
Proof.
 intros.
unfold tc_expr.
  induction e; simpl;
  destruct t; simpl; auto.
Qed.

Lemma extend_tc_exprlist: forall Delta t e rho, boxy extendM (tc_exprlist Delta t e rho).
Proof.
 intros. unfold tc_exprlist.
  induction e; simpl; auto.
Qed.

Lemma extend_tc_lvalue: forall Delta e rho, boxy extendM (tc_lvalue Delta e rho).
Proof.
 intros.
unfold tc_lvalue.
  induction e; simpl;
  destruct t; simpl; auto.
Qed.



Hint Resolve extend_tc_expr extend_tc_temp_id extend_tc_temp_id_load extend_tc_exprlist extend_tc_lvalue.
Hint Resolve (@extendM_refl rmap _ _ _ _ _).





