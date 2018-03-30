Require Import VST.msl.base.
Require Import VST.msl.boolean_alg.
Require Import VST.msl.sepalg.
Require Import VST.msl.functors.
Require Import VST.msl.sepalg_functors.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.shares.
Require Import VST.msl.cross_split.
Require Import VST.msl.psepalg.
Require Import VST.msl.pshares.
Require Import VST.msl.eq_dec.

Require VST.msl.predicates_sa.

Lemma in_app:   (* THIS IS FROM compcert/Coqlib.v *)
  forall (A: Type) (x: A) (l1 l2: list A), In x (l1 ++ l2) <-> In x l1 \/ In x l2.
Proof.
  intros. split; intro. apply in_app_or. auto. apply in_or_app. auto.
Qed.

Definition list_disjoint {A: Type} (l1 l2: list A) : Prop :=   (* THIS IS FROM compcert/Coqlib.v *)
  forall (x y: A), In x l1 -> In y l2 -> x <> y.

Inductive pshareval_join' {A}{JA: Join A}
  : option (pshare * A) ->  option (pshare * A) ->  option (pshare * A) -> Prop :=
  | pshareval_None1: forall x, pshareval_join' None x x
  | pshareval_None2: forall x, pshareval_join' x None x
  | pshareval_Some: forall x y z,
      join (fst x) (fst y) (fst z) ->
      join (snd x) (snd y) (snd z) ->
      pshareval_join' (Some x) (Some y) (Some z).

Lemma pshareval_join_e{A}{JA: Join A}:  forall a b c, join a b c -> pshareval_join' a b c.
Proof.
intros.
inv H; [constructor 1 | constructor 2 | constructor 3]; auto.
apply H0.
apply H0.
Qed.

Lemma pshareval_join_i{A}{JA: Join A}: forall a b c, pshareval_join' a b c -> join a b c.
Proof.
intros.
inv H; [constructor 1 | constructor 2 | constructor 3]; auto.
split; auto.
Qed.

Module Type ENV.

Parameter env: forall (key: Type) (A: Type), Type.

Section ENVSEC.
Context {key: Type}{A: Type}.

Instance JA: Join A := Join_equiv A. (* It's a feature, not a bug, that this Instance is not visible as an Instance
   outside the Section *)

Parameter env_get: forall (rho: env key A) (id: key), option (pshare * A).
Parameter env_set_sh: forall {KE: EqDec key} (id: key) (v: option (pshare * A)) (rho: env key A), env key A.

Definition env_set  {KE: EqDec key} (id: key) (v: A) (rho: env key A) : env key A :=
     env_set_sh id (Some (pfullshare, v)) rho.

Axiom env_gss: forall {KE: EqDec key}  i a rho, env_get (env_set i a rho) i = Some (pfullshare, a).
Axiom env_gso: forall {KE: EqDec key}  i j a rho, i <> j -> env_get (env_set j a rho) i = env_get rho i.

Axiom env_gss_sh: forall {KE: EqDec key} i v rho,
  env_get (env_set_sh i v rho) i = v.

Axiom env_gso_sh: forall {KE: EqDec key} i j v rho, i <> j ->
   env_get (env_set_sh j v rho) i = env_get rho i.

Definition finite_idfun (f: key -> option (pshare * A)) :=
  exists l, forall a, ~In a l -> f a = None.

Parameter mk_env:  forall (f: key -> option (pshare * A)), finite_idfun f -> env key A.
(*
Arguments mk_env.
*)

Axiom env_get_mk_env:  forall (f: key -> option (pshare * A)) P, env_get (mk_env f P) = f.

Axiom env_finite: forall rho, finite_idfun (env_get rho).

Axiom env_ext: forall rho1 rho2, env_get rho1 = env_get rho2 -> rho1=rho2.

Axiom env_funct: forall rho1 rho2,
  rho1 = rho2 -> forall id sh1 sh2 v1 v2, env_get rho1 id = Some(sh1, v1)
  -> env_get rho2 id = Some(sh2, v2)
  -> v1 = v2.

Parameter empty_env : env key A.

Axiom env_get_empty: forall id, env_get empty_env id = None.

(* SEPARATION ALGEBRAS *)
(* We use the Section to hide these instances, because  variables-as-resources clients
  will want Join_env, but global-variables users will want Join_equiv.
  Only the variables-as-resources clients should add these instances,
  which is done in the Module EnvSA,  below
*)
Instance Join_env: Join (env key A) :=
    fun (rho1 rho2 rho3: env key A) => join (env_get rho1) (env_get rho2) (env_get rho3).
Parameter Perm_env: forall {PA: Perm_alg A}, Perm_alg (env key A).  Existing Instance Perm_env.

Instance Sep_env {SA: Sep_alg A}: Sep_alg (env key A).
 refine (mkSep Join_env (fun _ => empty_env) _ _).
 repeat intro; rewrite env_get_empty; constructor.
 auto.
Defined.

Instance Sing_env  {SA: Sep_alg A} : Sing_alg (env key A).
  refine (mkSing empty_env _). reflexivity.
Defined.

Parameter Canc_env: forall {PA: Perm_alg A}{CA: Canc_alg A}, Canc_alg (env key A). Existing Instance Canc_env.
Parameter Disj_env: forall {PA: Perm_alg A}{DA: Disj_alg A}, Disj_alg (env key A).   Existing Instance Disj_env.
Parameter Cross_env : Cross_alg (env key A).  Existing Instance Cross_env.


(* env_mapsto and the lemmas about it are in a Separation Logic, not just a separation algebra.
  We have two style of separation logic (direct and ageable), and this module Env is usable with
   either kind.  Thus, we build primitives whose names start with _ to avoid polluting the
  namespace; then we reveal them at appropriate types in EnvSL and EnvASL, below.
*)
Import VST.msl.predicates_sa.

(* ENV_MAPSTO *)
Parameter _env_mapsto: forall {KE: EqDec key}  (id: key) (sh: Share.t) (v: A), pred (env key A).

Axiom _env_mapsto_exists: forall {KE: EqDec key}  id sh v, exists rho, _env_mapsto id (pshare_sh sh) v rho.

Axiom _env_get_mapsto: forall {KE: EqDec key}  id v rho,
  (exists sh, env_get rho id = Some (sh,v)) =
  (exp (fun sh => _env_mapsto id sh v) * TT)%pred rho.

Axiom _env_get_mapsto': forall {KE: EqDec key}  id (sh: pshare) v rho,
  env_get rho id = Some(pfullshare,v) ->
       (_env_mapsto id (pshare_sh sh) v * TT)%pred rho.

Axiom _env_mapsto_set: forall {KE: EqDec key} id v,
  _env_mapsto id Share.top v (env_set id v empty_env).

Axiom _env_mapsto_set_sh: forall {KE: EqDec key} id (sh: pshare) v,
  _env_mapsto id (pshare_sh sh) v (env_set_sh id (Some (sh, v)) empty_env).

Axiom _env_mapsto_get: forall {KE: EqDec key}  id sh v rho,
  _env_mapsto id sh v rho
   -> exists Pf,
        env_get rho id = Some (exist nonunit sh Pf, v).

Axiom _env_mapsto_get_neq: forall {KE: EqDec key}  (id1 id2: key) (sh: Share.t) (v: A) rho,
  id1 <> id2 -> _env_mapsto id1 sh v rho -> env_get rho id2 = None.

Axiom _env_mapsto_empty_env: forall {KE: EqDec key}  id v sh, ~(_env_mapsto id sh v empty_env).

Axiom _env_mapsto_splittable: forall {KE: EqDec key}  id v (sh sh1 sh2: pshare) rho,
  join sh1 sh2 sh
  -> (_env_mapsto id (pshare_sh sh) v rho
        <-> (_env_mapsto id (pshare_sh sh1) v * _env_mapsto id (pshare_sh sh2) v)%pred rho).
End ENVSEC.

End ENV.

Module Env: ENV.

Section ENVSEC.
Context {key: Type}{A: Type}.
Instance JA: Join A := Join_equiv A.

Definition env := fpm key (pshare * A).

Definition env_get (rho: env) (id: key) : option (pshare * A) := lookup_fpm rho id.

Definition env_set_sh {KE: EqDec key} (id: key) (v: option (pshare * A)) (rho: env) : env :=
  insert'_fpm _ id v rho.

Definition env_set {KE: EqDec key} (id: key) (v: A) (rho: env) : env :=
  insert_fpm _ id (pfullshare,v) rho.

Lemma env_gss {KE: EqDec key} : forall i a rho, env_get (env_set i a rho) i = Some (pfullshare, a).
Proof.
intros.
apply fpm_gss.
Qed.

Lemma env_gso {KE: EqDec key}: forall i j a rho, i <> j -> env_get (env_set j a rho) i = env_get rho i.
Proof.
intros.
apply fpm_gso; auto.
Qed.

Lemma env_gss_sh {KE: EqDec key}: forall i v rho, env_get (env_set_sh i v rho) i = v.
Proof.
  intros. unfold env_get, env_set_sh.
  unfold lookup_fpm, insert'_fpm; simpl. destruct rho as [f Hf]. simpl.
  destruct (eq_dec i i); auto. contradiction n; auto.
Qed.

Lemma env_gso_sh {KE: EqDec key} : forall i j v rho, i <> j -> env_get (env_set_sh j v rho) i = env_get rho i.
Proof.
  intros. unfold env_get, env_set_sh.
  unfold lookup_fpm, insert'_fpm; simpl. destruct rho as [f Hf]. simpl.
  destruct (eq_dec j i); auto.
  subst; contradiction H; auto.
Qed.

Definition finite_idfun (f: key -> option (pshare * A)) :=
          (exists l, forall a, ~In a l -> f a = None).

Definition mk_env_aux: forall f, finite_idfun f -> finMap f.
Proof.
intros.
unfold finMap.
destruct H as  [l ?].
exists l.
intros.
unfold compose; simpl.
rewrite H; auto.
Qed.

Definition mk_env (f: key -> option (pshare * A))  (FIN: finite_idfun f):  env :=
   exist _ _ (mk_env_aux _ FIN).

Lemma env_get_mk_env: forall (f: key -> option (pshare * A)) P, env_get (mk_env f P) = f.
Proof.
intros.
unfold mk_env, env_get.
simpl.
unfold compose.
extensionality id; auto.
Qed.

Lemma env_finite: forall rho, finite_idfun (env_get rho).
intros.
destruct rho.
unfold finite_idfun, finMap in *.
generalize f; intros [l ?].
exists l; simpl in *.
intros; unfold compose in *.
apply e; auto.
Qed.

Lemma env_ext: forall rho1 rho2, env_get rho1 = env_get rho2 -> rho1=rho2.
Proof.
intros.
destruct rho1; destruct rho2; simpl in *.
apply exist_ext.
unfold env_get in *.
simpl in *.
extensionality id.
generalize (equal_f  H id); intro.
destruct (x id); destruct (x0 id); inv H0; auto.
Qed.

Lemma env_funct: forall rho1 rho2,
  rho1 = rho2 -> forall id sh1 sh2 v1 v2, env_get rho1 id = Some(sh1, v1)
  -> env_get rho2 id = Some(sh2, v2)
  -> v1 = v2.
Proof.
  intros rho1 rho2 H id sh1 sh2 v1 v2 H1 H2.
  destruct rho1; destruct rho2; unfold env_get in *; simpl in *.
  inversion H; subst x0. inv H. congruence.
Qed.

Lemma finite_idfun_empty: finite_idfun (fun _ => None).
Proof.
exists nil.
auto.
Qed.

Definition empty_env : env := mk_env _ finite_idfun_empty.

Lemma env_get_empty: forall id, env_get empty_env id = None.
Proof.
intros.
unfold empty_env. rewrite env_get_mk_env; auto.
Qed.

Instance Join_env: Join env :=
    fun (rho1 rho2 rho3: env) => join (env_get rho1) (env_get rho2) (env_get rho3).

Lemma Join_env_eq: Join_env = Join_fpm (Join_prod _ Join_pshare _ JA).
Proof.
  repeat intro.
 extensionality rho1 rho2 rho3;
destruct rho1 as [rho1 V1]; destruct rho2 as [rho2 V2]; destruct rho3 as [rho3 V3].
unfold Join_env, Join_fpm; simpl.
apply prop_ext; split; intros H id; specialize ( H id);
unfold env_get in * ; simpl in *; clear - H;
destruct (rho1 id) as [[[sh1 v1] n1]| ];
destruct (rho2 id) as [[[sh2 v2] n2]| ];
destruct (rho3 id) as [[[sh3 v3] n3]| ];
inv H; simpl in *;  try constructor; auto.
rewrite (proof_irr v1 v3); constructor.
rewrite (proof_irr v2 v3); constructor.
rewrite (proof_irr v1 v3); constructor.
rewrite (proof_irr v2 v3); constructor.
Qed.

Instance Perm_env {PA: Perm_alg A}: @Perm_alg env Join_env.
Proof.
  rewrite Join_env_eq. apply Perm_fpm; auto with typeclass_instances.
Qed.

Instance Sep_env {SA: Sep_alg A}: @Sep_alg env Join_env.
 refine (mkSep Join_env (fun _ => empty_env) _ _).
 repeat intro; rewrite env_get_empty; constructor.
 auto.
Defined.

Instance Sing_env {SA: Sep_alg A}: @Sing_alg env Join_env Sep_env.
  refine (mkSing empty_env _). reflexivity.
Defined.

Instance Canc_env {PA: Perm_alg A}{CA: Canc_alg A}: @Canc_alg env Join_env.
Proof.   rewrite Join_env_eq. apply Canc_fpm; auto with typeclass_instances.
Qed.

Instance Disj_env {PA: Perm_alg A}{DA: Disj_alg A}: @Disj_alg env Join_env.
Proof.   rewrite Join_env_eq. apply Disj_fpm; auto with typeclass_instances.
Qed.

Instance Cross_env: Cross_alg env.
Proof.
 rewrite Join_env_eq.
 unfold env.
 pose (bij := @fpm_bij key _ _ (@lift_prod_bij share _ A)).
 pose (J := @Join_fpm key _ (@Join_lift _ (Join_prod share _ _ JA))).
 unfold pshare.
 replace
  (@Join_fpm key (@lifted Share.t Share.Join_ba * A)
     (Join_prod (@lifted Share.t Share.Join_ba) Join_pshare A
        JA))
  with (Join_bij
       (fpm key
          (@lifted (share * A)
             (Join_prod share Share.Join_ba A JA))) _
       (fpm key (@lifted share Share.Join_ba * A)) bij).
 apply (Cross_bij _ _ _ bij).
 apply cross_split_fpm; auto with typeclass_instances.
 intros [sh v]. destruct (dec_share_identity sh); [left | right].
 apply identity_unit_equiv in i. apply identity_unit_equiv. split; auto.
 contradict n.
 apply identity_unit_equiv in n. apply identity_unit_equiv. destruct n; auto.
 extensionality x y z.
 unfold J, bij; clear J bij.
 apply forall_ext; intro i.
 unfold finMap; simpl.
 change  (@proj1_sig (key -> option (@lifted Share.t Share.Join_ba * A))
     (fun f : key -> option (@lifted Share.t Share.Join_ba * A) =>
      exists l : list key,
        forall a : key,
        ~ @In key a l -> f a = @None (@lifted Share.t Share.Join_ba * A)))
  with (@proj1_sig (key -> option (@lifted share Share.Join_ba * A))
      (@finMap key (@lifted share Share.Join_ba * A))).
 set  (xi := proj1_sig x i); clearbody xi.
 set (yi:= proj1_sig y i); clearbody yi.
 set (zi:= proj1_sig z i); clearbody zi.
 clear.
 destruct xi; destruct yi; destruct zi;
 apply prop_ext; split; intro; inv H; try constructor.
 destruct p as [[x Hx] x']. destruct p0 as [[y Hy] y']. destruct p1 as [[z Hz] z'].
  simpl in *. inv H3; simpl in *. split; auto.
 destruct p as [[x Hx] x']. destruct p0 as [[y Hy] y']. destruct p1 as [[z Hz] z'].
  simpl in *. inv H3; simpl in *. split; auto.
 destruct p as [[x Hx] x']. destruct p0 as [[z Hz] z'].
 simpl in H1. inv H1. apply join_unit2; auto.
 repeat f_equal; apply proof_irr.
 destruct p as [[x Hx] x']. destruct p0 as [[z Hz] z'].
 simpl in H0. inv H0. apply join_unit1; auto.
 repeat f_equal; apply proof_irr.
Qed.

Import VST.msl.predicates_sa.

Definition _env_mapsto {KE: EqDec key} (id: key) (sh: Share.t) (v: A) : pred env :=
    fun rho => exists p,
   forall id', env_get rho id' = if eq_dec id id' then Some (exist _ sh p,v) else None.

Lemma _env_mapsto_exists{KE: EqDec key}: forall id sh v, exists rho, _env_mapsto id (pshare_sh sh) v rho.
Proof.
intros.
assert (finite_idfun (fun id' => if eq_dec id id' then Some (sh, v) else None)).
exists (id::nil).
intros.
simpl in H.
intuition.
destruct (eq_dec id a); try contradiction; auto.
exists (mk_env _ H).
unfold _env_mapsto.
destruct sh; simpl in *.
exists n.
intros.
auto.
Qed.

Lemma _env_get_mapsto {KE: EqDec key}:  forall (id: key) (v: A) (rho: env),
  (exists sh, env_get rho id = Some (sh,v)) =
  (exp (fun sh => _env_mapsto id sh v) * TT)%pred rho.
Proof.
intros.
apply prop_ext; split; intros.
destruct H as [sh ?].
destruct (_env_mapsto_exists id sh v) as [rho1 ?].
exists rho1.
assert (finite_idfun (fun id' => if eq_dec id id' then None else env_get rho id')).
destruct (env_finite rho) as [l ?].
exists l.
intros.
destruct (eq_dec id a); auto.
exists (mk_env _ H1).
split.
simpl.
intro x.
rewrite env_get_mk_env.
intros.
destruct H0.
rename x into id0.
specialize ( H0 id0).
destruct (eq_dec id id0).
subst.
rewrite H; rewrite H0.
destruct sh; simpl in *.
rewrite (proof_irr x0 n); constructor.
rewrite H0.
constructor.
split.
exists (pshare_sh sh).
auto.
auto.
destruct H as [?w [?w [? [[sh ?] _]]]].
destruct H0.
specialize ( H0 id).
destruct (eq_dec id id); try congruence.
specialize ( H id).
rewrite H0 in H.
inv H.
econstructor; eauto.
destruct a2; destruct a3; destruct H4 as [? [? ?]]; simpl in *; subst.
econstructor; eauto.
Qed.

Lemma _env_get_mapsto'  {KE: EqDec key}: forall id (sh: pshare) v rho,
  env_get rho id = Some(pfullshare,v) -> (_env_mapsto id (pshare_sh sh) v * TT)%pred rho.
Proof.
intros.
destruct (top_correct' (pshare_sh sh)) as [sh2 ?].
assert (finite_idfun (fun i => if eq_dec i id then Some (sh,v) else None)).
exists (id::nil); intros. simpl in H1.
assert (id <> a) by intuition.
destruct (eq_dec a id); auto. contradiction H2; auto.
destruct (dec_share_identity sh2).
assert (finite_idfun (fun i => if eq_dec i id then None else env_get rho i)).
destruct (env_finite rho) as [l ?].
exists l; intros. destruct (eq_dec a id); auto.
exists (mk_env _ H1); exists (mk_env _ H2); split; [|split]; auto.
intro i'.
do 2 rewrite env_get_mk_env.
destruct (eq_dec i' id).
subst. rewrite H.
apply join_comm in H0.
apply i in H0.
destruct sh; simpl in *.
subst.
rewrite (proof_irr n top_share_nonunit).
constructor.
constructor.
exists (proj2_sig sh).
intros.
rewrite env_get_mk_env.
destruct (eq_dec id' id).
subst. destruct (eq_dec id id); try congruence.
f_equal. f_equal. destruct sh; simpl. auto.
destruct (eq_dec id' id); try contradiction; auto.
destruct (eq_dec id id'); try contradiction; auto.
contradiction n; auto.
assert (finite_idfun (fun i => if eq_dec i id then Some(mk_lifted sh2 (nonidentity_nonunit n), v) else env_get rho i)).
destruct (env_finite rho) as [l ?].
exists l; intros. destruct (eq_dec a id); auto.
subst.
specialize ( H2 id H3).
rewrite H in H2; inv H2.
exists (mk_env _ H1); exists (mk_env _ H2); split; [|split]; auto.
intro i'.
do 2 rewrite env_get_mk_env.
destruct (eq_dec i' id).
subst. rewrite H.
constructor; simpl; auto.
constructor; simpl; auto.
apply join_equiv_refl.
constructor.
exists (proj2_sig sh).
intros.
rewrite env_get_mk_env.
destruct (eq_dec id' id).
subst. destruct (eq_dec id id); try contradiction n0; auto.
f_equal. f_equal. destruct sh; simpl.  auto.
destruct (eq_dec id id'); auto. contradiction n0; auto.
Qed.

Lemma _env_mapsto_set{KE: EqDec key}: forall id v,
  _env_mapsto id Share.top v (env_set id v empty_env).
Proof.
  intros id v.
  exists top_share_nonunit.
  intros id'.
  destruct (eq_dec id id') as [Hid|].
    rewrite <- Hid.
    rewrite env_gss; auto.
    rewrite env_gso; auto.
Qed.

Lemma _env_mapsto_set_sh{KE: EqDec key}: forall id (sh: pshare) v,
  _env_mapsto id (pshare_sh sh) v (env_set_sh id (Some (sh,v)) empty_env).
Proof.
  intros id [sh Pf] v.
  exists Pf.
  intros id'.
  destruct (eq_dec id id') as [Hid|].
    rewrite <- Hid.
    rewrite env_gss_sh; auto.
    rewrite env_gso_sh; auto.
Qed.

Lemma _env_mapsto_get{KE: EqDec key}: forall id sh v rho,
  _env_mapsto id sh v rho
   -> exists Pf: nonunit sh,
        env_get rho id = Some (exist nonunit sh Pf, v).
Proof.
  unfold _env_mapsto, env_get.
  intros id sh v rho [p H1].
  specialize ( H1 id); simpl in *.
  destruct (eq_dec id id); firstorder.
Qed.

Lemma _env_mapsto_empty_env {KE: EqDec key} : forall id v sh,
  ~(_env_mapsto id sh v empty_env).
Proof.
  unfold not, _env_mapsto.
  intros ? ? ? [p H].
  specialize ( H id).
  destruct (eq_dec id id); auto.
  inversion H.
Qed.

Lemma _env_mapsto_get_neq {KE: EqDec key} : forall (id1 id2: key) (sh: Share.t) (v: A) rho,
  id1 <> id2 -> _env_mapsto id1 sh v rho -> env_get rho id2 = None.
Proof.
  unfold _env_mapsto.
  intros id1 id2 sh v rho Hneq [p H1].
  specialize ( H1 id2).
  destruct (eq_dec id1 id2); try contradiction ;auto.
Qed.

Lemma _env_mapsto_splittable1 {KE: EqDec key}: forall id v (sh sh1 sh2: pshare) rho,
  join (proj1_sig sh1) (proj1_sig sh2) (proj1_sig sh)
  -> (_env_mapsto id  (pshare_sh sh1) v * _env_mapsto id (pshare_sh sh2) v)%pred rho
  -> _env_mapsto id (pshare_sh sh) v rho.
Proof.
  intros id v sh sh1 sh2 rho H1 H2.
  destruct H2 as [rho1 [rho2 [Hrho_join [[Pf1 H_env_mapsto1] [Pf2 H_env_mapsto2]]]]].
  exists (proj2_sig sh); intro id'.
  specialize ( H_env_mapsto1 id'); specialize ( H_env_mapsto2 id').
  generalize Hrho_join; clear Hrho_join; unfold join; simpl; intros Hrho_join.
  specialize ( Hrho_join id').
  rewrite H_env_mapsto1 in Hrho_join; rewrite H_env_mapsto2 in Hrho_join.
  destruct (eq_dec id id').

  (* id = id' *)
  inversion Hrho_join; simpl in *; subst.
  destruct a3; destruct H3 as [? [? ?]]; simpl in *; subst.
  apply (f_equal (fun x => Some(x, a))).
  apply lifted_eq.
  eapply join_eq; eauto.

  (* id <> id' *)
  inversion Hrho_join; auto.
Qed.

Lemma _env_mapsto_splittable2{KE: EqDec key}: forall id v (sh sh1 sh2: pshare) rho,
  join (proj1_sig sh1) (proj1_sig sh2) (proj1_sig sh)
  -> _env_mapsto id (pshare_sh sh) v rho
  -> (_env_mapsto id (pshare_sh sh1) v * _env_mapsto id (pshare_sh sh2) v)%pred rho.
Proof.
  intros id v sh sh1 sh2 rho Hjoin H.
  destruct H as [? H0].
  exists (env_set_sh id (Some (sh1,v)) empty_env); exists (env_set_sh id (Some(sh2,v)) empty_env).
  split.

  intros id'.
  specialize ( H0 id'); rewrite H0.
  destruct (eq_dec id id') as [Hid_id'_eq | Hid_id'_neq].

  (* id = id' *)
  subst id'.
  do 2 rewrite env_gss_sh. constructor.
  constructor; auto.
  apply join_equiv_refl.

  (* id <> id' *)
  rewrite (env_gso_sh); auto.
  rewrite (env_gso_sh); auto.
  rewrite env_get_empty. constructor.

  destruct sh1 as [sh1 n1]; destruct sh2 as [sh2 n2];  unfold _env_mapsto; split.
  exists n1; reflexivity.
  exists n2; reflexivity.
Qed.

Lemma _env_mapsto_splittable {KE: EqDec key}: forall id v (sh sh1 sh2: pshare) rho,
  join (proj1_sig sh1) (proj1_sig sh2) (proj1_sig sh)
  -> (_env_mapsto id (pshare_sh sh) v rho
        <-> (_env_mapsto id (pshare_sh sh1) v * _env_mapsto id (pshare_sh sh2)  v)%pred rho).
Proof.
  intros.
  split; intros.
  eapply _env_mapsto_splittable2; eauto.
  eapply _env_mapsto_splittable1; eauto.
Qed.

End ENVSEC.
End Env.
Export Env.

Module EnvSA.

Existing Instance Join_env.
Existing Instance Perm_env.
Existing Instance Sep_env.
Existing Instance Sing_env.
Existing Instance Canc_env.
Existing Instance Disj_env.
Existing Instance Cross_env.

Lemma empty_env_unit {key: Type}{A: Type}:
    forall rho: env key A, unit_for empty_env rho.
Proof.
intro; intros.
unfold unit_for.
intro.
rewrite env_get_empty.
constructor.
Qed.

Lemma empty_env_unit' {key: Type}{A: Type}: forall rho: env key A, join empty_env rho rho.
Proof.
intros; apply empty_env_unit.
Qed.
Hint Resolve @empty_env_unit @empty_env_unit'.

Lemma env_join_sub1 {key: Type}{A: Type}:
  forall rho1 rho2: env key A, (forall id x, env_get rho1 id = Some x -> env_get rho2 id = Some x) ->
     join_sub rho1 rho2.
Proof.
intros.
pose (JA := Join_equiv A).
assert (forall i: key, cjoin_sub (env_get rho1 i) (env_get rho2 i)).

intro.
case_eq (env_get rho1 i); intros.
specialize (H _ _ H0).
exists None. rewrite H. constructor.
econstructor; constructor.
assert (finite_idfun (fun i => proj1_sig (X i))).
destruct (env_finite rho2) as [l ?].
exists l; intros.
specialize (H0 _ H1).
generalize (X a); intro.
destruct c.
simpl.
rewrite H0 in j; inv j; auto.
exists (mk_env _ H0).
intro i.
rewrite env_get_mk_env.
destruct (X i).
simpl.
auto.
Qed.

Lemma env_get_join_sub {key: Type}{A: Type}: forall (rho rho': env key A) id sh v,
   join_sub rho rho' -> env_get rho id = Some (sh,v) ->
     exists sh', env_get rho' id = Some (sh', v) /\ join_sub (pshare_sh sh)  (pshare_sh sh').
Proof.
intros.
destruct H.
specialize ( H id).
rewrite H0 in H.
clear H0 rho.
destruct sh as [sh n].
destruct (env_get rho' id) as [[[sh' n'] v'] |]; [|inv H].
revert H;
destruct (env_get x id) as [[[shx nx] vx] | ]; intro H; inv H.
simpl in *.
destruct H3 as [? [? ?]]; simpl in *; subst.
econstructor; split; eauto. econstructor; eauto.
econstructor; split; eauto.
simpl. apply join_sub_refl.
Qed.

Lemma env_at_joins {key: Type}{A: Type}{KE: EqDec key}:
  forall rho1 rho2: env key A,
         (forall id, @joins _ (@Join_lower (pshare * A) (Join_prod pshare Join_pshare A (Join_equiv _))) (env_get rho1 id) (env_get rho2 id)) ->
               joins rho1 rho2.
Proof.
intros.
unfold joins in H.
pose (share_of rho id := match @env_get key A rho id with
                                       | None => Share.bot
                                       | Some (p,v) => pshare_sh p
                                       end).
assert (forall id, joins (share_of rho1 id) (share_of rho2 id)).
intros.
destruct (H id) as [x H0].
clear - H0.
unfold share_of.
inv H0.
apply bot_joins.
rewrite joins_sym.
apply bot_joins.
destruct a1; destruct a2; destruct a3; destruct H2 as [? [? ?]]; simpl in *. subst. eauto.
pose (h id := proj1_sig (share_joins_constructive _ _ (H0 id))).
pose (g sh (v: A) := match dec_share_identity sh with
                         | left _ => None
                         | right p => Some (mk_lifted _ (nonidentity_nonunit p), v)
                         end).
pose (f id := match env_get rho1 id, env_get rho2 id with
                     | None, shv => shv
                     | shv, None => shv
                     | Some (_,v), _ => g (h id) v
                      end).
assert (finite_idfun f).
destruct (env_finite rho1) as [l1 ?].
destruct (env_finite rho2) as [l2 ?].
exists (l1++l2).
intros.
rewrite in_app in H3.
destruct (In_dec eq_dec a l1) as [H3' | H3'].
contradiction H3; auto.
assert (H4: ~In a l2) by intuition.
specialize ( H1 a H3'). specialize ( H2 a H4).
unfold f.
rewrite H1; rewrite H2; auto.
exists (mk_env _ H1).
intro id.
rewrite env_get_mk_env.
unfold f; clear H1 f.
unfold g, h; clear g h.
destruct (share_joins_constructive (share_of rho1 id) (share_of rho2 id) (H0 id)).
simpl.
specialize ( H id). destruct H as [c ?].
unfold share_of in *; clear share_of.
specialize ( H0 id).
destruct (env_get rho1 id) as [[sh1 v1]|];
destruct (env_get rho2 id) as [[sh2 v2]|];
try solve [constructor].
inv H.
destruct a3; destruct H3 as [? [? ?]].  simpl in H,H1,H2; subst.
destruct (dec_share_identity x).
generalize (split_identity _ _ j i); intro.
elimtype False; clear - H1.
revert H1; apply nonunit_nonidentity.
apply pshare_nonunit.
constructor; auto. constructor; auto. simpl. apply join_equiv_refl.
Qed.

Lemma env_at_join_sub {key: Type}{A: Type}{KE: EqDec key}:
  forall rho1 rho2, (forall id: key, @join_sub _ (@Join_lower (pshare * A) (Join_prod pshare Join_pshare A (Join_equiv _))) (env_get rho1 id) (env_get rho2 id)) -> join_sub rho1 rho2.
Proof.
intros.
unfold join_sub in H.
pose (share_of rho id := match @env_get key A rho id with
                                       | None => Share.bot
                                       | Some (p,v) => pshare_sh p
                                       end).
assert (forall id, join_sub (share_of rho1 id) (share_of rho2 id)).
intros.
specialize (H id); destruct H.
unfold share_of.
inv H.
apply bot_correct'.
apply join_sub_refl.
destruct a1; destruct a2; destruct a3; destruct H3 as [? [? ?]]; simpl in *. subst.
econstructor; eauto.
pose (h id := proj1_sig (share_join_sub_constructive _ _ (H0 id))).
pose (g sh (v: A) := match dec_share_identity sh with
                         | left _ => None
                         | right p => Some (mk_lifted _ (nonidentity_nonunit p), v)
                         end).
pose (f id := match env_get rho2 id with
                     | None => None
                     | Some (_,v) => g (h id) v
                      end).
assert (finite_idfun f).
destruct (env_finite rho2) as [l2 ?].
exists l2.
intros.
unfold f. rewrite H1; auto.
exists (mk_env _ H1).
intro id.
rewrite env_get_mk_env.
unfold f; clear H1 f.
unfold g, h; clear g h.
destruct (share_join_sub_constructive (share_of rho1 id) (share_of rho2 id) (H0 id)).
simpl.
specialize ( H id). destruct H as [c ?].
unfold share_of in *; clear share_of.
specialize ( H0 id).
destruct (env_get rho1 id) as [[sh1 v1]|];
destruct (env_get rho2 id) as [[sh2 v2]|].
inv H.
destruct (dec_share_identity x).
constructor.
contradiction n.
apply unit_identity with (pshare_sh sh2); apply join_comm; auto.
destruct H4 as [? [? ?]]; simpl snd in *; subst.
generalize (join_canc (join_comm j) (join_comm H)); intro; subst.
destruct (dec_share_identity (lifted_obj (fst a2))).
contradiction (@nonunit_nonidentity _ _ _ _ (lifted_obj (fst a2))).
destruct (fst a2); simpl; auto.
destruct a2; simpl in *. destruct p; simpl in *.
constructor; simpl; auto.
constructor; auto.
simpl. apply join_equiv_refl.
inv H.
apply bot_identity in j.
subst.
destruct (dec_share_identity (pshare_sh sh2)).
contradiction (@nonunit_nonidentity _ _ _ _ (pshare_sh sh2)).
apply pshare_nonunit.
apply join_unit1; auto.
f_equal. f_equal. unfold mk_lifted; destruct sh2; simpl. f_equal. apply proof_irr.
constructor.
Qed.


Lemma identity_empty_env {key: Type}{A: Type}{KE: EqDec key}:  forall rho: env key A, identity rho <-> rho = empty_env.
Proof.
intros.
split; intros.
generalize (identity_unit (a:=empty_env)H); intro.
spec H0.
exists rho; apply join_comm; apply empty_env_unit.
generalize (empty_env_unit rho); intro.
unfold unit_for in *.
generalize (join_eq H0 (join_comm H1)); intro; auto.
subst.
simpl.
apply unit_identity with empty_env; auto.
Qed.

End EnvSA.

Module EnvSL.
Import EnvSA.
Import VST.msl.predicates_sa.

Definition env_mapsto: forall {key A}{KE: EqDec key} (id: key) (sh: Share.t) (v: A) , pred (env key A) := @_env_mapsto.
Arguments env_mapsto [key] [A] [KE] _ _ _ _.

Lemma env_mapsto_exists{key A}{KE: EqDec key}: forall id sh (v: A), exists rho, _env_mapsto id (pshare_sh sh) v rho.
Proof. apply _env_mapsto_exists. Qed.

Lemma env_get_mapsto {key A}{KE: EqDec key}:  forall (id: key) (v: A) (rho: env _ _),
  (exists sh, env_get rho id = Some (sh,v)) =
  (exp (fun sh => _env_mapsto id sh v) * TT)%pred rho.
Proof. apply _env_get_mapsto. Qed.

Lemma env_get_mapsto'  {key A}{KE: EqDec key}: forall id (sh: pshare) (v: A) rho,
  env_get rho id = Some(pfullshare,v) -> (_env_mapsto id (pshare_sh sh) v * TT)%pred rho.
Proof. apply _env_get_mapsto'. Qed.

Lemma env_mapsto_set {key A}{KE: EqDec key}: forall id (v: A),
    env_mapsto id Share.top v (env_set id v empty_env).
Proof. apply _env_mapsto_set. Qed.

Lemma env_mapsto_set_sh{key A}{KE: EqDec key}: forall id (sh: pshare) (v: A),
  _env_mapsto id (pshare_sh sh) v (env_set_sh id (Some (sh,v)) empty_env).
Proof. apply _env_mapsto_set_sh. Qed.

Lemma env_mapsto_get{key A}{KE: EqDec key}: forall id sh (v:A) rho,
  env_mapsto id sh v rho
   -> exists Pf: nonunit sh,
        env_get rho id = Some (exist nonunit sh Pf, v).
Proof. apply _env_mapsto_get. Qed.

Lemma env_mapsto_empty_env {key A}{KE: EqDec key} : forall id (v:A) sh,
  ~(env_mapsto id sh v empty_env).
  Proof. apply _env_mapsto_empty_env. Qed.

Lemma env_mapsto_get_neq {key A}{KE: EqDec key} : forall (id1 id2: key) (sh: Share.t) (v: A) rho,
  id1 <> id2 -> env_mapsto id1 sh v rho -> env_get rho id2 = None.
Proof. apply _env_mapsto_get_neq. Qed.

Lemma env_mapsto_splittable {key A}{KE: EqDec key}: forall id (v:A) (sh sh1 sh2: pshare) rho,
  join (proj1_sig sh1) (proj1_sig sh2) (proj1_sig sh)
  -> (_env_mapsto id (pshare_sh sh) v rho
        <-> (_env_mapsto id (pshare_sh sh1) v * _env_mapsto id (pshare_sh sh2)  v)%pred rho).
Proof. apply _env_mapsto_splittable. Qed.

Lemma env_mapsto_positive{key: Type}{A: Type}{KE: EqDec key}: forall id sh (v: A) rho,
  env_mapsto id sh v rho -> nonidentity sh.
Proof.
  intros until rho.
  intro H; apply env_mapsto_get in H; destruct H.
  auto.
  apply nonunit_nonidentity; auto.
Qed.

Lemma emp_empty_env {key: Type}{A: Type}:  forall rho: env key A, emp rho <-> rho = empty_env.
Proof.
intros.
split; intros.
generalize (identity_unit (a:=empty_env)H); intro.
spec H0.
exists rho; apply join_comm; apply empty_env_unit.
generalize (empty_env_unit rho); intro.
unfold unit_for in *.
generalize (join_eq H0 (join_comm H1)); intro; auto.
subst.
simpl.
apply unit_identity with empty_env; auto.
Qed.

Lemma emp_empty_env' {key}{A}: emp (@empty_env key A).
Proof.
rewrite emp_empty_env.
auto.
Qed.
Hint Resolve @emp_empty_env'.

Lemma env_mapsto_cohere{key: Type}{A: Type}{KE: EqDec key}: forall id sh1 (v1: A) sh2 v2,
  (env_mapsto id sh1 v1 * TT) && (env_mapsto id sh2 v2 * TT)
    |-- !!(v1=v2).
Proof.
  intros.
  intros w [? ?].
  unfold prop.
  destruct H as [?w [?w [? [? _]]]].
  destruct H0 as [?w [?w [? [? _]]]].
  apply env_mapsto_get in H1; destruct H1.
  apply env_mapsto_get in H2; destruct H2.
  destruct (env_get_join_sub _ _ _ _ _ (join_join_sub H) H1) as [sh' [? ?]].
  destruct (env_get_join_sub _ _ _ _ _ (join_join_sub H0) H2) as [sh'' [? ?]].
  congruence.
Qed.

Lemma env_mapsto_precise{key: Type}{A: Type}{KE: EqDec key}: forall id sh (v:A), precise (env_mapsto id sh v).
Proof.
  intros; intro; intros.
  apply env_ext.
  extensionality id'.
  destruct (eq_dec id id'); auto; subst.
    apply env_mapsto_get in H; destruct H.
    apply env_mapsto_get in H0; destruct H0.
    rewrite H; rewrite H0.
    repeat f_equal; auto. apply proof_irr.

    eapply env_mapsto_get_neq in H; eauto.
    eapply env_mapsto_get_neq in H0; eauto.
    rewrite H; rewrite H0; auto.
Qed.

Definition own_var {key: Type}{A: Type}{KE: EqDec key} (sh: pshare) (id: key) : pred (env key A) :=
  exp (env_mapsto id (pshare_sh sh)).

Definition see_var {key: Type}{A: Type}{KE: EqDec key} (id: key) : pred (env key A) :=
  exp (fun sh: pshare => own_var sh id).

Definition own_all {key: Type}{A: Type}{KE: EqDec key} (l: list key) : pred (env key A) :=
   list_sepcon (map (own_var pfullshare) l).

Lemma own_all_nil {key: Type}{A: Type}{KE: EqDec key} : own_all nil = (emp: pred (env key A)).
Proof. unfold own_all; simpl; auto. Qed.

Opaque env_mapsto.
End EnvSL.



Definition restrict_env' {key: Type}{A: Type}{KE: EqDec key} (ids: list key) (rho: env key A) (id: key) : option (pshare * A) :=
  if  In_dec eq_dec id ids
                      then env_get rho id
                      else None.

Lemma restrict_env'_finite {key: Type}{A: Type}{KE: EqDec key} : forall ids (rho: env key A), finite_idfun (restrict_env' ids rho).
Proof.
unfold finite_idfun, restrict_env'; intros.
exists ids.
intros.
destruct (in_dec eq_dec a ids); try contradiction; auto.
Qed.

Definition restrict_env {key: Type}{A: Type}{KE: EqDec key} (ids: list key) (rho:env key A) : env key A :=
  mk_env _ (restrict_env'_finite ids rho).

Definition restrict_env_comp' {key: Type}{A: Type}{KE: EqDec key} (ids: list key) (rho: env key A) (id: key) : option (pshare * A) :=
  if  In_dec eq_dec id ids
                      then None
                      else env_get rho id.

Lemma restrict_env_comp'_finite {key: Type}{A: Type}{KE: EqDec key}:
    forall ids (rho: env key A), finite_idfun (restrict_env_comp' ids rho).
Proof.
unfold finite_idfun, restrict_env_comp'; intros.
destruct (env_finite rho) as [l ?].
exists l.
intros.
destruct (in_dec eq_dec a ids); try contradiction; auto.
Qed.

Definition restrict_env_comp  {key: Type}{A: Type}{KE: EqDec key} (ids: list key) (rho:env key A) : env key A:=
  mk_env _ (restrict_env_comp'_finite ids rho).

Lemma restrict_env_nil  {key: Type}{A: Type}{KE: EqDec key}:
  forall ge, restrict_env nil ge = (empty_env: env key A).
Proof.
intros.
apply env_ext. extensionality id.
unfold restrict_env; rewrite env_get_mk_env; unfold restrict_env'; simpl.
rewrite env_get_empty.
auto.
Qed.

Lemma restrict_env_app  {key: Type}{A: Type}{KE: EqDec key} :
  forall ids1 ids2 (rho: env key A),  list_disjoint ids1 ids2 ->
    join (restrict_env ids1 rho) (restrict_env ids2 rho) (restrict_env (ids1++ids2) rho).
Proof.
intros.
intro id.
unfold restrict_env; simpl.
repeat rewrite env_get_mk_env.
unfold restrict_env'.
unfold list_disjoint in H.
specialize ( H id id).
destruct (in_dec eq_dec id ids1).
destruct (in_dec eq_dec id ids2).
contradiction H; auto.
destruct (in_dec eq_dec id (ids1++ids2)).
constructor.
contradiction n0;
rewrite in_app; auto.
destruct (in_dec eq_dec id ids2).
destruct (in_dec eq_dec id (ids1++ids2)).
constructor.
contradiction n0;
rewrite in_app; auto.
destruct (in_dec eq_dec id (ids1++ids2)).
rewrite in_app in i; intuition.
constructor.
Qed.

Lemma restrict_env_comp_join {key: Type}{A: Type}{KE: EqDec key}:
  forall ids (ge: env key A), join (restrict_env ids ge) (restrict_env_comp ids ge) ge.
Proof.
intros.
intro id.
unfold restrict_env, restrict_env_comp.
repeat rewrite env_get_mk_env.
unfold restrict_env', restrict_env_comp'.
destruct (in_dec eq_dec id ids); constructor.
Qed.

Lemma restrict_env_rev {key: Type}{A: Type}{KE: EqDec key}:
    forall ids, @restrict_env key A _ (rev ids) = restrict_env ids.
Proof.
intros.
extensionality w.
unfold restrict_env.
apply env_ext; extensionality id.
repeat rewrite env_get_mk_env.
unfold restrict_env'.
destruct (in_dec eq_dec id (rev ids));
destruct (in_dec eq_dec id ids); auto.
rewrite <- In_rev in i; contradiction.
rewrite In_rev in i; contradiction.
Qed.


Instance Trip_pshareval {B} : @Trip_alg (option (pshare * B)) (Join_lower (Join_prod _ _ _ (Join_equiv B))).
Proof.
intro; intros.
apply pshareval_join_e in H.
apply pshareval_join_e in H0.
apply pshareval_join_e in H1.
destruct a as [[[sa pa] va]|];
destruct b as [[[sb pb] vb]|];
destruct ab as [[[sab pab] vab]|]; try solve [elimtype False; inv H];
destruct c as [[[sc pc] vc]|];
destruct bc as [[[sbc pbc] vbc]|]; try solve [elimtype False; inv H0];
destruct ac as [[[sac pac] vac]|]; try solve [elimtype False; inv H1];
simpl in *;
try (assert (Hx: join sa sb sab /\ va = vb /\ vb = vab)
     by (inv H; simpl in *; intuition;
            match goal with H: @join B _ _ _ _ |- _ => destruct H end;
             congruence);
    decompose [and] Hx; clear H Hx; subst vab);
try (assert (Hx: join sb sc sbc /\ vb = vc /\ vb = vbc)
    by (inv H0; simpl in *; intuition;
            match goal with H: @join B _ _ _ _ |- _ => destruct H end;
             congruence);
    decompose [and] Hx; clear H0 Hx; subst vbc);
try (assert (Hx: join sa sc sac /\ va = vc /\ va = vac)
    by (inv H1; simpl in *; intuition;
            match goal with H: @join B _ _ _ _ |- _ => destruct H end;
             congruence);
    decompose [and] Hx; clear H1 Hx; subst vac);
subst; subst;
try solve [econstructor; constructor].
destruct (triple_join_exists_share _ _ _ _ _ _ H2 H H0) as [sabc ?].
assert (nonidentity sabc). eapply join_nonidentity. apply nonunit_nonidentity; apply pab. eauto.
exists (Some (mk_lifted _ (nonidentity_nonunit H1), vc)).
constructor; split; simpl; auto.
exists (Some (mk_lifted _ pac, vbc)); econstructor; simpl; auto.
inv H0. inv H. constructor; auto.
exists (Some (mk_lifted _ pbc, vac)); inv H1; inv H; constructor; simpl; auto.
constructor; auto.
Qed.

Instance Trip_env {A} {EA: EqDec A} {B} {JB: Join B}: Trip_alg (env A B).
Proof.
intro; intros.
pose (f id := Trip_pshareval _ _ _ _ _ _ (H id) (H0 id) (H1 id)).
assert (finite_idfun (fun id => proj1_sig (f id))).
destruct (env_finite ab) as [l1 H3].
destruct (env_finite c) as [l2 H4].
exists (l1++l2).
intro id; specialize ( H3 id); specialize ( H4 id).
intro.
assert (~ (In id l1 \/ In id l2)).
contradict H2.
rewrite in_app. auto.
clear H2.
destruct (In_dec eq_dec id l1) as [H5' | H5'].
contradiction H5; auto.
assert (H6: ~In id l2) by intuition.
destruct (f id).
simpl.
apply pshareval_join_e in j.
rewrite H3 in j; rewrite H4 in j; inv j; auto.
exists (mk_env (fun id => proj1_sig (f id)) H2).
intro id.
rewrite env_get_mk_env.
destruct (f id); simpl.
auto.
Qed.
