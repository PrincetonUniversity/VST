(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

(** This library defines boolean algebras defined from an order-theoretic
    perspective.  In short, a boolean algebra is a complemented distributive
    lattice.  We additionally require that the boolean algebra be non-trivial.

    From this definition we can recover the axioms of boolean algebras as
    defined in allp algebra.

    We also define module interfaces for boolean algebras with a splitting
    operator, with a relativization operator, and those which support
    token counting.

    We then say that a share model is a boolean algebra which satisfies
    all three module interfaces.  We also require that the elements
    have a decidable equality.
*)

Require Import VST.msl.base.
Require Import VST.msl.eq_dec.
Require Import VST.msl.sepalg.
Require Import GenericMinMax.

Module Type BOOLEAN_ALGEBRA.
  Parameters (t:Type) (Ord : t -> t -> Prop)
     (top bot : t) (lub glb : t -> t -> t) (comp : t -> t).

  Delimit Scope ba with ba. Open Scope ba.
  Notation "x <= y" := (Ord x y) (at level 70, no associativity) : ba.

  Axiom ord_refl : forall x, x <= x.
  Axiom ord_trans : forall x y z, x <= y -> y <= z -> x <= z.
  Axiom ord_antisym : forall x y, x <= y -> y <= x -> x = y.

  Axiom lub_upper1 : forall x y, x <= (lub x y).
  Axiom lub_upper2 : forall x y, y <= (lub x y).
  Axiom lub_least : forall x y z, x <= z -> y <= z -> (lub x y) <= z.

  Axiom glb_lower1 : forall x y, (glb x y) <= x.
  Axiom glb_lower2 : forall x y, (glb x y) <= y.
  Axiom glb_greatest : forall x y z, z <= x -> z <= y -> z <= (glb x y).

  Axiom top_correct : forall x, x <= top.
  Axiom bot_correct : forall x, bot <= x.

  Axiom distrib1 : forall x y z, glb x (lub y z) = lub (glb x y) (glb x z).

  Axiom comp1 : forall x, lub x (comp x) = top.
  Axiom comp2 : forall x, glb x (comp x) = bot.

  Axiom nontrivial : top <> bot.

  Hint Resolve ord_refl ord_antisym lub_upper1 lub_upper2 lub_least
         glb_lower1 glb_lower2 glb_greatest top_correct bot_correct
         ord_trans : ba.
End BOOLEAN_ALGEBRA.

Module Type BA_FACTS.
  Include BOOLEAN_ALGEBRA.

  Axiom ord_spec1 : forall x y, x <= y <-> x = glb x y.
  Axiom ord_spec2 : forall x y, x <= y <-> lub x y = y.

  Axiom lub_idem : forall x, (lub x x) = x.
  Axiom lub_commute : forall x y, lub x y = lub y x.
  Axiom lub_bot : forall x, lub x bot = x.
  Axiom lub_top : forall x, lub x top = top.
  Axiom lub_absorb : forall x y, lub x (glb x y) = x.
  Axiom lub_assoc : forall x y z, lub (lub x y) z = lub x (lub y z).

  Axiom glb_idem : forall x, glb x x = x.
  Axiom glb_commute : forall x y, glb x y = glb y x.
  Axiom glb_bot : forall x, glb x bot = bot.
  Axiom glb_top : forall x, glb x top = x.
  Axiom glb_absorb : forall x y, glb x (lub x y) = x.
  Axiom glb_assoc : forall x y z, glb (glb x y) z = glb x (glb y z).

  Axiom distrib2 : forall x y z, lub x (glb y z) = glb (lub x y) (lub x z).

  Axiom distrib_spec : forall x y1 y2,
    lub x y1 = lub x y2 ->
    glb x y1 = glb x y2 ->
    y1 = y2.

  Axiom demorgan1 : forall x y, comp (lub x y) = glb (comp x) (comp y).
  Axiom demorgan2 : forall x y, comp (glb x y) = lub (comp x) (comp y).
  Axiom comp_inv : forall x, comp (comp x) = x.

  Instance Join_ba: Join t := fun x y z : t => glb x y = bot /\ lub x y = z.

  Axiom pa: Perm_alg t.   Existing Instance pa.
  Axiom sa : Sep_alg t.   Existing Instance sa.
  Axiom ca : Canc_alg t. Existing Instance ca.
  Axiom singa : Sing_alg t.   Existing Instance singa.
  Axiom da : Disj_alg t.   Existing Instance da.
End BA_FACTS.

(* BEGIN NEW MATERIAL *)

Class heightable (A : Type) : Type := Heightable {
  height : A -> nat;
  is_height_zero : forall a : A, {height a = 0} + {height a <> 0} (* Should run in O(1) time for trees *)
 }.
Arguments Heightable [A] _ _.
Definition is_height_zero_spec {A : Type} (height : A -> nat) : Type :=
  forall a : A, {height a = 0} + {height a <> 0}.

Definition list_height {A} `{heightable A} (LA : list A) : nat :=
  fold_right max 0 (map height LA).
Fixpoint list_is_height_zero_bool {A} `{heightable A} (L : list A) : bool :=
  match L with
   | nil => true
   | a :: L' =>
      if is_height_zero a then list_is_height_zero_bool L' else false
  end.
Instance list_heightable {A} `{heightable A} : heightable (list A).
  apply Heightable with list_height.
  induction a. left. trivial.
  unfold list_height in *.
  case (is_height_zero a). destruct IHa. left.
  simpl. rewrite e, e0. trivial.
  right. intro. apply n. simpl in H0. rewrite e in H0. apply H0.
  right. intro. apply n. simpl in H0. icase (height a). icase (fold_right max 0 (map height a0)).
Defined.

 Class decomposible (A : Type) : Type := Decomposible {
  decompose : A -> (A * A)
 }.
 Arguments Decomposible [A] _.

 Class roundableLeft (A : Type) : Type := RoundableLeft {
   roundL : nat -> A -> option A
 }.
 Arguments RoundableLeft [A] _.

 Class roundableRight (A : Type) : Type := RoundableRight {
   roundR : nat -> A -> option A
 }.
 Arguments RoundableRight [A] _.

 Class avgable (A : Type) : Type := Avgable {
    avg : nat -> A -> A -> option A
 }.
 Arguments Avgable [A] _.

(* END NEW MATERIAL *)

Module Type SHARE_MODEL.
  Include BA_FACTS.

  Parameter EqDec_share: EqDec t.
  Existing Instance EqDec_share.

  (* Splittability *)
  Parameter split : t -> t * t.

  Axiom split_disjoint : forall x1 x2 x,
    split x = (x1, x2) ->
    glb x1 x2 = bot.

  Axiom split_together : forall x1 x2 x,
    split x = (x1, x2) ->
    lub x1 x2 = x.

  Axiom split_nontrivial : forall x1 x2 x,
    split x = (x1, x2) ->
    (x1 = bot \/ x2 = bot) ->
    x = bot.

  (* Token factories *)
  Parameter isTokenFactory : t -> nat -> Prop.
  Parameter isToken : t -> nat -> Prop.

  Parameter create_token : nat -> t -> (t*t).

  Axiom create_token_correct : forall fac fac' tok x n,
    create_token n fac = (fac',tok) ->
    isTokenFactory fac x ->
      isTokenFactory fac' (n+x) /\
      isToken tok n /\
      join fac' tok fac.

  Axiom absorbToken : forall fac fac' tok x n,
    isTokenFactory fac' (n+x) ->
    isToken tok n ->
    join fac' tok fac ->
    isTokenFactory fac x.

  Axiom mergeToken : forall tok1 n1 tok2 n2 tok',
    isToken tok1 n1 ->
    isToken tok2 n2 ->
    join tok1 tok2 tok' ->
    isToken tok' (n1+n2).

  Parameter split_token : nat -> t -> t*t.

  Axiom split_token_correct : forall n1 n2 tok tok1 tok2,
    isToken tok (n1+n2) ->
    split_token n1 tok = (tok1,tok2) ->
      isToken tok1 n1 /\
      isToken tok2 n2 /\
      join tok1 tok2 tok.

  Axiom factoryOverlap : forall f1 f2 n1 n2,
    isTokenFactory f1 n1 -> isTokenFactory f2 n2 -> glb f1 f2 <> bot.

  Axiom fullFactory : forall x, isTokenFactory x 0 <-> x = top.
  Axiom identityToken : forall x, isToken x 0 <-> x = bot.

  Axiom nonidentityToken : forall x n, (n > 0)%nat -> isToken x n -> x <> bot.
  Axiom nonidentityFactory : forall x n, isTokenFactory x n -> x <> bot.


  (* relativization *)
  Parameter rel : t -> t -> t.

  Axiom rel_inj_l : forall a x y, a <> bot -> rel a x = rel a y -> x = y.
  Axiom rel_inj_r : forall a b x, x <> bot -> rel a x = rel b x -> a = b.

  Axiom rel_assoc : forall x y z, rel x (rel y z) = rel (rel x y) z.

  Axiom rel_preserves_glb : forall a x y, rel a (glb x y) = glb (rel a x) (rel a y).
  Axiom rel_preserves_lub : forall a x y, rel a (lub x y) = lub (rel a x) (rel a y).

  Axiom rel_bot1 : forall a, rel a bot = bot.
  Axiom rel_bot2 : forall x, rel bot x = bot.
  Axiom rel_top1 : forall a, rel a top = a.
  Axiom rel_top2 : forall x, rel top x = x.

  Parameter unrel: t -> t -> t.
  Definition Lsh  : t := fst (split top).
  Definition Rsh  : t := snd (split top).
  Definition splice (a b: t) : t := lub (rel Lsh a) (rel Rsh b).

  Axiom unrel_rel: forall x sh, nonidentity x -> unrel x (rel x sh) = sh.
  Axiom unrel_splice_L: forall a b, unrel Lsh (splice a b) = a.
  Axiom unrel_splice_R: forall a b, unrel Rsh (splice a b) = b.
  Axiom contains_Lsh_e: forall sh, join_sub Lsh sh -> unrel Lsh sh = top.
  Axiom contains_Rsh_e: forall sh, join_sub Rsh sh -> unrel Rsh sh = top.
  Axiom unrel_disjoint: forall a a', a <> bot -> glb a a' = bot -> unrel a a' = bot.
  Axiom unrel_lub: forall a b1 b2, unrel a (lub b1 b2) = lub (unrel a b1) (unrel a b2).
  Axiom unrel_glb: forall a b1 b2, unrel a (glb b1 b2) = glb (unrel a b1) (unrel a b2).
  Axiom unrel_join: forall x a b c, join a b c -> join (unrel x a) (unrel x b) (unrel x c).
  Axiom unrel_top: forall a, unrel a top = top.
  Axiom unrel_bot: forall a, unrel a bot = bot.
  Axiom top_unrel: forall a, unrel top a = a.
  Axiom bot_unrel: forall a, unrel bot a = a.

(* BEGIN NEW MATERIAL *)
 (*D1*)
 Parameter tree_height : t -> nat.
 Parameter tree_height_zero : forall t, {tree_height t = 0} + {tree_height t <> 0}.
 Instance tree_heightable : heightable t :=
   Heightable tree_height tree_height_zero.
 (*D2*)
 Parameter tree_round_left : nat -> t -> option t.
 Instance  roundableL_tree : roundableLeft t :=
   RoundableLeft tree_round_left.
 (*D3*)
 Parameter tree_round_right : nat -> t -> option t.
 Instance  roundableR_tree : roundableRight t :=
   RoundableRight tree_round_right.
 (*D4*)
 Parameter tree_avg : nat -> t -> t -> option t.
 Instance avgable_tree : avgable t :=
    Avgable tree_avg.
 (*D5*)
 Parameter countBLeafCT : nat -> t -> nat.
 (*D6*)
 Parameter share_metric : nat -> t -> nat.
 (*D7*)
 Parameter tree_decompose : t -> (t * t).
 Instance decompose_tree : decomposible t :=
   Decomposible tree_decompose.
 (*D8*)
 Parameter recompose : (t * t) -> t.
 (*D9*)
 Parameter power : nat -> nat -> nat.
 (*D10*)
 Parameter add : t -> t -> option t.
 (*D11*)
 Parameter sub : t -> t -> option t.
 (*L0*)
 Axiom leq_dec : forall (x y : t), {x <= y} + {~ (x <= y)}.
 (*L1*)
 Axiom height_top : height top = 0.
 (*L2*)
 Axiom height_bot : height bot = 0.
 (*L3*)
 Axiom height_zero_eq: forall t, height t = 0 -> {t = top} + {t = bot}.
 (*L4*)
 Axiom decompose_height : forall n t1 t2 t3,
                          height t1 = S n ->
                          decompose t1 = (t2, t3) ->
                          (height t2 <= n)%nat /\ (height t3 <= n)%nat.
 (*L5*)
 Axiom decompose_recompose: forall t,
    decompose (recompose t) = t.
 (*L6*)
 Axiom recompose_decompose: forall t,
    recompose (decompose t) = t.
 (*L7*)
 Axiom decompose_join: forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
    decompose t1 = (t11, t12) ->
    decompose t2 = (t21, t22) ->
    decompose t3 = (t31, t32) ->
    (join t1 t2 t3 <->
    (join t11 t21 t31 /\ join t12 t22 t32)).
 Axiom decompose_glb: forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
  decompose t1 = (t11,t12) ->
  decompose t2 = (t21,t22) ->
  decompose t3 = (t31,t32) ->
  (glb t1 t2 = t3 <-> (glb t11 t21 = t31 /\ glb t12 t22 = t32)).
 Axiom decompose_lub: forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
  decompose t1 = (t11,t12) ->
  decompose t2 = (t21,t22) ->
  decompose t3 = (t31,t32) ->
  (lub t1 t2 = t3 <-> (lub t11 t21 = t31 /\ lub t12 t22 = t32)).
 (*L8*)
 Axiom add_join : forall t1 t2 t3,
    add t1 t2 = Some t3 <-> join t1 t2 t3.
 (*L9*)
 Axiom sub_join : forall t1 t2 t3,
    sub t1 t2 = Some t3 <-> join t2 t3 t1.
 (*L10*)
 Axiom decompose_share_height_no_increase: forall sh sh' sh'' ,
   decompose sh = (sh',sh'')->
   (height sh' <= height sh /\ height sh'' <= height sh)%nat.
 (*This one looks like L4
 Axiom decompose_share_height_decrease : forall sh sh' sh'' n,
   decompose sh = (sh',sh'') ->
   height sh = S n ->
   (height sh' <= n /\ height sh'' <= n)%nat.
 *)
 (*L11*)
 Axiom decompose_height_le: forall n s s1 s2,
  decompose s = (s1,s2) ->
  (height s <= S n)%nat ->
  (height s1 <= n)%nat /\ (height s2 <= n)%nat.
 (*L12*)
 Axiom decompose_le: forall s1 s2 s11 s12 s21 s22,
  s1 <= s2 ->
  decompose s1 = (s11,s12) ->
  decompose s2 = (s21,s22) ->
  s11 <= s21 /\ s12 <= s22.
 (*L13*)
 Axiom decompose_diff: forall s1 s2 s11 s12 s21 s22,
  s1 <> s2 ->
  decompose s1 = (s11,s12) ->
  decompose s2 = (s21,s22) ->
  s11 <> s21 \/ s12 <> s22.
 (*L14*)
 Axiom tree_round_left_join : forall n t1 t2 t3 t1' t2' t3',
    join t1 t2 t3 ->
    roundL n t1 = Some t1' ->
    roundL n t2 = Some t2' ->
    roundL n t3 = Some t3' ->
    join t1' t2' t3'.
 (*L15*)
 Axiom tree_round_left_identity : forall n t,
    height t < n ->
    roundL n t = Some t.
 (*L16*)
 Axiom tree_round_left_None : forall n t,
    n < height t ->
    roundL n t = None.
 (*L17*)
 Axiom tree_round_left_decrease : forall n t,
    S n = height t ->
    exists t', roundL (S n) t = Some t' /\ (height t' <= n)%nat.
 (*L18*)
 Axiom tree_round_left_Some : forall n t,
    (height t <= S n)%nat ->
    exists t', roundL (S n) t = Some t'.
 (*L19*)
 Axiom tree_round_left_height_compare : forall t t' n,
    roundL n t = Some t' ->
    (height t' < n)%nat.
 (*L20*)
  Axiom tree_round_left_zero: forall t,
    roundL 0 t = None.
 (*L21*)
 Axiom tree_round_right_join : forall n t1 t2 t3 t1' t2' t3',
    join t1 t2 t3 ->
    roundR n t1 = Some t1' ->
    roundR n t2 = Some t2' ->
    roundR n t3 = Some t3' ->
    join t1' t2' t3'.
 (*L22*)
 Axiom tree_round_right_identity : forall n t,
    height t < n ->
    roundR n t = Some t.
 (*L23*)
 Axiom tree_round_right_None : forall n t,
    n < height t ->
    roundR n t = None.
 (*L24*)
 Axiom tree_round_right_decrease : forall n t,
    S n = height t ->
    exists t', roundR (S n) t = Some t' /\ (height t' <= n)%nat.
 (*L25*)
 Axiom tree_round_right_Some : forall n t,
    (height t <= S n)%nat ->
    exists t', roundR (S n) t = Some t'.
 (*L26*)
 Axiom tree_round_right_height_compare : forall t t' n,
    roundR n t = Some t' ->
    (height t' < n)%nat.
 (*L27*)
  Axiom tree_round_right_zero: forall t,
    roundR 0 t = None.

  (*L29*)
  Axiom tree_avg_identity (* before: avg_share_Iden *): forall n t,
   height t < n ->
   avg n t t = Some t.
  (*L30*)
  Axiom tree_avg_None : forall n t1 t2,
   (n <= max (height t1) (height t2))%nat ->
   avg n t1 t2 = None.
  (*L31*)
    Axiom tree_avg_round2avg : forall n t1 t2 t3,
   roundL n t3 = Some t1 ->
   roundR n t3 = Some t2 ->
   avg n t1 t2 = Some t3.
  (*L32*)
  Axiom tree_avg_avg2round : forall n t1 t2 t3,
   avg n t1 t2 = Some t3 ->
   roundL n t3 = Some t1 /\
   roundR n t3 = Some t2.
  (*L33*)
  Axiom tree_avg_join : forall n t11 t12 t13 t21 t22 t23 t31 t32 t33,
   avg n t11 t12 =  Some t13 ->
   avg n t21 t22 = Some t23 ->
   avg n t31 t32 = Some t33 ->
   join t11 t21 t31 ->
   join t12 t22 t32 ->
   join t13 t23 t33.
  (*L34*)
  Axiom tree_avg_ex: forall n t1 t2,
   height t1 < n ->
   height t2 < n ->
   exists t3, avg n t1 t2 = Some t3.
  (*L35*)
  Axiom avg_share_correct: forall n s,
   (height s <= S n)%nat ->
   exists s', exists s'',
    roundL (S n) s = Some s' /\
    roundR (S n) s = Some s'' /\
    avg (S n) s' s'' = Some s.

 (*L36*)
 Axiom countBLeafCT_decompose : forall n s s1 s2,
  decompose s = (s1,s2) ->
  countBLeafCT (S n) s = countBLeafCT n s1 + countBLeafCT n s2.
 (*L37*)
 Axiom countBLeafCT_le : forall n s1 s2,
  s1 <= s2 -> (countBLeafCT n s1 <= countBLeafCT n s2)%nat.
 (*L38*)
 Axiom countBLeafCT_lt : forall n s1 s2,
  s1 <= s2 ->
  s1 <> s2 ->
  (height s2 <= n)%nat ->
  countBLeafCT n s1 < countBLeafCT n s2.
 (*L39*)
 Axiom countBLeafCT_limit: forall n s, (countBLeafCT n s <= power 2 n)%nat.
 (*L40*)
 Axiom countBLeafCT_bot: forall n, countBLeafCT n bot = 0.
 (*L41*)
 Axiom countBLeafCT_top: forall n, countBLeafCT n top = power 2 n.
 (*L42*)
 Axiom countBLeafCT_positive : forall s n,
   (height s <= n)%nat ->
   bot <> s -> 0 < countBLeafCT n s.
 (*L43*)
 Axiom countBLeafCT_mono_le: forall n1 n2 s,
  (n1 <= n2)%nat ->
  (countBLeafCT n1 s <= countBLeafCT n2 s)%nat .
 (*L44*)
 Axiom countBLeafCT_mono_diff: forall n1 n2 s1 s2,
  (n1 <= n2)%nat ->
   s1 <= s2 ->
  (countBLeafCT n1 s2 - countBLeafCT n1 s1 <= countBLeafCT n2 s2 - countBLeafCT n2 s1)%nat.
 (*L45*)
 Axiom countBLeafCT_mono_lt: forall n1 n2 s,
  n1 < n2 ->
  0 < countBLeafCT n1 s ->
  countBLeafCT n1 s < countBLeafCT n2 s .
 (*L46*)
 Axiom countBLeafCT_join_le: forall n s1 s2 s3,
  join s1 s2 s3 ->
  (countBLeafCT n s1 + countBLeafCT n s2 <= countBLeafCT n s3)%nat.
 (*L47*)
 Axiom countBLeafCT_join_eq: forall n s1 s2 s3,
  join s1 s2 s3 ->
  (height s1 <= n)%nat ->
  (height s2 <= n)%nat ->
  countBLeafCT n s1 + countBLeafCT n s2 = countBLeafCT n s3.
 (*L48*)
 Axiom share_metric_nerr : forall s n,
  height s < n ->
  0 < share_metric n s.
 (*L49*)
 Axiom share_metric_err  : forall s n,
  (n <= height s)%nat ->
  share_metric n s = 0.
 (*L50*)
 Axiom share_metric_height_monotonic : forall s n1 n2,
  (n1 <= n2)%nat ->
  (share_metric n1 s <= share_metric n2 s)%nat.
 (*L51*)
 Axiom share_metric_lub : forall s s' n,
  ~(s'<=s) ->
  0 < share_metric n s ->
  0 < share_metric n (lub s s') ->
  share_metric n s < share_metric n (lub s s').
 (*L52*)
 Axiom share_metric_glb : forall s s' n,
  ~(s<=s') ->
  0 < share_metric n s ->
  0 < share_metric n (glb s s') ->
  share_metric n (glb s s') < share_metric n s.
 (*L53*)
 Axiom share_metric_dif_monotonic: forall s1 s2 n n0,
  s1<=s2 ->
  (n<=n0)%nat ->
  height s1 < n -> height s2 < n ->
  (share_metric n s2 - share_metric n s1 <=
  share_metric n0 s2 - share_metric n0 s1)%nat.

 (*L54*)
 Axiom tree_height_lub_limit: forall n s1 s2,
  (height s1 <= n)%nat ->
  (height s2 <= n)%nat ->
  (height (lub s1 s2) <= n)%nat.
 (*L55*)
 Axiom tree_height_glb_limit: forall n s1 s2,
  (height s1 <= n)%nat ->
  (height s2 <= n)%nat ->
  (height (glb s1 s2) <= n)%nat.
 (*L56*)
 Axiom height_lub1 : forall s1 s2,
  (height s1<= height s2)%nat->
  (height (lub s1 s2) <= height s2)%nat.
 (*L57*)
 Axiom height_glb1 : forall s1 s2,
  (height s1<= height s2)%nat->
  (height (glb s1 s2) <= height s2)%nat.
 (*L58*)
 Axiom height_comp: forall s,
  height (comp s)= height s.

 Axiom decompose_height_zero: forall s sL sR,
  decompose s = (sL,sR) ->
  height s = 0 ->
  sL = s /\ sR = s.

 Axiom decompose_equal: forall a b aL aR bL bR,
  decompose a = (aL,aR) ->
  decompose b = (bL,bR) ->
  (a = b <-> aL = bL /\ aR = bR).

 Axiom decompose_nonzero: forall sL sR s,
 decompose s = (sL,sR) ->
 (s <> bot <-> sL <> bot \/ sR <> bot).

 Axiom tree_avg_equal: forall sL sR sL' sR' s n,
  avg n sL sR = Some s ->
  avg n sL' sR' = Some s ->
  sL = sL' /\ sR = sR'.

 Axiom tree_avg_zero: forall sL sR s n,
  avg n sL sR = Some s ->
  (s = bot <-> sL = bot /\ sR = bot).

 Axiom tree_avg_nonzero: forall sL sR s n,
  avg n sL sR = Some s ->
  (s <> bot <-> sL <> bot \/ sR <> bot).

 Axiom tree_avg_bound: forall sL sR s n,
  avg n sL sR = Some s -> (height s <= n)%nat.

 Axiom Lsh_recompose: Lsh = recompose (top, bot).
 Axiom Rsh_recompose: Rsh = recompose (bot,top).
 Axiom decompose_Rsh: forall sh, unrel Rsh sh = snd (decompose sh).
 Axiom decompose_Lsh: forall sh, unrel Lsh sh = fst (decompose sh).
 Axiom rel_Lsh: forall sh, rel Lsh sh = recompose (sh,bot).
 Axiom rel_Rsh: forall sh, rel Rsh sh = recompose (bot,sh).
 Axiom lub_rel_recompose: forall sh1 sh2,
             lub (rel Lsh sh1) (rel Rsh sh2) = recompose (sh1,sh2).

 (* END NEW MATERIAL *)



End SHARE_MODEL.


Module BA_Facts (BA:BOOLEAN_ALGEBRA) <: BA_FACTS.
  Include BA.

  Lemma ord_spec1 : forall x y, x <= y <-> x = glb x y.
  Proof.
    split; intros.
    auto with ba.
    rewrite H; auto with ba.
  Qed.

  Lemma ord_spec2 : forall x y, x <= y <-> lub x y = y.
  Proof.
    intros; split; intros.
    auto with ba.
    rewrite <- H; auto with ba.
  Qed.

  Lemma lub_idem : forall x, lub x x = x.
  Proof. auto with ba. Qed.

  Lemma glb_idem : forall x, glb x x = x.
  Proof. auto with ba. Qed.

  Lemma lub_commute : forall x y, lub x y = lub y x.
  Proof. auto with ba. Qed.

  Lemma glb_commute : forall x y, glb x y = glb y x.
  Proof. auto with ba. Qed.

  Lemma lub_absorb : forall x y, lub x (glb x y) = x.
  Proof. auto with ba. Qed.

  Lemma glb_absorb : forall x y, glb x (lub x y) = x.
  Proof. auto with ba. Qed.

  Lemma lub_assoc : forall x y z, lub (lub x y) z = lub x (lub y z).
  Proof.
    intros; apply ord_antisym; eauto with ba.
  Qed.

  Lemma glb_assoc : forall x y z, glb (glb x y) z = glb x  (glb y z).
  Proof.
    intros; apply ord_antisym; eauto with ba.
  Qed.

  Lemma glb_bot : forall x, glb x bot = bot.
  Proof. auto with ba. Qed.

  Lemma lub_top : forall x, lub x top = top.
  Proof. auto with ba. Qed.

  Lemma lub_bot : forall x, lub x bot = x.
  Proof. auto with ba. Qed.

  Lemma glb_top : forall x, glb x top = x.
  Proof. auto with ba. Qed.

  Lemma distrib2 : forall x y z,
    lub x (glb y z) = glb (lub x y) (lub x z).
  Proof.
    intros.
    apply ord_antisym.
    apply lub_least.
    rewrite distrib1.
    rewrite glb_commute.
    rewrite glb_absorb.
    apply lub_upper1.
    apply glb_greatest.
    apply ord_trans with y.
    apply glb_lower1.
    apply lub_upper2.
    apply ord_trans with z.
    apply glb_lower2.
    apply lub_upper2.
    rewrite distrib1.
    apply lub_least.
    rewrite glb_commute.
    rewrite glb_absorb.
    apply lub_upper1.
    rewrite glb_commute.
    rewrite distrib1.
    apply lub_least.
    apply ord_trans with x.
    apply glb_lower2.
    apply lub_upper1.
    rewrite glb_commute.
    apply lub_upper2.
  Qed.

  Lemma distrib_spec : forall x y1 y2,
    lub x y1 = lub x y2 ->
    glb x y1 = glb x y2 ->
    y1 = y2.
  Proof.
    intros.
    rewrite <- (lub_absorb y2 x).
    rewrite glb_commute.
    rewrite <- H0.
    rewrite distrib2.
    rewrite lub_commute.
    rewrite <- H.
    rewrite (lub_commute x y1).
    rewrite (lub_commute y2 y1).
    rewrite <- distrib2.
    rewrite <- H0.
    rewrite glb_commute.
    rewrite lub_absorb.
    auto.
  Qed.

  Lemma comp_inv : forall x, comp (comp x) = x.
  Proof.
    intro x.
    apply distrib_spec with (comp x).
    rewrite comp1.
    rewrite lub_commute.
    rewrite comp1.
    auto.
    rewrite comp2.
    rewrite glb_commute.
    rewrite comp2.
    auto.
  Qed.

  Lemma demorgan1 : forall x y, comp (lub x y) = glb (comp x) (comp y).
  Proof.
    intros x y.
    apply distrib_spec with (lub x y).
    rewrite comp1.
    rewrite distrib2.
    rewrite (lub_assoc x y (comp y)).
    rewrite comp1.
    rewrite lub_top.
    rewrite glb_top.
    rewrite (lub_commute x y).
    rewrite lub_assoc.
    rewrite comp1.
    rewrite lub_top.
    auto.
    rewrite comp2.
    rewrite glb_commute.
    rewrite distrib1.
    rewrite (glb_commute (comp x) (comp y)).
    rewrite glb_assoc.
    rewrite (glb_commute (comp x) x).
    rewrite comp2.
    rewrite glb_bot.
    rewrite lub_commute.
    rewrite lub_bot.
    rewrite (glb_commute (comp y) (comp x)).
    rewrite glb_assoc.
    rewrite (glb_commute (comp y) y).
    rewrite comp2.
    rewrite glb_bot.
    auto.
  Qed.

  Lemma demorgan2 : forall x y, comp (glb x y) = lub (comp x) (comp y).
  Proof.
    intros x y.
    apply distrib_spec with (glb x y).
    rewrite comp1.
    rewrite lub_commute.
    rewrite distrib2.
    rewrite (lub_commute (comp x) (comp y)).
    rewrite lub_assoc.
    rewrite (lub_commute (comp x) x).
    rewrite comp1.
    rewrite lub_top.
    rewrite glb_commute.
    rewrite glb_top.
    rewrite (lub_commute (comp y) (comp x)).
    rewrite lub_assoc.
    rewrite (lub_commute (comp y) y).
    rewrite comp1.
    rewrite lub_top.
    auto.
    rewrite comp2.
    rewrite distrib1.
    rewrite (glb_commute x y).
    rewrite glb_assoc.
    rewrite comp2.
    rewrite glb_bot.
    rewrite lub_commute.
    rewrite lub_bot.
    rewrite (glb_commute y x).
    rewrite glb_assoc.
    rewrite comp2.
    rewrite glb_bot.
    auto.
  Qed.

  Instance Join_ba: Join t := fun x y z : t => glb x y = bot /\ lub x y = z.

  Instance pa: Perm_alg t.
  Proof. constructor; simpl; intros.
    (* saf_eq *)
    hnf in *. destruct H; destruct H0; subst; auto.

   (* saf_proper *)
   repeat intro; hnf in *; subst; auto.

    (* saf_assoc *)
    hnf in *. intuition.
    exists (lub b c); intuition; hnf in *. split; auto.
    rewrite <- H2 in H.
    rewrite <- H.
    apply ord_antisym.
    eauto with ba.
    rewrite H; auto with ba.
    cut (glb a c = bot); intros.
    rewrite distrib1.
    rewrite H1.
    rewrite lub_commute; rewrite lub_bot; auto. split; auto.
    subst.
    apply ord_antisym; rewrite lub_assoc; auto with ba.
    subst.
    rewrite glb_commute in H |- *.
    rewrite distrib1 in H.
    generalize (lub_upper1 (glb c a) (glb c b)); intro.
    rewrite H in H0.
    apply ord_antisym; auto.
    apply bot_correct.

    (* saf_com *)
    hnf in *.
    rewrite glb_commute.
    rewrite lub_commute.
    auto.

    (* saf_positivity *)
    hnf in *.
    intuition.
    subst a.
    rewrite (lub_commute b) in H2. rewrite lub_commute in H2.
     rewrite <- lub_assoc in H2.
    apply ord_spec2 in H2.
    rewrite lub_commute; apply ord_spec2.
    apply ord_trans with (lub a' b'); auto.
    apply ord_spec2. rewrite (lub_commute b'). rewrite lub_assoc. rewrite lub_idem; auto.
  Qed.

  Instance sa: Sep_alg t.
  Proof.  apply mkSep with (fun _ => bot).
    intros. unfold unit_for. constructor. rewrite glb_commute; apply glb_bot.
             rewrite lub_commute; apply lub_bot.
    intros. reflexivity.
  Defined.

  Instance singa: Sing_alg t.
  Proof.  apply (mkSing bot). unfold core; intros; simpl. reflexivity.
  Defined.

  Instance ca: Canc_alg t.
  Proof. repeat intro.  hnf in *. intuition.
    apply distrib_spec with b.
    rewrite lub_commute; rewrite H2.
    rewrite lub_commute; rewrite H3.
    trivial.
    rewrite glb_commute; rewrite H1.
    rewrite glb_commute; rewrite H.
    trivial.
  Qed.

  Instance da: Disj_alg t.
  Proof. repeat intro.
    destruct H, H0.
    rewrite lub_idem in H1; subst.
    rewrite glb_idem in H; subst.
    rewrite lub_commute, lub_bot; auto.
  Qed.

End BA_Facts.
