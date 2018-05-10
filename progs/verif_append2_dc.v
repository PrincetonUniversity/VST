(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**      Definitions and tactics for decorated program.    **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)


Require Import VST.floyd.proofauto.

Inductive statement : Type :=
  | Sassert : (environ -> mpred) -> statement
  | Sassume : Prop -> statement (* assert_PROP *)
  | Sgiven: forall A: Type, (A -> statement) -> statement
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: (environ -> mpred) -> (environ -> mpred) -> statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)

Notation "'GIVEN'  x ':' T ',' c " := (Sgiven _ (fun x : T => c)) (at level 65, x at level 99) : logic.

Definition Swhile (Inv: environ -> mpred) (e: expr) (s: statement):=
  Sloop Inv Inv (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

(*
Definition Sdowhile (s: statement) (e: expr) :=
  Sloop s (Sifthenelse e Sskip Sbreak).

Definition Sfor (s1: statement) (e2: expr) (s3: statement) (s4: statement) :=
  Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).
 *)

Lemma decorate_C_step2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 d2 Delta P c Post,
      (* should check d1 not Sassert or Sassume *)
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence d1 d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_step1:
  forall {Espec: OracleKind} {cs: compspecs},
    forall (d1: statement) Delta P c Post,
      (* should check d1 not Sassert or Sassume *)
      semax Delta P c Post ->
      (let d := @abbreviate _ d1 in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_then1:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Sifthenelse b d1 d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_else1:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Sifthenelse b d1 d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_then2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 Q d3 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sifthenelse b d1 d2) (Ssequence (Sassert Q) d3)) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_else2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 Q d3 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sifthenelse b d1 d2) (Ssequence (Sassert Q) d3)) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_while_body2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 Inv d2 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Swhile Inv b d1) d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_while_after2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 Inv d2 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Swhile Inv b d1) d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_assert:
  forall {Espec: OracleKind} {cs: compspecs},
    forall P' d1 Delta P c Post,
      ENTAIL Delta, P |-- P' ->
      (let d := @abbreviate _ d1 in semax Delta P' c Post) ->
      (let d := @abbreviate _ (Ssequence (Sassert P') d1) in semax Delta P c Post).
Proof.
  intros.
  eapply semax_pre.
  + exact H.
  + exact H0.
Qed.

Lemma decorate_C_assume:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Pure d1 Delta P c Post,
      ENTAIL Delta, P |-- !! Pure ->
      (Pure -> let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sassume Pure) d1) in semax Delta P c Post).
Proof.
  intros.
  assert_PROP Pure; auto.
Qed.

Lemma decorate_C_given:
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} d1 Delta P c Post,
      (forall a, let d := @abbreviate _ (d1 a) in semax Delta (P a) c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta (exp P) c Post).
Proof.
  intros.
  Intros a.
  apply H.
Qed.

Lemma decorate_C_given':
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} a d1 Delta P c Post,
      (let d := @abbreviate _ (d1 a) in semax Delta P c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta P c Post).
Proof.
  intros.
  apply H.
Qed.

Tactic Notation "forwardD" :=
  match goal with
  | |- let d := @abbreviate _ (Sifthenelse _ _ _) in
       semax _ _ (Clight.Sifthenelse _ _ _) _ =>
      intro d; forward_if;
      [ ..
      | revert d; refine (decorate_C_if_then1 _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_if_else1 _ _ _ _ _ _ _ _)]
  | |- let d := @abbreviate _ (Ssequence (Swhile ?Inv _ _) _) in
       semax _ _ (Clight.Ssequence (Clight.Swhile _ _) _) _ =>
      intro d; forward_while Inv;
      [ ..
      | revert d; refine (decorate_C_while_body2 _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_while_after2 _ _ _ _ _ _ _ _ _)]
  | |- let d := @abbreviate _ (Sgiven _ (fun x => _)) in
       semax _ _ _ _ =>
      refine (decorate_C_given _ _ _ _ _ _); intros x d; Intros; revert d
  | |- let d := @abbreviate _ (Ssequence (Sassert ?P) _) in
       semax _ _ _ _ =>
      refine (decorate_C_assert P _ _ _ _ _ _ _)
  | |- let d := @abbreviate _ (Ssequence _ _) in
       semax _ _ (Clight.Ssequence _ _) _ =>
      intro d;
      forward;
      revert d;
      refine (decorate_C_step2 _ _ _ _ _ _ _)
  | |- let d := @abbreviate _ _ in
       semax _ _ _ _ =>
      refine (decorate_C_step1 _ _ _ _ _ _);
      forward
  end.

Tactic Notation "forwardD" constr(a) :=
  match goal with
  | |- let d := @abbreviate _ (Sgiven _ (fun x => _)) in
       semax _ _ _ _ =>
      refine (decorate_C_given' a _ _ _ _ _ _); intros d; Intros; revert d
  end.


(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**        Original definitions in verif_append2.v         **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)


Require Import VST.progs.append.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sh: share)
            (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_struct_list (h,y) x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Arguments listrep sh contents x : simpl never.

Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p=nullval <-> contents=nil)).
Proof.
intros.
revert p; induction contents; unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sh contents p,
   sepalg.nonidentity sh ->
   listrep sh contents p |-- valid_pointer p.
Proof.
 destruct contents; unfold listrep; fold listrep; intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto. simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_null: forall sh contents,
    listrep sh contents nullval = !! (contents=nil) && emp.
Proof.
destruct contents; unfold listrep; fold listrep.
normalize.
apply pred_ext.
Intros y. entailer. destruct H; contradiction.
Intros.
Qed.

Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.

Definition append_spec :=
 DECLARE _append
  WITH sh : share, contents : list int, x: val, y: val, s1: list val, s2: list val
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP(writable_share sh)
     LOCAL (temp _x x; temp _y y)
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep sh (s1++s2) r).

Definition Gprog : funspecs :=   ltac:(with_library prog [ append_spec ]).

Module Proof1.

Definition lseg (sh: share) (contents: list val) (x z: val) : mpred :=
  ALL cts2:list val, listrep sh cts2 z -* listrep sh (contents++cts2) x.

(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**                       THE  PROOF                       **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)

Definition DC (sh: share) (s1 s2: list val) (x: val) (y: val): statement :=
  (Sifthenelse (Ebinop Oeq (Etempvar _x (tptr (Tstruct _list noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn (Some (Etempvar _y (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sset _t (Etempvar _x (tptr (Tstruct _list noattr))))
    (Ssequence
      (Sassert (EX a: val, EX s1b: list val,
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y))))
    (GIVEN a: val, GIVEN s1b: list val,
    (Ssequence
      (Sassert (EX u: val,
        (PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert)
    (GIVEN u: val,
    (Ssequence
      (Sset _u
        (Efield
          (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
      (Ssequence
        (Swhile
          (EX a: val, EX s1b: list val, EX t: val, EX u: val,
            PROP ()
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                   data_at sh t_struct_list (a,u) t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert
          (Ebinop One (Etempvar _u (tptr (Tstruct _list noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
          (GIVEN a: val, GIVEN s1b: list val, GIVEN t: val, GIVEN u: val,
          (Ssequence
            (Sassert (EX b: val, EX s1c: list val, EX z: val,
              (PROP (s1b = b :: s1c)
               LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
               SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                    data_at sh t_struct_list (a, u) t;
                    data_at sh t_struct_list (b, z) u;
                    listrep sh s1c z; listrep sh s2 y)))%assert)
          (GIVEN b: val, GIVEN s1c: list val, GIVEN z: val,
          (Ssequence
            (Sset _t (Etempvar _u (tptr (Tstruct _list noattr))))
            (Sset _u
              (Efield
                (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr)))))))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
            (Etempvar _y (tptr (Tstruct _list noattr))))
          (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr)))))))))))))).

(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**              Check the side conditions                 **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
start_function.
match goal with
| |- ?P => let d1 := eval hnf in (DC sh s1 s2 x y) in
           change (let d := @abbreviate _ d1 in P)
end.
forwardD.
* forwardD.
  rewrite listrep_null. normalize.
  Exists y.
  simpl; entailer!.
* forwardD.
  forwardD.
  {
    destruct s1 as [| a s1b]; [unfold listrep at 1; fold listrep; normalize; entailer! |].
    Exists a s1b.
    entailer!.
  }
  forwardD.
  forwardD.
  forwardD.
  {
    subst s1.
    unfold listrep at 1; fold listrep.
    Intros u; Exists u.
    entailer!.
  }
  forwardD.
  forwardD.
  forwardD.
  {
    Exists a s1b x u.
    subst s1. entailer!. cancel_wand.
  }
  {
    entailer!.
  }
  {
    clear a s1b H0 u.
    rename a0 into a, s1b0 into s1b, u0 into u.
    forwardD a.
    forwardD s1b.
    forwardD t.
    forwardD u.
    forwardD.
    {
      destruct s1b as [| b s1c]; unfold listrep at 3; fold listrep; [ Intros; contradiction |].
      Intros z.
      Exists b s1c z.
      entailer!.
    }
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    {
      Exists (b,s1c,u,z). unfold fst, snd.
      simpl app.
      entailer!.
      rewrite sepcon_comm.
      apply RAMIF_PLAIN.trans''.
      apply wand_sepcon_adjoint.
      simpl.
      forget (b::s1c++s2) as s3.
      unfold listrep; fold listrep; Exists u; auto.
    }
  }
  clear a s1b H0 u.
  rename a0 into a, s1b0 into s1b, u0 into u.
  forwardD.
  forwardD.
  {
    rewrite (proj1 H2 (eq_refl _)).
    Exists x.
    simpl app.
    clear.
    entailer!.
    unfold listrep at 3; fold listrep. normalize.
    pull_right (listrep sh (a :: s2) t -* listrep sh (s1 ++ s2) x).
    apply modus_ponens_wand'.
    unfold listrep at 2; fold listrep. Exists y; auto.
  }
Qed.

End Proof1.

