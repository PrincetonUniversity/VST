Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Require Import VST.veric.mpred.
Require Import VST.veric.address_conflict.
Require Export VST.veric.shares.
Require Import VST.veric.Cop2. (*for definition of tc_val'*)

Local Open Scope pred.


Definition callingconvention_of_funspec (phi:funspec):calling_convention :=
  match phi with
    mk_funspec sig cc A P Q Pne Qne => cc
  end.

Definition WithType_of_funspec (phi:funspec):TypeTree :=
  match phi with
    mk_funspec sig cc A P Q Pne Qne => A
  end.

(*******************material moved here from tycontext.v *******************)

Inductive Annotation :=
  WeakAnnotation : (environ -> mpred) -> Annotation
| StrongAnnotation : (environ -> mpred) -> Annotation.

Inductive tycontext : Type :=
  mk_tycontext : forall (tyc_temps: PTree.t type)
                        (tyc_vars: PTree.t type)
                        (tyc_ret: type)
                        (tyc_globty: PTree.t type)
                        (tyc_globsp: PTree.t funspec)
                        (tyc_annot: PTree.t Annotation),
                             tycontext.

Definition empty_tycontext : tycontext :=
  mk_tycontext (PTree.empty _) (PTree.empty _) Tvoid
         (PTree.empty _)  (PTree.empty _) (PTree.empty _).

Definition temp_types (Delta: tycontext): PTree.t type :=
  match Delta with mk_tycontext a _ _ _ _ _ => a end.
Definition var_types (Delta: tycontext) : PTree.t type :=
  match Delta with mk_tycontext _ a _ _ _ _ => a end.
Definition ret_type (Delta: tycontext) : type :=
  match Delta with mk_tycontext _ _ a _ _ _ => a end.
Definition glob_types (Delta: tycontext) : PTree.t type :=
  match Delta with mk_tycontext _ _ _ a _ _ => a end.
Definition glob_specs (Delta: tycontext) : PTree.t funspec :=
  match Delta with mk_tycontext _ _ _ _ a _ => a end.
Definition annotations (Delta: tycontext) : PTree.t Annotation :=
  match Delta with mk_tycontext _ _ _ _ _ a => a end.

(** Creates a typecontext from a function definition **)
(* NOTE:  params start out initialized, temps do not! *)

Definition make_tycontext_t (params: list (ident*type)) (temps : list(ident*type)) :=
fold_right (fun (param: ident*type) => PTree.set (fst param) (snd param))
 (fold_right (fun (temp : ident *type) tenv => let (id,ty):= temp in PTree.set id ty tenv)
  (PTree.empty type) temps) params.

Definition make_tycontext_v (vars : list (ident * type)) :=
 fold_right (fun (var : ident * type) venv => let (id, ty) := var in PTree.set id ty venv)
   (PTree.empty type) vars.

Definition make_tycontext_g (V: varspecs) (G: funspecs) :=
 (fold_right (fun (var : ident * funspec) => PTree.set (fst var) (type_of_funspec (snd var)))
      (fold_right (fun (v: ident * type) => PTree.set (fst v) (snd v))
         (PTree.empty _) V)
            G).

Definition make_tycontext_a (anns : list (ident * Annotation)) :=
 fold_right (fun (ia : ident * Annotation) aenv => let (id, a) := ia in PTree.set id a aenv)
   (PTree.empty Annotation) anns.

Definition make_tycontext (params: list (ident*type)) (temps: list (ident*type)) (vars: list (ident*type))
                       (return_ty: type)
                       (V: varspecs) (G: funspecs) (A: list (ident*Annotation)):  tycontext :=
 mk_tycontext
   (make_tycontext_t params temps)
   (make_tycontext_v vars)
   return_ty
   (make_tycontext_g V G)
   (make_tycontext_s G)
   (make_tycontext_a A).

(******************* end of material from tycontext.v*)

(*******************material moved here from expr.v *******************)

(** Environment typechecking functions **)

Definition typecheck_temp_environ
(te: tenviron) (tc: PTree.t type) :=
forall id ty , tc ! id = Some ty  -> exists v, Map.get te id = Some v /\ tc_val' ty v.

Definition typecheck_var_environ
(ve: venviron) (tc: PTree.t type) :=
forall id ty, tc ! id = Some ty <-> exists v, Map.get ve id = Some(v,ty).

Definition typecheck_glob_environ
(ge: genviron) (tc: PTree.t type) :=
forall id  t,  tc ! id = Some t ->
(exists b, Map.get ge id = Some b).

Definition typecheck_environ (Delta: tycontext) (rho : environ) :=
typecheck_temp_environ (te_of rho) (temp_types Delta) /\
typecheck_var_environ  (ve_of rho) (var_types Delta) /\
typecheck_glob_environ (ge_of rho) (glob_types Delta).

Definition local:  (environ -> Prop) -> environ->mpred :=  lift1 prop.

Definition tc_environ (Delta: tycontext) : environ -> Prop :=
   fun rho => typecheck_environ Delta rho.

Definition funsig_tycontext (fs: funsig) : tycontext :=
  make_tycontext (fst fs) nil nil (snd fs) nil nil nil.

Definition funsig_of_funspec (fs: funspec) : funsig :=
 match fs with mk_funspec fsig _ _ _ _ _ _ => fsig end.

Definition ret0_tycon (Delta: tycontext): tycontext :=
  mk_tycontext (PTree.empty _) (PTree.empty _) (ret_type Delta) (glob_types Delta) (glob_specs Delta) (annotations Delta).

(* If we were to require that a non-void-returning function must,
   at a function call, have its result assigned to a temp,
   then we could change "ret0_tycon" to "ret_tycon" in this
   definition (and in NDfunspec_sub). *)

Lemma eqb_type_symm t1 t2: eqb_type t1 t2 = eqb_type t2 t1.
Proof. 
  remember (eqb_type t2 t1) as b; symmetry in Heqb; destruct b.
+ apply eqb_type_spec.
  apply eqb_type_spec in Heqb; subst; trivial.
+ apply eqb_type_false in Heqb. apply eqb_type_false; auto. 
Qed.

Fixpoint Forallb2 {A} (f: A -> A -> bool) l l' :=
  match l, l' with
    nil, nil => true
  | (a::t), (a'::t') => (f a a' && Forallb2 f t t')%bool
  | _, _ => false
  end.

Lemma Forallb2_char {A} f: forall l l', @Forallb2 A f l l' = true <-> Forall2 (fun x y => f x y = true) l l'.
Proof.
  induction l; simpl; intros.
+ destruct l'; split; intros. constructor. trivial. discriminate. inv H.
+ destruct l'; split; intros. inv H. inv H.
  rewrite andb_true_iff in H; destruct H. constructor; [ | apply IHl]; trivial.
  inv H. rewrite andb_true_iff. split; [ | apply IHl]; trivial.
Qed.

Lemma Forallb2_refl {A f} (Hf: forall a, f a a =true): forall l, @Forallb2 A f l l = true.
Proof. induction l; simpl; trivial. rewrite Hf, IHl; trivial. Qed.

Lemma Forallb2_symm {A f} (Hf: forall a b, f a b = f b a): 
      forall l1 l2, @Forallb2 A f l1 l2 = @Forallb2 A f l2 l1.
Proof. induction l1; simpl.
  destruct l2; simpl; trivial.
  destruct l2; simpl; trivial. rewrite Hf, IHl1; trivial.
Qed.

Definition funsigs_match (s1 s2:funsig):bool := 
  (match s1, s2 with (args1,ret1), (args2, ret2) => 
      eqb_type ret1 ret2 &&
      Forallb2 eqb_type (map snd args1) (map snd args2) (*implies equality of length*)
      && (compute_list_norepet (map fst args1) && compute_list_norepet (map fst args2))
  end)%bool. 

Lemma funsigs_match_refl {f} (F: list_norepet (map fst (fst f))): funsigs_match f f = true.
Proof. apply compute_list_norepet_i in F.
  destruct f; simpl in *.
  rewrite Forallb2_refl, F; intros; rewrite eqb_type_refl; simpl; trivial.
Qed.

Lemma funsigs_match_symm f g: funsigs_match f g = funsigs_match g f.
Proof.
  destruct f; destruct g; simpl.
  rewrite Forallb2_symm; intros; rewrite eqb_type_symm; trivial.
  f_equal. rewrite andb_comm; trivial.
Qed.

Lemma funsigs_match_argtypes {s1 s2} (FSM: funsigs_match s1 s2 = true): 
      map snd (fst s1) = map snd (fst s2).
Proof.
  destruct s1; destruct s2; simpl in *.
  apply andb_true_iff in FSM; destruct FSM as [? _]. 
  apply andb_true_iff in H; destruct H as [_ ?]. generalize dependent l0.
  induction l; intros; destruct l0; simpl in *; trivial; inv H.
  apply andb_true_iff in H1; destruct H1. apply eqb_type_true in H. f_equal; eauto.
Qed.

Lemma funsigs_match_arglengths {s1 s2} (FSM: funsigs_match s1 s2 = true):
      length (map fst (fst s1)) = length (map fst (fst s2)).
Proof.
  apply funsigs_match_argtypes in FSM.
  rewrite 2 map_length, <- (map_length snd), FSM, map_length; trivial.
Qed.

Lemma funsigs_match_rettypes {s1 s2} (FSM: funsigs_match s1 s2 = true): snd s1 = snd s2.
Proof.
  destruct s1; destruct s2; simpl in *.
  apply andb_true_iff in FSM; destruct FSM.
  apply andb_true_iff in H; destruct H. apply eqb_type_true in H; trivial.
Qed.

Lemma funsigs_match_LNR1 {s1 s2} (FSM: funsigs_match s1 s2 = true): 
      list_norepet (map fst (fst s1)).
Proof. destruct s1; destruct s2; simpl in *. apply compute_list_norepet_e.
  apply andb_true_iff in FSM; destruct FSM as [_ ?].
  apply andb_true_iff in H; apply H. 
Qed.

Lemma funsigs_match_LNR2 {s1 s2} (FSM: funsigs_match s1 s2 = true): 
      list_norepet (map fst (fst s2)).
Proof. destruct s1; destruct s2; simpl in *. apply compute_list_norepet_e.
  apply andb_true_iff in FSM; destruct FSM as [_ ?].
  apply andb_true_iff in H; apply H. 
Qed.

Lemma forallb2_eqbtype_trans: forall {l1 l2 l3},
      Forallb2 eqb_type l1 l2 = true -> Forallb2 eqb_type l2 l3 = true -> Forallb2 eqb_type l1 l3 = true.
Proof. 
  induction l1; simpl; intros.
+ destruct l2; [ destruct l3; simpl in *; trivial | discriminate].
+ destruct l2. discriminate.
  destruct l3; simpl in *. discriminate.
  apply andb_true_iff in H; destruct H.
  apply andb_true_iff in H0; destruct H0.
  apply eqb_type_true in H; subst. rewrite H0; simpl. eauto.
Qed.
 
Lemma funsigs_match_typesigs_eq {f1 f2} (FSM: funsigs_match f1 f2 = true):
      typesig_of_funsig f1 = typesig_of_funsig f2.
Proof. 
  specialize (funsigs_match_rettypes FSM); intros. 
  apply funsigs_match_argtypes in FSM. 
  unfold typesig_of_funsig; simpl. rewrite FSM, H. trivial.
Qed.

Lemma funsigs_match_trans {f1 f2 f3}: funsigs_match f1 f2 = true ->
   funsigs_match f2 f3 = true -> funsigs_match f1 f3 = true.
Proof. 
  destruct f1 as [args1 rt1].
  destruct f2 as [args2 rt2].
  destruct f3 as [args3 rt3].
  simpl. rewrite ! andb_true_iff. intros [[RT12 ARGS12] [LNR1 LNR2]] [[RT23 ARGS23] [_ LNR3]].
  split3; trivial.
  apply eqb_type_true in RT12. apply eqb_type_true in RT23. subst.
  rewrite eqb_type_refl. split; trivial.
  eapply forallb2_eqbtype_trans; eassumption.
Qed.

Fixpoint tr {A} l (m:Map.t A) := 
  match l with
    nil => (*m*)Map.empty A
  | (s,t)::l' => let m' := tr l' m in
                 match Map.get m s with
                   None => m'
                 | Some v => Map.set t v m'
                 end
  end.

Definition restrict {A} l rho := @tr A (combine l l) rho.

Lemma tr_refl {A}: forall l rho, @tr A (combine l l) rho = restrict l rho.
Proof.
 induction l; simpl; [ trivial | intros]. unfold restrict; simpl. trivial.
Qed.

Definition funspec_sub_si (f1 f2 : funspec):mpred :=
let Delta1 := funsig_tycontext (funsig_of_funspec f1) in
let Delta2 := funsig_tycontext (funsig_of_funspec f2) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        !!(funsigs_match fsig1 fsig2 = true /\ cc1=cc2) &&
        ! (ALL ts2 :_, ALL x2:dependent_type_functor_rec ts2 A2 mpred , ALL rho2:_,
        (((local (tc_environ Delta2) rho2) && 
           (P2 ts2 x2 (mkEnviron (ge_of rho2) (ve_of rho2) (restrict (map fst (fst fsig2)) (te_of rho2)))))
         >=> EX ts1:_,  EX x1:dependent_type_functor_rec ts1 A1 mpred, EX F:_,
             let rho1 := mkEnviron (ge_of rho2) (ve_of rho2)
                                   (tr (combine (map fst (fst fsig2)) (map fst (fst fsig1))) (te_of rho2)) in
            ((local (tc_environ Delta1) rho1) && (F * (P1 ts1 x1 rho1)) &&
             ALL rho':_, (     !( ((local (tc_environ (ret0_tycon Delta1)) rho') && (F * (Q1 ts1 x1 rho')))
                          >=> ((local (tc_environ (ret0_tycon Delta2)) rho') && Q2 ts2 x2 rho'))))))
    end
end.

Definition funspec_sub (f1 f2 : funspec):Prop :=
let Delta1 := funsig_tycontext (funsig_of_funspec f1) in
let Delta2 := funsig_tycontext (funsig_of_funspec f2) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        funsigs_match fsig1 fsig2 = true /\ cc1=cc2 /\
        forall (ts2 : list Type) (x2:dependent_type_functor_rec ts2 A2 mpred) rho2,
               ((local (tc_environ Delta2) rho2) && 
                 (P2 ts2 x2 (mkEnviron (ge_of rho2) (ve_of rho2) (restrict (map fst (fst fsig2)) (te_of rho2)))))
           |--
               (EX ts1:_,  EX x1:dependent_type_functor_rec ts1 A1 mpred, EX F:_,
                  (*!!(transfer' (map fst (fst fsig2)) (map fst (fst fsig1)) (ve_of rho2) = Some ve1) &&*)
                  let rho1 := mkEnviron (ge_of rho2) (ve_of rho2) (tr (combine (map fst (fst fsig2)) (map fst (fst fsig1))) (te_of rho2)) in
                  ((local (tc_environ Delta1) rho1) && (F * (P1 ts1 x1 rho1)) &&
                  (!! (forall rho',
                        ((local (tc_environ (ret0_tycon Delta1)) rho') && (F * (Q1 ts1 x1 rho')))
                         |-- ((local (tc_environ (ret0_tycon Delta2)) rho') && Q2 ts2 x2 rho')))))
   end
end.

Lemma funspecs_sub_funsigs_match s1 s2: funspec_sub s1 s2 ->
      funsigs_match (funsig_of_funspec s1) (funsig_of_funspec s2) = true.
Proof. destruct s1; destruct s2; simpl; intros H; apply H. Qed.

Lemma funspec_sub_si_funsigs_match s1 s2: funspec_sub_si s1 s2 |--
      !!(funsigs_match (funsig_of_funspec s1) (funsig_of_funspec s2) = true).
Proof. destruct s1; destruct s2; simpl; intros r H; apply H. Qed.
(*
Definition funspec_sub_si (f1 f2 : funspec):mpred :=
let Delta := funsig_tycontext (funsig_of_funspec f1) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        !!(fsig1 = fsig2 /\ cc1=cc2) &&
        ! (ALL ts2 :_, ALL x2:_, ALL rho:_,
        (((local (tc_environ Delta) rho) && (P2 ts2 x2 rho))
         >=> EX ts1:_,  EX x1:_, EX F:_, 
            (F * (P1 ts1 x1 rho)) &&
            ALL rho':_, (     !( ((local (tc_environ (ret0_tycon Delta)) rho') && (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho')))))
    end
end.
Definition funspec_sub_early (f1 f2 : funspec):mpred :=
let Delta := funsig_tycontext (funsig_of_funspec f1) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        !!(fsig1 = fsig2 /\ cc1=cc2) &&
        ! (ALL ts2 :_, ALL x2:_, ALL rho:_, EX ts1:_,  EX x1:_, EX F:_,
        (((local (tc_environ Delta) rho) && (P2 ts2 x2 rho))
         >=> (*EX ts1:_,  EX x1:_, EX F:_, *)
            (F * (P1 ts1 x1 rho)) &&
            ALL rho':_, (     !( ((local (tc_environ (ret0_tycon Delta)) rho') && (F * (Q1 ts1 x1 rho')))
                         >=> (Q2 ts2 x2 rho')))))
    end
end.

Definition funspec_sub (f1 f2 : funspec):Prop :=
let Delta := funsig_tycontext (funsig_of_funspec f1) in
match f1 with
| mk_funspec fsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec fsig2 cc2 A2 P2 Q2 _ _ =>
        fsig1 = fsig2 /\ cc1=cc2 /\
        forall (ts2 : list Type) x2 rho,
               ((local (tc_environ Delta) rho) && (P2 ts2 x2 rho))
           |--
               (EX ts1:_,  EX x1:_, EX F:_, 
                           (F * (P1 ts1 x1 rho)) &&
                               (!! (forall rho',
                                           ((local (tc_environ (ret0_tycon Delta)) rho') &&
                                                 (F * (Q1 ts1 x1 rho')))
                                         |--
                                           (Q2 ts2 x2 rho'))))
    end
end.*)

Lemma funspec_sub_sub_si f1 f2: funspec_sub f1 f2 -> TT |-- funspec_sub_si f1 f2.
Proof. intros. destruct f1; destruct f2; simpl in *.
destruct H as [? [? H']]; subst. intros w _. split; [split; trivial |].
intros ts2 x2 rho2 y WY k YK K.
destruct (H' ts2 x2 rho2 _ K) as [ts1 [x1 [F [HF1 HF2]]]]; clear H'.
exists ts1, x1, F; split; trivial.
intros rho' v KV z VZ Z. hnf in HF2. apply HF2; trivial.
Qed.
Lemma funspec_sub_sub_si' f1 f2: !!(funspec_sub f1 f2) |-- funspec_sub_si f1 f2.
Proof. intros w W. apply funspec_sub_sub_si; trivial.
Qed.
(*
Lemma funspec_sub_early_sub_si f1 f2: funspec_sub_early f1 f2 |-- funspec_sub_si f1 f2.
Proof. intros p P. destruct f1; destruct f2; simpl in *.
destruct P as [[? ?] H']; subst. split; [split; trivial |].
intros ts2 x2 rho y WY k YK K.
destruct (H' ts2 x2 rho) as [ts1 [x1 [F HF]]]; clear H'.
exists ts1, x1, F. apply (HF _ WY _ YK K).
Qed.
*)

Lemma funspec_sub_refl {f} (F:list_norepet (map fst (fst (funsig_of_funspec f)))): funspec_sub f f.
Proof.
  destruct f; split; [ apply funsigs_match_refl; trivial | split; [trivial | intros ts2 x2 rho2 w [T W]]].
  rewrite tr_refl.
  exists ts2, x2, emp. hnf.
  rewrite emp_sepcon. split. 
  + destruct rho2. simpl in *. split; trivial.
    unfold tc_environ, typecheck_environ in *. simpl in *. intuition.
    unfold restrict. red; intros; simpl. destruct (H id _ H0) as [v [? ?]].
    exists v; split; trivial. forget (fst f) as l. clear - H0 H3.
    induction l; simpl in *. rewrite PTree.gempty in H0. discriminate.
    destruct a as [j tp]; simpl in *. rewrite PTree.gsspec in H0.
    destruct (peq id j); subst. { rewrite H3, Map.gss; trivial. }
    specialize (IHl H0).
    remember (Map.get te j) as w; symmetry in Heqw; destruct w; trivial.
    rewrite Map.gso; auto.
  + hnf; intros. rewrite emp_sepcon. simpl; trivial.
Qed.

Lemma combine_cons {A B a b aseq bseq}: @combine A B (a::aseq) (b::bseq) = (a,b)::combine aseq bseq.
Proof. reflexivity. Qed.

Lemma tr_combine_cons {A a a' l l' u rho }: Map.get rho a = Some u ->
  @tr A (combine (a::l) (a'::l')) rho = Map.set a' u (tr (combine l l') rho).
Proof. intros. simpl. rewrite H. trivial. Qed.

Lemma get_tr_None {A}: forall {l x} (Hl: ~In x (map snd l)) rho, Map.get (tr l rho) x = @None A.
induction l.
reflexivity.
destruct a as [a a']; simpl; intros.
destruct (Map.get rho a). rewrite Map.gso. apply IHl. auto. auto.
apply IHl; auto.
Qed.
  
Lemma get_tr_Some {A}: forall l y x l2
      (Lfst: list_norepet (map fst (l++(y,x)::l2)))
      (Lsnd: list_norepet (map snd (l++(y,x)::l2))) rho,
      Map.get (tr (l++(y,x)::l2) rho) x = @Map.get A rho y.
Proof. 
induction l as [ | [y1 x1]]; simpl; intros.
+ remember (Map.get rho y). destruct o; [ rewrite Map.gss; trivial |].
  induction l2 as [ | [y2 x2]]; [ simpl; reflexivity | inv Lfst; inv Lsnd ].
  simpl. inv H2; inv H4. exploit IHl2; clear IHl2.
  { constructor; trivial. intros N. apply H1; right; trivial. }
  { constructor; trivial. intros N. apply H3; right; trivial. }
  intros IHl2.
  remember (Map.get rho y2) as v2; symmetry in Heqv2. destruct v2; trivial.
  rewrite Map.gso; trivial. intros N; subst. apply H3; left; trivial.
+ inv Lfst; inv Lsnd. specialize (IHl _ _ _ H2 H4).
  remember (Map.get rho y1) as v1; symmetry in Heqv1. destruct v1; trivial.
  rewrite Map.gso; trivial. intros N; subst. apply H3. apply in_map_iff.
  exists (y,x); split; trivial. apply in_or_app. right; left; trivial.
Qed.

Lemma fst_combine {A B}: forall {l1:list A} {l2:list B}, length l1 = length l2 ->
      map fst (combine l1 l2) = l1.
Proof.
  induction l1; simpl; intros.
+ destruct l2; inv H; auto.
+ destruct l2; inv H. simpl. rewrite IHl1; trivial.
Qed.

Lemma snd_combine {A B}: forall {l1:list A} {l2:list B}, length l1 = length l2 ->
      map snd (combine l1 l2) = l2.
Proof.
  induction l1; simpl; intros.
+ destruct l2; inv H; auto.
+ destruct l2; inv H. simpl. rewrite IHl1; trivial.
Qed.

Lemma list_norepet_app_split_unique {A}: forall {l:list A} (L: list_norepet l) {l1 l1' l2 l2' a} 
      (L12: l = l1++a::l2) (L12': l = l1'++a::l2'), l1=l1' /\ l2=l2'.
Proof.
  induction l; simpl.
+ intros. symmetry in L12. apply app_eq_nil in L12; destruct L12; subst. discriminate.
+ intros L. inv L. rename H1 into Ha. rename H2 into L. specialize (IHl L).
  destruct l1. 
  - simpl in *.
    destruct l1'.
    * simpl; intros; subst. inv L12; inv L12'. split; trivial.
    * simpl; intros; subst. inv L12. inv L12'.
      elim Ha; clear. apply in_or_app. right; left; trivial. 
  - simpl in *.
    destruct l1'.
    * simpl; intros; subst. inv L12; inv L12'. 
      elim Ha; clear. apply in_or_app. right; left; trivial.
    * simpl; intros; subst. inv L12. inv L12'.
      destruct (IHl l1 l1' l2 l2' a2); trivial. subst. split; trivial.
Qed.

Lemma tr_trans {A}: forall {l2 l1 l3},
  length l1 = length l2 -> length l2 = length l3 -> 
  forall (L1:list_norepet l1) (L2:list_norepet l2) (L3:list_norepet l3) rho,
  @tr A (combine l2 l1) (tr (combine l3 l2) rho) = tr (combine l3 l1) rho.
Proof.
induction l2; intros.
+ destruct l1; inv H. destruct l3; inv H0. simpl; trivial.
+ rename a into a2. destruct l1 as [ | a1 l1]; inv H. destruct l3 as [ | a3 l3]; inv H0.
  inv L1. rename H3 into A1; rename H4 into L1.
  inv L2. rename H3 into A2; rename H4 into L2.
  inv L3. rename H3 into A3. rename H4 into L3.
  specialize (IHl2 _ _ H2 H1 L1 L2 L3). rewrite 3 combine_cons.
  simpl. remember (Map.get rho a3) as v3; symmetry in Heqv3; destruct v3 as [ v3 | ].
  - rewrite Map.gss. apply Map.ext; intros.
    rewrite 2 Map.gsspec. destruct (ident_eq x a1); trivial.
    destruct (in_dec peq x (map snd (combine l3 l1))).
    * apply list_in_map_inv in i. destruct i as [[z3 z1] [Hz HH]]. simpl in Hz. subst x.
      apply in_split in HH. destruct HH as [L31 [M31 C31]].
      rewrite C31, get_tr_Some.
      2: rewrite <- C31, fst_combine; [ trivial | rewrite H2, H1; trivial].
      2: rewrite <- C31, snd_combine; [ trivial | rewrite H2, H1; trivial].
      destruct (in_dec peq z1 l1).
      2:{ rewrite <- (@snd_combine _ _ l3 l1), C31 in n0. 2: rewrite H2, H1; trivial.
          elim n0. apply in_map_iff. exists (z3, z1). split; trivial. apply in_or_app. right; left; trivial. }
      symmetry in H2; rewrite <- (snd_combine H2) in i.
      apply list_in_map_inv in i. destruct i as [[z2 q1] [Hq1 HH]]. simpl in Hq1; subst q1.
      apply in_split in HH. destruct HH as [L21 [M21 C21]].
      rewrite C21, get_tr_Some, Map.gsspec.
      2: rewrite <- C21, (fst_combine H2); trivial.
      2: rewrite <- C21, (snd_combine H2); trivial.
      destruct (ident_eq z2 a2); [ subst a2 | ].
      { elim A2; clear - H2 C21. rewrite <- (fst_combine H2), C21.
        apply in_map_iff. exists (z2, z1). split; trivial. apply in_or_app. right; left; trivial. }
      destruct (in_dec peq z2 (map snd (combine l3 l2))).
      2:{ elim n1. symmetry in H1; rewrite (snd_combine H1). rewrite <- (fst_combine H2), C21.
          apply in_map_iff. exists (z2, z1). split; trivial. apply in_or_app. right; left; trivial. }
      apply list_in_map_inv in i. destruct i as [[q3 q2] [Hq2 HH]]. simpl in Hq2; subst q2.
      apply in_split in HH. destruct HH as [L32 [M32 C32]].
      rewrite C32, get_tr_Some. 
      2: symmetry in H1; rewrite <- C32, (fst_combine H1); trivial.
      2: symmetry in H1; rewrite <- C32, (snd_combine H1); trivial.

      assert (L321: Datatypes.length L32 = Datatypes.length L21).
      { assert (XX: length (map snd L32) = length (map fst L21)).
        2: rewrite 2 map_length in XX; trivial.
        symmetry in H1; specialize (snd_combine H1); intros X2.
        rewrite C32, map_app in X2; simpl in X2; symmetry in X2.
        specialize (fst_combine H2); intros Y2.
        rewrite C21, map_app in Y2; simpl in Y2; symmetry in Y2.
        destruct (list_norepet_app_split_unique L2 X2 Y2). rewrite H; trivial. }

      assert (L312: Datatypes.length L31 = Datatypes.length L21).
      { assert (XX: length (map snd L31) = length (map fst L21)). 
        2: rewrite 2 map_length in XX; trivial. 
        specialize (snd_combine H2); intros Y2.
        rewrite C21, map_app in Y2; simpl in Y2; symmetry in Y2.
        rewrite H1 in H2. specialize (snd_combine H2); intros X2.
        rewrite C31, map_app in X2; simpl in X2; symmetry in X2.
        destruct (list_norepet_app_split_unique L1 X2 Y2). rewrite H, 2 map_length; trivial. }

      exploit (@app_nth2 _ L32 ((q3, z2) :: M32) (a1,a1) (length L32)). omega.
      simpl; rewrite minus_diag, <- C32, combine_nth; intros.
      exploit (@app_nth2 _ L21 ((z2, z1) :: M21) (a1,a1) (length L21)). omega.
      simpl; rewrite minus_diag, <- C21, combine_nth; intros.
      exploit (@app_nth2 _ L31 ((z3, z1) :: M31) (a1,a1) (length L31)). omega.
      simpl; rewrite minus_diag, <- C31, combine_nth; intros.
      rewrite L321 in *.  rewrite L312 in *. inv H. inv H3. trivial.
      rewrite <- H1; trivial. trivial. rewrite H1; trivial.
    * rewrite (get_tr_None n0).
      assert (~ In x (map snd (combine l2 l1))).
      { symmetry in H2;  rewrite (snd_combine H2). 
        rewrite H1 in H2. rewrite (snd_combine H2) in n0; trivial. }
      rewrite (get_tr_None H); trivial.
  - remember (Map.get (tr (combine l3 l2) rho) a2); symmetry in Heqo; destruct o as [ v2 |]; trivial.
    apply Map.ext; intros. rewrite Map.gsspec.
    destruct (ident_eq x a1); [ subst | rewrite IHl2; trivial].
    elim A2; clear - H1 Heqo.
    generalize dependent l2. induction l3; simpl; intros; destruct l2; try discriminate.
    inv H1. simpl in Heqo. destruct (Map.get rho a).
    * rewrite Map.gsspec in Heqo.
      destruct (ident_eq a2 p); subst. left; trivial. right; auto.
    * right; auto.
Qed.

Lemma get_combine {A l1 l2 n m i1 i2} (LNR1: list_norepet l1) (LNR2 : list_norepet l2)
      (L : length l1 = length l2)
      (Hi2 : nth_error l2 n = Some i2)
      (Hi1 : nth_error l1 n = Some i1):
  @Map.get A (tr (combine l1 l2) m) i2 = Map.get m i1.
Proof. 
  generalize dependent n. generalize dependent l2. induction l1; simpl; intros.
+ destruct l2; simpl in *. rewrite nth_error_nil in Hi2; discriminate. discriminate. 
+ destruct l2; simpl in *. rewrite nth_error_nil in Hi2; discriminate. inv LNR1. inv L. inv LNR2.
  destruct n; simpl in *.
  - inv Hi1. inv Hi2.
    destruct (Map.get m i1); [ rewrite Map.gss; trivial | apply get_tr_None].
    rewrite snd_combine; trivial.
  - specialize (IHl1 H2 _ H5 H0 _ Hi2 Hi1).
    destruct (Map.get m a); trivial.
    rewrite Map.gso; trivial. intros N; subst. apply nth_error_In in Hi2. contradiction.
Qed.

Lemma funspec_sub_trans {f1 f2 f3} (FSM12: funspec_sub f1 f2) (FSM23: funspec_sub f2 f3): 
      funspec_sub f1 f3.
Proof.
destruct f1 as [sig1 cc A1 P1 Q1 P1ne Q1ne].
destruct f2 as [sig2 cc2 A2 P2 Q2 P2ne Q2ne].
destruct f3 as [sig3 cc3 A3 P3 Q3 P3ne Q3ne].
destruct FSM12 as [FSM12 [? H12]]. destruct FSM23 as [FSM23 [? H23]]. subst cc3 cc2.
specialize (funsigs_match_trans FSM12 FSM23); intros FSM13.
split; [ trivial | split; [ trivial | intros ts3 x3 rho3 m M]]; simpl in M.
simpl in H23, H12.
specialize (funsigs_match_rettypes FSM13); intros RET13.
destruct (H23 ts3 x3 rho3 _ M) as [ts2 [x2 [F2 [[TC23 X23] Y23]]]]; clear H23; hnf in Y23.
remember ((mkEnviron (ge_of rho3) (ve_of rho3)
            (tr (combine (map fst (fst sig3)) (map fst (fst sig2))) (te_of rho3)))) as rho2.
destruct X23 as [m1 [m2 [JM [M1 M2]]]]; destruct (join_level _ _ _ JM) as [Lev_m1 Lev_m2].
specialize (funsigs_match_LNR1 FSM12); intros LNR1.
specialize (funsigs_match_LNR2 FSM12); intros LNR2.
specialize (funsigs_match_LNR2 FSM13); intros LNR3.
destruct (H12 ts2 x2 rho2 m2) as [ts1 [x1 [F1 [[TC12 X12] Y12]]]]; clear H12; try hnf in Y12.
{ split; trivial. clear - M2 LNR2 LNR3 FSM23 Heqrho2. subst; simpl. unfold restrict. 
  apply funsigs_match_arglengths in FSM23.
  rewrite tr_trans; trivial. } 
assert (TR: mkEnviron (ge_of rho3) (ve_of rho3)
                   (tr (combine (map fst (fst sig3)) (map fst (fst sig1))) (te_of rho3))
          = mkEnviron (ge_of rho2) (ve_of rho2)
                   (tr (combine (map fst (fst sig2)) (map fst (fst sig1))) (te_of rho2))).
    { subst rho2. destruct rho3. simpl in *. f_equal. rewrite tr_trans; trivial.
      apply funsigs_match_arglengths; trivial.
      apply funsigs_match_arglengths; trivial. }
exists ts1, x1, (F2 * F1). rewrite TR. split.
+ split; trivial.
  rewrite sepcon_assoc. exists m1, m2; split3; trivial.
+ intros rho'. simpl.
  eapply derives_trans; [ clear Y23 | apply Y23]. 
  unfold local, lift1; simpl. rewrite sepcon_assoc.
  rewrite <- 2 (sepcon_andp_prop F2). apply sepcon_derives; trivial. apply Y12.
Qed.
(*
Lemma funspec_sub_early_refl f: TT |-- funspec_sub_early f f.
Proof. destruct f; split; [ split; trivial | clear H]. intros ts2 x2 rho.
exists ts2, x2, emp. intros y AY m YM [M1 M2]. rewrite emp_sepcon. split; trivial.
intros rho' k WK u necKU U. rewrite emp_sepcon in U. apply U.
Qed.

Lemma funspec_sub_early_trans f1 f2 f3: funspec_sub_early f1 f2 && funspec_sub_early f2 f3 |--
      funspec_sub_early f1 f3.
Proof. destruct f1; destruct f2; destruct f3.
intros w [[X H12] [Y H23]]; destruct X; subst; destruct Y; subst; split; [split; trivial|].
intros ts x rho. 
destruct (H23 ts x rho) as [ts1 [x1 [F X23]]]; clear H23. hnf in X23.
destruct (H12 ts1 x1 rho) as [ts3 [x3 [G X12]]]; clear H12. hnf in X12.
exists ts3, x3, (F * G). intros y WY m YM M.
destruct (X23 _ WY _ YM M) as [A23 B23]; clear X23.
destruct A23 as [m1 [m2 [JM [M1 M2]]]]; destruct (join_level _ _ _ JM) as [Lev_m1 Lev_m2].
assert (Wm2: (level w >= level m2)%nat) by (apply necR_level in YM; omega).
specialize (X12 _ Wm2 _ (necR_refl _)). destruct X12 as [A12 B12].
{ destruct M as [HM1 HM2]; simpl in HM1. split; simpl; trivial. }
split.
+ rewrite sepcon_assoc. exists m1, m2; auto. 
+ intros rho' k MK v KV [Z V]. rewrite sepcon_assoc in V.
  destruct V as [v1 [v2 [JV [V1 V2]]]]; destruct (join_level _ _ _ JV) as [Lev_v1 Lev_v2].
  assert (M2v2: (level m2 >= level v2)%nat) by (apply necR_level in KV; omega).
  specialize (B12 rho' _ M2v2 _ (necR_refl _)). spec B12.
  { split; trivial. }
  assert (Mv: (level m >= level v)%nat) by (apply necR_level in KV; omega).
  apply (B23 rho' _ Mv _ (necR_refl _)). split; [ trivial | exists v1, v2; auto].
Qed.
*)

Lemma funspec_sub_si_refl f (F:list_norepet (map fst (fst (funsig_of_funspec f)))): 
      TT |-- funspec_sub_si f f.
Proof. destruct f; split; [ split; trivial | clear H; intros ts2 x2 rho2].
apply funsigs_match_refl; apply F.
hnf; intros. hnf; intros z YZ [TC HP].
exists ts2, x2, emp. split. 
+ split.
  - destruct rho2. simpl in *. clear - TC.
    unfold tc_environ, typecheck_environ in *. simpl in *. intuition.
    clear - H.
    unfold restrict. red; intros; simpl. destruct (H _ _ H0) as [v [? ?]].
    exists v; split; trivial. forget (fst f) as l. clear - H0 H1.
    induction l; simpl in *. rewrite PTree.gempty in H0. discriminate.
    destruct a as [j tp]; simpl in *. rewrite PTree.gsspec in H0.
    destruct (peq id j); subst. { rewrite H1, Map.gss; trivial. }
    specialize (IHl H0).
    remember (Map.get te j) as w; symmetry in Heqw; destruct w; trivial.
    rewrite Map.gso; auto.
  - rewrite emp_sepcon; apply HP.
+ hnf; intros. rewrite emp_sepcon. simpl; trivial.
Qed.

Lemma funspec_sub_si_trans {f1 f2 f3}:
      funspec_sub_si f1 f2 && funspec_sub_si f2 f3 |-- funspec_sub_si f1 f3.
Proof. 
destruct f1 as [sig1 cc A1 P1 Q1 P1ne Q1ne].
destruct f2 as [sig2 cc2 A2 P2 Q2 P2ne Q2ne].
destruct f3 as [sig3 cc3 A3 P3 Q3 P3ne Q3ne].
intros w [[[FSM12 ?] H12] [[FSM23 ?] H23]]. subst cc3 cc2.
specialize (funsigs_match_trans FSM12 FSM23); intros FSM13.
specialize (funsigs_match_rettypes FSM13); intros RET13.
split. split; trivial.
specialize (funsigs_match_LNR1 FSM12); intros LNR1.
specialize (funsigs_match_LNR2 FSM12); intros LNR2.
specialize (funsigs_match_LNR2 FSM13); intros LNR3.
intros ts3 x3 rho3 y WY m YM M. 
destruct (H23 ts3 x3 rho3 _ WY _ YM M) as [ts2 [x2 [F2 [[TC23 A23] B23]]]]; clear H23. hnf in B23.
destruct A23 as [m1 [m2 [JM [M1 M2]]]]; destruct (join_level _ _ _ JM) as [Lev_m1 Lev_m2].
assert (Wm2: (level w >= level m2)%nat) by (apply necR_level in YM; omega).
remember (mkEnviron (ge_of rho3) (ve_of rho3) (tr (combine (map fst (fst sig3)) (map fst (fst sig2))) (te_of rho3))) as rho2.
destruct (H12 ts2 x2 rho2 _ Wm2 _ (necR_refl _)) as [ts1 [x1 [F1 [[TC12 A12] B12]]]]; clear H12.
{ subst; split; trivial. clear - M2 LNR2 LNR3 FSM23. simpl. unfold restrict. 
  apply funsigs_match_arglengths in FSM23.
  rewrite tr_trans; trivial. } 
assert (TR: mkEnviron (ge_of rho3) (ve_of rho3)
                   (tr (combine (map fst (fst sig3)) (map fst (fst sig1))) (te_of rho3))
          = mkEnviron (ge_of rho2) (ve_of rho2)
                   (tr (combine (map fst (fst sig2)) (map fst (fst sig1))) (te_of rho2))).
    { subst rho2. destruct rho3. simpl in *. f_equal. rewrite tr_trans; trivial. 
      apply funsigs_match_arglengths; trivial.
      apply funsigs_match_arglengths; trivial. }
rewrite TR.
exists ts1, x1, (F2 * F1); split.
+ split. trivial. rewrite sepcon_assoc. exists m1, m2; auto.
+ intros rho' k MK v KV [Z V]. rewrite sepcon_assoc in V.
  destruct V as [v1 [v2 [JV [V1 V2]]]]; destruct (join_level _ _ _ JV) as [Lev_v1 Lev_v2].
  assert (M2v2: (level m2 >= level v2)%nat) by (apply necR_level in KV; omega).
  specialize (B12 rho' _ M2v2 _ (necR_refl _)). spec B12.
  { split; trivial. }
  assert (Mv: (level m >= level v)%nat) by (apply necR_level in KV; omega).
  apply (B23 rho' _ Mv _ (necR_refl _)).
  destruct B12 as [XX YY]. split. trivial.
  exists v1, v2; auto.
Qed.

(*******************end of material moved here from expr.v *******************)

Definition port l1 l2 (P:environ -> mpred) : environ -> mpred :=
  fun rho => P (mkEnviron (ge_of rho) (ve_of rho) (tr (combine l2 l1) (te_of rho))).

Fixpoint normalparams n:list ident :=
  match n with
    O => nil
  | S n' => Pos.of_nat n :: normalparams n'
  end.

Fixpoint check_normalized (l: list (ident * type)):bool :=
  match l with
    nil => true
  | (i,t)::l' => peq i (Pos.of_nat (length l)) && check_normalized l'
  end.

Lemma norm_char: forall l, check_normalized l = true <->
                 map fst l = normalparams (length l).
Proof. induction l; simpl; intros.
split; intros; trivial.
destruct a. simpl in *. forget (match Datatypes.length l with
   | 0%nat => 1%positive
   | S _ => Pos.succ (Pos.of_nat (Datatypes.length l))
   end) as q.
destruct IHl as [IH1 IH2].
destruct (length l); split; intros.
+ clear IH2. simpl in H. destruct (peq i q); simpl in *; [subst | discriminate].
  rewrite IH1; trivial.
+ clear IH1. inv H. destruct (peq q q); rewrite IH2; simpl; trivial. elim n; trivial.
+ clear IH2. rewrite andb_true_iff in H; destruct H. rewrite <- (IH1 H0); clear IH1 H0. f_equal.
  destruct (peq i q); trivial. inv H. 
+ clear IH1. inv H. rewrite IH2, andb_true_r; trivial. clear. destruct (peq q q); trivial. elim n; trivial.
Qed.

Lemma length_normalparams A l: length (normalparams (length l)) = @length A l.
Proof. induction l; simpl; trivial. rewrite IHl; trivial. Qed.

Definition funspec_normalized (fs:funspec):bool := check_normalized (fst (funsig_of_funspec fs)).
 
Lemma normalparams_bound n m: In m (normalparams n) <-> (Pos.to_nat m <= n)%nat.
Proof.
  induction n; simpl.
{ split; intros. simpl in *; omega. specialize (Pos2Nat.is_pos m); omega. } 
destruct n. 
+ split; intros.
  - destruct H; subst.
    * unfold Pos.to_nat. simpl; omega.
    * apply IHn in H. specialize (Pos2Nat.is_pos m); omega.
  - left. apply Pos2Nat.inj. clear IHn.
    assert (Pos.to_nat m = 1)%nat by (specialize (Pos2Nat.is_pos m); omega).
    rewrite H0; clear H H0. reflexivity.
+ split; intros.
  - destruct H. 
    * subst. specialize (SuccNat2Pos.id_succ (S n)). intros. simpl Pos.of_succ_nat in H.
      rewrite Pos.of_nat_succ in H. rewrite H. omega.
    * apply IHn in H. omega.
  - destruct (peq (Pos.succ (Pos.of_nat (S n))) m).
    left; trivial. right. apply IHn; clear IHn.
    destruct (NPeano.Nat.le_gt_cases (Pos.to_nat m) (S n)). trivial. exfalso.
    apply n0; clear n0. rewrite <- Nat2Pos.inj_succ by omega.
    assert (Pos.of_nat (Pos.to_nat m) = m) by apply Pos2Nat.id.
    rewrite <- H1; clear H1. apply Nat2Pos.inj_iff; omega.
Qed. 

Lemma normalparams_LNR n: list_norepet (normalparams n).
Proof. induction n. constructor.
  simpl.
  destruct n.
+ simpl. constructor. simpl. intros N; trivial. trivial.
+  constructor; trivial. intros N. apply normalparams_bound in N.
   rewrite Pos2Nat.inj_succ, Nat2Pos.id in N; omega.
Qed.

Lemma port_super_nonexpansive {A ids1 ids2 P} (NP: @super_non_expansive A P): 
      super_non_expansive (fun ts (x:dependent_type_functor_rec ts A mpred) => port ids1 ids2 (P ts x)).
Proof. hnf; intros. unfold port. rewrite <- NP. trivial. Qed.

Definition func_at (f: funspec): address -> pred rmap :=
  match f with
   | mk_funspec fsig cc A P Q _ _ =>
    fun l => !! list_norepet (map fst (fst fsig)) &&
             pureat (SomeP (SpecTT A) (packPQ P Q)) (FUN (typesig_of_funsig fsig) cc) l
  end.

Definition func_at' (f: funspec) (loc: address) : pred rmap :=
  match f with
   | mk_funspec fsig cc _ _ _ _ _ => 
           EX pp:_, !!(list_norepet (map fst (fst fsig))) &&
           pureat pp (FUN (typesig_of_funsig fsig) cc) loc
  end.
Definition sigcc_at (fsig: funsig) (cc:calling_convention) (loc: address) : pred rmap :=
  EX pp:_, !!(list_norepet (map fst (fst fsig))) && pureat pp (FUN (typesig_of_funsig fsig) cc) loc.

Definition func_ptr_si (f: funspec) (v: val): mpred :=
  EX b:block, !! (v = Vptr b Ptrofs.zero) && (EX gs:funspec, !!(funspec_normalized gs=true) && funspec_sub_si gs f && func_at gs (b, 0)).
(*
Definition func_ptr_early (f: funspec) (v: val): mpred :=
  EX b: block, !! (v = Vptr b Ptrofs.zero) && (EX gs: funspec, funspec_sub_early gs f && func_at gs (b, 0)).
*)
Definition func_ptr (f: funspec) (v: val): mpred :=
  EX b:block, !! (v = Vptr b Ptrofs.zero) && (EX gs:funspec, !!(funspec_normalized gs=true /\ funspec_sub gs f) && func_at gs (b, 0)).
(*
Lemma func_ptr_early_func_ptr_si f v: func_ptr_early f v |-- func_ptr_si f v.
Proof. apply exp_derives; intros b. apply andp_derives; trivial.
 apply exp_derives; intros gs. apply andp_derives; trivial. apply funspec_sub_early_sub_si.
Qed.
*)

Lemma funsigs_match_siggcc_eq {f1 f2} (FSM: funsigs_match f1 f2=true):
      sigcc_at f1 = sigcc_at f2.
Proof. unfold sigcc_at; rewrite (funsigs_match_typesigs_eq FSM).
  extensionality cc. extensionality loc. f_equal. extensionality pp. f_equal.
  apply pred_ext; intros w; simpl; intros.
  apply (funsigs_match_LNR2 FSM). 
  apply (funsigs_match_LNR1 FSM). 
Qed.

Lemma func_ptr_fun_ptr_si f v: func_ptr f v |-- func_ptr_si f v.
Proof. apply exp_derives; intros b. apply andp_derives; trivial.
 apply exp_derives; intros gs. apply andp_derives; trivial.
 intros w [W1 W2]; split; [ | apply funspec_sub_sub_si' ]; trivial.
Qed.

Lemma func_ptr_si_mono fs gs v: 
      funspec_sub_si fs gs && func_ptr_si fs v |-- func_ptr_si gs v.
Proof. unfold func_ptr_si. rewrite exp_andp2. apply exp_derives; intros b.
  rewrite andp_comm, andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm, exp_andp2. apply exp_derives; intros hs.
  intros w [W1 [[W2 W3] W4]]; simpl.
  split; trivial. split; trivial. eapply funspec_sub_si_trans; split; eassumption.
Qed.
(*
Lemma func_ptr_early_mono fs gs v: 
      funspec_sub_early fs gs && func_ptr_early fs v |-- func_ptr_early gs v.
Proof.  unfold func_ptr_early. rewrite exp_andp2. apply exp_derives; intros b.
  rewrite andp_comm, andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm, exp_andp2. apply exp_derives; intros hs.
  rewrite <- andp_assoc. apply andp_derives; trivial.
  rewrite andp_comm. apply funspec_sub_early_trans.
Qed.
*)
Lemma func_ptr_mono fs gs v: funspec_sub fs gs -> 
      func_ptr fs v |-- func_ptr gs v.
Proof. intros. unfold func_ptr. apply exp_derives; intros b.
  apply andp_derives; trivial. apply exp_derives; intros hs.
  apply andp_derives; trivial. 
  intros w [W1 W2]. split; trivial. eapply funspec_sub_trans; eassumption.
Qed.
(*
Lemma funspec_sub_early_implies_func_prt_si_mono fs gs v: 
      funspec_sub_early fs gs && func_ptr_si fs v |-- func_ptr_si gs v.
Proof. 
  eapply derives_trans. 2: apply func_ptr_si_mono.
  apply andp_derives. 2: apply derives_refl. apply funspec_sub_early_sub_si.
Qed.
*)
Lemma funspec_sub_implies_func_prt_si_mono' fs gs v: 
      !!(funspec_sub fs gs) && func_ptr_si fs v |-- func_ptr_si gs v.
Proof.
  eapply derives_trans. 2: apply func_ptr_si_mono.
  apply andp_derives. 2: apply derives_refl. 
Search funspec_sub funspec_sub_si. apply funspec_sub_sub_si'. 
Qed.

Lemma funspec_sub_implies_func_prt_si_mono fs gs v: funspec_sub fs gs ->
      func_ptr_si fs v |-- func_ptr_si gs v.
Proof. intros. 
  eapply derives_trans. 2: apply funspec_sub_implies_func_prt_si_mono'. 
  apply andp_right. 2: apply derives_refl. hnf; intros; apply H. 
Qed.

Definition NDmk_funspec (f: funsig) (cc: calling_convention)
  (A: Type) (Pre Post: A -> environ -> mpred): funspec :=
  mk_funspec f cc (rmaps.ConstType A) (fun _ => Pre) (fun _ => Post)
             (const_super_non_expansive _ _) (const_super_non_expansive _ _).

Lemma funsigs_match_type_of_params {f g} (M:funsigs_match f g = true): 
      type_of_params (fst f) = type_of_params (fst g).
Proof.
  apply funsigs_match_argtypes in M.
  destruct f; destruct g; simpl in *.
  generalize dependent l0.
  induction l; simpl; destruct l0; simpl; trivial; intros; try discriminate.
  destruct a; destruct p; simpl in *; subst.
  inv M. rewrite (IHl _ H1). auto.
Qed.

Lemma type_of_funspec_sub:
  forall fs1 fs2, funspec_sub fs1 fs2 ->
  type_of_funspec fs1 = type_of_funspec fs2.
Proof.
intros.
destruct fs1, fs2; destruct H as [? [? _]]; subst; simpl.
rewrite (funsigs_match_type_of_params H), (funsigs_match_rettypes H); trivial.
Qed.

Lemma type_of_funspec_sub_si fs1 fs2:
  funspec_sub_si fs1 fs2 |-- !!(type_of_funspec fs1 = type_of_funspec fs2).
Proof.
intros w W.
destruct fs1, fs2. destruct W as [[? ?] _]. subst; simpl.
rewrite (funsigs_match_type_of_params H), (funsigs_match_rettypes H); trivial.
Qed.
(*
Lemma type_of_funspec_sub_early fs1 fs2:
  funspec_sub_early fs1 fs2 |-- !!(type_of_funspec fs1 = type_of_funspec fs2).
Proof.
eapply derives_trans. apply funspec_sub_early_sub_si. apply type_of_funspec_sub_si.
Qed.
*)

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

Fixpoint sepcon_list {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AG: ageable A} {AgeA: Age_alg A}
   (p: list (pred A)) : pred A :=
 match p with nil => emp | h::t => h * sepcon_list t end.

Definition typed_true (t: type) (v: val)  : Prop := strict_bool_val v t
= Some true.

Definition typed_false (t: type)(v: val) : Prop := strict_bool_val v t =
                                                   Some false.

Definition subst {A} (x: ident) (v: val) (P: environ -> A) : environ -> A :=
  fun s => P (env_set s x v).

Lemma func_ptr_isptr: forall spec f, func_ptr spec f |-- !! val_lemmas.isptr f.
Proof.
  intros.
  unfold func_ptr.
  destruct spec. intros ? ?. destruct H as [b [Hb _]]; simpl in Hb; subst. unfold val_lemmas.isptr; simpl; trivial.
Qed.
Lemma func_ptr_si_isptr: forall spec f, func_ptr_si spec f |-- !! val_lemmas.isptr f.
Proof.
  intros.
  unfold func_ptr_si.
  destruct spec. intros ? ?. destruct H as [b [Hb _]]; simpl in Hb; subst. unfold val_lemmas.isptr; simpl; trivial.
Qed.
(*
Lemma func_ptr_early_isptr: forall spec f, func_ptr_early spec f |-- !! val_lemmas.isptr f.
Proof.
  intros.
  unfold func_ptr_early.
  destruct spec. intros ? ?. destruct H as [b [Hb _]]; simpl in Hb; subst. unfold val_lemmas.isptr; simpl; trivial.
Qed.*)
Lemma  subst_extens:
 forall a v P Q, (forall rho, P rho |-- Q rho) -> forall rho, subst a v P rho |-- subst a v Q rho.
Proof.
unfold subst, derives.
simpl;
auto.
Qed.

Lemma approx_sepcon: forall (P Q: mpred) n,
  approx n (P * Q) =
  approx n P *
  approx n Q.
Proof.
  intros.
  change sepcon with predicates_sl.sepcon in *.
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    destruct H as [? [y [z [? [? ?]]]]].
    exists y, z; split; auto.
    split; split; auto.
    - apply age_sepalg.join_level in H0.
      omega.
    - apply age_sepalg.join_level in H0.
      omega.
  + intros w ?.
    simpl in *.
    destruct H as [y [z [? [[? ?] [? ?]]]]].
    split.
    - apply age_sepalg.join_level in H.
      omega.
    - exists y, z.
      split; [| split]; auto.
Qed.

Lemma approx_orp n P Q: approx n (orp P Q) = orp (approx n P) (approx n Q).
Proof.
  apply pred_ext; intros w W.
  + destruct W. destruct H0;  [left | right]; split; trivial.
  + destruct W; destruct H; split; trivial. left; trivial. right; trivial.
Qed.

Lemma approx_andp: forall (P Q: mpred) n,
  approx n (P && Q) =
  approx n P &&
  approx n Q.
Proof.
  intros.
  change andp with (@predicates_hered.andp compcert_rmaps.RML.R.rmap _) in *.
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    tauto.
  + intros w ?.
    simpl in *.
    tauto.
Qed.

Lemma approx_exp: forall A (P: A -> mpred) n,
  approx n (exp P) =
  EX a: A, approx n (P a).
Proof.
  intros.
(*  change (@exp _ Nveric A) with (@predicates_hered.exp compcert_rmaps.RML.R.rmap _ A) in *. *)
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    firstorder.
  + intros w ?.
    simpl in *.
    firstorder.
Qed.

Lemma approx_allp: forall A (P: A -> mpred) n,
  A ->
  approx n (allp P) =
  ALL a: A, approx n (P a).
Proof.
  intros.
  apply predicates_hered.pred_ext.
  + intros w ?.
    simpl in *.
    firstorder.
  + intros w ?.
    simpl in *.
    firstorder.
Qed.

Lemma approx_jam {B: Type} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l}) (P Q: B -> mpred) n (b : B) :
  approx n (jam S P Q b) =
  jam S (approx n oo P) (approx n oo Q) b.
Proof.
  apply predicates_hered.pred_ext.
  + intros w ?. simpl in *. if_tac; firstorder.
  + intros w ?. simpl in *. if_tac; firstorder.
Qed.
(*(*
Lemma approx_func_ptr: forall (A: Type) fsig0 cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
  approx n (func_ptr (NDmk_funspec fsig0 cc A P Q) v) = approx n (func_ptr (NDmk_funspec fsig0 cc A (fun a rho => approx n (P a rho)) (fun a rho => approx n (Q a rho))) v).
Proof.
  intros.
  unfold func_ptr.
  rewrite !approx_exp; f_equal; extensionality b.
  rewrite !approx_andp; f_equal.
  unfold func_at, NDmk_funspec.
  simpl.
  apply pred_ext; intros w; simpl; intros [? ?]; split; auto.
  + (*destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros ts2 a rho m WM u necU U. simpl in U.
    exists ts2, a, emp. rewrite emp_sepcon. split; intros; [ apply U | intros rho' k UP j KJ J; hnf].
    rewrite emp_sepcon in J. simpl in J. intuition. apply necR_level in KJ. apply necR_level in necU. omega. *)
    destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros ts2 a rho m WM u necU U. simpl in U.
    exists ts2, a, emp. rewrite emp_sepcon. split; intros; [ apply U | intros rho' k UP j KJ z JZ HZ; hnf].
    rewrite emp_sepcon in HZ. simpl in HZ. intuition. apply necR_level in JZ. apply laterR_level in UP. omega.
  + destruct H0 as [gs [SUBS H0]]. exists gs; split; trivial.
    eapply funspec_sub_trans; split. apply SUBS. clear SUBS H0; hnf.
    split. split; trivial.
    intros ts2 a rho m WM u necU U. simpl in U.
    exists ts2, a, emp. rewrite emp_sepcon. split; intros. 
    - apply necR_level in necU. split. omega. apply U.
    - (*intros rho' k UP j KJ J.
      rewrite emp_sepcon in J. simpl in J. apply J. *)
      intros rho' k UP j KJ z JZ HZ. hnf in HZ.
      rewrite emp_sepcon in HZ. simpl in HZ. apply HZ. 
Qed. *)*)
(*
Lemma approx_func_ptr_early: forall (A: Type) fsig0 cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
  approx n (func_ptr_early (NDmk_funspec fsig0 cc A P Q) v) = approx n (func_ptr_early (NDmk_funspec fsig0 cc A (fun a rho => approx n (P a rho)) (fun a rho => approx n (Q a rho))) v).
Proof.
  intros.
  unfold func_ptr_early.
  rewrite !approx_exp; f_equal; extensionality b.
  rewrite !approx_andp; f_equal.
  unfold func_at, NDmk_funspec.
  simpl.
  apply pred_ext; intros w; simpl; intros [? [g [G ?]]]; split; auto.
  + exists g. split; trivial. destruct g; clear H0; hnf; hnf in G; destruct G; split; trivial.
    intros ts x rho. destruct (H1 ts x rho) as [ts1 [x1 [F HF]]]; clear H1.
    exists ts1, x1, F. hnf; intros y Y z YZ [Z1 Z2]; specialize (HF _ Y _ YZ). apply approx_p in Z2.
    destruct HF as [HF1 HF2]. { split; trivial. }
    split. apply HF1. intros rho' u YU m UM M. specialize (HF2 rho' u YU m UM M).
    apply approx_lt; trivial. apply necR_level in UM. apply necR_level in YZ. omega.
  + exists g; split; trivial. destruct g; clear H0; hnf; hnf in G; destruct G; split; trivial.
    intros ts x rho. destruct (H1 ts x rho) as [ts1 [x1 [F HF]]]; clear H1.
    exists ts1, x1, F. hnf; intros y Y z YZ [Z1 Z2]; specialize (HF _ Y _ YZ).
    destruct HF as [HF1 HF2]. { split; trivial. apply approx_lt; trivial. apply necR_level in YZ. omega. }
    split. apply HF1. intros rho' u YU m UM M. specialize (HF2 rho' u YU m UM M).
    apply approx_p in HF2. trivial.
Qed.*)

Lemma approx_func_ptr_si: forall (A: Type) fs cc (P Q: A -> environ -> mpred) (v: val) (n: nat),
  approx n (func_ptr_si (NDmk_funspec fs cc A P Q) v) = approx n (func_ptr_si (NDmk_funspec fs cc A (fun a rho => approx n (P a rho)) (fun a rho => approx n (Q a rho))) v).
Proof.
  intros.
  unfold func_ptr_si.
  rewrite !approx_exp. f_equal. extensionality b.
  rewrite !approx_andp; f_equal.
  rewrite !approx_exp. f_equal. extensionality gs.
  rewrite !approx_andp; f_equal. f_equal.
  unfold func_at, NDmk_funspec.
  simpl.
  apply pred_ext; intros w; simpl; intros [? SUBS]; split; trivial.
  + (*destruct H0 as [SUBS H0]. exists gs; split; trivial. *)
    eapply funspec_sub_si_trans; split. apply SUBS. (* apply SUBS.*)
    apply funspec_sub_si_funsigs_match in SUBS. apply funsigs_match_LNR2 in SUBS. simpl in SUBS.
    (*clear H0 gs.*)
    split. 
    - split; [ apply funsigs_match_refl | ]; trivial.
    - intros ts x rho m WM u necU [TC U]. (*[U1 U2]]. *)simpl in TC.
      exists ts, x, emp. split.
      * rewrite emp_sepcon; simpl. apply approx_p in U. split; trivial.
        unfold tc_environ, typecheck_environ in *. simpl in *. intuition.
        unfold typecheck_temp_environ in *; intros. clear H2 H3 U. clear - H0 H1 SUBS.
        destruct (H0 _ _ H1) as [q [? ?]]; clear H0. exists q; split; trivial.
        forget (fst fs) as l. clear - SUBS H H1. induction l.
        { simpl in *. rewrite PTree.gempty in H1. discriminate. }
        simpl in H1. inv SUBS. destruct a as [i t]; simpl in *.
        rewrite PTree.gsspec in H1. destruct (peq id i); subst.
        ++ inv H1. rewrite H, Map.gss; trivial.
        ++ specialize (IHl H4 H1).
           remember (Map.get (te_of rho) i) as w; symmetry in Heqw.
           destruct w; trivial. rewrite Map.gso; trivial. auto. 
      * intros rho' y UY k YK [TCK K]; hnf; intros. rewrite emp_sepcon in K. simpl in TCK.
        apply necR_level in necU. apply necR_level in YK.
        simpl. split. apply TCK. split; [ omega | apply K]. 
  + eapply funspec_sub_si_trans; split. apply SUBS.

    apply funspec_sub_si_funsigs_match in SUBS. apply funsigs_match_LNR2 in SUBS. simpl in SUBS.
    (*clear H0 gs.*)
    split. 
    - split; [ apply funsigs_match_refl | ]; trivial.
    - intros ts x rho m WM u necU [TC U]. (*[U1 U2]]. *)simpl in TC.
      exists ts, x, emp. split.
      * rewrite emp_sepcon; simpl. apply necR_level in necU. split. 2: split; [omega | trivial].
        unfold tc_environ, typecheck_environ in *. simpl in *. intuition.
        unfold typecheck_temp_environ in *; intros. clear H2 H3 U. clear - H0 H1 SUBS.
        destruct (H0 _ _ H1) as [q [? ?]]; clear H0. exists q; split; trivial.
        forget (fst fs) as l. clear - SUBS H H1. induction l.
        { simpl in *. rewrite PTree.gempty in H1. discriminate. }
        simpl in H1. inv SUBS. destruct a as [i t]; simpl in *.
        rewrite PTree.gsspec in H1. destruct (peq id i); subst.
        ++ inv H1. rewrite H, Map.gss; trivial.
        ++ specialize (IHl H4 H1).
           remember (Map.get (te_of rho) i) as w; symmetry in Heqw.
           destruct w; trivial. rewrite Map.gso; trivial. auto. 
      * intros rho' y UY k YK [TCK K]; hnf; intros. rewrite emp_sepcon in K. simpl in TCK.
        apply necR_level in necU. apply necR_level in YK. apply approx_p in K.
        simpl. split. apply TCK. apply K.
Qed. 

Definition funspecs_assert (FunSpecs: PTree.t funspec): assert :=
 fun rho =>
   (ALL  id: ident, ALL fs:funspec,  !! (FunSpecs!id = Some fs) -->
              EX b:block,
                   !! (funspec_normalized fs=true /\ Map.get (ge_of rho) id = Some b) && func_at fs (b,0))
 &&  (ALL  b: block, ALL fsig:funsig, ALL cc: calling_convention, sigcc_at fsig cc (b,0) -->
             EX id:ident, !! (Map.get (ge_of rho) id = Some b)
                             && !! exists fs, FunSpecs!id = Some fs).

Definition globals_only (rho: environ) : environ := (mkEnviron (ge_of rho) (Map.empty _) (Map.empty _)).

Fixpoint make_args (il: list ident) (vl: list val) (rho: environ)  :=
  match il, vl with
  | nil, nil => globals_only rho
  | i::il', v::vl' => env_set (make_args il' vl' rho) i v
   | _ , _ => rho
  end.

Lemma same_FS_funspecs_assert:
  forall FS1 FS2,
     (forall id, FS1 ! id = FS2 ! id) ->
              funspecs_assert FS1 = funspecs_assert FS2.
Proof.
assert (forall FS FS' rho,
             (forall id, FS ! id = FS' ! id) ->
             funspecs_assert FS rho |-- funspecs_assert FS' rho).
{ intros. intros w [? ?]. split.
  + intro id. rewrite <- (H id); auto.
  + intros loc sig cc w' Hw' HH. hnf in H0. destruct (H1 loc sig cc w' Hw' HH)  as [id ID].
    exists id; rewrite <- (H id); auto. }
intros.
extensionality rho.
apply pred_ext; apply H; intros; auto.
Qed.

Lemma funspecs_assert_rho:
  forall G rho rho', ge_of rho = ge_of rho' -> funspecs_assert G rho |-- funspecs_assert G rho'.
Proof. unfold funspecs_assert; intros. rewrite H; auto. Qed.

(************** INTERSECTION OF funspecs -- case ND  ************************)

(* --------------------------------- Binary case: 2 specs only ----------  *)

Definition funspec_intersection_ND fA cA A PA QA FSA (HFSA: FSA = NDmk_funspec fA cA A PA QA) 
                    fB cB B PB QB FSB (HFSB: FSB = NDmk_funspec fB cB B PB QB): option funspec :=
(if (funsigs_match fA fB && eq_dec cA cB) 
  then Some (NDmk_funspec fB cB (A+B) 
         (fun x => match x with inl a => (port (map fst (fst fA)) (map fst (fst fB)) (PA a)) | inr b => PB b end)
         (fun x => match x with inl a => QA a | inr b => QB b end))
  else None)%bool.
(*
Definition funspec_intersection_ND fA cA A PA QA FSA (HFSA: FSA = NDmk_funspec fA cA A PA QA) 
                    fB cB B PB QB FSB (HFSB: FSB = NDmk_funspec fB cB B PB QB): option funspec.
destruct (eq_dec fA fB); subst.
+ destruct (eq_dec cA cB); subst.
  - apply Some. eapply (NDmk_funspec fB cB (A+B) 
         (fun x => match x with inl a => PA a | inr b => PB b end)
         (fun x => match x with inl a => QA a | inr b => QB b end)).
  - apply None.
+ apply None.
Defined.*)

Lemma make_tycontext_t_elim: forall {l i t}, (make_tycontext_t l nil) ! i = Some t ->
      In i (map fst l).
Proof.
  induction l; simpl; intros.
+ rewrite PTree.gempty in H; discriminate.
+ rewrite PTree.gsspec in H. destruct (peq i (fst a)); subst. left; trivial. right; eauto.
Qed.

Lemma tc_environ_restrict rho: forall fs (LNR: list_norepet (map fst (fst fs)))
        (TC : tc_environ (funsig_tycontext fs) rho),
      tc_environ (funsig_tycontext fs)
         (mkEnviron (ge_of rho) (ve_of rho) (restrict (map fst (fst fs)) (te_of rho))).
Proof.
  unfold tc_environ, typecheck_environ; simpl; intros. intuition. clear - LNR H.
  intros i t Hi. destruct (H _ _ Hi) as [v [Mv Tv]]; clear H. exists v; split; trivial.
  apply make_tycontext_t_elim in Hi. unfold restrict. forget (map fst (fst fs)) as l.
  induction l; simpl; [ inv Hi | inv LNR; destruct Hi; subst].
  + clear IHl. rewrite Mv, Map.gss; trivial.
  + destruct (Map.get (te_of rho) a); auto. rewrite Map.gso; auto.
    intros N; subst. contradiction.
Qed.

Lemma funsigs_match_tc_environ {fA fB:funsig} (FSM: funsigs_match fB fA = true) rho
      (TC: tc_environ (funsig_tycontext fA) rho):
      tc_environ (funsig_tycontext fB) (mkEnviron (ge_of rho) (ve_of rho) (tr (combine (map fst (fst fA)) (map fst (fst fB))) (te_of rho))).
Proof.
  unfold tc_environ, typecheck_environ in *; simpl in *. intuition.
  clear - FSM H; red; intros.
  specialize (funsigs_match_LNR1 FSM); intros LNR1.
  specialize (funsigs_match_LNR2 FSM); intros LNR2.
  apply funsigs_match_argtypes in FSM.
  destruct fA as [argsA rtA]. destruct fB as [argsB rtB].
  simpl in *. generalize dependent argsB.
  induction argsA; simpl; intros; destruct argsB; simpl in *; try discriminate.
  { rewrite PTree.gempty in H0; discriminate. }
  inv LNR1; inv LNR2. inv FSM.
  destruct a as [a ta]. destruct p as [b tb]. simpl in *. subst.
  rewrite PTree.gsspec in H0. destruct (peq id b); subst.
  + inv H0. specialize (H a); rewrite PTree.gss in H.
    destruct (H ty) as [? [? ?]]; trivial.
    rewrite H0, Map.gss. exists x; split; trivial.
  + spec IHargsA. { intros i t Hi. apply (H i t). rewrite PTree.gso; trivial.
                    intros N; subst. clear - H5 Hi. apply make_tycontext_t_elim in Hi. auto. }
    destruct (IHargsA H6 argsB) as [v [MV TV]]; clear IHargsA; trivial. exists v; split; trivial.
    remember (Map.get (te_of rho) a) as w; symmetry in Heqw; destruct w; trivial.
    rewrite Map.gso; trivial. auto.
Qed.

(*The two rules S-inter1 and S-inter2 from page 206 of TAPL*)
Lemma funspec_intersection_ND_sub {fA cA A PA QA fB cB B PB QB} f1 F1 f2 F2 f
      (I: funspec_intersection_ND fA cA A PA QA f1 F1 fB cB B PB QB f2 F2 = Some f):
  funspec_sub f f1 /\ funspec_sub f f2.
Proof.
  subst. unfold funspec_intersection_ND in I. unfold NDmk_funspec in I.
  remember (funsigs_match fA fB) as b; symmetry in Heqb;
  destruct b; simpl in I; [ | discriminate].
  destruct (eq_dec cA cB); simpl in I; [subst cB | discriminate].
  rewrite funsigs_match_symm in Heqb. inv I.
  specialize (funsigs_match_LNR1 Heqb); intros LNR1.
  specialize (funsigs_match_LNR2 Heqb); intros LNR2.
  specialize (funsigs_match_argtypes Heqb); intros TPS.
  specialize (funsigs_match_arglengths Heqb); intros ARGSLEN.
  split.
  + split. trivial. split. trivial. intros. simpl. intros w [W1 W2].
    exists ts2, (inl x2), emp. rewrite emp_sepcon.
    split.
    - simpl. split. 
      * apply funsigs_match_tc_environ; trivial. 
      * unfold port; destruct rho2; simpl in *. rewrite tr_trans; trivial. intuition.
    - simpl; intros; rewrite emp_sepcon; trivial.
  + split3; trivial. apply funsigs_match_refl; trivial.
    simpl; intros. intros w [W1 W2].
    exists ts2, (inr x2), emp. rewrite emp_sepcon.
    split.
    - simpl. split; [ | apply W2].
      unfold tc_environ, typecheck_environ in *; simpl in *. intuition.
      clear - H LNR1. forget (fst fB) as l. red; intros. destruct (H _ _ H0) as [v [Mv Tv]]; clear H.
      exists v; split; trivial. clear Tv.
      induction l; simpl in *. rewrite PTree.gempty in H0. discriminate.
      rewrite PTree.gsspec in H0. inv LNR1.
      destruct (peq id (fst a)); subst. inv H0. rewrite Mv, Map.gss; trivial.
      specialize (IHl H3 H0).
      remember (Map.get (te_of rho2) (fst a)) as w; destruct w; trivial.
      rewrite Map.gso; auto.
    - simpl; intros. rewrite emp_sepcon. trivial.
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_intersection_ND_sub3 {fA cA A PA QA fB cB B PB QB fC cC C PC QC} f1 F1 f2 F2 f
      (I: funspec_intersection_ND fA cA A PA QA f1 F1 fB cB B PB QB f2 F2 = Some f) g
      (G: g = NDmk_funspec fC cC C PC QC):
  funspec_sub g f1 -> funspec_sub g f2 -> funspec_sub g f.
Proof.
  subst. intros. destruct H as [? [? G1]]; subst cA. destruct H0 as [? [? G2]]; subst cB.
  unfold funspec_intersection_ND in I.
  remember (funsigs_match fA fB && eq_dec cC cC)%bool as b.
  destruct b; inv I.
  symmetry in Heqb; apply andb_true_iff in Heqb; destruct Heqb as [? _].
  simpl. split3; trivial.
  intros.
  destruct x2 as [a | b]; auto. clear G2. simpl in G1.
  intros w [W1 W2]. unfold port, restrict in W2. simpl in W2.
  specialize (funsigs_match_LNR1 H1); intros LNR1.
  specialize (funsigs_match_LNR2 H1); intros LNR2.
  specialize (funsigs_match_arglengths H1); intros LEN.
  rewrite tr_trans in W2; trivial.
  destruct (G1 ts2 a
     (mkEnviron (ge_of rho2) (ve_of rho2)
        (tr (combine (map fst (fst fB)) (map fst (fst fA))) (te_of rho2)))w)
    as [ts1 [c [FR [[TC pre] post]]]]; clear G1.
  + split.
    - apply funsigs_match_tc_environ; trivial.
    - unfold restrict in *; simpl in *; rewrite tr_trans; trivial.
  + simpl in TC. exists ts1, c, FR; split; trivial; clear post.
    specialize (funsigs_match_LNR1 H0); intros LNRc.
    specialize (funsigs_match_arglengths H); intros LenCA.
    split.
    - rewrite tr_trans in TC; trivial.
    - eapply sepcon_derives; [ apply derives_refl | clear pre TC | apply pre].
      simpl. rewrite tr_trans; trivial.
Qed.

(*-------------------- ND case, specification Sigma families --------------------- *)

Definition funspec_Sigma_ND (cc: calling_convention)  (I:Type) (sigs:I -> funsig) (A : I -> Type)
           (Pre Post: forall i, A i -> environ -> mpred) (i:I)
           (Hsigs: forall j, funsigs_match (sigs i) (sigs j) = true):funspec.
Proof.
  apply (NDmk_funspec (sigs i) cc (sigT A)).
  intros [j Aj]; apply (port (map fst (fst (sigs j))) (map fst (fst (sigs i))) (Pre _ Aj)).
  intros [j Aj]; apply (Post _ Aj). 
Defined.

(*The two rules S-inter1 and S-inter2 from page 206 of TAPL*)
Lemma funspec_Sigma_ND_sub cc I sigs A Pre Post i Hsigs j:
  funspec_sub (funspec_Sigma_ND cc I sigs A Pre Post i Hsigs) (NDmk_funspec (sigs j) cc (A j) (Pre j) (Post j)).
Proof.
  unfold funspec_Sigma_ND.
  split3; [ auto | trivial | intros; simpl in *].
  exists ts2, (existT A j x2), emp. rewrite emp_sepcon.
  specialize (Hsigs j).
  specialize (funsigs_match_LNR1 Hsigs); intros LNR1.
  specialize (funsigs_match_LNR2 Hsigs); intros LNR2.
  destruct H; split; [ split | simpl; intros; rewrite emp_sepcon; trivial].
  + clear H0; simpl in *. apply funsigs_match_tc_environ; trivial.
  + specialize (funsigs_match_arglengths Hsigs); intros ARGSLEN.
    unfold port; destruct rho2; simpl in *. rewrite tr_trans; trivial. intuition.
Qed.

(*Rule S-inter3 from page 206 of TAPL*)
Lemma funspec_Sigma_ND_sub3 cc I sigs A Pre Post i Hsigs g
      (HI: forall j,  funspec_sub g (NDmk_funspec (sigs j) cc (A j) (Pre j) (Post j))):
  funspec_sub g (funspec_Sigma_ND cc I sigs A Pre Post i Hsigs).
Proof.
  assert (HIi := HI i).
  destruct g. destruct HIi as [? [? Hi]]; subst c.
  split. trivial. split. trivial.
  simpl; intros. clear (*i*) Hi. destruct x2 as [j aj].
  specialize (HI j). destruct HI as [_ [_ Hj]].
  specialize (Hsigs j); rewrite funsigs_match_symm in Hsigs.
  intros w [W1 W2]. unfold port, restrict in W2. simpl in W2.
  specialize (funsigs_match_LNR1 Hsigs); intros LNR1.
  specialize (funsigs_match_LNR2 Hsigs); intros LNR2.
  specialize (funsigs_match_arglengths Hsigs); intros LEN.
  rewrite tr_trans in W2; trivial.
  destruct (Hj ts2 aj
     (mkEnviron (ge_of rho2) (ve_of rho2)
        (tr (combine (map fst (fst (sigs i))) (map fst (fst (sigs j)))) (te_of rho2)))w)
    as [ts1 [c [FR [[TC pre] post]]]]; clear Hj.
  + split.
    - apply funsigs_match_tc_environ; trivial.
    - unfold restrict in *; simpl in *; rewrite tr_trans; trivial.
  + simpl in TC. exists ts1, c, FR; split; trivial; clear post.
    specialize (funsigs_match_LNR1 H); intros LNRc.
    specialize (funsigs_match_arglengths H); intros LenC.
    unfold ident in *.
    split.
    - rewrite tr_trans in TC; trivial. rewrite LenC, LEN; trivial.
    - eapply sepcon_derives; [ apply derives_refl | clear pre TC | apply pre].
      simpl. rewrite tr_trans; trivial. rewrite LenC, LEN; trivial.
Qed.

(*Specialization of funspec_Sigma_ND to binary case, i.e. I=bool*)
Program Definition BinarySigma cc (sigA sigB: funsig) (A B:Type)
        (PA QA: A -> environ ->mpred) (PB QB:B -> environ -> mpred)
        (FSM: funsigs_match sigA sigB = true): funspec :=
  funspec_Sigma_ND cc bool (fun b => if b then sigA else sigB) _ _ _ _ _.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? b. destruct b. apply A. apply B.
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? b X rho.
  destruct b; simpl in X. apply (PA X rho). apply (PB X rho).
Defined.
Next Obligation.
  intros ? ? ? ? ? ? ? ? ? ? b X rho.
  destruct b; simpl in X. apply (QA X rho). apply (QB X rho).
Defined.
Next Obligation.
  intros. apply true.
Defined.
Next Obligation.
  intros. simpl.
  destruct j; trivial.
  apply funsigs_match_LNR1 in FSM. apply funsigs_match_refl; trivial.
Defined. 
(*
Definition funspecspec_sub_antisym (f g: funspec):= funspec_sub f g /\ funspec_sub g f.
  
Lemma Intersection_BinarySigma sigA ccA A PA QA fsA PrfA sigB ccB B PB QB fsB PrfB f
      (F:  funspec_intersection_ND sigA ccA A PA QA fsA PrfA sigB ccB B PB QB fsB PrfB  = Some f):
  sigA=sigB /\ ccA=ccB /\
  funspecspec_sub_antisym f (BinarySigma sigA ccA A B PA QA PB QB).
Proof.
  unfold funspec_intersection_ND in F.
  destruct (eq_dec sigA sigB); [ subst sigA; split; trivial | discriminate].
  destruct (eq_dec ccA ccB); [ inv F; split; trivial | discriminate]. 
  split.
  + split. trivial. split. trivial. simpl; intros. destruct x2 as [i p].
    destruct i; simpl in *.
  - exists ts2, (inl p), emp. rewrite emp_sepcon. split; simpl. apply H.
    intros. rewrite emp_sepcon. intros u U; apply U.
  - exists ts2, (inr p), emp. rewrite emp_sepcon. split; simpl. apply H.
    intros. rewrite emp_sepcon. intros u U; apply U. 
    + split. trivial. split. trivial. intros. intros u [L U]. destruct x2.
  - exists ts2, (existT (BinarySigma_obligation_1 A B) true a), emp.
    rewrite emp_sepcon. simpl; split. apply U. intros. rewrite emp_sepcon.
    intros w W. apply W.
  -  exists ts2, (existT (BinarySigma_obligation_1 A B) false b), emp.
     rewrite emp_sepcon. simpl; split. apply U. intros. rewrite emp_sepcon.
     intros w W. apply W.
Qed.*)
(*
Lemma Intersection_sameSigCC_Some sig cc A PA QA fsA PrfA B PB QB fsB PrfB:
  ~ funspec_intersection_ND sig cc A PA QA fsA PrfA sig cc B PB QB fsB PrfB  = None.
Proof.
  intros N. unfold funspec_intersection_ND in N.
  rewrite funsigs_match_refl, andb_true_l in N.
  destruct (proj_sumbool (eq_dec cc cc)); trivial. discriminate. if_tac in N.
  rewrite if_true in N; trivial. discriminate.
Qed.
*)
(*-------------------Bifunctor version, binary case ------------*)

Definition binarySUM (*f f2*) {A1 A2}
           (P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred)
           (P2: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred):
  forall ts : list Type, 
    (dependent_type_functor_rec ts (AssertTT (@SigType bool 
      (fun b => if b then A1 else A2)))) mpred.
Proof.
  intros ts X rho. simpl in *. specialize (P1 ts). specialize (P2 ts).
  simpl in *. destruct X as [b B]; destruct b; simpl in B.
  apply (P1 B rho). apply (P2 B rho). 
Defined.

Lemma binarySUM_ne {A1 A2}
           {P1: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A1)) mpred}
           {P2: forall ts : list Type, (dependent_type_functor_rec ts (AssertTT A2)) mpred}
           (P1_ne: super_non_expansive P1) (P2_ne: super_non_expansive P2):
  super_non_expansive (binarySUM P1 P2).
Proof.
  hnf; simpl; intros. unfold binarySUM. destruct x as [b B].
  destruct b; simpl in B. apply P1_ne. apply P2_ne. 
Qed.

Definition binarySUMport {A1 A2}
           (P1: forall ts : list Type, dependent_type_functor_rec ts (AssertTT A1) mpred)
           (P2: forall ts : list Type, dependent_type_functor_rec ts (AssertTT A2) mpred)
           (f1 f2:funsig):
  forall ts : list Type, 
    (dependent_type_functor_rec ts (AssertTT(@SigType bool 
      (fun b => if b then A1 else A2)))) mpred.
Proof.
  intros ts X rho. simpl in *. specialize (P1 ts). specialize (P2 ts).
  simpl in *. destruct X as [b B]; destruct b; simpl in B.
  apply (P1 B rho). 
  apply ((port (map fst (fst f2)) (map fst (fst f1)) (P2 B)) rho).
Defined.

Lemma binarySUMport_ne {A1 A2}
           (P1: forall ts : list Type, dependent_type_functor_rec ts (AssertTT A1) mpred)
           (P2: forall ts : list Type, dependent_type_functor_rec ts (AssertTT A2) mpred)
           (P1_ne: super_non_expansive P1) (P2_ne: super_non_expansive P2) f1 f2:
  super_non_expansive (binarySUMport P1 P2 f1 f2).
Proof.
  hnf; simpl; intros. unfold binarySUMport. destruct x as [b B].
  destruct b; simpl in B. apply P1_ne. apply P2_ne. 
Qed.
Definition binary_intersection (phi psi:funspec): option funspec.
  destruct phi as [f c A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct (funsigs_match f f2); [ | apply None].
  destruct (eq_dec c c2); [subst c2 | apply None]. simpl in *.
  remember (binarySUMport P1 P2 f f2) as P.
  remember (binarySUM Q1 Q2) as Q.
  apply Some. apply (mk_funspec f c _ P Q).
  subst P. apply (binarySUMport_ne P1 P2 P1_ne P2_ne f f2).
  subst Q; apply (binarySUM_ne Q1_ne Q2_ne).
Defined.

Lemma binaryintersection_sub phi psi omega
  (LNR: list_norepet (map fst (fst (funsig_of_funspec omega)))):
  binary_intersection phi psi = Some omega ->
  funspec_sub omega phi /\  funspec_sub omega psi.
Proof.
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne]. intros.
  simpl in H, LNR.
  remember (funsigs_match f1 f2) as b; destruct b; [ symmetry in Heqb | inv H]. 
  destruct (eq_dec c1 c2); inv H.
  apply inj_pair2 in H5. apply inj_pair2 in H4. subst P Q. split.
  + split3; try solve [reflexivity]; intros. apply funsigs_match_refl; trivial.
    exists ts2.
    fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
    simpl in H; destruct H.
    exists (existT _ true x2), emp.
    split.
    - rewrite emp_sepcon.
      split. apply tc_environ_restrict; trivial.
      apply H0.
    - simpl. intros rho'; rewrite emp_sepcon; trivial.
  + split3; try solve [reflexivity]; trivial; intros. 
    specialize (funsigs_match_LNR2 Heqb); intros LNR2.
    exists ts2.
    fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
    simpl in H; destruct H.
    exists (existT _ false x2), emp.
    split. 
    - rewrite emp_sepcon.
      split. simpl. apply funsigs_match_tc_environ; trivial.
      specialize (funsigs_match_arglengths Heqb); intros. 
      simpl; unfold port; simpl. unfold ident in *. rewrite tr_trans; trivial. rewrite H1; trivial.
    - simpl. intros rho'; rewrite emp_sepcon; trivial.
Qed.
Lemma BINARY_intersection_sub3  phi psi omega:
  binary_intersection phi psi = Some omega ->
  forall xi, funspec_sub xi phi -> funspec_sub xi psi -> funspec_sub xi omega.
Proof.
  intros. 
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne].
  simpl in H.
  remember (funsigs_match f1 f2) as b; destruct b; [ symmetry in Heqb | inv H]. 
  destruct (eq_dec c1 c2); inv H.
  apply inj_pair2 in H6. apply inj_pair2 in H7. subst P Q.
  destruct xi as [f' c' A' P' Q' P_ne' Q_ne'].
  destruct H0 as [FSM [? ?]]; subst c'.
  destruct H1 as [FSM' [_ ?]]. 
  split3; try solve [reflexivity]; trivial; intros.
  simpl in *.
  specialize (H ts2). specialize (H0 ts2). simpl in *. 
  fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
  destruct x2 as [bb Hbb]; destruct bb; [ solve [ apply H0] | simpl in *; clear H0].
  intros w [W1 W2]. unfold port in W2; simpl in W2.
  specialize (funsigs_match_LNR1 FSM'); intros LNR'.
  specialize (funsigs_match_LNR2 FSM'); intros LNR2.
  specialize (funsigs_match_LNR2 FSM); intros LNR.
  specialize (funsigs_match_arglengths FSM'); intros LEN2'.
  specialize (funsigs_match_arglengths FSM); intros LEN'.
  assert (L2: Datatypes.length (map fst (fst f2)) = Datatypes.length (map fst (fst f))).
  1: solve [unfold ident in *; rewrite <- LEN2', <- LEN'; trivial].
  exploit (H Hbb (mkEnviron (ge_of rho2) (ve_of rho2) (tr (combine (map fst (fst f)) (map fst (fst f2))) (te_of rho2))) w); clear H.
  + split; simpl. 
    - rewrite funsigs_match_symm in Heqb. apply funsigs_match_tc_environ; trivial.
    - unfold restrict in *. rewrite tr_trans in *; trivial. rewrite tr_trans in W2; trivial.
  + intros [ts1 [x1 [FR [TC HF]]]].
    exists ts1, x1, FR; split. 
    * clear HF. destruct TC as [TC HFR]; split.
      - simpl in *; rewrite tr_trans in TC; trivial.
      - eapply sepcon_derives; [ apply derives_refl | clear HFR | apply HFR].
        simpl. rewrite tr_trans; trivial.
  * clear - FSM FSM' HF.
    specialize (funsigs_match_rettypes FSM); intros.
    specialize (funsigs_match_rettypes FSM'); intros.
    simpl; intros. simpl in HF. specialize (HF rho').
    unfold ret0_tycon in *. simpl in *. rewrite <- H0, <- H in *. apply HF.
Qed.

Definition binary_intersectionOLD (phi psi:funspec): option funspec.
  destruct phi as [f c A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct (eq_dec f f2); [subst f2 | apply None].
  destruct (eq_dec c c2); [subst c2 | apply None].
  remember (binarySUM P1 P2) as P.
  remember (binarySUM Q1 Q2) as Q.
  apply Some. apply (mk_funspec f c _ P Q).
  subst P; apply (binarySUM_ne P1_ne P2_ne).
  subst Q; apply (binarySUM_ne Q1_ne Q2_ne).
Defined.

Lemma binaryintersectionOLD_sub phi psi omega
  (LNR: list_norepet (map fst (fst (funsig_of_funspec omega)))):
  binary_intersectionOLD phi psi = Some omega ->
  funspec_sub omega phi /\  funspec_sub omega psi.
Proof.
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne]. intros.
  simpl in H, LNR.
  destruct (eq_dec f1 f2); [ subst f2 | inv H]. 
  destruct (eq_dec c1 c2); inv H.
  apply inj_pair2 in H5. apply inj_pair2 in H4. subst P Q. split.
  + split3; try solve [reflexivity]; intros. apply funsigs_match_refl; trivial.
    exists ts2.
    fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
    simpl in H; destruct H.
    exists (existT _ true x2), emp.
    split.
    - rewrite emp_sepcon.
      split. apply tc_environ_restrict; trivial.
      apply H0. 
    - simpl. intros rho'; rewrite emp_sepcon; trivial.
  + split3; try solve [reflexivity]; intros. apply funsigs_match_refl; trivial. 
    exists ts2.
    fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
    simpl in H; destruct H.
    exists (existT _ false x2), emp.
    split. 
    - rewrite emp_sepcon.
      split. apply tc_environ_restrict; trivial.
      apply H0.
    - simpl. intros rho'; rewrite emp_sepcon; trivial.
Qed.
Lemma BINARY_intersectionOLD_sub3  phi psi omega:
  binary_intersectionOLD phi psi = Some omega ->
  forall xi, funspec_sub xi phi -> funspec_sub xi psi -> funspec_sub xi omega.
Proof.
  intros. 
  destruct phi as [f1 c1 A1 P1 Q1 P1_ne Q1_ne].
  destruct psi as [f2 c2 A2 P2 Q2 P2_ne Q2_ne].
  destruct omega as [f c A P Q P_ne Q_ne].
  simpl in H.
  destruct (eq_dec f1 f2); [ subst f2 | inv H]. 
  destruct (eq_dec c1 c2); inv H.
  apply inj_pair2 in H6. apply inj_pair2 in H7. subst P Q.
  destruct xi as [f' c' A' P' Q' P_ne' Q_ne'].
  destruct H0 as [FSM [? ?]]; subst c'.
  destruct H1 as [_ [_ ?]]. 
  split3; try solve [reflexivity]; trivial; intros.
  simpl in x2.
  specialize (H ts2). specialize (H0 ts2). 
  fold (@dependent_type_functor_rec ts2) in *. simpl funsig_of_funspec in *.
  destruct x2 as [b Hb]; destruct b; eauto.
Qed. 

(*-------------------Bifunctor version, general case ------------*)
(* (*
Definition generalSUM {I} (Ai: I -> TypeTree)
           (P: forall i ts, (dependent_type_functor_rec ts (AssertTT (Ai i))) mpred):  forall ts : list Type, 
    (dependent_type_functor_rec ts (AssertTT (@SigType I Ai))) mpred.
Proof. intros ts [i Hi] rho. simpl in *. apply (P i ts Hi rho). Defined. 

Lemma generalSUM_ne {I} (Ai: I -> TypeTree) P
      (P_ne: forall i,  super_non_expansive (P i)):
  super_non_expansive (generalSUM Ai P).
Proof.
  hnf; simpl; intros. unfold generalSUM. destruct x as [i Hi].
  apply P_ne. 
Qed.

Definition generalSUMport {I} {Idec: forall (i j:I), {i=j}+{i<>j}} (Ai: I -> TypeTree)
           (idents: I -> list ident)
           (P: forall j ts, (dependent_type_functor_rec ts (AssertTT (Ai j))) mpred) (i:I):  forall ts : list Type, 
    (dependent_type_functor_rec ts (AssertTT (@SigType I Ai))) mpred.
Proof. intros ts [j Hi] rho. simpl in *.
  destruct (Idec i j).
  + subst j. apply (P i ts Hi rho).
  + apply ((port (idents j) (idents i) (P j ts Hi)) rho).
Defined. 

Lemma generalSUMport_ne {I Idec} (Ai: I -> TypeTree) idents P i
      (P_ne: forall i,  super_non_expansive (P i)):
  super_non_expansive (@generalSUMport I Idec Ai idents P i).
Proof.
  hnf; simpl; intros. unfold generalSUMport. destruct x as [j Hj].
  destruct (Idec i j); subst; apply P_ne. 
Qed.

Definition intersectionPRE {I} phi:
  forall (i : I) (ts : list Type),
    (dependent_type_functor_rec ts (AssertTT (WithType_of_funspec (phi i)))) mpred.
Proof.
  intros i. destruct (phi i) as  [fi ci A_i Pi Qi Pi_ne Qi_ne]. apply Pi. 
Defined.

Definition intersectionPOST {I} phi:
  forall (i : I) (ts : list Type),
    (dependent_type_functor_rec ts (AssertTT (WithType_of_funspec (phi i)))) mpred.
Proof.
  intros i. destruct (phi i) as  [fi ci A_i Pi Qi Pi_ne Qi_ne]. apply Qi. 
Defined.

Definition iPre {I} phi:
forall ts : list Type,
        (dependent_type_functor_rec ts
           (AssertTT (SigType I (fun i : I => WithType_of_funspec (phi i)))))
          mpred.
Proof. intros. apply (generalSUM _ (intersectionPRE phi)). Defined.

Definition iPost {I} phi:
forall ts : list Type,
        (dependent_type_functor_rec ts
           (AssertTT (SigType I (fun i : I => WithType_of_funspec (phi i)))))
          mpred.
Proof. intros. apply (generalSUM _ (intersectionPOST phi)). Defined.

Lemma iPre_ne {I} (phi: I -> funspec): super_non_expansive (iPre phi).
Proof.
  unfold iPre. apply generalSUM_ne.
  intros. unfold intersectionPRE. simpl. destruct (phi i); trivial.
Qed.

Lemma iPost_ne {I} (phi: I -> funspec): super_non_expansive (iPost phi).
Proof.
  unfold iPost. apply generalSUM_ne.
  intros. unfold intersectionPOST. simpl. destruct (phi i); trivial.
Qed.

Definition general_intersection {I cc} (phi: I -> funspec) (i:I) 
           (Hsig: forall j, funsigs_match (funsig_of_funspec (phi j)) (funsig_of_funspec (phi i))= true)
           (Hcc: forall j, callingconvention_of_funspec (phi j) = cc): funspec.
Proof.
  apply (mk_funspec (funsig_of_funspec (phi i)) cc
                    ((@SigType I (fun j => WithType_of_funspec (phi j))))
                    (iPre phi) (iPost phi)).
  apply iPre_ne.
  apply iPost_ne.
Defined.

Lemma generalintersection_sub {I cc} (phi: I -> funspec) i 
           (Hsig: forall j, funsigs_match (funsig_of_funspec (phi j)) (funsig_of_funspec (phi i))= true)
           (Hcc: forall j, callingconvention_of_funspec (phi j) = cc) omega:
  general_intersection phi i Hsig Hcc = omega ->
  forall j, funspec_sub omega (phi j).
Proof.
  intros; subst. hnf. simpl funsig_of_funspec in *.
  specialize (Hsig j); specialize (Hcc j); subst.
  unfold  general_intersection; simpl.
  remember (phi j) as zz; destruct zz; intros; split3; try reflexivity; intros.
  1: simpl in Hsig. rewrite funsigs_match_symm; trivial.
  exists ts2. simpl in H; destruct H. simpl in Hsig.
  assert (exists D: (dependent_type_functor_rec ts2 (WithType_of_funspec (phi i))) mpred,
         JMeq.JMeq x2 D).
  { exists x2.  simpl in *. rewrite <- Heqzz. simpl. exists x2. constructor. }
  destruct H1 as [D HD].
  unfold iPre, intersectionPRE, generalSUM. *)

  exists (existT _ i D), emp.  
  rewrite emp_sepcon. split; simpl.
  + split; [ apply tc_environ_restrict; trivial | ].
    remember (phi i). destruct f0.
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5; apply inj_pair2 in H6; subst P0 Q0.
    inv HD. apply inj_pair2 in H1; subst; trivial. 
  + intros; rewrite emp_sepcon. unfold intersectionPOST.
    intros x X. destruct (phi i). 
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5; apply inj_pair2 in H6; subst P0 Q0.
    inv HD. apply inj_pair2 in H1; subst; trivial. 
Qed.

Lemma generalintersection_sub3  {I sig cc}
      (INH: inhabited I) (phi: I -> funspec) 
           (Hsig: forall i, funsig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc) omega:
  general_intersection phi Hsig Hcc = omega ->
  forall xi, (forall i, funspec_sub xi (phi i)) -> funspec_sub xi omega.
Proof.
  intros. subst. inv INH; rename X into i.
  unfold general_intersection. 
  destruct xi as [f c A P Q P_ne Q_ne].
  split3.
  { specialize (H0 i); specialize (Hsig i). destruct (phi i); subst; apply H0. }
  { specialize (H0 i); specialize (Hcc i). destruct (phi i); subst; apply H0. }
  intros. simpl. simpl in x2. clear i. destruct x2 as [i Hi]. simpl.
  specialize (H0 i); specialize (Hsig i); specialize (Hcc i); subst; simpl.
  unfold intersectionPRE, intersectionPOST.
  forget (phi i) as zz. clear phi.
  destruct zz. simpl in *.
  destruct H0 as [? [? ?]]; subst.
  apply (H1 ts2 Hi rho2). 
Qed.
Definition general_intersection {I sig cc} (phi: I -> funspec) 
           (Hsig: forall i, funsig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc): funspec.
Proof.
  apply (mk_funspec sig cc
                    ((@SigType I (fun i => WithType_of_funspec (phi i))))
                    (iPre phi) (iPost phi)).
  apply iPre_ne.
  apply iPost_ne.
Defined.

Lemma generalintersection_sub {I sig cc} (phi: I -> funspec) 
           (Hsig: forall i, funsig_of_funspec (phi i) = sig)
           (FSM: list_norepet (map fst (fst sig)))
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc) omega:
  general_intersection phi Hsig Hcc = omega ->
  forall i,  funspec_sub omega (phi i).
Proof.
  intros; subst. hnf. simpl funsig_of_funspec in *.
  specialize (Hsig i); specialize (Hcc i); subst.
  unfold  general_intersection; simpl.
  remember (phi i) as zz; destruct zz; intros; split3; try reflexivity; intros.
  1: apply funsigs_match_refl; trivial.
  exists ts2. simpl in H; destruct H.
  assert (exists D: (dependent_type_functor_rec ts2 (WithType_of_funspec (phi i))) mpred,
         JMeq.JMeq x2 D).
  { rewrite <- Heqzz. simpl. exists x2. constructor. }
  destruct H1 as [D HD].
  unfold iPre, intersectionPRE, generalSUM. 
  exists (existT _ i D), emp.  
  rewrite emp_sepcon. split; simpl.
  + split; [ apply tc_environ_restrict; trivial | ].
    remember (phi i). destruct f0.
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5; apply inj_pair2 in H6; subst P0 Q0.
    inv HD. apply inj_pair2 in H1; subst; trivial. 
  + intros; rewrite emp_sepcon. unfold intersectionPOST.
    intros x X. destruct (phi i). 
    simpl in *; inv Heqzz.
    apply inj_pair2 in H5; apply inj_pair2 in H6; subst P0 Q0.
    inv HD. apply inj_pair2 in H1; subst; trivial. 
Qed.

Lemma generalintersection_sub3  {I sig cc}
      (INH: inhabited I) (phi: I -> funspec) 
           (Hsig: forall i, funsig_of_funspec (phi i) = sig)
           (Hcc: forall i, callingconvention_of_funspec (phi i) = cc) omega:
  general_intersection phi Hsig Hcc = omega ->
  forall xi, (forall i, funspec_sub xi (phi i)) -> funspec_sub xi omega.
Proof.
  intros. subst. inv INH; rename X into i.
  unfold general_intersection. 
  destruct xi as [f c A P Q P_ne Q_ne].
  split3.
  { specialize (H0 i); specialize (Hsig i). destruct (phi i); subst; apply H0. }
  { specialize (H0 i); specialize (Hcc i). destruct (phi i); subst; apply H0. }
  intros. simpl. simpl in x2. clear i. destruct x2 as [i Hi]. simpl.
  specialize (H0 i); specialize (Hsig i); specialize (Hcc i); subst; simpl.
  unfold intersectionPRE, intersectionPOST.
  forget (phi i) as zz. clear phi.
  destruct zz. simpl in *.
  destruct H0 as [? [? ?]]; subst.
  apply (H1 ts2 Hi rho2). 
Qed.
*)

Fixpoint make_args' (il: list ident) (vl: list val)  : tenviron :=
  match il, vl with
  | i::il', v::vl' => Map.set i v (make_args' il' vl') 
  | _, _ => Map.empty _
  end.

Lemma make_args_eq:  forall il vl, length il = length vl ->
    forall rho,
    make_args il vl rho = mkEnviron (ge_of rho) (Map.empty _) (make_args' il vl).
Proof.
induction il; destruct vl; intros; inv H; simpl.
auto.
unfold env_set.
rewrite IHil; auto.
Qed.

Lemma set_set_commute {A} x1 x2 (a1 a2:A) t (X: x1 <> x2): 
      Map.set x1 a1 (Map.set x2 a2 t) = Map.set x2 a2 (Map.set x1 a1 t).
Proof.
  apply Map.ext; intros. rewrite ! Map.gsspec.
  destruct (ident_eq x x1); subst. rewrite if_false; trivial.
  destruct (ident_eq x x2); subst; trivial.
Qed.

Lemma tr_make_args': forall l l' args, length l = length l' -> length l = length args ->
  list_norepet l -> list_norepet l' ->
  tr (combine l l') (make_args' l args) = make_args' l' args.
Proof.
  induction l; destruct l'; destruct args; intros; try inv H; try inv H0; simpl. trivial.
  inv H1. inv H2. specialize (IHl _ _ H4 H3 H6 H7). rewrite Map.gss.
  rewrite <- IHl; clear IHl. forget (make_args' l args) as rho. clear H3 args.
  generalize dependent l'. induction l; simpl; intros. trivial.
  destruct l'; inv H4. inv H6; inv H7. simpl.
  rewrite Map.gso. 2: intros N; subst; apply H5; left; trivial.
  exploit IHl; clear IHl; try eassumption.
  + intros N; subst; apply H5. simpl; eauto.
  + intros N; subst; apply H1. simpl; eauto.
  + intros. destruct (Map.get rho a0); trivial.
    rewrite set_set_commute, H, set_set_commute; trivial; intros N; subst; apply H1; simpl; eauto.
Qed.

Lemma restrict_make_args': forall args l, length l = length args -> list_norepet l ->
      restrict l (make_args' l args) = make_args' l args.
Proof. intros. apply tr_make_args'; trivial. Qed.

Lemma has_type_list_length: forall vals tys, 
      Val.has_type_list vals tys -> length vals = length tys.
Proof.
  induction vals; simpl; intros; destruct tys; try contradiction; simpl; trivial.
  destruct H. rewrite (IHvals _ H0); trivial.
Qed.

Lemma port_trans {l1 l2 l3 P} (L12: length l1 = length l2) (L23: length l2 = length l3)
                 (L1:list_norepet l1) (L2:list_norepet l2) (L3:list_norepet l3):
      port l1 l3 P = port l2 l3 (port l1 l2 P).
Proof. unfold port. extensionality rho; simpl. rewrite tr_trans; trivial. Qed.

Lemma check_normalized_unique_idents: forall l1 l2 (L: length l1 = length l2) 
      (N1:check_normalized l1 = true) (N2: check_normalized l2=true), map fst l1 = map fst l2.
Proof.
  induction l1; intros; destruct l2; inv L; simpl; trivial. inv N1. inv N2.
  destruct a; destruct p. rewrite H0 in H1. simpl. 
  apply andb_true_iff in H1; destruct H1. apply andb_true_iff in H2; destruct H2. f_equal; eauto.
  clear - H H2.
  destruct (length l2).
  + destruct (peq i 1); subst; simpl in *; try discriminate.
    destruct (peq i0 1); subst; simpl in *; trivial. discriminate.
  + destruct (peq i (Pos.succ (Pos.of_nat (S n)))); try discriminate.
    rewrite <- e in H2. destruct (peq i0 i); subst; trivial; discriminate.
Qed.

Lemma ge_of_make_args:  
    forall s a rho, ge_of (make_args s a rho) = ge_of rho.
Proof.
induction s; intros.
 destruct a; auto.
 simpl in *. destruct a0; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

Lemma ve_of_make_args:  
    forall s a rho, length s = length a -> ve_of (make_args s a rho) = (Map.empty (block * type)).
Proof.
induction s; intros.
 destruct a; inv H; auto.
 simpl in *. destruct a0; inv H; auto.
 rewrite <- (IHs a0 rho); auto.
Qed.

Definition normalize_funspec (fs:funspec):funspec :=
  match fs with mk_funspec sig cc A P Q NEP NEQ =>
    match sig with (params, rt) =>
    let np := normalparams (length params) in
    mk_funspec (combine np (map snd params), rt) cc A 
          (fun ts (x:dependent_type_functor_rec ts A mpred) => port np (map fst params) (P ts x)) 
          Q (port_super_nonexpansive NEP) NEQ 
  end end.

Lemma normalize_funspec_is_normalized fs: funspec_normalized (normalize_funspec fs) = true.
Proof.
destruct fs. destruct f. simpl. unfold funspec_normalized. simpl. apply norm_char. 
rewrite fst_combine, combine_length; rewrite length_normalparams, map_length; trivial.
rewrite Nat.min_id; trivial.
Qed.

Definition rename_pre {A} (ids1 ids2:list ident)(P: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)):
  forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap).
Proof.
  intros ts x rho.
  apply (P ts x (mkEnviron (ge_of rho) (ve_of rho) (tr (combine ids1 ids2) (te_of rho)))).
Defined.

Lemma  rename_port_eq {A ts} {x:dependent_type_functor_rec ts A (pred rmap)} {ids1 ids2:list ident} P:
  (@rename_pre A ids1 ids2 P) ts x = port ids2 ids1 (P ts x).
Proof. reflexivity. Qed.

(*move to seplog?*)

Lemma rename_pre_super_non_expansive {A} {P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred}
      (NEP : super_non_expansive P) ids1 ids2:
      super_non_expansive (rename_pre ids1 ids2 P).
Proof. unfold rename_pre; simpl. red; intros. apply NEP. Qed.

Lemma rename_pre_trans {A l1 l2 l3} {P: forall ts, dependent_type_functor_rec ts (AssertTT A) mpred}
      (L31: length l3 = length l1) (L12: length l1 = length l2)
      (LNR1: list_norepet l1) (LNR2: list_norepet l2) (LNR3: list_norepet l3):
      rename_pre l2 l1 (rename_pre l1 l3 P) = rename_pre l2 l3 P.
Proof.
  unfold rename_pre. simpl. extensionality ts. extensionality x. extensionality rho.
  rewrite tr_trans; trivial.
Qed.

