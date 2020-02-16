Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import VST.progs.sumarray. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Functional spec of this program.  *)
Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; omega.
Qed.
(*
(* Beginning of the API spec for the sumarray.c program *)
Definition sumarray_spec : ident * funspec :=
 DECLARE _sumarray
  FOR a: val, sh : share, contents : list Z, size: Z
  PRE [ (tptr tuint), tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed;
          Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
          (LAMBDAx nil ([a; Vint (Int.repr size)])
          (SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)))
  POST [ tuint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
           SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).
*)

Definition sumarray_spec_old : ident * funspec :=
 (DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ _a OF (tptr tuint), _n OF tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed;
          Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
          LOCAL (temp _a a; temp _n (Vint (Int.repr size)))
          SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
  POST [ tuint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
           SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a))%old_funspec.

Definition sumarray_spec : ident * funspec :=
 DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ (tptr tuint), tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed;
                 Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
          PARAMS (a; Vint (Int.repr size))
          GLOBALS () (*TODO: make this line optional, ie insert GLOBALx nil during parsing of notation.
                          Currently, omitting the line leads to failaure of start_function, specifically of compute_close_precondition_eq *)
          SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
  POST [ tuint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
           SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

(*
Lemma modernize_funspec_pre:
 forall f A Pre' Pre,
  convertPre f A Pre' = Pre.
Proof.
intros.
unfold convertPre.
extensionality w ae.
destruct ae as [g args].
*)

Lemma modernize_funspec:
  forall f cc A Pre' Pre Post,
  convertPre f A Pre' = Pre ->
  NDmk_funspec' f cc A Pre' Post = NDmk_funspec (compcert_rmaps.typesig_of_funsig f) cc A Pre Post.
Proof.
intros.
unfold NDmk_funspec'.
f_equal.
auto.
Qed.

Definition convert_funspecX (fs: funspec) := {fs' | fs = fs'}.

Ltac simpl_snd a :=
 match a with
 | NDmk_funspec' _ _ _ _ _ => constr:(a)
 | _ => let b := eval red in a in simpl_snd b
 end.

Definition sumarray_spec2 : convert_funspecX (snd sumarray_spec_old).
eexists.
apply modernize_funspec.
match goal with |- _ = ?x => set (Pre := x) end.
unfold convertPre.
extensionality w ae.
destruct ae as [g args].
repeat match goal with |- _ && (let (_,_) := ?x in _) _ = _ => destruct x end.
match goal with |- _ && (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ = Pre _ _ => idtac end.
Abort.
  
(*

Ltac convert_funspec_pre f A Pre := 
  let p := constr:(convertPre f A Pre) in
(*  let p := eval unfold convertPre in p in *)
  constr:(p).

Ltac convert_funspec fs :=
 let fs := simpl_snd fs in 
 match fs with 
 | NDmk_funspec' ?f ?cc ?A ?Pre ?Post => 
    let b := convert_funspec_pre f A Pre in
    let f' := constr:(compcert_rmaps.typesig_of_funsig f) in
    let f'' := eval simpl in f' in
    let c := constr:(NDmk_funspec f'' cc A b Post) in
  pose (xx := c)
  end.

convert_funspec (snd sumarray_spec_old).
*)


Lemma modernize_DECLARE:
  forall (id: ident)  (fspec' fspec: funspec),
   fspec' = fspec -> (id,fspec') = (id,fspec).
Proof.
intros.
congruence.
Qed.

Lemma modernize_sumarray_spec: sumarray_spec_old = sumarray_spec.
Proof.
apply modernize_DECLARE.
apply modernize_funspec.
unfold convertPre.
extensionality x y.
destruct x. destruct p. destruct p.
match goal with |- context [PROPx ?A _] => forget A as P end.
match goal with |- context [SEPx ?A] => forget A as R end.
simpl map.
destruct y.
simpl snd. simpl fst.
match goal with |- context [make_args ?A ?B ?C]  => set (ma := make_args A B C) end.
unfold PROPx, LAMBDAx, GLOBALSx, LOCALx, SEPx; simpl.
unfold argsassert2assert.
unfold local, lift1.
unfold_lift.
rewrite (prop_true_andp True) by auto.
normalize.
f_equal.
f_equal.
apply prop_ext; split; intros H; decompose [and] H; clear H.
-
subst.
destruct l0; try discriminate.
destruct l0; try discriminate.
destruct l0; try discriminate.
clear H0 H6.
subst ma.
unfold eval_id in *; simpl in *.
subst.
split3; auto.
-
subst.
split3; auto.
subst ma; unfold eval_id; simpl.
inv H3. inv H4.
split3; auto.
Qed.

Print sumarray_spec_old. (*Prints as LAMBDAx*)

(* Note: It would also be reasonable to let [contents] have type [list int].
  Then the [Forall] would not be needed in the PROP part of PRE.
*)

(* The precondition of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (1+2+3+4)))) 
     SEP(TT).

(* Note: It would also be reasonable to let [contents] have type [list int].
  Then the [Forall] would not be needed in the PROP part of PRE.
*)

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
        ltac:(with_library prog [sumarray_spec_old; main_spec]).


Lemma convertPre_helper1:
  forall P1 P Q R x,
   !! P1 && PROPx P (LOCALx Q (SEPx R)) x = 
   PROPx P ((!!P1 && (local (fold_right (liftx and) (liftx True) (map locald_denote Q)))) && SEPx R) x.
Proof.
intros.
unfold PROPx, LOCALx; simpl; normalize.
f_equal; auto.
f_equal; auto.
apply prop_ext; intuition.
Qed.

Lemma convertPre_helper2:
  forall P1 P Q R G L x y,
   !!P1 && (local (fold_right (liftx and) (liftx True) (map locald_denote Q)) x) =
      !! (snd y = L /\ Forall (fun v : val => v <> Vundef) L) &&
         local (fold_right (liftx and) (liftx True) (map locald_denote (map gvars G)))
                   (Clight_seplog.mkEnv (fst y) [] []) ->
   !! P1 && PROPx P (LOCALx Q (SEPx R)) x = PROPx P (LAMBDAx G L (SEPx R)) y.
Proof.
intros.
unfold PROPx,PARAMSx, GLOBALSx, LOCALx, SEPx.
transitivity 
 (( !! P1 &&
    local
      (fold_right (liftx and) (liftx True) (map locald_denote Q)) x ) && 
  (!! fold_right and True P &&
    (fun _ : environ => fold_right_sepcon R) x)).
simpl.
rewrite andp_assoc.
f_equal.
rewrite <- !andp_assoc.
f_equal.
rewrite andp_comm.
auto.
rewrite H; clear H.
unfold local, lift1.
unfold_lift.
simpl.
normalize.
f_equal.
f_equal.
f_equal.
apply prop_ext; intuition.
Qed.

Fixpoint findPARAM i D :=
 match D with
 | temp j v :: D' => if ident_eq i j then v else findPARAM i D'
 | _ :: D' => findPARAM i D'
 | nil => Vundef
 end.

Fixpoint makePARAMS (L: list (ident * type)) D :=
 match L with
 | (i,_)::L' => findPARAM i D :: makePARAMS L' D
 | nil => nil
 end.

Ltac convertPreElim' := 
unfold convertPre;
let ae := fresh "ae" in extensionality ae;
let g := fresh "g" in let args := fresh "args" in destruct ae as [g args];
apply convertPre_helper2;
simpl fst; simpl snd;
match goal with |- !! (_ = Datatypes.length ?L) && local (fold_right _ _ (map _ ?D)) _=
                              !! (args = ?A /\ _) && local (fold_right _ _ (map _ (map _ ?G))) _ => 
 let p := constr:(makePARAMS L D) in
 let p := eval simpl in p in 
  unify A p;
  unify G (@nil globals)
end;
unfold local, lift1; unfold_lift; normalize; f_equal;
apply prop_ext; split;
[ let H := fresh in let H0 := fresh in 
  intros [H H0];
  repeat (let a := fresh "a" in destruct args as [ | a args]; [discriminate | ]);
  destruct args; [ | discriminate];
  simpl in H0;
  unfold_lift in H0;
  unfold eval_id in H0; simpl in H0;
  decompose [and] H0; subst;
  split; [ reflexivity | ];
  repeat apply Forall_cons; try apply Forall_nil; auto
| let H := fresh in let H0 := fresh in 
  intros [H H0]; subst; split; [reflexivity |];
  repeat match goal with H: Forall _ _ |- _ => inv H end;
  simpl; unfold_lift; unfold eval_id; simpl;
  repeat split; auto
].

Ltac convertPreElim := 
  match goal with |- convertPre _ _ _ _ = _ => idtac end;
  convertPreElim' || fail 100 "Could not convert old-style precondition to new-style".

Ltac prove_call_setup_aux  ts witness ::=
 let H := fresh "SetupOne" in
 intro H;
 match goal with | |- @semax ?CS _ _ (PROPx ?P (LOCALx ?L (SEPx ?R'))) _ _ =>
 let Frame := fresh "Frame" in evar (Frame: list mpred); 
 let R := strip1_later R' in
 exploit (call_setup2_i _ _ _ _ _ _ _ _ R R' _ _ _ _ ts _ _ _ _ _ _ _ H witness Frame); clear H;
 simpl functors.MixVariantFunctor._functor;
 [ convertPreElim || reflexivity
 | check_prove_local2ptree
 | check_vl_eq_args (*WAS: Forall_pTree_from_elements*)
 | auto 50 with derives
 | unfold check_gvars_spec; solve [exact I | reflexivity]
 | try change_compspecs CS; cancel_for_forward_call
 |
 ]
 end.

Fixpoint temps_of_localdef (dl: list localdef) : list ident :=
 match dl with
 | temp i _ :: dl' => i :: temps_of_localdef dl'
 | _ :: dl' => temps_of_localdef dl'
 | nil => nil
 end.


Set Nested Proofs Allowed.

Lemma convertPre_helper3:
  forall (fsig: funsig) P Q R vals,
  makePARAMS (fst fsig) Q = vals ->
  list_norepet (temps_of_localdef Q) ->
  list_norepet (map fst (fst fsig)) ->
  (forall i, In i (temps_of_localdef Q) <-> In i (map fst (fst fsig))) ->
  Forall (fun v : val => v <> Vundef) vals ->
  (fun ae : argsEnviron => !! (Datatypes.length (snd ae) = Datatypes.length (fst fsig)) &&
      (PROPx P (LOCALx Q (SEPx R)))
        (make_args
           (map fst (fst fsig))
           (snd ae)
           (mkEnviron (fst ae) (Map.empty (block * type))
              (Map.empty val)))) =
  PROPx P (PARAMSx vals (GLOBALSx nil (SEPx R))).
Proof.
intros. rename H0 into Hno. rename H1 into H0.
extensionality ae.
apply convertPre_helper2.
unfold local, lift1.
unfold_lift.
simpl.
normalize.
f_equal.
apply prop_ext.
split.
-
intros [? ?].
split; auto.
destruct ae as [g args].
simpl in *.
subst vals.
(*
revert args H0 H1 H2; induction (fst fsig) as [|[??]]; destruct args; simpl; intros; subst; try discriminate.
auto.
injection H1 as H1.
inv H0.
specialize (IHl args H5 H1).
f_equal.
 + clear - H2 H4. induction Q; simpl in *. congruence.
    destruct a. if_tac. subst. destruct H2. destruct H.
    hnf in H. unfold eval_id in H; simpl in H. rewrite Map.gss in H. simpl in H. auto.
    apply IHQ. destruct H2;  auto. auto.
    apply IHQ. destruct H2; auto. auto.
    apply IHQ. destruct H2; auto. auto.
 + apply IHl; auto.
    clear - H2 Hno.
    induction Q; simpl in *. auto.
    destruct a. inv Hno.
    destruct H2.
    specialize (IHQ H3 H0). split; auto.
    split; simpl; unfold_lift. destruct H.
    hnf in H. subst v0. unfold eval_id.
   simpl. 
    destruct (ident_eq i0 i). subst. rewrite Map.gss. 
    simpl. unfold_lift.
    clear - H.
    split; simpl.
    hnf. apply IHQ.
    inv H0. 
    
    
     clear - H3 H2.
     
    
    destruct H2.
    simpl in H. destru unfold_lift in H.
    hnf in H.
    destruct H2. simpl in H0.
 subst.
*)
Admitted.

Ltac prove_norepet := 
   clear; repeat constructor; simpl; intros ?H;
     repeat match goal with H: _ \/ _ |- _ => destruct H end;
      repeat match goal with H: _ = _ |- _ => inv H end; auto.


(** Proof that f_sumarray, the body of the sumarray() function,
 ** satisfies sumarray_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec_old.
Proof.

 leaf_function;
 match goal with |- semax_body ?V ?G ?F ?spec =>
    check_normalized F;
    let s := fresh "spec" in
    pose (s:=spec); hnf in s; cbn zeta in s; (* dependent specs defined with Program Definition often have extra lets *)
   repeat lazymatch goal with
    | s := (_, NDmk_funspec _ _ _ _ _) |- _ => fail
    | s := (_, mk_funspec _ _ _ _ _ _ _) |- _ => fail
    | s := (_, ?a _ _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _) |- _ => unfold a in s
    | s := (_, ?a _) |- _ => unfold a in s
    | s := (_, ?a) |- _ => unfold a in s
    end;
    lazymatch goal with
    | s :=  (_,  WITH _: globals
               PRE  [] main_pre _ _ _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end.
unfold NDmk_funspec'.
 let DependedTypeList := fresh "DependedTypeList" in
 unfold NDmk_funspec.

 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>

   (*WAS:split; [split3; [check_parameter_types' | check_return_type
          | try (apply compute_list_norepet_e; reflexivity);
             fail "Duplicate formal parameter names in funspec signature"  ] 
         |];*)
   (*NOW:*)split3; [check_parameter_types' | check_return_type | ];

   match Pre with
(*   | (fun _ => convertPre _ _ (fun x => match _ with (a,b) => _ end)) =>
              intros Espec DependedTypeList [a b]
*)
   | (fun _ => convertPre _ _ (fun i => _)) =>  intros Espec DependedTypeList i
   | (fun _ x => match _ with (a,b) => _ end) => intros Espec DependedTypeList [a b]
   | (fun _ i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end.

 try match goal with |- semax _ (fun rho => ?A rho * ?B rho) _ _ =>
     change (fun rho => ?A rho * ?B rho) with (A * B)
  end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList.
 unfold convertPre.
 repeat match goal with
 | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (close_precondition _ match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (close_precondition _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
             destruct p as [a b]
 | |- semax _ (close_precondition _
                                                (fun ae => !! (Datatypes.length (snd ae) = ?A) && ?B
                                                      (make_args ?C (snd ae) (mkEnviron (fst ae) _ _))) * _) _ _ =>
          match B with match ?p with (a,b) => _ end => destruct p as [a b] end
       end.
Print PARAMSx.
erewrite convertPre_helper3; [ | reflexivity | prove_norepet | prove_norepet | intros; simpl; intuition | ].

2:{
simpl.
repeat constructor; try congruence.

intros; simpl; intuition.

decompose [or] H; clear H; try congruence.
intros [?|?]. 
intro H.
prove_list_norepet.
 2: reflexivity.


start_function. (* Always do this at the beginning of a semax_body proof *)
(* The next two lines do forward symbolic execution through
   the first two executable statements of the function body *)
forward.  (* i = 0; *)
forward.  (* s = 0; *)
(* To do symbolic execution through a [while] loop, we must
 * provide a loop invariant, so we use [forward_while] with
 * the invariant as an argument .*)
forward_while
 (EX i: Z,
   PROP  (0 <= i <= size)
   LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
(* forward_while leaves four subgoals; here we label them
   with the * bullet. *)
* (* Prove that current precondition implies loop invariant *)
Exists 0.   (* Instantiate the existential on the right-side of |--   *)
entailer!.  (* Simplify this entailment as much as possible; in this
      case, it solves entirely; in other cases, entailer! leaves subgoals *)
* (* Prove that loop invariant implies typechecking condition *)
entailer!.  (* Typechecking conditions usually solve quite easily *)
* (* Prove postcondition of loop body implies loop invariant *)
(* In order to get to the postcondition of the loop body, of course,
   we must forward-symbolic-execute through the loop body;
   so we start that here. *)
(* "forward" fails and tells us to first make (0 <= i < Zlength contents)
   provable by auto, so we assert the following: *)
assert_PROP (Zlength contents = size). {
  entailer!. do 2 rewrite Zlength_map. reflexivity.
}
forward. (* x = a[i] *)
forward. (* s += x; *)
forward. (* i++; *) 
 (* Now we have reached the end of the loop body, and it's
   time to prove that the _current precondition_  (which is the
   postcondition of the loop body) entails the loop invariant. *)
 Exists (i+1).
 entailer!. simpl.
 f_equal.
 rewrite (sublist_split 0 i (i+1)) by omega.
 rewrite sum_Z_app. rewrite (sublist_one i) by omega.
 autorewrite with sublist. normalize.
 simpl. rewrite Z.add_0_r. reflexivity.
* (* After the loop *)
forward.  (* return s; *)
 (* Here we prove that the postcondition of the function body
    entails the postcondition demanded by the function specification. *)
entailer!.
autorewrite with sublist in *.
autorewrite with sublist.
reflexivity.
Qed.

(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].


Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call (*  s = sumarray(four,4); *)
  (gv _four, Ews,four_contents,4).
 split3. auto. computable. repeat constructor; computable.
forward. (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
  prove_semax_prog.
  semax_func_cons body_sumarray.
  semax_func_cons body_main.
Qed.
