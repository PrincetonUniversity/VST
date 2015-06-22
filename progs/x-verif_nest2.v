Require Import floyd.proofauto.
Require Import progs.nest2.

Instance CompSpecs : compspecs := compspecs_program prog.
Instance CS_legal : compspecs_legal CompSpecs.
Proof. prove_CS_legal. Qed.

Local Open Scope logic.

Definition t_struct_b := Tstruct _b noattr.

Definition get_spec :=
 DECLARE _get
  WITH v : reptype' t_struct_b, p : val
  PRE  [] 
        PROP ()
        LOCAL(gvar _p p)
        SEP(`(data_at Ews t_struct_b (repinj _ v) p))
  POST [ tint ]
         PROP() 
         LOCAL (temp 1%positive (Vint (snd (snd v))))
         SEP (`(data_at Ews t_struct_b (repinj _ v) p)).

Definition update22 (i: int) (v: reptype' t_struct_b) : reptype' t_struct_b :=
   (fst v, (fst (snd v), i)).

Definition set_spec :=
 DECLARE _set
  WITH i : int, v : reptype' t_struct_b, p : val
  PRE  [ _i OF tint ] 
         PROP  ()
         LOCAL (gvar _p p; 
                temp _i (Vint i))
         SEP   (`(data_at Ews t_struct_b (repinj _ v) p))
  POST [ tvoid ]
         PROP() LOCAL()
        SEP(`(data_at Ews t_struct_b (repinj _ (update22 i v)) p)).

Definition Vprog : varspecs := (_p, t_struct_b)::nil.

Definition Gprog : funspecs := 
    get_spec::set_spec::nil.
(*
Lemma body_get:  semax_body Vprog Gprog f_get get_spec.
Proof.
start_function.
name i _i.
simpl in v.
unfold_repinj.
Time forward. (* 5.989 sec  -> 2.6*)
Time forward. (* 11.1118 sec -> 7.5 *)
unfold_repinj.
cancel.
Qed.
*)
Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
name i_ _i.
simpl in v.
(*destruct v as [a [b c]]; simpl in *. *)
unfold_repinj.

eapply semax_seq'.

ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e ?e2) _ =>
  (* Super canonical field store *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let HRE := fresh "H" in
    let v0 := fresh "v" in evar (v0: val);
      do_compute_expr Delta P Q R (Ecast e2 (typeof (nested_efield e1 efs tts))) v0 HRE;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type2 t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    let H_LEGAL := fresh "H" in
    sc_new_instantiate P Q R R Delta e1 gfs tts lr p sh t_root gfs0 v n (0%nat) H H_LEGAL;

    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;

    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs p;

    let Heq := fresh "H" in
    match type of H with
    | (PROPx _ (LOCALx _ (SEPx (?R0 :: nil))) 
           |-- _) => assert (nth_error R n = Some R0) as Heq by reflexivity
    end;
          eapply (semax_SC_field_store Delta sh n)
            with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
            [reflexivity | reflexivity | reflexivity
            | reflexivity | exact Heq | exact HLE 
            | exact HRE | exact H_Denote | exact H | solve [auto]
| .. (*            | solve_store_rule_evaluation
            | unfold tc_efield; try solve[entailer!]; try (clear Heq HLE HRE H_Denote H H_LEGAL;
              subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n; simpl app; simpl typeof)
            | solve_legal_nested_field_in_entailment; try clear Heq HLE HRE H_Denote H H_LEGAL;
           subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n 
*)]

end.

{
Require Import type_induction.
  apply data_equal_congr.

repeat match goal with  
 | |- context [nested_field_type2 ?A ?B] =>
     really_simplify (nested_field_type2 A B)
 end.


Ltac compute_defs :=
  match goal with
  | A : _ |- _ => clear A; compute_defs
  | A := _ |- _ => clear A; compute_defs
  | A := _ : list gfield |- _ => 
          compute in A; subst A
(*
  | A := _ |- _ => 
          compute in A; revert A; 
          compute_defs; intro A
*)
  | |- _ => idtac
  end.


  clear;
  repeat match goal with
   | A := _ |- _ => clear A 
   | A := _ : type |- _ => compute in A; subst A
   | A := _ : list gfield |- _ => compute in A; subst A
   | A := _ : reptype ?B |- _ =>
       let t := fresh "t" in set (t:=reptype B) in *;
        compute in t; subst t
   end.

match goal with 
 |- @upd_reptype ?CS ?CSL _ _ _ _ = _ =>
 let cs := fresh "cs" in let csl := fresh "csl" in
 set (csl := CSL); revert csl;
 destruct CSL; intro;
 set (cs := CS);
 compute in cs; 
 match goal with cs := ?A : compspecs |- _ =>
    change A with (@abbreviate _ A) in cs
 end
end.

(* HERE *)

Ltac foo :=
lazy beta iota zeta delta [ 
  abbreviate
  nested_field_type2 nested_field_rec
  field_type fieldlist.field_type2 Ctypes.field_type
   upd_reptype singleton_hole singleton_hole_rec
   singleton_subs
   default_val valinject rev app map 
   fold_reptype unfold_reptype list_rect
   compact_prod compact_prod_map
   ListTypeGen
   rgfs_dec list_eq_dec sumbool_rec sumbool_rect
].

Ltac bar :=
   match goal with |- ?GG = _ => match GG with
    | (_,_) =>
              eapply pair_congr
    | _ =>
          rewrite eq_rect_r_eq
    | _ =>
          rewrite <- eq_rect_eq
    | context [fst (?A, ?B)] =>
              change (fst (A, B)) with A
    | context [snd (?A, ?B)] =>
              change (snd (A, B)) with B
    | replace_reptype _ _ _ _ =>
      rewrite replace_reptype_ind
    | func_type _ _ _ _ _ _ _ _ _  => 
             rewrite func_type_ind
    | context [ident_eq ?A ?B] =>
             really_simplify (ident_eq A B)
    | context [co_members (get_co ?i)] =>
            really_simplify (co_members (get_co i))
    | context [compute_in_members ?A ?B] =>
            really_simplify (compute_in_members A B)
    | context [gfield_dec ?A ?B] =>
         really_simplify (gfield_dec A B)
    | context [member_dec ?A ?B] =>
       really_simplify (member_dec A B)
    end 
  | A := _ |- _ => subst A
  end; 
  foo.

foo.
bar. bar. bar. bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar. bar. bar. bar.
bar. bar. bar. bar.
reflexivity.
bar. bar. bar. bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar.
reflexivity.
bar. bar. bar. bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar.
reflexivity.

cbv delta [compute_in_members]; foo.
 bar.
bar. bar. bar. bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar.



    | context [fst (?A, ?B)] =>
              change (fst (A, B)) with A
    | context [snd (?A, ?B)] =>
              change (snd (A, B)) with B
match goal with 
 | A := _ |- _ => subst A
end.


bar.
rewrite replace_reptype_ind.


Ltac bar :=
match goal with 
 first
 [ progress (simpl ident_eq)
 | progress (simpl co_members)
 | progress (simpl compute_in_members)
 | rewrite eq_rect_r_eq
 | rewrite <- eq_rect_eq
 | rewrite replace_reptype_ind
 ]; foo.

bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar.

foo. 
bar. bar. bar. bar. bar.
repeat bar.
foo.
bar. bar. bar. bar. bar.
bar. bar. bar. bar. bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
repeat bar.
foo.
bar. bar. bar. 
foo. bar. bar. bar. bar. bar.

repeat bar.
 |

rewrite replace_reptype_ind; foo.
simpl co_members; foo.
rewrite eq_rect_r_eq; foo.
lazy zeta iota beta.
unfold ListTypeGen.
simpl reptype.
rewrite <- eq_rect_eq; foo.
simpl cenv_cs.

Locate compspecs_program.

lazy beta iota zeta delta [
  ListType
].
rewrite <- eq_rect_eq; foo.


lazy beta iota zeta delta [
  nested_field_type2 nested_field_rec
   upd_reptype singleton_hole singleton_hole_rec
   valinject rev app fold_reptype compact_prod_map
   co_members get_co
   cenv_cs PTree.get CompSpecs compspecs_program
   prog_comp_env prog
].


 subst

  match goal with |- context [valinject ?t ?v] =>
     rewrite (valinject_JMeq t v (eq_refl _))
 end;
 rewrite upd_reptype_ind;
 really_simplify_some_things;
 cbv beta iota delta [upd_reptype_rec];
 really_simplify_some_things;
 cbv beta iota delta [upd_gfield_reptype];
 really_simplify_some_things;
 reflexivity.



Time forward. (* 10.17 -> 6.93 sec *)
Time forward. (* 8.77 sec *)
unfold update22. simpl.
unfold_repinj.
cancel.
Qed.  (* approx 28 seconds *)

repeat bar.