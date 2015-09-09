Require Import floyd.proofauto.
Require Import progs.nest2.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  

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

Definition get_spec' :=
 DECLARE _get
  WITH v : (int * (float * int))%type, p : val
  PRE  [] 
        PROP ()
        LOCAL(gvar _p p)
        SEP(`(data_at Ews t_struct_b (repinj t_struct_b v) p))
  POST [ tint ]
         PROP() 
         LOCAL (temp 1%positive (Vint (snd (snd v))))
         SEP (`(data_at Ews t_struct_b (repinj t_struct_b v) p)).

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

Lemma body_get':  semax_body Vprog Gprog f_get get_spec'.
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

Lemma body_set:  semax_body Vprog Gprog f_set set_spec.
Proof.
 start_function.
name i_ _i.
simpl in v.
(*destruct v as [a [b c]]; simpl in *. *)
unfold_repinj.
(*  OBSTACLES to using "cbv delta" to simplify proj_reptype:  
cbv beta iota zeta delta [eq_rect_r eq_rect eq_sym 
   nested_field_type2 nested_field_rec field_type 
   fieldlist.field_type2 Ctypes.field_type co_members get_co
   cenv_cs CompSpecs
   compute_in_members mk_prog_compspecs prog_comp_env
   nested_field_type2_ind co_default reptype_ind
   id_in_list fst snd prog_comp_env PTree.get Pos.eqb
  ident_eq map gfield_type eq_ind_r peq
  not_in_members_field_type reptype_gen Pos.eq_dec
  field_type sumbool_rec
 BUG:  these two are opaque in the Coq library,
   can't unfold them:  dec_Zge Decidable.dec_not_not
*)
forward.
Time forward. (* 8.77 sec *)
unfold update22. unfold_repinj.
cancel.
Qed.  (* approx 28 seconds *)

