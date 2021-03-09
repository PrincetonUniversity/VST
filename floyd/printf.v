Require Import VST.floyd.proofauto.
Require Export VST.floyd.io_events.
Require Export ITree.ITree.


Inductive format_item :=
| FI_int: format_item
| FI_string: format_item
| FI_text: list byte -> format_item
| FI_error: format_item.

Fixpoint interpret_format_string (s: list Z) : 
    list format_item :=
 match s with
 | 37 :: 100 :: s' =>   (* %d *)
    FI_int :: interpret_format_string s'
 | 37 :: 115 :: s' =>  (* %s *)
    FI_string :: interpret_format_string s'
 | 37 :: 37 :: s' =>    (* %% *)
                  match interpret_format_string s' with
                  | FI_text s1 :: fl => FI_text (Byte.repr 37 :: s1) :: fl
                  | fl => FI_text (Byte.repr 37 :: nil) :: fl
                  end
 | 37 :: s' => FI_error :: interpret_format_string s'
 | c :: s' => match interpret_format_string s' with
                  | FI_text s1 :: fl => FI_text (Byte.repr c :: s1) :: fl
                  | fl => FI_text (Byte.repr c :: nil) :: fl
                  end
 | nil => nil
  end.

Fixpoint format_stuff (fl: list format_item) : Type :=
 match fl with
 | FI_int :: fl' => int * format_stuff fl'
 | FI_string :: fl' => (share * list byte * val) * format_stuff fl'
 | FI_text _ :: fl' => format_stuff fl'
 | FI_error :: fl' => format_stuff fl'
 | nil => unit
 end.

Fixpoint format_argtys (fl: list format_item) : list type :=
 match fl with
 | FI_int :: fl' => tint :: format_argtys fl'
 | FI_string :: fl' => tptr tschar :: format_argtys fl'
 | FI_text _ :: fl' => format_argtys fl'
 | FI_error :: fl' => format_argtys fl'
 | nil => nil
 end.

Definition readable_cstring {CS: compspecs} x := 
  !! readable_share (fst (fst x)) && cstring (fst (fst x)) (snd (fst x)) (snd x).

Fixpoint SEP_of_format {CS: compspecs}
    (fl: list format_item)
    (stuff: format_stuff fl) {struct fl} : list mpred.
destruct fl as [ | fi fl'].
apply nil.
destruct fi; simpl in stuff.
- (* FI_int *)
apply (SEP_of_format CS fl' (snd stuff)).
- (* FI_string *)
apply (
(* cstring (fst (fst (fst stuff))) (snd (fst (fst stuff))) (snd (fst stuff))
          :: SEP_of_format CS fl' (snd stuff)). *)
match stuff with ((sh,s,p),_) => cstring sh s p end
          :: SEP_of_format CS fl' (match stuff with (_,r) => r end)).
- (* FI_text *)
apply (SEP_of_format CS fl' stuff).
- (* FI_error *)
apply (FF::nil).
Defined.


Fixpoint PARAMS_of_format 
    (fl: list format_item) (stuff: format_stuff fl) {struct fl} : list val.
destruct fl as [ | fi fl'].
apply nil.
destruct fi; simpl in stuff.
- (* FI_int *)
apply (Vint (fst stuff) :: PARAMS_of_format fl'  (snd stuff)).
- (* FI_string *)
apply ((snd (fst stuff)) :: PARAMS_of_format fl' (snd stuff)).
- (* FI_text *)
apply (PARAMS_of_format fl' stuff).
- (* FI_error *)
apply (PARAMS_of_format fl' stuff).
Defined.

Fixpoint PROP_of_format (fl: list format_item) (stuff: format_stuff fl) {struct fl} : list Prop.
destruct fl as [ | fi fl'].
apply nil.
destruct fi; simpl in stuff.
- (* FI_int *)
apply (PROP_of_format fl' (snd stuff)).
- (* FI_string *)
apply (readable_share (fst (fst (fst stuff))) :: PROP_of_format fl' (snd stuff)).
- (* FI_text *)
apply (PROP_of_format fl' stuff).
- (* FI_error *)
apply (PROP_of_format fl' stuff).
Defined.

(* Compute the string representation of an int *)
Lemma div_10_dec : forall n, 0 < n ->
  (Z.to_nat (n / 10) < Z.to_nat n)%nat.
Proof.
  intros.
  change 10 with (Z.of_nat 10).
  rewrite <- (Z2Nat.id n) by lia.
  rewrite <- div_Zdiv by discriminate.
  rewrite !Nat2Z.id.
  apply Nat2Z.inj_lt.
  rewrite div_Zdiv, Z2Nat.id by lia; simpl.
  apply Z.div_lt; auto; lia.
Qed.

Definition charminus := Byte.repr 45.

Program Fixpoint chars_of_Z (n : Z) { measure (Z.to_nat (if n <? 0 then Z.abs n + 1 else n)) } : list byte :=
  match n <? 0 with true => charminus :: chars_of_Z (Z.abs n) | false =>
  let n' := n / 10 in
  match n' <=? 0 with true => [Byte.repr (n + char0)] | false => chars_of_Z n' ++ [Byte.repr (n mod 10 + char0)] end end.
Next Obligation.
Proof.
  destruct (Z.ltb_spec n 0); try discriminate.
  destruct (Z.abs_spec n) as [[]|[? ->]]; try lia.
  replace (- n <? 0) with false.
  rep_lia.
  destruct (Z.ltb_spec (-n) 0); auto; lia.
Defined.
Next Obligation.
Proof.
  rewrite <- Heq_anonymous0.
  destruct (Z.ltb_spec n 0); try discriminate.
  pose proof (Z.div_pos _ 10 H).
  destruct (Z.ltb_spec (n / 10) 0); try lia.
  apply div_10_dec.
  symmetry in Heq_anonymous; apply Z.leb_nle in Heq_anonymous.
  eapply Z.lt_le_trans, Z_mult_div_ge with (b := 10); lia.
Defined.

Lemma chars_of_Z_eq : forall n, chars_of_Z n =
  match n <? 0 with true => charminus :: chars_of_Z (Z.abs n) | false =>
  let n' := n / 10 in
  match n' <=? 0 with true => [Byte.repr (n + char0)] | false => chars_of_Z n' ++ [Byte.repr (n mod 10 + char0)] end end.
Proof.
  intros.
  unfold chars_of_Z at 1.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext; simpl; fold chars_of_Z.
  destruct (_ <? _); auto.
  destruct (_ <=? _); auto.
Qed.

Fixpoint string_of_format {CS: compspecs}
    (fl: list format_item)
    (stuff: format_stuff fl) {struct fl} : list byte.
destruct fl as [ | fi fl'].
apply nil.
destruct fi; simpl in stuff.
- (* FI_int *)
apply (chars_of_Z (Int.signed (fst stuff)) ++ string_of_format CS fl' (snd stuff)).
- (* FI_string *)
apply (
(* cstring (fst (fst (fst stuff))) (snd (fst (fst stuff))) (snd (fst stuff))
          :: SEP_of_format CS fl' (snd stuff)). *)
match stuff with ((_,s,_),_) => s end ++ string_of_format CS fl' (match stuff with (_,r) => r end)).
- (* FI_text *)
apply (l ++ string_of_format CS fl' stuff).
- (* FI_error *)
apply nil.
Defined.

Section file_id.

Class FileId := { file_id : Type; stdin : file_id; stdout : file_id }.
Context {FI : FileId}.
Context {E : Type -> Type} `{IO_event(file_id := file_id) -< E} {CS : compspecs}.

Axiom file_at : file_id -> val -> mpred.

Axiom file_at_local_facts:
   forall f p, file_at f p |-- !! (isptr p).

Class FileStruct := { abs_file :> FileId; FILEid : ident; reent : ident; f_stdin : ident; f_stdout : ident }.
Context {FS : FileStruct}.

Axiom reent_struct : val -> mpred.

Axiom init_stdio : emp |-- EX p : val, EX inp : val, EX outp : val, EX inp' : _, EX outp' : _,
  !!(JMeq inp' inp /\ JMeq outp' outp) && reent_struct p *
  field_at Ews (Tstruct reent noattr) [StructField f_stdin] inp' p *
  field_at Ews (Tstruct reent noattr) [StructField f_stdout] outp' p *
  file_at stdin inp * file_at stdout outp.

Definition get_reent_spec :=
  WITH p : val
  PRE [ ]
    PROP ()
    PARAMS() GLOBALS ()
    SEP (reent_struct p)
  POST [ tptr (Tstruct reent noattr) ]
    PROP ()
    LOCAL (temp ret_temp p)
    SEP (reent_struct p).

Definition fprintf_spec_parametrized FILEid (fmtz: list Z) :=
  let fl := interpret_format_string fmtz in
  NDmk_funspec
    (((  (*1%positive, *) tptr (Tstruct FILEid noattr)) ::
      ((*2%positive,*) tptr tschar) :: 
      format_argtys fl),
     tint)
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}
     (val * share * list byte * val * format_stuff fl * (file_id * IO_itree))
     (fun x : (val * share * list byte * val * format_stuff fl * (file_id * IO_itree)) => 
      match x with (outp,sh,fmt,fmtp,stuff,(out,k)) =>
        PROPx (readable_share sh :: (fmt = map Byte.repr fmtz) ::
                      PROP_of_format fl stuff)
        (PARAMSx (outp :: fmtp :: PARAMS_of_format fl stuff)
         (GLOBALSx nil 
         (SEPx (cstring sh fmt fmtp :: file_at out outp :: ITREE (write_list out (string_of_format fl stuff);; k) :: SEP_of_format  fl stuff))))
      end)
     (fun x : (val * share * list byte * val * format_stuff fl * (file_id * IO_itree)) => 
      match x with (outp,sh,fmt,fmtp,stuff,(out,k)) =>
       EX n:int,
        PROPx nil 
        (LOCALx (temp ret_temp (Vint n)::nil)
         (SEPx (cstring sh fmt fmtp :: file_at out outp :: ITREE k :: SEP_of_format fl stuff)))
       end).

Definition printf_spec_parametrized (fmtz: list Z) :=
  let fl := interpret_format_string fmtz in
  NDmk_funspec 
    ((((*1%positive,*) tptr tschar) :: 
      format_argtys (*2%positive*) fl),
     tint)
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}
     (val * share * list byte * val * format_stuff fl * IO_itree)
     (fun x : (val * share * list byte * val * format_stuff fl * IO_itree) => 
      match x with (outp,sh,fmt,fmtp,stuff,k) =>
        PROPx (readable_share sh :: (fmt = map Byte.repr fmtz) :: 
                      PROP_of_format fl stuff)
        (PARAMSx (fmtp :: PARAMS_of_format fl stuff)
         (GLOBALSx nil 
         (SEPx (cstring sh fmt fmtp :: ITREE (write_list stdout (string_of_format fl stuff);; k) :: SEP_of_format  fl stuff))))
      end)
     (fun x : (val * share * list byte * val * format_stuff fl * IO_itree) => 
      match x with (outp,sh,fmt,fmtp,stuff,k) =>
       EX n:int,
        PROPx nil 
        (LOCALx (temp ret_temp (Vint n)::nil)
         (SEPx (cstring sh fmt fmtp :: ITREE k :: SEP_of_format fl stuff)))
       end).

Definition fprintf_placeholder_spec FILEid : funspec :=
  NDmk_funspec 
    ((((*1%positive,*) tptr (Tstruct FILEid noattr)) ::
      ((*2%positive,*) tptr tschar) :: nil),
     tint)
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}
     unit
     (fun x : unit =>  PROP (False) PARAMS () GLOBALS () SEP ())%argsassert
     (fun x : unit =>  PROP () LOCAL () SEP ()).

Definition printf_placeholder_spec : funspec :=
  NDmk_funspec 
    ((((*1%positive,*) tptr tschar) :: nil),
     tint)
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}
     unit
     (fun x : unit =>  PROP (False) PARAMS () GLOBALS () SEP ())%argsassert
     (fun x : unit =>  PROP () LOCAL () SEP ()).

Axiom fprintf_spec_sub:
  forall FILEid fmtz, 
   funspec_sub (fprintf_placeholder_spec FILEid)
      (fprintf_spec_parametrized FILEid fmtz).

Axiom printf_spec_sub:
  forall fmtz, 
   funspec_sub (printf_placeholder_spec)
      (printf_spec_parametrized fmtz).

End file_id.

#[export] Hint Resolve file_at_local_facts : saturate_local.

Ltac make_stdio :=
  sep_apply (@init_stdio _ _ _); let p := fresh "reentp" in let inp := fresh "inp" in let outp := fresh "outp" in
  let inp' := fresh "inp'" in let outp' := fresh "outp'" in Intros p inp outp inp' outp';
  change (reptype (tptr (Tstruct _ noattr))) with val in inp', outp';
  repeat match goal with H : JMeq _ _ |- _ => apply JMeq_eq in H; subst end.

Definition ascii2byte (a: Ascii.ascii) : byte :=
 Byte.repr (Z.of_N (Ascii.N_of_ascii a)).

Fixpoint string2bytes (s: string) : list byte :=
 match s with
 | EmptyString => nil
 | String a s' => ascii2byte a :: string2bytes s'
 end.

Definition Z2ascii (i : Z) : Ascii.ascii :=
 match i with
 | Zneg _ => Ascii.ascii_of_pos 255
 | Z0 => Ascii.ascii_of_nat 0
 | Zpos p => Ascii.ascii_of_pos p
 end.

Fixpoint listZ2string (il : list Z) : String.string :=
 match il with
 | i :: il' => String (Z2ascii i) (listZ2string il')
 | nil => EmptyString
 end.

Ltac is_posconst A x:=
 match A with
 | xH => constr:(x)
 | xI ?B => is_posconst B x
 | xO ?B => is_posconst B x
 end.

Ltac strip_int_repr s :=
 lazymatch s with
 | Int.repr Z0 :: nil => constr:(@nil Z)
 | Int.repr (Zpos ?c) :: ?s' => 
     let s'' := strip_int_repr s' in
     let x := constr:(Zpos c :: s'')
      in is_posconst c x
 | _ => fail 100 "foox" s
 end.

Ltac do_string2bytes :=
match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
 match R with context [data_at _ (tarray tschar ?n) 
                                     (map (Vint oo cast_int_int I8 Signed) ?il)] =>
  match il with context [Int.repr 0 :: nil] =>
    let zl := strip_int_repr il in
    let s := constr:(listZ2string zl) in
    let s := eval compute in s in
    let y := constr:(string2bytes s) in
    change  (map (Vint oo cast_int_int I8 Signed) il) 
             with (map Vbyte (y ++ [Byte.zero]))
 end end end.

Arguments string2bytes s : simpl never.

Fixpoint string2Zs (s: string) : list Z :=
 match s with
 | EmptyString => nil
 | String a s' => Z.of_N (Ascii.N_of_ascii a) :: string2Zs s'
 end.

Ltac check_fprintf_witness Hsub w :=
lazymatch type of Hsub with funspec_sub _ (NDmk_funspec _ _ ?t _ _) =>
 lazymatch t with (_ * _ * _ * _ * ?t' * _)%type =>
  lazymatch type of w with ?tw => 
   tryif unify tw t' then idtac
   else fail 10 "In forward_printf, your witness type does not match the format string.
Witness:" w "
Witness Type:" tw "
Format Type:" t' "
"
  end end end.

Ltac forward_fprintf' gv Pre id sub outv w w' :=
 lazymatch Pre with context [cstring ?sh (string2bytes ?s) (gv id)] => 
   let fmtz := constr:(string2Zs s) in
   let u := constr:(interpret_format_string fmtz) in
   let u := eval compute in u in
   let H := fresh "Hsub" in
   assert (H := sub fmtz);
    unfold fprintf_spec_parametrized, printf_spec_parametrized in H;
    change (interpret_format_string _) with u in H;
    simpl format_argtys in H;
    simpl format_stuff in H; 
    simpl PROP_of_format in H; 
    simpl PARAMS_of_format in H; 
    simpl SEP_of_format in H;
    check_fprintf_witness H w;
    forward_call H (outv, sh, string2bytes s, gv id, w, w');
    clear H
 end.

Ltac forward_fprintf outv w w' :=
 repeat rewrite <- seq_assoc;
 try match goal with |- semax _ _ (Scall _ _) _ =>
   rewrite -> semax_seq_skip
 end;
lazymatch goal with
 | gv: globals |- @semax ?cs _ _ ?Pre (Ssequence (Scall None (Evar _ _) (?f :: Evar ?id _ :: _)) _) _ =>
   let tf := constr:(typeof f) in
   let tf := eval hnf in tf in
   lazymatch tf with Tpointer (Tstruct ?FILEid _) _ =>
     let sub := constr:(fprintf_spec_sub(CS := cs) FILEid) in
       forward_fprintf' gv Pre id sub outv w w'
   end
end.

Ltac forward_printf w w' :=
 repeat rewrite <- seq_assoc;
 try match goal with |- semax _ _ (Scall _ _) _ =>
   rewrite -> semax_seq_skip
 end;
match goal with
 | gv: globals |- @semax ?cs _ _ ?Pre (Ssequence (Scall None (Evar _ _) (Evar ?id _ :: _)) _) _ =>
       forward_fprintf' gv Pre id (printf_spec_sub(CS := cs)) nullval w w'
end.

Fixpoint make_printf_specs' {FS : FileStruct} (defs: list (ident * globdef (fundef function) type)) : list (ident*funspec) :=
 match defs with
 | (i, Gfun (External (EF_external "fprintf" _) 
                       (Tcons (Tpointer (Tstruct id _) _) _) _ _)) :: defs' => 
         (i, fprintf_placeholder_spec id) :: make_printf_specs' defs'
 | (i, Gfun (External (EF_external "printf" _) _ _ _)) :: defs' => 
         (i, printf_placeholder_spec) :: make_printf_specs' defs'
 | (i, Gfun (External (EF_external "__getreent" _) _ _ _)) :: defs' =>
        (i, get_reent_spec) :: make_printf_specs' defs'
 | _ :: defs' => make_printf_specs' defs'
 | nil => nil
 end.

Ltac make_printf_specs prog :=
 let d := constr:(prog_defs prog) in
  let d := eval unfold prog in d in
match d with prog_defs (Clightdefs.mkprogram _ ?d' _ _ _) =>
 let s := constr:(make_printf_specs' d') in
 let s := eval simpl in s in
 exact s
 end.
