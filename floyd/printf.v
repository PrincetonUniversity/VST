Require Import VST.floyd.proofauto.


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

Fixpoint format_argtys (i: positive) (fl: list format_item) : list (ident * type) :=
 match fl with
 | FI_int :: fl' => (i, tint) :: format_argtys (Pos.succ i) fl'
 | FI_string :: fl' => (i, tptr tschar) :: format_argtys (Pos.succ i) fl'
 | FI_text _ :: fl' => format_argtys i fl'
 | FI_error :: fl' => format_argtys i fl'
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

Fixpoint LOCAL_of_format 
    (fl: list format_item) (id: ident) (stuff: format_stuff fl) {struct fl} : list localdef.
destruct fl as [ | fi fl'].
apply nil.
destruct fi; simpl in stuff.
- (* FI_int *)
apply (temp id (Vint (fst stuff)) :: LOCAL_of_format fl' (Pos.succ id) (snd stuff)).
- (* FI_string *)
apply (temp id (snd (fst stuff)) :: LOCAL_of_format fl' (Pos.succ id) (snd stuff)).
- (* FI_text *)
apply (LOCAL_of_format fl' id stuff).
- (* FI_error *)
apply (LOCAL_of_format fl' id stuff).
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

Definition fprintf_spec_parametrized {CS: compspecs} FILEid (fmtz: list Z) :=
  let fl := interpret_format_string fmtz in
  NDmk_funspec 
    (((1%positive, tptr (Tstruct FILEid noattr)) ::
      (2%positive, tptr tschar) :: 
      format_argtys 3%positive fl),
     tint)
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}
     (val * share * list byte * val * format_stuff fl)
     (fun x : (val * share * list byte * val * format_stuff fl) => 
      match x with (outp,sh,fmt,fmtp,stuff) =>
        PROPx (readable_share sh :: (fmt = map Byte.repr fmtz) :: 
                      PROP_of_format fl stuff)
        (LOCALx (temp 1 outp ::
                      LOCAL_of_format fl 3%positive stuff)
         (SEPx (cstring sh fmt fmtp :: SEP_of_format  fl stuff)))
      end)
     (fun x : (val * share * list byte * val * format_stuff fl) => 
      match x with (outp,sh,fmt,fmtp,stuff) =>
       EX n:int,
        PROPx nil 
        (LOCALx (temp ret_temp (Vint n)::nil)
         (SEPx (cstring sh fmt fmtp :: SEP_of_format fl stuff)))
       end).

Definition printf_spec_parametrized {CS: compspecs} (fmtz: list Z) :=
  let fl := interpret_format_string fmtz in
  NDmk_funspec 
    (((1%positive, tptr tschar) :: 
      format_argtys 2%positive fl),
     tint)
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}
     (val * share * list byte * val * format_stuff fl)
     (fun x : (val * share * list byte * val * format_stuff fl) => 
      match x with (outp,sh,fmt,fmtp,stuff) =>
        PROPx (readable_share sh :: (fmt = map Byte.repr fmtz) :: 
                      PROP_of_format fl stuff)
        (LOCALx (LOCAL_of_format fl 2%positive stuff)
         (SEPx (cstring sh fmt fmtp :: SEP_of_format  fl stuff)))
      end)
     (fun x : (val * share * list byte * val * format_stuff fl) => 
      match x with (outp,sh,fmt,fmtp,stuff) =>
       EX n:int,
        PROPx nil 
        (LOCALx (temp ret_temp (Vint n)::nil)
         (SEPx (cstring sh fmt fmtp :: SEP_of_format fl stuff)))
       end).

Definition fprintf_placeholder_spec FILEid : funspec :=
  NDmk_funspec 
    (((1%positive, tptr (Tstruct FILEid noattr)) ::
      (2%positive, tptr tschar) :: nil),
     tint)
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}
     unit
     (fun x : unit =>  PROP (False) LOCAL () SEP ())
     (fun x : unit =>  PROP () LOCAL () SEP ()).

Definition printf_placeholder_spec : funspec :=
  NDmk_funspec 
    (((1%positive, tptr tschar) :: nil),
     tint)
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}
     unit
     (fun x : unit =>  PROP (False) LOCAL () SEP ())
     (fun x : unit =>  PROP () LOCAL () SEP ()).

Axiom fprintf_spec_sub:
  forall {CS: compspecs} FILEid fmtz, 
   funspec_sub (fprintf_placeholder_spec FILEid)
      (fprintf_spec_parametrized FILEid fmtz).

Axiom printf_spec_sub:
  forall {CS: compspecs} fmtz, 
   funspec_sub (printf_placeholder_spec)
      (printf_spec_parametrized fmtz).

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
 lazymatch t with (_ * _ * _ * _ * ?t')%type =>
  lazymatch type of w with ?tw => 
   tryif unify tw t' then idtac
   else fail 10 "In forward_printf, your witness type does not match the format string.
Witness:" w "
Witness Type:" tw "
Format Type:" t' "
"
  end end end.

Ltac forward_fprintf' gv Pre id sub outv w :=
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
    simpl LOCAL_of_format in H; 
    simpl SEP_of_format in H;
    check_fprintf_witness H w;
    forward_call H (outv, sh, string2bytes s, gv id, w);
    clear H
 end.

Ltac forward_fprintf outv w :=
 repeat rewrite <- seq_assoc;
 try match goal with |- semax _ _ (Scall _ _) _ =>
   rewrite -> semax_seq_skip
 end;
lazymatch goal with
 | gv: globals |- @semax ?cs _ _ ?Pre (Ssequence (Scall None (Evar _ _) (?f :: Evar ?id _ :: _)) _) _ =>
   let tf := constr:(typeof f) in
   let tf := eval hnf in tf in
   lazymatch tf with Tpointer (Tstruct ?FILEid _) _ =>
     let sub := constr:(@fprintf_spec_sub cs FILEid) in
       forward_fprintf' gv Pre id sub outv w 
   end
end.

Ltac forward_printf w :=
 repeat rewrite <- seq_assoc;
 try match goal with |- semax _ _ (Scall _ _) _ =>
   rewrite -> semax_seq_skip
 end;
match goal with
 | gv: globals |- @semax ?cs _ _ ?Pre (Ssequence (Scall None (Evar _ _) (Evar ?id _ :: _)) _) _ =>
       forward_fprintf' gv Pre id (@printf_spec_sub cs) nullval w
end.

Fixpoint make_printf_specs' (defs: list (ident * globdef (fundef function) type)) : list (ident*funspec) :=
 match defs with
 | (i, Gfun (External (EF_external "fprintf" _) 
                       (Tcons (Tpointer (Tstruct id _) _) _) _ _)) :: defs' => 
         (i, fprintf_placeholder_spec id) :: make_printf_specs' defs'
 | (i, Gfun (External (EF_external "printf" _) _ _ _)) :: defs' => 
         (i, printf_placeholder_spec) :: make_printf_specs' defs'
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
