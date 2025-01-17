open Cerb_frontend
open AilSyntax

module Scopes = struct
  module C2A_eff = Cabs_to_ail_effect
  type scope = C2A_eff.scope

  let scopeEqual =
    C2A_eff.scopeEqual

  let string_of_scope =
    C2A_eff.string_of_scope

  type table = (scope, Symbol.sym, unit) Scope_table.t3

  let dict: Symbol.sym Lem_pervasives.mapKeyType_class = {
    mapKeyCompare_method=  Symbol.instance_Basic_classes_Ord_Symbol_sym_dict.compare_method
  }

  let empty: table =
    []

  let register sym (tbl: table) =
    Scope_table.register dict sym () tbl

  let create_scope scope (tbl: table) =
    Scope_table.create_scope dict scope tbl

  let resolve sym (tbl: table) =
    Scope_table.resolve dict sym tbl

  let current_scope_is tbl =
    Scope_table.current_scope_is tbl
end




type env = {
  counter: int;
  block_depth: int;
  scopes: (Cabs_to_ail_effect.scope, Symbol.sym, unit) Scope_table.t3;
}


let eq_sym sym1 sym2 =
  Symbol.instance_Basic_classes_Eq_Symbol_sym_dict.isEqual_method sym1 sym2

let show_sym sym =
  Pp_utils.to_plain_string (Pp_ail.pp_id sym)


type pointsto =
  | Current of ail_identifier
  | Local of Cabs_to_ail_effect.scope * ail_identifier
  | Funptr of ail_identifier
  | Global of ail_identifier
  | Wild
  | PTRVAL of pointsto


(* TODO: debug *)
let foo z =
  Lem_show.stringFromList begin
    let rec aux = function
      | Global sym ->
          "global: " ^ show_sym sym
      | Funptr sym ->
          "funptr: " ^ show_sym sym
      | Current sym ->
          "current: " ^ show_sym sym
      | Local (scope, sym) ->
          "local(scope: " ^ Scopes.string_of_scope scope ^ "): " ^ show_sym sym
      | Wild ->
          "wild"
      | PTRVAL pt ->
          "PTRVAL[" ^ aux pt ^ "]" in
    aux
  end z

let rec strip_PTRVAL = function
  | PTRVAL z ->
      strip_PTRVAL z
  | z ->
      z

(* returns [[true]] iff pt1 extends (strictly) further than pt2 *)
let gt_pointsto (pt1: pointsto) (pt2: pointsto) =
  let open Cabs_to_ail_effect in
  (* removing the PTRVAL, we know we are dealing with an rvalue *)
  let pt2 = strip_PTRVAL pt2 in
  match pt1, pt2 with
  | Current _, _ ->
      false
  | Local (Scope_block n1, _), Local (Scope_block n2, _) ->
      n1 < n2
  | Local _, Local _ ->
      (* TODO: remove the scopes and only have block id *)
      assert false
  | Funptr _, _
  | _, Funptr _ ->
      (* TODO: this doesn't match the spec, but does correspond to no escape *)
      false
  | Global _, (Current _ | Local _) ->
      true
  | Local _, Current _ ->
      true
  | _, Wild ->
      false
  | Wild, _ ->
      true
  | _ ->
      false


let classify sigm env sym =
  match List.assoc_opt sym sigm.declarations with
    | Some (_, _, Decl_object _) ->
        Global sym
    | Some (_, _, Decl_function _) ->
        Funptr sym
    | None ->
        begin match Scopes.resolve sym env.scopes with
          | None ->
              assert false
          | Some (scope, ()) ->
              if Scopes.(scopeEqual scope (current_scope_is env.scopes)) then
                Current sym
              else
                Local (scope, sym)
        end


let get_ctype (AnnotatedExpression(gtc,_,_,_)) : Ctype.ctype =
  (* TODO: these are taken from ail_to_coq.ml (should we just export them in the .mli ?) *)
  let c_type_of_type_cat = function
    | GenTypes.LValueType(_,c_ty,_) -> c_ty
    | GenTypes.RValueType(c_ty)     -> c_ty in
  let to_type_cat tc =
    let loc = Cerb_location.unknown in
    let impl = Ocaml_implementation.hafniumIntImpl in
    let m_tc = GenTypesAux.interpret_genTypeCategory loc impl tc in
    match ErrorMonad.runErrorMonad m_tc with
      | Either.Right(tc) -> tc
      | Either.Left(_,_) -> assert false (* FIXME possible here? *) in
  c_type_of_type_cat (to_type_cat gtc)


let ptr_taints : ((ail_identifier * pointsto list) list) ref =
  ref []


let get_ptr_taints xs =
  List.fold_left (fun acc pt ->
    match pt with
    | Current sym
    | Local (_, sym)
    | Global sym ->
        begin match List.assoc_opt sym !ptr_taints with
          | Some z ->
              z
          | None ->
              [ Wild ]
        end
    | Funptr _
    | Wild ->
        acc
    | PTRVAL _ ->
        acc (* TODO: assignment to an lvalue resulting from a deref already gives
               a warning, so we can ignore this case here *)
  ) [] xs

let points_to classify expr =
  let is_lvalue =
    match expr with
      | AnnotatedExpression (GenTypes.GenLValueType _, _, _, _) ->
          true
      | AnnotatedExpression (GenTypes.GenRValueType _, _, _, _) ->
          false in

  let rec aux (AnnotatedExpression (_, _, loc, expr_)) =
    match expr_ with
      | AilEbuiltin _
      | AilEstr _
      | AilEconst _
      | AilEsizeof _
      | AilEalignof _
      | AilEreg_load _
      | AilEsizeof_expr _
      | AilEoffsetof _
      | AilEassert _ ->
          []
      | AilEident sym ->
          [classify sym]
      | AilEunary (Address, e) ->
          List.map (fun z -> PTRVAL z) (aux e)

      | AilEunary (Indirection, e) ->
          let pts = aux e in
          let pts_deref =
            List.fold_left (fun acc pt ->
              match pt with
                | PTRVAL pt' ->
                    pt' :: acc
                | _ ->
                    acc
              ) [] pts in
          begin match AilTypesAux.referenced_type (get_ctype e) with
            | Some ref_ty when AilTypesAux.is_pointer ref_ty ->
                if pts <> [] && List.for_all (function PTRVAL _ -> true | _ -> false) pts then
                  (* the lvalue can only point to a known object, so we can stay precise *)
                  get_ptr_taints pts_deref
                else
                  [ Wild ]
            | _ ->
                if is_lvalue then
                  if pts <> [] && List.for_all (function PTRVAL _ -> true | _ -> false) pts then
                    (* the lvalue can only point to a known object, so we can stay precise *)
                    pts_deref
                  else
                    [ Wild ]
                else
                  pts_deref
          end
      | AilEunary (_, e) ->
          aux e
      | AilEcast (_, _, e) ->
          aux e
      | AilEcompound (_, _, e) ->
          []
      | AilEmemberof (e, _) ->
          aux e
      | AilEmemberofptr (e, _) ->
          aux e
      | AilEannot (_, e) ->
          aux e

      | AilEva_start _
      | AilEva_arg _
      | AilEva_end _
      | AilEva_copy _ ->
          []

      | AilEprint_type e
      | AilEbmc_assume e ->
          aux e

      | AilErvalue e ->
          if AilTypesAux.is_pointer (get_ctype e) then
            (* if we read the value of a pointer, this can point to anything that has
               been stored on that pointer *)
            get_ptr_taints (aux e)
          else
            []
      | AilEarray_decay e ->
          []
      | AilEfunction_decay e ->
          []
      | AilEbinary (e1, _, e2) ->
          aux e1 @ aux e2
      | AilEassign (e1, e2) ->
          aux e2
      | AilEcompoundAssign (e1, _, e2) ->
          aux e2
      | AilEcond (_, None, e3) ->
          aux e3
      | AilEcond (_, Some e2, e3) ->
          aux e2 @ aux e3

      | AilEcall (e, es) ->
          []

      | AilEgeneric (e ,gas) ->
          []
      | AilEarray (_, _, xs) ->
          []
      | AilEstruct (_, xs) ->
          []
      | AilEunion (_, _, e_opt) ->
          []
      | AilEatomic e ->
          aux e
      | AilEgcc_statement _ ->
          Panic.panic loc "Not implemented GCC statement expr." (* TODO *)
  in
  aux expr


(* ************************************************************************** *)
(* Warning for unsequenced function calls *)

type unseq_status =
    (* HACK: empty list is for the occurence of at least one wild call *)
  | HAS_CALLS of ail_identifier list
  | NO_CALL

let merge_status xs =
  let rec aux acc = function
    | [] ->
        if acc = [] then
          NO_CALL
        else
          HAS_CALLS acc
    | NO_CALL :: xs ->
        aux acc xs
    | HAS_CALLS calls :: xs ->
        aux (calls @ acc) xs
  in aux [] xs


let is_unseq = function
  | Comma | And | Or ->
      false
  | Arithmetic _
  | Lt | Gt | Le | Ge | Eq | Ne ->
      true

let merge_pointsto xss =
(*
  let eq pt1 pt2 =
    match pt1, pt2 with
      | `Current sym1, `Current sym2
      | `Local (_, sym1), `Local (_, sym2)
      | `Funptr sym1, `Funptr sym2
      | `Global sym1, `Global sym2 ->
          eq_sym sym1 sym2
      | `Wild, `Wild ->
          true
      | _ ->
          false in
  List.fold_left (fun acc pts ->
    let pts' =
      List.filter (fun pt -> not (List.exists (fun z -> eq pt z) acc)) pts in
      pts' @ acc
  ) [] xss
*)
  List.concat xss


type taint =
  [ `LOAD of pointsto | `STORE of pointsto | `CALL_WILD | `CALL of ail_identifier ]


let potential_races : ((Cerb_location.t * taint list * taint list) list) ref =
  ref []


let rec taint_expr points_to (AnnotatedExpression (_, _, loc, expr_)) =
  let self = taint_expr points_to in
  match expr_ with
    | AilErvalue e ->
        List.map (fun z -> `LOAD z) (points_to e)

    | AilEoffsetof _
    | AilEbuiltin _
    | AilEstr _
    | AilEconst _
    | AilEident _
    | AilEsizeof _
    | AilEalignof _
    | AilEreg_load _
    | AilEunion (_, _, None) ->
        []

    | AilEunary (_, e)
    | AilEcast (_, _, e)
    | AilEassert e
    | AilEcompound (_, _, e)
    | AilEmemberof (e, _)
    | AilEmemberofptr (e, _)
    | AilEsizeof_expr e
    | AilEannot (_, e)
    | AilEva_start (e, _)
    | AilEva_arg (e, _)
    | AilEva_end e
    | AilEprint_type e
    | AilEbmc_assume e
    | AilEarray_decay e
    | AilEfunction_decay e
    | AilEunion (_, _, Some e)
    | AilEatomic e ->
        self e

    | AilEbinary (e1, _, e2) ->
        begin match self e1, self e2 with
          | [], xs
          | xs, [] ->
              xs
          | xs1, xs2 ->
              potential_races := (loc, xs1, xs2) :: !potential_races;
              merge_pointsto [xs1; xs2]
        end

    | AilEassign (e1, e2)
    | AilEcompoundAssign (e1, _, e2) ->
        merge_pointsto [List.map (fun z -> `STORE z) (points_to e1); self e1; self e2]

    | AilEcond (e1, None, e3) ->
          merge_pointsto [self e1; self e3]
    | AilEcond (e1, Some e2, e3) ->
          merge_pointsto [self e1; self e2; self e3]
    | AilEcall (e, es) ->
        begin match e with
          | AnnotatedExpression (_, _, _, AilEfunction_decay (AnnotatedExpression (_, _, _, AilEident f))) ->
              `CALL f
          | _ ->
              `CALL_WILD
        end :: merge_pointsto (List.map self es)
    | AilEgeneric (e, gas) ->
        merge_pointsto begin
          self e ::
          List.map (function
            | AilGAtype (_, e)
            | AilGAdefault e ->
                self e) gas
        end
    | AilEarray (_, _, xs) ->
        merge_pointsto (List.map (function Some e -> self e | None -> []) xs)
    | AilEstruct (_, xs) ->
       merge_pointsto (List.map (function (_, Some e) -> self e | (_, None) -> []) xs)
    | AilEva_copy (e1, e2) ->
        merge_pointsto [self e1; self e2]
    | AilEgcc_statement _ ->
        Panic.panic loc "Not implemented GCC statement expr." (* TODO *)

let taints_of_functions sigm =
  List.fold_left (fun acc (sym_decl, (_, _, decl)) ->
    match decl with
      | Decl_object _ ->
          acc
      | Decl_function _ ->
          begin match List.assoc_opt sym_decl sigm.function_definitions with
            | None ->
                (* no definition for this function, assuming wild taint *)
                (sym_decl, [`STORE Wild]) :: acc
            | Some (_, _, _, params, stmt) ->
                let fun_scopes =
                  List.fold_left (fun acc sym ->
                    Scopes.register sym acc
                ) (Scopes.(create_scope (Cabs_to_ail_effect.Scope_block 0) empty)) params in
                let rec fold_stmt env (AnnotatedStatement (_, _, stmt_)) =
                  let taint_expr e = taint_expr (points_to (classify sigm env)) e in
                  match stmt_ with
                    | AilSskip
                    | AilSbreak
                    | AilScontinue
                    | AilSreturnVoid
                    | AilSgoto _ ->
                        [] (* points to nothing *)
                    | AilSexpr e
                    | AilSreturn e
                    | AilSreg_store (_, e) ->
                        taint_expr e
                    | AilSblock (bs, ss) ->
                        let new_scopes =
                          List.fold_left (fun acc (sym, _) ->
                            Scopes.register sym acc
                          ) (Scopes.create_scope (Cabs_to_ail_effect.Scope_block env.counter) env.scopes) bs in
                        let env' = {
                          counter= env.counter + 1;
                          block_depth= env.block_depth + 1;
                          scopes = new_scopes;
                        } in
                        merge_pointsto (List.map (fold_stmt env') ss)
                    | AilSif (e, s1, s2) ->
                        merge_pointsto [taint_expr e; fold_stmt env s1; fold_stmt env s2]
                    | AilSwhile (e, s, _)
                    | AilSdo (s, e, _)
                    | AilSswitch (e, s) ->
                        merge_pointsto [taint_expr e; fold_stmt env s]
                    | AilScase (_, s)
                    | AilScase_rangeGNU (_, _, s)
                    | AilSdefault s
                    | AilSlabel (_, s, _) ->
                        fold_stmt env s
                    | AilSdeclaration xs ->
                        merge_pointsto (List.filter_map (fun (_, e_opt) -> Option.map taint_expr e_opt) xs)
                    | AilSpar ss ->
                        merge_pointsto (List.map (fold_stmt env) ss)
                    | AilSmarker(_,_) -> assert false (* FIXME *)
                in
                (sym_decl, fold_stmt { counter= 1; block_depth= 0; scopes= fun_scopes } stmt) :: acc
          end
  ) [] sigm.declarations


let resolve_calls xs =
  List.map (fun (fsym, pts) ->
    let pts' = List.fold_left (fun acc pt ->
      match pt with
        | `CALL sym ->
            if sym = fsym then
              acc
            else
              merge_pointsto [List.assoc sym xs; acc]
        | `CALL_WILD ->
            [`STORE Wild]
        | z ->
            z :: acc
    ) [] pts in
    (fsym, pts')
  ) xs


let may_alias pts1 pts2 =
  List.exists (fun (pt1, pt2) ->
    match pt1, pt2 with
      | `LOAD _, `LOAD _ ->
          false
      | `STORE z1, `STORE z2
      | `STORE z1, `LOAD z2
      | `LOAD z1, `STORE z2 ->
          begin match z1, z2 with
            | Wild, _
            | _, Wild ->
                true
            | Current sym1, Current sym2
            | Local (_, sym1), Local (_, sym2)
            | Funptr sym1, Funptr sym2
            | Global sym1, Global sym2 ->
                eq_sym sym1 sym2
            | _, _ ->
                false
          end
      | _ ->
          assert false (* shouldn't happen after CALLs resolution *)
  ) (Utils.product_list pts1 pts2)


let warn_unseq taints_map expr =
  let rec aux (AnnotatedExpression (_, _, loc, expr_)) =
    match expr_ with
      | AilEoffsetof _
      | AilEbuiltin _
      | AilEstr _
      | AilEconst _
      | AilEident _
      | AilEsizeof _
      | AilEalignof _
      | AilEreg_load _
      | AilEunion (_, _, None) ->
          NO_CALL

      | AilEunary (_, e)
      | AilEcast (_, _, e)
      | AilEassert e
      | AilEcompound (_, _, e)
      | AilEmemberof (e, _)
      | AilEmemberofptr (e, _)
      | AilEsizeof_expr e
      | AilEannot (_, e)
      | AilEva_start (e, _)
      | AilEva_arg (e, _)
      | AilEva_end e
      | AilEprint_type e
      | AilEbmc_assume e
      | AilErvalue e
      | AilEarray_decay e
      | AilEfunction_decay e
      | AilEunion (_, _, Some e)
      | AilEatomic e ->
          aux e

      | AilEbinary (e1, bop, e2) when is_unseq bop ->
          begin match aux e1, aux e2 with
            | HAS_CALLS calls1, HAS_CALLS calls2 ->
                HAS_CALLS (calls1 @ calls2)
            | NO_CALL, HAS_CALLS calls
            | HAS_CALLS calls, NO_CALL ->
                HAS_CALLS calls
            | NO_CALL, NO_CALL ->
                NO_CALL
          end

      | AilEbinary (e1, _, e2)
      | AilEassign (e1, e2)
      | AilEcompoundAssign (e1, _, e2) ->
          merge_status [aux e1; aux e2]

      | AilEcond (e1, None, e3) ->
          merge_status [aux e1; aux e3]
      | AilEcond (e1, Some e2, e3) ->
          merge_status [aux e1; aux e2; aux e3]

      | AilEcall (e, es) ->
          merge_status (begin match e with
            | AnnotatedExpression (_, _, _, AilEfunction_decay (AnnotatedExpression (_, _, _, AilEident f))) ->
                [HAS_CALLS [f]]
            | _ ->
                [HAS_CALLS []]
          end @ (List.map aux es))

      | AilEgeneric (e, gas) ->
          merge_status begin
            aux e ::
            List.map (function
              | AilGAtype (_, e)
              | AilGAdefault e ->
                  aux e) gas
          end
      | AilEarray (_, _, xs) ->
          merge_status (List.map (function Some e -> aux e | None -> NO_CALL) xs)
      | AilEstruct (_, xs) ->
          merge_status (List.map (function (_, Some e) -> aux e | (_, None) -> NO_CALL) xs)
      | AilEva_copy (e1, e2) ->
          merge_status [aux e1; aux e2]
      | AilEgcc_statement _ ->
          Panic.panic loc "Not implemented GCC statement expr." (* TODO *)
  in
  ignore (aux expr)



(* ************************************************************************** *)
(* Driver *)
let warn_file (_, sigm) =
  let taints_map = resolve_calls (taints_of_functions sigm) in

  let rec aux_expr env (AnnotatedExpression (_, _, loc, expr_)) =
    let self = aux_expr env in
    match expr_ with
      | AilEbuiltin _
      | AilEstr _
      | AilEconst _
      | AilEident _
      | AilEsizeof _
      | AilEalignof _
      | AilEreg_load _ ->
          ()

      | AilEassign (e1, e2)
      | AilEcompoundAssign (e1, _, e2) ->
          (* Warn if [[e2]] points to objects whose scope is smaller than the scope of
             the object referred by the lvalue [[e1]] *)
          let xs1 = points_to (classify sigm env) e1 in
          let xs2 = points_to (classify sigm env) e2 in

          let sym_of = function
            | Current sym
            | Local (_, sym)
            | Global sym ->
                Some sym
            | Funptr _
            | Wild
            | PTRVAL _ -> (* TODO: check this one *)
                None in
          List.iter (fun pt ->
            match sym_of pt with
              | Some sym ->
                  let old =
                    begin match List.assoc_opt sym !ptr_taints with
                      | None    -> []
                      | Some xs -> xs
                    end in
                  ptr_taints := (sym, (xs2 @ old)) :: List.remove_assoc sym !ptr_taints (* TODO: use a map ... *)
              | None ->
                  ()
          ) xs1;

          if xs2 <> [] && List.exists (fun (x, y) -> gt_pointsto x y) (Utils.product_list xs1 xs2) then
            Panic.wrn (Some loc) "the address of a block-scoped variable may be escaping";
(*
(*          else *)
            Printf.printf "%sASSIGN[%s] ==> lvalue: %s -- e2: %s\x1b[0m\n"
              (if List.exists (fun (x, y) -> gt_pointsto x y) (Utils.product_list xs1 xs2) then "\x1b[31m" else "")
              (Cerb_location.location_to_string loc)
              (foo xs1)
              (foo xs2);
*)


      | AilEunary (_, e)
      | AilEcast (_, _, e)
      | AilEassert e
      | AilEcompound (_, _, e)
      | AilEmemberof (e, _)
      | AilEmemberofptr (e, _)
      | AilEsizeof_expr e
      | AilEannot (_, e)
      | AilEva_start (e, _)
      | AilEva_arg (e, _)
      | AilEva_end e
      | AilEprint_type e
      | AilEbmc_assume e
      | AilErvalue e
      | AilEarray_decay e
      | AilEfunction_decay e
      | AilEatomic e ->
          self e
      | AilEbinary (e1, _, e2)
      | AilEva_copy (e1, e2) ->
          self e1;
          self e2
      | AilEcond (e1, None, e3) ->
          self e1;
          self e3
      | AilEcond (e1, Some e2, e3) ->
          self e1;
          self e2;
          self e3
      | AilEcall (e, es) ->
          self e;
          List.iter self es
      | AilEoffsetof _ ->
          ()
      | AilEgeneric (e ,gas) ->
          self e;
          List.iter (function
            | AilGAtype (_, e)
            | AilGAdefault e ->
                self e
          ) gas
      | AilEarray (_, _, xs) ->
          List.iter (function
            | Some e ->
                self e
            | None ->
                ()
          ) xs
      | AilEstruct (_, xs) ->
          List.iter (function
            | (_, Some e) ->
                self e
            | (_, None) ->
                ()
          ) xs
      | AilEunion (_, _, e_opt) ->
          begin match e_opt with
            | Some e ->
                self e
            | None ->
                ()
          end
      | AilEgcc_statement _ ->
          Panic.panic loc "Not implemented GCC statement expr." (* TODO *)
  in
  let rec aux env (AnnotatedStatement (loc, _, stmt_)) =
    let self = aux env in
    let warn_unseq e = warn_unseq taints_map e in
    match stmt_ with
      | AilSskip ->
          ()
      | AilSexpr e
      | AilSreturn e ->
          aux_expr env e;
          warn_unseq e
      | AilSblock (bs, ss) ->
          let new_scopes =
            List.fold_left (fun acc (sym, _) ->
              Scopes.register sym acc
            ) (Scopes.create_scope (Cabs_to_ail_effect.Scope_block env.counter) env.scopes) bs in
          let env' = {
            counter= env.counter + 1;
            block_depth= env.block_depth + 1;
            scopes = new_scopes;
          } in
          List.iter (aux env') ss
      | AilSif (e, s1, s2) ->
          aux_expr env e;
          warn_unseq e;
          self s1;
          self s2
      | AilSwhile (e, s, _) ->
          self s;
          aux_expr env e;
          warn_unseq e
      | AilSdo (s, e, _) ->
          aux_expr env e;
          warn_unseq e;
          self s
      | AilSbreak
      | AilScontinue
      | AilSreturnVoid ->
          ()
      | AilSswitch (e, s) ->
          aux_expr env e;
          warn_unseq e;
          self s
      | AilScase (_, s)
      | AilScase_rangeGNU (_, _, s)
      | AilSdefault s
      | AilSlabel (_, s, _) ->
          self s
      | AilSgoto _ ->
          ()
      | AilSdeclaration xs ->
          List.iter (fun (sym, e_opt) ->
            match e_opt with
              | None -> ()
              | Some e ->
                  (* We need to record the tainting if [[sym]] is a pointer *)
                  let pts = points_to (classify sigm env) e in
                  let old =
                    begin match List.assoc_opt sym !ptr_taints with
                      | None    -> []
                      | Some xs -> xs
                    end in
                  ptr_taints := (sym, (pts @ old)) :: List.remove_assoc sym !ptr_taints; (* TODO: use a map ... *)
                  aux_expr env e;
                  warn_unseq e;
          ) xs
      | AilSpar ss ->
          List.iter (aux { env with block_depth= 0 }) ss
      | AilSreg_store (_, e) ->
          aux_expr env e;
          warn_unseq e
      | AilSmarker(_,_) -> assert false (* FIXME *)
  in
  List.iter (fun (fsym, (_, _, _, params, stmt)) ->
    (* NOTE: following (§6.2.1#4), the function parameters are placed in a block scope *)
    let fun_scopes =
      List.fold_left (fun acc sym ->
        Scopes.register sym acc
      ) (Scopes.(create_scope (Cabs_to_ail_effect.Scope_block 0) empty)) params in
    aux { counter= 1; block_depth= 0; scopes= fun_scopes } stmt;
    flush_all ()
  ) sigm.function_definitions;

  let resolve_calls2 pts =
    List.fold_left (fun acc pt ->
      match pt with
      | `CALL sym ->
          merge_pointsto [List.assoc sym taints_map; acc]
      | `CALL_WILD ->
          [`STORE Wild]
      | z ->
          z :: acc
    ) [] pts in
  (* This display the warning for potential nondeterminism from unsequenced calls *)
  List.iter (fun (loc, xs1, xs2) ->
    if may_alias (resolve_calls2 xs1) (resolve_calls2 xs2) then
      Panic.wrn (Some loc) "a function call potentially introduces non-determinism"
  ) (List.rev !potential_races)
