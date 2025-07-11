open Format
open Extra
open Panic
open Coq_ast
open Rc_annot
open Comment_annot

(* Flags set by CLI. *)
let print_expr_locs = ref true
let print_stmt_locs = ref true
let no_mem_cast = ref false

let pp_str = pp_print_string

let pp_as_tuple : 'a pp -> 'a list pp = fun pp ff xs ->
  match xs with
  | []      -> pp_str ff "()"
  | [x]     -> pp ff x
  | x :: xs -> fprintf ff "(%a" pp x;
               List.iter (fprintf ff ", %a" pp) xs;
               pp_str ff ")"

let pp_encoded_patt_name : bool -> string list pp = fun used ff xs ->
  match xs with
  | []  -> pp_str ff (if used then "unit__" else "_")
  | [x] -> pp_str ff x
  | _   -> pp_str ff "patt__"

(* Print projection to get the [i]-th element of a tuple with [n] elements. *)
let rec pp_projection : int -> int pp = fun n ff i ->
  match n with
  | 1                -> ()
  | _ when i = n - 1 -> fprintf ff ".2"
  | _                -> fprintf ff ".1%a" (pp_projection (n - 1)) i

let pp_encoded_patt_bindings : string list pp = fun ff xs ->
  let nb = List.length xs in
  if nb <= 1 then () else
  let pp_let i x =
    fprintf ff "let %s := patt__%a in@;" x (pp_projection nb) i
  in
  List.iteri pp_let xs

let pp_sep : string -> 'a pp -> 'a list pp = fun sep pp ff xs ->
  match xs with
  | []      -> ()
  | x :: xs -> pp ff x; List.iter (fprintf ff "%s%a" sep pp) xs

let pp_as_prod : 'a pp -> 'a list pp = fun pp ff xs ->
  match xs with
  | [] -> pp_str ff "()"
  | _  -> pp_sep " * " pp ff xs

let pp_id_args : bool -> string -> string list pp = fun need_paren id ff xs ->
  if xs <> [] && need_paren then pp_str ff "(";
  pp_str ff id; List.iter (fprintf ff " %s") xs;
  if xs <> [] && need_paren then pp_str ff ")"

let pp_simple_coq_expr wrap ff coq_e =
  match coq_e with
  | Coq_ident(x)             -> pp_str ff x
  | Coq_all([Quot_plain(s)]) -> fprintf ff (if wrap then "(%s)" else "%s") s
  | _                        ->
  Panic.panic_no_pos "Antiquotation forbidden here." (* FIXME location *)

let pp_int_type : Coq_ast.int_type pp = fun ff it ->
  let pp fmt = Format.fprintf ff fmt in
  match it with
  | ItSize_t(true)      -> pp "ssize_t"
  | ItSize_t(false)     -> pp "size_t"
  | ItIntptr_t(true)    -> pp "intptr_t"
  | ItIntptr_t(false)   -> pp "uintptr_t"
  | ItPtrdiff_t         -> pp "ptrdiff_t"
  | ItI8(true)          -> pp "i8"
  | ItI8(false)         -> pp "u8"
  | ItI16(true)         -> pp "i16"
  | ItI16(false)        -> pp "u16"
  | ItI32(true)         -> pp "i32"
  | ItI32(false)        -> pp "u32"
  | ItI64(true)         -> pp "i64"
  | ItI64(false)        -> pp "u64"

let rec pp_layout : bool -> Coq_ast.layout pp = fun wrap ff layout ->
  let pp fmt = Format.fprintf ff fmt in
  match layout with
  | LVoid              -> pp "void_layout"
  | LBool              -> pp "bool_layout"
  | LPtr               -> pp "void*"
  | _ when wrap        -> pp "(%a)" (pp_layout false) layout
  | LStruct(id, false) -> pp "layout_of struct_%s" id
  | LStruct(id, true ) -> pp "ul_layout union_%s" id
  | LInt(i)            -> pp "it_layout %a" pp_int_type i
  | LArray(layout, n)  -> pp "mk_array_layout %a %s"
                            (pp_layout true) layout n

let rec pp_op_type : Coq_ast.op_type pp = fun ff ty ->
  let pp fmt = Format.fprintf ff fmt in
  match ty with
  | OpBool           -> pp "BoolOp"
  | OpInt(i)         -> pp "IntOp %a" pp_int_type i
  | OpPtr(_)         -> pp "PtrOp" (* FIXME *)
  | OpStruct(id, os) -> pp "StructOp struct_%s ([ %a ])" id (pp_sep " ; " pp_op_type) os
  | OpUntyped(ly)    -> pp "UntypedOp (%a)" (pp_layout false) ly

let pp_un_op : Coq_ast.un_op pp = fun ff op ->
  let pp fmt = Format.fprintf ff fmt in
  match op with
  | NotBoolOp  -> pp "NotBoolOp"
  | NotIntOp   -> pp "NotIntOp"
  | NegOp      -> pp "NegOp"
  | CastOp(ty) -> pp "(CastOp $ %a)" pp_op_type ty

let pp_bin_op : Coq_ast.bin_op pp = fun ff op ->
  pp_str ff @@
  match op with
  | AddOp     -> "+"
  | SubOp     -> "-"
  | MulOp     -> "×"
  | DivOp     -> "/"
  | ModOp     -> "%"
  | AndOp     -> "&"
  | OrOp      -> "|"
  | XorOp     -> "^"
  | ShlOp     -> "<<"
  | ShrOp     -> ">>"
  | EqOp      -> "="
  | NeOp      -> "!="
  | LtOp      -> "<"
  | GtOp      -> ">"
  | LeOp      -> "≤"
  | GeOp      -> "≥"
  | CommaOp   -> ","
  | LazyAndOp -> "&&"
  | LazyOrOp  -> "||"

let is_bool_result_op = fun op ->
  match op with
  | EqOp | NeOp | LtOp | GtOp | LeOp | GeOp -> true
  | LazyAndOp | LazyOrOp -> true
  | _ -> false

let rec pp_expr : Coq_ast.expr pp = fun ff e ->
  let pp fmt = Format.fprintf ff fmt in
  let pp_expr_body ff e =
    match Location.(e.elt) with
    | Var(None   ,_)                ->
        pp "\"_\""
    | Var(Some(x),g)                ->
        if g then fprintf ff "global_%s" x else fprintf ff "\"%s\"" x
    | Val(Null)                     ->
        pp "NULL"
    | Val(Void)                     ->
        pp "VOID"
    | Val(Int(s,it))                ->
        pp "i2v %s %a" s pp_int_type it
    | Val(SizeOf(ly))               ->
        pp "i2v (%a).(ly_size) %a" (pp_layout false) ly
          pp_int_type (ItSize_t false)
    | UnOp(op,ty,e)                 ->
        pp "UnOp %a (%a) (%a)" pp_un_op op pp_op_type ty pp_expr e
    | BinOp(op,ty1,ty2,e1,e2)       ->
        begin
          match (ty1, ty2, op) with
          (* Comma operator. *)
          | (_       , _       , CommaOp) ->
              pp "(%a) %a{%a, %a} (%a)" pp_expr e1 pp_bin_op op
                pp_op_type ty1 pp_op_type ty2 pp_expr e2
          (* Pointer offset operations. *)
          | (OpPtr(l), OpInt(_), AddOp  ) ->
              pp "(%a) at_offset{%a, PtrOp, %a} (%a)" pp_expr e1
                (pp_layout false) l pp_op_type ty2 pp_expr e2
          | (OpPtr(l), OpInt(_), SubOp  ) ->
              pp "(%a) at_neg_offset{%a, PtrOp, %a} (%a)" pp_expr e1
                (pp_layout false) l pp_op_type ty2 pp_expr e2
          (* Pointer difference. *)
          | (OpPtr(l1), OpPtr(l2), SubOp) ->
              pp "(%a) sub_ptr{%a, PtrOp, PtrOp} (%a)" pp_expr e1
                (pp_layout false) l1 pp_expr e2
          (* Pointer compared to 0 (Cerberus rejects non-0 integer values). *)
          | (OpInt(_) , OpPtr(l) , (EqOp | NeOp)) ->
              let e1 = {e1 with elt = UnOp(CastOp(ty2), ty1, e1)} in
              pp "(%a) %a{PtrOp, PtrOp, i32} (%a)" pp_expr e1
                pp_bin_op op pp_expr e2
          | (OpPtr(l) , OpInt(_) , (EqOp | NeOp)) ->
              let e2 = {e2 with elt = UnOp(CastOp(ty1), ty2, e2)} in
              pp "(%a) %a{PtrOp, PtrOp, i32} (%a)" pp_expr e1
                pp_bin_op op pp_expr e2
          (* Invalid operations mixing an integer and a pointer. *)
          | (OpPtr(_), OpInt(_), _      )
          | (OpInt(_), OpPtr(_), _      ) ->
              let loc = Location.to_cerb_loc e.loc in
              panic loc "Invalid use of binary operation [%a]." pp_bin_op op
          (* All other operations are defined. *)
          | _                             ->
              if is_bool_result_op op then
                pp "(%a) %a{%a, %a, i32} (%a)" pp_expr e1 pp_bin_op op
                  pp_op_type ty1 pp_op_type ty2 pp_expr e2
              else
                pp "(%a) %a{%a, %a} (%a)" pp_expr e1 pp_bin_op op
                  pp_op_type ty1 pp_op_type ty2 pp_expr e2
        end
    | Deref(atomic,ty,e)            ->
       if !no_mem_cast then
         if atomic then
           pp "!{%a, ScOrd, false} (%a)" pp_op_type ty pp_expr e
         else
           pp "!{%a, Na1Ord, false} (%a)" pp_op_type ty pp_expr e
        else
         if atomic then
           pp "!{%a, ScOrd} (%a)" pp_op_type ty pp_expr e
         else
           pp "!{%a} (%a)" pp_op_type ty pp_expr e
    | CAS(ty,e1,e2,e3)              ->
        pp "CAS@ (%a)@ (%a)@ (%a)@ (%a)" pp_op_type ty
          pp_expr e1 pp_expr e2 pp_expr e3
    | Call(e,es)        ->
      let pp_args _ es =
        let n = List.length es in
        let fn i e =
          pp (if i = n - 1 then "%a" else "%a ;@;") pp_expr e
        in
        List.iteri fn es
      in
      pp "Call (%a) [@@{expr} %a ]" pp_expr e pp_args es
    | IfE(ty,e1,e2,e3)              ->
        pp "IfE@ (%a)@ (%a)@ (%a)@ (%a)" pp_op_type ty
          pp_expr e1 pp_expr e2 pp_expr e3
    | SkipE(e)                      ->
        pp "SkipE (%a)" pp_expr e
    | Use(atomic,ty,e)              ->
       if !no_mem_cast then
         if atomic then
           pp "use{%a, ScOrd, false} (%a)" pp_op_type ty pp_expr e
         else
           pp "use{%a, Na1Ord, false} (%a)" pp_op_type ty pp_expr e
       else
         if atomic then
           pp "use{%a, ScOrd} (%a)" pp_op_type ty pp_expr e
         else
           pp "use{%a} (%a)" pp_op_type ty pp_expr e
    | AddrOf(e)                     ->
        pp "&(%a)" pp_expr e
    | LValue(e)                     ->
        pp "LValue (%a)" pp_expr e
    | GetMember(e,name,false,field) ->
        pp "(%a) at{struct_%s} %S" pp_expr e name field
    | GetMember(e,name,true ,field) ->
        pp "(%a) at_union{union_%s} %S" pp_expr e name field
    | OffsetOf(name,false,field)    ->
        pp "(OffsetOf (struct_%s) (%S))" name field
    | OffsetOf(name,true ,field)    ->
        pp "(OffsetOfUnion (union_%s) (%S))" name field
    | AnnotExpr(i,coq_e,e)          ->
        pp "AnnotExpr %i%%nat %a (%a)" i
          (pp_simple_coq_expr true) coq_e pp_expr e
    | Struct(id, fs)                ->
        pp "@[@[<hov 2>StructInit struct_%s [" id;
        let fn i (id, e) =
          let s = if i = List.length fs - 1 then "" else " ;" in
          pp "@;(%S, %a : expr)%s" id pp_expr e s
        in
        List.iteri fn fs;
        pp "@]@;]@]"
    | Macro(name, args, es, e)      ->
        pp "@[@[<hov 2>CheckedMacroE (%s %s) [" name (String.concat " " args);
        let fn i e =
          let s = if i = List.length es - 1 then "" else " ;" in
          pp "@;(%a : expr)%s" pp_expr e s
        in
        List.iteri fn es;
        pp "@]@;] (%a : expr)@]" pp_expr e
    | CopyAID(ot2, e1, e2)          ->
        pp "CopyAllocId (%a) (%a) (%a)" pp_op_type ot2 pp_expr e1 pp_expr e2
  in
  match Location.get e.loc with
  | Some(d) when !print_expr_locs ->
      pp "LocInfoE loc_%i (%a)" d.loc_key pp_expr_body e
  | _                             ->
      pp "%a" pp_expr_body e


let pp_if_join : string option pp = fun ff opt ->
  let pp fmt = Format.fprintf ff fmt in
    match opt with
    | None -> pp "None"
    | Some lb -> pp "Some %S" lb

let rec pp_stmt : Coq_ast.stmt pp = fun ff stmt ->
  let pp fmt = Format.fprintf ff fmt in
  if !print_stmt_locs then
    begin
      match Location.get stmt.loc with
      | None    -> ()
      | Some(d) -> pp "locinfo: loc_%i ;@;" d.loc_key
    end;
  match stmt.elt with
  | Goto(id)                      ->
      pp "Goto %S" id
  | Return(e)                     ->
      pp "Return @[<hov 0>(%a)@]" pp_expr e
  | Switch(it,e,map,bs,def)       ->
      pp "@[<v 2>Switch %a@;" pp_int_type it;
      pp "(%a)@;" pp_expr e;
      begin
        match map with
        | []         -> pp "∅@;"
        | (k,v)::map ->
        pp "@[<v 2>(@;<[ %s := %i%%nat ]> " k v;
        List.iter (fun (k,v) -> pp "$@;<[ %s := %i%%nat ]> " k v) map;
        pp "∅@]@;)@;"
      end;
      begin
        match bs with
        | []    -> pp "[]@;"
        | b::bs ->
        pp "@[<v 2>(@;(%a)" pp_stmt b;
        List.iter (pp " ::@;(%a)" pp_stmt) bs;
        pp " :: []@]@;)@;"
      end;
      pp "(%a)@]" pp_stmt def
  | Assign(atomic,ot,e1,e2,stmt) ->
      let order = if atomic then ", ScOrd" else "" in
      pp "@[<hov 2>%a <-{ %a%s }@ %a ;@]@;%a"
        pp_expr e1 pp_op_type ot order pp_expr e2 pp_stmt stmt
  | SkipS(stmt)                   ->
      pp_stmt ff stmt
  | If(ot,lb_opt,e,stmt1,stmt2)   ->
      pp "if{%a, %a}: @[<hov 0>%a@]@;then@;@[<v 2>%a@]@;else@;@[<v 2>%a@]"
        pp_op_type ot pp_if_join lb_opt pp_expr e pp_stmt stmt1 pp_stmt stmt2
  | Assert(ot,e,stmt)             ->
      pp "assert{%a}: (%a) ;@;%a" pp_op_type ot pp_expr e pp_stmt stmt
  | ExprS(annot, e, stmt)         ->
      let pp_expr_annot annot =
        match annot with
        | ExprAnnot_annot s    -> pp "annot: (%s) ;@;" s
        | ExprAnnot_assert(id) -> pp "annot: (AssertAnnot \"%i\") ;@;" id
      in
      Option.iter pp_expr_annot annot;
      pp "expr: (%a) ;@;%a" pp_expr e pp_stmt stmt

type import = string * string

let pp_import ff (from, mod_name) =
  Format.fprintf ff "From %s Require Import %s.@;" from mod_name

let pp_code : string -> import list -> Coq_ast.t pp =
    fun root_dir imports ff ast ->
  (* Formatting utilities. *)
  let pp fmt = Format.fprintf ff fmt in

  (* Printing some header. *)
  pp "@[<v 0>From caesium Require Export notation.@;";
  pp "From caesium Require Import tactics.@;";
  pp "From refinedc.typing Require Import annotations.@;";
  List.iter (pp_import ff) imports;
  pp "Set Default Proof Using \"Type\".@;@;";

  (* Printing generation data in a comment. *)
  pp "(* Generated from [%s]. *)@;" ast.source_file;

  (* Opening the section. *)
  pp "@[<v 2>Section code.";

  (* Printing of location data. *)
  if !print_expr_locs || !print_stmt_locs then
    begin
      let (all_locations, all_files) =
        let open Location in
        let locs = ref [] in
        let files = ref [] in
        let fn ({loc_file = file; _} as d) =
          locs := d :: !locs;
          if not (List.mem file !files) then files := file :: !files
        in
        Location.Pool.iter fn coq_locs;
        let locs = List.sort (fun d1 d2 -> d1.loc_key - d2.loc_key) !locs in
        let files = List.mapi (fun i s -> (s, i)) !files in
        (locs, files)
      in
      let pp_file_def (file, key) =
        let file =
          try Filename.relative_path root_dir file
          with Invalid_argument(_) -> file
        in
        fprintf ff "@;Definition file_%i : string := \"%s\"." key file
      in
      List.iter pp_file_def all_files;
      let pp_loc_def d =
        let open Location in
        pp "@;Definition loc_%i : location_info := " d.loc_key;
        pp "LocationInfo file_%i %i %i %i %i."
          (List.assoc d.loc_file all_files)
          d.loc_line1 d.loc_col1 d.loc_line2 d.loc_col2
      in
      List.iter pp_loc_def all_locations;
    end;

  (* Printing for struct/union members. *)
  let pp_members members is_struct =
    let nb_bytes = ref 0 in
    let n = List.length members in
    let fn i (id, (attrs, (align, size), layout)) =
      (* Insert padding for field alignment (for structs). *)
      if is_struct && !nb_bytes mod align <> 0 then
        begin
          let pad = align - !nb_bytes mod align in
          pp "@;(None, Layout %i%%nat 0%%nat);" pad;
          nb_bytes := !nb_bytes + pad;
        end;
      let sc = if i = n - 1 then "" else ";" in
      let some = if is_struct then "Some " else "" in
      pp "@;(%s%S, %a)%s" some id (pp_layout false) layout sc;
      nb_bytes := !nb_bytes + size
    in
    List.iteri fn members;
    (* Insert final padding if necessary. *)
    if is_struct then
      begin
        let max_align =
          let fn acc (_,(_,(align,_),_)) = max acc align in
          List.fold_left fn 1 members
        in
        let r = !nb_bytes mod max_align in
        if r <> 0 then pp ";@;(None, Layout %i%%nat 0%%nat)" (max_align - r)
      end
  in

  (* Definition of structs/unions. *)
  let pp_struct (id, decl) =
    pp "\n@;(* Definition of struct [%s]. *)@;" id;
    pp "@[<v 2>Program Definition struct_%s := {|@;" id;

    pp "@[<v 2>sl_members := [";
    pp_members decl.struct_members true;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations."
  in
  let pp_union (id, decl) =
    pp "\n@;(* Definition of union [%s]. *)@;" id;
    pp "@[<v 2>Program Definition union_%s := {|@;" id;

    pp "@[<v 2>ul_members := [";
    pp_members decl.struct_members false;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations."
  in
  let rec sort_structs found strs =
    match strs with
    | []                     -> []
    | (id, s) as str :: strs ->
    if List.for_all (fun id -> List.mem id found) s.struct_deps then
      str :: sort_structs (id :: found) strs
    else
      sort_structs found (strs @ [str])
  in
  let pp_struct_union ((_, {struct_is_union; _}) as s) =
    if struct_is_union then pp_union s else pp_struct s
  in
  List.iter pp_struct_union (sort_structs [] ast.structs);

  (* Definition of functions. *)
  let pp_function_def (id, def) =
    let deps = fst def.func_deps @ snd def.func_deps in
    pp "\n@;(* Definition of function [%s]. *)@;" id;
    pp "@[<v 2>Definition impl_%s " id;
    if deps <> [] then begin
      pp "(";
      List.iter (pp "global_%s ") deps;
      pp ": loc)";
    end;
    pp ": function := {|@;";

    pp "@[<v 2>f_args := [";
    begin
      let n = List.length def.func_args in
      let fn i (id, layout) =
        let sc = if i = n - 1 then "" else ";" in
        pp "@;(%S, %a)%s" id (pp_layout false) layout sc
      in
      List.iteri fn def.func_args
    end;
    pp "@]@;];@;";

    pp "@[<v 2>f_local_vars := [";
    begin
      let n = List.length def.func_vars in
      let fn i (id, layout) =
        let sc = if i = n - 1 then "" else ";" in
        pp "@;(%S, %a)%s" id (pp_layout false) layout sc
      in
      List.iteri fn def.func_vars
    end;
    pp "@]@;];@;";

    pp "f_init := \"#0\";@;";

    pp "@[<v 2>f_code := (";
    begin
      let fn id (attrs, stmt) =
        pp "@;@[<v 2><[ \"%s\" :=@;" id;

        pp_stmt ff stmt;
        pp "@]@;]> $";
      in
      SMap.iter fn def.func_blocks;
      pp "∅"
    end;
    pp "@]@;)%%E";
    pp "@]@;|}.";
  in
  let pp_function (id, def_or_decl) =
    match def_or_decl with
    | FDef(def) -> pp_function_def (id, def)
    | _         -> ()
  in
  List.iter pp_function ast.functions;

  (* Closing the section. *)
  pp "@]@;End code.@]"

let pp_code_vst : string -> import list -> Coq_ast.t pp =
    fun root_dir imports ff ast ->
  (* Formatting utilities. *)
  let pp fmt = Format.fprintf ff fmt in

  (* Printing some header. *)
  pp "@[<v 0>From caesium Require Export notation.@;";
  pp "From caesium Require Import tactics.@;";
  pp "From VST.typing Require Import annotations.@;";
  List.iter (pp_import ff) imports;
  pp "Set Default Proof Using \"Type\".@;@;";

  (* Printing generation data in a comment. *)
  pp "(* Generated from [%s]. *)@;" ast.source_file;

  (* Opening the section. *)
  pp "@[<v 2>Section code.";

  (* Printing of location data. *)
  if !print_expr_locs || !print_stmt_locs then
    begin
      let (all_locations, all_files) =
        let open Location in
        let locs = ref [] in
        let files = ref [] in
        let fn ({loc_file = file; _} as d) =
          locs := d :: !locs;
          if not (List.mem file !files) then files := file :: !files
        in
        Location.Pool.iter fn coq_locs;
        let locs = List.sort (fun d1 d2 -> d1.loc_key - d2.loc_key) !locs in
        let files = List.mapi (fun i s -> (s, i)) !files in
        (locs, files)
      in
      let pp_file_def (file, key) =
        let file =
          try Filename.relative_path root_dir file
          with Invalid_argument(_) -> file
        in
        fprintf ff "@;Definition file_%i : string := \"%s\"." key file
      in
      List.iter pp_file_def all_files;
      let pp_loc_def d =
        let open Location in
        pp "@;Definition loc_%i : location_info := " d.loc_key;
        pp "LocationInfo file_%i %i %i %i %i."
          (List.assoc d.loc_file all_files)
          d.loc_line1 d.loc_col1 d.loc_line2 d.loc_col2
      in
      List.iter pp_loc_def all_locations;
    end;

  (* Printing for struct/union members. *)
  let pp_members members is_struct =
    let nb_bytes = ref 0 in
    let n = List.length members in
    let fn i (id, (attrs, (align, size), layout)) =
      (* Insert padding for field alignment (for structs). *)
      if is_struct && !nb_bytes mod align <> 0 then
        begin
          let pad = align - !nb_bytes mod align in
          pp "@;(None, Layout %i%%nat 0%%nat);" pad;
          nb_bytes := !nb_bytes + pad;
        end;
      let sc = if i = n - 1 then "" else ";" in
      let some = if is_struct then "Some " else "" in
      pp "@;(%s%S, %a)%s" some id (pp_layout false) layout sc;
      nb_bytes := !nb_bytes + size
    in
    List.iteri fn members;
    (* Insert final padding if necessary. *)
    if is_struct then
      begin
        let max_align =
          let fn acc (_,(_,(align,_),_)) = max acc align in
          List.fold_left fn 1 members
        in
        let r = !nb_bytes mod max_align in
        if r <> 0 then pp ";@;(None, Layout %i%%nat 0%%nat)" (max_align - r)
      end
  in

  (* Definition of structs/unions. *)
  let pp_struct (id, decl) =
    pp "\n@;(* Definition of struct [%s]. *)@;" id;
    pp "@[<v 2>Program Definition struct_%s := {|@;" id;

    pp "@[<v 2>sl_members := [";
    pp_members decl.struct_members true;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations."
  in
  let pp_union (id, decl) =
    pp "\n@;(* Definition of union [%s]. *)@;" id;
    pp "@[<v 2>Program Definition union_%s := {|@;" id;

    pp "@[<v 2>ul_members := [";
    pp_members decl.struct_members false;
    pp "@]@;];@]@;|}.@;";
    pp "Solve Obligations with solve_struct_obligations."
  in
  let rec sort_structs found strs =
    match strs with
    | []                     -> []
    | (id, s) as str :: strs ->
    if List.for_all (fun id -> List.mem id found) s.struct_deps then
      str :: sort_structs (id :: found) strs
    else
      sort_structs found (strs @ [str])
  in
  let pp_struct_union ((_, {struct_is_union; _}) as s) =
    if struct_is_union then pp_union s else pp_struct s
  in
  List.iter pp_struct_union (sort_structs [] ast.structs);

  (* Definition of functions. *)
  let pp_function_def (id, def) =
    let deps = fst def.func_deps @ snd def.func_deps in
    pp "\n@;(* Definition of function [%s]. *)@;" id;
    pp "@[<v 2>Definition impl_%s " id;
    if deps <> [] then begin
      pp "(";
      List.iter (pp "global_%s ") deps;
      pp ": loc)";
    end;
    pp ": function := {|@;";

    pp "@[<v 2>f_args := [";
    begin
      let n = List.length def.func_args in
      let fn i (id, layout) =
        let sc = if i = n - 1 then "" else ";" in
        pp "@;(%S, %a)%s" id (pp_layout false) layout sc
      in
      List.iteri fn def.func_args
    end;
    pp "@]@;];@;";

    pp "@[<v 2>f_local_vars := [";
    begin
      let n = List.length def.func_vars in
      let fn i (id, layout) =
        let sc = if i = n - 1 then "" else ";" in
        pp "@;(%S, %a)%s" id (pp_layout false) layout sc
      in
      List.iteri fn def.func_vars
    end;
    pp "@]@;];@;";

    pp "f_init := \"#0\";@;";

    pp "@[<v 2>f_code := (";
    begin
      let fn id (attrs, stmt) =
        pp "@;@[<v 2><[ \"%s\" :=@;" id;

        pp_stmt ff stmt;
        pp "@]@;]> $";
      in
      SMap.iter fn def.func_blocks;
      pp "∅"
    end;
    pp "@]@;)%%E";
    pp "@]@;|}.";
  in
  let pp_function (id, def_or_decl) =
    match def_or_decl with
    | FDef(def) -> pp_function_def (id, def)
    | _         -> ()
  in
  List.iter pp_function ast.functions;

  (* Closing the section. *)
  pp "@]@;End code.@]"

type rec_mode =
  | Rec_none
  | Rec_in_def of string
  | Rec_in_lem of string

let (reset_nroot_counter, with_uid) : (unit -> unit) * string pp =
  let counter = ref (-1) in
  let with_uid ff s = incr counter; fprintf ff "\"%s_%i\"" s !counter in
  let reset _ = counter := -1 in
  (reset, with_uid)

let rec pp_quoted : type_expr pp -> type_expr quoted pp = fun pp_ty ff l ->
  let pp_quoted_elt ff e =
    match e with
    | Quot_plain(s) -> pp_str ff s
    | Quot_anti(ty) -> fprintf ff "(%a)" pp_ty ty
  in
  match l with
  | []     -> assert false (* Unreachable. *)
  | [e]    -> pp_quoted_elt ff e
  | e :: l -> fprintf ff "%a " pp_quoted_elt e; pp_quoted pp_ty ff l

and pp_coq_expr : bool -> type_expr pp -> coq_expr pp = fun wrap pp_ty ff e ->
  match e with
  | Coq_ident(x) -> pp_str ff x
  | Coq_all(l)   ->
      fprintf ff (if wrap then "(%a)" else "%a") (pp_quoted pp_ty) l

and pp_type_annot : type_expr pp -> coq_expr option pp = fun pp_ty ff eo ->
  Option.iter (fprintf ff " : %a" (pp_coq_expr false pp_ty)) eo

and pp_constr_rec : unit pp option -> rec_mode -> bool -> constr pp =
    fun pp_dots r wrap ff c ->
  let pp_ty = pp_type_expr_rec pp_dots r in
  let pp_coq_expr wrap = pp_coq_expr wrap pp_ty in
  let pp_constr = pp_constr_rec pp_dots r in
  let pp_kind ff k =
    match k with
    | Own     -> pp_str ff "◁ₗ"
    | Shr     -> pp_str ff "◁ₗ{Shr}"
    | Frac(e) -> fprintf ff "◁ₗ{%a}" (pp_coq_expr false) e
  in
  match c with
  (* Needs no wrapping. *)
  | Constr_Coq(e)       ->
      fprintf ff "⌜%a⌝" (pp_coq_expr false) e
  (* Apply wrapping. *)
  | _ when wrap         ->
      fprintf ff "(%a)" (pp_constr false) c
  (* No need for wrappin now. *)
  | Constr_Iris(l)      ->
      pp_quoted pp_ty ff l
  | Constr_exist(x,a,c) ->
      fprintf ff "∃ %s%a, %a" x (pp_type_annot pp_ty) a (pp_constr false) c
  | Constr_own(x,k,ty)  ->
      fprintf ff "%s %a %a" x pp_kind k pp_ty ty
  | Constr_val(x, ty)   ->
      fprintf ff "%s ◁ᵥ %a" x pp_ty ty
  | Constr_glob(x,ty)   ->
      fprintf ff "global_with_type %S Own %a" x pp_ty ty

and pp_type_expr_rec : unit pp option -> rec_mode -> type_expr pp =
    fun pp_dots r ff ty ->
  let pp_constr = pp_constr_rec pp_dots r in
  let rec pp_ty_annot ff a =
    pp_type_annot (pp false false) ff a
  and pp wrap rfnd ff ty =
    let pp_coq_expr wrap = pp_coq_expr wrap (pp false rfnd) in
    match ty with
    (* Don't need explicit wrapping. *)
    | Ty_Coq(e)          -> (pp_coq_expr wrap) ff e
    (* Remaining constructors (no need for explicit wrapping). *)
    | Ty_dots            ->
        begin
          match pp_dots with
          | None     -> Panic.panic_no_pos "Unexpected ellipsis."
          | Some(pp) ->
          fprintf ff (if wrap then "(@;  %a@;)" else "%a") pp ()
        end
    (* Insert wrapping if needed. *)
    | _ when wrap        -> fprintf ff "(%a)" (pp false rfnd) ty
    | Ty_refine(e,ty)    ->
        begin
          match (r, ty) with
          | (Rec_in_def(s), Ty_params(c,tys)) when c = s ->
              fprintf ff "self (%a" (pp_coq_expr true) e;
              List.iter (fprintf ff ", %a" (pp_arg true)) tys;
              fprintf ff ")"
          | (Rec_in_lem(s), Ty_params(c,tys)) when c = s ->
              fprintf ff "%a @@ " (pp_coq_expr true) e;
              if tys <> [] then pp_str ff "(";
              pp_str ff c;
              List.iter (fprintf ff " %a" (pp_arg true)) tys;
              if tys <> [] then pp_str ff ")"
          | (_              , _               )            ->
              fprintf ff "%a @@ %a" (pp_coq_expr true) e
                (pp true true) ty
        end
    | Ty_exists(xs,a,ty) ->
        fprintf ff "∃ₜ %a%a, %a%a" (pp_encoded_patt_name false) xs
          pp_ty_annot a pp_encoded_patt_bindings xs
          (pp false false) ty
    | Ty_constr(ty,c)    ->
        fprintf ff "constrained %a %a" (pp true false) ty
          (pp_constr true) c
    | Ty_params(id,tyas) ->
        let default () =
          pp_str ff id;
          List.iter (fprintf ff " %a" (pp_arg true)) tyas
        in
        match r with
        | Rec_in_def(s) when id = s ->
           (* We cannot use the ∃ₜ notation here as it hard-codes a
              rtype-to-type conversion.*)
            fprintf ff "tyexists (λ rfmt__, ";
            fprintf ff "self (rfmt__";
            List.iter (fprintf ff ", %a" (pp_arg true)) tyas;
            fprintf ff "))"
        | Rec_in_lem(s) when id = s ->
            fprintf ff "tyexists (λ rfmt__, ";
            fprintf ff "rfmt__ @@ ";
            default (); fprintf ff ")"
        | _                           ->
        match id with
        | "&frac"                  ->
            let (beta, ty) =
              match tyas with
              | [tya1; tya2] -> (tya1, tya2)
              | _            ->
                 Panic.panic_no_pos "[%s] expects two arguments." id
            in
            fprintf ff "&frac{%a} %a"
              (pp_arg false) beta (pp_arg true) ty
        | "optional" when not rfnd ->
            let (tya1, tya2) =
              match tyas with
              | [tya]        -> (tya, Ty_arg_expr(Ty_Coq(Coq_ident("null"))))
              | [tya1; tya2] -> (tya1, tya2)
              | _            ->
                 Panic.panic_no_pos "[%s] expects one or two arguments." id
            in
            let tya1 =
              Ty_arg_lambda([], Some(Coq_ident("unit")), tya1)
            in
            fprintf ff "optionalO %a %a" (pp_arg true) tya1
              (pp_arg true) tya2
        | "optional" | "optionalO" ->
           (match tyas with
           | [tya]        ->
               fprintf ff "%s %a null" id (pp_arg true) tya
           | [tya1; tya2] ->
               fprintf ff "%s %a %a" id (pp_arg true) tya1
                 (pp_arg true) tya2
           | _            ->
               Panic.panic_no_pos "[%s] expects one or two arguments." id)
        | "struct"                 ->
            let (tya, tyas) =
              match tyas with tya :: tyas -> (tya, tyas) | [] ->
              Panic.panic_no_pos "[%s] expects at least one argument." id
            in
            fprintf ff "struct %a [@@{type} %a ]"
              (pp_arg true) tya
              (pp_sep " ; " (pp_arg false)) tyas
        | _                        ->
            default ()
  and pp_arg wrap ff tya =
    match tya with
    | Ty_arg_expr(ty)         ->
        pp wrap false ff ty
    | Ty_arg_lambda(xs,a,tya) ->
        fprintf ff "(λ %a%a,@;  @[<v 0>%a%a@]@;)"
          (pp_encoded_patt_name false) xs
          pp_ty_annot a pp_encoded_patt_bindings xs
          (pp_arg false) tya
  in
  pp true false ff ty

let pp_type_expr = pp_type_expr_rec None Rec_none
let pp_constr = pp_constr_rec None Rec_none true

let pp_constrs : constr list pp = fun ff cs ->
  match cs with
  | []      -> pp_str ff "True"
  | c :: cs -> pp_constr ff c; List.iter (fprintf ff " ∗ %a" pp_constr) cs

let gather_struct_fields id s =
  let fn (x, (ty_opt, _, layout)) =
    match ty_opt with
    | Some(MA_field(ty)) -> (x, ty, layout)
    | Some(MA_utag(_))
    | Some(MA_none)      ->
        Panic.panic_no_pos "Bad annotation on field [%s] of struct [%s]." x id
    | None           ->
        Panic.panic_no_pos "No annotation on field [%s] of struct [%s]." x id
  in
  List.map fn s.struct_members

let rec pp_struct_def_np structs r annot fields ff id =
  let pp fmt = fprintf ff fmt in
  (* Print the part that may stand for dots in case of "typedef". *)
  let pp_dots ff () =
    (* Printing of the "exists". *)
    pp "@[<v 0>";
    if annot.st_exists <> [] then
      begin
        pp "∃ₜ";
        let pp_exist (x, e) =
          pp " (%s : %a)" x (pp_simple_coq_expr false) e
        in
        List.iter pp_exist annot.st_exists;
        pp ",@;"
      end;
    (* Printing the let-bindings. *)
    let pp_let (id, ty, def) =
      let pp_coq = pp_simple_coq_expr false in
      match ty with
      | None    -> pp "let %s := %a in@;" id pp_coq def;
      | Some ty -> pp "let %s : %a := %a in@;" id pp_coq ty pp_coq def;
    in
    List.iter pp_let annot.st_lets;
    (* Opening the "constrained". *)
    pp "@[<v 2>"; (* Open box for struct fields. *)
    if annot.st_constrs <> [] then pp "constrained (";
    let pp fmt = fprintf ff fmt in
    (* Printing the "padded". *)
    Option.iter (fun _ -> pp "padded (") annot.st_size;
    (* Printing the struct fields. *)
    pp "struct struct_%s [@@{type}" id;
    let pp_field ff (_, ty, layout) =
      match layout with
      | LStruct(s_id, false) ->
          let (s, structs) =
            try (List.assoc s_id structs, List.remove_assoc s_id structs)
            with Not_found -> Panic.panic_no_pos "Unknown struct [%s]." s_id
          in
          let annot =
            match s.struct_annot with
            | Some(annot) -> annot
            | None        ->
            Panic.panic_no_pos "Annotations on struct [%s] are invalid." s_id
          in
          begin
            match annot with
            | SA_union        ->
                Panic.panic_no_pos "Annotations on struct [%s] are invalid \
                  since it is not a union." s_id
            | SA_tagged_u(_)  ->
                Panic.panic_no_pos "Annotations on struct [%s] are invalid \
                  since it is not a tagged union." s_id
            | SA_basic(annot) ->
            if annot = default_basic_struct_annot || basic_struct_annot_defines_type annot then
              (* No annotation on struct, fall back to normal printing. *)
              pp_type_expr_rec None r ff ty
            else
            let annot =
              match annot.st_typedef with
              | None    -> {annot with st_typedef = Some((s_id,ty))}
              | Some(_) ->
              Panic.panic_no_pos "[rc::typedef] in nested struct [%s]." s_id
            in
            let fields = gather_struct_fields s_id s in
            pp "(%a)" (pp_struct_def_np structs Rec_none annot fields) s_id
          end
      | LStruct(_   , true ) -> assert false (* TODO *)
      | _                    -> pp_type_expr_rec None r ff ty
    in
    begin
      match fields with
      | []              -> ()
      | field :: fields ->
      reset_nroot_counter ();
      pp "@;%a" pp_field field;
      List.iter (pp " ;@;%a" pp_field) fields
    end;
    pp "@]@;]"; (* Close box for struct fields. *)
    let fn = pp ") struct_%s %a" id (pp_simple_coq_expr true) in
    Option.iter fn annot.st_size;
    (* Printing of constraints. *)
    if annot.st_constrs <> [] then
      begin
        pp ") (@;  @[<v 0>";
        let (c, cs) = (List.hd annot.st_constrs, List.tl annot.st_constrs) in
        pp "%a" pp_constr c;
        List.iter (pp " ∗@;%a" pp_constr) cs;
        pp "@]@;)"
      end;
    pp "@]"
  in
  reset_nroot_counter ();
  match annot.st_typedef with
  | None        -> pp_dots ff ()
  | Some(_, ty) -> pp_type_expr_rec (Some(pp_dots)) r ff ty

let collect_invs : func_def -> (string * state_descr) list = fun def ->
  let fn id (annot, _) acc =
    match annot with
    | BA_none     -> acc
    | BA_loop(sd) -> (id, sd) :: acc
  in
  SMap.fold fn def.func_blocks []

let pp_spec : Coq_path.t -> import list -> inlined_code ->
      typedef list -> string list -> Coq_ast.t pp =
    fun coq_path imports inlined typedefs ctxt ff ast ->

  (* Formatting utilities. *)
  let pp fmt = Format.fprintf ff fmt in

  (* Print inlined code (starts with an empty line) *)
  let pp_inlined extra_line_after descr ls =
    if ls <> [] then pp "\n";
    if ls <> [] then
      begin
        match descr with
        | None        -> pp "@;(* Inlined code. *)\n"
        | Some(descr) -> pp "@;(* Inlined code (%s). *)\n" descr
      end;
    List.iter (fun s -> if s = "" then pp "\n" else pp "@;%s" s) ls;
    if extra_line_after && ls <> [] then pp "\n";
  in

  (* Printing some header. *)
  pp "@[<v 0>From refinedc.typing Require Import typing.@;";
  pp "From %a Require Import generated_code.@;" Coq_path.pp coq_path;
  List.iter (pp_import ff) imports;
  pp "Set Default Proof Using \"Type\".\n";

  (* Printing generation data in a comment. *)
  pp "@;(* Generated from [%s]. *)" ast.source_file;

  (* Printing inlined code (from comments). *)
  pp_inlined true (Some "prelude") inlined.ic_prelude;

  (* Opening the section. *)
  pp "@;@[<v 2>Section spec.@;";
  pp "Context `{!typeG Σ} `{!globalG Σ}.";
  List.iter (pp "@;%s.") ctxt;

  (* Printing inlined code (from comments). *)
  pp_inlined false None inlined.ic_section;

  (* [Notation] data for printing sugar. *)
  let sugar = ref [] in

  (* [Typeclass Opaque] stuff that needs to be repeated after the section. *)
  let opaque = ref [] in

  (* Definition of types. *)
  let pp_type id refs params movable unfold_order pp_body =
    let refs = if refs = [] then [("x__", Coq_ident "unit")] else refs in
    let (ref_names, ref_types) = List.split refs in
    let (par_names, par_types) = List.split params in
    let ref_and_par_names = ref_names @ par_names in
    let ref_and_par_types = ref_types @ par_types in
    let pp_params ff =
      let fn (x,e) = fprintf ff "(%s : %a) " x (pp_simple_coq_expr false) e in
      List.iter fn
    in
    pp "\n@;(* Definition of type [%s]. *)@;" id;
    let pp_prod = pp_as_prod (pp_simple_coq_expr true) in
    pp "@[<v 2>Definition %s_rec : (%a → type) → (%a → type) := " id
      pp_prod ref_and_par_types pp_prod ref_and_par_types;
    pp "(λ self %a,@;" (pp_encoded_patt_name false) ref_and_par_names;
    pp_encoded_patt_bindings ff ref_and_par_names;
    let r = Rec_in_def(id) in
    pp_body r;
    pp "@]@;)%%I.@;Global Typeclasses Opaque %s_rec.\n" id;
    if par_names <> [] then sugar := !sugar @ [(id, par_names)];
    opaque := !opaque @ [id ^ "_rec"; id];

    pp "@;Global Instance %s_rec_le : TypeMono %s_rec." id id;
    pp "@;Proof. solve_type_proper. Qed.\n@;";

    pp "@[<v 2>Definition %s %a: rtype (%a) := {|@;" id pp_params params pp_prod ref_types;
    pp "rty r__ := %s_rec (type_fixpoint %s) %a@]@;|}.\n" id (id ^ "_rec")
      (pp_as_tuple pp_str) ("r__" :: par_names);

    (* Generation of the unfolding lemma. *)
    pp "@;@[<v 2>Lemma %s_unfold %a(%a : %a):@;" id pp_params params
      (pp_encoded_patt_name true) ref_names
      (pp_as_prod (pp_simple_coq_expr true)) ref_types;
    pp "@[<v 2>(%a @@ %a)%%I ≡@@{type} (@;"
      (pp_encoded_patt_name true) ref_names
      (pp_id_args false id) par_names;
    pp "%a" pp_encoded_patt_bindings ref_names;
    let r = Rec_in_lem(id) in
    pp_body r;
    pp "@]@;)%%I.@]@;";
    pp "Proof. apply: (type_fixpoint_unfold2 %s_rec). Qed.\n" id;

    (* Generation of the global instances. *)
    let pp_instance inst_name type_name =
      pp "@;Definition %s_%s_inst_generated %apatt__ :=@;"
        id inst_name pp_params params;
      pp "  [instance %s_eq _ _ (%s_unfold %apatt__) with %i%%N].@;"
        inst_name id pp_params params unfold_order;
      pp "Global Existing Instance %s_%s_inst_generated." id inst_name;
    in
    pp_instance "simplify_hyp_place" "SimplifyHyp";
    pp_instance "simplify_goal_place" "SimplifyGoal";
    if movable then
      begin
        pp "\n";
        pp_instance "simplify_hyp_val" "SimplifyHyp";
        pp_instance "simplify_goal_val" "SimplifyGoal"
      end
  in
  let pp_struct struct_id annot s =
    (* Check if a type must be generated. *)
    if not (basic_struct_annot_defines_type annot) then () else
    (* Gather the field annotations. *)
    let fields = gather_struct_fields struct_id s in
    let id =
      match annot.st_typedef with
      | None       -> struct_id
      | Some(id,_) -> id
    in
    let pp_body r =
      pp_struct_def_np ast.structs r annot fields ff struct_id;
    in
    pp_type id annot.st_refined_by annot.st_parameters (not annot.st_immovable)
      annot.st_unfold_order pp_body
  in
  let pp_tagged_union id tag_type_e s =
    if s.struct_is_union then
      Panic.panic_no_pos "Tagged union annotations used on [%s] should \
        rather be placed on a struct definition." id;
    (* Extract the two fields of the wrapping structure (tag and union). *)
    let (tag_field, union_field) =
      match s.struct_members with
      | [tag_field ; union_field] -> (tag_field, union_field)
      | _                         ->
      Panic.panic_no_pos "Tagged union [%s] is ill-formed: it should have \
        exactly two fields (tag and union)." id
    in
    (* Obtain the name of the tag field and check its type. *)
    let tag_field =
      let (tag_field, (annot, _, layout)) = tag_field in
      if annot <> Some(MA_none) then
        Panic.wrn None "Annotation ignored on the tag field [%s] of \
          the tagged union [%s]." tag_field id;
      if layout <> LInt(ItSize_t(false)) then
        Panic.panic_no_pos "The tag field [%s] of tagged union [%s] does \
          not have the expected [size_t] type." tag_field id;
      tag_field
    in
    (* Obtain the name of the union field and the name of the actual union. *)
    let (union_field, union_name) =
      let (union_field, (annot, _, layout)) = union_field in
      if annot <> Some(MA_none) then
        Panic.wrn None "Annotation ignored on the union field [%s] of \
          the tagged union [%s]." union_field id;
      match layout with
      | LStruct(union_name, true) -> (union_field, union_name)
      | _                         ->
      Panic.panic_no_pos "The union field [%s] of tagged union [%s] is \
        expected to be a union." union_field id
    in
    (* Find the union and extract its fields and corresponding annotations. *)
    let union_cases =
      let union =
        try List.assoc union_name ast.structs
        with Not_found -> assert false (* Unreachable thanks to Cerberus. *)
      in
      (* Some sanity checks. *)
      if not union.struct_is_union then
        Panic.panic_no_pos "[%s] was expected to be a union." union_name;
      assert (union.struct_annot = Some(SA_union));
      (* Extracting data from the fields. *)
      let fn (name, (annot, _, layout)) =
        match annot with
        | Some(MA_utag(ts)) ->
            let id_struct =
              match layout with
              | LStruct(id, false) -> id
              | _                  ->
              Panic.panic_no_pos "Field [%s] of union [%s] is not a struct."
                name union_name
            in
            (name, ts, id_struct)
        | Some(MA_none    ) ->
            Panic.panic_no_pos "Union tag annotation expected on field [%s] \
              of union [%s]." name union_name
        | Some(MA_field(_)) ->
            Panic.panic_no_pos "Unexpected field annotation on [%s] in the \
              union [%s]." name union_name
        | None              ->
            Panic.panic_no_pos "Invalid annotation on field [%s] in the \
              union [%s]." name union_name
      in
      List.map fn union.struct_members
    in
    (* Starting to do the printing. *)
    pp "\n@;(* Definition of type [%s] (tagged union). *)@;" id;
    (* Definition of the tag function. *)
    pp "@[<v 2>Definition %s_tag (c : %a) : nat :=@;"
      id (pp_simple_coq_expr false) tag_type_e;
    pp "match c with@;";
    let pp_tag_case i (_, (c, args), _) =
      pp "| %s" c; List.iter (fun _ -> pp " _") args; pp " => %i%%nat@;" i
    in
    List.iteri pp_tag_case union_cases;
    pp "end.@]\n@;";
    (* Simplifications hints for inversing the tag function. *)
    let pp_inversion_hint i (_, (c, args), _) =
      pp "Global Instance simpl_%s_tag_%s c :@;" id c;
      pp "  SimplBothRel (=) (%s_tag c) %i%%nat (" id i;
      if args <> [] then pp "∃";
      let fn (x,e) = pp " (%s : %a)" x (pp_simple_coq_expr false) e in
      List.iter fn args;
      if args <> [] then pp ", ";
      pp "c = %s" c; List.iter (fun (x,_) -> pp " %s" x) args; pp ").@;";
      pp "Proof. split; destruct c; naive_solver. Qed.\n@;";
    in
    List.iteri pp_inversion_hint union_cases;
    (* Definition for the tagged union info. *)
    pp "@[<v 2>Program Definition %s_tunion_info : tunion_info %a := {|@;"
      id (pp_simple_coq_expr true) tag_type_e;
    pp "ti_base_layout := struct_%s;@;" id;
    pp "ti_tag_field_name := \"%s\";@;" tag_field;
    pp "ti_union_field_name := \"%s\";@;" union_field;
    pp "ti_union_layout := union_%s;@;" union_name;
    pp "ti_tag := %s_tag;@;" id;
    pp "ti_type c :=@;";
    pp "  match c with@;";
    let fn (name, (c, args), struct_id) =
      pp "  | %s" c; List.iter (fun (x,_) -> pp " %s" x) args;
      pp " => struct struct_%s [@@{type} " name;
      begin
        let s =
          try List.assoc struct_id ast.structs
          with Not_found -> assert false (* Unreachable thanks to Cerberus. *)
        in
        let fields = gather_struct_fields struct_id s in
        let pp_field ff (_, ty, _) = fprintf ff "%a" pp_type_expr ty in
        match fields with
        | []      -> ()
        | f :: fs -> pp "%a" pp_field f; List.iter (pp "; %a" pp_field) fs
      end;
      pp "]%%I@;"
    in
    List.iter fn union_cases;
    pp "  end;@]@;";
    pp "|}.@;";
    pp "Next Obligation. done. Qed.@;";
    pp "Next Obligation. by case; eauto. Qed.\n@;";
    (* Actual definition of the type. *)
    pp "Program Definition %s : rtype _ := tunion %s_tunion_info." id id
  in
  let pp_struct_or_tagged_union (id, s) =
    match s.struct_annot with
    | Some(SA_basic(annot)) -> pp_struct id annot s
    | Some(SA_tagged_u(e))  -> pp_tagged_union id e s
    | Some(SA_union)        -> ()
    | None                  ->
        Panic.panic_no_pos "Annotations on struct [%s] are invalid." id
  in
  List.iter pp_struct_or_tagged_union ast.structs;

  (* Type definitions (from comments). *)
  let pp_typedef td =
    let pp_body r =
      pp_type_expr_rec None r ff td.td_body
    in
    pp_type td.td_id td.td_refinements td.td_parameters (not td.td_immovable)
      td.td_unfold_order pp_body
  in
  List.iter pp_typedef typedefs;

  (* Function specs. *)
  let pp_spec (id, def_or_decl) =
    let annot =
      match def_or_decl with
      | FDef({func_annot=Some(annot); _}) -> annot
      | FDec(Some(annot))                 -> annot
      | _                                 ->
      Panic.panic_no_pos "Annotations on function [%s] are invalid." id
    in
    match annot.fa_proof_kind with
    | Proof_inlined ->
        ()
    | Proof_skipped ->
        pp "\n@;(* Function [%s] has been skipped. *)" id
    | _             ->
    pp "\n@;(* Specifications for function [%s]. *)" id;
    let (param_names, param_types) = List.split annot.fa_parameters in
    let (exist_names, exist_types) = List.split annot.fa_exists in
    let pp_args ff tys =
      match tys with
      | [] -> ()
      | _  -> pp "; "; pp_sep ", " pp_type_expr ff tys
    in
    pp "@;Definition type_of_%s :=@;  @[<hov 2>" id;
    let pp_prod = pp_as_prod (pp_simple_coq_expr true) in
    pp "fn(∀ %a : %a%a; %a)@;→ ∃ %a : %a, %a; %a.@]"
      (pp_as_tuple pp_str) param_names pp_prod param_types
      pp_args annot.fa_args pp_constrs annot.fa_requires (pp_as_tuple pp_str)
      exist_names pp_prod exist_types pp_type_expr
      annot.fa_returns pp_constrs annot.fa_ensures
  in
  List.iter pp_spec ast.functions;

  (* Closing the section. *)
  pp "@]@;End spec.";

  (* [Notation] stuff (printing sugar). *)
  if !sugar <> [] then pp "@;";
  let pp_sugar (id, params) =
    pp "@;Notation \"%s< %a >\"" id (pp_sep " , " pp_print_string) params;
    pp " := (%s %a)@;  " id (pp_sep " " pp_print_string) params;
    pp "(only printing, format \"'%s<' %a '>'\") : printing_sugar." id
      (pp_sep " ,  " pp_print_string) params
  in
  List.iter pp_sugar !sugar;

  (* [Typeclass Opaque] stuff. *)
  if !opaque <> [] then pp "@;";
  let pp_opaque = pp "@;Global Typeclasses Opaque %s." in
  List.iter pp_opaque !opaque;

  (* Printing inlined code (from comments). *)
  pp_inlined false (Some "final") inlined.ic_final;
  pp "@]"

let pp_spec_vst : Coq_path.t -> import list -> inlined_code ->
      typedef list -> string list -> Coq_ast.t pp =
    fun coq_path imports inlined typedefs ctxt ff ast ->

  (* Formatting utilities. *)
  let pp fmt = Format.fprintf ff fmt in

  (* Print inlined code (starts with an empty line) *)
  let pp_inlined extra_line_after descr ls =
    if ls <> [] then pp "\n";
    if ls <> [] then
      begin
        match descr with
        | None        -> pp "@;(* Inlined code. *)\n"
        | Some(descr) -> pp "@;(* Inlined code (%s). *)\n" descr
      end;
    List.iter (fun s -> if s = "" then pp "\n" else pp "@;%s" s) ls;
    if extra_line_after && ls <> [] then pp "\n";
  in

  (* Printing some header. *)
  pp "@[<v 0>From VST.typing Require Import typing.@;";
  pp "From %a Require Import generated_code_vst.@;" Coq_path.pp coq_path;
  List.iter (pp_import ff) imports;
  pp "Set Default Proof Using \"Type\".\n";
  pp "Notation int := VST.typing.int.int.\n";

  (* Printing generation data in a comment. *)
  pp "@;(* Generated from [%s]. *)" ast.source_file;

  (* Printing inlined code (from comments). *)
  pp_inlined true (Some "prelude") inlined.ic_prelude;

  (* Opening the section. *)
  pp "@;@[<v 2>Section spec.@;";
  pp "Context `{!typeG OK_ty Σ} {cs : compspecs} `{!externalGS OK_ty Σ}.";
  List.iter (pp "@;%s.") ctxt;

  (* Printing inlined code (from comments). *)
  pp_inlined false None inlined.ic_section;

  (* [Notation] data for printing sugar. *)
  let sugar = ref [] in

  (* [Typeclass Opaque] stuff that needs to be repeated after the section. *)
  let opaque = ref [] in

  (* Definition of types. *)
  let pp_type id refs params movable unfold_order pp_body =
    let refs = if refs = [] then [("x__", Coq_ident "unit")] else refs in
    let (ref_names, ref_types) = List.split refs in
    let (par_names, par_types) = List.split params in
    let ref_and_par_names = ref_names @ par_names in
    let ref_and_par_types = ref_types @ par_types in
    let pp_params ff =
      let fn (x,e) = fprintf ff "(%s : %a) " x (pp_simple_coq_expr false) e in
      List.iter fn
    in
    pp "\n@;(* Definition of type [%s]. *)@;" id;
    let pp_prod = pp_as_prod (pp_simple_coq_expr true) in
    pp "@[<v 2>Definition %s_rec : (%a → type) → (%a → type) := " id
      pp_prod ref_and_par_types pp_prod ref_and_par_types;
    pp "(λ self %a,@;" (pp_encoded_patt_name false) ref_and_par_names;
    pp_encoded_patt_bindings ff ref_and_par_names;
    let r = Rec_in_def(id) in
    pp_body r;
    pp "@]@;)%%I.@;Global Typeclasses Opaque %s_rec.\n" id;
    if par_names <> [] then sugar := !sugar @ [(id, par_names)];
    opaque := !opaque @ [id ^ "_rec"; id];

    pp "@;Global Instance %s_rec_le : TypeMono %s_rec." id id;
    pp "@;Proof. solve_type_proper. Qed.\n@;";

    pp "@[<v 2>Definition %s %a: rtype (%a) := {|@;" id pp_params params pp_prod ref_types;
    pp "rty r__ := %s_rec (type_fixpoint %s) %a@]@;|}.\n" id (id ^ "_rec")
      (pp_as_tuple pp_str) ("r__" :: par_names);

    (* Generation of the unfolding lemma. *)
    pp "@;@[<v 2>Lemma %s_unfold %a(%a : %a):@;" id pp_params params
      (pp_encoded_patt_name true) ref_names
      (pp_as_prod (pp_simple_coq_expr true)) ref_types;
    pp "@[<v 2>(%a @@ %a)%%I ≡@@{type} (@;"
      (pp_encoded_patt_name true) ref_names
      (pp_id_args false id) par_names;
    pp "%a" pp_encoded_patt_bindings ref_names;
    let r = Rec_in_lem(id) in
    pp_body r;
    pp "@]@;)%%I.@]@;";
    pp "Proof. apply: (type_fixpoint_unfold2 %s_rec). Qed.\n" id;

    (* Generation of the global instances. *)
    let pp_instance inst_name type_name =
      pp "@;Definition %s_%s_inst_generated %apatt__ :=@;"
        id inst_name pp_params params;
      pp "  [instance %s_eq _ _ (%s_unfold %apatt__) with %i%%N].@;"
        inst_name id pp_params params unfold_order;
      pp "Global Existing Instance %s_%s_inst_generated." id inst_name;
    in
    pp_instance "simplify_hyp_place" "SimplifyHyp";
    pp_instance "simplify_goal_place" "SimplifyGoal";
    if movable then
      begin
        pp "\n";
        pp_instance "simplify_hyp_val" "SimplifyHyp";
        pp_instance "simplify_goal_val" "SimplifyGoal"
      end
  in
  let pp_struct struct_id annot s =
    (* Check if a type must be generated. *)
    if not (basic_struct_annot_defines_type annot) then () else
    (* Gather the field annotations. *)
    let fields = gather_struct_fields struct_id s in
    let id =
      match annot.st_typedef with
      | None       -> struct_id
      | Some(id,_) -> id
    in
    let pp_body r =
      pp_struct_def_np ast.structs r annot fields ff struct_id;
    in
    pp_type id annot.st_refined_by annot.st_parameters (not annot.st_immovable)
      annot.st_unfold_order pp_body
  in
  let pp_tagged_union id tag_type_e s =
    if s.struct_is_union then
      Panic.panic_no_pos "Tagged union annotations used on [%s] should \
        rather be placed on a struct definition." id;
    (* Extract the two fields of the wrapping structure (tag and union). *)
    let (tag_field, union_field) =
      match s.struct_members with
      | [tag_field ; union_field] -> (tag_field, union_field)
      | _                         ->
      Panic.panic_no_pos "Tagged union [%s] is ill-formed: it should have \
        exactly two fields (tag and union)." id
    in
    (* Obtain the name of the tag field and check its type. *)
    let tag_field =
      let (tag_field, (annot, _, layout)) = tag_field in
      if annot <> Some(MA_none) then
        Panic.wrn None "Annotation ignored on the tag field [%s] of \
          the tagged union [%s]." tag_field id;
      if layout <> LInt(ItSize_t(false)) then
        Panic.panic_no_pos "The tag field [%s] of tagged union [%s] does \
          not have the expected [size_t] type." tag_field id;
      tag_field
    in
    (* Obtain the name of the union field and the name of the actual union. *)
    let (union_field, union_name) =
      let (union_field, (annot, _, layout)) = union_field in
      if annot <> Some(MA_none) then
        Panic.wrn None "Annotation ignored on the union field [%s] of \
          the tagged union [%s]." union_field id;
      match layout with
      | LStruct(union_name, true) -> (union_field, union_name)
      | _                         ->
      Panic.panic_no_pos "The union field [%s] of tagged union [%s] is \
        expected to be a union." union_field id
    in
    (* Find the union and extract its fields and corresponding annotations. *)
    let union_cases =
      let union =
        try List.assoc union_name ast.structs
        with Not_found -> assert false (* Unreachable thanks to Cerberus. *)
      in
      (* Some sanity checks. *)
      if not union.struct_is_union then
        Panic.panic_no_pos "[%s] was expected to be a union." union_name;
      assert (union.struct_annot = Some(SA_union));
      (* Extracting data from the fields. *)
      let fn (name, (annot, _, layout)) =
        match annot with
        | Some(MA_utag(ts)) ->
            let id_struct =
              match layout with
              | LStruct(id, false) -> id
              | _                  ->
              Panic.panic_no_pos "Field [%s] of union [%s] is not a struct."
                name union_name
            in
            (name, ts, id_struct)
        | Some(MA_none    ) ->
            Panic.panic_no_pos "Union tag annotation expected on field [%s] \
              of union [%s]." name union_name
        | Some(MA_field(_)) ->
            Panic.panic_no_pos "Unexpected field annotation on [%s] in the \
              union [%s]." name union_name
        | None              ->
            Panic.panic_no_pos "Invalid annotation on field [%s] in the \
              union [%s]." name union_name
      in
      List.map fn union.struct_members
    in
    (* Starting to do the printing. *)
    pp "\n@;(* Definition of type [%s] (tagged union). *)@;" id;
    (* Definition of the tag function. *)
    pp "@[<v 2>Definition %s_tag (c : %a) : nat :=@;"
      id (pp_simple_coq_expr false) tag_type_e;
    pp "match c with@;";
    let pp_tag_case i (_, (c, args), _) =
      pp "| %s" c; List.iter (fun _ -> pp " _") args; pp " => %i%%nat@;" i
    in
    List.iteri pp_tag_case union_cases;
    pp "end.@]\n@;";
    (* Simplifications hints for inversing the tag function. *)
    let pp_inversion_hint i (_, (c, args), _) =
      pp "Global Instance simpl_%s_tag_%s c :@;" id c;
      pp "  SimplBothRel (=) (%s_tag c) %i%%nat (" id i;
      if args <> [] then pp "∃";
      let fn (x,e) = pp " (%s : %a)" x (pp_simple_coq_expr false) e in
      List.iter fn args;
      if args <> [] then pp ", ";
      pp "c = %s" c; List.iter (fun (x,_) -> pp " %s" x) args; pp ").@;";
      pp "Proof. split; destruct c; naive_solver. Qed.\n@;";
    in
    List.iteri pp_inversion_hint union_cases;
    (* Definition for the tagged union info. *)
    pp "@[<v 2>Program Definition %s_tunion_info : tunion_info %a := {|@;"
      id (pp_simple_coq_expr true) tag_type_e;
    pp "ti_base_layout := struct_%s;@;" id;
    pp "ti_tag_field_name := \"%s\";@;" tag_field;
    pp "ti_union_field_name := \"%s\";@;" union_field;
    pp "ti_union_layout := union_%s;@;" union_name;
    pp "ti_tag := %s_tag;@;" id;
    pp "ti_type c :=@;";
    pp "  match c with@;";
    let fn (name, (c, args), struct_id) =
      pp "  | %s" c; List.iter (fun (x,_) -> pp " %s" x) args;
      pp " => struct struct_%s [@@{type} " name;
      begin
        let s =
          try List.assoc struct_id ast.structs
          with Not_found -> assert false (* Unreachable thanks to Cerberus. *)
        in
        let fields = gather_struct_fields struct_id s in
        let pp_field ff (_, ty, _) = fprintf ff "%a" pp_type_expr ty in
        match fields with
        | []      -> ()
        | f :: fs -> pp "%a" pp_field f; List.iter (pp "; %a" pp_field) fs
      end;
      pp "]%%I@;"
    in
    List.iter fn union_cases;
    pp "  end;@]@;";
    pp "|}.@;";
    pp "Next Obligation. done. Qed.@;";
    pp "Next Obligation. by case; eauto. Qed.\n@;";
    (* Actual definition of the type. *)
    pp "Program Definition %s : rtype _ := tunion %s_tunion_info." id id
  in
  let pp_struct_or_tagged_union (id, s) =
    match s.struct_annot with
    | Some(SA_basic(annot)) -> pp_struct id annot s
    | Some(SA_tagged_u(e))  -> pp_tagged_union id e s
    | Some(SA_union)        -> ()
    | None                  ->
        Panic.panic_no_pos "Annotations on struct [%s] are invalid." id
  in
  List.iter pp_struct_or_tagged_union ast.structs;

  (* Type definitions (from comments). *)
  let pp_typedef td =
    let pp_body r =
      pp_type_expr_rec None r ff td.td_body
    in
    pp_type td.td_id td.td_refinements td.td_parameters (not td.td_immovable)
      td.td_unfold_order pp_body
  in
  List.iter pp_typedef typedefs;

  (* Function specs. *)
  let pp_spec (id, def_or_decl) =
    let annot =
      match def_or_decl with
      | FDef({func_annot=Some(annot); _}) -> annot
      | FDec(Some(annot))                 -> annot
      | _                                 ->
      Panic.panic_no_pos "Annotations on function [%s] are invalid." id
    in
    match annot.fa_proof_kind with
    | Proof_inlined ->
        ()
    | Proof_skipped ->
        pp "\n@;(* Function [%s] has been skipped. *)" id
    | _             ->
    pp "\n@;(* Specifications for function [%s]. *)" id;
    let (param_names, param_types) = List.split annot.fa_parameters in
    let (exist_names, exist_types) = List.split annot.fa_exists in
    let pp_args ff tys =
      match tys with
      | [] -> ()
      | _  -> pp "; "; pp_sep ", " pp_type_expr ff tys
    in
    pp "@;Definition type_of_%s :=@;  @[<hov 2>" id;
    let pp_prod = pp_as_prod (pp_simple_coq_expr true) in
    pp "fn(∀ %a : %a%a; <affine> %a)@;→ ∃ %a : %a, %a; %a.@]"
      (pp_as_tuple pp_str) param_names pp_prod param_types
      pp_args annot.fa_args pp_constrs annot.fa_requires (pp_as_tuple pp_str)
      exist_names pp_prod exist_types pp_type_expr
      annot.fa_returns pp_constrs annot.fa_ensures
  in
  List.iter pp_spec ast.functions;

  (* Closing the section. *)
  pp "@]@;End spec.";

  (* [Notation] stuff (printing sugar). *)
  if !sugar <> [] then pp "@;";
  let pp_sugar (id, params) =
    pp "@;Notation \"%s< %a >\"" id (pp_sep " , " pp_print_string) params;
    pp " := (%s %a)@;  " id (pp_sep " " pp_print_string) params;
    pp "(only printing, format \"'%s<' %a '>'\") : printing_sugar." id
      (pp_sep " ,  " pp_print_string) params
  in
  List.iter pp_sugar !sugar;

  (* [Typeclass Opaque] stuff. *)
  if !opaque <> [] then pp "@;";
  let pp_opaque = pp "@;Global Typeclasses Opaque %s." in
  List.iter pp_opaque !opaque;

  (* Printing inlined code (from comments). *)
  pp_inlined false (Some "final") inlined.ic_final;
  pp "@]"

let pp_proof : Coq_path.t -> func_def -> import list -> string list
    -> proof_kind -> Coq_ast.t pp =
    fun coq_path def imports ctxt proof_kind ff ast ->
  (* Formatting utilities. *)
  let pp fmt = Format.fprintf ff fmt in

  (* Only print a comment if the function is trusted. *)
  match proof_kind with
  | Proof_trusted ->
      pp "(* Let's skip that, you seem to have some faith. *)"
  | Proof_skipped ->
      pp "(* You were too lazy to even write a spec for this function. *)"
  | _             ->

  (* Add the extra import in case of manual proof. *)
  let imports =
    match proof_kind with
    | Proof_manual(from,file,_) -> imports @ [(from,file)]
    | _                         -> imports
  in

  (* Printing some header. *)
  pp "@[<v 0>From VST.typing Require Import typing.@;";
  (* FIXME should use the refinedC to Clight AST convertor *)
  pp "From %a Require Import generated_code_vst_clight.@;" Coq_path.pp coq_path;
  pp "From %a Require Import generated_spec_vst.@;" Coq_path.pp coq_path;
  List.iter (pp_import ff) imports;
  pp "Set Default Proof Using \"Type\".@;@;";

  (* Printing generation data in a comment. *)
  pp "(* Generated from [%s]. *)@;" ast.source_file;

  (* Opening the section. *)
  pp "@[<v 2>Section proof_%s.@;" def.func_name;
  pp " Context `{!typeG OK_ty Σ} {cs : compspecs}.";
  List.iter (pp "@;%s.") ctxt;

  (* Statement of the typing proof. *)
  let func_annot =
    match def.func_annot with
    | Some(annot) -> annot
    | None        -> assert false (* Unreachable. *)
  in
  if List.length def.func_args <> List.length func_annot.fa_args then
    Panic.panic_no_pos "Argument number missmatch between code and spec.";
  pp "\n@;(* Typing proof for [%s]. *)@;" def.func_name;
  (* Get all globals, including those needed for inlined functions. *)
  let (used_globals, used_functions) =
    let merge (g1, f1) (g2, f2) =
      let dedup = List.dedup String.compare in
      (dedup (g1 @ g2), dedup (f1 @ f2))
    in
    let fn acc f =
      match List.assoc_opt f ast.functions with
      | Some(FDef(def)) when is_inlined def -> merge acc def.func_deps
      | _                                   -> acc
    in
    List.fold_left fn def.func_deps (snd def.func_deps)
  in
  let deps = used_globals @ used_functions in
  let pp_args ff xs =
    let xs = List.map (fun s -> "global_" ^ s) xs in
    match xs with
    | [] -> ()
    | _  -> fprintf ff " (%a : loc)" (pp_sep " " pp_str) xs
  in
  pp "@[<v 2>Lemma type_%s%a Espec ge :@;" def.func_name pp_args deps;
  begin
    let prefix = if used_functions = [] then "⊢ " else "" in
    let pp_impl ff def =
      let (used_globals, used_functions) = def.func_deps in
      let wrap = used_globals <> [] || used_functions <> [] in
      if wrap then fprintf ff "(";
      (* FIXME this is the clight name; change it back to impl_%s when AST convertor is fixed *)
      fprintf ff "f_%s" def.func_name;
      List.iter (fprintf ff " global_%s") used_globals;
      List.iter (fprintf ff " global_%s") used_functions;
      if wrap then fprintf ff ")"
    in
    let pp_global f = pp "global_locs !! \"%s\" = Some global_%s →@;" f f in
    List.iter pp_global used_globals;
    let pp_prod = pp_as_prod (pp_simple_coq_expr true) in
    let pp_global_type f =
      match List.assoc_opt f ast.global_vars with
      | Some(Some(global_type)) ->
          let (param_names, param_types) =
            List.split global_type.ga_parameters
          in
          pp "global_initialized_types !! \"%s\" = " f;
          pp "Some (GT (%a) (λ '%a, %a : type)%%I) →@;" pp_prod param_types
            (pp_as_tuple pp_str) param_names
            (pp_type_expr_rec None Rec_none) global_type.ga_type
      | _                       -> ()
    in
    List.iter pp_global_type used_globals;
    let pp_dep f =
      let inlined_def =
        match List.assoc_opt f ast.functions with
        | Some(FDef(def)) when is_inlined def -> Some(def)
        | _                                   -> None
      in
      pp "global_%s ◁ᵥ global_%s @@ " f f;
      begin
        match inlined_def with
        | Some(def) -> pp "inline_function_ptr %a" pp_impl def
        | None      -> pp "function_ptr type_of_%s" f
      end;
      pp " -∗@;"
    in
    List.iter pp_dep used_functions;
    pp "%styped_function(A := ConstType _) Espec ge %a type_of_%s.@]@;" prefix pp_impl def def.func_name
  end;

  (* We have a manual proof. *)
  match proof_kind with
  | Proof_manual(_,_,thm) ->
      pp "Proof. refine %s. Qed." thm;
      pp "@]@;End proof_%s.@]" def.func_name (* Section closing. *)
  | _                     ->

  (* We output a normal proof. *)
  let _pp_intros ff xs =
    let pp_intro ff (x,_) = pp_str ff x in
    match xs with
    | []      -> fprintf ff "[]"
    | [x]     -> pp_intro ff x
    | x :: xs -> List.iter (fun _ -> pp_str ff "[") xs;
                 pp_intro ff x;
                 List.iter (fprintf ff " %a]" pp_intro) xs
  in
  pp "@[<v 2>Proof.@;";
  pp "Local Open Scope printing_sugar.@;";
  (* FIXME the intro pattern in type function is currently just x, the entire argument array *)
  pp "type_function \"%s\" ( x )" def.func_name
    (*pp_intros func_annot.fa_parameters *);
  (* FIXME same as above *)
  (* if def.func_vars <> [] || def.func_args <> [] then
    begin
      pp " =>";
      List.iter (fun (x,_) -> pp " arg_%s" x) def.func_args;
      List.iter (fun (x,_) -> pp " local_%s" x) def.func_vars
    end; *)
  pp ".@;";
  if func_annot.fa_parameters <> [] then
    begin
      let pp_var ff (x, _) = pp_print_string ff x in
      pp "prepare_parameters (%a).@;" (pp_sep " " pp_var) func_annot.fa_parameters;
    end;

  let pp_state_descr print_unused print_exist sd =
    (* Printing the existentials. *)
    begin
      if print_exist then
        let pp_exists (id, e) =
          pp "@;∃ %s : %a," id (pp_simple_coq_expr false) e
        in
        List.iter pp_exists sd.sd_exists;
      else ()
    end;
    (* Compute the used and unused arguments and variables. *)
    let used =
      let fn (id, ty) =
        (* Check if [id_var] is a function argument. *)
        try
          let layout = List.assoc id def.func_args in
          (* Check for name clash with local variables. *)
          if List.mem_assoc id def.func_vars then
            Panic.panic_no_pos "[%s] denotes both an argument and a local \
              variable of function [%s]." id def.func_name;
          (* Check if the type is different for the toplevel one. *)
          let toplevel_ty =
            try
              let i = List.find_index (fun (s,_) -> s = id) def.func_args in
              List.nth func_annot.fa_args i
            with Not_found | Failure(_) -> assert false (* Unreachable. *)
          in
          if ty = toplevel_ty then
            Panic.wrn None "Useless annotation for argument [%s]." id;
          ("arg_" ^ id, (layout, Some(ty)))
        with Not_found ->
        (* Not a function argument, check that it is a local variable. *)
        try
          let layout = List.assoc id def.func_vars in
          ("local_" ^ id, (layout, Some(ty)))
        with Not_found ->
          Panic.panic_no_pos "[%s] is neither a local variable nor an \
            argument." id
      in
      List.map fn sd.sd_inv_vars
    in
    let unused =
      let unused_args =
        let pred (id, _) =
          let id = "arg_" ^ id in
          List.for_all (fun (id_var, _) -> id <> id_var) used
        in
        let args = List.filter pred def.func_args in
        let fn (id, layout) =
          let ty =
            try
              let i = List.find_index (fun (s,_) -> s = id) def.func_args in
              List.nth func_annot.fa_args i
            with Not_found | Failure(_) -> assert false (* Unreachable. *)
          in
          ("arg_" ^ id, (layout, Some(ty)))
        in
        List.map fn args
      in
      let unused_vars =
        let pred (id, _) =
          let id = "local_" ^ id in
          List.for_all (fun (id_var, _) -> id <> id_var) used
        in
        let vars = List.filter pred def.func_vars in
        List.map (fun (id, layout) -> ("local_" ^ id, (layout, None))) vars
      in
      unused_args @ unused_vars
    in
    let all_vars = if print_unused then unused @ used else used in
    let first = ref true in
    let pp_sep ff _ = if !first then first := false else fprintf ff " ∗" in
    let pp_var ff (id, (layout, ty_opt)) =
      match ty_opt with
      | None     ->
         fprintf ff "%a@;%s ◁ₗ uninit %a" pp_sep () id (pp_layout true) layout
      | Some(ty) -> fprintf ff "%a@;%s ◁ₗ %a" pp_sep () id pp_type_expr ty
    in
    begin
      match (all_vars, sd.sd_constrs) with
      | ([], []) -> pp "True"
      | (vs , cs) ->
          List.iter (pp "%a" pp_var) vs;
          List.iter (pp "%a@;%a" pp_sep () pp_constr) cs
    end;
  in
  let _pp_inv (id, annot) =
    (* Opening a box and printing the existentials. *)
    pp "@;  @[<v 2><[ \"%s\" :=" id;
    pp_state_descr true true annot;
    (* Closing the box. *)
    pp "@]@;]> $"
  in
  let _pp_hint hint =
    (* Opening a box. *)
    pp "@;  @[<v 2>IPROP_HINT ";
    begin match hint.ht_kind with
    | HK_block bid ->
       pp "(BLOCK_PRECOND \"%s\") (λ _ : unit," bid;
       pp_state_descr false true hint.ht_annot
    | HK_assert id ->
       let (exist_idents, exist_types) = List.split hint.ht_annot.sd_exists in
       pp "(ASSERT_COND \"%i\") (λ %a : %a,@;%a" id
         (pp_encoded_patt_name false) exist_idents
         (pp_as_prod (pp_simple_coq_expr true)) exist_types
         pp_encoded_patt_bindings exist_idents;
       pp_state_descr false false hint.ht_annot;
    end;
    (* Closing the box. *)
    pp "@;)%%I ::@]"
  in
  
  let invs = collect_invs def in
  (* No basic blocks to split in VST it seems *)
  (* pp "split_blocks ((";
  List.iter pp_inv invs;
  pp "@;  ∅@;)%%I : gmap label (iProp Σ)) (";
  List.iter pp_hint def.func_hints;
  pp "@;  @nil Prop@;)."; *)
  let pp_do_step id =
    pp "@;- repeat liRStep; liShow. type_function_end.";
    pp "@;  all: print_typesystem_goal \"%s\" \"%s\"." def.func_name id
  in
  List.iter pp_do_step (List.cons "#0" (List.map fst invs));
  pp "@;Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; ";
  pp "normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.";
  let tactics_items =
    let is_all t =
      let is_selector s =
        s = "all" ||
        let ok c = ('0' <= c && c <= '9') || List.mem c [' '; ','; '-'] in
        String.for_all ok s
      in
      match String.split_on_char ':' t with
      | []     -> false
      | s :: _ -> is_selector (String.trim s)
    in
    let rec pp_tactics_all tactics =
      match tactics with
      | t :: ts when is_all t -> pp "@;%s" t; pp_tactics_all ts
      | ts                    -> ts
    in
    pp_tactics_all func_annot.fa_tactics
  in
  List.iter (pp "@;+ %s") tactics_items;
  pp "@;all: print_sidecondition_goal \"%s\"." def.func_name;
  pp "@;Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal \"%s\"." def.func_name;
  pp "@]@;Qed.";

  (* Closing the section. *)
  pp "@]@;End proof_%s.@]" def.func_name

type mode =
  | Code of string * import list
  | CodeVST of string * import list
  | Spec of Coq_path.t * import list * inlined_code * typedef list * string list
  | SpecVST of Coq_path.t * import list * inlined_code * typedef list * string list
  | Fprf of Coq_path.t * func_def * import list * string list * proof_kind

let write : mode -> string -> Coq_ast.t -> unit = fun mode fname ast ->
  let pp =
    match mode with
    | Code(root_dir,imports)                 ->
        pp_code root_dir imports
    | CodeVST(root_dir,imports)              ->
        pp_code_vst root_dir imports
    | Spec(coq_path,imports,inlined,tydefs,ctxt) ->
        pp_spec coq_path imports inlined tydefs ctxt
    | SpecVST(coq_path,imports,inlined,tydefs,ctxt) ->
        pp_spec_vst coq_path imports inlined tydefs ctxt
    | Fprf(coq_path,def,imports,ctxt,kind)       ->
        pp_proof coq_path def imports ctxt kind
  in
  (* We write to a buffer. *)
  let buffer = Buffer.create 4096 in
  Format.fprintf (Format.formatter_of_buffer buffer) "%a@." pp ast;
  (* Check if we should write the file (inexistent / contents different). *)
  let must_write =
    try Buffer.contents (Buffer.from_file fname) <> Buffer.contents buffer
    with Sys_error(_) -> true
  in
  if must_write then Buffer.to_file fname buffer
