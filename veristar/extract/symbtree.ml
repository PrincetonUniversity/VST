open Misc

type component = string

(* canonical expression *)
type can_exp =
  | Ce_num of int
  | Ce_ident of ident
  | Ce_xor of can_exp * can_exp

(* canonical atom: e1==e2 or e1!=e2 *)
type can_atom =
  | EQ of can_exp * can_exp
  | NEQ of can_exp * can_exp

type link_kind = SINGLE | DOUBLE | XOR

type can_spred =
  | Csp_listseg of link_kind * component * can_exp * can_exp * component * can_exp * can_exp
  | Csp_pointsto of can_exp * (component * can_exp) list
  | Csp_tree of component * component * can_exp
  | Csp_indpred of string * can_exp list * component list

type can_form = can_atom list * can_spred list

type can_prop =
  | Cp_base of can_form
  | Cp_ifthenelse of can_atom * can_prop * can_prop
  | Cp_star of can_prop * can_prop

open Parsetree

type can_stmt =
  { can_st_desc: can_st_desc;
    can_st_loc: Location.t }

and can_cmd = can_stmt list

and can_st_desc =
  | Cst_ifthenelse of can_atom * can_cmd * can_cmd
  | Cst_assign of ident * can_exp
  | Cst_fldlookup of ident * can_exp * string
  | Cst_fldassign of can_exp * string * can_exp
  | Cst_new of ident
  | Cst_dispose of can_exp
  | Cst_fcall of IdSet.t * can_prop * can_prop * string
  | Cst_wand of can_prop

type can_entailment = can_prop * can_cmd * can_prop * string * Location.t

exception Inconsistent

(* misc ops on data structs *)
let mk_EQ (e1,e2) = EQ (min e1 e2, max e1 e2)
let mk_NEQ (e1,e2) = NEQ (min e1 e2, max e1 e2)

let neg_can_atom = function
  | EQ (e1,e2) -> mk_NEQ (e1,e2)
  | NEQ (e1,e2) -> mk_EQ (e1,e2)

let eval_can_atom ca =
  let eval_eq = function
    | (Ce_num n1, Ce_num n2) -> n1=n2
    | e1,e2 -> if e1=e2 then true else raise Not_found
  in match ca with
    | EQ (e1,e2) -> eval_eq (e1,e2)
    | NEQ (e1,e2) -> not (eval_eq (e1,e2))

let can_spred_eq = function
  | (csp1,csp2) when csp1=csp2 -> true
  | (Csp_listseg(k1,t1,e1,f1,_,_,_), Csp_listseg(k2,t2,e2,f2,_,_,_))
      when (k1,t1,e1,f1)=(k2,t2,e2,f2) && k1=SINGLE -> true
  | _ -> false

let is_EQ = function
  | EQ _ -> true
  | NEQ _ -> false

let un_EQ = function
  | EQ (e1,e2) -> (e1,e2)
  | NEQ _ -> raise (Invalid_argument "un_EQ")

let un_NEQ = function
  | NEQ (e1,e2) -> (e1,e2)
  | EQ _ -> raise (Invalid_argument "un_NEQ")

let is_uneq pl = function
  | (Ce_num n1, Ce_num n2) when n1<> n2 -> true
  | (e1,e2) -> List.mem (mk_NEQ (e1,e2)) pl

let can_prop_empty = Cp_base ([],[])

let normalize_can_exp =
  let simplify_xor e =
    let rec list_of_ce = function
      | Ce_num 0  -> []
      | Ce_num _ as e -> [e]
      | Ce_ident _ as e -> [e]
      | Ce_xor(e1,e2) -> (list_of_ce e1)@(list_of_ce e2) in
    let rec ce_of_list = function
      | [] -> Ce_num 0
      | [e] -> e
      | e::l -> Ce_xor(e, ce_of_list l) in
    let rec simplify = function  (* simplifies the sorted xor list of expressions *)
      | e1::(e2::l) when e1=e2 -> simplify l
      | (Ce_num n1)::(Ce_num n2::l) -> simplify (Ce_num ((lxor) n1 n2)::l)
      | e::l -> e::(simplify l)
      | [] -> []
    in  ce_of_list (simplify (List.stable_sort compare (list_of_ce e)))
  in function
    | Ce_xor (e1,e2) as e -> simplify_xor e
    | e -> e

let normalize_can_atom p =
  if is_EQ p
    then let (ce1,ce2) = un_EQ p in mk_EQ(normalize_can_exp ce1, normalize_can_exp ce2)
    else let (ce1,ce2) = un_NEQ p in mk_NEQ(normalize_can_exp ce1, normalize_can_exp ce2)

let normalize_can_spred = function
  | Csp_listseg (k,t1,e1,f1,t2,e2,f2) ->
      Csp_listseg(k,t1, normalize_can_exp e1, normalize_can_exp f1, t2, normalize_can_exp e2, normalize_can_exp f2)
  | Csp_pointsto (e,el) ->
      let el1 = List.map (fun (c,e) -> (c,normalize_can_exp e)) el
      in Csp_pointsto (normalize_can_exp e, el1)
  | Csp_tree (c1,c2,e) -> Csp_tree (c1,c2,normalize_can_exp e)
  | Csp_indpred _ -> assert false

let normalize_can_form (pl,sl) =
  (List.map normalize_can_atom pl, List.map normalize_can_spred sl)


(* substitutions *)
type subst = (can_exp -> can_exp) * (component -> component)

let mk_subst f_i f_c =
  let rec f_e = function
    | Ce_num n -> Ce_num n
    | Ce_ident i -> f_i i
    | Ce_xor (ce1,ce2) -> Ce_xor (f_e ce1, f_e ce2)
  in (f_e,f_c)

let mk_subst_pairs l =
  let f_i i =
    try snd (List.find (fun (x,e) -> x=i) l)
    with Not_found -> Ce_ident i
  and f_c x = x
  in mk_subst f_i f_c

let mk_single_subst (i,e) =
  let f_i x = if x=i then e else Ce_ident x
  and f_c x = x
  in mk_subst f_i f_c

let mk_gensym_garb_subst i =
  mk_single_subst (i, Ce_ident (gensym_garb i))

let gensym_subst_list is_garb l =
  let l' = List.map (fun i -> (i,(if is_garb then gensym_garb else gensym) i)) l in
  let f_i i = try Ce_ident (snd (List.find (fun (x,x') -> x=i) l'))
    with Not_found -> Ce_ident i
  and f_c x = x
  in mk_subst f_i f_c

let mk_gensym_subst_list =
  gensym_subst_list false

let mk_gensym_garb_subst_list =
  gensym_subst_list true

let sub_can_exp (f_e,_) = f_e

let (++) = IdSet.union
let (+) s x = IdSet.add x s
let (-) s x = IdSet.remove x s

let sub_idset (f_e,_) ss =
  let f i = match f_e (Ce_ident i) with
    | Ce_ident x -> x
    | _ -> assert false
  in IdSet.fold (fun i s -> s + (f i)) ss IdSet.empty

let sub_can_atom (f_e,_) = function
  | EQ (e1,e2) -> mk_EQ (f_e e1, f_e e2)
  | NEQ (e1,e2) -> mk_NEQ (f_e e1, f_e e2)

let sub_can_spred (f_e,f_c) = function
  | Csp_listseg (k,t1,e1,f1,t2,e2,f2) ->
      Csp_listseg (k, f_c t1, f_e e1, f_e f1, f_c t2, f_e e2, f_e f2)
  | Csp_pointsto (e,cel) ->
      Csp_pointsto (f_e e, List.map (fun (c,e) -> (f_c c, f_e e)) cel)
  | Csp_tree (t1,t2,e) ->
      Csp_tree (f_c t1, f_c t2, f_e e)
  | Csp_indpred (id,el,cl) ->
      Csp_indpred (id, List.map f_e el, List.map f_c cl)

let sub_can_form sub (pl,sl) =
  (List.map (sub_can_atom sub) pl, List.map (sub_can_spred sub) sl)

let rec sub_can_prop sub = function
  | Cp_base cf -> Cp_base (sub_can_form sub cf)
  | Cp_ifthenelse (ca,cp1,cp2) ->
      Cp_ifthenelse (sub_can_atom sub ca, sub_can_prop sub cp1, sub_can_prop sub cp2)
  | Cp_star (cp1,cp2) ->
      Cp_star (sub_can_prop sub cp1, sub_can_prop  sub cp2)

let rec fv_can_exp = function
  | Ce_num _ -> IdSet.empty
  | Ce_ident i -> IdSet.singleton i
  | Ce_xor (ce1,ce2) -> (fv_can_exp ce1) ++ (fv_can_exp ce2)

let fv_can_atom = function
  | EQ(e1,e2) -> (fv_can_exp e1) ++ (fv_can_exp e2)
  | NEQ(e1,e2) -> (fv_can_exp e1) ++ (fv_can_exp e2)

let fv_norm_can_atom ca =
  let fv = fv_can_atom ca
  in IdSet.filter (fun x -> not (is_existential x || is_garbage x)) fv

let fv_can_spred = function
  | Csp_listseg (_,_,ce1,ce2,_,ce3,ce4) ->
      (fv_can_exp ce1) ++ (fv_can_exp ce2) ++ (fv_can_exp ce3) ++ (fv_can_exp ce4)
  | Csp_pointsto (ce, ccel) ->
      let cel = List.map (function (_,ce) -> fv_can_exp ce) ccel
      in (fv_can_exp ce) ++ (List.fold_left (++) IdSet.empty cel)
  | Csp_tree (_,_,ce) -> fv_can_exp ce
  | Csp_indpred (i,cel,cl) -> assert false

let rec fv_can_form (pl,sl) =
  let fvl1 = List.map fv_can_atom pl
  and fvl2 = List.map fv_can_spred sl
  in List.fold_left (++) IdSet.empty (fvl1 @ fvl2)

let rec fv_can_prop = function
  | Cp_ifthenelse (ca,cp1,cp2) ->
      fv_can_atom ca ++ fv_can_prop cp1 ++ fv_can_prop cp2
  | Cp_star (cp1,cp2) ->
      fv_can_prop cp1 ++ fv_can_prop cp2
  | Cp_base cf -> fv_can_form cf

(**** equalities ****)

(* equalities are represented as a list  x1=E1,...,xn=En  where
     -the xi are distinct
     -the Ei do not contain occurrences of any xj and are normalized
     -xi < fv(Ei) where < is Pervasives.compare *)

type equalities = (ident * can_exp) list

let empty_eq = []

(* create a substitution from equalities *)
let eq_to_sub eq =
  let f_i x = try (snd (List.find (fun (i,e) -> i=x) eq))
              with Not_found -> Ce_ident x
  in mk_subst f_i (fun c -> c)

let eq_to_can_prop eq =
  let pl = List.map (fun (id,e) -> mk_EQ(Ce_ident id,e)) eq
  in Cp_base (pl,[])

let sub_eq sub eq =
  (* fprintf !Config.formatter "Substituting into %a@." pp_eq eq; *)
  let f i =
    let un_id = function Ce_ident x -> x | _ -> assert false
    in un_id (sub_can_exp sub (Ce_ident i)) in
  let eq' = List.map (fun (i,e) -> (f i, sub_can_exp sub e)) eq in
  (* fprintf !Config.formatter "Returns %a@." pp_eq eq'; *)
  eq'

let mk_sub (i,e) eq =
  let eq' = sub_eq (mk_single_subst (i,e)) eq
  in List.map (fun (i,e) -> (i, normalize_can_exp e)) eq'

(* extend equalities eq with e1=e2 *)
let eq_add eq (e1,e2) =
  match normalize_can_exp (sub_can_exp (eq_to_sub eq) (Ce_xor (e1,e2))) with
    | Ce_num 0 -> eq
    | Ce_num n -> raise Inconsistent
    | Ce_ident i -> (i,Ce_num 0)::(mk_sub (i,Ce_num 0) eq)
    | Ce_xor(Ce_num n, Ce_ident i) -> (i,Ce_num n)::(mk_sub (i,Ce_num n) eq)
    | Ce_xor(Ce_num n, Ce_xor (Ce_ident i, e)) -> (i,Ce_xor (Ce_num n, e))::(mk_sub (i,Ce_xor (Ce_num n, e)) eq)
    | Ce_xor(Ce_ident i, e) -> (i,e)::(mk_sub (i,e) eq)
    | _ -> assert false

(* remove binding for e from eq *)
let kill_vars_eq eq kill =
  let kl = IdSet.elements kill in
  let rec f (eq_left,eq_gone) = function
    | [] -> (eq_left,eq_gone)
    | id::l ->
	let (eq1,eq2) = List.partition (fun (x,_) -> x=id) eq_left
	in match eq1 with
	  | [] -> (eq_left,eq_gone)
	  | [(_,e1)] -> f (mk_sub (id,e1) eq2, (id,e1)::(mk_sub (id,e1) eq_gone)) l
	  | _ -> assert false in
  let (eq_left,eq_gone) = f (eq,empty_eq) kl
  in (eq_left, eq_to_sub eq_gone)

let sub_equalities sub eq =
  let eq' = sub_eq sub eq
  in List.fold_left (fun eq1 (id,e) -> eq_add eq1 (Ce_ident id, e)) [] eq'

(* constraints *)
type constr = (can_exp * can_exp) list * (can_exp * can_exp)

module ConstrSet =
  Set.Make(struct
    type t = (can_atom list * can_atom)
    let compare = compare
  end)

type constraints = ConstrSet.t

let empty_constrs = ConstrSet.empty

let normalize_constr (cal,ca) =
  (List.map normalize_can_atom cal, normalize_can_atom ca)

let normalize_constrs cs =
  let csr = ref ConstrSet.empty in
  ConstrSet.iter (fun c -> csr := ConstrSet.add (normalize_constr c) !csr) cs;
  !csr

let add_constr cs (l,(e1,e2)) =
  let (cal,ca)  = normalize_constr (List.map mk_NEQ l, mk_NEQ (e1,e2))
  in ConstrSet.add (List.stable_sort compare cal, ca) cs

let add_ineq ca pl =
  if List.mem ca pl
  then pl
  else ca::pl

let simp_constr (pl,cs) =
  let plr = ref pl in
  let f (cal,ca) =
    let cal1 = remove_duplicates cal in
    let cal2 = List.filter (fun ca1 -> not (is_uneq pl (un_NEQ ca1))) cal1
    in
      if (List.exists (fun ca -> let (e1,e2) = un_NEQ ca in e1=e2) cal2
	  || is_uneq pl (un_NEQ ca)
	  || List.mem ca cal2)
      then None
      else if cal2=[] then (plr := add_ineq ca !plr; None)
      else Some (cal2,ca) in
  let constrl = ConstrSet.elements cs in
  let csr = ref ConstrSet.empty in
    List.iter (function Some c -> csr := ConstrSet.add c !csr | None -> ()) (List.map f constrl);
    (!plr,!csr)

let rec simplify_constraints x = (* constraint simplification *)
  let y = simp_constr x
  in if x=y then x else simplify_constraints y

(* for debug

let pp_constraints_hook = ref (fun _ -> assert false)

let simplify_constraints x =
  let y = simplify_constraints x in
  Format.fprintf !Config.formatter "@.BEFORE SIMPLIFY@.";
  !pp_constraints_hook !Config.formatter x;
    Format.fprintf !Config.formatter "@.AFTER SIMPLIFY@.";
  !pp_constraints_hook !Config.formatter y;
  y
*)

let sub_constrs sub cs =
  let f (cal,ca) = (List.map (sub_can_atom sub) cal, sub_can_atom sub ca) in
  let csr = ref ConstrSet.empty in
  ConstrSet.iter (fun c -> csr := ConstrSet.add (f c) !csr) cs;
  !csr

let solve_constr (eq,pl,cs) =
  let rec f (eq,pl,cs) =
    let (pl,cs) = (List.map normalize_can_atom pl, normalize_constrs cs) in
    let (pl',cs') = simplify_constraints (pl,cs) in
    let cal = ref [] in
    ConstrSet.iter (function
      | ([ca0],ca) -> let (e1,e2)=un_NEQ ca in if e1=e2 then cal := add_ineq ca0 !cal
      | _ -> ()) cs';
    if !cal<>[] then
      begin
	let eq' = List.fold_left (fun eq ca -> eq_add eq (un_NEQ ca)) eq !cal in
	let sub = eq_to_sub eq' in
	let pl'' = remove_duplicates (List.map (sub_can_atom sub) pl') in
	let cs'' = sub_constrs sub cs'
	in f (eq',pl'',cs'')
      end
    else (eq,pl',cs') in
  let (eq1,pl1,cs1) = f (eq,pl,cs) in
  (eq1,pl1,cs1)

let is_inconsistent pl =
  List.exists
    (fun p ->
      if is_EQ p then false
      else let (e1,e2) = un_NEQ p in e1=e2)
    pl

let constrset_find f cs =
  let cl = ConstrSet.elements cs
  in List.find f cl

let solve_constraints eq pl cs = (* solve constraints and generate equalities and inequalities *)
  let inconsistent_eq ca (eq,pl,cs) =
    let eq1 = eq_add eq (un_NEQ ca) in
    let sub = eq_to_sub eq1 in
    let pl' = remove_duplicates (List.map (sub_can_atom sub) pl) in
    let cs' = sub_constrs sub cs in
    let (eq',pl'',cs'') = solve_constr (eq1,pl',cs')
    in is_inconsistent pl'' in
  let cur_state = ref (solve_constr (eq,pl,cs)) in
  let rec loop () =
    let (eq',pl',cs') = !cur_state in
    if not (is_inconsistent pl') then
    try
      let (cal,ca) = constrset_find (fun (cal,ca) -> inconsistent_eq ca !cur_state) cs'
      in cur_state := solve_constr (eq',add_ineq ca pl',cs'); loop()
    with Not_found -> ()
  in loop(); !cur_state

(**** pretty printing ****)
open Format

let pp_string f s = fprintf f "%s" s

let rec pp_listsep pp s1 s2 f = function
  | [] -> fprintf f "%s" s2
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a%s %a" pp x s1 (pp_listsep pp s1 s2) l

let rec pp_seq pp f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a,%a" pp x (pp_seq pp) l

let rec pp_can_exp f = function
  | Ce_num n -> fprintf f "%d" n
  | Ce_ident id -> fprintf f "%a" pp_ident id
  | Ce_xor (e1,e2) -> fprintf f "%a ^ %a" pp_can_exp e1 pp_can_exp e2

let pp_can_atom f ca =
  match ca with
    | EQ (e1,e2) -> fprintf f "%a==%a" pp_can_exp e1 pp_can_exp e2
    | NEQ (e1,e2) -> fprintf f "%a!=%a" pp_can_exp e1 pp_can_exp e2

let pp_can_spred f = function
  | Csp_listseg (SINGLE,t1,e1,f1,_,_,_) ->
      fprintf f "listseg(%s; %a, %a)"
      t1 pp_can_exp e1 pp_can_exp f1
  | Csp_listseg (DOUBLE,t1,e1,f1,t2,e2,f2) ->
      fprintf f "dlseg(%s,%s; %a, %a, %a, %a)"
      t1 t2 pp_can_exp e1 pp_can_exp f1 pp_can_exp e2 pp_can_exp f2
  | Csp_listseg (XOR,t1,e1,f1,t2,e2,f2) ->
      fprintf f "xlseg(%s; %a, %a, %a, %a)"
      t1 pp_can_exp e1 pp_can_exp f1 pp_can_exp e2 pp_can_exp f2
  | Csp_pointsto (e1, cel) ->
      let pp f (c,e) = fprintf f "%s:%a" c pp_can_exp e
      in fprintf f "%a |-> %a"
	   pp_can_exp e1 (pp_seq pp) cel
  | Csp_tree (t1,t2,e) ->
      fprintf f "tree(%s,%s;%a)" t1 t2 pp_can_exp e
  | Csp_indpred (id,el,cl) ->
      fprintf f "%s(%a;@[<hov 2>%a@])" id (pp_seq pp_can_exp) el (pp_seq pp_print_string) cl

let pp_pure_list = pp_listsep pp_can_atom " *" ""
let pp_spatial_list = pp_listsep pp_can_spred " *" "emp"

let pp_can_form f (pl,sl) = match (pl,sl) with
  | ([],[]) -> fprintf f "emp"
  | (_::_,[]) -> pp_pure_list f pl
  | ([],_::_) -> pp_spatial_list f sl
  | _ -> fprintf f "%a * %a" pp_pure_list pl pp_spatial_list sl

let rec pp_can_prop f = function
  | Cp_ifthenelse (ca,p1,p2) ->
      fprintf f "if %a@ then %a@ else %a"
      pp_can_atom ca pp_can_prop p1 pp_can_prop p2
  | Cp_star (p1,p2) ->
      fprintf f "%a * %a" pp_can_prop p1 pp_can_prop p2
  | Cp_base cf -> pp_can_form f cf

let rec pp_can_stmt f st = match st.can_st_desc with
  | Cst_ifthenelse (ca,c1,c2) ->
      fprintf f "@[<hov>if %a@ then @[<hv>%a@]@ else @[<hv>%a@]"
      pp_can_atom ca pp_can_cmd c1 pp_can_cmd c2
  | Cst_assign (x,e) ->
      fprintf f "%a=%a" pp_ident x pp_can_exp e
  | Cst_fldlookup (x,e,t) ->
      fprintf f "%a=%a->%s" pp_ident x pp_can_exp e t
  | Cst_fldassign (e1,t,e2) ->
      fprintf f "%a->%s=%a"
      pp_can_exp e1 t pp_can_exp e2
  | Cst_new (x) ->
      fprintf f "new(%a)" pp_ident x
  | Cst_dispose (e) ->
      fprintf f "dispose(%a)" pp_can_exp e
  | Cst_fcall (modif,cp1,cp2,s) ->
      fprintf f "fcall(@[<hv>{%a},@[<hov 2>%a@],@ @[<hov 2>%a@]@])"
      (pp_listsep pp_string "," "") (List.map string_of_ident (IdSet.elements modif))
      pp_can_prop cp1 pp_can_prop cp2
  | Cst_wand (cp) ->
      pp_can_stmt f {st with can_st_desc = Cst_fcall (IdSet.empty,can_prop_empty,cp,"")}

and pp_can_cmd pp sl =
  List.iter (fun st -> fprintf pp "%a;@." pp_can_stmt st) sl

let pp_entailment f (cp1,c,cp2,s,loc) =
  fprintf f "[%a]@.%a[%a]@."
    pp_can_prop cp1 pp_can_cmd c pp_can_prop cp2

let pp_can_entailment f (cf1,cf2) =
  fprintf f "@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]"
    pp_can_form cf1 pp_can_form cf2

let pp_pure_entailment f (cf1,a) =
  fprintf f "@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]"
    pp_can_form cf1 pp_can_atom a

let pp_sp_entailment f (cf1,cf2) =
  fprintf f "@[<hv>@[<hov 2>%a@]@ |-@ @[<hov 2>%a@]@]"
    pp_can_form cf1 pp_can_form cf2

let pp_inst f inst =
  if !Config.verbose1 then
    if inst <> []
    then fprintf f "Instantiations inferred: %a@."
	(pp_seq (fun f (x,e) -> fprintf f "%s=%a" (string_of_ident x) pp_can_exp e)) inst

let pp_constraint f (cal,ca) =
  fprintf f "%a => %a@."  pp_pure_list cal pp_can_atom ca

let pp_constraints f (pl,cs) =
  fprintf f "CONSTRAINTS: @.";
  fprintf f "%a@." pp_pure_list pl;
  ConstrSet.iter (pp_constraint f) cs

(* for debug
let _ = pp_constraints_hook := pp_constraints
*)

(**** Conversion to canonical form ****)

let report_error s pp x =
  if !Config.verbose1 then
    Format.fprintf !Config.formatter "**** %s%a@." s pp x

let report_prop_error s p = report_error s pp_assert p

let report_a_exp_error s e = report_error s pp_a_exp e

let rec a_exp_to_can_exp e = match e with
  | Aexp_ident s -> Ce_ident (create_ident s)
  | Aexp_num n -> Ce_num n
  | Aexp_infix ("^",e1,e2) -> Ce_xor (a_exp_to_can_exp e1, a_exp_to_can_exp e2)
  | _ -> report_a_exp_error "a_exp_to_can_exp: " e; Ce_num 0

let p_exp_to_can_exp pe =
  a_exp_to_can_exp (a_exp_of_p_exp pe)

let can_atom_to_can_prop ca =
  Cp_base ([ca],[])

exception Undef_prop_to_can_atom of string

let rec prop_to_can_atom ?(quiet=false) p  = match p with
  | Aprop_equal (e1,e2) ->
      mk_EQ (a_exp_to_can_exp e1, a_exp_to_can_exp e2)
  | Aprop_not_equal (e1,e2) ->
      mk_NEQ (a_exp_to_can_exp e1, a_exp_to_can_exp e2)
  | Aprop_infix (op,e1,e2) ->
      if not quiet then report_prop_error "abstracting arithmetic in " p;
      let (id2,id1) = (gensym_garb (create_ident "abs"), gensym_garb (create_ident "abs"))
      in mk_EQ (Ce_ident id1, Ce_ident id2)
  | Aprop_spred(Aspred_empty) -> mk_EQ (Ce_num 0,Ce_num 0)
  | Aprop_false -> mk_NEQ (Ce_num 0,Ce_num 0)
  | _ -> raise(Undef_prop_to_can_atom
		 (let buf = Buffer.create 16 in
		  let fmt = Format.formatter_of_buffer buf in
		    pp_assert fmt p;
		    Format.pp_print_flush fmt ();
		    Buffer.contents buf))

let a_space_pred_to_can_spred = function
  | Aspred_list (t,e) ->
      if !Config.inductive_preds
      then [Csp_indpred ("list",[a_exp_to_can_exp e],[t])]
      else [(Csp_listseg(SINGLE, t, a_exp_to_can_exp e, Ce_num 0,
             t, a_exp_to_can_exp e, Ce_num 0))] (* last 3 argument are garbage *)
  | Aspred_listseg (t,e1,e2) ->
      [Csp_listseg(SINGLE, t, a_exp_to_can_exp e1, a_exp_to_can_exp e2,
                    t, a_exp_to_can_exp e1, a_exp_to_can_exp e2)] (* last 3 argument are garbage *)
  | Aspred_dlseg (k,t1,e1,f1,t2,e2,f2) ->
      [Csp_listseg((if k=DL then DOUBLE else XOR),
                   t1,a_exp_to_can_exp e1, a_exp_to_can_exp f1,
                   t2,a_exp_to_can_exp e2, a_exp_to_can_exp f2)]
  | Aspred_pointsto (e,cel) ->
      let f (c,e) = (c, a_exp_to_can_exp e)
      in [Csp_pointsto (a_exp_to_can_exp e, List.map f cel)]
  | Aspred_tree (t1,t2,e)->
      [Csp_tree (t1,t2, a_exp_to_can_exp e)]
  | Aspred_empty -> []

let rec simpl_can_prop cp = match cp with
  |  Cp_base cf -> cp
  |  Cp_ifthenelse (ca,cp1,cp2) ->
       Cp_ifthenelse (ca, simpl_can_prop cp1, simpl_can_prop cp2)
  |  Cp_star (cp1,cp2) ->
       (match (simpl_can_prop cp1, simpl_can_prop cp2) with
	  | (Cp_base ([],[]), cp2') -> cp2'
	  | (cp1', Cp_base ([],[])) -> cp1'
	  | (Cp_base (pl1,sl1), Cp_base (pl2,sl2)) -> Cp_base (pl1@pl2, sl1@sl2)
	  | (cp1',cp2') -> Cp_star (cp1',cp2'))

let can_prop_star cp1 cp2 =
  simpl_can_prop (Cp_star (cp1,cp2))

let and_cprop_catom cp ca =
  simpl_can_prop (Cp_star (cp, Cp_base ([ca],[])))

let rec is_pure = function
  | Cp_base (_,sl) -> sl = []
  | Cp_ifthenelse (_,cp1,cp2) -> (is_pure cp1) && (is_pure cp2)
  | Cp_star (cp1,cp2) -> (is_pure cp1) && (is_pure cp2)

let is_can_prop_empty = is_pure

let rec prop_to_can_prop p = match p with
  | Aprop_star (p1,p2) ->
      can_prop_star (prop_to_can_prop p1) (prop_to_can_prop p2)
  | Aprop_ifthenelse (p1,p2,p3) ->
      Cp_ifthenelse (prop_to_can_atom p1, prop_to_can_prop p2, prop_to_can_prop p3)
  | Aprop_spred sp ->
      Cp_base([], a_space_pred_to_can_spred sp)
  | _ -> Cp_base ([prop_to_can_atom p],[])

(* convention for existentially quantified identifiers *)
let existential_id = function
  | Ce_ident id -> is_existential id
  | _ -> false

let ex_fv_can_prop cp =
  let fv = fv_can_prop cp in
  IdSet.filter is_existential fv

let existentials_sub fv =
  let idl = IdSet.elements fv in
  let idl' = List.map (fun x -> (x, Ce_ident (gensym (un_existential x)))) idl
  in mk_subst_pairs idl'

let fv_norm_can_prop cp =
  let fv = fv_can_prop cp
  in IdSet.filter (fun x -> not (is_existential x || is_garbage x)) fv

let fv_keep_can_spred = function
  | Csp_listseg (_,_,ce1,ce2,_,ce3,ce4) ->
      (fv_can_exp ce1) ++ (fv_can_exp ce2) ++ (fv_can_exp ce3) ++ (fv_can_exp ce4)
  | Csp_pointsto (ce, ccel) ->
      fv_can_exp ce
  | Csp_tree (_,_,ce) -> fv_can_exp ce
  | Csp_indpred (i,cel,cl) -> assert false

(* important variables not to be treated as garbage *)
let fv_keep_can_prop cp =
  let rec f = function
    | Cp_base (pl,sl) ->
	List.fold_left (fun s sp -> fv_keep_can_spred sp ++ s) IdSet.empty sl
    | Cp_star (cp1,cp2) -> f cp1 ++ f cp2
    | Cp_ifthenelse(ca,cp1,cp2) -> fv_can_atom ca ++ f cp1 ++ f cp2
  in f cp

let fv_killable_vars cp =
  let s = fv_can_prop cp in
  let s1 = IdSet.filter is_garbage s in
  let keep = fv_keep_can_prop cp in
  let kill = IdSet.diff s1 keep
  in kill

let kill_vars_can_prop cp kill =
  let rec f = function
    | Cp_base (pl,sl) ->
	let pl1 = List.filter
	  (fun ca -> IdSet.is_empty (IdSet.inter (fv_can_atom ca) kill)) pl in
	let sl1 = List.map
	  (function Csp_pointsto (e,cel) ->
	     Csp_pointsto (e,List.filter (fun (c,e1) -> IdSet.is_empty (IdSet.inter (fv_can_exp e1) kill)) cel)
	     | csp -> csp) sl
	in Cp_base (pl1,sl1)
    | Cp_star (cp1,cp2) -> Cp_star(f cp1, f cp2)
    | Cp_ifthenelse(ca,cp1,cp2) -> Cp_ifthenelse(ca,f cp1, f cp2)
  in f cp

let pp_eq pp eq =
  let cal = List.map (fun (i,e) -> EQ(Ce_ident i, e)) eq
  in (pp_listsep pp_can_atom "," ".") pp cal

let kill_garbage_vars (eq,cp) =
  let kill = fv_killable_vars cp in
  let (eq1,sub) = kill_vars_eq eq kill in
  let cp1 = kill_vars_can_prop (sub_can_prop sub cp) kill
  in
  (* for debugging
    if not (IdSet.is_empty kill)
    then
      fprintf !Config.formatter "@.STATE %a@.%a@.KILLING VARS %a@.RETURNS %a@.%a@."
	pp_eq eq pp_can_prop cp
	(pp_listsep pp_ident " " "") (IdSet.elements kill)
	pp_eq eq1 pp_can_prop cp1;
  *)
  (eq1,cp1)

(* for debug
let eq_add eq (e1,e2) =
  let _ = fprintf !Config.formatter "Extend equalities %a with %a=%a@."
      pp_eq eq pp_can_exp e1 pp_can_exp e2 in
  let eq' = eq_add eq (e1,e2) in
  let _ = fprintf !Config.formatter "Results in %a@." pp_eq eq'
  in eq'
*)
