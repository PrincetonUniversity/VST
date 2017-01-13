open Misc
open Parsetree
open Symbtree
open Error

type fun_item =
    { fid : string;
      param: string list * string list;
      locals: IdSet.t;
      bound : IdSet.t;  (* locals + params *)
      mutable calls: StringSet.t StringMap.t;  (* map from fid to minimum set of resources
                                                  always acquired before calling fid *)
      mutable in_parallel_with: StringSet.t;
      mutable requires: StringSet.t;
      mutable modif: IdSet.t;
      mutable vars: IdSet.t;
      pre: can_prop;
      body: p_statement list;
      post: can_prop;
      post_loc: Location.t;
      fun_loc: Location.t }

type res_item =
    { rid : string;
      owned: IdSet.t;
      rinv : can_prop;
      res_loc: Location.t }

type env = {mutable functions: fun_item list;
            mutable resources: res_item list;
	    mutable enable :  IdSet.t * IdSet.t -> StringSet.t}

let initial_env () = {functions = []; resources = []; enable = fun _ -> assert false}

exception Env_not_found

let lookup_function env fid =
  let filter fi = fi.fid = fid
  in try List.find filter env.functions
     with Not_found -> raise Env_not_found

let lookup_resource env rid =
  let filter ri = ri.rid=rid
  in try List.find filter env.resources
     with Not_found -> raise Env_not_found

let env_add_fun fi env =
  env.functions <- fi::env.functions

let env_add_res ri env =
  List.iter
    (function r ->
       if r.rid=ri.rid then raise (Vcgen_rsrc_not_distinct(ri.rid,ri.res_loc));
       (try (let v = IdSet.choose (IdSet.inter r.owned ri.owned)
	     in raise (Vcgen_owned_not_disjoint(string_of_ident v,ri.rid,r.rid,ri.res_loc)))
	with Not_found -> ());
       (try (let v =
	       IdSet.choose (IdSet.inter (fv_norm_can_prop r.rinv) ri.owned)
	     in raise (Vcgen_owned_free_in_inv(string_of_ident v,r.rid,ri.rid,ri.res_loc)))
	with Not_found -> ());
       (try (let v =
	       IdSet.choose (IdSet.inter (fv_norm_can_prop ri.rinv) r.owned)
	     in raise (Vcgen_owned_free_in_inv(string_of_ident v,ri.rid,r.rid,ri.res_loc)))
	with Not_found -> ())
    ) env.resources;
  env.resources <- ri::env.resources

let (++) = IdSet.union
let (--) = IdSet.diff
let (+) s x = s ++ (IdSet.singleton x)
let (-) s x = IdSet.remove x s
let set_of_list l =
  List.fold_left (+) IdSet.empty l
let union_map f l =
   List.fold_left (fun ss x -> ss ++ (f x)) IdSet.empty l
let set_find f s = IdSet.choose (fst (IdSet.partition f s))

(* translate an invariant to a proposition *)
let inv_to_prop po = match po with
  | None -> can_prop_empty
  | Some p -> prop_to_can_prop p

type mod_var_req =
 { md: IdSet.t; vr: IdSet.t; rq:StringSet.t }

let union_map_mvr f l =
   List.fold_left
   (fun mvr x -> let mvr' = f x in {md=mvr.md++mvr'.md; vr=mvr.vr++mvr'.vr; rq=  StringSet.union mvr.rq mvr'.rq})
   {md=IdSet.empty; vr=IdSet.empty; rq=StringSet.empty} l

(* modified and vars and required for a sequence of statements *)
let mvr_body env stl =
  let enable = env.enable in
  let enable_var vr = enable (IdSet.empty,vr) in
  let fv_e e = fv_can_exp (p_exp_to_can_exp e) in
  let fv_a a = fv_norm_can_atom ((prop_to_can_atom ~quiet:true (a_prop_of_p_exp a))) in
  let fv_p p = fv_norm_can_prop (inv_to_prop p) in
  let rec f st = match st.pstm_desc with
    | Pstm_assign (i,e) ->
	let id = create_ident i in
        let md = IdSet.singleton id
	and vr = fv_e e + id in
        {md=md; vr=vr; rq=enable(md,vr)}
    | Pstm_fldlookup (i,e,_) ->
	let id = create_ident i in
        let md = IdSet.singleton id
	and vr = fv_e e + id in
        {md=md; vr=vr; rq=enable(md,vr)}
    | Pstm_fldassign (e1,_,e2) ->
        let md = IdSet.empty
	and vr = fv_e e1 ++ fv_e e2 in
        {md=md; vr=vr; rq=enable(md,vr)}
    | Pstm_new i ->
	let id = create_ident i in
        let md = IdSet.singleton id
	and vr = IdSet.singleton id in
        {md=md; vr=vr; rq=enable(md,vr)}
    | Pstm_dispose e ->
        let md = IdSet.empty
        and vr = fv_e e in
        {md=md; vr=vr; rq=enable(md,vr)}
    | Pstm_block stl -> union_map_mvr f stl
    | Pstm_if (a,st1,st2) ->
        let mvr1 = f st1
	and mvr2 = f st2
	and vr' = fv_a a in
	{md = mvr1.md++mvr2.md; vr = mvr1.vr ++ mvr2.vr ++ vr'; rq = StringSet.union (StringSet.union mvr1.rq mvr2.rq) (enable_var vr')}
    | Pstm_while (inv,a,st) ->
        let mvr = f st
	and vr' = fv_a a ++ fv_p inv in
	{md = mvr.md; vr = mvr.vr ++ vr'; rq = StringSet.union mvr.rq (enable_var vr')}
    | Pstm_withres (rid,a,st) ->
        let ri = lookup_resource env rid in
        let mvr = f st
        and owned = ri.owned
        and vr' = fv_a a in
	let md = mvr.md -- owned in
        {md = md; vr = md ++ ((mvr.vr ++ vr') -- (fv_norm_can_prop ri.rinv));
	 rq = StringSet.remove rid (StringSet.union mvr.rq (enable_var vr'))}
    | Pstm_fcall (fid,(refpars,valpars)) ->
       let fi = lookup_function env fid in
       let (md1,vr1,rq1) = (fi.modif,fi.vars,fi.requires) in
       let md2 = union_map IdSet.singleton (List.map create_ident refpars) in
       let vr2 = union_map fv_e valpars ++ md2 in
       {md = md1++md2; vr = vr1++vr2; rq = StringSet.union rq1 (enable(md2,vr2))}
    | Pstm_parallel_fcall (f1,pr1,f2,pr2) ->
      let mvr1 = f {st with pstm_desc = Pstm_fcall (f1,pr1)}
      and mvr2 = f {st with pstm_desc = Pstm_fcall (f2,pr2)} in
     {md = mvr1.md++mvr2.md; vr = mvr1.vr ++ mvr2.vr; rq = StringSet.union mvr1.rq mvr2.rq}
  in union_map_mvr f stl

let (+++) sm (i,s) =
  try let s' = StringMap.find i sm
      in StringMap.add i (StringSet.inter s s') sm
  with Not_found -> StringMap.add i s sm

let (++++) sm1 sm2 =
  StringMap.fold (fun i acq sm -> sm +++ (i,acq)) sm1 sm2

(* initial call graph: only functions called directly *)
let initial_call_graph env fi  =
  let check_fcall fid loc =
    try ignore (lookup_function env fid)
    with Env_not_found -> raise (Vcgen_unknown_fun (fid,loc)) in
  let check_withres rid loc =
    try ignore (lookup_resource env rid)
    with Env_not_found -> raise (Vcgen_unknown_res (rid,loc)) in
  let add_fcall fid acquired = fi.calls <- fi.calls +++ (fid,acquired) in
  let rec f acquired st = match st.pstm_desc with
    | Pstm_if (_,st1,st2) -> f acquired st1; f acquired st2
    | Pstm_while (_,_,st) -> f acquired st
    | Pstm_block stl -> List.iter (f acquired) stl
    | Pstm_withres (rid,_,st) ->
        check_withres rid st.pstm_loc;
	f (StringSet.add rid acquired) st
    | Pstm_fcall (i,_) ->
        check_fcall i st.pstm_loc;
        add_fcall i acquired
    | Pstm_parallel_fcall (i1,args1,i2,args2) ->
        check_fcall i1 st.pstm_loc;
        check_fcall i2 st.pstm_loc;
        add_fcall i1 acquired;
        add_fcall i2 acquired
    | Pstm_assign _ | Pstm_fldlookup _ | Pstm_fldassign _ | Pstm_new _ | Pstm_dispose _ -> ()
  in List.iter (f StringSet.empty) fi.body

(* compute the entire call graph of fi assuming _.calls in stop are complete *)
let call_graph_fid env fi stop =
  let stopr = ref stop in
  let rec f acquired fi =
    StringMap.fold
    (fun fid' acquired' sm ->
       let fi' = lookup_function env fid' in
       let acq = StringSet.union acquired acquired' in
       let deep_calls =
         if StringSet.mem fid' !stopr
         then StringMap.map (fun acquired'' -> StringSet.union acquired'' acq) fi'.calls
         else
           (stopr := StringSet.add fid' !stopr;
           f (StringSet.union acquired acquired') fi')
       in sm ++++ (deep_calls +++ (fid',acq)))
    fi.calls StringMap.empty
  in f StringSet.empty fi

(* entire call graph of all the functions *)
let calc_call_graph env =
  let fil = env.functions in
  let _ = List.iter (initial_call_graph env) fil in
  let stopr = ref StringSet.empty in
  let f fi =
    begin
      fi.calls <- call_graph_fid env fi !stopr;
      stopr := StringSet.add fi.fid !stopr
    end
  in List.iter f fil

(* create a function  enable (mS aS) returning the resources required to modify mS and access aS *)
let mk_enable_fun env =
  let m = ref IdMap.empty in
  let find id =
    try IdMap.find id !m
    with Not_found -> (StringSet.empty,StringSet.empty) in
  let add_mods id rid =
    let (mods,vars) = find id
    in m := IdMap.add id (StringSet.add rid mods,vars) !m  in
  let add_vars id rid =
    let (mods,vars) = find id
    in m := IdMap.add id (mods,StringSet.add rid vars) !m in
  let f ri =
    let inv_vars = fv_norm_can_prop ri.rinv
    in IdSet.iter (fun id -> add_mods id ri.rid) inv_vars;
      IdSet.iter (fun id -> add_vars id ri.rid) ri.owned
  in List.iter f env.resources;
    let enable (mS,aS) =
      StringSet.union
	(IdSet.fold (fun id s -> StringSet.union s (fst (find id))) mS StringSet.empty)
	(IdSet.fold (fun id s -> StringSet.union s (snd (find id))) aS StringSet.empty)
    in enable

let check_disjoint_bound_globals env globals =
  let check_fun fi =
    try
      let x = IdSet.choose (IdSet.inter fi.locals globals)
      in raise (Vcgen_bound_globals ("local",string_of_ident x,"function",fi.fid,fi.fun_loc))
    with Not_found -> ();
    try
      let x = IdSet.choose (IdSet.inter fi.bound globals)
      in raise (Vcgen_bound_globals ("parameter",string_of_ident x,"function",fi.fid,fi.fun_loc))
    with Not_found -> ()
  in List.iter check_fun env.functions


(* calculates the modified and vars and required set for each function *)
let calc_mvr env =
  let enable = mk_enable_fun env in
  env.enable <- enable;
  let shallow_mod fi =
    let mvr = mvr_body env fi.body in
    let fv_spec = (fv_norm_can_prop fi.pre ++ fv_norm_can_prop fi.post) in
    fi.modif <- mvr.md -- fi.bound;
    fi.vars <- (mvr.vr ++ fv_spec) -- fi.bound;
    fi.requires <- StringSet.union mvr.rq (enable (IdSet.empty, fv_spec -- fi.bound))
  in List.iter shallow_mod env.functions;
  let deep_mod fi =
    let call_set fi' =
      StringMap.fold (fun fid _ s -> StringSet.add fid s) fi'.calls (StringSet.singleton fi'.fid) in
    let in_par_with loc = function
      | Pstm_parallel_fcall (f1,_,f2,_) ->
          let (fi1,fi2) = (lookup_function env f1, lookup_function env f2)
          in fi1.in_parallel_with <- StringSet.union fi1.in_parallel_with (call_set fi2);
             fi2.in_parallel_with <- StringSet.union fi2.in_parallel_with (call_set fi1)
      | _ -> ()
    in Parsetree.iter in_par_with fi.body;
    let owned_set acq =
      StringSet.fold (fun rid s -> (lookup_resource env rid).owned ++ s) acq IdSet.empty in
    let modif =
      StringMap.fold
      (fun fid acq modif -> modif ++ ((lookup_function env fid).modif -- owned_set acq))
      fi.calls fi.modif
    and vars =
      StringMap.fold
      (fun fid acq vars -> vars ++ ((lookup_function env fid).vars -- owned_set acq))
      fi.calls fi.vars
    and requires =
      StringMap.fold
      (fun fid acq req -> StringSet.union req (StringSet.diff (lookup_function env fid).requires acq))
      fi.calls fi.requires
    in fi.requires <- requires;
       fi.modif <- modif;
       fi. vars <- vars in
    List.iter deep_mod env.functions;
    let globals = ref (IdSet.empty) in
    let globals_fun fi =
      globals := !globals ++ fi.vars ++ (fv_norm_can_prop fi.pre -- fi.bound) ++ (fv_norm_can_prop fi.post -- fi.bound) in
    let globals_res ri =
      globals := !globals ++ (fv_norm_can_prop ri.rinv) ++ ri.owned in
    List.iter globals_fun env.functions;
    List.iter globals_res env.resources;
    check_disjoint_bound_globals env !globals

let rec desugar_fun_res iteml env =
  let f = function
    | Pfundecl (fid,param,pre,locals,body,post,post_loc,fun_loc) ->
        let pre = inv_to_prop pre
	and post = inv_to_prop post in
        let locals = set_of_list (List.map create_ident locals) in
	let bound =
	  let param_vars = set_of_list (List.map create_ident ((fst param) @ (snd param))) in
	  let _ =
	    try
	      let x = IdSet.choose (IdSet.inter locals param_vars)
	      in raise (Vcgen_param_locals (string_of_ident x,fid,fun_loc))
	    with Not_found -> ()
          in locals ++ param_vars
	in
	  env_add_fun
	    {fid=fid; param=param; locals=locals; bound=bound; calls=StringMap.empty; in_parallel_with=StringSet.empty;
	     requires=StringSet.empty; modif=IdSet.empty; vars=IdSet.empty; pre=pre; body=body; post=post; post_loc=post_loc; fun_loc=fun_loc}
	    env
    | Presource (rid,owned,inv,loc) ->
        let owned = set_of_list (List.map create_ident owned) in
	  env_add_res
            {rid=rid; owned=owned; rinv=prop_to_can_prop inv; res_loc=loc}
            env
  in List.iter f iteml

open Format

let pp_string pp s = fprintf pp "%s" s

let rec pp_listsep pp s1 s2 f = function
  | [] -> fprintf f "%s" s2
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a%s%a" pp x s1 (pp_listsep pp s1 s2) l

let pp_call_item pp (fid,acq) =
  match StringSet.elements acq with
  | [] -> pp_string pp fid
  | l -> fprintf pp "{%a}%a" (pp_listsep pp_string " " "") l pp_string fid

let pp_call_set pp sm =
  match StringMap.fold (fun fid acq l -> (fid,acq)::l) sm [] with
  | [] -> ()
  | call_items -> fprintf pp " CALLS %a" (pp_listsep pp_call_item "," "") call_items

let pp_strset x pp s = match StringSet.elements s with
  | [] -> ()
  | l -> fprintf pp " %s %a" x (pp_listsep pp_string "," "") l

let pp_idset x pp s = match (List.map string_of_ident (IdSet.elements s)) with
  | [] -> ()
  | l -> fprintf pp " %s %a" x (pp_listsep pp_string "," "") l

let print_env pp env =
  let f fi = fprintf pp "FUNCTION %s%a%a%a%a%a@." fi.fid
     pp_call_set fi.calls  (pp_strset "IN_PARALLEL_WITH") fi.in_parallel_with (pp_strset "REQUIRES") fi.requires
     (pp_idset "MODIFIES") fi.modif (pp_idset "READS") fi.vars
  in List.iter f env.functions

let check_sequential rsrc =
  Parsetree.iter
    (fun loc -> function
       | Pstm_withres _ | Pstm_fcall _ | Pstm_parallel_fcall _ ->
	   raise (Vcgen_non_seq_initzer(rsrc,loc))
       | _ -> ())

(* star resource invariants *)
let desugar_rsrc_initzers iteml env =
  let rsrc_invs =
    List.fold_right
      (fun item invs -> match item with
	 | Presource(rid,prots,inv,loc) -> (
	     let can_inv = prop_to_can_prop inv in
	       can_prop_star can_inv invs)
	 | _ -> invs)
      iteml
      can_prop_empty
  (* if absent, extend iteml with an init function consisting of the
     resource initializers *)
  in (rsrc_invs,
      if (List.exists
	    (function
	       | Pfundecl("init",_,_,_,body,_,_,_) ->
		   check_sequential "combination" body; true
	       | _ -> false)
	    iteml) || not (List.exists (function Presource _ -> true | _ -> false) iteml)
      then iteml
      else (Pfundecl("init",
	 	     ([],[]),
	 	     Some (Aprop_spred Aspred_empty),
	 	     [],
	 	     [],
	 	     Some (Aprop_spred Aspred_empty),
	 	     Location.none,
	 	     Location.none)
	    :: iteml))

let compose_init_and_main rsrc_invs env =
  let init_post =
    let l,funs = (try List.partition (fun fi -> fi.fid = "init") env.functions
	 	  with Not_found -> [], env.functions) in
      match l with
	| [] -> can_prop_empty
	| [init_fun] -> (* add resource invariants to post of init *)
	    env.functions <-
	      {init_fun with post = (can_prop_star init_fun.post rsrc_invs)} ::
	      funs;
	    init_fun.post
	| i0::i1::_ -> raise (Vcgen_multiple_inits(i0.fun_loc, i1.fun_loc)) in
  let l,funs = (try List.partition (fun fi -> fi.fid = "main") env.functions
		with Not_found -> [], env.functions) in
    match l with
      | [] -> (if !Config.verbose2
	       then (fprintf !Config.formatter "No main() found.@."))
      | [main_fun] ->
	  env.functions <-
	    {fid= "compose_init_main";
	     pre= init_post;
	     body= [];
	     post= main_fun.pre;
	     param= [],[];
	     locals= IdSet.empty;
	     bound= IdSet.empty;
	     calls= StringMap.empty;
	     in_parallel_with= StringSet.empty;
	     requires= StringSet.empty;
	     modif= IdSet.empty;
	     vars= IdSet.empty;
	     post_loc= Location.none;
	     fun_loc= Location.none}
	  :: env.functions
      | m0::m1::_ -> raise (Vcgen_multiple_mains(m0.fun_loc, m1.fun_loc))

let check_variable_conditions env =
  let check_main_req_empty () =
    try (let main_fun = List.find (fun fi -> fi.fid = "main") env.functions in
	   (* check that main requires no resources *)
	   if not (StringSet.is_empty main_fun.requires)
	   then raise (Vcgen_main_nonempty_req(main_fun.fun_loc)))
    with Not_found -> () in
  let rec check_fcalls loc = function
  | Pstm_parallel_fcall (fid1,args1,fid2,args2) ->
    check_fcalls loc (Pstm_fcall (fid1,args1));
    check_fcalls loc (Pstm_fcall (fid2,args2));
    let (fi1,fi2) = (lookup_function env fid1, lookup_function env fid2) in
    let mvr1 = mvr_body env [{pstm_desc = Pstm_fcall (fid1,args1); pstm_loc=loc}]
    and mvr2 = mvr_body env [{pstm_desc = Pstm_fcall (fid2,args2); pstm_loc=loc}] in
    let fv_spec1 = fv_norm_can_prop fi1.pre ++ fv_norm_can_prop fi1.post
    and fv_spec2 = fv_norm_can_prop fi2.pre ++ fv_norm_can_prop fi2.post in
    let check_mod_spec fid m fid' fv_spec =
      try let id = IdSet.choose (IdSet.inter m fv_spec)
          in raise (Vcgen_modify_spec (fid,string_of_ident id,fid',loc))
      with Not_found -> () in
    let check_race fid m fid' a =
      try let id = IdSet.choose (IdSet.inter m a)
          in raise (Vcgen_var_race (fid,string_of_ident id,fid',loc))
      with Not_found -> ()
    in check_race fid1 mvr1.md fid2 mvr2.vr;
       check_race fid2 mvr2.md fid1 mvr1.vr;
       check_mod_spec fid1 mvr1.md fid2 fv_spec2;
       check_mod_spec fid2 mvr2.md fid1 fv_spec1
  |  Pstm_fcall (fid,(refpars,valpars)) ->
       let fi = lookup_function env fid in
       let refset = set_of_list (List.map create_ident refpars) in
       let bad_set = IdSet.inter refset fi.vars in
       (try let id = IdSet.choose bad_set
            in raise (Vcgen_global_ref (string_of_ident id,fid,loc))
       with Not_found -> ())
  | _ -> ()
  in (check_main_req_empty();
      List.iter (fun fid -> Parsetree.iter check_fcalls fid.body) env.functions)

let create_env iteml =
  let env = initial_env () in
  let rsrc_invs, iteml = desugar_rsrc_initzers iteml env in
    desugar_fun_res iteml env;
    compose_init_and_main rsrc_invs env;
    env.functions <- List.rev env.functions;
    calc_call_graph env;
    calc_mvr env;
    if !Config.verbose1 then print_env !Config.formatter env;
    check_variable_conditions env;
    env

let vcgen_fun env fi =
  let mkst desc loc =
    { can_st_desc = desc;
      can_st_loc = loc; } in
  let provisos = ref [] in
  let rec f {pstm_desc = d; pstm_loc = loc} = match d with
    | Pstm_assign (i, e) ->
	let ce = p_exp_to_can_exp e
	in [mkst (Cst_assign (create_ident i, ce)) loc]
    | Pstm_fldlookup (i, e, t) ->
	let ce = p_exp_to_can_exp e
	in [mkst (Cst_fldlookup (create_ident i, ce, t)) loc]
    | Pstm_fldassign (e1, t, e2) ->
	let ce1 = p_exp_to_can_exp e1 in
	let ce2 = p_exp_to_can_exp e2
	in [mkst (Cst_fldassign (ce1,t,ce2)) loc]
    | Pstm_new i ->
	[mkst (Cst_new (create_ident i)) loc]
    | Pstm_dispose e ->
	let ce = p_exp_to_can_exp e
	in [mkst (Cst_dispose ce) loc]
    | Pstm_block sl ->
	List.flatten (List.map f sl)
    | Pstm_if (e, s1, s2) ->
	let (ae,c1,c2) = (prop_to_can_atom (a_prop_of_p_exp e), f s1, f s2)
	in [mkst (Cst_ifthenelse (ae,c1,c2)) loc]
    | Pstm_while (inv, e, s) ->
        let ca = prop_to_can_atom (a_prop_of_p_exp e) in
	let inv = inv_to_prop inv in
        let exfv = ex_fv_can_prop inv in
        let sub = existentials_sub exfv in
        let while_post = and_cprop_catom inv (neg_can_atom ca) in
	  (* add an fcall to inv in order to allow s to frame away some of inv *)
	let prov1 = (and_cprop_catom (sub_can_prop sub inv) ca, f s, inv, "loop exit", loc) in
	  begin
	    provisos := prov1 :: !provisos;
	    [mkst (Cst_fcall ((mvr_body env [s]).md,inv,while_post, "loop entry")) loc]
          end
    | Pstm_withres (rid, e, s) ->
	let modified_in_parallel = union_map (function fid -> (lookup_function env fid).modif) (StringSet.elements fi.in_parallel_with) in
	let ca = prop_to_can_atom (a_prop_of_p_exp e) in
	let ri = lookup_resource env rid in
	let inv = ri.rinv in
	let exfv = ex_fv_can_prop inv in
	let sub = existentials_sub exfv in
	let modif_on_exit = ri.owned ++ (IdSet.inter (fv_norm_can_prop ri.rinv) modified_in_parallel) in
	let body_post = mkst (Cst_fcall (modif_on_exit ,inv,can_prop_empty,"resource exit")) loc
	in [mkst (Cst_wand (and_cprop_catom (sub_can_prop sub inv) ca)) loc]
           @ f s @ [body_post]
    | Pstm_fcall (fid',args) ->
        let fi' = lookup_function env fid' in
        let refprms = fst fi'.param in
	let valprms = snd fi'.param in
	let idrefprms =  List.map create_ident refprms in
        let idvalprms =  List.map create_ident valprms in
        let erefargs = List.map (fun x -> Ce_ident (create_ident x)) (fst args) in
        let evalargs = List.map p_exp_to_can_exp (snd args) in
        let sl_ref = try List.combine idrefprms erefargs
        with Invalid_argument _ ->
          raise (Vcgen_wrong_arg_num ("reference",refprms,erefargs,loc)) in
        let idvalprms' = List.map gensym idvalprms in
	let sl_val = List.combine idvalprms (List.map (fun x -> Ce_ident x) idvalprms') in
	let sub = mk_subst_pairs (sl_ref @ sl_val) in
        let modif_body =
	  let ms = (mvr_body env fi'.body).md -- fi'.locals
	  in sub_idset sub ms in
        let val_eqs =
	  try List.map
            (fun (x,e) -> mk_EQ (e,Ce_ident x))
            (List.combine idvalprms' evalargs)
          with Invalid_argument _ ->
            raise (Vcgen_wrong_arg_num ("value",valprms,evalargs,loc)) in
        let exfv_post = (ex_fv_can_prop fi'.post) -- (ex_fv_can_prop fi'.pre) in
        let sub_ex = existentials_sub exfv_post in
	let sub_locals = mk_gensym_subst_list (IdSet.elements fi'.locals) in
        let post = sub_can_prop sub_ex (sub_can_prop sub (sub_can_prop sub_locals fi'.post)) in
        let pre = sub_can_prop sub fi'.pre
        in [mkst (Cst_wand (Cp_base (val_eqs,[]))) loc;
            mkst (Cst_fcall (modif_body,pre,post,"function call")) loc]
    | Pstm_parallel_fcall (fid1,args1,fid2,args2) ->
	let stm1 = {pstm_desc = Pstm_fcall (fid1,args1); pstm_loc = loc}
	and stm2 = {pstm_desc = Pstm_fcall (fid2,args2); pstm_loc = loc} in
	  match (f stm1, f stm2) with
	    | [{can_st_desc = Cst_wand (Cp_base (val_eqs1,[]))};
               {can_st_desc = Cst_fcall (m1,pre1,post1,_)}],
              [{can_st_desc = Cst_wand (Cp_base (val_eqs2,[]))};
               {can_st_desc = Cst_fcall (m2,pre2,post2,_)}] ->
		let (pre2,post2) =
		  let exfv1 = ex_fv_can_prop pre1
		  and exfv2 = ex_fv_can_prop pre2 in
		    if IdSet.is_empty (IdSet.inter exfv1 exfv2)
		    then (pre2,post2)
		    else
		      let sub2 = mk_gensym_subst_list (IdSet.elements exfv2)
		      in (sub_can_prop sub2 pre2, sub_can_prop sub2 post2)
		in [mkst (Cst_wand (Cp_base (val_eqs1 @ val_eqs2,[]))) loc;
		    mkst (Cst_fcall (m1++m2,can_prop_star pre1 pre2, can_prop_star post1 post2, "parallel call")) loc]
	    | _ -> assert false
  in
  let exfv = ex_fv_can_prop fi.pre in
  let sub = existentials_sub exfv in
  let pre = sub_can_prop sub fi.pre in
  let post = sub_can_prop sub fi.post in
  let pp = (pre, List.flatten (List.map f fi.body), post,"function exit",fi.post_loc)
  in pp::!provisos

let print_error = Error.print

let vcgen iteml =
  Error.report (fun () ->
		  let env = create_env iteml in
		    List.map (fun fi -> (fi.fid, vcgen_fun env fi)) env.functions)
