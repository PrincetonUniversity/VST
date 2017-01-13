open Misc
open Parsetree
open Symbtree
open Inductive_preds
open Format

let split_spatial filter spl =
  let (spl1,spl2) = List.partition (fun x -> filter x <> None) spl
  in match spl1 with
     | pl::spl1' ->
         (match filter pl with Some x -> (x,spl1'@spl2) | None -> assert false)
     | [] -> raise Not_found

let ptsto_filter e = function
  | Csp_pointsto(e',el') when e=e' -> Some (e',el')
  | _ -> None

let using_induction () =
  if !Config.show_induction then
  fprintf !Config.formatter "USING INDUCTION@."

(* base id name for unrolling of predicates *)
let split_id_base = create_ident "split"

(* unroll spatial predicate csp to expose epto|-> *)
let unroll_can_sp pl tags epto csp = match csp with
  | Csp_pointsto (e,_) -> if e=epto then Some [csp] else None
  | Csp_listseg (SINGLE,t1,e1,f1,t2,e2,f2) ->
      if is_uneq pl (e1,f1) && e1=epto
      then
	let split_id = gensym_garb split_id_base in
	let mapf t = (t, Ce_ident (if t=t1 then split_id else gensym_garb (create_ident t))) in
	let cel = List.map mapf tags
	in Some [Csp_pointsto (e1, cel); Csp_listseg (SINGLE,t1, Ce_ident split_id, f1,t2,e2,f2)]
      else None
  | Csp_listseg (k,t1,e1,f1,t2,e2,f2) ->
      if is_uneq pl (e1,f1) && e1=epto  (* unroll from lhs *)
      then
        let split_id = gensym_garb split_id_base in
        let mapf t = (t, if t=t1 then (if k=DOUBLE then Ce_ident(split_id) else Ce_xor(Ce_ident(split_id),e2)) else
                        if (t=t2 && k=DOUBLE) then e2
			else Ce_ident (gensym_garb (create_ident t))) in
        let cel = List.map mapf tags
        in Some [Csp_pointsto (e1, cel); Csp_listseg (k,t1, Ce_ident split_id, f1,t2,e1,f2)]
      else if is_uneq pl (e2,f2) && f2=epto  (* unroll from rhs *)
      then
        let _ = using_induction () in
        let split_id = gensym_garb split_id_base in
        let mapf t = (t, if t=t1 then (if k=DOUBLE then f1 else Ce_xor(Ce_ident(split_id),f1))
		      else if (t=t2 && k=DOUBLE) then Ce_ident(split_id)
		      else Ce_ident (gensym_garb (create_ident t))) in
        let cel = List.map mapf tags
        in Some [Csp_pointsto (f2, cel); Csp_listseg (k,t1,e1,f2,t2,e2,Ce_ident split_id)]
      else None
  | Csp_tree (t1,t2,ce) ->
      if is_uneq pl (Ce_num 0,ce) && ce=epto
      then
	let split_id1 = gensym_garb split_id_base in
	let split_id2 = gensym_garb split_id_base in
	let mapf t = (t, Ce_ident (if t=t1 then split_id1
				   else if t=t2 then split_id2
				   else gensym_garb (create_ident t))) in
	let cel = List.map mapf tags
	in Some [Csp_pointsto (ce, cel); Csp_tree (t1,t2, Ce_ident split_id1); Csp_tree (t1,t2, Ce_ident split_id2)]
      else None
  | Csp_indpred(id,el,cl) ->
      let (guard,newids,body) = instance_ip (id,el,cl) in
      let do_splitting =
        if is_EQ guard
	then
	  let (e1,e2) = un_EQ guard in e1=e2
	else List.mem (neg_can_atom guard) pl
      in if do_splitting then Some body else None

let derive_alloc (pl,sl) = (* list of e known to be allocated *)
  let is_cur_ineq (e,f) = is_uneq pl (e,f) in
  let l = ref [] in
  let f = function
    | Csp_pointsto (e,_) ->
	l := e::!l
    | Csp_listseg(SINGLE,_,e1,f1,_,_,_) ->
        if is_cur_ineq (e1,f1)
        then l := e1::!l
    | Csp_listseg(k,_,e1,f1,_,e2,f2) when k=DOUBLE || k=XOR ->
        if (is_cur_ineq (e1,f1) || is_cur_ineq (e2,f2))
        then l := e1::f2::!l
    | Csp_tree(_,_,e) ->
        if is_cur_ineq (e,Ce_num 0)
        then l := e::!l
    | _ -> ()
  in List.iter f sl;
    !l

let derive_maybe_alloc (pl,sl) = (* pairs (e,f) where e is allocated if e!=f is added *)
  let l = ref [] in
  let f = function
    | Csp_pointsto _ -> ()
    | Csp_listseg(SINGLE,_,e1,f1,_,_,_)  ->
  if e1=f1 || is_uneq pl (e1,f1) then ()
  else l := (e1,f1)::!l
    | Csp_listseg(k,_,e1,f1,_,e2,f2) ->
  if e1=f1 || e2=f2 || is_uneq pl (e1,f1) || is_uneq pl (e2,f2) then ()
  else l := (e1,f1)::(e2,f2)::!l
    | Csp_tree(_,_,e) ->
  if Ce_num 0 = e || is_uneq pl (e,Ce_num 0) then ()
  else l := (e,Ce_num 0)::!l
    | Csp_indpred _  -> ()
  in List.iter f sl;
     !l

let expose_ptsto (pl,sl) tags epto =
  let expose_filter = unroll_can_sp pl tags epto
  in try
      let sl1,sl2 = split_spatial expose_filter sl
      in Some (Cp_base (pl,sl1@sl2))
    with Not_found ->
      let alloc = derive_maybe_alloc (pl,sl)
      in try
	  let (_,f) = List.find (fun (e,f) -> e=epto) alloc
	  in Some (Cp_ifthenelse (mk_EQ (epto,f), Cp_base (pl,sl), Cp_base(pl,sl)))
	with Not_found -> None

let remove_empty_preds pl = (* remove spatial predicates when they're empty *)
  List.filter
    (function
       | Csp_pointsto _ -> true
       | Csp_listseg(k,_,e1,f1,_,e2,f2) -> e1<>f1 || (k<>SINGLE && e2<>f2)
       | Csp_tree(_,_,e) -> e <> Ce_num 0
       | Csp_indpred (id,el,cl) ->
	   let (guard,newids,body) = instance_ip (id,el,cl)
	   in if is_EQ guard
	     then let (e1,e2) = un_EQ guard in e1!=e2
	     else not(List.mem guard pl))

let add_constraints sl =
  let constrs = ref empty_constrs in
  let add c = constrs := add_constr !constrs c in
  let add_basic_constrs () =
    let f = function
      | Csp_listseg(k,_,e1,f1,_,e2,f2) when k=DOUBLE || k=XOR ->
	  begin
	    add ([(e1,f1)],(e2,f2));
	    add ([(e2,f2)],(e1,f1))
	  end
      | _ -> ()
    in List.iter f sl in
  let ptsto_list =
    let f = function
      | Csp_pointsto (e,_) ->
          ([],[e])
      | Csp_listseg(SINGLE,_,e1,f1,_,_,_) ->
          ([(e1,f1)],[e1])
      | Csp_listseg(k,_,e1,f1,_,e2,f2) when k=DOUBLE || k=XOR ->
          ([(e1,f1)],[e1;f2])
      | Csp_tree(_,_,e) ->
          ([(e,Ce_num 0)],[e])
      | _ -> assert false
    in List.map f sl in
  let add_notnil_constrs () =
    let f (ineql,alloc) = List.iter (fun e -> add (ineql,(e,Ce_num 0))) alloc
    in List.iter f ptsto_list in
  let add_star_constrs () =
    let f ((ineql1,alloc1),(ineql2,alloc2)) =
      let ineql = ineql1@ineql2
      in iter_pairs (fun (e1,e2) -> add (ineql,(e1,e2))) alloc1 alloc2
    in iter_pairwise f ptsto_list
  in add_basic_constrs();
     add_notnil_constrs ();
     add_star_constrs ();
     !constrs

(* substitute equalities eq into cf and normalize *)
let apply_equalities eq cf =
  let sub = eq_to_sub eq in
  let (pl,sl) = normalize_can_form (sub_can_form sub cf)
  in (List.stable_sort compare pl, sl)

let apply_equalities_list eq el =
  let sub = eq_to_sub eq
  in List.map (fun e -> normalize_can_exp (sub_can_exp sub e)) el

(* transfer equalities from pl to eq and normalize *)
let update_equalities eq (pl,sl) =
  let (pl1,pl2) = List.partition is_EQ pl in
  let eq' = List.fold_right (fun ca eq -> eq_add eq (un_EQ ca)) pl1 eq in
  let (pl',sl') = apply_equalities eq' (pl2,sl)
  in (eq',pl',sl')

let check_inconsistent (pl,sl) =
  if (List.exists
        (fun p ->
           if is_EQ p then false
           else let (e1,e2) = un_NEQ p in e1=e2)
         pl)    (* e != e *)
  then raise Inconsistent

let normal_form eq (pl,sl) =
  let (eq1,pl1,sl1) = update_equalities eq (pl,sl) in
  let cs = add_constraints sl1 in
(*
  Format.fprintf !Config.formatter "@.@.NORMAL FORM CONSTRAINT START@.";
  pp_constraints !Config.formatter (pl1,cs);
*)
  let (eq2,pl2,cs') =  solve_constraints eq1 pl1 cs in
(*
  Format.fprintf !Config.formatter "@.@.NORMAL FORM CONSTRAINT END@.";
  pp_constraints !Config.formatter (pl2,cs');
*)
  let (pl3,sl2) = apply_equalities eq2 (pl2,sl1) in
  let sl3 = remove_empty_preds pl3 sl2 in
  check_inconsistent (pl3,sl3);
  (eq2,(remove_duplicates pl3,sl3))

let check_atom_entailment ca pl =
  if is_EQ ca then let (e1,e2) = un_EQ ca in e1=e2
  else is_uneq pl (un_NEQ ca)

exception No_frame_found of can_form * can_form

let compare_can_spred csp1 csp2 =
  let lhs = function
    | Csp_listseg (_,_,e,_,_,_,_) -> e
    | Csp_pointsto (e,_) -> e
    | Csp_tree (_,_,e) -> e
    | Csp_indpred _ -> assert false
  in compare (existential_id (lhs csp1),csp1) (existential_id (lhs csp2),csp2)

let (>) cel t =
  try snd(List.find (fun (t',e) -> t'=t) cel)
  with Not_found -> Ce_ident (gensym_garb (create_ident t))

type ctx = {ctx_eq: equalities;
            ctx_inst: (ident * can_exp) list;
      ctx_alloc: can_exp list;
      ctx_maybe_alloc: (can_exp*can_exp) list}

(* finds sl' such that  pl1 ^ sl1 * sl' |- pl2 ^ sl2 *)
let find_frame (eq,inst) ((pl1,sl1) as cf1) ((pl2,sl2) as cf2) tags =
  let sl2 = List.stable_sort compare_can_spred sl2 in
  let _ =
    if !Config.verbose2 then
      fprintf !Config.formatter "Entailment:@.%a@." pp_can_entailment (cf1,cf2) in
  let calc_alloc_and_maybe eq' pl' =
    let sub = eq_to_sub eq' in
    let (pl'',sl1') = sub_can_form sub (pl',sl1) in
    let alloc = derive_alloc (pl'',sl1') in
    let maybe_alloc = derive_maybe_alloc (pl'',sl1')
    in (alloc,maybe_alloc) in
  let rec f_ifthen (eq',inst) cp cf2 =  (* case analysis for ifthenelse *)
    match cp with
      | Cp_base cf ->
          let (eq'',(pl',sl')) =
            try normal_form eq' cf
            with Inconsistent -> assert false in
	  let (pl2',sl2') = apply_equalities eq'' cf2 in
	  let sl2'' = List.stable_sort compare_can_spred sl2' in
	  let (alloc,maybe_alloc) = calc_alloc_and_maybe eq'' pl' in
	  let (cp1,inst1) =
	    f {ctx_eq=eq''; ctx_inst=inst; ctx_alloc=alloc; ctx_maybe_alloc=maybe_alloc} (pl',sl') (pl2',sl2'')
	  in (can_prop_star cp1 (eq_to_can_prop eq''), inst1)
      | Cp_ifthenelse (ca,cp1,cp2) ->
	  let cp' = and_cprop_catom cp1 ca
	  and cp''= and_cprop_catom cp2 (neg_can_atom ca) in
	  let (fr1,inst1) = f_ifthen (eq',inst) cp' cf2 in
	  let (fr2,inst2) = f_ifthen (eq',inst1) cp'' cf2
	  in (Cp_ifthenelse (ca,fr1,fr2),inst2)
      | _ -> assert false
  and f ctx (pl1,sl1) (pl2,sl2) =  (* main subtraction function *)
    let (_,sl1) = normalize_can_form ([],sl1) in
    let (_,sl2) = normalize_can_form ([],sl2) in
    let error () = raise (No_frame_found (cf1,cf2)) in
      if !Config.verbose2 then
	fprintf !Config.formatter "Subtraction Entailment:@.%a@."
	  pp_can_entailment ((pl1,sl1),(pl2,sl2));
      let can_append e = e=(Ce_num 0) || List.mem e ctx.ctx_alloc in
      let try_append e = can_append e || List.exists (fun (e',_) -> e'=e) ctx.ctx_maybe_alloc in
	match sl2 with
	  | [] ->
	      if List.for_all (fun a -> check_atom_entailment a pl1) pl2
	      then (Cp_base ([],sl1),ctx.ctx_inst)
	      else error()
	  | Csp_pointsto(e,el)::sl' ->
	      let record_subset inst el1 el2 =
		let (el1,el2) = (List.sort compare el1, List.sort compare el2) in
		let inst_existential (xe,e') (inst,l) =
		  let x = match xe with | Ce_ident x -> x | _ -> assert false in
		  let sub = mk_single_subst (x,e') in
		  let l' = List.map (fun (t,e) -> (t,sub_can_exp sub e)) l
		  in ((x,e')::inst,l') in
		let rec subset inst = function
		  | (_,[]) -> Some inst
		  | ([],(t2,e2)::l') ->
		      if existential_id e2 then
			let split_id = Ce_ident (gensym_garb (create_ident t2)) in
			let (inst',l'') = inst_existential (e2,split_id) (inst,l')
			in subset inst' ([],l'')
		      else None
		  | (x::l,y::l') when x=y -> subset inst (l,l')
		  | ((t1,e1)::l,(t2,e2)::l') when t1=t2 ->
		      if existential_id e2 then
			let (inst',l'') = inst_existential (e2,e1) (inst,l')
			in subset inst' (l,l'')
		      else None
		  | ((t1,e1)::l,(t2,e2)::l') when t1<>t2 ->
		      subset inst (l,(t2,e2)::l')
		  | _ -> None
		in subset inst (el1,el2)
	      in
		(try let ((_,el'),sl1b) = split_spatial (ptsto_filter e) sl1 in
		   match record_subset ctx.ctx_inst el' el with
		     | Some inst' ->
			 let (pl2',sl'') = sub_can_form (mk_subst_pairs inst') (pl2,sl')
			 in f {ctx with ctx_inst = inst'} (pl1,sl1b) (pl2',sl'')
		     | None -> error()
		 with Not_found ->
		   match expose_ptsto (pl1,sl1) tags e with
		     | Some (Cp_base (_,sl1')) -> f ctx (pl1,sl1') (pl2,sl2)
		     | Some cp  -> f_ifthen (ctx.ctx_eq,ctx.ctx_inst) cp (pl2,sl2)
		     | None -> error())
	  | csp::sl' when List.exists (fun csp' -> can_spred_eq (csp,csp')) sl1 ->  (* frame for ls's and trees *)
	      let (sl1a,sl1b) = List.partition (fun csp' -> can_spred_eq (csp,csp')) sl1
	      in (match sl1a with
		    | _::sl1a' -> f ctx (pl1,(sl1a'@sl1b)) (pl2,sl')
		    | _ -> assert false)
	  | Csp_listseg(SINGLE,_,e1,f1,_,_,_)::sl' when e1=f1 -> f ctx (pl1,sl1) (pl2,sl')
	  | Csp_listseg(_,_,e1,f1,_,e2,f2)::sl' when e1=f1 && e2=f2 -> f ctx (pl1,sl1) (pl2,sl')
	  | Csp_listseg(k,t1,e1,f1,t2,e2,f2)::sl' ->
	      let inst_existentials inst' =
		let sub = mk_subst_pairs inst'
		in sub_can_form sub (pl2,sl2) in
	      let inst_existential (ex,e) ctx' cf =
		let x = (match ex with | Ce_ident x -> x | _ -> assert false) in
		let sub = mk_single_subst (x,e)
		in ({ctx' with ctx_inst = (x,e)::ctx'.ctx_inst}, sub_can_form sub cf) in
	      let rec g = function
		| (sl1a, sp::sl1b) ->
		    let sl1' = sl1a@sl1b in
		      begin match sp with
			| Csp_pointsto(e,cel)
			    when e1=e && (k<>DOUBLE || List.mem (t2,e2) cel)
			      && is_uneq pl1 (e1,f1) && (k=SINGLE || is_uneq pl1 (e2,f2)) ->
			    let e3 = cel>t1
			    in f ctx (pl1,sl1') (pl2,(Csp_listseg (k,t1,(if k=XOR then Ce_xor(e3,e2) else e3),f1,t2,e1,f2)::sl'))
			| Csp_pointsto(e,cel)
			    when e1=e && (k=SINGLE) && existential_id f1 ->
			    let e3 = cel>t1 in
			    let (_,inst') = f ctx (pl1,sl1') (pl2,(Csp_listseg(k,t1,e3,f1,t2,e1,f2)::sl')) in
			    let cf2' = inst_existentials inst'
			    in f ctx (pl1,sl1) cf2'
			| Csp_pointsto(e,cel)  (* |-> on the rhs *)
			    when f2=e && k<>SINGLE && (k<>DOUBLE || List.mem (t1,f1) cel)
			      && is_uneq pl1 (e1,f1) && is_uneq pl1 (e2,f2) ->
			    using_induction ();
				let e3 = cel>(if k=DOUBLE then t2 else t1)
				in f ctx (pl1,sl1') (pl2,(Csp_listseg (k,t1,e1,f2,t2,e2,(if k=XOR then Ce_xor(e3,f1) else e3))::sl'))
			| Csp_listseg(SINGLE,t1',e1',f1',t2',e2',f2')
			    when k=SINGLE && (t1',e1')=(t1,e1) && not(existential_id e1) && existential_id f1 ->
			    let (_,inst') = f ctx (pl1,sl1') (pl2,(Csp_listseg(k,t1,f1',f1,t2,e1,f2)::sl')) in
			    let cf2' = inst_existentials inst'
			    in f ctx (pl1,sl1) cf2'
			| Csp_listseg(k',t1',e1',f1',t2',e2',f2')
			    when (k,t1,e1) = (k',t1',e1') && (k=SINGLE || e2 = e2') && (k<>DOUBLE || t2 = t2')
			      && try_append f1 && (k=SINGLE || try_append e2) ->
			    using_induction ();
				if can_append f1
				then
				  if k=SINGLE || can_append e2
				  then f ctx (pl1,sl1') (pl2,(Csp_listseg(k,t1,f1',f1,t2,f2',f2)::sl'))
				  else
				    begin
				      let (e2,e) = List.find (function (e',_) -> e'=e2) ctx.ctx_maybe_alloc in
					if !Config.show_induction then fprintf !Config.formatter "CASE ANALYSIS on %a=%a@." pp_can_exp e2 pp_can_exp e;
					f_ifthen (ctx.ctx_eq,ctx.ctx_inst) (Cp_ifthenelse (mk_EQ (e2,e),Cp_base (pl1,sl1),Cp_base (pl1,sl1))) (pl2,sl2)
				    end
				else
				  begin
				    let (f1,e) = List.find (function (f',_) -> f'=f1) ctx.ctx_maybe_alloc in
				      if !Config.show_induction then fprintf !Config.formatter "CASE ANALYSIS on %a=%a@." pp_can_exp f1 pp_can_exp e;
				      f_ifthen (ctx.ctx_eq,ctx.ctx_inst) (Cp_ifthenelse (mk_EQ (f1,e),Cp_base (pl1,sl1),Cp_base (pl1,sl1))) (pl2,sl2)
				  end
			| Csp_listseg(XOR,t1',e1',f1',t2',e2',f2')
			    when t2'<>"" ->  (* hack to try both directions once *)
			    (try g (sl1a@[sp],sl1b)
			     with No_frame_found _ ->
			       using_induction ();
			       g (sl1a, Csp_listseg(XOR,t1',f2',e2',"",f1',e1')::sl1b))
			| _ -> g (sl1a@[sp],sl1b)
		      end
		| (sl1a,[]) -> error()
	      in
		if (k=SINGLE) && not (existential_id e1) && existential_id f1
		then
		  try let (ctx',cf2') = inst_existential (f1,e1) ctx (pl2,sl2)
                  in f ctx' (pl1,sl1) cf2'
		  with No_frame_found _ -> g ([],sl1)
		else g ([],sl1)
	  | Csp_indpred (id,el,cl)::sl' ->
	      let (guard,newids,body) = instance_ip (id,el,cl) in
		if (if is_EQ guard then let (e1,e2) = un_EQ guard in e1=e2
		    else List.mem guard pl1)
		then f ctx (pl1,sl1) (pl2,sl')
		else let (sl1a,sl1b) = List.partition (function
							 | Csp_indpred (id1,el1,cl1) -> (id1,el1,cl1) = (id,el,cl)
							 | _ -> false) sl1
		in begin match sl1a with
		  | (Csp_indpred _)::sl1a' -> f ctx (pl1,(sl1a' @ sl1b)) (pl2,sl')
		  | _ -> error()
		end
	  | Csp_tree(_,_,Ce_num 0)::sl' -> f ctx (pl1,sl1) (pl2,sl')
	  | Csp_tree(t1,t2,e)::sl' ->
	      let rec g = function
		| (sl1a, sp::sl1b) ->
		    let sl1' = sl1a@sl1b in
		      begin match sp with
			| Csp_pointsto(e1,cel)
			    when e=e1 &&
			      List.exists (fun (t',_) -> t'=t1) cel &&
			      List.exists (fun (t',_) -> t'=t1) cel ->
			    let (_,e2) = List.find (fun (t',_) -> t'=t1) cel in
			    let (_,e3) = List.find (fun (t',_) -> t'=t2) cel
			    in f ctx (pl1,sl1') (pl2,(Csp_tree(t1,t2,e2)::Csp_tree(t1,t2,e3)::sl'))
			| Csp_tree(t1',t2',e') when (t1,t2,e) = (t1',t2',e') ->
			    f ctx (pl1,sl1') (pl2,sl')
			| _ -> g (sl1a@[sp],sl1b)
		      end
		| (sl1a,[]) -> error()
	      in g ([],sl1) in
  let (alloc,maybe_alloc) = calc_alloc_and_maybe eq pl1 in
  let ctx = {ctx_eq=eq; ctx_inst=inst; ctx_alloc=alloc; ctx_maybe_alloc=maybe_alloc}
  in f ctx (pl1,sl1) (pl2,sl2)

let pp_frame_inferred (loc,cp,inst) =
  if !Config.verbose1 then
    begin
      if cp <> Cp_base([],[])
      then Error.print loc "FRAME inferred:@.@[<hov 2>%a@]@." pp_can_prop cp;
      pp_inst !Config.formatter inst
    end

let (%%) (pl1,sl1) (pl2,sl2) = (pl1@pl2,sl1@sl2)
let (%) (pl,sl) ca = (ca::pl,sl)

(* given f_cf cp converts a check cp |- ... into a number of
   checks cf1 |- ...  cfn |- ...  *)
let map_lhs_can_prop eq f_cf cp =
  let cp = sub_can_prop (eq_to_sub eq) cp in
  let rec f (cpl,cf) = match cpl with
    | [] -> f_cf cf
    | Cp_base cf1::cpl1 -> f (cpl1,(cf %% cf1))
    | Cp_ifthenelse(ca,cp1,cp2)::cpl1 ->
	(try
	   if
	     try eval_can_atom ca
	     with Not_found ->
	       if List.mem ca (fst cf) then true else raise Not_found
	   then f (cp1::cpl1,cf)
	   else f (cp2::cpl1,cf)
	 with Not_found ->
           (f (cp1::cpl1,(cf % ca))); (f (cp2::cpl1,(cf % neg_can_atom ca))))
    | Cp_star (cp1,cp2)::cpl1 ->
        f (cp1::cp2::cpl1,cf)
  in f ([cp],([],[]))

(* given f_cf cf cp converts a check cf|-cp into a number of
   checks cf|-cf1  cf|-cfn  *)
let map_rhs_can_prop eq ?(rebuild=fun inst ca x y -> (x,inst)) f_cf cf1 cp =
  let cp = sub_can_prop (eq_to_sub eq) cp in
  let rec f inst cf1 (cpl,cf2) =
    match cpl with
      | [] -> f_cf inst cf1 cf2
      | Cp_base cf2'::cpl' -> f inst cf1 (cpl',cf2 %% cf2')
      | Cp_ifthenelse (ca,cp1,cp2)::cpl' ->
	  (try
	     if
	       try eval_can_atom ca
	       with Not_found ->
		 if List.mem ca (fst cf1) then true else raise Not_found
	     then f inst cf1 (cp1::cpl',cf2)
	     else f inst cf1 (cp2::cpl',cf2)
	   with Not_found ->
	     let r =
	       try Some (f inst (cf1 % ca) (cp1::cpl',cf2))
	       with Inconsistent -> None
	     in match r with
	       | Some (x,inst1) ->
		   (try
		      let y,inst2 = f inst1 (cf1 % (neg_can_atom ca)) (cp2::cpl',cf2)
		      in rebuild inst2 ca x y
		    with Inconsistent -> (x,inst1))
	       | None -> f inst (cf1 % (neg_can_atom ca)) (cp2::cpl',cf2))
      | Cp_star (cp1,cp2)::cpl' ->
	  f inst cf1 (cp1::cp2::cpl',cf2)
  in f [] cf1 ([cp],([],[]))

let rec check_entailment eq (cp1,c,cp2,s,loc) tags =
  let (eq,cp1) = kill_garbage_vars (eq,cp1) in
  (if !Config.all_states then
     let cur_com_loc = match c with
       |  {can_st_loc = loc1}::_ -> loc1
       | _ -> loc
     in Error.print cur_com_loc "Intermediate State:@.%a@." pp_entailment
	  (can_prop_star (eq_to_can_prop eq) cp1,c,cp2,s,loc));
  let f_cf cf =
    let nf = try Some (normal_form eq cf)
    with Inconsistent ->
      (if !Config.verbose2 then
         fprintf !Config.formatter "Inconsistent: %a@." pp_can_form cf;
       None) in
      match nf with
	| Some (eq1,cf1) -> check_ent eq1 (cf1,c,cp2,s,loc) tags
	| None -> ()
  in map_lhs_can_prop eq f_cf cp1

and check_ent eq2 ((pl2,sl2),c,post,s,loc) tags =
  let heap_error loc' pp =
    Error.print loc' "ERROR: %a in %a@." pp () pp_can_form (pl2,sl2);
    raise Error.Symb_exe_heap_error in
  let sub = eq_to_sub eq2 in
  let sub_e = sub_can_exp sub in
    match c with
      | [] ->
	  (match post with
	     | Cp_base cf ->
		 let (pl3,sl3) = apply_equalities eq2 cf in
		   (try let (fr,inst) = find_frame (eq2,[]) (pl2, sl2) (pl3, sl3) tags in
		      if not (is_can_prop_empty fr)
		      then raise (Error.Symb_exe_entail ((pl2,sl2),(pl3,sl3),s,loc));
		      pp_inst !Config.formatter inst
		    with No_frame_found (cf1,cf2) -> raise (Error.Symb_exe_entail ((pl2,sl2),(pl3,sl3),s,loc)))
	     | _ ->
		 let f_cf inst cf1 cf2 = (check_entailment eq2 (Cp_base cf1,[],Cp_base cf2,s,loc) tags,inst)
		 in fst (map_rhs_can_prop eq2 f_cf (pl2,sl2) post))
      | {can_st_desc=Cst_ifthenelse (ca,c1,c2)}::c3 ->
	  let ca' = sub_can_atom sub ca in
	  let cf1 = ((ca'::pl2),sl2)
	  and cf2 = (((neg_can_atom ca')::pl2),sl2)
	  in (check_entailment eq2 (Cp_base cf1,c1@c3,post,s,loc) tags);
	    (check_entailment eq2 (Cp_base cf2,c2@c3,post,s,loc) tags)
      | {can_st_desc=Cst_assign (x,e)}::c1 ->
	  let e = sub_e e in
	  let sub = mk_gensym_garb_subst x in
	  let e' = sub_can_exp sub e
	  and cf' = sub_can_form sub (pl2,sl2) in
	  let eq' = sub_equalities sub eq2 in
	    check_entailment (eq_add eq' (Ce_ident x, e')) (Cp_base cf',c1,post,s,loc) tags
      | {can_st_desc=Cst_fldlookup (x,e,t);can_st_loc=loc'}::c1 ->
	  let lookup t cel =
            try (cel, snd (List.find (fun (t',e) -> t'=t) cel))
            with Not_found ->
              let dummye = Ce_ident (gensym_garb (create_ident "dummy"))
              in ((t,dummye)::cel, dummye)  in
	  let e = sub_e e in
	    (match expose_ptsto (pl2,sl2) tags e with
	       | Some (Cp_base (_,sl2)) ->
		   let ((_,cel),sl2b) =
		     try  split_spatial (ptsto_filter e) sl2
		     with Not_found -> assert false in
		   let (cel',f) = lookup t cel in
		   let sl3 = Csp_pointsto(e,cel')::sl2b in
		   let sub = mk_gensym_garb_subst x in
		   let f' = sub_can_exp sub f
		   and cf' = sub_can_form sub (pl2,sl3) in
		   let eq2' = sub_equalities sub eq2
		   in check_entailment (eq_add eq2' (Ce_ident x,f')) (Cp_base cf',c1,post,s,loc) tags
	       | Some cp -> check_entailment eq2 (cp,c,post,s,loc) tags
	       | None ->heap_error loc' (fun fmt () -> fprintf fmt "lookup %a->%s" pp_can_exp e t))
      | {can_st_desc=Cst_fldassign (ce1,t,ce2);can_st_loc=loc'}::c1 ->
	  let mutate cel t f =
	    if List.exists (fun (t',e) -> t=t') cel
	    then List.map (fun (t',e) -> (t', if t=t' then f else e)) cel
	    else (t,f)::cel  in
	  let (ce1,ce2) = (sub_e ce1, sub_e ce2) in
	    (match expose_ptsto (pl2,sl2) tags ce1 with
	       | Some (Cp_base (_,sl2)) ->
		   let ((_,cel),sl2b) =
		     try  split_spatial (ptsto_filter ce1) sl2
		     with Not_found -> assert false in
		   let cel' = mutate cel t ce2
		   in check_entailment eq2 (Cp_base (pl2, Csp_pointsto(ce1,cel')::sl2b),c1,post,s,loc) tags
	       | Some cp -> check_entailment eq2 (cp,c,post,s,loc) tags
	       | None -> heap_error loc' (fun fmt () -> fprintf fmt "assign %a->%s" pp_can_exp ce1 t))
      | {can_st_desc=Cst_new(x)}::c1 ->
	  let ex = Ce_ident x in
	  let cel = List.map (fun t -> (t,Ce_num 0)) tags in
	  let sub = mk_gensym_garb_subst x in
	  let (pl2',sl2') = sub_can_form sub (pl2,sl2) in
	  let eq2' = sub_equalities sub eq2
	  in check_entailment eq2' (Cp_base (pl2',Csp_pointsto(ex,cel)::sl2'),c1,post,s,loc) tags
      | {can_st_desc=Cst_dispose(e);can_st_loc=loc'}::c1 ->
	  let ce = sub_e e in
	    (match expose_ptsto (pl2,sl2) tags ce with
	       | Some (Cp_base (_,sl2)) ->
		   let (_,sl2b) =
		     try  split_spatial (ptsto_filter ce) sl2
		     with Not_found -> assert false
		   in  check_entailment eq2 (Cp_base (pl2,sl2b),c1,post,s,loc) tags
	       | Some cp -> check_entailment eq2 (cp,c,post,s,loc) tags
	       | None -> heap_error loc' (fun fmt () -> fprintf fmt "dispose %a" pp_can_exp ce))
      | {can_st_desc=Cst_fcall (modif,cp1,cp2,s'); can_st_loc=loc1}::c1 ->
	  (try
	     let (fr,inst) =
	       let rebuild inst ca cpx cpy = (Cp_ifthenelse (ca,cpx,cpy),inst) in
	       let f_cf inst cf1 cf2 =
		 let (eq2',cf1') = normal_form eq2 cf1 in
		 let cf2' = apply_equalities eq2' cf2 in
		   try find_frame (eq2',inst) cf1' cf2' tags
		   with  No_frame_found _ -> raise (Error.Symb_exe_noframe (cf1,cf2,s',loc1))
	       in map_rhs_can_prop ~rebuild:rebuild eq2 f_cf (pl2,sl2) cp1 in
	     let sub = mk_gensym_garb_subst_list (IdSet.elements modif)
	     in
	       pp_frame_inferred (loc,fr,inst);
	       let eq2' = sub_equalities sub eq2 in
	       let fr' = sub_can_prop sub (Cp_star (Cp_base (pl2,[]),fr)) in
	       let inst' = List.map (fun (x,e) -> (x, sub_can_exp sub e)) inst in
	       let sub_inst = mk_subst_pairs inst' in
	       let cp2inst = sub_can_prop sub_inst cp2
	       in check_entailment eq2' (Cp_star (fr',cp2inst),c1,post,s,loc) tags
	   with Inconsistent -> ())
      | {can_st_desc=Cst_wand cp; can_st_loc=loc1}::c1 ->
	  check_entailment eq2 (can_prop_star cp (Cp_base (pl2,sl2)), c1,post,s,loc) tags

let check_prop ent tags =
  if !Config.verbose1 then
    fprintf !Config.formatter "@.VERIFICATION CONDITION:@.%a@." pp_entailment ent;
  Error.report
    ~nonfatal_thunk:(fun () -> false)
    (fun () -> check_entailment empty_eq ent tags; true)
