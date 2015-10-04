let _ =
  let anon_arg_func fname =
    let fmt = !Config.formatter in
    let cols = !Config.columns in
      begin
	Format.pp_set_margin fmt cols;
	Format.pp_set_max_boxes fmt max_int;
	if !Config.verbose1
	then Format.fprintf fmt "@.File %s@." fname;
	Toplevel.verify_wp_fname fname !Config.verbose1;
	if Config.print_gc_stats then Gc.print_stat stdout
      end in
    Arg.parse Config.speclist anon_arg_func Config.usage_msg
