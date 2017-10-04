open StdLabels
open GMain

let file_dialog ~title ~callback ?filename () =
  let sel =
    GWindow.file_selection ~title ~modal:true ?filename () in
    sel#cancel_button#connect#clicked ~callback:sel#destroy;
    sel#ok_button#connect#clicked ~callback:
      begin fun () ->
	let name = sel#get_filename in
	  sel#destroy ();
	  callback name
      end;
    sel#show ()

let font_dialog ~title ~callback () =
  let sel =
    GWindow.font_selection_dialog ~title ~modal:true () in
    sel#cancel_button#connect#clicked ~callback:sel#destroy;
    sel#ok_button#connect#clicked ~callback:
      begin fun () ->
	let font = sel#selection#font in
	  sel#destroy ();
	  callback font
      end;
    sel#show ()

class results ?packing ?show () = object (self)
  val text = GEdit.text ~editable:false ?packing ?show ()

  method text = text

  method formatter =
    let out s pos len = text#insert (String.sub s ~pos ~len)
    and flush () = ()
    in Format.make_formatter out flush

  method reset () = text#freeze ();
    text#delete_text ~start:0 ~stop:text#length;
    text#thaw ()
end

class editor ?packing ?show () = object (self)
  val text = GEdit.text ~editable:true ?packing ?show ()
  val mutable filename = None

  method text = text

  method load_file name =
    try
      let ic = open_in name in
	filename <- Some name;
	text#freeze ();
	text#delete_text ~start:0 ~stop:text#length;
	let buf = String.create 1024 and len = ref 0 in
	  while len := input ic buf 0 1024; !len > 0 do
	    if !len = 1024 then text#insert buf
	    else text#insert (String.sub buf ~pos:0 ~len:!len)
	  done;
	  text#set_point 0;
	  text#thaw ();
	  close_in ic
    with _ -> ()

  method open_file () = file_dialog ~title:"Open" ~callback:self#load_file ()

  method save_dialog () =
    file_dialog ~title:"Save" ?filename
      ~callback:(fun file -> self#output ~file) ()

  method save_file () =
    match filename with
	Some file -> self#output ~file
      | None -> self#save_dialog ()

  method output ~file =
    try
      if Sys.file_exists file then Sys.rename file (file ^ "~");
      let oc = open_out file in
	output_string oc (text#get_chars ~start:0 ~stop:text#length);
	close_out oc;
	filename <- Some file
    with _ -> prerr_endline "Save failed"
end

let window = GWindow.window ~width:500 ~height:300 ~title:"Smallfoot" ()
(* let _ = GtkBase.Widget.add_events window#as_widget [`ALL_EVENTS] *)
let vbox = GPack.vbox ~packing:window#add ()

let menubar = GMenu.menu_bar ~packing:vbox#pack ()
let factory = new GMenu.factory menubar
let accel_group = factory#accel_group
let file_menu = factory#add_submenu "File"
let edit_menu = factory#add_submenu "Edit"

let hbox1 = GPack.hbox ~packing:vbox#add ()
let editor = new editor ~packing:hbox1#add ()
let vscrollbar1 = GRange.scrollbar `VERTICAL ~packing:hbox1#pack ()
let lbl = GMisc.label ~packing:vbox#pack ()
let button = GButton.button ~label:"Verify" ~packing:vbox#pack ()
let hbox2 = GPack.hbox ~packing:vbox#add ()
let results = new results ~packing:hbox2#add ()
let vscrollbar2 = GRange.scrollbar `VERTICAL ~packing:hbox2#pack ()

let counter = new GUtil.variable 0

let change_font = function
  | Some font ->
      let style = window#misc#style#copy
      in style#set_font font;
	editor#text#freeze ();
	editor#text#misc#set_style style;
	editor#text#thaw ();
	results#text#freeze ();
	results#text#misc#set_style style;
	results#text#thaw ();
  | None -> ()

let select_font () = font_dialog ~title:"Open" ~callback:change_font ()

open GdkKeysyms

let _ =
  window#connect#destroy ~callback:Main.quit;
  let factory = new GMenu.factory file_menu ~accel_group in
    factory#add_item "Open..." ~key:_O ~callback:editor#open_file;
    factory#add_item "Save" ~key:_S ~callback:editor#save_file;
    factory#add_item "Save as..." ~callback:editor#save_dialog;
    factory#add_separator ();
    factory#add_item "Font..." ~key:_F ~callback:select_font;
    factory#add_separator ();
    factory#add_item "Quit" ~key:_Q ~callback:window#destroy;
    let factory = new GMenu.factory edit_menu ~accel_group in
      factory#add_item "Copy" ~key:_C ~callback:editor#text#copy_clipboard;
      factory#add_item "Cut" ~key:_X ~callback:editor#text#cut_clipboard;
      factory#add_item "Paste" ~key:_V ~callback:editor#text#paste_clipboard;
      factory#add_separator ();
      factory#add_check_item "Word wrap" ~active:false
	~callback:editor#text#set_word_wrap;
      factory#add_check_item "Read only" ~active:false
	~callback:(fun b -> editor#text#set_editable (not b));
      window#add_accel_group accel_group;
      editor#text#event#add [`KEY_RELEASE];
      editor#text#event#connect#any
	~callback:(fun ev -> counter#set editor#text#position; false);
      counter#connect#changed ~callback:(fun n -> lbl#set_text ("position: " ^ (string_of_int n)));
      editor#text#event#connect#button_press
	~callback:(fun ev ->
		     let button = GdkEvent.Button.button ev in
		       if button = 3 then begin
			 file_menu#popup ~button ~time:(GdkEvent.Button.time ev); true
		       end else false);
      editor#text#set_line_wrap false;
      editor#text#set_vadjustment vscrollbar1#adjustment;
      results#text#set_vadjustment vscrollbar2#adjustment;;


let g () = try () with e -> raise e;;


(* Connection between gui and backend *)
let fmt = results#formatter
and n = ref 0
and anon_arg_func fname =
  editor#load_file fname
in
  button#connect#clicked ~callback:
    (fun () ->
       results#reset ();
       let s = editor#text#get_chars ~start:0 ~stop:editor#text#length
       in results#text#freeze ();
       Toplevel.verify_wp_string s;
       results#text#thaw ()
    );
  Arg.parse Config.speclist anon_arg_func Config.usage_msg;
  Config.formatter := fmt;
  Format.pp_set_margin fmt !Config.columns;
  Format.pp_set_max_boxes fmt max_int;
  window#show ();
  Main.main ()
