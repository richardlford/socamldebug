(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Jerome Vouillon, projet Cristal, INRIA Rocquencourt          *)
(*           OCaml port by John Malecki and Xavier Leroy                  *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Handling of symbol tables (globals and events) *)

open Instruct
open Debugger_config (* Toplevel *)
open Program_loading
open Debugcom
open Events
module String = Misc.Stdlib.String
open Format

(* List of directories to act as workspace roots. *)
let workspace_roots = ref String.Set.empty

let workspace_marker = "/workspace_root"
let workspace_marker_slash = "/workspace_root/"

let workspace_marker_len = String.length workspace_marker
let build_re = Str.regexp {|\(.*\)/_build/.*|}

(* We only try to map workspace roots if the marker does not exists. *)
let do_workspace_map = not (Sys.file_exists workspace_marker)

let add_workspace_root filename  =
  if do_workspace_map then begin
    let the_realfile = Soc_compat.realpath filename in
    if Str.string_match build_re the_realfile 0 then begin
      let root = Str.matched_group 1 the_realfile in
      printf "Adding %s to workspace roots@." root;
      workspace_roots := String.Set.add root !workspace_roots
    end
  end
    
let has_workspace_marker dir_name =
  (dir_name = workspace_marker) ||
   Soc_compat.starts_with ~prefix: workspace_marker_slash dir_name

(* Because we might have multiple workspace roots, a single
   filename might expand into multiple filenames. *)
let expand_workspace_root dir_name =
  if not (has_workspace_marker dir_name) then [dir_name]
  else begin
    let stem = String.sub dir_name workspace_marker_len 
              (String.length dir_name - workspace_marker_len) in
    List.map (fun root -> root ^ stem) (String.Set.elements !workspace_roots)
  end

let modules =
  ref ([] : string list)

let program_source_dirs =
  ref ([] : string list)

let functions =
  ref ([] : string list)

let events_by_pc =
  (Hashtbl.create 257 : (pc, debug_event) Hashtbl.t)
let events_by_module =
  (Hashtbl.create 17 : (string, int * debug_event array) Hashtbl.t)
let all_events_by_module =
  (Hashtbl.create 17 : (string, int * debug_event list) Hashtbl.t)
let events_by_function =
  (Hashtbl.create 17 : (string, int * debug_event array) Hashtbl.t)

let start_pc_by_function =
  (Hashtbl.create 17 : (string, pc list ref) Hashtbl.t)

let exported_items_by_module =
  (Hashtbl.create 17 : (string, int * string array) Hashtbl.t)

let partition_modules evl =
  let rec partition_modules' ev evl =
    match evl with
      [] -> [ev],[]
    | ev'::evl ->
       let evl,evll = partition_modules' ev' evl in
       if ev.ev_module = ev'.ev_module then ev::evl,evll else [ev],evl::evll
  in
  match evl with
    [] -> []
  | ev::evl -> let evl,evll = partition_modules' ev evl in evl::evll

let relocate_event orig ev =
  ev.ev_pos <- orig + ev.ev_pos;
  match ev.ev_repr with
    Event_parent repr -> repr := ev.ev_pos
  | _                 -> ()

let read_symbols' bytecode_file =
  add_workspace_root bytecode_file;
  let ic = open_in_bin bytecode_file in
  begin try
    Bytesections.read_toc ic;
    ignore(Bytesections.seek_section ic "SYMB");
  with Bytesections.Bad_magic_number | Not_found ->
    prerr_string bytecode_file; prerr_endline " is not a bytecode file.";
    raise Toplevel
  end;
  Symtable.restore_state (input_value ic);
  begin try
    ignore (Bytesections.seek_section ic "DBUG")
  with Not_found ->
    prerr_string bytecode_file; prerr_endline " has no debugging info.";
    raise Toplevel
  end;
  let num_eventlists = input_binary_int ic in
  let dirs = ref String.Set.empty in
  let eventlists = ref [] in
  for _i = 1 to num_eventlists do
    let orig = input_binary_int ic in
    let evl = (input_value ic : debug_event list) in
    (* Relocate events in event list *)
    List.iter (relocate_event orig) evl;
    let evll = partition_modules evl in
    eventlists := evll @ !eventlists;
    let dirlist = (input_value ic : string list) in
    dirs :=
      List.fold_left 
      (fun s e -> 
        let expanded_dirs = expand_workspace_root e in
        List.fold_left (fun s d -> String.Set.add d s)  s expanded_dirs)
      !dirs dirlist
  done;
  !eventlists, !dirs, ic

let clear_symbols () =
  modules := [];
  program_source_dirs := [];
  Hashtbl.clear events_by_pc; Hashtbl.clear events_by_module;
  Hashtbl.clear all_events_by_module;
  functions := [];
  Hashtbl.clear start_pc_by_function; Hashtbl.clear exported_items_by_module

let print_evl evl =
    List.iteri (fun i ev -> 
      printf "ev[%d]=" i; 
      Sdumper.print_event ev
      ) evl

let print_functions () =
  printf "@[<2>{Function starts:@ ";
  List.iter (fun fname -> 
    let pcs = Hashtbl.find start_pc_by_function fname in
      printf "@[{Func: %s:@ " fname;
      List.iteri (fun i {frag;pos} -> 
        printf "startpc[%i]%d:%d(%d)@ " i frag pos (pos/4)
        ) !pcs;
      printf "}@]@.";
    ) !functions;
  printf "}@]@."

let print_exports () =
  printf "{Module exports;@.";
  List.iter (fun md ->
    try 
      begin
        let (frag, exports) = Hashtbl.find exported_items_by_module md in
        printf "@[<2>{frag=%d, mod=%s, exports:@ " frag md;
        for i = 0 to (Array.length exports - 1) do
          printf "%i:%s@ " i exports.(i)
        done;
        printf "}@]@.";
      end
    with Not_found -> 
      printf "Module %s not found@." md
    ) !modules;
  printf "}@."

let add_functions frag evl =
  (* 
  printf "add_functions, frag=%d, events:@." frag;
  print_evl evl;
  *)
  List.iter (fun ev ->
    let md = ev.ev_module in
    let fname = ev.ev_defname in
    let flen = String.length fname in
    if fname = "??" then begin
      if ev.ev_kind = Event_pseudo then begin
        if ev.ev_stacksize > 0 then
          let stack = Sdumper.get_stack ev in
          if Array.length stack > 0 then
            Hashtbl.add exported_items_by_module md (frag, stack);
      end
    end else if flen > 5 && String.sub fname (flen - 5) 5 = "(fun)" then begin
      (* Skip anonymous functions and operators *)
      ()
    end else begin
      if (ev.ev_kind = Event_before || ev.ev_kind=Event_pseudo) && 
          ev.ev_info=Event_function then begin
        let pc = {frag; pos=ev.ev_pos } in
        (* Start of new function *)
        if Hashtbl.mem start_pc_by_function fname then begin
          let prior = Hashtbl.find start_pc_by_function fname in
          prior := pc :: !prior
        end else
          Hashtbl.add start_pc_by_function fname (ref [pc])
      end
    end
    ) evl
  
let fill_unique_simple_names () =
  let short_to_long = 
    (Hashtbl.create 257 : (string, string list ref ) Hashtbl.t) in
  Hashtbl.iter (fun fname entry -> 
    let last_dot_opt = String.rindex_opt fname '.' in
    match last_dot_opt with
    | None -> ()
    | Some ld -> 
      let sname = String.sub fname (ld + 1) (String.length fname - ld - 1) in
      if Hashtbl.mem short_to_long sname then
        let entry = Hashtbl.find short_to_long sname in
        entry := fname :: !entry
      else
        Hashtbl.add short_to_long sname (ref [fname])
    ) start_pc_by_function;

  (* Now see which simple names are unique. *)
  Hashtbl.iter (fun sname entry ->
    match !entry with
    | [fname] -> (* it is unique *)
      let entry = Hashtbl.find start_pc_by_function fname in
      Hashtbl.add start_pc_by_function sname entry
    | _ -> () (* Not unique *)
    ) short_to_long

let add_symbols frag all_events =
  List.iter
    (fun evl ->
      List.iter
        (fun ev ->
          Hashtbl.add events_by_pc {frag; pos = ev.ev_pos} ev)
        evl)
    all_events;

  List.iter
    (function
        [] -> ()
      | ev :: _ as evl ->
          let md = ev.ev_module in
          let cmp ev1 ev2 = compare (Events.get_pos ev1).Lexing.pos_cnum
                                    (Events.get_pos ev2).Lexing.pos_cnum
          in
          let sorted_evl = List.sort cmp evl in
          add_functions frag sorted_evl;
          modules := md :: !modules;
          Hashtbl.add all_events_by_module md (frag, sorted_evl);
          let real_evl =
            List.filter
              (function
                 {ev_kind = Event_pseudo} -> false
               | _                        -> true)
              sorted_evl
          in
          Hashtbl.add events_by_module md (frag, Array.of_list real_evl))
    all_events;
  fill_unique_simple_names ();
  Hashtbl.iter (fun fname v ->
    functions := fname :: !functions;
    ) start_pc_by_function;
  functions := List.sort compare !functions;
  modules := List.rev !modules
  (*
  print_functions ();
  print_exports ()
  
  *)
  
let read_symbols frag bytecode_file =
  let all_events, all_dirs, ic = read_symbols' bytecode_file in
  program_source_dirs := !program_source_dirs @ (String.Set.elements all_dirs);
  add_symbols frag all_events;
  ic

let erase_symbols frag =
  let pcs = Hashtbl.fold (fun pc _ pcs ->
      if pc.frag = frag then pc :: pcs else pcs)
    events_by_pc []
  in
  List.iter (Hashtbl.remove events_by_pc) pcs;

  let mds = Hashtbl.fold (fun md (frag', _) mds ->
      if frag' = frag then md :: mds else mds)
    events_by_module []
  in
  List.iter (Hashtbl.remove events_by_module) mds;
  List.iter (Hashtbl.remove all_events_by_module) mds;
  modules := List.filter (fun md -> not (List.mem md mds)) !modules

let code_fragments () =
  let frags =
    Hashtbl.fold
      (fun _ (frag, _) l -> frag :: l)
      all_events_by_module []
  in
  List.sort_uniq compare frags

let modules_in_code_fragment frag' =
  Hashtbl.fold (fun md (frag, _) l ->
      if frag' = frag then md :: l else l)
    all_events_by_module []

let any_event_at_pc pc =
  { ev_frag = pc.frag; ev_ev = Hashtbl.find events_by_pc pc }

let event_at_pc pc =
  match any_event_at_pc pc with
    { ev_ev = { ev_kind = Event_pseudo } } -> raise Not_found
  | ev -> ev

let set_event_at_pc pc =
 try ignore(event_at_pc pc); set_event pc
 with Not_found -> ()

(* List all events in module *)
let events_in_module mdle =
  try
    Hashtbl.find all_events_by_module mdle
  with Not_found ->
    0, []

(* Binary search of event at or just after char *)
let find_event ev char =
  let rec bsearch lo hi =
    if lo >= hi then begin
      if (Events.get_pos ev.(hi)).Lexing.pos_cnum < char
      then raise Not_found
      else hi
    end else begin
      let pivot = (lo + hi) / 2 in
      let e = ev.(pivot) in
      if char <= (Events.get_pos e).Lexing.pos_cnum
      then bsearch lo pivot
      else bsearch (pivot + 1) hi
    end
  in
  if Array.length ev = 0 then
    raise Not_found
  else
    bsearch 0 (Array.length ev - 1)

(* Return first event after the given position. *)
(* Raise [Not_found] if module is unknown or no event is found. *)
let event_at_pos md char =
  let ev_frag, ev = Hashtbl.find events_by_module md in
  { ev_frag; ev_ev = ev.(find_event ev char) }

(* Return event closest to given position *)
(* Raise [Not_found] if module is unknown or no event is found. *)
let event_near_pos md char =
  let ev_frag, ev = Hashtbl.find events_by_module md in
  try
    let pos = find_event ev char in
    (* Desired event is either ev.(pos) or ev.(pos - 1),
       whichever is closest *)
    if pos > 0 && char - (Events.get_pos ev.(pos - 1)).Lexing.pos_cnum
                  <= (Events.get_pos ev.(pos)).Lexing.pos_cnum - char
    then { ev_frag; ev_ev = ev.(pos - 1) }
    else { ev_frag; ev_ev = ev.(pos) }
  with Not_found ->
    let pos = Array.length ev - 1 in
    if pos < 0 then raise Not_found;
    { ev_frag; ev_ev = ev.(pos) }

(* Flip "event" bit on all instructions *)
let set_all_events frag =
  Hashtbl.iter
    (fun pc ev ->
       match ev.ev_kind with
         Event_pseudo -> ()
       | _ when pc.frag = frag -> set_event pc
       | _ -> ())
    events_by_pc

(* Previous `pc'. *)
(* Save time if `update_current_event' is called *)
(* several times at the same point. *)
let old_pc = ref (None : pc option)

(* Recompute the current event *)
let update_current_event () =
  match Checkpoints.current_pc () with
    None ->
      Events.current_event := None;
      old_pc := None
  | (Some pc) as opt_pc when opt_pc <> !old_pc ->
      Events.current_event :=
        begin try
          Some (event_at_pc pc)
        with Not_found ->
          None
        end;
      old_pc := opt_pc
  | _ ->
      ()
