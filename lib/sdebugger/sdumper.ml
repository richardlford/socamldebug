open Format
open Asttypes
open Lambda
let comp_env_filter_flag = ref true

let print_float f =
  if String.contains f '.'
  then printf "%s" f
  else printf "%s." f
;;

let rec print_struct_const ppf = function
    Const_base(Const_int i) -> fprintf ppf "%d" i
  | Const_base(Const_float f) -> print_float f
  | Const_base(Const_string (s, _, _)) -> fprintf ppf "%S" s
  | Const_immstring s -> fprintf ppf "%S" s
  | Const_base(Const_char c) -> fprintf ppf "%C" c
  | Const_base(Const_int32 i) -> fprintf ppf "%ldl" i
  | Const_base(Const_nativeint i) -> fprintf ppf "%ndn" i
  | Const_base(Const_int64 i) -> fprintf ppf "%LdL" i
  | Const_block(tag, args) ->
      fprintf ppf "<%d>" tag;
      begin match args with
        [] -> ()
      | [a1] ->
          fprintf ppf "("; print_struct_const ppf a1; fprintf ppf ")"
      | a1::al ->
          fprintf ppf "("; print_struct_const ppf a1;
          List.iter (fun a -> fprintf ppf ", "; print_struct_const ppf a) al;
          fprintf ppf ")"
      end
  | Const_float_array a ->
      fprintf ppf "[|";
      List.iter (fun f -> print_float f; fprintf ppf "; ") a;
      fprintf ppf "|]"

(* Print an obj *)

let same_custom x y =
  Obj.field x 0 = Obj.field (Obj.repr y) 0

let rec print_obj ppf x =
  if Obj.is_block x then begin
    let tag = Obj.tag x in
    if tag = Obj.string_tag then
        fprintf ppf "%S" (Obj.magic x : string)
    else if tag = Obj.double_tag then
        fprintf ppf "%.12g" (Obj.magic x : float)
    else if tag = Obj.double_array_tag then begin
        let a = (Obj.magic x : floatarray) in
        fprintf ppf "[|";
        for i = 0 to Array.Floatarray.length a - 1 do
          if i > 0 then fprintf ppf ", ";
          fprintf ppf "%.12g" (Array.Floatarray.get a i)
        done;
        fprintf ppf "|]"
    end else if tag = Obj.custom_tag && same_custom x 0l then
        fprintf ppf "%ldl" (Obj.magic x : int32)
    else if tag = Obj.custom_tag && same_custom x 0n then
        fprintf ppf "%ndn" (Obj.magic x : nativeint)
    else if tag = Obj.custom_tag && same_custom x 0L then
        fprintf ppf "%LdL" (Obj.magic x : int64)
    else if tag < Obj.no_scan_tag then begin
        fprintf ppf "<%d>" (Obj.tag x);
        match Obj.size x with
          0 -> ()
        | 1 ->
            fprintf ppf "("; print_obj ppf (Obj.field x 0); fprintf ppf ")"
        | n ->
            fprintf ppf "("; print_obj ppf (Obj.field x 0);
            for i = 1 to n - 1 do
              fprintf ppf ", "; print_obj ppf (Obj.field x i)
            done;
            fprintf ppf ")"
    end else
        fprintf ppf "<tag %d>" tag
  end else
    fprintf ppf "%d" (Obj.magic x : int)

    let kind_string ev =
    (match ev.Instruct.ev_kind with
      Event_before   -> "before"
    | Event_after _  -> "after"
    | Event_pseudo   -> "pseudo")

let info_string ev =
  (match ev.Instruct.ev_info with
      Event_function -> "/fun"
    | Event_return _ -> "/ret"
    | Event_other    -> "")

let repr_string ev =
  (match ev.Instruct.ev_repr with
    Event_none        -> ""
  | Event_parent _    -> "(repr)"
  | Event_child repr  -> Int.to_string !repr)

let get_env ev = 
  Envaux.env_from_summary ev.Instruct.ev_typenv

let in_comp_env (ev: Instruct.debug_event) (id: Ident.t) =
  if not !comp_env_filter_flag then true else begin
    let ce : Instruct.compilation_env = ev.ev_compenv in
    let stack : int Ident.tbl = ce.ce_stack in
    let heap : int Ident.tbl = ce.ce_heap in
    let recs : int Ident.tbl = ce.ce_rec in
    try ignore (Ident.find_same id stack); true;
    with Not_found -> 
    try ignore (Ident.find_same id heap); true;
    with Not_found -> 
    try ignore (Ident.find_same id recs); true;
    with Not_found -> false
end

let print_summary_id title id = 
  printf " %s: " title;
  Ident.print_with_scope std_formatter id;
  printf  ";@ "

let print_summary_string title s =
  printf " %s: %s@ " title s

let next_summary summary =
      match summary with
      | Env.Env_empty -> None
      | Env_value (s, id, vd) -> Some s
      | Env_type (s, id, td) -> Some s
      | Env_extension (s, id, ec) -> Some s
      | Env_module (s, id, mp, md) -> Some s
      | Env_modtype (s, id, md) -> Some s
      | Env_class (s, id, cd) -> Some s
      | Env_cltype (s, id, ctd) -> Some s
      | Env_open (s, p) -> Some s
      | Env_functor_arg (s, id) -> Some s
      | Env_constraints (s, cstrs) -> Some s
      | Env_copy_types s -> Some s
      | Env_persistent (s, id) -> Some s
      | Env_value_unbound (s, n, r) -> Some s
      | Env_module_unbound (s, n, r) -> Some s

let print_value_desc (vd: Types.value_description) =
  printf "@[{";
  printf "val_type=@ ";
  Printtyp.raw_type_expr std_formatter vd.val_type;
  ignore vd.val_kind;
  ignore vd.val_loc;
  ignore vd.val_attributes;
  ignore vd.val_uid;
  printf "}@]"

      (*
    let ls = ev.ev_loc.loc_start in
    let le = ev.ev_loc.loc_end in
    printf "ev_loc={File \"%s\", line %d, characters %d-%d},@ " ls.Lexing.pos_fname
      ls.Lexing.pos_lnum (ls.Lexing.pos_cnum - ls.Lexing.pos_bol)
      (le.Lexing.pos_cnum - ls.Lexing.pos_bol);
      *)

let myprint_loc (loc: Location.t)  =
    let ls = loc.loc_start in
    let filename = ls.pos_fname in
    if filename <> "_none_" then begin
      Location.print_loc std_formatter loc;
    end

let print_summary_item ev summary =
  match summary with
  | Env.Env_empty ->
      () (*print_summary_string "Env_empty" "" *)
  | Env_value (s, id, vd) ->
    if not (in_comp_env ev id) then ()
    else begin
      let loc = vd.val_loc in
      printf "@[<hov 2>";
      (* print_summary_id "Env_value" id; *)
      let buf = Buffer.create 100 in
      let ppf = Format.formatter_of_buffer buf in
      Printtyp.value_description id ppf vd;
      fprintf ppf "@?" ;
      let bcontent = Buffer.contents buf in
      printf "%s;@ " bcontent;
      myprint_loc loc;
      let num_atts = List.length vd.val_attributes in
      if num_atts > 0 then begin
        printf ",@ ";
        printf "#atts=%d@ " num_atts
      end;
      printf "@]@;"
  end
  | Env_type (s, id, td) ->
    if not !comp_env_filter_flag then begin
      let loc = td.type_loc in
      printf "@[<hov 2>";
      (* print_summary_id "Env_type" id; *)
      Printtyp.type_declaration id std_formatter td;
      myprint_loc loc;
      printf "@]@;";
    end
  | Env_extension (s, id, ec) ->
    if not !comp_env_filter_flag then begin
      let loc = ec.ext_loc in
      printf "@[<hov 2>";
      (* print_summary_id "Env_extension" id; *)
      Printtyp.extension_constructor id std_formatter ec;
      myprint_loc ec.ext_loc;
      printf "@]@;";
    end
  | Env_module (s, id, mp, md) ->
      if not !comp_env_filter_flag then
        print_summary_id "Env_module" id;
  | Env_modtype (s, id, md) ->
      print_summary_id "Env_modtype" id;
      Printtyp.modtype_declaration id std_formatter md
  | Env_class (s, id, cd) ->
      print_summary_id "Env_class" id
  | Env_cltype (s, id, ctd) ->
      print_summary_id "Env_cltype" id
  | Env_open (s, p) ->
      if not !comp_env_filter_flag then
        print_summary_string "Env_open" (Path.name p)
  | Env_functor_arg (s, id) ->
      print_summary_id "Env_functor_arg" id
  | Env_constraints (s, cstrs) ->
      print_summary_string "Env_constraints" "cstrs"
  | Env_copy_types s ->
      print_summary_string "Env_copy_types" ""
  | Env_persistent (s, id) ->
      print_summary_id "Env_persistent" id
  | Env.Env_value_unbound (s, n, r) ->
      if not !comp_env_filter_flag then begin
        print_summary_string "Env_value_unbound" 
        (String.concat " " [n; "reason"])
      end
  | Env_module_unbound (s, n, r) ->
      if not !comp_env_filter_flag then begin
        print_summary_string "Env_module_unbound" 
        (String.concat " " [n; "reason"])
      end

let rec print_summary ev summary =
  print_summary_item ev summary;
  match next_summary summary with
  | None -> ()
  | Some s -> print_summary ev s

let print_ident_tbl  (title: string) (tbl: int Ident.tbl) =
  if tbl = Ident.empty then begin
    printf "%s = empty@ " title
  end else begin
    printf "@[<2>%s {@ " title;
    Ident.iter (fun id idval -> 
      printf "%s=%d@ " (Ident.name id) idval
      ) tbl;
    printf "}@ @]";
  end
  
(* 
type compilation_env =
  { ce_stack: int Ident.tbl; (* Positions of variables in the stack *)
    ce_heap: int Ident.tbl;  (* Structure of the heap-allocated env *)
    ce_rec: int Ident.tbl }  (* Functions bound by the same let rec *)
   
*)
let print_comp_env (ce : Instruct.compilation_env) =
  let stack : int Ident.tbl = ce.ce_stack in
  let heap : int Ident.tbl = ce.ce_heap in
  let recs : int Ident.tbl = ce.ce_rec in
  if stack = Ident.empty && 
     heap = Ident.empty &&
     recs = Ident.empty 
  then () 
  else begin 
    printf "@[<2>ev_compenv{@ ";
    print_ident_tbl "ce_stack" stack;
    print_ident_tbl "ce_heap" heap;
    print_ident_tbl "ce_rec" recs;
    printf "}@ @]";
  end

  (* From typing/subst.ml 
    type type_replacement =
      | Path of Path.t
      | Type_function of { params : type_expr list; body : type_expr }

    type t =
      { types: type_replacement Path.Map.t;
        modules: Path.t Path.Map.t;
        modtypes: module_type Path.Map.t;
        for_saving: bool;
        loc: Location.t option;
      }
  *)
  let print_subst title (ts: Subst.t) =
    if ts = Subst.identity then begin
      (* printf "%s is empty substitution,@ " title *)
      ()
    end else begin
      (* Unfortunately, the substitution is not made available *)
      printf "{%s is non-empty (but opaque) substitution},@ " title
    end

(* If there is a non-trivial substitution, get the summary of the
   substituted environment. *)
let get_substituted_summary (ev: Instruct.debug_event) =
  let summary = ev.ev_typenv in
  let subst = ev.ev_typsubst in
  if subst = Subst.identity then
    (* No substitution *)
    summary
  else begin
    let env2 = Envaux.env_from_summary summary subst in
    let summary2 = Env.summary env2 in
    summary2
  end
  

(* From instruct.mli 

type debug_event =
  { mutable ev_pos: int;                (* Position in bytecode *)
    ev_module: string;                  (* Name of defining module *)
    ev_loc: Location.t;                 (* Location in source file *)
    ev_kind: debug_event_kind;          (* Before/after event *)
    ev_defname: string;                 (* Enclosing definition *)
    ev_info: debug_event_info;          (* Extra information *)
    ev_typenv: Env.summary;             (* Typing environment *)
    ev_typsubst: Subst.t;               (* Substitution over types *)
    ev_compenv: compilation_env;        (* Compilation environment *)
    ev_stacksize: int;                  (* Size of stack frame *)
    ev_repr: debug_event_repr }         (* Position of the representative *)

*)

let print_ev (ev: Instruct.debug_event) =
  printf "pc=%d(=4*%d),@ " ev.Instruct.ev_pos (ev.Instruct.ev_pos/4 );
  printf "ev_module=%s@ " ev.Instruct.ev_module;
  myprint_loc ev.ev_loc;
  printf ",@ ev_kind=%s,@ " (kind_string ev);
  printf "ev_defname=%s,@ " ev.ev_defname;
  printf "ev_info=%s,@ " (info_string ev);
  printf "ev_typenv={@;@[";
  print_summary ev (get_substituted_summary ev);
  printf "}@;@]@.";
  print_comp_env ev.ev_compenv;
  print_subst "ev_typsubst" ev.ev_typsubst;
  printf "ev_stacksize=%d,@ " ev.ev_stacksize;
  printf "ev_repr=%s,@ " (repr_string ev);
  printf "@."
