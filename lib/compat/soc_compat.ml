[%%if ocaml_version < (4,13,0)]
  let starts_with ~prefix s =
    let re = Str.regexp_string prefix in
    try
      ignore (Str.search_forward re s 0);
      true
    with Not_found -> false
[%%else]
  let starts_with ~prefix s =
    String.starts_with ~prefix s
[%%endif]

[%%if ocaml_version < (4,13,0)]
  let realpath fname =
    if Filename.is_relative fname then
      Sys.getcwd() ^ "/" ^ fname
    else
      fname

[%%else]
let realpath = Unix.realpath
[%%endif]

[%%if ocaml_version < (5,0,0)]
let load_path_init = Load_path.init
[%%else]
let load_path_init path = 
  Load_path.reset();
  List.iter Load_path.add_dir (List.rev path)
  
[%%endif]

[%%if ocaml_version < (4,13,0)]
  let int64_max (x: Int64.t) (y: Int64.t) =
    if x >= y then x else y 
[%%else]
  let int64_max = Int64.max
[%%endif]

[%%if ocaml_version < (4,13,0)]
  let int_max (x: Int.t) (y: Int.t) =
    if x >= y then x else y 
[%%else]
  let int_max = Int.max
[%%endif]

[%%if ocaml_version < (4,14,0)]
  let types_get_desc ty = (Ctype.repr ty).desc
[%%else]
  let types_get_desc = Types.get_desc
[%%endif]

(* Save the following as a template*)
[%%if ocaml_version < (4,13,0)]
[%%else]
[%%endif]
