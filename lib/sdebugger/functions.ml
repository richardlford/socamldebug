open Format
open Debugcom
open Opcodes
open Opnames
open Program_loading
open Sdumper

(* Debug options*)
let print_description_flag = ref true
let pc_by_function = (Hashtbl.create 257 : (string, pc) Hashtbl.t)

(* Read signed and unsigned integers *)

let inputu ic =
  let b1 = input_byte ic in
  let b2 = input_byte ic in
  let b3 = input_byte ic in
  let b4 = input_byte ic in
  (b4 lsl 24) + (b3 lsl 16) + (b2 lsl 8) + b1

let inputs ic =
  let b1 = input_byte ic in
  let b2 = input_byte ic in
  let b3 = input_byte ic in
  let b4 = input_byte ic in
  let b4' = if b4 >= 128 then b4-256 else b4 in
  (b4' lsl 24) + (b3 lsl 16) + (b2 lsl 8) + b1

let start = ref 0

type global_table_entry =
    Empty
  | Global of Ident.t
  | Constant of Obj.t

let globals = ref ([||] : global_table_entry array) (* Global map *)
let primitives = ref ([||] : string array)     (* Table of primitives *)

let read_primitive_table ic len =
  let p = really_input_string ic len in
  String.split_on_char '\000' p |> List.filter ((<>) "") |> Array.of_list

let print_global item =
  match item with
    Global id -> print_string (Ident.name id)
  | Constant obj -> print_obj obj
  | _ -> print_string "???"

let print_getglobal_name ic =
  begin
    let n = inputu ic in
    if n >= Array.length !globals || n < 0
    then print_string "<global table overflow>"
    else print_global !globals.(n) 
  end

let print_getglobal_name' n =
begin
  if n >= Array.length !globals || n < 0
  then print_string "<global table overflow>"
  else print_global !globals.(n) 
end

let print_setglobal_name ic =
  let n = inputu ic in
  if n >= Array.length !globals || n < 0
  then print_string "<global table overflow>"
  else match !globals.(n) with
          Global id -> print_string (Ident.name id)
        | _ -> print_string "???"

let print_setglobal_name' n =
  if n >= Array.length !globals || n < 0
  then print_string "<global table overflow>"
  else match !globals.(n) with
          Global id -> print_string (Ident.name id)
        | _ -> print_string "???"

let print_primitive ic =
  let n = inputu ic in
  if n >= Array.length !primitives || n < 0
  then print_int n
  else print_string !primitives.(n)

let print_primitive' n =
  if n >= Array.length !primitives || n < 0
  then print_int n
  else print_string !primitives.(n)

  let currpos ic =
  pos_in ic - !start

let currpc ic =
  currpos ic / 4

type shape =
| Nothing
| Uint
| Sint
| Uint_Uint
| Disp
| Uint_Disp
| Sint_Disp
| Getglobal
| Getglobal_Uint
| Setglobal
| Primitive
| Uint_Primitive
| Switch
| Closurerec
| Pubmet


type shape_val =
| Sv_Nothing
| Sv_Uint of int
| Sv_Sint of int
| Sv_Uint_Uint of int * int
| Sv_Disp of int
| Sv_Uint_Disp of int * int
| Sv_Sint_Disp of int * int
| Sv_Getglobal of int
| Sv_Getglobal_Uint of int * int
| Sv_Setglobal of int
| Sv_Primitive of int
| Sv_Uint_Primitive of int * int
| Sv_Switch of int * int * int list * int list
| Sv_Closurerec of int * int * int list
| Sv_Pubmet of int * int

(* Shape and description of each opcode *)
let op_info = [
  opACC0, (Nothing, "accu = sp[0]");
  opACC1, (Nothing, "accu = sp[1]");
  opACC2, (Nothing, "accu = sp[2]");
  opACC3, (Nothing, "accu = sp[3]");
  opACC4, (Nothing, "accu = sp[4]");
  opACC5, (Nothing, "accu = sp[5]");
  opACC6, (Nothing, "accu = sp[6]");
  opACC7, (Nothing, "accu = sp[7]");
  opACC, (Uint, "n=> accu = sp[n]");
  opPUSH, (Nothing, "push accu");
  opPUSHACC0, (Nothing, "push accu; accu = sp[0]");
  opPUSHACC1, (Nothing, "push accu; accu = sp[1]");
  opPUSHACC2, (Nothing, "push accu; accu = sp[2]");
  opPUSHACC3, (Nothing, "push accu; accu = sp[3]");
  opPUSHACC4, (Nothing, "push accu; accu = sp[4]");
  opPUSHACC5, (Nothing, "push accu; accu = sp[5]");
  opPUSHACC6, (Nothing, "push accu; accu = sp[6]");
  opPUSHACC7, (Nothing, "push accu; accu = sp[7]");
  opPUSHACC, (Uint, "n=> push accu; accu = sp[n]");
  opPOP, (Uint, "n=> pop  items from the stack");
  opASSIGN, (Uint, "n=> sp[n] = accu; accu = ()");
  opENVACC1, (Nothing, "accu = env(1)");
  opENVACC2, (Nothing, "accu = env(2)");
  opENVACC3, (Nothing, "accu = env(3)");
  opENVACC4, (Nothing, "accu = env(4)");
  opENVACC, (Uint, "n=> accu = env(n)");
  opPUSHENVACC1, (Nothing, "push accu; accu = env(1)");
  opPUSHENVACC2, (Nothing, "push accu; accu = env(2)");
  opPUSHENVACC3, (Nothing, "push accu; accu = env(3)");
  opPUSHENVACC4, (Nothing, "push accu; accu = env(4)");
  opPUSHENVACC, (Uint, "push accu; accu = env(*pc++)");
  opPUSH_RETADDR, (Disp, "n=> push pc+n; push env; push extra_args");
  opAPPLY, (Uint, "n=> extra_args = n - 1; pc = Code_val(accu); env = accu;");
  opAPPLY1, (Nothing, "arg1 = pop; push extra_args, env, pc, arg1; pc = Code_val(accu); env = accu; extra_args = 0");
  opAPPLY2, (Nothing, "arg1,arg2 = pops; push extra_args, env, pc, arg2, arg1; pc = Code_val(accu); env = accu; extra_args = 1");
  opAPPLY3, (Nothing, "arg1,arg2,arg3 = pops; push extra_args, env, pc, arg3, arg2, arg1; pc = Code_val(accu); env = accu; extra_args = 2");
  opAPPTERM, (Uint_Uint, "n,s=> sp[0..s-1]=sp[0..n-1];pc = Code_val(accu); env = accu; extra_args += n-1");
  opAPPTERM1, (Uint, "n=> arg1=pop;pop n-1 items; push arg1;pc = Code_val(accu); env = accu");
  opAPPTERM2, (Uint, "n=> arg1,arg2=pops;pop n-2 items; push arg2,arg1;pc = Code_val(accu); env = accu;extra_args++");
  opAPPTERM3, (Uint, "n=> arg1,arg2,arg3=pops;pop n-3 items; push arg3,arg2,arg1;pc = Code_val(accu); env = accu;extra_args+=2");
  opRETURN, (Uint, "n=> pop n elements; if(extra_args> 0){extra_args--;pc=Code_val(accu);env = accu}else{pc,env,extra_args=pops}");
  opRESTART, (Nothing, "n=size(env);push env(n-1..3);env=env(2);extra_args+=n-3");
  opGRAB, (Uint, "n=> if(extra_args>=n){extra_args-=n}else{m=1+extra_args;accu=closure with m args, field2=env,code=pc-3, args popped}");
  opCLOSURE, (Uint_Disp, "n,ofs=> if(n>0){push accu};accu=closure of n+1 elements;Code_val(acc)=pc+ofs;arity=0;env offset=2");
  opCLOSUREREC, (Closurerec, "nvar,[f...]=> accu=closure for f0 and Infix closures for f1..., all sharing the nvars from accu and stack;push closures");
  opOFFSETCLOSUREM3, (Nothing, "accu=&env[-3]");
  opOFFSETCLOSURE0, (Nothing, "accu=env");
  opOFFSETCLOSURE3, (Nothing, "accu=*env[3]");
  opOFFSETCLOSURE, (Sint, "n=> accu=&env[n]");  (* was Uint *)
  opPUSHOFFSETCLOSUREM3, (Nothing, "push accu;accu=&env[-3]");
  opPUSHOFFSETCLOSURE0, (Nothing, "push accu;accu=env");
  opPUSHOFFSETCLOSURE3, (Nothing, "push accu;accu=*env[3]");
  opPUSHOFFSETCLOSURE, (Sint, "n=> push accu;accu=&env[n]"); (* was Nothing *)
  opGETGLOBAL, (Getglobal, "n=> accu=global[n]");
  opPUSHGETGLOBAL, (Getglobal, "n=> push accu; accu=global[n]");
  opGETGLOBALFIELD, (Getglobal_Uint, "n,p=> accu=global[n][p]");
  opPUSHGETGLOBALFIELD, (Getglobal_Uint, "n,p=> push accu;accu=global[n][p]");
  opSETGLOBAL, (Setglobal, "n=> global[n]=accu; accu=()");
  opATOM0, (Nothing, "accu = Atom(0)");
  opATOM, (Uint, "n=> accu = Atom(n)");
  opPUSHATOM0, (Nothing, "push accu; accu = Atom(0)");
  opPUSHATOM, (Uint, "n=> push accu; accu = Atom(n)");
  opMAKEBLOCK, (Uint_Uint, "n,t=> accu=n-element block with tag t, elements from accu and popped stack");
  opMAKEBLOCK1, (Uint, "t=> accu=1-element block, tag t, element from accu");
  opMAKEBLOCK2, (Uint, "t=> accu=2-element block, tag t, elements from accu and pop");
  opMAKEBLOCK3, (Uint, "t=> accu=3-element block, tag t, elements from accu and popped stack");
  opMAKEFLOATBLOCK, (Uint, "n=> n-element float block, elements from accu and popped stack");
  opGETFIELD0, (Nothing, "accu = accu[0]");
  opGETFIELD1, (Nothing, "accu = accu[1]");
  opGETFIELD2, (Nothing, "accu = accu[2]");
  opGETFIELD3, (Nothing, "accu = accu[3]");
  opGETFIELD, (Uint, "n=> accu = accu[n]");
  opGETFLOATFIELD, (Uint, "n=> accu=Double Block with DoubleField(accu, n)");
  opSETFIELD0, (Nothing, "accu[0] = pop; accu=()");
  opSETFIELD1, (Nothing, "accu[1] = pop; accu=()");
  opSETFIELD2, (Nothing, "accu[2] = pop; accu=()");
  opSETFIELD3, (Nothing, "accu[3] = pop; accu=()");
  opSETFIELD, (Uint, "n=> accu[n] = pop; accu=()");
  opSETFLOATFIELD, (Uint, "DoubleField(accu, n) = pop; accu=()");
  opVECTLENGTH, (Nothing, "accu = size of block in accu (/2 if Double array)");
  opGETVECTITEM, (Nothing, "n=pop; accu=accu[n]");
  opSETVECTITEM, (Nothing, "n=pop;v=pop;accu[n]=v");
  opGETSTRINGCHAR, (Nothing, "n=pop; accu = nth unsigned char of accu string");
  opGETBYTESCHAR, (Nothing, "n=pop; accu = nth unsigned char of accu string");
  opSETBYTESCHAR, (Nothing, "n=pop;v=pop; nth unsigned char of accu set to v");
  opBRANCH, (Disp, "ofs=> pc += ofs");
  opBRANCHIF, (Disp, "ofs=> if(accu != false){pc += ofs}");
  opBRANCHIFNOT, (Disp, "ofs=> if(accu == false){pc += ofs}");
  opSWITCH, (Switch, "n=> tab=pc;szt=n>>16;szl=n&0xffff;if(Is_block(accu)){ix=Tag_val(accu);pc += tab[szl+ix]}else{pc += tab[accu]");
  opBOOLNOT, (Nothing, "accu = not accu");
  opPUSHTRAP, (Disp, "ofs=> push extra_args, env, trap_sp_offset, pc+ofs");
  opPOPTRAP, (Nothing, "pop;trap_sp_offset=pop;pop;pop");
  opRAISE, (Nothing, "if(no frame){stop}else{sp=trapsp;pop pc,trapsp,env,extra_args}");
  opCHECK_SIGNALS, (Nothing, "Handle signals, if any. accu not preserved.");
  opC_CALL1, (Primitive, "p=> accu=primitive(p)(accu)");
  opC_CALL2, (Primitive, "p=> accu=primitive(p)(accu, pop)");
  opC_CALL3, (Primitive, "p=> accu=primitive(p)(accu, pop, pop)");
  opC_CALL4, (Primitive, "p=> accu=primitive(p)(accu, pop, pop, pop)");
  opC_CALL5, (Primitive, "p=> accu=primitive(p)(accu, pop, pop, pop, pop)");
  opC_CALLN, (Uint_Primitive, "n,p=> accu=primitive(p)(accu, (n-1)-pops");
  opCONST0, (Nothing, "accu = 0");
  opCONST1, (Nothing, "accu = 1");
  opCONST2, (Nothing, "accu = 2");
  opCONST3, (Nothing, "accu = 3");
  opCONSTINT, (Sint, "n=> accu = n");
  opPUSHCONST0, (Nothing, "push accu; accu = 0");
  opPUSHCONST1, (Nothing, "push accu; accu = 1");
  opPUSHCONST2, (Nothing, "push accu; accu = 2");
  opPUSHCONST3, (Nothing, "push accu; accu = 3");
  opPUSHCONSTINT, (Sint, "n=> push accu; accu = n");
  opNEGINT, (Nothing, "accu = -accu");
  opADDINT, (Nothing, "accu = accu + pop");
  opSUBINT, (Nothing, "accu = accu - pop");
  opMULINT, (Nothing, "accu = accu * pop");
  opDIVINT, (Nothing, "accu = accu / pop.");
  opMODINT, (Nothing, "accu = accu % pop");
  opANDINT, (Nothing, "accu = accu & pop");
  opORINT, (Nothing, "accu = accu | pop");
  opXORINT, (Nothing, "accu = accu ^ pop");
  opLSLINT, (Nothing, "accu = accu << pop");
  opLSRINT, (Nothing, "accu = (unsigned)accu >> pop");
  opASRINT, (Nothing, "accu = (signed)accu >> pop ");
  opEQ, (Nothing, "accu = accu == pop");
  opNEQ, (Nothing, "accu = accu != pop");
  opLTINT, (Nothing, "accu = accu < pop");
  opLEINT, (Nothing, "accu = accu <= pop");
  opGTINT, (Nothing, "accu = accu > pop");
  opGEINT, (Nothing, "accu = accu >= pop");
  opOFFSETINT, (Sint, "ofs=> accu += ofs");
  opOFFSETREF, (Sint, "ofs=> accu[0] += ofs");
  opISINT, (Nothing, "accu = Val_long(accu & 1)");
  opGETMETHOD, (Nothing, "x=pop;y=x[0];accu = y[accu]");
  opGETDYNMET, (Nothing, "object=sp[0];accu=method matching tag in object's method table");
  opGETPUBMET, (Pubmet, "tag,cache=> object=accu;methods=object[0];push object;accu=method matching tag in methods;");
  opBEQ, (Sint_Disp, "val,ofs=> val == (signed)accu){pc += ofs}");
  opBNEQ, (Sint_Disp, "val,ofs=> if(val != (signed)accu){pc += ofs}");
  opBLTINT, (Sint_Disp, "val,ofs=> if(val < (signed)accu){pc += ofs}");
  opBLEINT, (Sint_Disp, "val,ofs=> if(val <= (signed)accu){pc += ofs}");
  opBGTINT, (Sint_Disp, "val,ofs=> if(val > (signed)accu){pc += ofs}");
  opBGEINT, (Sint_Disp, "val,ofs=> if(val >= (signed)accu){pc += ofs}");
  opULTINT, (Nothing, "accu < (unsigned)pop");
  opUGEINT, (Nothing, "accu >= (unsigned)pop");
  opBULTINT, (Uint_Disp, "val,ofs=> if(val < (unsigned)accu){pc += ofs}");
  opBUGEINT, (Uint_Disp, "val,ofs=> if(val >= (unsigned)accu){pc += ofs}");
  opSTOP, (Nothing, "Stop interpreting, return accu");
  opEVENT, (Nothing, "if(--caml_event_count==0){send event message to debugger}");
  opBREAK, (Nothing, "Send break message to debugger");
  opRERAISE, (Nothing, "Like Raise, but backtrace slightly different");
  opRAISE_NOTRACE, (Nothing, "Raise but do not record backtrace.");
];;

type parsed_instr =
  { pi_opcode: int;
    pi_pc: pc;
    pi_ev: Events.code_event option;
    pi_shape: shape;
    pi_descr: string option;
    pi_payload: shape_val
  }

let parse_instr  frag ic : parsed_instr =
  let pos = currpos ic in 
  let pc = { frag; pos } in
  let code_ev =
    try Some (Symbols.any_event_at_pc pc)
    with
    | Not_found -> None in
  let op = inputu ic in
  let info = List.assoc op op_info in
  let shape = fst info in
  let descr = snd info in
  (* Setup default result *)
  let result = 
    { pi_opcode = op;
      pi_pc = pc;
      pi_ev = code_ev;
      pi_shape = shape;
      pi_descr = Some descr;
      pi_payload = Sv_Nothing;
    } in

  match shape with
  | Uint -> { result with pi_payload= Sv_Uint (inputu ic) } 
  | Sint -> { result with pi_payload= Sv_Sint (inputu ic) } 
  | Uint_Uint -> 
      {result with pi_payload= Sv_Uint_Uint((inputu ic), (inputu ic)) }
  | Disp -> let p = currpc ic in 
      {result with pi_payload= Sv_Disp (p + inputs ic) }
  | Uint_Disp ->
      let u = (inputu ic) in
      let p = currpc ic in 
      {result with pi_payload= Sv_Uint_Disp  (u, p + inputs ic) }
  | Sint_Disp ->
      let s = (inputs ic) in
      let p = currpc ic in 
      {result with pi_payload= Sv_Sint_Disp  (s, p + inputs ic) }
  | Getglobal -> { result with pi_payload= Sv_Getglobal (inputu ic) } 
  | Getglobal_Uint ->
      {result with pi_payload= Sv_Getglobal_Uint((inputu ic), (inputu ic)) }
  | Setglobal -> { result with pi_payload= Sv_Setglobal (inputu ic) } 
  | Primitive -> { result with pi_payload= Sv_Primitive (inputu ic) } 
  | Uint_Primitive ->
      {result with pi_payload= Sv_Uint_Primitive((inputu ic), (inputu ic)) }
  | Switch ->
        let n = inputu ic in
        let orig = currpc ic in
        (* Switch does case analysis on either a "long", i.e. an iteger, or
           over the tag of a block. The switch is for an inductive type that
           may have a mix of simple element and elements with data.
           The simple elements are longs, and the others are blocks, with
           the tag telling which alternative. *)
        let size_longs = (n land 0xFFFF) in
        let size_tags = (n lsr 16) in
        (* Longs list comes first *)
        let longs_list = ref ([]: int list) in
        for i = 0 to size_longs - 1 do
          longs_list := (orig + inputs ic) :: !longs_list;
        done;
        let tags_list = ref ([]: int list) in
        for i = 0 to size_tags - 1 do
          tags_list := (orig + inputs ic) :: !tags_list;
        done;
        {result with pi_payload=
          Sv_Switch (size_longs, size_tags, List.rev !longs_list, List.rev !tags_list) }
  | Closurerec ->
        let nfuncs = inputu ic in
        let nvars = inputu ic in
        let orig = currpc ic in
        let funl = ref ([]: int list) in
        for _i = 0 to nfuncs - 1 do
          funl := (orig + inputs ic) :: !funl
        done;
        {result with pi_payload=
         Sv_Closurerec (nfuncs, nvars, List.rev !funl)
          }
  | Pubmet -> 
        let tag = inputs ic in
        let _cache = inputu ic in
        {result with pi_payload= Sv_Pubmet (tag, _cache) }
  | Nothing -> result

type inst_outcome =
| Ino_continue 
| Ino_seek of int (* Seek to new position in file *)
| Ino_done
  ;;

let print_parsed_instr  index (inst: parsed_instr) : inst_outcome =
  printf "%8d  " (inst.pi_pc.pos / 4);
  let op = inst.pi_opcode in
  begin 
    if op >= Array.length Opnames.names_of_instructions || op < 0
    then (print_string "*** unknown opcode : "; print_int op)
     else print_string names_of_instructions.(op);
  end;
  begin
    if inst.pi_shape <> Nothing then print_string " ";
    match inst.pi_payload with
    | Sv_Uint u1 -> print_int u1
    | Sv_Sint s1 -> print_int s1
    | Sv_Uint_Uint (u1, u2)
       -> print_int u1; print_string ", "; print_int u2
    | Sv_Disp d -> print_int d
    | Sv_Uint_Disp (u, d)
       -> print_int u; print_string ", ";
          print_int d
    | Sv_Sint_Disp (s, d)
       -> print_int s; print_string ", ";
          print_int d
    | Sv_Getglobal g -> print_getglobal_name' g
    | Sv_Getglobal_Uint (g, u)
       -> print_getglobal_name' g; print_string ", "; print_int u
    | Sv_Setglobal g -> print_setglobal_name' g
    | Sv_Primitive p -> print_primitive' p
    | Sv_Uint_Primitive (u, p)
       -> print_int u; print_string ", "; print_primitive' p
    | Sv_Switch (size_longs, size_tags, longs_list, tags_list) ->
          List.iteri (fun i target ->
            printf "@.        int "; print_int i; print_string " -> ";
            print_int target
          ) longs_list;

          List.iteri (fun i target ->
            printf "@.        tag "; print_int i; print_string " -> ";
            print_int target
          ) longs_list;
    | Sv_Closurerec (nfuncs, nvars, funs) ->
          print_int nvars;
          List.iter (fun func -> 
            print_string ", ";
            print_int func;
            ) funs
    | Sv_Pubmet (tag, cache) ->
          print_int tag
    | Sv_Nothing -> ();
  end;
  printf "@.";
  begin
  match inst.pi_ev with
  | None -> ()
  | Some {ev_frag; ev_ev} -> print_event ev_ev;  printf "@.";
  end;
  Ino_continue

  (* Function combining reading and printing an instruction *)
let direct_print_inst  frag ic =
  let pos = currpos ic in 
  let pc = { frag; pos } in
  match Symbols.any_event_at_pc pc with
  | code_ev -> 
    let ev = code_ev.ev_ev in
    print_ev ev;
  | exception Not_found -> ();
  let descr = ref "" in
  printf "%8d  " (pos / 4);
  let op = inputu ic in
  if op >= Array.length Opnames.names_of_instructions || op < 0
  then (print_string "*** unknown opcode : "; print_int op)
  else print_string names_of_instructions.(op);
  begin try
    let info = List.assoc op op_info in
    let shape = fst info in
    descr := snd info;
    begin
    if shape <> Nothing then print_string " ";
    match shape with
    | Uint -> print_int (inputu ic)
    | Sint -> print_int (inputs ic)
    | Uint_Uint
       -> print_int (inputu ic); print_string ", "; print_int (inputu ic)
    | Disp -> let p = currpc ic in print_int (p + inputs ic)
    | Uint_Disp
       -> print_int (inputu ic); print_string ", ";
          let p = currpc ic in print_int (p + inputs ic)
    | Sint_Disp
       -> print_int (inputs ic); print_string ", ";
          let p = currpc ic in print_int (p + inputs ic)
    | Getglobal -> print_getglobal_name ic
    | Getglobal_Uint
       -> print_getglobal_name ic; print_string ", "; print_int (inputu ic)
    | Setglobal -> print_setglobal_name ic
    | Primitive -> print_primitive ic
    | Uint_Primitive
       -> print_int (inputu ic); print_string ", "; print_primitive ic
    | Switch
       -> let n = inputu ic in
          let orig = currpc ic in
          for i = 0 to (n land 0xFFFF) - 1 do
            printf "@.        int "; print_int i; print_string " -> ";
            print_int (orig + inputs ic);
          done;
          for i = 0 to (n lsr 16) - 1 do
            printf "@.        tag "; print_int i; print_string " -> ";
            print_int (orig + inputs ic);
          done;
    | Closurerec
       -> let nfuncs = inputu ic in
          let nvars = inputu ic in
          let orig = currpc ic in
          print_int nvars;
          for _i = 0 to nfuncs - 1 do
            print_string ", ";
            print_int (orig + inputs ic);
          done;
    | Pubmet
       -> let tag = inputs ic in
          let _cache = inputu ic in
          print_int tag
    | Nothing -> ();
    end;
  with Not_found -> print_string " (unknown arguments)"
  end;
  printf "@."

let start_positions = ref ([] : int list)
let missing_start_positions = ref ([] : int list)


let find_start_pos_in_instr index (inst: parsed_instr) : inst_outcome =
  let op = inst.pi_opcode in
  begin
  match inst.pi_payload with
  | Sv_Uint_Disp (u, disp) when op = opCLOSURE -> 
    start_positions := disp :: !start_positions
  |  Sv_Closurerec (nfuncs, nvars, funs) when op = opCLOSUREREC ->
      List.iter (fun func -> 
        start_positions := func :: !start_positions
        ) funs
  | e -> ()
  end;
  start_positions := List.sort compare !start_positions;
  Ino_continue

let print_start_positions () =
  printf "@[<2>{Function starting positions:@ ";
  List.iter (fun pos -> printf "%d@ " pos) !start_positions;
  printf "@."

let do_code_pass frag (ic: in_channel) (name: string) (f: int -> parsed_instr -> inst_outcome) : unit =
  let code_size = Bytesections.seek_section ic "CODE" in
  start := pos_in ic;
  let stop = !start + code_size in
  let pass_done = ref false in
  let index = ref 0 in
  try 
    begin
      while not !pass_done && pos_in ic < stop do 
        incr index;
        if !index < 0 then begin
          printf "do_code_pass: before parse, name=%s, index=%d@." name !index;
        end;
        let pi = parse_instr frag ic in
        if !index < 0 then begin
          printf "do_code_pass: before call, name=%s, index=%d@." name !index;
          ignore (print_parsed_instr !index pi);
        end;
        match f !index pi with
        | Ino_seek pos -> seek_in ic pos;
        | Ino_continue -> ()
        | Ino_done -> 
          printf "do_code_pass: exiting, name=%s, index=%d@." name !index;
          pass_done := true;
      done
    end
  with er -> printf "do_code_pass: Got error, name=%s, index=%d, error=%s@." name !index (Printexc.to_string er)

let fill_start_table frag ic =
  let code_size = Bytesections.seek_section ic "CODE" in
  start := pos_in ic;
  let stop = !start + code_size in
  List.iteri (fun i pos ->
    try begin
      seek_in ic (4 * pos + !start);
      let count = ref 0 in
      let max_tries = 2 in
      let found = ref false in
      while (!count < max_tries) && pos_in ic < stop && not !found do
        incr count;
        let pi = parse_instr frag ic in
        match pi.pi_ev with
        | Some code_ev -> 
            let ev = code_ev.ev_ev in
            let fun_name = ev.ev_defname in
            Hashtbl.add pc_by_function fun_name { frag=frag; pos=ev.ev_pos };
            found := true
        | None -> ()
      done;
      if not !found then begin
        missing_start_positions := pos :: !missing_start_positions
      end
    end
  with er -> printf "fill_start_table: Got error, i=%d, pos=%d, error=%s@."  i pos (Printexc.to_string er)
    ) !start_positions
  (*
  let num_found = Hashtbl.length pc_by_function in
  let num_missing = List.length !missing_start_positions in
  let num_known = List.length !Symbols.functions in
  printf "fill_start_table: num_found=%d, num_missing=%d, known funcs=%d@." num_found num_missing num_known;
  printf "@[<2>{Known missing functions:@ ";
  List.iter (fun fname ->
    if not (Hashtbl.mem pc_by_function fname) then 
      printf "%s@ " fname;
    ) !Symbols.functions;
  printf "}@]@."
  *)
      
let fill_unique_simple_names () =
  let short_to_long = 
    (Hashtbl.create 257 : (string, string list ref ) Hashtbl.t) in
  Hashtbl.iter (fun fname pc -> 
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
    ) pc_by_function;
  (* Now see which simple names are unique. *)
  Hashtbl.iter (fun sname entry ->
    match !entry with
    | [fname] -> (* it is unique *)
      let pc = Hashtbl.find pc_by_function fname in
      Hashtbl.add pc_by_function sname pc
    | _ -> () (* Not unique *)
    ) short_to_long
  

(* Find the function definitions in the code. On entry ic is positioned
   at the start of the code section. *)
let find_functions' frag (ic: in_channel) : unit = 
  do_code_pass frag ic "Find start" find_start_pos_in_instr;
  (* print_start_positions (); *)
  (* printf "find_functions': printed positions@."; *)
  fill_start_table frag ic;
  fill_unique_simple_names ();
  ()
  (* do_code_pass frag ic print_parsed_instr *)

let find_functions frag (ic: in_channel) = 
  try
    let prim_size = Bytesections.seek_section ic "PRIM" in
    primitives := read_primitive_table ic prim_size;

    ignore(Bytesections.seek_section ic "DATA");
    let init_data = (input_value ic : Obj.t array) in
    globals := Array.make (Array.length init_data) Empty;
    for i = 0 to Array.length init_data - 1 do
      !globals.(i) <- Constant (init_data.(i))
    done;

    Symtable.iter_global_map
      (fun id pos -> 
        !globals.(pos) <- Global id
        ) (Symtable.current_state ());

  (* We process the code after calling add_symbols as we need that info.*)
    ignore (Bytesections.seek_section ic "CODE");
    find_functions' frag ic
  with Not_found ->
    (* The file contains only debugging info,
       loading mode is forced to "manual" *)
    set_launching_function (List.assoc "manual" loading_modes);
  
  close_in_noerr ic
