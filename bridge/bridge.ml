open Primitives
open Codecs
open Camlcoq

let format_version = "compcert4lean-prototype-v3"
let member name value = Yojson.Basic.Util.member name value
let text name value = Yojson.Basic.Util.to_string (member name value)
let optimization = ref "O0"
let target () = "x86_64-linux-sysv-" ^ !optimization

let language_options = [
  "longdouble", Clflags.option_flongdouble;
  "struct-passing", Clflags.option_fstruct_passing;
  "vararg-calls", Clflags.option_fvararg_calls;
  "unprototyped", Clflags.option_funprototyped;
  "packed-structs", Clflags.option_fpacked_structs;
  "unstructured-switch", Clflags.option_funstructured_switch;
  "inline-asm", Clflags.option_finline_asm]

let configure request =
  let root = text "root" request in
  if Configuration.arch <> "x86" || Configuration.model <> "64" ||
     Configuration.abi <> "standard" || Configuration.system <> "linux" ||
     Configuration.is_big_endian then failwith "expected System V x86-64 Linux CompCert";
  Clflags.stdlib_path := Filename.concat root "runtime";
  Clflags.option_fpic := false;
  Clflags.option_fpie := false;
  Clflags.option_fcommon := false;
  optimization := "O0";
  let standard = match member "standard" request with
   | `Null -> "c99"
   | `String ("c99" | "c11" | "c18" as selected) -> selected
   | _ -> failwith "invalid C standard" in
  (match member "configuration" request with
   | `Null -> ()
   | `Assoc fields as config ->
       if not (List.mem (List.sort compare (List.map fst fields))
           [["common"; "pic"; "pie"]; ["common"; "optimization"; "pic"; "pie"]])
       then failwith "invalid configuration fields";
       (match member "optimization" config with
        | `Null -> ()
        | `String ("O0" | "O2" as profile) -> optimization := profile
        | _ -> failwith "invalid optimization profile");
       Clflags.option_fpic := Yojson.Basic.Util.to_bool (member "pic" config);
       Clflags.option_fcommon := Yojson.Basic.Util.to_bool (member "common" config);
       if Yojson.Basic.Util.to_bool (member "pie" config)
       then failwith "PIE is not supported by this profile"
   | _ -> failwith "invalid configuration");
  (match member "language" request with
   | `Null -> ()
   | flags -> List.iter (fun flag ->
       let flag = Yojson.Basic.Util.to_string flag in
       if flag = "-fall" || flag = "-fnone" then
         List.iter (fun (_, setting) -> setting := (flag = "-fall")) language_options
       else
         let enabled = not (String.starts_with ~prefix:"-fno-" flag) in
         let prefix = if enabled then "-f" else "-fno-" in
         if not (String.starts_with ~prefix flag) then failwith "invalid language option";
         let name = String.sub flag (String.length prefix) (String.length flag - String.length prefix) in
         (List.assoc name language_options) := enabled)
       (Yojson.Basic.Util.to_list flags));
  let enabled = !optimization = "O2" in
  Clflags.option_ffloatconstprop := (if enabled then 2 else 0);
  Clflags.option_ftailcalls := enabled;
  Clflags.option_fconstprop := enabled;
  Clflags.option_fcse := enabled;
  Clflags.option_fredundancy := enabled;
  Clflags.option_fifconversion := enabled;
  Clflags.option_finline := enabled;
  Clflags.option_finline_functions_called_once := enabled;
  Clflags.option_Osize := false;
  Clflags.option_Obranchless := false;
  Clflags.option_g := false;
  Camlcoq.use_canonical_atoms := false;
  CommonOptions.set_std standard;
  Frontend.init ()

let configuration_json (source : Csyntax.program) =
  let symbols = Hashtbl.fold (fun identifier facts result ->
    let storage = match facts.C2C.a_storage with
      | C.Storage_default -> "default"
      | C.Storage_extern -> "extern"
      | C.Storage_static -> "static"
      | _ -> failwith "unsupported global storage class" in
    (identifier, `List [enc_pos identifier; `Assoc [
      "storage", `String storage;
      "definedHere", `Bool facts.C2C.a_defined;
      "size", (match facts.C2C.a_size with None -> `Null | Some size -> `String (Int64.to_string size))]]) :: result)
    C2C.decl_atom [] in
  `Assoc ["pic", `Bool !Clflags.option_fpic; "pie", `Bool false;
          "common", `Bool !Clflags.option_fcommon;
          "optimization", `String !optimization;
          "functions", `List (List.filter_map (fun (identifier, definition) ->
            match definition with
            | AST.Gfun _ ->
                let status = match C2C.atom_inline identifier with
                  | C2C.Inline -> "inline" | C2C.Noinline -> "noinline"
                  | C2C.No_specifier -> "none" in
                Some (`List [enc_pos identifier; `Assoc ["inline", `String status;
                  "static", `Bool (C2C.atom_is_static identifier)]])
            | AST.Gvar _ -> None) source.prog_defs);
          "symbols", `List (List.map snd (List.sort (fun (left, _) (right, _) -> compare left right) symbols))]

let canonical_register_name = function
  | Machregs.BX -> "RBX"
  | Machregs.BP -> "RBP"
  | Machregs.R12 -> "R12"
  | Machregs.R13 -> "R13"
  | Machregs.R14 -> "R14"
  | Machregs.R15 -> "R15"
  | _ -> failwith "reserved register is not a System V callee-save register"

let allocation_context_json () =
  `Assoc ["reserved", `List
    (List.map (fun name -> `String name)
      (List.sort_uniq compare (List.map canonical_register_name !CPragmas.reserved_registers)))]

let source_json configuration (source : Csyntax.program) =
  `Assoc ["format", `String format_version;
          "target", `String (target ());
          "configuration", configuration;
          "allocationContext", allocation_context_json ();
          "fresh", enc_pos (Camlcoq.first_unused_ident ());
          "definitions", enc_list (enc_pair enc_pos enc_CGlobdef) source.prog_defs;
          "public", enc_list enc_pos source.prog_public;
          "main", enc_pos source.prog_main;
          "composites", enc_list enc_Ctypes_composite_definition source.prog_types;
          "names", `List (List.map (fun (identifier, name) -> `List [enc_pos identifier; `String name])
            (List.sort (fun (left, _) (right, _) -> compare (Camlcoq.P.to_int left) (Camlcoq.P.to_int right))
              (Hashtbl.fold (fun identifier name result -> (identifier, name) :: result)
                Camlcoq.string_of_atom [])))]

let same_ireg left right = Asm.ireg_eq left right

let supported_address_arg = function
  | AST.BA (Asm.IR _) -> true
  | AST.BA_addrstack _ | AST.BA_addrglobal _ -> true
  | AST.BA_addptr (AST.BA (Asm.IR _), AST.BA_int _)
  | AST.BA_addptr (AST.BA (Asm.IR _), AST.BA_long _) -> true
  | _ -> false

let address_mentions register = function
  | AST.BA (Asm.IR candidate) -> same_ireg register candidate
  | AST.BA_addptr (AST.BA (Asm.IR candidate), _) -> same_ireg register candidate
  | _ -> false

let address_is_exact register = function
  | AST.BA (Asm.IR candidate) -> same_ireg register candidate
  | _ -> false

let rec supported_annotation_arg = function
  | AST.BA (Asm.IR _) | AST.BA (Asm.FR _)
  | AST.BA_int _ | AST.BA_long _ | AST.BA_float _ | AST.BA_single _
  | AST.BA_loadstack _ | AST.BA_addrstack _
  | AST.BA_loadglobal _ | AST.BA_addrglobal _ -> true
  | AST.BA _ -> false
  | AST.BA_splitlong (high, low) | AST.BA_addptr (high, low) ->
      supported_annotation_arg high && supported_annotation_arg low

let supported_vload_result chunk = function
  | AST.BR (Asm.IR _) when (chunk = AST.Mbool || chunk = AST.Mint8signed ||
      chunk = AST.Mint8unsigned || chunk = AST.Mint16signed ||
      chunk = AST.Mint16unsigned || chunk = AST.Mint32 || chunk = AST.Mint64) -> true
  | AST.BR (Asm.FR _) when (chunk = AST.Mfloat32 || chunk = AST.Mfloat64) -> true
  | AST.BR_splitlong (AST.BR (Asm.IR _), AST.BR (Asm.IR _))
      when chunk = AST.Mint64 -> true
  | _ -> false

let rec argument_registers = function
  | AST.BA register -> [register]
  | AST.BA_splitlong (left, right) | AST.BA_addptr (left, right) ->
      argument_registers left @ argument_registers right
  | _ -> []

let rec result_registers = function
  | AST.BR register -> [register]
  | AST.BR_splitlong (left, right) -> result_registers left @ result_registers right
  | AST.BR_none -> []

let rec satisfies_constraints registers constraints =
  match registers, constraints with
  | _, [] | [], _ -> true
  | register :: rest, constraint_ :: constraints ->
      (match constraint_ with None -> true | Some expected -> register = Asm.preg_of expected) &&
      satisfies_constraints rest constraints

let supported_inline name args result =
  let open AST in
  let open Asm in
  match name, args, result with
  | ("__builtin_bswap" | "__builtin_bswap16" | "__builtin_bswap32" | "__builtin_bswap64"
    | "__builtin_clz" | "__builtin_clzl" | "__builtin_clzll"
    | "__builtin_ctz" | "__builtin_ctzl" | "__builtin_ctzll"
    | "__builtin_read16_reversed" | "__builtin_read32_reversed"), [BA (IR _)], BR (IR _) -> true
  | ("__builtin_clzll" | "__builtin_ctzll"),
      [BA_splitlong (BA (IR _), BA (IR _))], BR (IR _) -> true
  | "__builtin_bswap64", [BA_splitlong (BA (IR RAX), BA (IR RDX))],
      BR_splitlong (BR (IR RDX), BR (IR RAX)) -> true
  | ("__builtin_fsqrt" | "__builtin_sqrt"), [BA (FR _)], BR (FR _) -> true
  | ("__builtin_fmadd" | "__builtin_fmsub" | "__builtin_fnmadd" | "__builtin_fnmsub"),
      [BA (FR _); BA (FR _); BA (FR _)], BR (FR _) -> true
  | "__builtin_negl", [BA_splitlong (BA (IR RDX), BA (IR RAX))],
      BR_splitlong (BR (IR RDX), BR (IR RAX)) -> true
  | ("__builtin_addl" | "__builtin_subl"),
      [BA_splitlong (BA (IR RDX), BA (IR RAX)); BA_splitlong (BA (IR RCX), BA (IR RBX))],
      BR_splitlong (BR (IR RDX), BR (IR RAX)) -> true
  | "__builtin_mull", [BA (IR RAX); BA (IR RDX)], BR_splitlong (BR (IR RDX), BR (IR RAX)) -> true
  | ("__builtin_write16_reversed" | "__builtin_write32_reversed"), [BA (IR _); BA (IR _)], _ -> true
  | "__builtin_va_start", [BA (IR RDX)], _ -> true
  | ("__builtin_membar" | "__builtin_nop" | "__builtin_unreachable"), [], _ -> true
  | _ -> false

let check_builtin function_name instruction_index variadic ef args result =
  let fail message =
    failwith (Printf.sprintf "function %s instruction %d: %s"
      function_name instruction_index message) in
  let require condition message = if not condition then fail message in
  let results = result_registers result in
  require (List.length (List.sort_uniq compare results) = List.length results)
    "builtin results overlap";
  let argument_constraints, result_constraints = Machregs.mregs_for_builtin ef in
  require (satisfies_constraints (List.concat_map argument_registers args) argument_constraints &&
           satisfies_constraints (result_registers result) result_constraints)
    "builtin operands violate pinned x86 fixed-register placement";
  match ef with
  | AST.EF_memcpy (size, _) ->
      let size = Z.to_int size in
      require (size >= 0) "memcpy has a negative size";
      begin match args, result with
      | [destination; source], AST.BR_none ->
          require (supported_address_arg destination && supported_address_arg source)
            "memcpy requires two address operands";
          if size <= 32 then begin
            require (not (address_mentions Asm.RCX destination ||
              address_mentions Asm.RCX source))
              "small memcpy address overlaps RCX scratch"
          end else begin
            require (address_is_exact Asm.RSI source || not (address_mentions Asm.RSI destination))
              "large memcpy source setup overwrites the destination address"
          end
      | _ -> fail "memcpy must have two operands and no result"
      end
  | AST.EF_vload chunk ->
      begin match args with
      | [address] ->
          require (supported_address_arg address) "vload requires an address operand";
          require (supported_vload_result chunk result) "vload has an incompatible result"
      | _ -> fail "vload must have one operand"
      end
  | AST.EF_vstore chunk ->
      begin match args, result with
      | [address; value], AST.BR_none ->
          require (supported_address_arg address) "vstore requires an address operand";
          begin match value with
          | AST.BA (Asm.IR _) ->
              require (supported_vload_result chunk (AST.BR (Asm.IR Asm.RAX)))
                "vstore integer value has an unsupported chunk"
          | AST.BA (Asm.FR _) ->
              require (chunk = AST.Mfloat32 || chunk = AST.Mfloat64)
                "vstore floating-point value has an integer chunk"
          | AST.BA_splitlong (AST.BA (Asm.IR _), AST.BA (Asm.IR _)) ->
              require (chunk = AST.Mint64) "split vstore requires Mint64"
          | _ -> fail "vstore value must be a register"
          end
      | _ -> fail "vstore must have an address and register value"
      end
  | AST.EF_builtin (name, _) when name = "__builtin_va_start" ->
      require variadic "va_start appears in a non-variadic function";
      begin match args, result with
      | [AST.BA (Asm.IR register)], AST.BR_none ->
          require (same_ireg register Asm.RDX) "va_start requires RDX and clobbers RAX"
      | _ -> fail "va_start requires one integer address and no result"
      end
  | AST.EF_annot _ | AST.EF_debug _ ->
      require (List.for_all supported_annotation_arg args)
        "annotation/debug operand is not printable"
  | AST.EF_annot_val _ ->
      require (match args, result with
        | [AST.BA (Asm.IR _)], AST.BR (Asm.IR _)
        | [AST.BA (Asm.FR _)], AST.BR (Asm.FR _) -> true
        | _ -> false) "annotation value requires matching register classes"
  | AST.EF_builtin (name, _) ->
      require (supported_inline name args result) ("unsupported operands for " ^ name)
  | AST.EF_inline_asm _ ->
      require (List.for_all supported_annotation_arg args &&
        List.for_all (function Asm.IR _ | Asm.FR _ -> true | _ -> false) (result_registers result))
        "unsupported inline assembly operand"
  | _ -> fail "external call is not an expandable builtin"

let check_program_compatibility (program : Asm.program) =
  List.iter (fun (identifier, definition) ->
    match definition with
    | AST.Gfun (AST.Internal function_definition) ->
        List.iteri (fun instruction_index instruction ->
          match instruction with
          | Asm.Pbuiltin (external_function, arguments, result) ->
              check_builtin (Camlcoq.extern_atom identifier) (instruction_index + 1)
                (function_definition.Asm.fn_sig.AST.sig_cc.AST.cc_vararg <> None)
                external_function arguments result
          | _ -> ()) function_definition.Asm.fn_code
    | AST.Gfun (AST.External _) | AST.Gvar _ -> ()) program.AST.prog_defs

let print_assembly configuration allocation_context input output =
  let data = Yojson.Basic.from_file input in
  let version = text "format" data in
  if not (List.mem version [format_version; "compcert4lean-prototype-v2"; "compcert4lean-prototype-v1"]) ||
     text "target" data <> target () ||
     (version <> format_version && !optimization <> "O0")
  then failwith "unsupported assembly interchange version/target";
  let compatible =
    if version = format_version then Yojson.Basic.equal (member "configuration" data) configuration
    else if version = "compcert4lean-prototype-v2" then
      let legacy = match configuration with
        | `Assoc fields -> `Assoc (List.filter (fun (name, _) -> name <> "optimization" && name <> "functions") fields)
        | _ -> assert false in
      Yojson.Basic.equal (member "configuration" data) legacy
    else member "configuration" data = `Null &&
         not !Clflags.option_fpic && not !Clflags.option_fpie && not !Clflags.option_fcommon in
  if not compatible then
    failwith "inconsistent assembly relocation configuration";
  let context_compatible =
    match member "allocationContext" data with
    | `Null -> allocation_context = `Assoc ["reserved", `List []]
    | `Assoc [("reserved", `List registers)] ->
        let canonical = List.sort_uniq compare registers in
        List.length canonical = List.length registers &&
        Yojson.Basic.equal (`Assoc ["reserved", `List canonical]) allocation_context
    | _ -> false in
  if not context_compatible then
    failwith "inconsistent reserved-register allocation context";
  let program = dec_AProgram (member "program" data) in
  check_program_compatibility program;
  match Asmexpand.expand_program program with
  | Errors.Error errors ->
      Format.eprintf "%a@." Driveraux.print_error errors;
      failwith "assembly expansion failed"
  | Errors.OK expanded ->
      let channel = open_out output in
      Fun.protect ~finally:(fun () -> close_out channel)
        (fun () -> PrintAsm.print_program channel expanded)

let respond fields =
  Yojson.Basic.to_channel stdout (`Assoc (("ok", `Bool true) :: fields));
  output_char stdout '\n'; flush stdout

let respond_error error =
  let message = Printexc.to_string error in
  Yojson.Basic.to_channel stdout (`Assoc ["ok", `Bool false; "error", `String message]);
  output_char stdout '\n'; flush stdout

(* Print a whole program whose identifiers are not those of a frontend run in
   this process (for example several translation units renamed into one
   numbering and linked in Lean). The request supplies every identifier's
   assembly name; no symbol has frontend declaration facts, so the printer
   uses its defaults: global symbols, functions in .text, initialised
   variables in .data with 8-byte alignment. *)
let print_named request =
  configure request;
  List.iter (fun entry ->
    match entry with
    | `List [identifier; `String name] ->
        let atom = P.of_int (int_of_string (Yojson.Basic.Util.to_string identifier)) in
        Hashtbl.replace string_of_atom atom name;
        Hashtbl.replace atom_of_string name atom
    | _ -> failwith "invalid name entry")
    (Yojson.Basic.Util.to_list (member "names" request));
  let data = Yojson.Basic.from_file (text "input" request) in
  if text "target" data <> target () then failwith "unsupported assembly target";
  let program = dec_AProgram (member "program" data) in
  check_program_compatibility program;
  match Asmexpand.expand_program program with
  | Errors.Error errors ->
      Format.eprintf "%a@." Driveraux.print_error errors;
      failwith "assembly expansion failed"
  | Errors.OK expanded ->
      let channel = open_out (text "output" request) in
      Fun.protect ~finally:(fun () -> close_out channel)
        (fun () -> PrintAsm.print_program channel expanded)

let run_request request read_request =
  if member "operation" request = `String "print_named" then begin
    print_named request;
    respond ["phase", `String "assembly"]
  end else
  let () = configure request in
  Clflags.prepro_options := List.rev (dec_list Yojson.Basic.Util.to_string (member "preprocessor" request));
  let input = text "source" request in
  let preprocessed = text "preprocessed" request in
  Frontend.preprocess input preprocessed;
  let source = Frontend.parse_c_file input preprocessed in
  Diagnostics.raise_on_errors ();
  let configuration = configuration_json source in
  let allocation_context = allocation_context_json () in
  Yojson.Basic.to_file (text "csyntax" request) (source_json configuration source);
  respond ["phase", `String "frontend"];
  let request = read_request () in
  if text "operation" request <> "print" then failwith "unknown bridge operation";
  print_assembly configuration allocation_context (text "input" request) (text "output" request);
  respond ["phase", `String "assembly"]

let run_once () =
  let read_request () = Yojson.Basic.from_string (read_line ()) in
  run_request (read_request ()) read_request

let read_server_line () =
  let buffer = Buffer.create 1024 in
  let character = Bytes.create 1 in
  let rec loop () =
    let count =
      try Unix.read Unix.stdin character 0 1
      with Unix.Unix_error (Unix.EINTR, _, _) -> -1 in
    match count with
    | -1 -> loop ()
    | 0 -> if Buffer.length buffer = 0 then raise End_of_file else Buffer.contents buffer
    | _ ->
        if Bytes.get character 0 = '\n' then Buffer.contents buffer
        else (Buffer.add_char buffer (Bytes.get character 0); loop ())
  in
  loop ()

let rec wait_child process =
  try snd (Unix.waitpid [] process)
  with Unix.Unix_error (Unix.EINTR, _, _) -> wait_child process

let run_server () =
  let rec loop () =
    match (try Some (read_server_line ()) with End_of_file -> None) with
    | None -> ()
    | Some line ->
        flush_all ();
        let process = Unix.fork () in
        if process = 0 then begin
          (try
            run_request (Yojson.Basic.from_string line)
              (fun () -> Yojson.Basic.from_string (read_server_line ()))
          with error ->
            prerr_endline ("CompCert bridge: " ^ Printexc.to_string error);
            respond_error error);
          exit 0
        end;
        (match wait_child process with
         | Unix.WEXITED 0 -> ()
         | Unix.WEXITED code -> respond_error (Failure (Printf.sprintf "bridge transaction exited %d" code))
         | Unix.WSIGNALED signal | Unix.WSTOPPED signal ->
             respond_error (Failure (Printf.sprintf "bridge transaction terminated by signal %d" signal)));
        loop ()
  in
  loop ()

let test_builtin_placement () =
  let open AST in
  let open Asm in
  let signature = { sig_args = []; sig_res = Xvoid; sig_cc = cc_default } in
  let reg register = BA (IR register) in
  let stack = BA_addrstack (Integers.Ptrofs.repr Z.zero) in
  let offset register = BA_addptr (reg register, BA_long (Integers.Int64.repr (Z.of_uint 8))) in
  let memcpy size = EF_memcpy (Z.of_uint size, Z.of_uint 8) in
  let va_start = EF_builtin ("__builtin_va_start", signature) in
  let cases = [
    true, true, memcpy 16, [reg RAX; reg RDX], BR_none;
    true, true, memcpy 16, [stack; reg RAX], BR_none;
    true, true, memcpy 16, [reg RAX; stack], BR_none;
    true, true, memcpy 16, [stack; stack], BR_none;
    false, true, memcpy 16, [reg RCX; reg RDX], BR_none;
    true, true, memcpy 128, [reg RDI; reg RSI], BR_none;
    true, true, memcpy 128, [stack; reg RDI], BR_none;
    true, true, memcpy 128, [reg RDI; stack], BR_none;
    true, true, memcpy 128, [offset RDI; offset RSI], BR_none;
    false, true, memcpy 128, [reg RSI; stack], BR_none;
    false, true, memcpy 128, [reg RDI; reg RDI], BR_none;
    true, true, va_start, [reg RDX], BR_none;
    false, true, va_start, [reg RAX], BR_none;
    false, false, va_start, [reg RDX], BR_none;
    false, true, EF_vstore Many64, [reg RAX; reg RDX], BR_none;
    false, true, EF_vload Mint32, [BA_int Integers.Int.zero], BR (IR RAX);
    false, true, EF_builtin ("__builtin_sqrt", signature), [reg RAX], BR (IR RAX);
    true, true, EF_builtin ("__builtin_sqrt", signature), [BA (FR XMM0)], BR (FR XMM1);
    true, true, EF_annot (P.of_int 1, "test", List.init 8 (fun _ -> Tint)),
      List.init 8 (fun _ -> BA_loadstack (Mint32, Integers.Ptrofs.zero)), BR_none
  ] in
  List.iteri (fun index (expected, variadic, ef, args, result) ->
    let accepted =
      try check_builtin "placement_fixture" (index + 1) variadic ef args result; true
      with Failure message ->
        if not (String.starts_with ~prefix:"function placement_fixture instruction " message)
        then failwith "missing placement diagnostic context";
        false in
    if accepted <> expected then failwith (Printf.sprintf "builtin placement case %d" index)) cases;
  print_endline "builtin placement tests: PASS"

let () =
  try
    let server_mode =
      try Sys.getenv "COMPCERT4LEAN_BRIDGE_SERVER" = "1" with Not_found -> false in
    if Array.to_list Sys.argv = [Sys.argv.(0); "--test-builtin-placement"]
    then test_builtin_placement ()
    else if server_mode || Array.to_list Sys.argv = [Sys.argv.(0); "--server"]
    then run_server ()
    else run_once ()
  with
  | Assert_failure (file, line, _) ->
      Printf.eprintf "CompCert bridge: unsupported construct for assembly expansion/printing (%s:%d); retain asm.json\n" file line;
      exit 1
  | error ->
      prerr_endline ("CompCert bridge: " ^ Printexc.to_string error);
      exit 1
