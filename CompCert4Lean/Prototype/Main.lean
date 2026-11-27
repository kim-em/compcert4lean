import CompCert4Lean.Prototype.Codecs
import CompCert4Lean.Prototype.Services
import CompCert4Lean.Prototype.AllocationReport
import CompCert4Lean.Driver.Diagnostics
import CompCert4Lean.Prototype.AllocationTrace

namespace CompCert4Lean.Prototype

open Lean Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Allocator
open CompCert4Lean.X86.Machregs

def formatVersion := "compcert4lean-prototype-v3"
def codecFuel := 16777216

def getField (value : Json) (name : String) : CodecResult Json := value.getObjVal? name

def exactFields (value : Json) (names : List String) : CodecResult Unit := do
  let object ← value.getObj?
  unless object.size == names.length && names.all (fun name => (value.getObjVal? name).isOk) do
    throw "invalid configuration fields"

def rocqString (value : String) : RocqString :=
  value.toUTF8.toList.foldr .String .EmptyString

def canonicalReservedRegister (name : String) : Option mreg :=
  match name with
  | "RBX" => some .BX
  | "RBP" => some .BP
  | "R12" => some .R12
  | "R13" => some .R13
  | "R14" => some .R14
  | "R15" => some .R15
  | _ => none

def decodeReservedRegister (value : Json) : CodecResult mreg := do
  let name ← value.getStr?
  let some register := canonicalReservedRegister name |
    throw "reserved register must use a canonical callee-save x86 name"
  unless (register_by_name (rocqString name)).isSome do
    throw "unknown reserved register"
  return register

def decodeAllocationContext (value : Json) : CodecResult AllocationContext := do
  match value.getObjVal? "allocationContext" with
  | .error _ => return .empty
  | .ok context =>
      exactFields context ["reserved"]
      let names ← decList decodeReservedRegister (← getField context "reserved")
      let result : AllocationContext := { reserved := names }
      unless reservedWellFormed result do throw "duplicate reserved register"
      return result

def decodeLinkage (value : Json) : CodecResult Config.SymbolLinkageFacts := do
  exactFields value ["storage", "definedHere", "size"]
  let storage ← match ← (← getField value "storage").getStr? with
    | "default" => pure Config.StorageClass.storageDefault
    | "extern" => pure Config.StorageClass.storageExtern
    | "static" => pure Config.StorageClass.storageStatic
    | _ => throw "invalid symbol storage"
  let definedHere ← (← getField value "definedHere").getBool?
  let size ← decOption (fun value => do
    let number ← decimal value
    unless number >= 0 && number < (2 : Int)^63 do throw "invalid symbol size"
    return Int64.ofInt number) (← getField value "size")
  return { storage, definedHere, size }

def decodeOptimization (value : Json) : CodecResult Bool := do
  let version ← (← getField value "format").getStr?
  if version == formatVersion then
    match ← (← getField (← getField value "configuration") "optimization").getStr? with
    | "O0" => return false
    | "O2" => return true
    | _ => throw "unsupported optimization profile"
  else return false

def indexIdentifiers {α : Type} (entries : List (positive × α)) :
    Option (Lib.Maps.PTree.tree α) :=
  entries.foldlM (fun index (identifier, entry) =>
    if (Lib.Maps.PTree.get identifier index).isSome then none
    else some (Lib.Maps.PTree.set identifier entry index)) (Lib.Maps.PTree.empty α)

def decodeInlining (value : Json) : CodecResult Backend.Inlining.InliningConfig := do
  if (← (← getField value "format").getStr?) != formatVersion then return inlineCfg
  let enabled ← decodeOptimization value
  let fresh ← dec_pos codecFuel (← getField value "fresh")
  let functions ← decList (decPair (dec_pos codecFuel) (fun entry => do
    exactFields entry ["inline", "static"]
    let status ← match ← (← getField entry "inline").getStr? with
      | "inline" => pure Backend.Inlining.InlineStatus.inline
      | "noinline" => pure Backend.Inlining.InlineStatus.noinline
      | "none" => pure Backend.Inlining.InlineStatus.noSpecifier
      | _ => throw "invalid inline status"
    let isStatic ← (← getField entry "static").getBool?
    return (status, isStatic))) (← getField (← getField value "configuration") "functions")
  let some index := indexIdentifiers functions | throw "duplicate function metadata"
  let fresh := posToNat fresh
  unless functions.all (fun entry => posToNat entry.1 < fresh) do
    throw "function metadata exceeds fresh identifier boundary"
  return { enabled, functionsCalledOnce := enabled
           inlineStatus := fun identifier =>
             ((Lib.Maps.PTree.get identifier index).map Prod.fst).getD .noSpecifier
           isStatic := fun identifier =>
             ((Lib.Maps.PTree.get identifier index).map Prod.snd).getD false }

def decodeConfiguration (value : Json) : CodecResult Config.CompilerConfig := do
  let version ← (← getField value "format").getStr?
  if version == "compcert4lean-prototype-v1" then
    if (value.getObjVal? "configuration").isOk then throw "legacy input cannot specify configuration"
    return cfg
  unless version == formatVersion || version == "compcert4lean-prototype-v2" do
    throw "unsupported interchange version"
  let config ← getField value "configuration"
  exactFields config (if version == formatVersion then
    ["pic", "pie", "common", "symbols", "optimization", "functions"]
    else ["pic", "pie", "common", "symbols"])
  let base := if ← decodeOptimization value then optimizedCfg else cfg
  let _ ← decodeInlining value
  let pic ← (← getField config "pic").getBool?
  let pie ← (← getField config "pie").getBool?
  if pie then throw "PIE is not supported by this profile"
  let common ← (← getField config "common").getBool?
  let symbols ← decList (decPair (dec_pos codecFuel) decodeLinkage) (← getField config "symbols")
  let some index := indexIdentifiers symbols | throw "duplicate symbol linkage"
  let fresh := posToNat (← dec_pos codecFuel (← getField value "fresh"))
  unless symbols.all (fun entry => posToNat entry.1 < fresh) do
    throw "symbol linkage exceeds fresh identifier boundary"
  let relocation : Config.RelocationContext :=
    { pic := pic
      pie := pie
      common := common
      facts := fun identifier => Lib.Maps.PTree.get identifier index }
  return { base with relocation := relocation }

def decodeSource (value : Json) : CodecResult (Cfrontend.Csyntax.program × Cfrontend.SimplExpr.FreshIdentContext) := do
  let _ ← decodeConfiguration value
  let target := if ← decodeOptimization value then "x86_64-linux-sysv-O2" else "x86_64-linux-sysv-O0"
  unless (← (← getField value "target").getStr?) == target do
    throw "unsupported target configuration"
  let fresh ← dec_pos codecFuel (← getField value "fresh")
  let definitions ← decList (decPair (dec_pos codecFuel) (dec_CGlobdef codecFuel)) (← getField value "definitions")
  if (← (← getField value "format").getStr?) == formatVersion then
    let metadata ← decList (decPair (dec_pos codecFuel) pure)
      (← getField (← getField value "configuration") "functions")
    let functions := definitions.filterMap (fun (identifier, definition) => match definition with
      | .Gfun _ => some identifier | _ => none)
    let functionIndex := functions.foldl (fun index identifier =>
      Lib.Maps.PTree.set identifier () index) (Lib.Maps.PTree.empty Unit)
    unless metadata.length == functions.length &&
        metadata.all (fun pair => (Lib.Maps.PTree.get pair.1 functionIndex).isSome) do
      throw "function metadata does not match source definitions"
  let publicSymbols ← decList (dec_pos codecFuel) (← getField value "public")
  let mainIdent ← dec_pos codecFuel (← getField value "main")
  let types ← decList (dec_Ctypes_composite_definition codecFuel) (← getField value "composites")
  match built : Cfrontend.Ctypes.build_composite_env types with
  | .Error errors => throw ("composite environment: " ++ errorText errors)
  | .OK environment =>
      return ({ prog_defs := definitions, prog_public := publicSymbols, prog_main := mainIdent,
                prog_types := types, prog_comp_env := environment, prog_comp_env_eq := built },
              ⟨.sequential fresh⟩)

def encodeTarget (input : Json) (target : X86.Asm.program) : CodecResult Json := do
  let configuration := match input.getObjVal? "configuration" with
    | .ok config => [("configuration", config)]
    | .error _ => []
  let allocationContext := match input.getObjVal? "allocationContext" with
    | .ok context => [("allocationContext", context)]
    | .error _ => []
  return Json.mkObj ([("format", ← getField input "format"), ("target", ← getField input "target"),
    ("allocator", .str "irc"), ("program", ← enc_AProgram codecFuel target)] ++
    configuration ++ allocationContext)

structure TargetHeader where
  configuration : List (String × Json)
  allocationContext : List (String × Json)
  format : CodecResult Json
  target : CodecResult Json

def targetHeader (input : Json) : TargetHeader :=
  { configuration := match input.getObjVal? "configuration" with
      | .ok value => [("configuration", value)]
      | .error _ => []
    allocationContext := match input.getObjVal? "allocationContext" with
      | .ok value => [("allocationContext", value)]
      | .error _ => []
    format := getField input "format"
    target := getField input "target" }

def encodeHeader (header : TargetHeader) (target : X86.Asm.program) : CodecResult Json := do
  return Json.mkObj ([("format", ← header.format), ("target", ← header.target),
    ("allocator", .str "irc"), ("program", ← enc_AProgram codecFuel target)] ++
    header.configuration ++ header.allocationContext)

-- Keep this boundary so input JSON is consumed before the compiler passes run.
@[noinline] def compileDecoded (header : TargetHeader)
    (configuration : Config.CompilerConfig) (allocationContext : AllocationContext)
    (inlining : Backend.Inlining.InliningConfig)
    (fresh : Cfrontend.SimplExpr.FreshIdentContext) (source : Cfrontend.Csyntax.program) :
    CodecResult Json := do
  match Driver.Compiler.transf_c_program configuration (selectionFor configuration) inlining
      (Allocator.regalloc configuration allocationContext) enumeration fresh source with
  | .Error errors => throw ("Lean compiler: " ++ errorText errors)
  | .OK target => encodeHeader header target

def compileJson (value : Json) : CodecResult Json := do
  let (source, fresh) ← decodeSource value
  let configuration ← decodeConfiguration value
  let allocationContext ← decodeAllocationContext value
  let inlining ← decodeInlining value
  compileDecoded (targetHeader value) configuration allocationContext inlining fresh source

def diagnoseJson (value : Json) (folder : System.FilePath) (allocation : Bool := false) : IO (CodecResult Json) := do
  let decoded := do
    let source ← decodeSource value
    let configuration ← decodeConfiguration value
    let inlining ← decodeInlining value
    let context ← decodeAllocationContext value
    return (source, configuration, inlining, context)
  match decoded with
  | .error message => return .error message
  | .ok ((source, fresh), configuration, inlining, context) =>
      IO.FS.createDirAll folder
      let started ← IO.monoMsNow
      let emit (stage : String) (details : Json := .null) : IO Unit := do
        let elapsed := (← IO.monoMsNow) - started
        let record := Json.mkObj [("stage", .str stage), ("milliseconds", toJson elapsed), ("details", details)]
        IO.FS.writeFile (folder / (stage ++ ".json")) (record.compress ++ "\n")
        (← IO.getStderr).putStrLn (stage ++ ": " ++ toString elapsed ++ " ms")
      let sink : Driver.Diagnostics.DiagnosticSink :=
        { clight := fun _ => emit "clight"
          cminor := fun _ => emit "cminor"
          rtl := fun tag program => do
            emit ("rtl-" ++ toString (intOfZ tag))
              (.arr ((program.prog_defs.filterMap (fun (identifier, definition) => match definition with
                | .Gfun (.Internal function) => some (Json.mkObj [
                    ("identifier", toJson (posToNat identifier)),
                    ("nodes", toJson (Lib.Maps.PTree.elements function.fn_code).length)])
                | _ => none)).toArray))
            if allocation && intOfZ tag == 8 then
              traceAllocation configuration context program (fun stage => emit stage)
          ltl := fun _ => emit "ltl"
          mach := fun _ => emit "mach" }
      emit "start" ((value.getObjVal? "configuration").toOption.getD .null)
      match ← Driver.Diagnostics.transf_c_program sink configuration (selectionFor configuration) inlining
          (Allocator.regalloc configuration context) enumeration fresh source with
      | .Error errors => return .error ("Lean compiler: " ++ errorText errors)
      | .OK target => emit "assembly"; return encodeTarget value target

def compileFiles (input output : System.FilePath) : IO (CodecResult Unit) := do
  let text ← IO.FS.readFile input
  match Json.parse text >>= compileJson with
  | .error message => return .error message
  | .ok value =>
      IO.FS.writeFile output (value.compress ++ "\n")
      return .ok ()

def runtimeVersion : String :=
  s!"Lean (version {Lean.versionString}, {System.Platform.target}, commit {Lean.githash})"

def serve : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then return 0
    let result : CodecResult (Option String) ← try
      let request := do
        let value ← Json.parse line
        if value == Json.mkObj [("operation", .str "version")] then return none
        exactFields value ["input", "output"]
        return some (← (← getField value "input").getStr?, ← (← getField value "output").getStr?)
      match request with
      | .error message => pure (.error message)
      | .ok none => pure (.ok (some runtimeVersion))
      | .ok (some (source, target)) => do
          let compiled ← compileFiles source target
          pure (compiled.map (fun _ => none))
    catch error => pure (.error ("leanCompiler: " ++ error.toString))
    let response := match result with
      | .ok none => Json.mkObj [("ok", .bool true)]
      | .ok (some version) => Json.mkObj [("ok", .bool true), ("version", .str version)]
      | .error message => Json.mkObj [("ok", .bool false), ("error", .str message)]
    output.putStrLn response.compress
    output.flush
  return 0

def run (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] =>
      IO.println runtimeVersion
      return 0
  | ["--server"] => serve
  | [mode, input, output, folder] =>
      unless mode == "--diagnose" || mode == "--diagnose-allocation" do return 2
      let text ← IO.FS.readFile input
      match Json.parse text with
      | .error message => IO.eprintln message; return 1
      | .ok value =>
          match ← diagnoseJson value folder (mode == "--diagnose-allocation") with
          | .error message => IO.eprintln message; return 1
          | .ok target => IO.FS.writeFile output (target.compress ++ "\n"); return 0
  | ["--allocator-report", input, output] =>
      let text ← IO.FS.readFile input
      let result := do
        let input ← Json.parse text
        let (source, fresh) ← decodeSource input
        allocationReport (← decodeConfiguration input) (← decodeInlining input)
          (← decodeAllocationContext input) source fresh
      match result with
      | .error message => (← IO.getStderr).putStrLn message; return 1
      | .ok report => IO.FS.writeFile output (report.compress ++ "\n"); return 0
  | ["--test-invalid-allocation", input] =>
      let text ← IO.FS.readFile input
      let result := do
        let input ← Json.parse text
        let (source, fresh) ← decodeSource input
        let configuration ← decodeConfiguration input
        let allocationContext ← decodeAllocationContext input
        let inlining ← decodeInlining input
        let corrupt : Backend.Allocation.RegallocOracle := fun function => do
          let proposed ← Allocator.regalloc configuration allocationContext function
          .OK { proposed with fn_stacksize := ZArith.BinInt.Z.add function.fn_stacksize (z 1) }
        match Driver.Compiler.transf_c_program configuration (selectionFor configuration) inlining corrupt enumeration fresh source with
        | .Error errors => throw (errorText errors)
        | .OK _ => pure ()
      match result with
      | .error message => (← IO.getStderr).putStrLn message; return 1
      | .ok () => return 0
  | ["--test-codecs"] =>
      let result : CodecResult Unit := do
        for bits in ["0", "9223372036854775808", "9218868437227405312", "9221120237041090561", "18446744073709551615"] do
          let encoded ← enc_float codecFuel (← dec_float codecFuel (.str bits))
          unless encoded == .str bits do throw ("float bits changed: " ++ bits)
        for bits in ["0", "2147483648", "2139095040", "2143289345", "4294967295"] do
          let encoded ← enc_single codecFuel (← dec_single codecFuel (.str bits))
          unless encoded == .str bits do throw ("single bits changed: " ++ bits)
        let identifier := "18446744073709551616000000000001"
        unless (← enc_pos codecFuel (← dec_pos codecFuel (.str identifier))) == .str identifier do
          throw "identifier bits changed"
      match result with
      | .error message => (← IO.getStderr).putStrLn message; return 1
      | .ok () => return 0
  | [input, output] =>
      let text ← IO.FS.readFile input
      match Json.parse text >>= compileJson with
      | .error message =>
          (← IO.getStderr).putStrLn message
          return 1
      | .ok value =>
          IO.FS.writeFile output (value.compress ++ "\n")
          return 0
  | _ =>
      (← IO.getStderr).putStrLn "usage: leanCompiler input.json output.json"
      return 2

end CompCert4Lean.Prototype
