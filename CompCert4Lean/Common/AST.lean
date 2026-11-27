import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.Errors
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats
import CompCert4Lean.X86_64.Archi

/-!
# Shared abstract-syntax definitions

This module translates the definition-bearing surface of CompCert's
`common/AST.v`. Proofs assigned to the later proof-migration phase are
represented by transparent proposition descriptors.
-/

namespace CompCert4Lean.Common.AST

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32

private abbrev z0 : Z := .Z0
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt

private def decEqSumbool {A : Type} [DecidableEq A] (x y : A) :
    Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

/-! ## Syntactic elements -/

abbrev ident : Type := positive

def ident_eq (x y : ident) : Sumbool (x = y) (x ≠ y) :=
  CompCert4Lean.Lib.Coqlib.peq x y

inductive typ : Type where
  | Tint
  | Tfloat
  | Tlong
  | Tsingle
  | Tany32
  | Tany64
deriving DecidableEq

export typ (Tint Tfloat Tlong Tsingle Tany32 Tany64)

def typ_eqStatement :=
  ∀ t1 t2 : typ, Sumbool (t1 = t2) (t1 ≠ t2)

def Tptr : typ :=
  if CompCert4Lean.X86_64.Archi.ptr64 then Tlong else Tint

def typesize : typ → Z
  | .Tint => zOfNat 4
  | .Tfloat => zOfNat 8
  | .Tlong => zOfNat 8
  | .Tsingle => zOfNat 4
  | .Tany32 => zOfNat 4
  | .Tany64 => zOfNat 8

def typesize_posStatement : Prop :=
  ∀ ty : typ, zLt z0 (typesize ty)

def subtype : typ → typ → Bool
  | .Tint, .Tint => true
  | .Tlong, .Tlong => true
  | .Tfloat, .Tfloat => true
  | .Tsingle, .Tsingle => true
  | .Tint, .Tany32 => true
  | .Tsingle, .Tany32 => true
  | .Tany32, .Tany32 => true
  | _, .Tany64 => true
  | _, _ => false

inductive xtype : Type where
  | Xbool
  | Xint8signed
  | Xint8unsigned
  | Xint16signed
  | Xint16unsigned
  | Xint
  | Xfloat
  | Xlong
  | Xsingle
  | Xptr
  | Xany32
  | Xany64
  | Xvoid
deriving DecidableEq

export xtype (Xbool Xint8signed Xint8unsigned Xint16signed Xint16unsigned Xint
  Xfloat Xlong Xsingle Xptr Xany32 Xany64 Xvoid)

def Xsize_t : xtype :=
  if CompCert4Lean.X86_64.Archi.ptr64 then Xlong else Xint

def xtype_eqStatement :=
  ∀ t1 t2 : xtype, Sumbool (t1 = t2) (t1 ≠ t2)

def inj_type : typ → xtype
  | .Tint => .Xint
  | .Tfloat => .Xfloat
  | .Tlong => .Xlong
  | .Tsingle => .Xsingle
  | .Tany32 => .Xany32
  | .Tany64 => .Xany64

def proj_xtype : xtype → typ
  | .Xbool | .Xint8signed | .Xint8unsigned | .Xint16signed | .Xint16unsigned
  | .Xint => .Tint
  | .Xfloat => .Tfloat
  | .Xlong => .Tlong
  | .Xsingle => .Tsingle
  | .Xptr => Tptr
  | .Xany32 => .Tany32
  | .Xany64 => .Tany64
  | .Xvoid => .Tint

structure calling_convention : Type where
  cc_vararg : Option Z
  cc_unproto : Bool
  cc_structret : Bool
deriving DecidableEq

export calling_convention (cc_vararg cc_unproto cc_structret)

def cc_default : calling_convention :=
  { cc_vararg := none, cc_unproto := false, cc_structret := false }

def calling_convention_eq (x y : calling_convention) :
    Sumbool (x = y) (x ≠ y) :=
  decEqSumbool x y

structure signature : Type where
  sig_args : List xtype
  sig_res : xtype
  sig_cc : calling_convention
deriving DecidableEq

export signature (sig_args sig_res sig_cc)

def proj_sig_args (s : signature) : List typ :=
  s.sig_args.map proj_xtype

def proj_sig_res (s : signature) : typ :=
  proj_xtype s.sig_res

def signature_eq (s1 s2 : signature) : Sumbool (s1 = s2) (s1 ≠ s2) :=
  decEqSumbool s1 s2

def signature_main : signature :=
  { sig_args := [], sig_res := Xint, sig_cc := cc_default }

/-! ## Memory chunks and initialization data -/

inductive memory_chunk : Type where
  | Mbool
  | Mint8signed
  | Mint8unsigned
  | Mint16signed
  | Mint16unsigned
  | Mint32
  | Mint64
  | Mfloat32
  | Mfloat64
  | Many32
  | Many64
deriving DecidableEq

export memory_chunk (Mbool Mint8signed Mint8unsigned Mint16signed Mint16unsigned
  Mint32 Mint64 Mfloat32 Mfloat64 Many32 Many64)

def chunk_eq (c1 c2 : memory_chunk) : Sumbool (c1 = c2) (c1 ≠ c2) :=
  decEqSumbool c1 c2

def Mptr : memory_chunk :=
  if CompCert4Lean.X86_64.Archi.ptr64 then Mint64 else Mint32

def type_of_chunk : memory_chunk → typ
  | .Mbool | .Mint8signed | .Mint8unsigned | .Mint16signed | .Mint16unsigned
  | .Mint32 => .Tint
  | .Mint64 => .Tlong
  | .Mfloat32 => .Tsingle
  | .Mfloat64 => .Tfloat
  | .Many32 => .Tany32
  | .Many64 => .Tany64

def xtype_of_chunk : memory_chunk → xtype
  | .Mbool => .Xbool
  | .Mint8signed => .Xint8signed
  | .Mint8unsigned => .Xint8unsigned
  | .Mint16signed => .Xint16signed
  | .Mint16unsigned => .Xint16unsigned
  | .Mint32 => .Xint
  | .Mint64 => .Xlong
  | .Mfloat32 => .Xsingle
  | .Mfloat64 => .Xfloat
  | .Many32 => .Xany32
  | .Many64 => .Xany64

def proj_xtype_of_chunkStatement : Prop :=
  ∀ chunk : memory_chunk,
    proj_xtype (xtype_of_chunk chunk) = type_of_chunk chunk

def chunk_of_type : typ → memory_chunk
  | .Tint => .Mint32
  | .Tfloat => .Mfloat64
  | .Tlong => .Mint64
  | .Tsingle => .Mfloat32
  | .Tany32 => .Many32
  | .Tany64 => .Many64

def chunk_of_TptrStatement : Prop :=
  chunk_of_type Tptr = Mptr

inductive init_data : Type where
  | Init_int8 (value : CCInt)
  | Init_int16 (value : CCInt)
  | Init_int32 (value : CCInt)
  | Init_int64 (value : CCInt64)
  | Init_float32 (value : CCFloat32)
  | Init_float64 (value : CCFloat)
  | Init_space (size : Z)
  | Init_addrof (symbol : ident) (offset : Ptrofs)

export init_data (Init_int8 Init_int16 Init_int32 Init_int64 Init_float32
  Init_float64 Init_space Init_addrof)

def init_data_size : init_data → Z
  | .Init_int8 _ => zOfNat 1
  | .Init_int16 _ => zOfNat 2
  | .Init_int32 _ => zOfNat 4
  | .Init_int64 _ => zOfNat 8
  | .Init_float32 _ => zOfNat 4
  | .Init_float64 _ => zOfNat 8
  | .Init_addrof _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then zOfNat 8 else zOfNat 4
  | .Init_space n => zMax n z0

def init_data_list_size : List init_data → Z
  | [] => z0
  | i :: rest => zAdd (init_data_size i) (init_data_list_size rest)

def init_data_size_posStatement : Prop :=
  ∀ i : init_data, zLe z0 (init_data_size i)

def init_data_list_size_posStatement : Prop :=
  ∀ il : List init_data, zLe z0 (init_data_list_size il)

/-! ## Globals and programs -/

structure globvar (V : Type) : Type where
  gvar_info : V
  gvar_init : List init_data
  gvar_readonly : Bool
  gvar_volatile : Bool

export globvar (gvar_info gvar_init gvar_readonly gvar_volatile)

inductive globdef (F V : Type) : Type where
  | Gfun (f : F)
  | Gvar (v : globvar V)

export globdef (Gfun Gvar)

structure program (F V : Type) : Type where
  prog_defs : List (ident × globdef F V)
  prog_public : List ident
  prog_main : ident

export program (prog_defs prog_public prog_main)

def prog_defs_names {F V : Type} (p : program F V) : List ident :=
  p.prog_defs.map Prod.fst

def prog_defmap {F V : Type} (p : program F V) :
    CompCert4Lean.Lib.Maps.PTree.t (globdef F V) :=
  p.prog_defs.foldl
    (fun m idg => CompCert4Lean.Lib.Maps.PTree.set idg.1 idg.2 m)
    (CompCert4Lean.Lib.Maps.PTree.empty (globdef F V))

def in_prog_defmapStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (id : ident) (g : globdef F V),
    CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p) = some g →
      (id, g) ∈ p.prog_defs

def prog_defmap_domStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (id : ident),
    id ∈ prog_defs_names p →
      ∃ g : globdef F V,
        CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p) = some g

def prog_defmap_norepetStatement : Prop :=
  ∀ (F V : Type) (p : program F V) (id : ident) (g : globdef F V),
    CompCert4Lean.Lib.Coqlib.list_norepet (prog_defs_names p) →
    (id, g) ∈ p.prog_defs →
    CompCert4Lean.Lib.Maps.PTree.get id (prog_defmap p) = some g

/-! ## Generic transformations over programs -/

def transform_program_globdef {A B V : Type} (transf : A → B) :
    ident × globdef A V → ident × globdef B V
  | (id, .Gfun f) => (id, .Gfun (transf f))
  | (id, .Gvar v) => (id, .Gvar v)

def transform_program {A B V : Type} (transf : A → B)
    (p : program A V) : program B V :=
  { prog_defs := p.prog_defs.map (transform_program_globdef transf)
    prog_public := p.prog_public
    prog_main := p.prog_main }

def transf_globvar {V W : Type}
    (transf_var : ident → V → Res W) (i : ident)
    (g : globvar V) : Res (globvar W) :=
  match transf_var i g.gvar_info with
  | .Error msg => .Error msg
  | .OK info' =>
      .OK
        { gvar_info := info'
          gvar_init := g.gvar_init
          gvar_readonly := g.gvar_readonly
          gvar_volatile := g.gvar_volatile }

private def bytesToString : List UInt8 → RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (bytesToString rest)

private def inFunctionText : RocqString :=
  bytesToString [73, 110, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32]

private def inVariableText : RocqString :=
  bytesToString [73, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32]

private def colonText : RocqString :=
  bytesToString [58, 32]

def transf_globdefs {A B V W : Type}
    (transf_fun : ident → A → Res B)
    (transf_var : ident → V → Res W) :
    List (ident × globdef A V) → Res (List (ident × globdef B W))
  | [] => .OK []
  | (id, .Gfun f) :: rest =>
      match transf_fun id f with
      | .Error msg =>
          .Error
            (CompCert4Lean.Common.Errors.MSG inFunctionText ::
              CompCert4Lean.Common.Errors.CTX id ::
              CompCert4Lean.Common.Errors.MSG colonText :: msg)
      | .OK tf =>
          match transf_globdefs transf_fun transf_var rest with
          | .Error msg => .Error msg
          | .OK tail => .OK ((id, .Gfun tf) :: tail)
  | (id, .Gvar v) :: rest =>
      match transf_globvar transf_var id v with
      | .Error msg =>
          .Error
            (CompCert4Lean.Common.Errors.MSG inVariableText ::
              CompCert4Lean.Common.Errors.CTX id ::
              CompCert4Lean.Common.Errors.MSG colonText :: msg)
      | .OK tv =>
          match transf_globdefs transf_fun transf_var rest with
          | .Error msg => .Error msg
          | .OK tail => .OK ((id, .Gvar tv) :: tail)

def transform_partial_program2 {A B V W : Type}
    (transf_fun : ident → A → Res B)
    (transf_var : ident → V → Res W)
    (p : program A V) : Res (program B W) :=
  match transf_globdefs transf_fun transf_var p.prog_defs with
  | .Error msg => .Error msg
  | .OK defs =>
      .OK { prog_defs := defs, prog_public := p.prog_public, prog_main := p.prog_main }

def transform_partial_program {A B V : Type}
    (transf_fun : A → Res B) (p : program A V) :
    Res (program B V) :=
  transform_partial_program2
    (fun _ f => transf_fun f)
    (fun _ v => .OK v)
    p

def transform_program_partial_programStatement : Prop :=
  ∀ (A B V : Type) (transf_fun : A → B) (p : program A V),
    transform_partial_program
        (fun f => CompCert4Lean.Common.Errors.OK (transf_fun f)) p =
      CompCert4Lean.Common.Errors.OK (transform_program transf_fun p)

/-! ## External functions -/

inductive external_function : Type where
  | EF_external (name : RocqString) (sg : signature)
  | EF_builtin (name : RocqString) (sg : signature)
  | EF_runtime (name : RocqString) (sg : signature)
  | EF_vload (chunk : memory_chunk)
  | EF_vstore (chunk : memory_chunk)
  | EF_malloc
  | EF_free
  | EF_memcpy (size alignment : Z)
  | EF_annot (kind : positive) (text : RocqString) (targs : List typ)
  | EF_annot_val (kind : positive) (text : RocqString) (targ : typ)
  | EF_inline_asm (text : RocqString) (sg : signature) (clobbers : List RocqString)
  | EF_debug (kind : positive) (text : ident) (targs : List typ)
deriving DecidableEq

export external_function (EF_external EF_builtin EF_runtime EF_vload EF_vstore
  EF_malloc EF_free EF_memcpy EF_annot EF_annot_val EF_inline_asm EF_debug)

def ef_sig : external_function → signature
  | .EF_external _ sg | .EF_builtin _ sg | .EF_runtime _ sg => sg
  | .EF_vload chunk =>
      { sig_args := [Xptr], sig_res := xtype_of_chunk chunk, sig_cc := cc_default }
  | .EF_vstore chunk =>
      { sig_args := [Xptr, xtype_of_chunk chunk], sig_res := Xvoid,
        sig_cc := cc_default }
  | .EF_malloc =>
      { sig_args := [Xsize_t], sig_res := Xptr, sig_cc := cc_default }
  | .EF_free =>
      { sig_args := [Xptr], sig_res := Xvoid, sig_cc := cc_default }
  | .EF_memcpy _ _ =>
      { sig_args := [Xptr, Xptr], sig_res := Xvoid, sig_cc := cc_default }
  | .EF_annot _ _ targs =>
      { sig_args := targs.map inj_type, sig_res := Xvoid, sig_cc := cc_default }
  | .EF_annot_val _ _ targ =>
      { sig_args := [inj_type targ], sig_res := inj_type targ, sig_cc := cc_default }
  | .EF_inline_asm _ sg _ => sg
  | .EF_debug _ _ targs =>
      { sig_args := targs.map inj_type, sig_res := Xvoid, sig_cc := cc_default }

def ef_inline : external_function → Bool
  | .EF_external _ _ => false
  | .EF_builtin _ _ => true
  | .EF_runtime _ _ => false
  | .EF_vload _ => true
  | .EF_vstore _ => true
  | .EF_malloc => false
  | .EF_free => false
  | .EF_memcpy _ _ => true
  | .EF_annot _ _ _ => true
  | .EF_annot_val _ _ _ => true
  | .EF_inline_asm _ _ _ => true
  | .EF_debug _ _ _ => true

def external_function_eq (ef1 ef2 : external_function) :
    Sumbool (ef1 = ef2) (ef1 ≠ ef2) :=
  decEqSumbool ef1 ef2

inductive fundef (F : Type) : Type where
  | Internal (f : F)
  | External (ef : external_function)

export fundef (Internal External)

def transf_fundef {A B : Type} (transf : A → B) : fundef A → fundef B
  | .Internal f => .Internal (transf f)
  | .External ef => .External ef

def transf_partial_fundef {A B : Type} (transf_partial : A → Res B) :
    fundef A → Res (fundef B)
  | .Internal f =>
      match transf_partial f with
      | .Error msg => .Error msg
      | .OK f' => .OK (.Internal f')
  | .External ef => .OK (.External ef)

/-! ## Register pairs -/

inductive rpair (A : Type) : Type where
  | One (r : A)
  | Twolong (rhi rlo : A)

export rpair (One Twolong)

def typ_rpair {A : Type} (typ_of : A → typ) : rpair A → typ
  | .One r => typ_of r
  | .Twolong _ _ => Tlong

def map_rpair {A B : Type} (f : A → B) : rpair A → rpair B
  | .One r => .One (f r)
  | .Twolong rhi rlo => .Twolong (f rhi) (f rlo)

def regs_of_rpair {A : Type} : rpair A → List A
  | .One r => [r]
  | .Twolong rhi rlo => [rhi, rlo]

def regs_of_rpairs {A : Type} : List (rpair A) → List A
  | [] => []
  | p :: rest => regs_of_rpair p ++ regs_of_rpairs rest

def in_regs_of_rpairsStatement : Prop :=
  ∀ (A : Type) (x : A) (p : rpair A),
    x ∈ regs_of_rpair p →
      ∀ l : List (rpair A), p ∈ l → x ∈ regs_of_rpairs l

def forall_rpair {A : Type} (P : A → Prop) : rpair A → Prop
  | .One r => P r
  | .Twolong rhi rlo => P rhi ∧ P rlo

/-! ## Builtin arguments and results -/

inductive builtin_arg (A : Type) : Type where
  | BA (x : A)
  | BA_int (n : CCInt)
  | BA_long (n : CCInt64)
  | BA_float (f : CCFloat)
  | BA_single (f : CCFloat32)
  | BA_loadstack (chunk : memory_chunk) (ofs : Ptrofs)
  | BA_addrstack (ofs : Ptrofs)
  | BA_loadglobal (chunk : memory_chunk) (id : ident) (ofs : Ptrofs)
  | BA_addrglobal (id : ident) (ofs : Ptrofs)
  | BA_splitlong (hi lo : builtin_arg A)
  | BA_addptr (a1 a2 : builtin_arg A)
deriving DecidableEq

export builtin_arg (BA BA_int BA_long BA_float BA_single BA_loadstack BA_addrstack
  BA_loadglobal BA_addrglobal BA_splitlong BA_addptr)

inductive builtin_res (A : Type) : Type where
  | BR (x : A)
  | BR_none
  | BR_splitlong (hi lo : builtin_res A)

export builtin_res (BR BR_none BR_splitlong)

def eq_builtin_arg {A : Type} (eq : ∀ x y : A, Sumbool (x = y) (x ≠ y))
    (x y : builtin_arg A) : Sumbool (x = y) (x ≠ y) := by
  letI : DecidableEq A := fun a b =>
    match eq a b with
    | .left h => isTrue h
    | .right h => isFalse h
  exact decEqSumbool x y

def globals_of_builtin_arg {A : Type} : builtin_arg A → List ident
  | .BA_loadglobal _ id _ => [id]
  | .BA_addrglobal id _ => [id]
  | .BA_splitlong hi lo => globals_of_builtin_arg hi ++ globals_of_builtin_arg lo
  | .BA_addptr a1 a2 => globals_of_builtin_arg a1 ++ globals_of_builtin_arg a2
  | _ => []

def globals_of_builtin_args {A : Type} (al : List (builtin_arg A)) : List ident :=
  al.foldr (fun a l => globals_of_builtin_arg a ++ l) []

def params_of_builtin_arg {A : Type} : builtin_arg A → List A
  | .BA x => [x]
  | .BA_splitlong hi lo => params_of_builtin_arg hi ++ params_of_builtin_arg lo
  | .BA_addptr a1 a2 => params_of_builtin_arg a1 ++ params_of_builtin_arg a2
  | _ => []

def params_of_builtin_args {A : Type} (al : List (builtin_arg A)) : List A :=
  al.foldr (fun a l => params_of_builtin_arg a ++ l) []

def params_of_builtin_res {A : Type} : builtin_res A → List A
  | .BR x => [x]
  | .BR_none => []
  | .BR_splitlong hi lo => params_of_builtin_res hi ++ params_of_builtin_res lo

def map_builtin_arg {A B : Type} (f : A → B) : builtin_arg A → builtin_arg B
  | .BA x => .BA (f x)
  | .BA_int n => .BA_int n
  | .BA_long n => .BA_long n
  | .BA_float n => .BA_float n
  | .BA_single n => .BA_single n
  | .BA_loadstack chunk ofs => .BA_loadstack chunk ofs
  | .BA_addrstack ofs => .BA_addrstack ofs
  | .BA_loadglobal chunk id ofs => .BA_loadglobal chunk id ofs
  | .BA_addrglobal id ofs => .BA_addrglobal id ofs
  | .BA_splitlong hi lo => .BA_splitlong (map_builtin_arg f hi) (map_builtin_arg f lo)
  | .BA_addptr a1 a2 => .BA_addptr (map_builtin_arg f a1) (map_builtin_arg f a2)

def map_builtin_res {A B : Type} (f : A → B) : builtin_res A → builtin_res B
  | .BR x => .BR (f x)
  | .BR_none => .BR_none
  | .BR_splitlong hi lo => .BR_splitlong (map_builtin_res f hi) (map_builtin_res f lo)

inductive builtin_arg_constraint : Type where
  | OK_default
  | OK_const
  | OK_addrstack
  | OK_addressing
  | OK_all

export builtin_arg_constraint (OK_default OK_const OK_addrstack OK_addressing OK_all)

end CompCert4Lean.Common.AST

namespace CompCert4Lean.Common.AST

def typ_eq : typ_eqStatement := by
  intro t1 t2
  by_cases h : t1 = t2
  · exact .left h
  · exact .right h

theorem typesize_pos : typesize_posStatement := by
  intro ty
  cases ty <;>
    simp [typesize,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.lt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat]

def xtype_eq : xtype_eqStatement := by
  intro t1 t2
  by_cases h : t1 = t2
  · exact .left h
  · exact .right h

theorem proj_xtype_of_chunk : proj_xtype_of_chunkStatement := by
  intro chunk
  cases chunk <;> rfl

end CompCert4Lean.Common.AST

namespace CompCert4Lean.Common.AST

theorem chunk_of_Tptr : chunk_of_TptrStatement := by
  rfl

private theorem init_data_size_nonneg (i : init_data) :
    zLe z0 (init_data_size i) := by
  cases i with
  | Init_int8 _ =>
      change (0 : Int) ≤ 1
      omega
  | Init_int16 _ =>
      change (0 : Int) ≤ 2
      omega
  | Init_int32 _ =>
      change (0 : Int) ≤ 4
      omega
  | Init_int64 _ =>
      change (0 : Int) ≤ 8
      omega
  | Init_float32 _ =>
      change (0 : Int) ≤ 4
      omega
  | Init_float64 _ =>
      change (0 : Int) ≤ 8
      omega
  | Init_addrof _ _ =>
      simp [init_data_size, CompCert4Lean.X86_64.Archi.ptr64,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat]
      change (0 : Int) ≤ 8
      omega
  | Init_space n =>
      exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le_max_r n z0

theorem init_data_size_pos : init_data_size_posStatement := by
  intro i
  exact init_data_size_nonneg i

theorem init_data_list_size_pos : init_data_list_size_posStatement := by
  intro il
  induction il with
  | nil =>
      change (0 : Int) ≤ 0
      omega
  | cons i il ih =>
      change (0 : Int) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add
            (init_data_size i) (init_data_list_size il))
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hi := init_data_size_nonneg i
      have hil := ih
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (init_data_size i) at hi
      change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (init_data_list_size il) at hil
      exact Int.add_nonneg hi hil

end CompCert4Lean.Common.AST

namespace CompCert4Lean.Common.AST

private theorem ast_get_foldl_mem_or_initial {A : Type} :
    ∀ (l : List (CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive × A))
      (m : CompCert4Lean.Lib.Maps.PTree.tree A)
      (k : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) (v : A),
      CompCert4Lean.Lib.Maps.PTree.get k
          (List.foldl (fun m kv => CompCert4Lean.Lib.Maps.PTree.set kv.1 kv.2 m) m l) =
        some v →
      (k, v) ∈ l ∨ CompCert4Lean.Lib.Maps.PTree.get k m = some v := by
  intro l
  induction l with
  | nil =>
      intro m k v h
      exact Or.inr h
  | cons p l ih =>
      intro m k v h
      rcases p with ⟨j, w⟩
      have htail :
          CompCert4Lean.Lib.Maps.PTree.get k
              (List.foldl
                (fun m kv => CompCert4Lean.Lib.Maps.PTree.set kv.1 kv.2 m)
                (CompCert4Lean.Lib.Maps.PTree.set j w m) l) = some v := by
        simpa only [List.foldl] using h
      rcases ih (CompCert4Lean.Lib.Maps.PTree.set j w m) k v htail with hmem | hinit
      · exact Or.inl (List.mem_cons_of_mem (j, w) hmem)
      · by_cases hkj : k = j
        · subst k
          have hwv : w = v := Option.some.inj (by
            simpa [CompCert4Lean.Lib.Maps.PTree.getSet_equation] using hinit)
          subst v
          exact Or.inl (by simp)
        · exact Or.inr (by
            simpa [CompCert4Lean.Lib.Maps.PTree.getSet_equation, hkj] using hinit)

theorem in_prog_defmap : in_prog_defmapStatement := by
  intro F V p id g h
  have h' := ast_get_foldl_mem_or_initial (A := globdef F V) p.prog_defs
    (CompCert4Lean.Lib.Maps.PTree.empty (globdef F V)) id g h
  rcases h' with hmem | hempty
  · exact hmem
  · simp [CompCert4Lean.Lib.Maps.PTree.empty, CompCert4Lean.Lib.Maps.PTree.get] at hempty

end CompCert4Lean.Common.AST

namespace CompCert4Lean.Common.AST

private theorem transf_globdefs_ok {A B V : Type} (transf_fun : A → B)
    (l : List (ident × globdef A V)) :
    transf_globdefs (fun _ f => CompCert4Lean.Common.Errors.OK (transf_fun f))
        (fun _ v => CompCert4Lean.Common.Errors.OK v) l =
      CompCert4Lean.Common.Errors.OK (l.map (transform_program_globdef transf_fun)) := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨id, gd⟩
      cases gd with
      | Gfun f => simp [transf_globdefs, transform_program_globdef, ih]
      | Gvar v => simp [transf_globdefs, transf_globvar, transform_program_globdef, ih]

theorem transform_program_partial_program : transform_program_partial_programStatement := by
  intro A B V transf_fun p
  unfold transform_partial_program transform_partial_program2 transform_program
  rw [transf_globdefs_ok]

theorem in_regs_of_rpairs : in_regs_of_rpairsStatement := by
  intro A x p hx l hp
  induction l with
  | nil => cases hp
  | cons q l ih =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · change x ∈ regs_of_rpair p ++ regs_of_rpairs l
        exact List.mem_append_left _ hx
      · simp only [regs_of_rpairs]
        exact List.mem_append_right _ (ih hp)

end CompCert4Lean.Common.AST

namespace CompCert4Lean.Common.AST

private theorem ast_get_foldl_preserve {A : Type} :
    ∀ (l : List (CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive × A))
      (m : CompCert4Lean.Lib.Maps.PTree.tree A)
      (k : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive),
      k ∉ l.map Prod.fst →
      CompCert4Lean.Lib.Maps.PTree.get k
          (List.foldl (fun m kv => CompCert4Lean.Lib.Maps.PTree.set kv.1 kv.2 m) m l) =
        CompCert4Lean.Lib.Maps.PTree.get k m := by
  intro l
  induction l with
  | nil =>
      intro m k h
      rfl
  | cons p l ih =>
      intro m k h
      rcases p with ⟨j, w⟩
      have hne : k ≠ j := by
        intro hkj
        apply h
        simp [hkj]
      have htail : k ∉ l.map Prod.fst := by
        intro hmem
        apply h
        simp [hmem]
      change CompCert4Lean.Lib.Maps.PTree.get k
          (List.foldl
            (fun m kv => CompCert4Lean.Lib.Maps.PTree.set kv.1 kv.2 m)
            (CompCert4Lean.Lib.Maps.PTree.set j w m) l) =
        CompCert4Lean.Lib.Maps.PTree.get k m
      rw [ih (CompCert4Lean.Lib.Maps.PTree.set j w m) k htail]
      simpa [CompCert4Lean.Lib.Maps.PTree.getSet_equation, hne]

private theorem ast_get_foldl_dom {A : Type} :
    ∀ (l : List (CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive × A))
      (m : CompCert4Lean.Lib.Maps.PTree.tree A)
      (k : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive),
      k ∈ l.map Prod.fst →
      ∃ v, CompCert4Lean.Lib.Maps.PTree.get k
          (List.foldl (fun m kv => CompCert4Lean.Lib.Maps.PTree.set kv.1 kv.2 m) m l) =
        some v := by
  intro l
  induction l with
  | nil =>
      intro m k h
      cases h
  | cons p l ih =>
      intro m k h
      rcases p with ⟨j, w⟩
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with hhead | htail
      · subst k
        by_cases htailmem : j ∈ l.map Prod.fst
        · simpa only [List.foldl] using
            ih (CompCert4Lean.Lib.Maps.PTree.set j w m) j htailmem
        · have hp := ast_get_foldl_preserve l
              (CompCert4Lean.Lib.Maps.PTree.set j w m) j htailmem
          refine ⟨w, ?_⟩
          have hset : CompCert4Lean.Lib.Maps.PTree.get j
                (CompCert4Lean.Lib.Maps.PTree.set j w m) = some w := by
            simp [CompCert4Lean.Lib.Maps.PTree.getSet_equation]
          rw [hset] at hp
          simpa only [List.foldl] using hp
      · simpa only [List.foldl] using
          ih (CompCert4Lean.Lib.Maps.PTree.set j w m) k htail

private theorem ast_get_foldl_norepet {A : Type} :
    ∀ (l : List (CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive × A))
      (m : CompCert4Lean.Lib.Maps.PTree.tree A)
      (k : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive) (v : A),
      CompCert4Lean.Lib.Coqlib.list_norepet (l.map Prod.fst) →
      (k, v) ∈ l →
      CompCert4Lean.Lib.Maps.PTree.get k
          (List.foldl (fun m kv => CompCert4Lean.Lib.Maps.PTree.set kv.1 kv.2 m) m l) =
        some v := by
  intro l
  induction l with
  | nil =>
      intro m k v hnr hmem
      cases hmem
  | cons p l ih =>
      intro m k v hnr hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · rcases hhead with rfl
        have hnot : k ∉ l.map Prod.fst := by
          cases hnr with
          | cons _ hnot _ => exact hnot
        have hpres := ast_get_foldl_preserve l
            (CompCert4Lean.Lib.Maps.PTree.set k v m) k hnot
        have hset : CompCert4Lean.Lib.Maps.PTree.get k
              (CompCert4Lean.Lib.Maps.PTree.set k v m) = some v := by
          simp [CompCert4Lean.Lib.Maps.PTree.getSet_equation]
        rw [hset] at hpres
        simpa only [List.foldl] using hpres
      · rcases p with ⟨j, w⟩
        have htailnr : CompCert4Lean.Lib.Coqlib.list_norepet (l.map Prod.fst) := by
          cases hnr with
          | cons _ _ htailnr => exact htailnr
        have hstep := ih (CompCert4Lean.Lib.Maps.PTree.set j w m) k v htailnr htail
        simpa only [List.foldl] using hstep

theorem prog_defmap_dom : prog_defmap_domStatement := by
  intro F V p id hmem
  exact ast_get_foldl_dom p.prog_defs
    (CompCert4Lean.Lib.Maps.PTree.empty (globdef F V)) id hmem

theorem prog_defmap_norepet : prog_defmap_norepetStatement := by
  intro F V p id g hnr hmem
  exact ast_get_foldl_norepet p.prog_defs
    (CompCert4Lean.Lib.Maps.PTree.empty (globdef F V)) id g hnr hmem

end CompCert4Lean.Common.AST
