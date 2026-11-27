import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Events
import CompCert4Lean.Common.ExternalCalls
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Smallstep
import CompCert4Lean.Common.Values
import CompCert4Lean.Cfrontend.Cop
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Floats
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps

/-!
# The Clight language

Definition-bearing translation of CompCert's `cfrontend/Clight.v`.  The
integrated external-call interface is proof-bearing, so the transition and
whole-program semantics explicitly receive its `ExternalCalls` provider.
-/

namespace CompCert4Lean.Cfrontend.Clight

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.ExternalCalls
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev calling_convention := CompCert4Lean.Common.AST.calling_convention
private abbrev external_function := CompCert4Lean.Common.AST.external_function
private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev float := CompCert4Lean.Lib.Floats.float
private abbrev float32 := CompCert4Lean.Lib.Floats.float32
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev composite_env := CompCert4Lean.Cfrontend.Ctypes.composite_env
private abbrev bitfield := CompCert4Lean.Cfrontend.Ctypes.bitfield
private abbrev unary_operation := CompCert4Lean.Cfrontend.Cop.unary_operation
private abbrev binary_operation := CompCert4Lean.Cfrontend.Cop.binary_operation
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

private abbrev z0 : Z := .Z0
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zGt := ZArith.BinInt.Z.gt
private abbrev zDivide := ZArith.BinInt.Z.divide

/-! ## Abstract syntax -/

inductive expr : Type where
  | Econst_int (i : int) (ty : type)
  | Econst_float (f : float) (ty : type)
  | Econst_single (f : float32) (ty : type)
  | Econst_long (i : int64) (ty : type)
  | Evar (id : ident) (ty : type)
  | Etempvar (id : ident) (ty : type)
  | Ederef (a : expr) (ty : type)
  | Eaddrof (a : expr) (ty : type)
  | Eunop (op : unary_operation) (a : expr) (ty : type)
  | Ebinop (op : binary_operation) (a1 a2 : expr) (ty : type)
  | Ecast (a : expr) (ty : type)
  | Efield (a : expr) (id : ident) (ty : type)
  | Esizeof (ty1 ty : type)
  | Ealignof (ty1 ty : type)

export expr (Econst_int Econst_float Econst_single Econst_long Evar Etempvar
  Ederef Eaddrof Eunop Ebinop Ecast Efield Esizeof Ealignof)

def typeof : expr → type
  | .Econst_int _ ty => ty
  | .Econst_float _ ty => ty
  | .Econst_single _ ty => ty
  | .Econst_long _ ty => ty
  | .Evar _ ty => ty
  | .Etempvar _ ty => ty
  | .Ederef _ ty => ty
  | .Eaddrof _ ty => ty
  | .Eunop _ _ ty => ty
  | .Ebinop _ _ _ ty => ty
  | .Ecast _ ty => ty
  | .Efield _ _ ty => ty
  | .Esizeof _ ty => ty
  | .Ealignof _ ty => ty

def label := ident

mutual
  inductive statement : Type where
    | Sskip
    | Sassign (lhs rhs : expr)
    | Sset (id : ident) (rhs : expr)
    | Scall (result : Option ident) (fn : expr) (args : List expr)
    | Sbuiltin (result : Option ident) (ef : external_function)
        (argTypes : List type) (args : List expr)
    | Ssequence (first second : statement)
    | Sifthenelse (cond : expr) (ifso ifnot : statement)
    | Sloop (body iter : statement)
    | Sbreak
    | Scontinue
    | Sreturn (result : Option expr)
    | Sswitch (selector : expr) (cases : labeled_statements)
    | Slabel (lbl : label) (body : statement)
    | Sgoto (lbl : label)

  inductive labeled_statements : Type where
    | LSnil
    | LScons (case : Option Z) (stmt : statement) (rest : labeled_statements)
end

export statement (Sskip Sassign Sset Scall Sbuiltin Ssequence Sifthenelse Sloop
  Sbreak Scontinue Sreturn Sswitch Slabel Sgoto)
export labeled_statements (LSnil LScons)

structure function : Type where
  fn_return : type
  fn_callconv : calling_convention
  fn_params : List (ident × type)
  fn_vars : List (ident × type)
  fn_temps : List (ident × type)
  fn_body : statement

export function (fn_return fn_callconv fn_params fn_vars fn_temps fn_body)

def var_names (vars : List (ident × type)) : List ident :=
  vars.map Prod.fst

def fundef : Type :=
  CompCert4Lean.Cfrontend.Ctypes.fundef function

def type_of_function (f : function) : type :=
  .Tfunction (type_of_params f.fn_params) f.fn_return f.fn_callconv

def type_of_fundef (f : fundef) : type :=
  match f with
  | .Internal fd => type_of_function fd
  | .External _ args result cc => .Tfunction args result cc

def program : Type :=
  CompCert4Lean.Cfrontend.Ctypes.program function

/-! ## Environments and memory access -/

structure genv : Type where
  genv_genv : Genv.t fundef type
  genv_cenv : composite_env

export genv (genv_genv genv_cenv)

def globalenv (p : program) : genv :=
  { genv_genv := Genv.globalenv (program_of_program p)
    genv_cenv := p.prog_comp_env }

abbrev env : Type := PTree.t (block × type)

def empty_env : env := PTree.empty (block × type)

abbrev temp_env : Type := PTree.t val

inductive deref_loc (ty : type) (m : mem) (b : block) (ofs : ptrofs) :
    bitfield → val → Prop where
  | deref_loc_value (chunk : memory_chunk) (v : val)
      (hmode : access_mode ty = .By_value chunk)
      (hload : Mem.loadv chunk m (.Vptr b ofs) = some v) :
      deref_loc ty m b ofs .Full v
  | deref_loc_reference (hmode : access_mode ty = .By_reference) :
      deref_loc ty m b ofs .Full (.Vptr b ofs)
  | deref_loc_copy (hmode : access_mode ty = .By_copy) :
      deref_loc ty m b ofs .Full (.Vptr b ofs)
  | deref_loc_bitfield (sz : intsize) (sg : signedness) (pos width : Z) (v : val)
      (hload : load_bitfield ty sz sg pos width m (.Vptr b ofs) v) :
      deref_loc ty m b ofs (.Bits sz sg pos width) v

export deref_loc (deref_loc_value deref_loc_reference deref_loc_copy
  deref_loc_bitfield)

inductive assign_loc (ce : composite_env) (ty : type) (m : mem) (b : block)
    (ofs : ptrofs) : bitfield → val → mem → Prop where
  | assign_loc_value (v : val) (chunk : memory_chunk) (m' : mem)
      (hmode : access_mode ty = .By_value chunk)
      (hstore : Mem.storev chunk m (.Vptr b ofs) v = some m') :
      assign_loc ce ty m b ofs .Full v m'
  | assign_loc_copy (b' : block) (ofs' : ptrofs)
      (bytes : List CompCert4Lean.Common.Memdata.memval) (m' : mem)
      (hmode : access_mode ty = .By_copy)
      (halignSource : zGt (sizeof ce ty) z0 →
        zDivide (alignof_blockcopy ce ty) (Ptrofs.unsigned ofs'))
      (halignTarget : zGt (sizeof ce ty) z0 →
        zDivide (alignof_blockcopy ce ty) (Ptrofs.unsigned ofs))
      (hseparated : b' ≠ b ∨ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs ∨
        zLe (zAdd (Ptrofs.unsigned ofs') (sizeof ce ty)) (Ptrofs.unsigned ofs) ∨
        zLe (zAdd (Ptrofs.unsigned ofs) (sizeof ce ty)) (Ptrofs.unsigned ofs'))
      (hload : Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = some bytes)
      (hstore : Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = some m') :
      assign_loc ce ty m b ofs .Full (.Vptr b' ofs') m'
  | assign_loc_bitfield (sz : intsize) (sg : signedness) (pos width : Z)
      (v : val) (m' : mem) (v' : val)
      (hstore : store_bitfield ty sz sg pos width m (.Vptr b ofs) v m' v') :
      assign_loc ce ty m b ofs (.Bits sz sg pos width) v m'

export assign_loc (assign_loc_value assign_loc_copy assign_loc_bitfield)

inductive alloc_variables (ge : genv) :
    env → mem → List (ident × type) → env → mem → Prop where
  | nil (e : env) (m : mem) : alloc_variables ge e m [] e m
  | cons (e : env) (m : mem) (id : ident) (ty : type)
      (vars : List (ident × type)) (m1 : mem) (b1 : block) (m2 : mem) (e2 : env)
      (halloc : Mem.alloc m z0 (sizeof ge.genv_cenv ty) = (m1, b1))
      (hrest : alloc_variables ge (PTree.set id (b1, ty) e) m1 vars e2 m2) :
      alloc_variables ge e m ((id, ty) :: vars) e2 m2

inductive bind_parameters (ge : genv) (e : env) :
    mem → List (ident × type) → List val → mem → Prop where
  | nil (m : mem) : bind_parameters ge e m [] [] m
  | cons (m : mem) (id : ident) (ty : type) (params : List (ident × type))
      (v1 : val) (vl : List val) (b : block) (m1 m2 : mem)
      (hfind : PTree.get id e = some (b, ty))
      (hassign : assign_loc ge.genv_cenv ty m b Ptrofs.zero .Full v1 m1)
      (hrest : bind_parameters ge e m1 params vl m2) :
      bind_parameters ge e m ((id, ty) :: params) (v1 :: vl) m2

def create_undef_temps : List (ident × type) → temp_env
  | [] => PTree.empty val
  | (id, _) :: rest => PTree.set id .Vundef (create_undef_temps rest)

def bind_parameter_temps :
    List (ident × type) → List val → temp_env → Option temp_env
  | [], [], le => some le
  | (id, _) :: formals, v :: args, le =>
      bind_parameter_temps formals args (PTree.set id v le)
  | _, _, _ => none

def block_of_binding (ge : genv) (binding : ident × (block × type)) : block × Z × Z :=
  let (_, b, ty) := (binding.1, binding.2.1, binding.2.2)
  (b, z0, sizeof ge.genv_cenv ty)

def blocks_of_env (ge : genv) (e : env) : List (block × Z × Z) :=
  (PTree.elements e).map (block_of_binding ge)

def set_opttemp (result : Option ident) (v : val) (le : temp_env) : temp_env :=
  match result with
  | none => le
  | some id => PTree.set id v le

/-! ## Switches and labeled statements -/

def select_switch_default : labeled_statements → labeled_statements
  | sl@.LSnil => sl
  | sl@(.LScons none _ _) => sl
  | .LScons (some _) _ rest => select_switch_default rest

def select_switch_case (n : Z) : labeled_statements → Option labeled_statements
  | .LSnil => none
  | .LScons none _ rest => select_switch_case n rest
  | sl@(.LScons (some c) _ rest) =>
      match zeq c n with
      | .left _ => some sl
      | .right _ => select_switch_case n rest

def select_switch (n : Z) (sl : labeled_statements) : labeled_statements :=
  match select_switch_case n sl with
  | some selected => selected
  | none => select_switch_default sl

def seq_of_labeled_statement : labeled_statements → statement
  | .LSnil => .Sskip
  | .LScons _ stmt rest => .Ssequence stmt (seq_of_labeled_statement rest)

/-! ## Evaluation of expressions -/

mutual
  inductive eval_expr
      [binary64_certificate : BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
      (ge : genv) (e : env) (le : temp_env) (m : mem) :
      expr → val → Prop where
    | const_int (i : int) (ty : type) :
        eval_expr ge e le m (.Econst_int i ty) (.Vint i)
    | const_float (f : float) (ty : type) :
        eval_expr ge e le m (.Econst_float f ty) (.Vfloat f)
    | const_single (f : float32) (ty : type) :
        eval_expr ge e le m (.Econst_single f ty) (.Vsingle f)
    | const_long (i : int64) (ty : type) :
        eval_expr ge e le m (.Econst_long i ty) (.Vlong i)
    | eval_Etempvar (id : ident) (ty : type) (v : val)
        (hfind : PTree.get id le = some v) :
        eval_expr ge e le m (.Etempvar id ty) v
    | eval_Eaddrof (a : expr) (ty : type) (loc : block) (ofs : ptrofs)
        (hlvalue : eval_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a loc ofs .Full) :
        eval_expr ge e le m (.Eaddrof a ty) (.Vptr loc ofs)
    | unary (op : unary_operation) (a : expr) (ty : type) (v1 v : val)
        (ha : eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a v1)
        (hop : sem_unary_operation
          (binary64_certificate := binary64_certificate) op v1 (typeof a) m = some v) :
        eval_expr ge e le m (.Eunop op a ty) v
    | binary (op : binary_operation) (a1 a2 : expr) (ty : type)
        (v1 v2 v : val)
        (ha1 : eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a1 v1)
        (ha2 : eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a2 v2)
        (hop : sem_binary_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m = some v) :
        eval_expr ge e le m (.Ebinop op a1 a2 ty) v
    | cast (a : expr) (ty : type) (v1 v : val)
        (ha : eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a v1)
        (hcast : sem_cast
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v1 (typeof a) ty m = some v) :
        eval_expr ge e le m (.Ecast a ty) v
    | sizeof_type (ty1 ty : type) :
        eval_expr ge e le m (.Esizeof ty1 ty)
          (Vptrofs (Ptrofs.repr (sizeof ge.genv_cenv ty1)))
    | alignof_type (ty1 ty : type) :
        eval_expr ge e le m (.Ealignof ty1 ty)
          (Vptrofs (Ptrofs.repr (alignof ge.genv_cenv ty1)))
    | eval_Elvalue (a : expr) (loc : block) (ofs : ptrofs) (bf : bitfield) (v : val)
        (hlvalue : eval_lvalue
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a loc ofs bf)
        (hderef : deref_loc (typeof a) m loc ofs bf v) :
        eval_expr ge e le m a v

  inductive eval_lvalue
      [binary64_certificate : BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate
        (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
      (ge : genv) (e : env) (le : temp_env) (m : mem) :
      expr → block → ptrofs → bitfield → Prop where
    | eval_Evar_local (id : ident) (loc : block) (ty : type)
        (hfind : PTree.get id e = some (loc, ty)) :
        eval_lvalue ge e le m (.Evar id ty) loc Ptrofs.zero .Full
    | eval_Evar_global (id : ident) (loc : block) (ty : type)
        (hlocal : PTree.get id e = none)
        (hglobal : Genv.find_symbol ge.genv_genv id = some loc) :
        eval_lvalue ge e le m (.Evar id ty) loc Ptrofs.zero .Full
    | eval_Ederef (a : expr) (ty : type) (loc : block) (ofs : ptrofs)
        (ha : eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a (.Vptr loc ofs)) :
        eval_lvalue ge e le m (.Ederef a ty) loc ofs .Full
    | eval_Efield_struct (a : expr) (id : ident) (ty : type) (loc : block)
        (ofs : ptrofs) (structId : ident) (co : composite) (att : attr)
        (delta : Z) (bf : bitfield)
        (ha : eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a (.Vptr loc ofs))
        (htype : typeof a = .Tstruct structId att)
        (hcomposite : PTree.get structId ge.genv_cenv = some co)
        (hoffset : field_offset ge.genv_cenv id co.co_members = .OK (delta, bf)) :
        eval_lvalue ge e le m (.Efield a id ty) loc
          (Ptrofs.add ofs (Ptrofs.repr delta)) bf
    | eval_Efield_union (a : expr) (id : ident) (ty : type) (loc : block)
        (ofs : ptrofs) (unionId : ident) (co : composite) (att : attr)
        (delta : Z) (bf : bitfield)
        (ha : eval_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) ge e le m a (.Vptr loc ofs))
        (htype : typeof a = .Tunion unionId att)
        (hcomposite : PTree.get unionId ge.genv_cenv = some co)
        (hoffset : union_field_offset ge.genv_cenv id co.co_members = .OK (delta, bf)) :
        eval_lvalue ge e le m (.Efield a id ty) loc
          (Ptrofs.add ofs (Ptrofs.repr delta)) bf
end

export eval_expr (eval_Etempvar eval_Eaddrof eval_Elvalue)
export eval_lvalue (eval_Evar_local eval_Evar_global eval_Ederef
  eval_Efield_struct eval_Efield_union)

/-! The exact combined mutual-induction surface emitted by Rocq's
`Combined Scheme eval_expr_lvalue_ind`.  It is a descriptor, not a proof: the
proof remains a distinct DMC-006 obligation even though Lean generates the two
component recursors. -/
def eval_expr_lvalue_indStatement
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (ge : genv) (e : env) (le : temp_env) (m : mem)
    (P : expr → val → Prop)
    (P0 : expr → block → ptrofs → bitfield → Prop),
    (∀ (i : int) (ty : type), P (.Econst_int i ty) (.Vint i)) →
    (∀ (f : float) (ty : type), P (.Econst_float f ty) (.Vfloat f)) →
    (∀ (f : float32) (ty : type), P (.Econst_single f ty) (.Vsingle f)) →
    (∀ (i : int64) (ty : type), P (.Econst_long i ty) (.Vlong i)) →
    (∀ (id : ident) (ty : type) (v : val),
      PTree.get id le = some v → P (.Etempvar id ty) v) →
    (∀ (a : expr) (ty : type) (loc : block) (ofs : ptrofs),
      eval_lvalue ge e le m a loc ofs .Full → P0 a loc ofs .Full →
      P (.Eaddrof a ty) (.Vptr loc ofs)) →
    (∀ (op : unary_operation) (a : expr) (ty : type) (v1 v : val),
      eval_expr ge e le m a v1 → P a v1 →
      sem_unary_operation op v1 (typeof a) m = some v →
      P (.Eunop op a ty) v) →
    (∀ (op : binary_operation) (a1 a2 : expr) (ty : type) (v1 v2 v : val),
      eval_expr ge e le m a1 v1 → P a1 v1 →
      eval_expr ge e le m a2 v2 → P a2 v2 →
      sem_binary_operation ge.genv_cenv op v1 (typeof a1) v2 (typeof a2) m = some v →
      P (.Ebinop op a1 a2 ty) v) →
    (∀ (a : expr) (ty : type) (v1 v : val),
      eval_expr ge e le m a v1 → P a v1 →
      sem_cast v1 (typeof a) ty m = some v → P (.Ecast a ty) v) →
    (∀ ty1 ty : type,
      P (.Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge.genv_cenv ty1)))) →
    (∀ ty1 ty : type,
      P (.Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge.genv_cenv ty1)))) →
    (∀ (a : expr) (loc : block) (ofs : ptrofs) (bf : bitfield) (v : val),
      eval_lvalue ge e le m a loc ofs bf → P0 a loc ofs bf →
      deref_loc (typeof a) m loc ofs bf v → P a v) →
    (∀ (id : ident) (loc : block) (ty : type),
      PTree.get id e = some (loc, ty) →
      P0 (.Evar id ty) loc Ptrofs.zero .Full) →
    (∀ (id : ident) (loc : block) (ty : type),
      PTree.get id e = none → Genv.find_symbol ge.genv_genv id = some loc →
      P0 (.Evar id ty) loc Ptrofs.zero .Full) →
    (∀ (a : expr) (ty : type) (loc : block) (ofs : ptrofs),
      eval_expr ge e le m a (.Vptr loc ofs) → P a (.Vptr loc ofs) →
      P0 (.Ederef a ty) loc ofs .Full) →
    (∀ (a : expr) (id : ident) (ty : type) (loc : block) (ofs : ptrofs)
      (structId : ident) (co : composite) (att : attr) (delta : Z) (bf : bitfield),
      eval_expr ge e le m a (.Vptr loc ofs) → P a (.Vptr loc ofs) →
      typeof a = .Tstruct structId att →
      PTree.get structId ge.genv_cenv = some co →
      field_offset ge.genv_cenv id co.co_members = .OK (delta, bf) →
      P0 (.Efield a id ty) loc (Ptrofs.add ofs (Ptrofs.repr delta)) bf) →
    (∀ (a : expr) (id : ident) (ty : type) (loc : block) (ofs : ptrofs)
      (unionId : ident) (co : composite) (att : attr) (delta : Z) (bf : bitfield),
      eval_expr ge e le m a (.Vptr loc ofs) → P a (.Vptr loc ofs) →
      typeof a = .Tunion unionId att →
      PTree.get unionId ge.genv_cenv = some co →
      union_field_offset ge.genv_cenv id co.co_members = .OK (delta, bf) →
      P0 (.Efield a id ty) loc (Ptrofs.add ofs (Ptrofs.repr delta)) bf) →
    (∀ e0 v, eval_expr ge e le m e0 v → P e0 v) ∧
      (∀ e0 b i bf, eval_lvalue ge e le m e0 b i bf → P0 e0 b i bf)

inductive eval_exprlist
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (ge : genv) (e : env) (le : temp_env) (m : mem) :
    List expr → List type → List val → Prop where
  | nil : eval_exprlist ge e le m [] [] []
  | cons (a : expr) (rest : List expr) (ty : type) (types : List type)
      (v1 v2 : val) (values : List val)
      (ha : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v1)
      (hcast : sem_cast
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) v1 (typeof a) ty m = some v2)
      (hrest : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m rest types values) :
      eval_exprlist ge e le m (a :: rest) (ty :: types) (v2 :: values)

/-! ## Continuations and states -/

inductive cont : Type where
  | Kstop
  | Kseq (next : statement) (k : cont)
  | Kloop1 (body iter : statement) (k : cont)
  | Kloop2 (body iter : statement) (k : cont)
  | Kswitch (k : cont)
  | Kcall (result : Option ident) (caller : function) (e : env)
      (le : temp_env) (k : cont)

export cont (Kstop Kseq Kloop1 Kloop2 Kswitch Kcall)

def call_cont : cont → cont
  | .Kseq _ k => call_cont k
  | .Kloop1 _ _ k => call_cont k
  | .Kloop2 _ _ k => call_cont k
  | .Kswitch k => call_cont k
  | k => k

def is_call_cont : cont → Prop
  | .Kstop => True
  | .Kcall _ _ _ _ _ => True
  | _ => False

inductive state : Type where
  | State (f : function) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem)
  | Callstate (fd : fundef) (args : List val) (k : cont) (m : mem)
  | Returnstate (result : val) (k : cont) (m : mem)

export state (State Callstate Returnstate)

/-! `machine_state` is retained as a compatibility alias for existing proof
    consumers; `state` is the canonical source-shaped carrier. -/
abbrev machine_state : Type := state

mutual
  def find_label (lbl : label) : statement → cont → Option (statement × cont)
    | .Ssequence s1 s2, k =>
        match find_label lbl s1 (.Kseq s2 k) with
        | some result => some result
        | none => find_label lbl s2 k
    | .Sifthenelse _ s1 s2, k =>
        match find_label lbl s1 k with
        | some result => some result
        | none => find_label lbl s2 k
    | .Sloop body iter, k =>
        match find_label lbl body (.Kloop1 body iter k) with
        | some result => some result
        | none => find_label lbl iter (.Kloop2 body iter k)
    | .Sswitch _ cases, k => find_label_ls lbl cases (.Kswitch k)
    | .Slabel lbl' body, k =>
        match ident_eq lbl lbl' with
        | .left _ => some (body, k)
        | .right _ => find_label lbl body k
    | _, _ => none

  def find_label_ls (lbl : label) :
      labeled_statements → cont → Option (statement × cont)
    | .LSnil, _ => none
    | .LScons _ stmt rest, k =>
        match find_label lbl stmt (.Kseq (seq_of_labeled_statement rest) k) with
        | some result => some result
        | none => find_label_ls lbl rest k
end

/-! Compatibility name for the existing proof packet; `find_label_ls` is the
    canonical source-shaped declaration. -/
abbrev findLabelCases := find_label_ls

/-! ## Transition semantics -/

inductive step
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv)
    (function_entry : function → List val → mem → env → temp_env → mem → Prop) :
    state → trace → state → Prop where
  | step_assign (f : function) (a1 a2 : expr) (k : cont) (e : env)
      (le : temp_env) (m : mem) (loc : block) (ofs : ptrofs) (bf : bitfield)
      (v2 v : val) (m' : mem)
      (hlvalue : eval_lvalue
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a1 loc ofs bf)
      (hrvalue : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a2 v2)
      (hcast : sem_cast
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) v2 (typeof a2) (typeof a1) m = some v)
      (hassign : assign_loc ge.genv_cenv (typeof a1) m loc ofs bf v m') :
      step xi ge function_entry (.State f (.Sassign a1 a2) k e le m) E0
        (.State f .Sskip k e le m')
  | step_set (f : function) (id : ident) (a : expr) (k : cont) (e : env)
      (le : temp_env) (m : mem) (v : val)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v) :
      step xi ge function_entry (.State f (.Sset id a) k e le m) E0
        (.State f .Sskip k e (PTree.set id v le) m)
  | step_call (f : function) (result : Option ident) (a : expr) (args : List expr)
      (k : cont) (e : env) (le : temp_env) (m : mem) (argTypes : List type)
      (resultType : type) (cc : calling_convention) (vf : val) (vargs : List val)
      (fd : fundef)
      (hclassify : classify_fun (typeof a) = .fun_case_f argTypes resultType cc)
      (hfn : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a vf)
      (hargs : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m args argTypes vargs)
      (hfind : Genv.find_funct ge.genv_genv vf = some fd)
      (htype : type_of_fundef fd = .Tfunction argTypes resultType cc) :
      step xi ge function_entry (.State f (.Scall result a args) k e le m) E0
        (.Callstate fd vargs (.Kcall result f e le k) m)
  | step_builtin (f : function) (result : Option ident) (ef : external_function)
      (argTypes : List type) (args : List expr) (k : cont) (e : env)
      (le : temp_env) (m : mem) (vargs : List val) (t : trace) (vres : val)
      (m' : mem) (hargs : eval_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m args argTypes vargs)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge.genv_genv) vargs m t vres m') :
      step xi ge function_entry (.State f (.Sbuiltin result ef argTypes args) k e le m) t
        (.State f .Sskip k e (set_opttemp result vres le) m')
  | step_seq (f : function) (s1 s2 : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f (.Ssequence s1 s2) k e le m) E0
        (.State f s1 (.Kseq s2 k) e le m)
  | step_skip_seq (f : function) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f .Sskip (.Kseq s k) e le m) E0
        (.State f s k e le m)
  | step_continue_seq (f : function) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f .Scontinue (.Kseq s k) e le m) E0
        (.State f .Scontinue k e le m)
  | step_break_seq (f : function) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f .Sbreak (.Kseq s k) e le m) E0
        (.State f .Sbreak k e le m)
  | step_ifthenelse (f : function) (a : expr) (s1 s2 : statement) (k : cont)
      (e : env) (le : temp_env) (m : mem) (v1 : val) (b : Bool)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v1)
      (hbool : bool_val v1 (typeof a) m = some b) :
      step xi ge function_entry (.State f (.Sifthenelse a s1 s2) k e le m) E0
        (.State f (if b then s1 else s2) k e le m)
  | step_loop (f : function) (body iter : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f (.Sloop body iter) k e le m) E0
        (.State f body (.Kloop1 body iter k) e le m)
  | step_skip_or_continue_loop1 (f : function) (body iter : statement) (k : cont)
      (e : env) (le : temp_env) (m : mem) (s : statement)
      (hfinished : s = .Sskip ∨ s = .Scontinue) :
      step xi ge function_entry (.State f s (.Kloop1 body iter k) e le m) E0
        (.State f iter (.Kloop2 body iter k) e le m)
  | step_break_loop1 (f : function) (body iter : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f .Sbreak (.Kloop1 body iter k) e le m) E0
        (.State f .Sskip k e le m)
  | step_skip_loop2 (f : function) (body iter : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f .Sskip (.Kloop2 body iter k) e le m) E0
        (.State f (.Sloop body iter) k e le m)
  | step_break_loop2 (f : function) (body iter : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f .Sbreak (.Kloop2 body iter k) e le m) E0
        (.State f .Sskip k e le m)
  | step_return_0 (f : function) (k : cont) (e : env) (le : temp_env)
      (m m' : mem) (hfree : Mem.free_list m (blocks_of_env ge e) = some m') :
      step xi ge function_entry (.State f (.Sreturn none) k e le m) E0
        (.Returnstate .Vundef (call_cont k) m')
  | step_return_1 (f : function) (a : expr) (k : cont) (e : env)
      (le : temp_env) (m : mem) (v v' : val) (m' : mem)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v)
      (hcast : sem_cast
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) v (typeof a) f.fn_return m = some v')
      (hfree : Mem.free_list m (blocks_of_env ge e) = some m') :
      step xi ge function_entry (.State f (.Sreturn (some a)) k e le m) E0
        (.Returnstate v' (call_cont k) m')
  | step_skip_call (f : function) (k : cont) (e : env) (le : temp_env)
      (m m' : mem) (hcall : is_call_cont k)
      (hfree : Mem.free_list m (blocks_of_env ge e) = some m') :
      step xi ge function_entry (.State f .Sskip k e le m) E0
        (.Returnstate .Vundef k m')
  | step_switch (f : function) (a : expr) (cases : labeled_statements) (k : cont)
      (e : env) (le : temp_env) (m : mem) (v : val) (n : Z)
      (heval : eval_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate) ge e le m a v)
      (harg : sem_switch_arg v (typeof a) = some n) :
      step xi ge function_entry (.State f (.Sswitch a cases) k e le m) E0
        (.State f (seq_of_labeled_statement (select_switch n cases)) (.Kswitch k) e le m)
  | step_skip_break_switch (f : function) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) (hfinished : s = .Sskip ∨ s = .Sbreak) :
      step xi ge function_entry (.State f s (.Kswitch k) e le m) E0
        (.State f .Sskip k e le m)
  | step_continue_switch (f : function) (k : cont) (e : env) (le : temp_env)
      (m : mem) :
      step xi ge function_entry (.State f .Scontinue (.Kswitch k) e le m) E0
        (.State f .Scontinue k e le m)
  | step_label (f : function) (lbl : label) (s : statement) (k : cont) (e : env)
      (le : temp_env) (m : mem) :
      step xi ge function_entry (.State f (.Slabel lbl s) k e le m) E0
        (.State f s k e le m)
  | step_goto (f : function) (lbl : label) (k : cont) (e : env)
      (le : temp_env) (m : mem) (s' : statement) (k' : cont)
      (hfind : find_label lbl f.fn_body (call_cont k) = some (s', k')) :
      step xi ge function_entry (.State f (.Sgoto lbl) k e le m) E0
        (.State f s' k' e le m)
  | step_internal_function (f : function) (vargs : List val) (k : cont)
      (m : mem) (e : env) (le : temp_env) (m1 : mem)
      (hentry : function_entry f vargs m e le m1) :
      step xi ge function_entry (.Callstate (.Internal f) vargs k m) E0
        (.State f f.fn_body k e le m1)
  | step_external_function (ef : external_function) (argTypes : List type)
      (resultType : type) (cc : calling_convention) (vargs : List val) (k : cont)
      (m : mem) (vres : val) (t : trace) (m' : mem)
      (hcall : external_call
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        xi ef (Genv.to_senv ge.genv_genv) vargs m t vres m') :
      step xi ge function_entry
        (.Callstate (.External ef argTypes resultType cc) vargs k m) t
        (.Returnstate vres k m')
  | step_returnstate (v : val) (result : Option ident) (f : function) (e : env)
      (le : temp_env) (k : cont) (m : mem) :
      step xi ge function_entry (.Returnstate v (.Kcall result f e le k) m) E0
        (.State f .Sskip k e (set_opttemp result v le) m)

export step (step_assign step_set step_call step_builtin step_seq step_skip_seq
  step_continue_seq step_break_seq step_ifthenelse step_loop
  step_skip_or_continue_loop1 step_break_loop1 step_skip_loop2 step_break_loop2
  step_return_0 step_return_1 step_skip_call step_switch step_skip_break_switch
  step_continue_switch step_label step_goto step_internal_function
  step_external_function step_returnstate)

/-! ## Whole-program semantics -/

inductive initial_state (p : program) : state → Prop where
  | intro (b : block) (f : fundef) (m0 : mem)
      (hmem : Genv.init_mem (program_of_program p) = some m0)
      (hsymbol : Genv.find_symbol (Genv.globalenv (program_of_program p)) p.prog_main = some b)
      (hfun : Genv.find_funct_ptr (Genv.globalenv (program_of_program p)) b = some f)
      (htype : type_of_fundef f = .Tfunction [] type_int32s cc_default) :
      initial_state p (.Callstate f [] .Kstop m0)

inductive final_state : state → int → Prop where
  | intro (result : int) (m : mem) :
      final_state (.Returnstate (.Vint result) .Kstop m) result

inductive function_entry1 (ge : genv) (f : function) (vargs : List val)
    (m : mem) (e : env) (le : temp_env) (m' : mem) : Prop where
  | intro (m1 : mem)
      (hnorepet : CompCert4Lean.Lib.Coqlib.list_norepet
        (var_names f.fn_params ++ var_names f.fn_vars))
      (halloc : alloc_variables ge empty_env m (f.fn_params ++ f.fn_vars) e m1)
      (hbind : bind_parameters ge e m1 f.fn_params vargs m')
      (htemps : le = create_undef_temps f.fn_temps) :
      function_entry1 ge f vargs m e le m'

def step1
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) :
    state → trace → state → Prop :=
  step (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ge (function_entry1 ge)

inductive function_entry2 (ge : genv) (f : function) (vargs : List val)
    (m : mem) (e : env) (le : temp_env) (m' : mem) : Prop where
  | intro
      (hvars : CompCert4Lean.Lib.Coqlib.list_norepet (var_names f.fn_vars))
      (hparams : CompCert4Lean.Lib.Coqlib.list_norepet (var_names f.fn_params))
      (hdisjoint : list_disjoint (var_names f.fn_params) (var_names f.fn_temps))
      (halloc : alloc_variables ge empty_env m f.fn_vars e m')
      (hbind : bind_parameter_temps f.fn_params vargs
        (create_undef_temps f.fn_temps) = some le) :
      function_entry2 ge f vargs m e le m'

def step2
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (ge : genv) :
    state → trace → state → Prop :=
  step (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) xi ge (function_entry2 ge)

def semantics1
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  let ge := globalenv p
  { state := state
    genvtype := genv
    step := step1
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi
    initial_state := initial_state p
    final_state := final_state
    globalenv := ge
    symbolenv := Genv.to_senv ge.genv_genv }

def semantics2
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)]
    (xi : ExternalCalls) (p : program) :
    CompCert4Lean.Common.Smallstep.semantics :=
  let ge := globalenv p
  { state := state
    genvtype := genv
    step := step2
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) xi
    initial_state := initial_state p
    final_state := final_state
    globalenv := ge
    symbolenv := Genv.to_senv ge.genv_genv }

end CompCert4Lean.Cfrontend.Clight

namespace CompCert4Lean.Cfrontend.Clight

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eval_expr_lvalue_ind
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] :
    eval_expr_lvalue_indStatement := by
  intro ge e le m P P0
  intro hconst_int hconst_float hconst_single hconst_long htempvar haddrof
    hunary hbinary hcast hsizeof halign hElvalue hvar_local hvar_global
    hderef hfield_struct hfield_union
  let motive₁ : ∀ (a : expr) (v : val),
      eval_expr ge e le m a v → Prop := fun a v _ => P a v
  let motive₂ : ∀ (a : expr) (b : block) (ofs : ptrofs) (bf : bitfield),
      eval_lvalue ge e le m a b ofs bf → Prop := fun a b ofs bf _ => P0 a b ofs bf
  have hexpr : ∀ (a : expr) (v : val),
      eval_expr ge e le m a v → P a v := by
    intro a v h
    exact eval_expr.rec
      (motive_1 := motive₁) (motive_2 := motive₂)
      (const_int := fun i ty => hconst_int i ty)
      (const_float := fun f ty => hconst_float f ty)
      (const_single := fun f ty => hconst_single f ty)
      (const_long := fun i ty => hconst_long i ty)
      (eval_Etempvar := fun id ty v hfind => htempvar id ty v hfind)
      (eval_Eaddrof := fun a ty loc ofs hlvalue ih => haddrof a ty loc ofs hlvalue ih)
      (unary := fun op a ty v1 v ha hop ih => hunary op a ty v1 v ha ih hop)
      (binary := fun op a1 a2 ty v1 v2 v ha1 ha2 hop ih1 ih2 =>
        hbinary op a1 a2 ty v1 v2 v ha1 ih1 ha2 ih2 hop)
      (cast := fun a ty v1 v ha hcast' ih => hcast a ty v1 v ha ih hcast')
      (sizeof_type := fun ty1 ty => hsizeof ty1 ty)
      (alignof_type := fun ty1 ty => halign ty1 ty)
      (eval_Elvalue := fun a loc ofs bf v hlvalue hderef' ih =>
        hElvalue a loc ofs bf v hlvalue ih hderef')
      (eval_Evar_local := fun id loc ty hfind => hvar_local id loc ty hfind)
      (eval_Evar_global := fun id loc ty hlocal hglobal =>
        hvar_global id loc ty hlocal hglobal)
      (eval_Ederef := fun a ty loc ofs ha ih => hderef a ty loc ofs ha ih)
      (eval_Efield_struct := fun a id ty loc ofs structId co att delta bf ha htype
          hcomposite hoffset ih =>
        hfield_struct a id ty loc ofs structId co att delta bf ha ih htype hcomposite hoffset)
      (eval_Efield_union := fun a id ty loc ofs unionId co att delta bf ha htype
          hcomposite hoffset ih =>
        hfield_union a id ty loc ofs unionId co att delta bf ha ih htype hcomposite hoffset)
      h
  have hlvalue : ∀ (a : expr) (b : block) (ofs : ptrofs) (bf : bitfield),
      eval_lvalue ge e le m a b ofs bf → P0 a b ofs bf := by
    intro a b ofs bf h
    exact eval_lvalue.rec
      (motive_1 := motive₁) (motive_2 := motive₂)
      (const_int := fun i ty => hconst_int i ty)
      (const_float := fun f ty => hconst_float f ty)
      (const_single := fun f ty => hconst_single f ty)
      (const_long := fun i ty => hconst_long i ty)
      (eval_Etempvar := fun id ty v hfind => htempvar id ty v hfind)
      (eval_Eaddrof := fun a ty loc ofs hlvalue ih => haddrof a ty loc ofs hlvalue ih)
      (unary := fun op a ty v1 v ha hop ih => hunary op a ty v1 v ha ih hop)
      (binary := fun op a1 a2 ty v1 v2 v ha1 ha2 hop ih1 ih2 =>
        hbinary op a1 a2 ty v1 v2 v ha1 ih1 ha2 ih2 hop)
      (cast := fun a ty v1 v ha hcast' ih => hcast a ty v1 v ha ih hcast')
      (sizeof_type := fun ty1 ty => hsizeof ty1 ty)
      (alignof_type := fun ty1 ty => halign ty1 ty)
      (eval_Elvalue := fun a loc ofs bf v hlvalue hderef' ih =>
        hElvalue a loc ofs bf v hlvalue ih hderef')
      (eval_Evar_local := fun id loc ty hfind => hvar_local id loc ty hfind)
      (eval_Evar_global := fun id loc ty hlocal hglobal =>
        hvar_global id loc ty hlocal hglobal)
      (eval_Ederef := fun a ty loc ofs ha ih => hderef a ty loc ofs ha ih)
      (eval_Efield_struct := fun a id ty loc ofs structId co att delta bf ha htype
          hcomposite hoffset ih =>
        hfield_struct a id ty loc ofs structId co att delta bf ha ih htype hcomposite hoffset)
      (eval_Efield_union := fun a id ty loc ofs unionId co att delta bf ha htype
          hcomposite hoffset ih =>
        hfield_union a id ty loc ofs unionId co att delta bf ha ih htype hcomposite hoffset)
      h
  exact ⟨hexpr, hlvalue⟩

end CompCert4Lean.Cfrontend.Clight
