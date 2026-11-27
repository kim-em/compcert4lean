import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Values
import CompCert4Lean.Common.Memory
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats
import CompCert4Lean.X86_64.Archi

/-!
# Arithmetic and logical operators

Definition-bearing translation of CompCert's `cfrontend/Cop.v`.  Later proof
obligations are represented by exact proposition descriptors.
-/

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev mem := CompCert4Lean.Common.Memory.Mem.mem
private abbrev meminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev ident := CompCert4Lean.Common.AST.ident

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zGt := ZArith.BinInt.Z.gt
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

private def zltBool (x y : Z) : Bool :=
  match zlt x y with
  | .left _ => true
  | .right _ => false

private def zleBool (x y : Z) : Bool :=
  match zle x y with
  | .left _ => true
  | .right _ => false

namespace Int
private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int.mone
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int.min_signed
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev eq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev lt := CompCert4Lean.Lib.Integers.Int.lt
private abbrev ltu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int.add
private abbrev sub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev mul := CompCert4Lean.Lib.Integers.Int.mul
private abbrev divs := CompCert4Lean.Lib.Integers.Int.divs
private abbrev divu := CompCert4Lean.Lib.Integers.Int.divu
private abbrev and := CompCert4Lean.Lib.Integers.Int.and
private abbrev or := CompCert4Lean.Lib.Integers.Int.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int.shr
private abbrev zero_ext := CompCert4Lean.Lib.Integers.Int.zero_ext
private abbrev sign_ext := CompCert4Lean.Lib.Integers.Int.sign_ext
end Int

namespace Int64
private abbrev repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int64.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int64.mone
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int64.min_signed
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int64.iwordsize
private abbrev iwordsize' := CompCert4Lean.Lib.Integers.Int64.iwordsize'
private abbrev eq := CompCert4Lean.Lib.Integers.Int64.eq
private abbrev lt := CompCert4Lean.Lib.Integers.Int64.lt
private abbrev ltu := CompCert4Lean.Lib.Integers.Int64.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int64.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int64.add
private abbrev sub := CompCert4Lean.Lib.Integers.Int64.sub
private abbrev mul := CompCert4Lean.Lib.Integers.Int64.mul
private abbrev divs := CompCert4Lean.Lib.Integers.Int64.divs
private abbrev divu := CompCert4Lean.Lib.Integers.Int64.divu
private abbrev and := CompCert4Lean.Lib.Integers.Int64.and
private abbrev or := CompCert4Lean.Lib.Integers.Int64.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int64.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int64.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int64.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int64.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int64.shr
private abbrev loword := CompCert4Lean.Lib.Integers.Int64.loword
end Int64

namespace Float
private abbrev zero := CompCert4Lean.Lib.Floats.Float.zero
private abbrev neg := CompCert4Lean.Lib.Floats.Float.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float.cmp
private abbrev of_int := CompCert4Lean.Lib.Floats.Float.of_int
private abbrev of_intu := CompCert4Lean.Lib.Floats.Float.of_intu
private abbrev of_long := CompCert4Lean.Lib.Floats.Float.of_long
private abbrev of_longu := CompCert4Lean.Lib.Floats.Float.of_longu
private abbrev to_int := CompCert4Lean.Lib.Floats.Float.to_int
private abbrev to_intu := CompCert4Lean.Lib.Floats.Float.to_intu
private abbrev to_long := CompCert4Lean.Lib.Floats.Float.to_long
private abbrev to_longu := CompCert4Lean.Lib.Floats.Float.to_longu
private abbrev of_single := CompCert4Lean.Lib.Floats.Float.of_single
private abbrev to_single := CompCert4Lean.Lib.Floats.Float.to_single
end Float

namespace Float32
private abbrev zero := CompCert4Lean.Lib.Floats.Float32.zero
private abbrev neg := CompCert4Lean.Lib.Floats.Float32.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float32.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float32.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float32.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float32.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float32.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float32.cmp
private abbrev of_int := CompCert4Lean.Lib.Floats.Float32.of_int
private abbrev of_intu := CompCert4Lean.Lib.Floats.Float32.of_intu
private abbrev of_long := CompCert4Lean.Lib.Floats.Float32.of_long
private abbrev of_longu := CompCert4Lean.Lib.Floats.Float32.of_longu
private abbrev to_int := CompCert4Lean.Lib.Floats.Float32.to_int
private abbrev to_intu := CompCert4Lean.Lib.Floats.Float32.to_intu
private abbrev to_long := CompCert4Lean.Lib.Floats.Float32.to_long
private abbrev to_longu := CompCert4Lean.Lib.Floats.Float32.to_longu
end Float32

private abbrev boolEqInt : CCInt → CCInt → Bool := Int.eq
private abbrev boolEqInt64 : CCInt64 → CCInt64 → Bool := Int64.eq
private abbrev intsizeEq (x y : intsize) : Bool := decide (x = y)
private abbrev signednessEq (x y : signedness) : Bool := decide (x = y)
private abbrev identEq (x y : ident) : Bool := decide (x = y)

/-! ## Syntax of operators -/

inductive unary_operation : Type where
  | Onotbool
  | Onotint
  | Oneg
  | Oabsfloat

export unary_operation (Onotbool Onotint Oneg Oabsfloat)

inductive binary_operation : Type where
  | Oadd
  | Osub
  | Omul
  | Odiv
  | Omod
  | Oand
  | Oor
  | Oxor
  | Oshl
  | Oshr
  | Oeq
  | One
  | Olt
  | Ogt
  | Ole
  | Oge

export binary_operation (Oadd Osub Omul Odiv Omod Oand Oor Oxor Oshl Oshr Oeq One Olt Ogt Ole Oge)

inductive incr_or_decr : Type where
  | Incr
  | Decr

export incr_or_decr (Incr Decr)

/-! ## Casts and truth values -/

inductive classify_cast_cases : Type where
  | cast_case_pointer
  | cast_case_i2i (sz2 : intsize) (si2 : signedness)
  | cast_case_f2f
  | cast_case_s2s
  | cast_case_f2s
  | cast_case_s2f
  | cast_case_i2f (si1 : signedness)
  | cast_case_i2s (si1 : signedness)
  | cast_case_f2i (sz2 : intsize) (si2 : signedness)
  | cast_case_s2i (sz2 : intsize) (si2 : signedness)
  | cast_case_l2l
  | cast_case_i2l (si1 : signedness)
  | cast_case_l2i (sz2 : intsize) (si2 : signedness)
  | cast_case_l2f (si1 : signedness)
  | cast_case_l2s (si1 : signedness)
  | cast_case_f2l (si2 : signedness)
  | cast_case_s2l (si2 : signedness)
  | cast_case_i2bool
  | cast_case_l2bool
  | cast_case_f2bool
  | cast_case_s2bool
  | cast_case_struct (id1 id2 : ident)
  | cast_case_union (id1 id2 : ident)
  | cast_case_void
  | cast_case_default

export classify_cast_cases (cast_case_pointer cast_case_i2i cast_case_f2f cast_case_s2s
  cast_case_f2s cast_case_s2f cast_case_i2f cast_case_i2s cast_case_f2i cast_case_s2i
  cast_case_l2l cast_case_i2l cast_case_l2i cast_case_l2f cast_case_l2s cast_case_f2l
  cast_case_s2l cast_case_i2bool cast_case_l2bool cast_case_f2bool cast_case_s2bool
  cast_case_struct cast_case_union cast_case_void cast_case_default)

def classify_cast (tfrom tto : type) : classify_cast_cases :=
  match tto, tfrom with
  | .Tvoid, _ => .cast_case_void
  | .Tint sz2 si2 _, .Tint _ _ _ =>
      match sz2 with
      | .IBool => .cast_case_i2bool
      | .I32 => if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_i2i sz2 si2 else .cast_case_pointer
      | _ => .cast_case_i2i sz2 si2
  | .Tint sz2 si2 _, .Tlong _ _ =>
      if intsizeEq sz2 .IBool then .cast_case_l2bool else .cast_case_l2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F64 _ =>
      if intsizeEq sz2 .IBool then .cast_case_f2bool else .cast_case_f2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F32 _ =>
      if intsizeEq sz2 .IBool then .cast_case_s2bool else .cast_case_s2i sz2 si2
  | .Tint sz2 si2 _, .Tpointer _ _
  | .Tint sz2 si2 _, .Tarray _ _ _
  | .Tint sz2 si2 _, .Tfunction _ _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then
        if intsizeEq sz2 .IBool then .cast_case_l2bool else .cast_case_l2i sz2 si2
      else
        match sz2 with
        | .IBool => .cast_case_i2bool
        | .I32 => .cast_case_pointer
        | _ => .cast_case_i2i sz2 si2
  | .Tlong _ _, .Tlong _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_pointer else .cast_case_l2l
  | .Tlong _ _, .Tint _ si1 _ => .cast_case_i2l si1
  | .Tlong si2 _, .Tfloat .F64 _ => .cast_case_f2l si2
  | .Tlong si2 _, .Tfloat .F32 _ => .cast_case_s2l si2
  | .Tlong si2 _, .Tpointer _ _
  | .Tlong si2 _, .Tarray _ _ _
  | .Tlong si2 _, .Tfunction _ _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_pointer else .cast_case_i2l si2
  | .Tfloat .F64 _, .Tint _ si1 _ => .cast_case_i2f si1
  | .Tfloat .F32 _, .Tint _ si1 _ => .cast_case_i2s si1
  | .Tfloat .F64 _, .Tlong si1 _ => .cast_case_l2f si1
  | .Tfloat .F32 _, .Tlong si1 _ => .cast_case_l2s si1
  | .Tfloat .F64 _, .Tfloat .F64 _ => .cast_case_f2f
  | .Tfloat .F32 _, .Tfloat .F32 _ => .cast_case_s2s
  | .Tfloat .F64 _, .Tfloat .F32 _ => .cast_case_s2f
  | .Tfloat .F32 _, .Tfloat .F64 _ => .cast_case_f2s
  | .Tpointer _ _, .Tint _ si _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_i2l si else .cast_case_pointer
  | .Tpointer _ _, .Tlong _ _ =>
      if CompCert4Lean.X86_64.Archi.ptr64 then .cast_case_pointer else .cast_case_l2i .I32 .Unsigned
  | .Tpointer _ _, .Tpointer _ _
  | .Tpointer _ _, .Tarray _ _ _
  | .Tpointer _ _, .Tfunction _ _ _ => .cast_case_pointer
  | .Tstruct id2 _, .Tstruct id1 _ => .cast_case_struct id1 id2
  | .Tunion id2 _, .Tunion id1 _ => .cast_case_union id1 id2
  | _, _ => .cast_case_default

def cast_int_int (sz : intsize) (sg : signedness) (i : CCInt) : CCInt :=
  match sz, sg with
  | .I8, .Signed => Int.sign_ext (zOfNat 8) i
  | .I8, .Unsigned => Int.zero_ext (zOfNat 8) i
  | .I16, .Signed => Int.sign_ext (zOfNat 16) i
  | .I16, .Unsigned => Int.zero_ext (zOfNat 16) i
  | .I32, _ => i
  | .IBool, _ => if boolEqInt i Int.zero then Int.zero else Int.one

def cast_int_float
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (si : signedness) (i : CCInt) : CCFloat :=
  match si with
  | .Signed => Float.of_int (certificate := binary64_certificate) i
  | .Unsigned => Float.of_intu (certificate := binary64_certificate) i

def cast_float_int (si : signedness) (f : CCFloat) : Option CCInt :=
  match si with
  | .Signed => Float.to_int f
  | .Unsigned => Float.to_intu f

def cast_int_single
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (si : signedness) (i : CCInt) : CCFloat32 :=
  match si with
  | .Signed => Float32.of_int (certificate := binary32_certificate) i
  | .Unsigned => Float32.of_intu (certificate := binary32_certificate) i

def cast_single_int (si : signedness) (f : CCFloat32) : Option CCInt :=
  match si with
  | .Signed => Float32.to_int f
  | .Unsigned => Float32.to_intu f

def cast_int_long (si : signedness) (i : CCInt) : CCInt64 :=
  match si with
  | .Signed => Int64.repr (Int.signed i)
  | .Unsigned => Int64.repr (Int.unsigned i)

def cast_long_float
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (si : signedness) (i : CCInt64) : CCFloat :=
  match si with
  | .Signed => Float.of_long (certificate := binary64_certificate) i
  | .Unsigned => Float.of_longu (certificate := binary64_certificate) i

def cast_long_single
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (si : signedness) (i : CCInt64) : CCFloat32 :=
  match si with
  | .Signed => Float32.of_long (certificate := binary32_certificate) i
  | .Unsigned => Float32.of_longu (certificate := binary32_certificate) i

def cast_float_long (si : signedness) (f : CCFloat) : Option CCInt64 :=
  match si with
  | .Signed => Float.to_long f
  | .Unsigned => Float.to_longu f

def cast_single_long (si : signedness) (f : CCFloat32) : Option CCInt64 :=
  match si with
  | .Signed => Float32.to_long f
  | .Unsigned => Float32.to_longu f

def sem_cast
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v : val) (t1 t2 : type) (m : mem) : Option val :=
  match classify_cast t1 t2 with
  | .cast_case_pointer =>
      match v with
      | .Vptr _ _ => some v
      | .Vint _ => if CompCert4Lean.X86_64.Archi.ptr64 then none else some v
      | .Vlong _ => if CompCert4Lean.X86_64.Archi.ptr64 then some v else none
      | _ => none
  | .cast_case_i2i sz2 si2 =>
      match v with | .Vint i => some (.Vint (cast_int_int sz2 si2 i)) | _ => none
  | .cast_case_f2f => match v with | .Vfloat f => some (.Vfloat f) | _ => none
  | .cast_case_s2s => match v with | .Vsingle f => some (.Vsingle f) | _ => none
  | .cast_case_s2f => match v with | .Vsingle f => some (.Vfloat (Float.of_single f)) | _ => none
  | .cast_case_f2s => match v with | .Vfloat f => some (.Vsingle (Float.to_single f)) | _ => none
  | .cast_case_i2f si1 => match v with | .Vint i => some (.Vfloat (cast_int_float (binary64_certificate := binary64_certificate) si1 i)) | _ => none
  | .cast_case_i2s si1 => match v with | .Vint i => some (.Vsingle (cast_int_single (binary32_certificate := binary32_certificate) si1 i)) | _ => none
  | .cast_case_f2i sz2 si2 =>
      match v with
      | .Vfloat f => (cast_float_int si2 f).map (fun i => .Vint (cast_int_int sz2 si2 i))
      | _ => none
  | .cast_case_s2i sz2 si2 =>
      match v with
      | .Vsingle f => (cast_single_int si2 f).map (fun i => .Vint (cast_int_int sz2 si2 i))
      | _ => none
  | .cast_case_i2bool =>
      match v with
      | .Vint n => some (.Vint (if boolEqInt n Int.zero then Int.zero else Int.one))
      | .Vptr b ofs => if CompCert4Lean.X86_64.Archi.ptr64 then none else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some Vone else none
      | _ => none
  | .cast_case_l2bool =>
      match v with
      | .Vlong n => some (.Vint (if boolEqInt64 n Int64.zero then Int.zero else Int.one))
      | .Vptr b ofs => if !CompCert4Lean.X86_64.Archi.ptr64 then none else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some Vone else none
      | _ => none
  | .cast_case_f2bool =>
      match v with
      | .Vfloat f => some (.Vint (if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => none
  | .cast_case_s2bool =>
      match v with
      | .Vsingle f => some (.Vint (if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => none
  | .cast_case_l2l => match v with | .Vlong n => some (.Vlong n) | _ => none
  | .cast_case_i2l si => match v with | .Vint n => some (.Vlong (cast_int_long si n)) | _ => none
  | .cast_case_l2i sz si => match v with | .Vlong n => some (.Vint (cast_int_int sz si (Int.repr (Int64.unsigned n)))) | _ => none
  | .cast_case_l2f si1 => match v with | .Vlong i => some (.Vfloat (cast_long_float (binary64_certificate := binary64_certificate) si1 i)) | _ => none
  | .cast_case_l2s si1 => match v with | .Vlong i => some (.Vsingle (cast_long_single (binary32_certificate := binary32_certificate) si1 i)) | _ => none
  | .cast_case_f2l si2 => match v with | .Vfloat f => (cast_float_long si2 f).map .Vlong | _ => none
  | .cast_case_s2l si2 => match v with | .Vsingle f => (cast_single_long si2 f).map .Vlong | _ => none
  | .cast_case_struct id1 id2 => match v with | .Vptr _ _ => if identEq id1 id2 then some v else none | _ => none
  | .cast_case_union id1 id2 => match v with | .Vptr _ _ => if identEq id1 id2 then some v else none | _ => none
  | .cast_case_void => some v
  | .cast_case_default => none

inductive classify_bool_cases : Type where
  | bool_case_i
  | bool_case_l
  | bool_case_f
  | bool_case_s
  | bool_default

export classify_bool_cases (bool_case_i bool_case_l bool_case_f bool_case_s bool_default)

def classify_bool (ty : type) : classify_bool_cases :=
  match typeconv ty with
  | .Tint _ _ _ => .bool_case_i
  | .Tpointer _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then .bool_case_l else .bool_case_i
  | .Tfloat .F64 _ => .bool_case_f
  | .Tfloat .F32 _ => .bool_case_s
  | .Tlong _ _ => .bool_case_l
  | _ => .bool_default

def bool_val (v : val) (t : type) (m : mem) : Option Bool :=
  match classify_bool t with
  | .bool_case_i =>
      match v with
      | .Vint n => some (!(boolEqInt n Int.zero))
      | .Vptr b ofs => if CompCert4Lean.X86_64.Archi.ptr64 then none else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some true else none
      | _ => none
  | .bool_case_l =>
      match v with
      | .Vlong n => some (!(boolEqInt64 n Int64.zero))
      | .Vptr b ofs => if !CompCert4Lean.X86_64.Archi.ptr64 then none else if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then some true else none
      | _ => none
  | .bool_case_f => match v with | .Vfloat f => some (!(Float.cmp Ceq f Float.zero)) | _ => none
  | .bool_case_s => match v with | .Vsingle f => some (!(Float32.cmp Ceq f Float32.zero)) | _ => none
  | .bool_default => none

def sem_notbool (v : val) (ty : type) (m : mem) : Option val :=
  (bool_val v ty m).map (fun b => Values.Val.of_bool (!b))

inductive classify_neg_cases : Type where
  | neg_case_i (s : signedness)
  | neg_case_f
  | neg_case_s
  | neg_case_l (s : signedness)
  | neg_default

export classify_neg_cases (neg_case_i neg_case_f neg_case_s neg_case_l neg_default)

def classify_neg (ty : type) : classify_neg_cases :=
  match ty with
  | .Tint .I32 .Unsigned _ => .neg_case_i .Unsigned
  | .Tint _ _ _ => .neg_case_i .Signed
  | .Tfloat .F64 _ => .neg_case_f
  | .Tfloat .F32 _ => .neg_case_s
  | .Tlong si _ => .neg_case_l si
  | _ => .neg_default

def sem_neg (v : val) (ty : type) : Option val :=
  match classify_neg ty with
  | .neg_case_i _ => match v with | .Vint n => some (.Vint (Int.neg n)) | _ => none
  | .neg_case_f => match v with | .Vfloat f => some (.Vfloat (Float.neg f)) | _ => none
  | .neg_case_s => match v with | .Vsingle f => some (.Vsingle (Float32.neg f)) | _ => none
  | .neg_case_l _ => match v with | .Vlong n => some (.Vlong (Int64.neg n)) | _ => none
  | .neg_default => none

def sem_absfloat
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (v : val) (ty : type) : Option val :=
  match classify_neg ty with
  | .neg_case_i sg => match v with | .Vint n => some (.Vfloat (Float.abs (cast_int_float (binary64_certificate := binary64_certificate) sg n))) | _ => none
  | .neg_case_f => match v with | .Vfloat f => some (.Vfloat (Float.abs f)) | _ => none
  | .neg_case_s => match v with | .Vsingle f => some (.Vfloat (Float.abs (Float.of_single f))) | _ => none
  | .neg_case_l sg => match v with | .Vlong n => some (.Vfloat (Float.abs (cast_long_float (binary64_certificate := binary64_certificate) sg n))) | _ => none
  | .neg_default => none

inductive classify_notint_cases : Type where
  | notint_case_i (s : signedness)
  | notint_case_l (s : signedness)
  | notint_default

export classify_notint_cases (notint_case_i notint_case_l notint_default)

def classify_notint (ty : type) : classify_notint_cases :=
  match ty with
  | .Tint .I32 .Unsigned _ => .notint_case_i .Unsigned
  | .Tint _ _ _ => .notint_case_i .Signed
  | .Tlong si _ => .notint_case_l si
  | _ => .notint_default

def sem_notint (v : val) (ty : type) : Option val :=
  match classify_notint ty with
  | .notint_case_i _ => match v with | .Vint n => some (.Vint (Int.not n)) | _ => none
  | .notint_case_l _ => match v with | .Vlong n => some (.Vlong (Int64.not n)) | _ => none
  | .notint_default => none

/-! ## Binary operators -/

inductive binarith_cases : Type where
  | bin_case_i (s : signedness)
  | bin_case_l (s : signedness)
  | bin_case_f
  | bin_case_s
  | bin_default

export binarith_cases (bin_case_i bin_case_l bin_case_f bin_case_s bin_default)

def classify_binarith (ty1 ty2 : type) : binarith_cases :=
  match ty1, ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .bin_case_i .Unsigned
  | .Tint _ _ _, .Tint .I32 .Unsigned _ => .bin_case_i .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .bin_case_i .Signed
  | .Tlong .Signed _, .Tlong .Signed _ => .bin_case_l .Signed
  | .Tlong _ _, .Tlong _ _ => .bin_case_l .Unsigned
  | .Tlong sg _, .Tint _ _ _ => .bin_case_l sg
  | .Tint _ _ _, .Tlong sg _ => .bin_case_l sg
  | .Tfloat .F32 _, .Tfloat .F32 _ => .bin_case_s
  | .Tfloat _ _, .Tfloat _ _ => .bin_case_f
  | .Tfloat .F64 _, .Tint _ _ _
  | .Tfloat .F64 _, .Tlong _ _ => .bin_case_f
  | .Tint _ _ _, .Tfloat .F64 _
  | .Tlong _ _, .Tfloat .F64 _ => .bin_case_f
  | .Tfloat .F32 _, .Tint _ _ _
  | .Tfloat .F32 _, .Tlong _ _ => .bin_case_s
  | .Tint _ _ _, .Tfloat .F32 _
  | .Tlong _ _, .Tfloat .F32 _ => .bin_case_s
  | _, _ => .bin_default

def binarith_type (c : binarith_cases) : type :=
  match c with
  | .bin_case_i sg => .Tint .I32 sg noattr
  | .bin_case_l sg => .Tlong sg noattr
  | .bin_case_f => .Tfloat .F64 noattr
  | .bin_case_s => .Tfloat .F32 noattr
  | .bin_default => .Tvoid

def sem_binarith
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (sem_int : signedness → CCInt → CCInt → Option val)
    (sem_long : signedness → CCInt64 → CCInt64 → Option val)
    (sem_float : CCFloat → CCFloat → Option val)
    (sem_single : CCFloat32 → CCFloat32 → Option val)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  let c := classify_binarith t1 t2
  let t := binarith_type c
  match sem_cast (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 t m with
  | none => none
  | some v1' =>
      match sem_cast (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) v2 t2 t m with
      | none => none
      | some v2' =>
          match c with
          | .bin_case_i sg => match v1', v2' with | .Vint n1, .Vint n2 => sem_int sg n1 n2 | _, _ => none
          | .bin_case_f => match v1', v2' with | .Vfloat n1, .Vfloat n2 => sem_float n1 n2 | _, _ => none
          | .bin_case_s => match v1', v2' with | .Vsingle n1, .Vsingle n2 => sem_single n1 n2 | _, _ => none
          | .bin_case_l sg => match v1', v2' with | .Vlong n1, .Vlong n2 => sem_long sg n1 n2 | _, _ => none
          | .bin_default => none

inductive classify_add_cases : Type where
  | add_case_pi (ty : type) (si : signedness)
  | add_case_pl (ty : type)
  | add_case_ip (si : signedness) (ty : type)
  | add_case_lp (ty : type)
  | add_default

export classify_add_cases (add_case_pi add_case_pl add_case_ip add_case_lp add_default)

def classify_add (ty1 ty2 : type) : classify_add_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .add_case_pi ty si
  | .Tpointer ty _, .Tlong _ _ => .add_case_pl ty
  | .Tint _ si _, .Tpointer ty _ => .add_case_ip si ty
  | .Tlong _ _, .Tpointer ty _ => .add_case_lp ty
  | _, _ => .add_default

def ptrofs_of_int (si : signedness) (n : CCInt) : Ptrofs :=
  match si with
  | .Signed => Ptrofs.of_ints n
  | .Unsigned => Ptrofs.of_intu n

def sem_add_ptr_int (cenv : composite_env) (ty : type) (si : signedness) (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vint n2 =>
      let n2 := ptrofs_of_int si n2
      some (.Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
  | .Vint n1, .Vint n2 =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none else some (.Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
  | .Vlong n1, .Vint n2 =>
      let n2 := cast_int_long si n2
      if CompCert4Lean.X86_64.Archi.ptr64 then some (.Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else none
  | _, _ => none

def sem_add_ptr_long (cenv : composite_env) (ty : type) (v1 v2 : val) : Option val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vlong n2 =>
      let n2 := Ptrofs.of_int64 n2
      some (.Vptr b1 (Ptrofs.add ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
  | .Vint n1, .Vlong n2 =>
      let n2 := Int.repr (Int64.unsigned n2)
      if CompCert4Lean.X86_64.Archi.ptr64 then none else some (.Vint (Int.add n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
  | .Vlong n1, .Vlong n2 =>
      if CompCert4Lean.X86_64.Archi.ptr64 then some (.Vlong (Int64.add n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else none
  | _, _ => none

def sem_add
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cenv : composite_env) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_add t1 t2 with
  | .add_case_pi ty si => sem_add_ptr_int cenv ty si v1 v2
  | .add_case_pl ty => sem_add_ptr_long cenv ty v1 v2
  | .add_case_ip si ty => sem_add_ptr_int cenv ty si v2 v1
  | .add_case_lp ty => sem_add_ptr_long cenv ty v2 v1
  | .add_default =>
      sem_binarith (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (fun _ n1 n2 => some (.Vint (Int.add n1 n2)))
        (fun _ n1 n2 => some (.Vlong (Int64.add n1 n2)))
        (fun n1 n2 => some (.Vfloat (Float.add n1 n2)))
        (fun n1 n2 => some (.Vsingle (Float32.add n1 n2)))
        v1 t1 v2 t2 m

inductive classify_sub_cases : Type where
  | sub_case_pi (ty : type) (si : signedness)
  | sub_case_pp (ty : type)
  | sub_case_pl (ty : type)
  | sub_default

export classify_sub_cases (sub_case_pi sub_case_pp sub_case_pl sub_default)

def classify_sub (ty1 ty2 : type) : classify_sub_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .sub_case_pi ty si
  | .Tpointer ty _, .Tpointer _ _ => .sub_case_pp ty
  | .Tpointer ty _, .Tlong _ _ => .sub_case_pl ty
  | _, _ => .sub_default

def sem_sub
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cenv : composite_env) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_sub t1 t2 with
  | .sub_case_pi ty si =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vint n2 =>
          let n2 := ptrofs_of_int si n2
          some (.Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
      | .Vint n1, .Vint n2 =>
          if CompCert4Lean.X86_64.Archi.ptr64 then none else some (.Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
      | .Vlong n1, .Vint n2 =>
          let n2 := cast_int_long si n2
          if CompCert4Lean.X86_64.Archi.ptr64 then some (.Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else none
      | _, _ => none
  | .sub_case_pl ty =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vlong n2 =>
          let n2 := Ptrofs.of_int64 n2
          some (.Vptr b1 (Ptrofs.sub ofs1 (Ptrofs.mul (Ptrofs.repr (sizeof cenv ty)) n2)))
      | .Vint n1, .Vlong n2 =>
          let n2 := Int.repr (Int64.unsigned n2)
          if CompCert4Lean.X86_64.Archi.ptr64 then none else some (.Vint (Int.sub n1 (Int.mul (Int.repr (sizeof cenv ty)) n2)))
      | .Vlong n1, .Vlong n2 =>
          if CompCert4Lean.X86_64.Archi.ptr64 then some (.Vlong (Int64.sub n1 (Int64.mul (Int64.repr (sizeof cenv ty)) n2))) else none
      | _, _ => none
  | .sub_case_pp ty =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
          if identEq b1 b2 then
            let sz := sizeof cenv ty
            if zltBool z0 sz && zleBool sz Ptrofs.max_signed then
              some (Vptrofs (Ptrofs.divs (Ptrofs.sub ofs1 ofs2) (Ptrofs.repr sz)))
            else none
          else none
      | _, _ => none
  | .sub_default =>
      sem_binarith (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (fun _ n1 n2 => some (.Vint (Int.sub n1 n2)))
        (fun _ n1 n2 => some (.Vlong (Int64.sub n1 n2)))
        (fun n1 n2 => some (.Vfloat (Float.sub n1 n2)))
        (fun n1 n2 => some (.Vsingle (Float32.sub n1 n2)))
        v1 t1 v2 t2 m

def sem_mul
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (fun _ n1 n2 => some (.Vint (Int.mul n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Int64.mul n1 n2)))
    (fun n1 n2 => some (.Vfloat (Float.mul n1 n2)))
    (fun n1 n2 => some (.Vsingle (Float32.mul n1 n2))) v1 t1 v2 t2 m

def sem_div
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (fun sg n1 n2 => match sg with
      | .Signed => if boolEqInt n2 Int.zero || (boolEqInt n1 (Int.repr Int.min_signed) && boolEqInt n2 Int.mone) then none else some (.Vint (Int.divs n1 n2))
      | .Unsigned => if boolEqInt n2 Int.zero then none else some (.Vint (Int.divu n1 n2)))
    (fun sg n1 n2 => match sg with
      | .Signed => if boolEqInt64 n2 Int64.zero || (boolEqInt64 n1 (Int64.repr Int64.min_signed) && boolEqInt64 n2 Int64.mone) then none else some (.Vlong (Int64.divs n1 n2))
      | .Unsigned => if boolEqInt64 n2 Int64.zero then none else some (.Vlong (Int64.divu n1 n2)))
    (fun n1 n2 => some (.Vfloat (Float.div n1 n2)))
    (fun n1 n2 => some (.Vsingle (Float32.div n1 n2))) v1 t1 v2 t2 m

def sem_mod
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (fun sg n1 n2 => match sg with
      | .Signed => if boolEqInt n2 Int.zero || (boolEqInt n1 (Int.repr Int.min_signed) && boolEqInt n2 Int.mone) then none else some (.Vint (CompCert4Lean.Lib.Integers.Int.mods n1 n2))
      | .Unsigned => if boolEqInt n2 Int.zero then none else some (.Vint (CompCert4Lean.Lib.Integers.Int.modu n1 n2)))
    (fun sg n1 n2 => match sg with
      | .Signed => if boolEqInt64 n2 Int64.zero || (boolEqInt64 n1 (Int64.repr Int64.min_signed) && boolEqInt64 n2 Int64.mone) then none else some (.Vlong (CompCert4Lean.Lib.Integers.Int64.mods n1 n2))
      | .Unsigned => if boolEqInt64 n2 Int64.zero then none else some (.Vlong (CompCert4Lean.Lib.Integers.Int64.modu n1 n2)))
    (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

def sem_and
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) (fun _ n1 n2 => some (.Vint (Int.and n1 n2))) (fun _ n1 n2 => some (.Vlong (Int64.and n1 n2))) (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

def sem_or
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) (fun _ n1 n2 => some (.Vint (Int.or n1 n2))) (fun _ n1 n2 => some (.Vlong (Int64.or n1 n2))) (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

def sem_xor
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  sem_binarith (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate) (fun _ n1 n2 => some (.Vint (Int.xor n1 n2))) (fun _ n1 n2 => some (.Vlong (Int64.xor n1 n2))) (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

inductive classify_shift_cases : Type where
  | shift_case_ii (s : signedness)
  | shift_case_ll (s : signedness)
  | shift_case_il (s : signedness)
  | shift_case_li (s : signedness)
  | shift_default

export classify_shift_cases (shift_case_ii shift_case_ll shift_case_il shift_case_li shift_default)

def classify_shift (ty1 ty2 : type) : classify_shift_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .shift_case_ii .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .shift_case_ii .Signed
  | .Tint .I32 .Unsigned _, .Tlong _ _ => .shift_case_il .Unsigned
  | .Tint _ _ _, .Tlong _ _ => .shift_case_il .Signed
  | .Tlong s _, .Tint _ _ _ => .shift_case_li s
  | .Tlong s _, .Tlong _ _ => .shift_case_ll s
  | _, _ => .shift_default

def sem_shift
    (sem_int : signedness → CCInt → CCInt → CCInt)
    (sem_long : signedness → CCInt64 → CCInt64 → CCInt64)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  match classify_shift t1 t2 with
  | .shift_case_ii sg => match v1, v2 with
      | .Vint n1, .Vint n2 => if Int.ltu n2 Int.iwordsize then some (.Vint (sem_int sg n1 n2)) else none
      | _, _ => none
  | .shift_case_il sg => match v1, v2 with
      | .Vint n1, .Vlong n2 => if Int64.ltu n2 (Int64.repr (zOfNat 32)) then some (.Vint (sem_int sg n1 (Int64.loword n2))) else none
      | _, _ => none
  | .shift_case_li sg => match v1, v2 with
      | .Vlong n1, .Vint n2 => if Int.ltu n2 Int64.iwordsize' then some (.Vlong (sem_long sg n1 (Int64.repr (Int.unsigned n2)))) else none
      | _, _ => none
  | .shift_case_ll sg => match v1, v2 with
      | .Vlong n1, .Vlong n2 => if Int64.ltu n2 Int64.iwordsize then some (.Vlong (sem_long sg n1 n2)) else none
      | _, _ => none
  | .shift_default => none

def sem_shl (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  sem_shift (fun _ n1 n2 => Int.shl n1 n2) (fun _ n1 n2 => Int64.shl n1 n2) v1 t1 v2 t2

def sem_shr (v1 : val) (t1 : type) (v2 : val) (t2 : type) : Option val :=
  sem_shift
    (fun sg n1 n2 => match sg with | .Signed => Int.shr n1 n2 | .Unsigned => Int.shru n1 n2)
    (fun sg n1 n2 => match sg with | .Signed => Int64.shr n1 n2 | .Unsigned => Int64.shru n1 n2)
    v1 t1 v2 t2

inductive classify_cmp_cases : Type where
  | cmp_case_pp
  | cmp_case_pi (si : signedness)
  | cmp_case_ip (si : signedness)
  | cmp_case_pl
  | cmp_case_lp
  | cmp_default

export classify_cmp_cases (cmp_case_pp cmp_case_pi cmp_case_ip cmp_case_pl cmp_case_lp cmp_default)

def classify_cmp (ty1 ty2 : type) : classify_cmp_cases :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer _ _, .Tpointer _ _ => .cmp_case_pp
  | .Tpointer _ _, .Tint _ si _ => .cmp_case_pi si
  | .Tint _ si _, .Tpointer _ _ => .cmp_case_ip si
  | .Tpointer _ _, .Tlong _ _ => .cmp_case_pl
  | .Tlong _ _, .Tpointer _ _ => .cmp_case_lp
  | _, _ => .cmp_default

def cmp_ptr (m : mem) (c : comparison) (v1 v2 : val) : Option val :=
  ((if CompCert4Lean.X86_64.Archi.ptr64 then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 else Val.cmpu_bool (Mem.valid_pointer m) c v1 v2).map Val.of_bool)

def sem_cmp
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (c : comparison) (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match classify_cmp t1 t2 with
  | .cmp_case_pp => cmp_ptr m c v1 v2
  | .cmp_case_pi si =>
      match v2 with
      | .Vint n2 => cmp_ptr m c v1 (Vptrofs (ptrofs_of_int si n2))
      | .Vptr _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then none else cmp_ptr m c v1 v2
      | _ => none
  | .cmp_case_ip si =>
      match v1 with
      | .Vint n1 => cmp_ptr m c (Vptrofs (ptrofs_of_int si n1)) v2
      | .Vptr _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then none else cmp_ptr m c v1 v2
      | _ => none
  | .cmp_case_pl =>
      match v2 with
      | .Vlong n2 => cmp_ptr m c v1 (Vptrofs (Ptrofs.of_int64 n2))
      | .Vptr _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then cmp_ptr m c v1 v2 else none
      | _ => none
  | .cmp_case_lp =>
      match v1 with
      | .Vlong n1 => cmp_ptr m c (Vptrofs (Ptrofs.of_int64 n1)) v2
      | .Vptr _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then cmp_ptr m c v1 v2 else none
      | _ => none
  | .cmp_default =>
      sem_binarith (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (fun sg n1 n2 => some (Val.of_bool (match sg with | .Signed => CompCert4Lean.Lib.Integers.Int.cmp c n1 n2 | .Unsigned => CompCert4Lean.Lib.Integers.Int.cmpu c n1 n2)))
        (fun sg n1 n2 => some (Val.of_bool (match sg with | .Signed => CompCert4Lean.Lib.Integers.Int64.cmp c n1 n2 | .Unsigned => CompCert4Lean.Lib.Integers.Int64.cmpu c n1 n2)))
        (fun n1 n2 => some (Val.of_bool (Float.cmp c n1 n2)))
        (fun n1 n2 => some (Val.of_bool (Float32.cmp c n1 n2))) v1 t1 v2 t2 m

inductive classify_fun_cases : Type where
  | fun_case_f (targs : List type) (tres : type) (cc : calling_convention)
  | fun_default

export classify_fun_cases (fun_case_f fun_default)

def classify_fun (ty : type) : classify_fun_cases :=
  match ty with
  | .Tfunction args res cc => .fun_case_f args res cc
  | .Tpointer (.Tfunction args res cc) _ => .fun_case_f args res cc
  | _ => .fun_default

inductive classify_switch_cases : Type where
  | switch_case_i
  | switch_case_l
  | switch_default

export classify_switch_cases (switch_case_i switch_case_l switch_default)

def classify_switch (ty : type) : classify_switch_cases :=
  match ty with
  | .Tint _ _ _ => .switch_case_i
  | .Tlong _ _ => .switch_case_l
  | _ => .switch_default

def sem_switch_arg (v : val) (ty : type) : Option Z :=
  match classify_switch ty with
  | .switch_case_i => match v with | .Vint n => some (Int.unsigned n) | _ => none
  | .switch_case_l => match v with | .Vlong n => some (Int64.unsigned n) | _ => none
  | .switch_default => none

def sem_unary_operation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (op : unary_operation) (v : val) (ty : type) (m : mem) : Option val :=
  match op with
  | .Onotbool => sem_notbool v ty m
  | .Onotint => sem_notint v ty
  | .Oneg => sem_neg v ty
  | .Oabsfloat => sem_absfloat (binary64_certificate := binary64_certificate) v ty

def sem_binary_operation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cenv : composite_env) (op : binary_operation)
    (v1 : val) (t1 : type) (v2 : val) (t2 : type) (m : mem) : Option val :=
  match op with
  | .Oadd => sem_add (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cenv v1 t1 v2 t2 m
  | .Osub => sem_sub (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cenv v1 t1 v2 t2 m
  | .Omul => sem_mul (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Odiv => sem_div (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Omod => sem_mod (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Oand => sem_and (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Oor => sem_or (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Oxor => sem_xor (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) v1 t1 v2 t2 m
  | .Oshl => sem_shl v1 t1 v2 t2
  | .Oshr => sem_shr v1 t1 v2 t2
  | .Oeq => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Ceq v1 t1 v2 t2 m
  | .One => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Cne v1 t1 v2 t2 m
  | .Olt => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Clt v1 t1 v2 t2 m
  | .Ogt => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Cgt v1 t1 v2 t2 m
  | .Ole => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Cle v1 t1 v2 t2 m
  | .Oge => sem_cmp (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) Cge v1 t1 v2 t2 m

def sem_incrdecr
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cenv : composite_env) (id : incr_or_decr) (v : val) (ty : type) (m : mem) : Option val :=
  match id with
  | .Incr => sem_add (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cenv v ty (.Vint Int.one) type_int32s m
  | .Decr => sem_sub (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) cenv v ty (.Vint Int.one) type_int32s m

def incrdecr_type (ty : type) : type :=
  match typeconv ty with
  | .Tpointer ty a => .Tpointer ty a
  | .Tint sz sg _ => .Tint sz sg noattr
  | .Tlong sg _ => .Tlong sg noattr
  | .Tfloat sz _ => .Tfloat sz noattr
  | _ => .Tvoid

def chunk_for_carrier (sz : intsize) : memory_chunk :=
  match sz with
  | .I8 | .IBool => .Mint8unsigned
  | .I16 => .Mint16unsigned
  | .I32 => .Mint32

def bitsize_carrier (sz : intsize) : Z :=
  match sz with
  | .I8 | .IBool => zOfNat 8
  | .I16 => zOfNat 16
  | .I32 => zOfNat 32

def first_bit (sz : intsize) (pos width : Z) : Z :=
  if CompCert4Lean.X86_64.Archi.big_endian then zSub (zSub (bitsize_carrier sz) pos) width else pos

def bitfield_extract (sz : intsize) (sg : signedness) (pos width : Z) (c : CCInt) : CCInt :=
  if intsizeEq sz .IBool || signednessEq sg .Unsigned then
    CompCert4Lean.Lib.Integers.Int.unsigned_bitfield_extract (first_bit sz pos width) width c
  else CompCert4Lean.Lib.Integers.Int.signed_bitfield_extract (first_bit sz pos width) width c

def bitfield_normalize (sz : intsize) (sg : signedness) (width : Z) (n : CCInt) : CCInt :=
  if intsizeEq sz .IBool || signednessEq sg .Unsigned then Int.zero_ext width n else Int.sign_ext width n

inductive load_bitfield : type → intsize → signedness → Z → Z → mem → val → val → Prop where
  | load_bitfield_intro
      (sz : intsize) (sg1 : signedness) (attr : attr) (sg : signedness)
      (pos width : Z) (m : mem) (addr : val) (c : CCInt)
      (hpos : zLe z0 pos)
      (hwidth : zLt z0 width ∧ zLe width (bitsize_intsize sz))
      (hcarrier : zLe (zAdd pos width) (bitsize_carrier sz))
      (hsg : sg1 = (if zltBool width (bitsize_intsize sz) then .Signed else sg))
      (hload : Mem.loadv (chunk_for_carrier sz) m addr = some (.Vint c)) :
      load_bitfield (.Tint sz sg1 attr) sz sg pos width m addr
        (.Vint (bitfield_extract sz sg pos width c))

export load_bitfield (load_bitfield_intro)

inductive store_bitfield : type → intsize → signedness → Z → Z → mem → val → val → mem → val → Prop where
  | store_bitfield_intro
      (sz : intsize) (sg1 : signedness) (attr : attr) (sg : signedness)
      (pos width : Z) (m : mem) (addr : val) (c n : CCInt) (m' : mem)
      (hpos : zLe z0 pos)
      (hwidth : zLt z0 width ∧ zLe width (bitsize_intsize sz))
      (hcarrier : zLe (zAdd pos width) (bitsize_carrier sz))
      (hsg : sg1 = (if zltBool width (bitsize_intsize sz) then .Signed else sg))
      (hload : Mem.loadv (chunk_for_carrier sz) m addr = some (.Vint c))
      (hstore : Mem.storev (chunk_for_carrier sz) m addr
        (.Vint (CompCert4Lean.Lib.Integers.Int.bitfield_insert (first_bit sz pos width) width c n)) = some m') :
      store_bitfield (.Tint sz sg1 attr) sz sg pos width m addr (.Vint n)
        m' (.Vint (bitfield_normalize sz sg width n))

export store_bitfield (store_bitfield_intro)

/-! ## Compatibility with extensions and injections -/

def optval_self_injects (ov : Option val) : Prop :=
  match ov with
  | some (.Vptr _ _) => False
  | _ => True

/-! ## Properties of casted values -/

inductive val_casted : val → type → Prop where
  | val_casted_int
      (sz : intsize) (si : signedness) (attr : attr) (n : CCInt)
      (hcast : cast_int_int sz si n = n) :
      val_casted (.Vint n) (.Tint sz si attr)
  | val_casted_float
      (attr : attr) (n : CCFloat) :
      val_casted (.Vfloat n) (.Tfloat .F64 attr)
  | val_casted_single
      (attr : attr) (n : CCFloat32) :
      val_casted (.Vsingle n) (.Tfloat .F32 attr)
  | val_casted_long
      (si : signedness) (attr : attr) (n : CCInt64) :
      val_casted (.Vlong n) (.Tlong si attr)
  | val_casted_ptr_ptr
      (b : block) (ofs : Ptrofs) (ty : type) (attr : attr) :
      val_casted (.Vptr b ofs) (.Tpointer ty attr)
  | val_casted_int_ptr
      (n : CCInt) (ty : type) (attr : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = false) :
      val_casted (.Vint n) (.Tpointer ty attr)
  | val_casted_ptr_int
      (b : block) (ofs : Ptrofs) (si : signedness) (attr : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = false) :
      val_casted (.Vptr b ofs) (.Tint .I32 si attr)
  | val_casted_long_ptr
      (n : CCInt64) (ty : type) (attr : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = true) :
      val_casted (.Vlong n) (.Tpointer ty attr)
  | val_casted_ptr_long
      (b : block) (ofs : Ptrofs) (si : signedness) (attr : attr)
      (hptr64 : CompCert4Lean.X86_64.Archi.ptr64 = true) :
      val_casted (.Vptr b ofs) (.Tlong si attr)
  | val_casted_struct
      (id : ident) (attr : attr) (b : block) (ofs : Ptrofs) :
      val_casted (.Vptr b ofs) (.Tstruct id attr)
  | val_casted_union
      (id : ident) (attr : attr) (b : block) (ofs : Ptrofs) :
      val_casted (.Vptr b ofs) (.Tunion id attr)
  | val_casted_void
      (v : val) :
      val_casted v .Tvoid

export val_casted (val_casted_int val_casted_float val_casted_single val_casted_long
  val_casted_ptr_ptr val_casted_int_ptr val_casted_ptr_int val_casted_long_ptr
  val_casted_ptr_long val_casted_struct val_casted_union val_casted_void)

/-! Later-proof exact statement descriptors. -/

def sem_cast_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    ∀ v1 ty1 ty v tv1,
      sem_cast v1 ty1 ty m = some v →
      Val.inject f v1 tv1 →
      ∃ tv, sem_cast tv1 ty1 ty m' = some tv ∧ Val.inject f v tv

def bool_val_injStatement : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    ∀ v ty b tv,
      bool_val v ty m = some b →
      Val.inject f v tv →
      bool_val tv ty m' = some b

def sem_unary_operation_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)] : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    ∀ op v1 ty v tv1,
      sem_unary_operation op v1 ty m = some v →
      Val.inject f v1 tv1 →
      ∃ tv, sem_unary_operation op tv1 ty m' = some tv ∧ Val.inject f v tv

def sem_binarith_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    ∀ (sem_int : signedness → CCInt → CCInt → Option val)
      (sem_long : signedness → CCInt64 → CCInt64 → Option val)
      (sem_float : CCFloat → CCFloat → Option val)
      (sem_single : CCFloat32 → CCFloat32 → Option val)
      v1 t1 v2 t2 v v1' v2',
      sem_binarith sem_int sem_long sem_float sem_single v1 t1 v2 t2 m = some v →
      Val.inject f v1 v1' → Val.inject f v2 v2' →
      (∀ sg n1 n2, optval_self_injects (sem_int sg n1 n2)) →
      (∀ sg n1 n2, optval_self_injects (sem_long sg n1 n2)) →
      (∀ n1 n2, optval_self_injects (sem_float n1 n2)) →
      (∀ n1 n2, optval_self_injects (sem_single n1 n2)) →
      ∃ v', sem_binarith sem_int sem_long sem_float sem_single v1' t1 v2' t2 m' = some v' ∧ Val.inject f v v'

def sem_shift_injectStatement : Prop :=
  ∀ (f : meminj)
    (sem_int : signedness → CCInt → CCInt → CCInt)
    (sem_long : signedness → CCInt64 → CCInt64 → CCInt64)
    v1 t1 v2 t2 v v1' v2',
    sem_shift sem_int sem_long v1 t1 v2 t2 = some v →
    Val.inject f v1 v1' → Val.inject f v2 v2' →
    ∃ v', sem_shift sem_int sem_long v1' t1 v2' t2 = some v' ∧ Val.inject f v v'

def sem_cmp_ptr_injStatement : Prop :=
  ∀ (f : meminj) (m m' : mem),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
      (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ c v1 v2 v tv1 tv2,
    cmp_ptr m c v1 v2 = some v →
    Val.inject f v1 tv1 → Val.inject f v2 tv2 →
    ∃ tv, cmp_ptr m' c tv1 tv2 = some tv ∧ Val.inject f v tv

def sem_cmp_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m'),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
      (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ cmp v1 tv1 ty1 v2 tv2 ty2 v,
    sem_cmp cmp v1 ty1 v2 ty2 m = some v →
    Val.inject f v1 tv1 → Val.inject f v2 tv2 →
    ∃ tv, sem_cmp cmp tv1 ty1 tv2 ty2 m' = some tv ∧ Val.inject f v tv

def sem_binary_operation_injStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m'),
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ b1 ofs b2 delta,
      f b1 = some (b2, delta) →
      Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
      (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) = true →
      Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) → f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ cenv op v1 ty1 v2 ty2 v tv1 tv2,
    sem_binary_operation cenv op v1 ty1 v2 ty2 m = some v →
    Val.inject f v1 tv1 → Val.inject f v2 tv2 →
    ∃ tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = some tv ∧ Val.inject f v tv

def sem_cast_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (v1 : val) (ty1 ty : type) (m : mem)
    (v tv1 : val) (tm : mem),
    sem_cast v1 ty1 ty m = some v →
    Val.inject f v1 tv1 →
    Mem.inject f m tm →
    ∃ tv, sem_cast tv1 ty1 ty tm = some tv ∧ Val.inject f v tv

def sem_unary_operation_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)] : Prop :=
  ∀ (f : meminj) (m m' : mem) op v1 ty1 v tv1,
    sem_unary_operation op v1 ty1 m = some v →
    Val.inject f v1 tv1 →
    Mem.inject f m m' →
    ∃ tv, sem_unary_operation op tv1 ty1 m' = some tv ∧ Val.inject f v tv

def sem_binary_operation_injectStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (f : meminj) (m m' : mem) cenv op v1 ty1 v2 ty2 v tv1 tv2,
    sem_binary_operation cenv op v1 ty1 v2 ty2 m = some v →
    Val.inject f v1 tv1 → Val.inject f v2 tv2 →
    Mem.inject f m m' →
    ∃ tv, sem_binary_operation cenv op tv1 ty1 tv2 ty2 m' = some tv ∧ Val.inject f v tv

def bool_val_injectStatement : Prop :=
  ∀ (f : meminj) (m m' : mem) v ty b tv,
    bool_val v ty m = some b → Val.inject f v tv → Mem.inject f m m' → bool_val tv ty m' = some b

def cast_val_is_castedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty ty' v' m, sem_cast v ty ty' m = some v' → val_casted v' ty'

def cast_val_castedStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty m, val_casted v ty → sem_cast v ty ty m = some v

def cast_idempotentStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ v ty ty' v' m, sem_cast v ty ty' m = some v' → sem_cast v' ty' ty' m = some v'

def val_casted_has_argtypeStatement : Prop :=
  ∀ v ty, val_casted v ty → Val.has_argtype v (argtype_of_type ty)

end CompCert4Lean.Cfrontend.Cop


namespace CompCert4Lean.Cfrontend.Cop

private theorem bool_val_inj_aux : bool_val_injStatement := by
  intro f m m' hweak v ty b tv hval hinj
  cases hinj with
  | inject_int n =>
      cases hclass : classify_bool ty <;>
        simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hval ⊢ <;>
        exact hval
  | inject_long n =>
      cases hclass : classify_bool ty <;>
        simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hval ⊢ <;>
        exact hval
  | inject_float x =>
      cases hclass : classify_bool ty <;> simp [bool_val, hclass] at hval ⊢ <;>
        exact hval
  | inject_single x =>
      cases hclass : classify_bool ty <;> simp [bool_val, hclass] at hval ⊢ <;>
        exact hval
  | val_inject_undef x =>
      cases hclass : classify_bool ty <;> simp [bool_val, hclass] at hval
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      cases hclass : classify_bool ty with
      | bool_case_i =>
          simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hval ⊢
      | bool_case_l =>
          simp [bool_val, hclass, CompCert4Lean.X86_64.Archi.ptr64] at hval ⊢
          have hp' := hweak b1 ofs1 b2 delta hmap hval.1
          rw [hval.2]
          simpa [hofs] using hp'
      | _ => simp [bool_val, hclass] at hval

theorem sem_unary_operation_inj :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)],
      sem_unary_operation_injStatement := by
  intro _binary64_certificate f m m' hweak op v1 ty v tv1 hsem hinj
  cases op with
  | Onotbool =>
      unfold sem_unary_operation sem_notbool at hsem ⊢
      cases hb : bool_val v1 ty m with
      | none => simp [hb] at hsem
      | some b =>
          simp [hb] at hsem ⊢
          have hb' := bool_val_inj_aux f m m' hweak v1 ty b tv1 hb hinj
          cases b <;> simp [hb']
          · rw [← hsem]
            exact Common.Values.Val.inject.inject_int _
          · rw [← hsem]
            exact Common.Values.Val.inject.inject_int _
  | Onotint =>
      unfold sem_unary_operation sem_notint at hsem ⊢
      cases hc : classify_notint ty <;> simp [hc] at hsem ⊢ <;>
        cases hinj <;> simp_all <;> try { subst v; constructor }
  | Oneg =>
      unfold sem_unary_operation sem_neg at hsem ⊢
      cases hc : classify_neg ty <;> simp [hc] at hsem ⊢ <;>
        cases hinj <;> simp_all <;> try { subst v; constructor }
  | Oabsfloat =>
      unfold sem_unary_operation sem_absfloat at hsem ⊢
      cases hc : classify_neg ty <;> simp [hc] at hsem ⊢ <;>
        cases hinj <;> simp_all <;> try { subst v; constructor }

end CompCert4Lean.Cfrontend.Cop



namespace CompCert4Lean.Cfrontend.Cop

theorem bool_val_inj : bool_val_injStatement := bool_val_inj_aux

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem sem_cast_inj :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      sem_cast_injStatement := by
  intro _binary64_certificate _binary32_certificate f m m' hweak v1 ty1 ty v tv1 hsem hinj
  unfold sem_cast at hsem ⊢
  cases hclass : classify_cast ty1 ty <;>
    rw [hclass] at hsem <;>
    cases hinj <;>
    simp_all [cast_int_int, cast_int_float, cast_int_single, cast_int_long,
      cast_float_int, cast_single_int, cast_long_float, cast_long_single,
      cast_float_long, cast_single_long] <;>
    try { subst v; constructor }
  case cast_case_pointer.inject_int =>
    rcases hsem with ⟨_, hv⟩
    subst v
    exact Common.Values.Val.inject.inject_int _
  case cast_case_pointer.inject_long =>
    rcases hsem with ⟨_, hv⟩
    subst v
    exact Common.Values.Val.inject.inject_long _
  case cast_case_pointer.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    subst v
    have hp : Common.Values.Val.inject f (Common.Values.Vptr b1 ofs1)
        (Common.Values.Vptr b2 ofs2) :=
      Common.Values.Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
    simpa [hofs] using hp
  case cast_case_f2i.inject_float sz2 si f0 =>
    rcases hsem with ⟨i, hi, hv⟩
    subst v
    refine ⟨Common.Values.Vint (cast_int_int sz2 si i), ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · exact Common.Values.Val.inject.inject_int _
  case cast_case_s2i.inject_single sz2 si f0 =>
    rcases hsem with ⟨i, hi, hv⟩
    subst v
    refine ⟨Common.Values.Vint (cast_int_int sz2 si i), ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · exact Common.Values.Val.inject.inject_int _
  case cast_case_f2l.inject_float si f0 =>
    rcases hsem with ⟨i, hi, hv⟩
    subst v
    refine ⟨Common.Values.Vlong i, ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · exact Common.Values.Val.inject.inject_long _
  case cast_case_s2l.inject_single si f0 =>
    rcases hsem with ⟨i, hi, hv⟩
    subst v
    refine ⟨Common.Values.Vlong i, ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · exact Common.Values.Val.inject.inject_long _
  case cast_case_i2bool.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    rcases hsem with ⟨hptr, hvalid, hv⟩
    have hvalid' := hweak b1 ofs1 b2 delta hmap hvalid
    subst v
    refine ⟨Common.Values.Vone, ?_, ?_⟩
    · exact ⟨by simpa [hofs] using hvalid', rfl⟩
    · exact Common.Values.Val.inject.inject_int _
  case cast_case_l2bool.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    rcases hsem with ⟨hptr, hvalid, hv⟩
    have hvalid' := hweak b1 ofs1 b2 delta hmap hvalid
    subst v
    refine ⟨Common.Values.Vone, ?_, ?_⟩
    · exact ⟨by simpa [hofs] using hvalid', rfl⟩
    · exact Common.Values.Val.inject.inject_int _
  case cast_case_struct.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    rcases hsem with ⟨hid, hv⟩
    subst v
    have hp : Common.Values.Val.inject f (Common.Values.Vptr b1 ofs1)
        (Common.Values.Vptr b2 ofs2) :=
      Common.Values.Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
    simpa [hofs] using hp
  case cast_case_union.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    rcases hsem with ⟨hid, hv⟩
    subst v
    have hp : Common.Values.Val.inject f (Common.Values.Vptr b1 ofs1)
        (Common.Values.Vptr b2 ofs2) :=
      Common.Values.Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
    simpa [hofs] using hp
  case cast_case_void.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
    subst v
    have hp : Common.Values.Val.inject f (Common.Values.Vptr b1 ofs1)
        (Common.Values.Vptr b2 ofs2) :=
      Common.Values.Val.inject.inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs
    simpa [hofs] using hp

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem sem_shift_inject : sem_shift_injectStatement := by
  intro f sem_int sem_long v1 t1 v2 t2 v v1' v2' hsem hinj1 hinj2
  cases hclass : classify_shift t1 t2 <;> simp [sem_shift, hclass] at hsem ⊢
  all_goals
    cases hinj1 <;> cases hinj2 <;> simp_all <;> rcases hsem with ⟨_, rfl⟩ <;> constructor

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem cast_val_casted :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      cast_val_castedStatement := by
  intro _binary64_certificate _binary32_certificate v ty m h
  cases h with
  | val_casted_int sz si attr n hcast =>
      cases sz with
      | I8 =>
          cases si <;>
            simpa [sem_cast, classify_cast, cast_int_int,
              CompCert4Lean.X86_64.Archi.ptr64] using hcast
      | I16 =>
          cases si <;>
            simpa [sem_cast, classify_cast, cast_int_int,
              CompCert4Lean.X86_64.Archi.ptr64] using hcast
      | I32 =>
          simp [sem_cast, classify_cast, cast_int_int,
            CompCert4Lean.X86_64.Archi.ptr64]
      | IBool =>
          cases si <;>
            cases hb : boolEqInt n Int.zero <;>
              simpa [sem_cast, classify_cast, cast_int_int,
                CompCert4Lean.X86_64.Archi.ptr64, hb] using hcast
  | val_casted_float attr n =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_single attr n =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_long si attr n =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_ptr_ptr b ofs ty attr =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_int_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_ptr_int b ofs si attr hptr64 =>
      simp [CompCert4Lean.X86_64.Archi.ptr64] at hptr64
  | val_casted_long_ptr n ty attr hptr64 =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_ptr_long b ofs si attr hptr64 =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_struct id attr b ofs =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_union id attr b ofs =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]
  | val_casted_void v =>
      simp [sem_cast, classify_cast, CompCert4Lean.X86_64.Archi.ptr64]

theorem val_casted_has_argtype : val_casted_has_argtypeStatement := by
  intro v ty h
  cases h with
  | val_casted_int sz si attr n hcast =>
      cases sz with
      | I8 =>
          cases si with
          | Signed =>
              change n = Int.sign_ext (zOfNat 8) n
              exact hcast.symm
          | Unsigned =>
              change n = Int.zero_ext (zOfNat 8) n
              exact hcast.symm
      | I16 =>
          cases si with
          | Signed =>
              change n = Int.sign_ext (zOfNat 16) n
              exact hcast.symm
          | Unsigned =>
              change n = Int.zero_ext (zOfNat 16) n
              exact hcast.symm
      | I32 =>
          simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
            CompCert4Lean.Common.Values.Val.has_argtype]
      | IBool =>
          cases hb : boolEqInt n Int.zero with
          | false =>
              right
              simpa [hb, cast_int_int] using hcast.symm
          | true =>
              left
              simpa [hb, cast_int_int] using hcast.symm
  | val_casted_float attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_single attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_long si attr n =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_ptr_ptr b ofs ty attr =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_int_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype, hptr64]
  | val_casted_ptr_int b ofs si attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype, hptr64]
  | val_casted_long_ptr n ty attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype, hptr64]
  | val_casted_ptr_long b ofs si attr hptr64 =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype, hptr64]
  | val_casted_struct id attr b ofs =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_union id attr b ofs =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]
  | val_casted_void v =>
      simp [CompCert4Lean.Cfrontend.Ctypes.argtype_of_type,
        CompCert4Lean.Common.Values.Val.has_argtype]

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem sem_binarith_inject :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      sem_binarith_injectStatement := by
  intro _binary64_certificate _binary32_certificate f m m' hweak
    sem_int sem_long sem_float sem_single v1 t1 v2 t2 v v1' v2' hsem hinj1 hinj2
    hself_int hself_long hself_float hself_single
  have SELF : ∀ ov v, ov = some v → optval_self_injects ov → Common.Values.Val.inject f v v := by
    intro ov v0 hov hself
    subst ov
    cases v0 with
    | Vptr b ofs => exact False.elim hself
    | Vundef => exact Common.Values.Val.inject.val_inject_undef _
    | Vint n => exact Common.Values.Val.inject.inject_int _
    | Vlong n => exact Common.Values.Val.inject.inject_long _
    | Vfloat x => exact Common.Values.Val.inject.inject_float _
    | Vsingle x => exact Common.Values.Val.inject.inject_single _
  unfold sem_binarith at hsem ⊢
  let c := classify_binarith t1 t2
  let t := binarith_type c
  change (match sem_cast v1 t1 t m with
    | none => none
    | some v1' => match sem_cast v2 t2 t m with
      | none => none
      | some v2' => match c with
        | .bin_case_i sg => match v1', v2' with | .Vint n1, .Vint n2 => sem_int sg n1 n2 | _, _ => none
        | .bin_case_f => match v1', v2' with | .Vfloat n1, .Vfloat n2 => sem_float n1 n2 | _, _ => none
        | .bin_case_s => match v1', v2' with | .Vsingle n1, .Vsingle n2 => sem_single n1 n2 | _, _ => none
        | .bin_case_l sg => match v1', v2' with | .Vlong n1, .Vlong n2 => sem_long sg n1 n2 | _, _ => none
        | .bin_default => none) = some v at hsem
  cases hc1 : sem_cast v1 t1 t m with
  | none => simp [hc1] at hsem
  | some w1 =>
      cases hc2 : sem_cast v2 t2 t m with
      | none => simp [hc1, hc2] at hsem
      | some w2 =>
          have hi1 := sem_cast_inj (binary64_certificate := _binary64_certificate)
            (binary32_certificate := _binary32_certificate) f m m' hweak v1 t1 t w1 v1' hc1 hinj1
          have hi2 := sem_cast_inj (binary64_certificate := _binary64_certificate)
            (binary32_certificate := _binary32_certificate) f m m' hweak v2 t2 t w2 v2' hc2 hinj2
          rcases hi1 with ⟨w1', hc1', hinj1'⟩
          rcases hi2 with ⟨w2', hc2', hinj2'⟩
          dsimp [c, t] at hsem ⊢
          cases hcase : classify_binarith t1 t2 with
          | bin_case_i sg =>
              rw [hcase] at hsem
              have ht : t = binarith_type (.bin_case_i sg) := by
                dsimp [t, c]
                rw [hcase]
              rw [ht] at hc1 hc2 hc1' hc2'
              have hc1'' : sem_cast v1' t1 (binarith_type (.bin_case_i sg)) m' = some w1' := by
                simpa [hcase] using hc1'
              have hc2'' : sem_cast v2' t2 (binarith_type (.bin_case_i sg)) m' = some w2' := by
                simpa [hcase] using hc2'
              cases hinj1' with
              | inject_int n1 =>
                  cases hinj2' with
                  | inject_int n2 =>
                      rw [hc1, hc2] at hsem
                      simp [hcase] at hsem
                      have hself' : optval_self_injects (some v) := by
                        rw [← hsem]
                        exact hself_int sg n1 n2
                      refine ⟨v, ?_, SELF (some v) v rfl hself'⟩
                      simpa [hc1'', hc2'', hcase] using hsem
                  | _ =>
                      rw [hc1, hc2] at hsem
                      simp at hsem
              | _ =>
                  rw [hc1, hc2] at hsem
                  simp at hsem
          | bin_case_l sg =>
              rw [hcase] at hsem
              have ht : t = binarith_type (.bin_case_l sg) := by
                dsimp [t, c]
                rw [hcase]
              rw [ht] at hc1 hc2 hc1' hc2'
              have hc1'' : sem_cast v1' t1 (binarith_type (.bin_case_l sg)) m' = some w1' := by
                simpa [hcase] using hc1'
              have hc2'' : sem_cast v2' t2 (binarith_type (.bin_case_l sg)) m' = some w2' := by
                simpa [hcase] using hc2'
              cases hinj1' with
              | inject_long n1 =>
                  cases hinj2' with
                  | inject_long n2 =>
                      rw [hc1, hc2] at hsem
                      simp [hcase] at hsem
                      have hself' : optval_self_injects (some v) := by
                        rw [← hsem]
                        exact hself_long sg n1 n2
                      refine ⟨v, ?_, SELF (some v) v rfl hself'⟩
                      simpa [hc1'', hc2'', hcase] using hsem
                  | _ =>
                      rw [hc1, hc2] at hsem
                      simp at hsem
              | _ =>
                  rw [hc1, hc2] at hsem
                  simp at hsem
          | bin_case_f =>
              rw [hcase] at hsem
              have ht : t = binarith_type (.bin_case_f) := by
                dsimp [t, c]
                rw [hcase]
              rw [ht] at hc1 hc2 hc1' hc2'
              have hc1'' : sem_cast v1' t1 (binarith_type (.bin_case_f)) m' = some w1' := by
                simpa [hcase] using hc1'
              have hc2'' : sem_cast v2' t2 (binarith_type (.bin_case_f)) m' = some w2' := by
                simpa [hcase] using hc2'
              cases hinj1' with
              | inject_float n1 =>
                  cases hinj2' with
                  | inject_float n2 =>
                      rw [hc1, hc2] at hsem
                      simp [hcase] at hsem
                      have hself' : optval_self_injects (some v) := by
                        rw [← hsem]
                        exact hself_float n1 n2
                      refine ⟨v, ?_, SELF (some v) v rfl hself'⟩
                      simpa [hc1'', hc2'', hcase] using hsem
                  | _ =>
                      rw [hc1, hc2] at hsem
                      simp at hsem
              | _ =>
                  rw [hc1, hc2] at hsem
                  simp at hsem
          | bin_case_s =>
              rw [hcase] at hsem
              have ht : t = binarith_type (.bin_case_s) := by
                dsimp [t, c]
                rw [hcase]
              rw [ht] at hc1 hc2 hc1' hc2'
              have hc1'' : sem_cast v1' t1 (binarith_type (.bin_case_s)) m' = some w1' := by
                simpa [hcase] using hc1'
              have hc2'' : sem_cast v2' t2 (binarith_type (.bin_case_s)) m' = some w2' := by
                simpa [hcase] using hc2'
              cases hinj1' with
              | inject_single n1 =>
                  cases hinj2' with
                  | inject_single n2 =>
                      rw [hc1, hc2] at hsem
                      simp [hcase] at hsem
                      have hself' : optval_self_injects (some v) := by
                        rw [← hsem]
                        exact hself_single n1 n2
                      refine ⟨v, ?_, SELF (some v) v rfl hself'⟩
                      simpa [hc1'', hc2'', hcase] using hsem
                  | _ =>
                      rw [hc1, hc2] at hsem
                      simp at hsem
              | _ =>
                  rw [hc1, hc2] at hsem
                  simp at hsem
          | bin_default =>
              have ht : t = binarith_type (.bin_default) := by
                dsimp [t, c]
                rw [hcase]
              rw [ht] at hc1 hc2
              rw [hcase] at hsem
              rw [hc1, hc2] at hsem
              simp at hsem


end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem cmp_inj_repr_pos (p : positive) :
    (WordCore.repr 64 (.Zpos p)).intval = zOfNat (posToNat p % 2^64) := by
  change zOfNat (_ % 2^64) = zOfNat _
  congr 1
  congr 1
  induction p with
  | xH => rfl
  | xI p ih => change 2 * _ + 1 = 2 * _ + 1; rw [ih]
  | xO p ih => change 2 * _ = 2 * _; rw [ih]

private theorem cmp_inj_unsigned_repr (z : Z)
    (hz : zLe z0 z ∧ zLe z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  cases z with
  | Z0 => rfl
  | Zpos p =>
      have hmax := hz.2
      change (posToNat p : _root_.Int) ≤ 18446744073709551615 at hmax
      have hp : posToNat p < 2^64 := by omega
      change (WordCore.repr 64 (.Zpos p)).intval = .Zpos p
      rw [cmp_inj_repr_pos, Nat.mod_eq_of_lt hp]
      exact ZArith.Znat.positive_nat_Z p
  | Zneg p =>
      have hpos := posToNat_positive p
      have hmin := hz.1
      change (0 : _root_.Int) ≤ -(posToNat p : _root_.Int) at hmin
      omega

private theorem cmp_inj_unsigned_add (x d : Ptrofs)
    (h : zLe z0 (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) ∧
      zLe (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.add x d) = zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d) :=
  cmp_inj_unsigned_repr _ h

private theorem cmp_inj_ltu (x y : Ptrofs) :
    CompCert4Lean.Lib.Integers.Ptrofs.ltu x y =
      decide (intOfZ (Ptrofs.unsigned x) < intOfZ (Ptrofs.unsigned y)) := by
  unfold CompCert4Lean.Lib.Integers.Ptrofs.ltu WordCore.ltu
  run_tac
    let env ← Lean.MonadEnv.getEnv
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Integers.zltSelect" then
        let stx := Lean.mkIdent n
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $stx))
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Integers.sumboolSelect" then
        let stx := Lean.mkIdent n
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $stx))
  cases h : zlt (WordCore.unsigned x) (WordCore.unsigned y) with
  | left hlt => simp [h, show intOfZ (Ptrofs.unsigned x) < intOfZ (Ptrofs.unsigned y) from hlt]
  | right hge =>
      have hn : ¬ intOfZ (Ptrofs.unsigned x) < intOfZ (Ptrofs.unsigned y) :=
        _root_.Int.not_lt.mpr hge
      simp [h, hn]

private theorem cmp_inj_translate (c : comparison) (x y d : Ptrofs)
    (hx : zLe z0 (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) ∧
      zLe (zAdd (Ptrofs.unsigned x) (Ptrofs.unsigned d)) Ptrofs.max_unsigned)
    (hy : zLe z0 (zAdd (Ptrofs.unsigned y) (Ptrofs.unsigned d)) ∧
      zLe (zAdd (Ptrofs.unsigned y) (Ptrofs.unsigned d)) Ptrofs.max_unsigned) :
    CompCert4Lean.Lib.Integers.Ptrofs.cmpu c (Ptrofs.add x d) (Ptrofs.add y d) =
      CompCert4Lean.Lib.Integers.Ptrofs.cmpu c x y := by
  have heq : CompCert4Lean.Lib.Integers.Ptrofs.eq (Ptrofs.add x d) (Ptrofs.add y d) =
      CompCert4Lean.Lib.Integers.Ptrofs.eq x y := by
    change decide (Ptrofs.unsigned (Ptrofs.add x d) = Ptrofs.unsigned (Ptrofs.add y d)) =
      decide (Ptrofs.unsigned x = Ptrofs.unsigned y)
    rw [cmp_inj_unsigned_add x d hx, cmp_inj_unsigned_add y d hy]
    congr 1
    apply propext
    constructor
    · intro h
      apply intOfZ_injective
      have hh := congrArg intOfZ h
      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at hh
      omega
    · intro h; rw [h]
  have hlt : ∀ a b : Ptrofs,
      Ptrofs.unsigned (Ptrofs.add a d) = zAdd (Ptrofs.unsigned a) (Ptrofs.unsigned d) →
      Ptrofs.unsigned (Ptrofs.add b d) = zAdd (Ptrofs.unsigned b) (Ptrofs.unsigned d) →
      CompCert4Lean.Lib.Integers.Ptrofs.ltu (Ptrofs.add a d) (Ptrofs.add b d) =
        CompCert4Lean.Lib.Integers.Ptrofs.ltu a b := by
    intro a b ha hb
    rw [cmp_inj_ltu, cmp_inj_ltu, ha, hb]
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt, _root_.Int.add_lt_add_iff_right]
  have hxy := hlt x y (cmp_inj_unsigned_add x d hx) (cmp_inj_unsigned_add y d hy)
  have hyx := hlt y x (cmp_inj_unsigned_add y d hy) (cmp_inj_unsigned_add x d hx)
  cases c <;> simp only [CompCert4Lean.Lib.Integers.Ptrofs.cmpu, heq, hxy, hyx]

private theorem cmp_inj_ptrs (m : mem) (c : comparison) (b1 b2 : block) (o1 o2 : Ptrofs) :
    Val.cmplu_bool (Mem.valid_pointer m) c (.Vptr b1 o1) (.Vptr b2 o2) =
      (if b1 = b2 then
        if Mem.weak_valid_pointer m b1 (Ptrofs.unsigned o1) &&
           Mem.weak_valid_pointer m b2 (Ptrofs.unsigned o2) then
          some (CompCert4Lean.Lib.Integers.Ptrofs.cmpu c o1 o2) else none
       else if Mem.valid_pointer m b1 (Ptrofs.unsigned o1) &&
               Mem.valid_pointer m b2 (Ptrofs.unsigned o2) then
         Val.cmp_different_blocks c else none) := by
  unfold Val.cmplu_bool
  run_tac
    let env ← Lean.MonadEnv.getEnv
    for (n, _) in env.constants.toList do
      if (toString n).endsWith "Values.boolOfSumbool" then
        let stx := Lean.mkIdent n
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $stx))
  cases h : eq_block b1 b2 with
  | left he => simp [h, he, Mem.weak_valid_pointer, CompCert4Lean.X86_64.Archi.ptr64]
  | right hn => simp [h, hn, Mem.weak_valid_pointer, CompCert4Lean.X86_64.Archi.ptr64]

private theorem cmp_inj_pointer : sem_cmp_ptr_injStatement := by
  intro f m m' hv hw ho hd c v1 v2 v tv1 tv2 hcmp hi1 hi2
  have hb : ∀ c v1 v2 tv1 tv2 b,
      Val.inject f v1 tv1 → Val.inject f v2 tv2 →
      Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 = some b →
      Val.cmplu_bool (Mem.valid_pointer m') c tv1 tv2 = some b := by
    intro c v1 v2 tv1 tv2 b hi1 hi2 hc
    cases hi1 <;> cases hi2 <;>
      try { simp [Val.cmplu_bool] at hc }
    case inject_long.inject_long n1 n2 => exact hc
    case inject_long.inject_ptr n b1 o1 b2 o2 d hf he =>
      subst o2
      change (if Int64.eq n Int64.zero && Mem.weak_valid_pointer m b1 (Ptrofs.unsigned o1)
        then Val.cmp_different_blocks c else none) = some b at hc
      change (if Int64.eq n Int64.zero &&
        Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add o1 (Ptrofs.repr d)))
        then Val.cmp_different_blocks c else none) = some b
      split at hc
      · rename_i hh
        have hh' := Bool.and_eq_true_iff.mp hh
        rw [hh'.1, hw b1 o1 b2 d hf hh'.2]
        exact hc
      · cases hc
    case inject_ptr.inject_long b1 o1 b2 o2 d hf he n =>
      subst o2
      change (if Int64.eq n Int64.zero && Mem.weak_valid_pointer m b1 (Ptrofs.unsigned o1)
        then Val.cmp_different_blocks c else none) = some b at hc
      change (if Int64.eq n Int64.zero &&
        Mem.weak_valid_pointer m' b2 (Ptrofs.unsigned (Ptrofs.add o1 (Ptrofs.repr d)))
        then Val.cmp_different_blocks c else none) = some b
      split at hc
      · rename_i hh
        have hh' := Bool.and_eq_true_iff.mp hh
        rw [hh'.1, hw b1 o1 b2 d hf hh'.2]
        exact hc
      · cases hc
    case inject_ptr.inject_ptr b1 o1 t1 u1 d1 hf1 he1 b2 o2 t2 u2 d2 hf2 he2 =>
      subst u1 u2
      rw [cmp_inj_ptrs] at hc ⊢
      by_cases hs : b1 = b2
      · subst b2
        have he := Option.some.inj (hf1.symm.trans hf2)
        cases he
        simp only [ite_true] at hc ⊢
        split at hc
        · rename_i hh
          have hh' := Bool.and_eq_true_iff.mp hh
          rw [hw b1 o1 t1 d1 hf1 hh'.1, hw b1 o2 t1 d1 hf1 hh'.2]
          simp only [Bool.and_self, ite_true]
          rw [cmp_inj_translate c o1 o2 (Ptrofs.repr d1)
            (ho b1 o1 t1 d1 hf1 hh'.1) (ho b1 o2 t1 d1 hf1 hh'.2)]
          exact hc
        · cases hc
      · rw [if_neg hs] at hc
        split at hc
        · rename_i hh
          have hh' := Bool.and_eq_true_iff.mp hh
          by_cases ht : t1 = t2
          · subst t2
            simp only [ite_true]
            have hw1 : Mem.weak_valid_pointer m b1 (Ptrofs.unsigned o1) = true := by
              simp [Mem.weak_valid_pointer, hh'.1]
            have hw2 : Mem.weak_valid_pointer m b2 (Ptrofs.unsigned o2) = true := by
              simp [Mem.weak_valid_pointer, hh'.2]
            rw [hw b1 o1 t1 d1 hf1 hw1, hw b2 o2 t1 d2 hf2 hw2]
            simp only [Bool.and_self, ite_true]
            have hdiff := hd b1 o1 b2 o2 t1 d1 t1 d2 hs hh'.1 hh'.2 hf1 hf2
            have hne := hdiff.resolve_left (fun h => h rfl)
            have heq : CompCert4Lean.Lib.Integers.Ptrofs.eq
                (Ptrofs.add o1 (Ptrofs.repr d1)) (Ptrofs.add o2 (Ptrofs.repr d2)) = false := by
              exact decide_eq_false hne
            cases c <;> simp [Val.cmp_different_blocks] at hc <;>
              simp [CompCert4Lean.Lib.Integers.Ptrofs.cmpu, heq, hc]
          · rw [if_neg ht, hv b1 o1 t1 d1 hf1 hh'.1, hv b2 o2 t2 d2 hf2 hh'.2]
            exact hc
        · cases hc
  unfold cmp_ptr at hcmp ⊢
  simp only [CompCert4Lean.X86_64.Archi.ptr64, ite_true] at hcmp ⊢
  cases hbool : Val.cmplu_bool (Mem.valid_pointer m) c v1 v2 with
  | none => simp [hbool] at hcmp
  | some b =>
      simp only [hbool, Option.map_some, Option.some.injEq] at hcmp
      subst v
      refine ⟨Val.of_bool b, ?_, ?_⟩
      · rw [hb c v1 v2 tv1 tv2 b hi1 hi2 hbool]
        rfl
      · cases b <;> exact Val.inject.inject_int _

private theorem cmp_inj_bool_self (b : Bool) : optval_self_injects (some (Val.of_bool b)) := by
  cases b <;> trivial

theorem sem_cmp_inj :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      sem_cmp_injStatement := by
  intro _binary64_certificate _binary32_certificate f m m' hv hw ho hd
    c v1 tv1 ty1 v2 tv2 ty2 v hsem hi1 hi2
  have hp := cmp_inj_pointer f m m' hv hw ho hd
  unfold sem_cmp at hsem ⊢
  cases hc : classify_cmp ty1 ty2 with
  | cmp_case_pp =>
      simp only [hc] at hsem ⊢
      exact hp c v1 v2 v tv1 tv2 hsem hi1 hi2
  | cmp_case_pi si =>
      simp only [hc] at hsem ⊢
      cases hi2 with
      | inject_int n =>
          exact hp c v1 (Vptrofs (ptrofs_of_int si n)) v tv1
            (Vptrofs (ptrofs_of_int si n)) hsem hi1 (Val.inject.inject_long _)
      | _ => simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
  | cmp_case_ip si =>
      simp only [hc] at hsem ⊢
      cases hi1 with
      | inject_int n =>
          exact hp c (Vptrofs (ptrofs_of_int si n)) v2 v
            (Vptrofs (ptrofs_of_int si n)) tv2 hsem (Val.inject.inject_long _) hi2
      | _ => simp [CompCert4Lean.X86_64.Archi.ptr64] at hsem
  | cmp_case_pl =>
      simp only [hc] at hsem ⊢
      cases hi2 with
      | inject_long n =>
          exact hp c v1 (Vptrofs (Ptrofs.of_int64 n)) v tv1
            (Vptrofs (Ptrofs.of_int64 n)) hsem hi1 (Val.inject.inject_long _)
      | inject_ptr b1 o1 b2 o2 d hf he =>
          exact hp c v1 (.Vptr b1 o1) v tv1 (.Vptr b2 o2) hsem hi1
            (Val.inject.inject_ptr b1 o1 b2 o2 d hf he)
      | _ => simp at hsem
  | cmp_case_lp =>
      simp only [hc] at hsem ⊢
      cases hi1 with
      | inject_long n =>
          exact hp c (Vptrofs (Ptrofs.of_int64 n)) v2 v
            (Vptrofs (Ptrofs.of_int64 n)) tv2 hsem (Val.inject.inject_long _) hi2
      | inject_ptr b1 o1 b2 o2 d hf he =>
          exact hp c (.Vptr b1 o1) v2 v (.Vptr b2 o2) tv2 hsem
            (Val.inject.inject_ptr b1 o1 b2 o2 d hf he) hi2
      | _ => simp at hsem
  | cmp_default =>
      simp only [hc] at hsem ⊢
      exact sem_binarith_inject f m m' hw _ _ _ _ v1 ty1 v2 ty2 v tv1 tv2 hsem hi1 hi2
        (fun _ _ _ => cmp_inj_bool_self _) (fun _ _ _ => cmp_inj_bool_self _)
        (fun _ _ => cmp_inj_bool_self _) (fun _ _ => cmp_inj_bool_self _)

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open Lean Elab Tactic Meta

private abbrev copPtrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev copBlock := positive
private abbrev copMem := CompCert4Lean.Common.Memory.mem
private abbrev copMeminj := CompCert4Lean.Common.Values.Val.meminj
private abbrev copVal := CompCert4Lean.Common.Values.val
private abbrev copZLe := ZArith.BinInt.Z.le
private abbrev copZAdd := ZArith.BinInt.Z.add
private abbrev copZSub := ZArith.BinInt.Z.sub
private abbrev copZ0 : Z := .Z0
private abbrev copZ1 : Z := .Zpos .xH

private theorem cop_ptrofs_unsigned_range (i : copPtrofs) :
    copZLe copZ0 (Ptrofs.unsigned i) ∧ copZLe (Ptrofs.unsigned i) Ptrofs.max_unsigned := by
  have hnonneg := i.intrange.1
  have hlt := i.intrange.2
  constructor
  · change (-1 : Int) < intOfZ i.intval at hnonneg
    change 0 ≤ intOfZ i.intval
    omega
  · change intOfZ i.intval < intOfZ Ptrofs.modulus at hlt
    change intOfZ i.intval ≤ intOfZ Ptrofs.max_unsigned
    change intOfZ i.intval < (2 ^ Ptrofs.wordsize : Int) at hlt
    change intOfZ i.intval ≤ (2 ^ Ptrofs.wordsize : Int) - 1
    omega

private theorem cop_ptrofs_unsigned_repr (z : Z)
    (hz : copZLe copZ0 z ∧ copZLe z Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.repr z) = z := by
  have hzi : z = zOfInt (intOfZ z) := (zOfInt_intOfZ z).symm
  rw [hzi]
  change (CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
      (zOfInt (intOfZ z))).intval = zOfInt (intOfZ z)
  let w := CompCert4Lean.Lib.Integers.WordCore.repr Ptrofs.wordsize
      (zOfInt (intOfZ z))
  have hi : w.val = Int.toNat (intOfZ z % ((2 ^ Ptrofs.wordsize : Nat) : Int)) := by
    dsimp [w]
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.val_repr")
        | throwError "frozen WordCore.val_repr helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `z
      evalTactic
        (← `(tactic| exact $stx Ptrofs.wordsize
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ $arg)))
  have hwi : w.intval = ZArith.BinInt.Z.of_nat w.val := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.intval_eq_zOfNat_val")
        | throwError "frozen WordCore.intval_eq_zOfNat_val helper not found"
      let stx := Lean.mkIdent n
      let arg := Lean.mkIdent `w
      evalTactic (← `(tactic| exact $stx $arg))
  change w.intval = _
  rw [hwi, hi]
  have hznonneg : 0 ≤ intOfZ z := hz.1
  have hzmax := hz.2
  have hm : intOfZ Ptrofs.max_unsigned = (2 ^ Ptrofs.wordsize : Int) - 1 := by rfl
  have hzlt : intOfZ z < ((2 ^ Ptrofs.wordsize : Nat) : Int) := by
    change intOfZ z ≤ intOfZ Ptrofs.max_unsigned at hzmax
    rw [hm] at hzmax
    have hpcast : ((2 ^ Ptrofs.wordsize : Nat) : Int) = (2 : Int) ^ Ptrofs.wordsize := by
      exact (Int.natCast_pow 2 Ptrofs.wordsize).symm
    rw [hpcast]
    omega
  rw [Int.emod_eq_of_lt hznonneg hzlt]
  change zOfInt (↑(Int.toNat (intOfZ z)) : Int) = _
  rw [Int.toNat_of_nonneg hznonneg]

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common
open CompCert4Lean.Common.Values
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Memtype
open CompCert4Lean.Lib.Integers

private theorem cop_zadd_int (x y : Z) :
    intOfZ (copZAdd x y) = intOfZ x + intOfZ y := by
  change intOfZ (zOfInt (intOfZ x + intOfZ y)) = _
  rw [intOfZ_zOfInt]

private theorem cop_zsub_int (x y : Z) :
    intOfZ (copZSub x y) = intOfZ x - intOfZ y := by
  change intOfZ (zOfInt (intOfZ x - intOfZ y)) = _
  rw [intOfZ_zOfInt]

private theorem cop_ptrofs_add_unsigned (ofs : copPtrofs) (delta : Z)
    (hdelta : copZLe copZ0 delta ∧ copZLe delta Ptrofs.max_unsigned)
    (hsum : copZLe copZ0 (copZAdd (Ptrofs.unsigned ofs) delta) ∧
      copZLe (copZAdd (Ptrofs.unsigned ofs) delta) Ptrofs.max_unsigned) :
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) =
      copZAdd (Ptrofs.unsigned ofs) delta := by
  have hrepr_delta := cop_ptrofs_unsigned_repr delta hdelta
  have haddrepr : Ptrofs.add ofs (Ptrofs.repr delta) =
      Ptrofs.repr (copZAdd (Ptrofs.unsigned ofs)
        (Ptrofs.unsigned (Ptrofs.repr delta))) := by rfl
  rw [haddrepr, hrepr_delta]
  exact cop_ptrofs_unsigned_repr _ hsum

private theorem cop_weak_valid_pointer_inject_val
    (f : copMeminj) (m tm : copMem) (hmem : Mem.inject f m tm) :
    ∀ (b : copBlock) (ofs : copPtrofs) (b' : copBlock) (ofs' : copPtrofs),
      Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = true →
      Val.inject f (Vptr b ofs) (Vptr b' ofs') →
      Mem.weak_valid_pointer tm b' (Ptrofs.unsigned ofs') = true := by
  intro b ofs b' ofs' hvalid hinj
  cases hinj with
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      let b1 := b
      let ofs1 := ofs
      let b2 := b'
      subst ofs'
      rw [Mem.weak_valid_pointer_spec] at hvalid ⊢
      have hofs_range := cop_ptrofs_unsigned_range ofs1
      rcases hvalid with hvalid | hvalid
      · have hperm : Mem.perm m b1 (Ptrofs.unsigned ofs1) Cur Nonempty :=
          (Mem.valid_pointer_nonempty_perm m b1 (Ptrofs.unsigned ofs1)).mp hvalid
        have hperm_max := Mem.perm_cur_max m b1 (Ptrofs.unsigned ofs1) Nonempty hperm
        have hrep := hmem.mi_representable b1 b2 delta ofs1 hmap (Or.inl hperm_max)
        have hsum_max := hrep.2.2
        have hofs_nonneg := hofs_range.1
        have hdelta_max : copZLe delta Ptrofs.max_unsigned := by
          change intOfZ delta ≤ intOfZ Ptrofs.max_unsigned
          change intOfZ (copZAdd (Ptrofs.unsigned ofs1) delta) ≤
            intOfZ Ptrofs.max_unsigned at hsum_max
          change intOfZ (Ptrofs.unsigned ofs1) ≥ 0 at hofs_nonneg
          rw [cop_zadd_int] at hsum_max
          omega
        have hadd := cop_ptrofs_add_unsigned ofs1 delta ⟨hrep.1, hdelta_max⟩
          ⟨hrep.2.1, hrep.2.2⟩
        left
        apply (Mem.valid_pointer_nonempty_perm tm b2
          (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))).mpr
        rw [hadd]
        exact hmem.mi_inj.mi_perm b1 b2 delta (Ptrofs.unsigned ofs1) Cur Nonempty hmap hperm
      · have hperm : Mem.perm m b1 (copZSub (Ptrofs.unsigned ofs1) copZ1) Cur Nonempty :=
          (Mem.valid_pointer_nonempty_perm m b1 (copZSub (Ptrofs.unsigned ofs1) copZ1)).mp hvalid
        have hperm_max := Mem.perm_cur_max m b1 (copZSub (Ptrofs.unsigned ofs1) copZ1)
          Nonempty hperm
        have hrep := hmem.mi_representable b1 b2 delta ofs1 hmap (Or.inr hperm_max)
        have hsum_max := hrep.2.2
        have hofs_nonneg := hofs_range.1
        have hdelta_max : copZLe delta Ptrofs.max_unsigned := by
          change intOfZ delta ≤ intOfZ Ptrofs.max_unsigned
          change intOfZ (copZAdd (Ptrofs.unsigned ofs1) delta) ≤
            intOfZ Ptrofs.max_unsigned at hsum_max
          change intOfZ (Ptrofs.unsigned ofs1) ≥ 0 at hofs_nonneg
          rw [cop_zadd_int] at hsum_max
          omega
        have hadd := cop_ptrofs_add_unsigned ofs1 delta ⟨hrep.1, hdelta_max⟩
          ⟨hrep.2.1, hrep.2.2⟩
        right
        apply (Mem.valid_pointer_nonempty_perm tm b2
          (copZSub (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))) copZ1)).mpr
        have hshift : copZAdd (copZSub (Ptrofs.unsigned ofs1) copZ1) delta =
            copZSub (copZAdd (Ptrofs.unsigned ofs1) delta) copZ1 := by
          apply intOfZ_injective
          rw [cop_zadd_int, cop_zsub_int, cop_zsub_int, cop_zadd_int]
          omega
        rw [hadd, ← hshift]
        exact hmem.mi_inj.mi_perm b1 b2 delta (copZSub (Ptrofs.unsigned ofs1) copZ1)
          Cur Nonempty hmap hperm

theorem sem_cast_inject :
    ∀ [binary64_certificate :
        CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
          (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate :
        CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
          (zOfNat 24) (zOfNat 128)],
      sem_cast_injectStatement := by
  intro _binary64_certificate _binary32_certificate f v1 ty1 ty m v tv1 tm hsem hinj hmem
  exact sem_cast_inj (binary64_certificate := _binary64_certificate)
    (binary32_certificate := _binary32_certificate) f m tm
    (fun b ofs b' delta hmap hvalid =>
      cop_weak_valid_pointer_inject_val f m tm hmem b ofs b'
        (Ptrofs.add ofs (Ptrofs.repr delta)) hvalid
        (Val.inject.inject_ptr b ofs b' (Ptrofs.add ofs (Ptrofs.repr delta)) delta
          hmap rfl)) v1 ty1 ty v tv1 hsem hinj

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

theorem sem_unary_operation_inject :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)],
      sem_unary_operation_injectStatement := by
  intro _binary64_certificate f m m' op v1 ty1 v tv1 hsem hinj hmem
  exact sem_unary_operation_inj (binary64_certificate := _binary64_certificate) f m m'
    (fun b ofs b' delta hmap hvalid =>
      cop_weak_valid_pointer_inject_val f m m' hmem b ofs b'
        (Ptrofs.add ofs (Ptrofs.repr delta)) hvalid
        (Val.inject.inject_ptr b ofs b' (Ptrofs.add ofs (Ptrofs.repr delta)) delta
          hmap rfl)) op v1 ty1 v tv1 hsem hinj

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

theorem bool_val_inject : bool_val_injectStatement := by
  intro f m m' v ty b tv hval hinj hmem
  exact bool_val_inj f m m'
    (fun b1 ofs b2 delta hmap hvalid =>
      cop_weak_valid_pointer_inject_val f m m' hmem b1 ofs b2
        (Ptrofs.add ofs (Ptrofs.repr delta)) hvalid
        (Val.inject.inject_ptr b1 ofs b2
          (Ptrofs.add ofs (Ptrofs.repr delta)) delta hmap rfl))
    v ty b tv hval hinj

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values

private theorem cop_cast_int_int_idem_aux (sz : intsize) (sg : signedness) (i : CCInt) :
    cast_int_int sz sg (cast_int_int sz sg i) = cast_int_int sz sg i := by
  cases sz with
  | I8 =>
      cases sg with
      | Signed => exact CompCert4Lean.Lib.Integers.Int.sign_ext_idem_proof _ i (by change (0 : _root_.Int) < 8; decide)
      | Unsigned => exact CompCert4Lean.Lib.Integers.Int.zero_ext_idem_proof_api _ i (by change (0 : _root_.Int) ≤ 8; decide)
  | I16 =>
      cases sg with
      | Signed => exact CompCert4Lean.Lib.Integers.Int.sign_ext_idem_proof _ i (by change (0 : _root_.Int) < 16; decide)
      | Unsigned => exact CompCert4Lean.Lib.Integers.Int.zero_ext_idem_proof_api _ i (by change (0 : _root_.Int) ≤ 16; decide)
  | I32 => rfl
  | IBool =>
      cases h : boolEqInt i Int.zero <;> simp only [cast_int_int, h, Bool.false_eq_true, if_false, if_true] <;> rfl

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Common.Values

private theorem cop_cast_int_val_aux (sz : intsize) (sg : signedness) (a : attr)
    (i : CCInt) : val_casted (.Vint (cast_int_int sz sg i)) (.Tint sz sg a) :=
  val_casted_int sz sg a _ (cop_cast_int_int_idem_aux sz sg i)

private theorem cop_cast_bool_val_aux (b : Bool) (sg : signedness) (a : attr) :
    val_casted (.Vint (if b then Int.zero else Int.one)) (.Tint .IBool sg a) := by
  apply val_casted_int
  cases b <;> rfl

set_option maxHeartbeats 1600000 in
theorem cast_val_is_casted :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      cast_val_is_castedStatement := by
  intro _binary64_certificate _binary32_certificate v ty ty' v' m h
  cases ty
  case' Tint sz sg a => cases sz
  case' Tfloat fs a => cases fs
  all_goals
    cases ty'
    case' Tint sz sg a => cases sz
    case' Tfloat fs a => cases fs
    case' Tvoid => exact val_casted_void _
  all_goals
    cases v <;>
      simp only [sem_cast, classify_cast, intsizeEq,
        CompCert4Lean.X86_64.Archi.ptr64, if_true,
        Bool.not_true, Bool.false_eq_true, if_false] at h
  all_goals
    first
      | contradiction
      | (cases h; first
          | exact cop_cast_int_val_aux _ _ _ _
          | exact cop_cast_bool_val_aux _ _ _
          | solve | constructor <;> rfl)
      | (rcases Option.map_eq_some_iff.mp h with ⟨i, hi, rfl⟩
         first
          | exact cop_cast_int_val_aux _ _ _ _
          | solve | constructor <;> rfl)
      | (simp at h
         rcases h with ⟨_, rfl⟩
         first
          | exact cop_cast_bool_val_aux true _ _
          | exact cop_cast_bool_val_aux false _ _
          | solve | constructor <;> rfl)

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem cast_idempotent :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      cast_idempotentStatement := by
  intro _binary64_certificate _binary32_certificate v ty ty' v' m h
  apply cast_val_casted (binary64_certificate := _binary64_certificate)
    (binary32_certificate := _binary32_certificate)
  exact cast_val_is_casted (binary64_certificate := _binary64_certificate)
    (binary32_certificate := _binary32_certificate) v ty ty' v' m h

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

theorem sem_cmp_ptr_inj : sem_cmp_ptr_injStatement := cmp_inj_pointer

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Common.Values
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Integers

private theorem cop_add_ptr_int_inject
    (mapping : meminj) (composites : composite_env) (pointee : type)
    (sign : signedness) (first second result firstTarget secondTarget : val)
    (firstInjection : Val.inject mapping first firstTarget)
    (secondInjection : Val.inject mapping second secondTarget)
    (sourceResult : sem_add_ptr_int composites pointee sign first second = some result) :
    ∃ targetResult,
      sem_add_ptr_int composites pointee sign firstTarget secondTarget = some targetResult ∧
      Val.inject mapping result targetResult := by
  cases firstInjection <;> cases secondInjection <;>
    simp_all [sem_add_ptr_int, CompCert4Lean.X86_64.Archi.ptr64] <;> subst result
  · exact Val.inject.inject_long _
  · apply Val.inject.inject_ptr
    · assumption
    · simp only [Ptrofs.add_assoc_proof_api]
      congr 1
      exact Ptrofs.add_commut_proof_api _ _

private theorem cop_add_ptr_long_inject
    (mapping : meminj) (composites : composite_env) (pointee : type)
    (first second result firstTarget secondTarget : val)
    (firstInjection : Val.inject mapping first firstTarget)
    (secondInjection : Val.inject mapping second secondTarget)
    (sourceResult : sem_add_ptr_long composites pointee first second = some result) :
    ∃ targetResult,
      sem_add_ptr_long composites pointee firstTarget secondTarget = some targetResult ∧
      Val.inject mapping result targetResult := by
  cases firstInjection <;> cases secondInjection <;>
    simp_all [sem_add_ptr_long, CompCert4Lean.X86_64.Archi.ptr64] <;> subst result
  · exact Val.inject.inject_long _
  · apply Val.inject.inject_ptr
    · assumption
    · simp only [Ptrofs.add_assoc_proof_api]
      congr 1
      exact Ptrofs.add_commut_proof_api _ _

set_option maxHeartbeats 1600000 in
theorem sem_binary_operation_inj :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      sem_binary_operation_injStatement := by
  intro binary64Certificate binary32Certificate mapping sourceMemory targetMemory
    validPointers weakPointers noOverflow distinctPointers composites operation
    first firstType second secondType result firstTarget secondTarget
    sourceResult firstInjection secondInjection
  cases operation <;> simp only [sem_binary_operation] at sourceResult ⊢
  case Oadd =>
    unfold sem_add at sourceResult ⊢
    cases classification : classify_add firstType secondType <;>
      simp only [classification] at sourceResult ⊢
    · exact cop_add_ptr_int_inject mapping _ _ _ _ _ _ _ _
        firstInjection secondInjection sourceResult
    · exact cop_add_ptr_long_inject mapping _ _ _ _ _ _ _
        firstInjection secondInjection sourceResult
    · exact cop_add_ptr_int_inject mapping _ _ _ _ _ _ _ _
        secondInjection firstInjection sourceResult
    · exact cop_add_ptr_long_inject mapping _ _ _ _ _ _ _
        secondInjection firstInjection sourceResult
    · apply sem_binarith_inject mapping sourceMemory targetMemory weakPointers
        _ _ _ _ _ _ _ _ _ _ _ sourceResult firstInjection secondInjection <;>
        intros <;> trivial
  case Osub =>
    unfold sem_sub at sourceResult ⊢
    cases classification : classify_sub firstType secondType <;>
      simp only [classification] at sourceResult ⊢
    case sub_case_pi pointee sign =>
      cases firstInjection <;> cases secondInjection <;>
        simp_all [CompCert4Lean.X86_64.Archi.ptr64] <;> subst result
      · exact Val.inject.inject_long _
      · apply Val.inject.inject_ptr
        · assumption
        · exact Ptrofs.sub_add_l_proof_api _ _ _
    case sub_case_pl pointee =>
      cases firstInjection <;> cases secondInjection <;>
        simp_all [CompCert4Lean.X86_64.Archi.ptr64] <;> subst result
      · exact Val.inject.inject_long _
      · apply Val.inject.inject_ptr
        · assumption
        · exact Ptrofs.sub_add_l_proof_api _ _ _
    case sub_case_pp pointee =>
      cases firstInjection <;> cases secondInjection <;>
        dsimp only at sourceResult ⊢ <;> try contradiction
      rename_i firstBlock firstOffset firstTargetBlock firstTargetOffset firstDelta
        firstMapped firstShift secondBlock secondOffset secondTargetBlock
        secondTargetOffset secondDelta secondMapped secondShift
      subst firstTargetOffset secondTargetOffset
      split at sourceResult
      next sameBlock =>
        have sameBlock' : firstBlock = secondBlock := by
          change @Eq ident firstBlock secondBlock
          simpa only [identEq, decide_eq_true_eq] using sameBlock
        subst secondBlock
        have sameImage := Option.some.inj (firstMapped.symm.trans secondMapped)
        cases sameImage
        rw [if_pos (show identEq firstTargetBlock firstTargetBlock = true by
          simp only [identEq, decide_eq_true_eq])]
        split at sourceResult
        next sizeRange =>
          rw [if_pos sizeRange, Ptrofs.sub_shifted_proof_api]
          cases sourceResult
          exact ⟨_, rfl, Val.inject.inject_long _⟩
        next => cases sourceResult
      next => cases sourceResult
    case sub_default =>
      apply sem_binarith_inject mapping sourceMemory targetMemory weakPointers
        _ _ _ _ _ _ _ _ _ _ _ sourceResult firstInjection secondInjection <;>
        intros <;> trivial
  all_goals
    first
    | exact sem_cmp_inj mapping sourceMemory targetMemory validPointers weakPointers
        noOverflow distinctPointers _ _ _ _ _ _ _ _ sourceResult firstInjection secondInjection
    | exact sem_shift_inject mapping _ _ _ _ _ _ _ _ _
        sourceResult firstInjection secondInjection
    | (simp only [sem_mul, sem_div, sem_mod, sem_and, sem_or, sem_xor] at sourceResult ⊢
       apply sem_binarith_inject mapping sourceMemory targetMemory weakPointers
         _ _ _ _ _ _ _ _ _ _ _ sourceResult firstInjection secondInjection
       all_goals repeat first | trivial | split | intro _)

end CompCert4Lean.Cfrontend.Cop

namespace CompCert4Lean.Cfrontend.Cop

open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers

theorem sem_binary_operation_inject :
    ∀ [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
      [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)],
      sem_binary_operation_injectStatement := by
  intro binary64Certificate binary32Certificate mapping sourceMemory targetMemory
    composites operation first firstType second secondType result firstTarget secondTarget
    sourceResult firstInjection secondInjection memoryInjection
  refine sem_binary_operation_inj mapping sourceMemory targetMemory ?_ ?_ ?_ ?_
    composites operation first firstType second secondType result firstTarget secondTarget
    sourceResult firstInjection secondInjection
  · intro sourceBlock offset targetBlock delta mapped valid
    exact Mem.valid_pointer_inject_val mapping sourceMemory targetMemory
      sourceBlock offset targetBlock _ memoryInjection valid
      (Val.inject.inject_ptr sourceBlock offset targetBlock _ delta mapped rfl)
  · intro sourceBlock offset targetBlock delta mapped valid
    exact Mem.weak_valid_pointer_inject_val mapping sourceMemory targetMemory
      sourceBlock offset targetBlock _ memoryInjection valid
      (Val.inject.inject_ptr sourceBlock offset targetBlock _ delta mapped rfl)
  · intro sourceBlock offset targetBlock delta mapped valid
    exact Mem.weak_valid_pointer_inject_no_overflow mapping sourceMemory targetMemory
      sourceBlock offset targetBlock delta memoryInjection valid mapped
  · intro firstBlock firstOffset secondBlock secondOffset firstImage firstDelta
      secondImage secondDelta distinct firstValid secondValid firstMapped secondMapped
    exact Mem.different_pointers_inject mapping sourceMemory targetMemory
      firstBlock firstOffset secondBlock secondOffset firstImage firstDelta
      secondImage secondDelta memoryInjection distinct firstValid secondValid
      firstMapped secondMapped

end CompCert4Lean.Cfrontend.Cop
