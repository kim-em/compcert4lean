import CompCert4Lean.Common.AST
import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Floats
import CompCert4Lean.X86_64.Archi

/-!
  Definition-bearing translation of `common/Values.v`.

  The computational definitions below preserve the source-visible shape.  The
  proof declarations selected for later migration are represented by named
  proposition descriptors at the end of each relevant section.
-/

namespace CompCert4Lean.Common.Values

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats

private abbrev comparison := CompCert4Lean.Lib.Integers.comparison

namespace Archi
private abbrev ptr64 := CompCert4Lean.X86_64.Archi.ptr64
end Archi

namespace Int
private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int.mone
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev eq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev lt := CompCert4Lean.Lib.Integers.Int.lt
private abbrev ltu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int.add
private abbrev sub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev mul := CompCert4Lean.Lib.Integers.Int.mul
private abbrev divs := CompCert4Lean.Lib.Integers.Int.divs
private abbrev mods := CompCert4Lean.Lib.Integers.Int.mods
private abbrev divu := CompCert4Lean.Lib.Integers.Int.divu
private abbrev modu := CompCert4Lean.Lib.Integers.Int.modu
private abbrev negative := CompCert4Lean.Lib.Integers.Int.negative
private abbrev add_carry := CompCert4Lean.Lib.Integers.Int.add_carry
private abbrev sub_overflow := CompCert4Lean.Lib.Integers.Int.sub_overflow
private abbrev mulhs := CompCert4Lean.Lib.Integers.Int.mulhs
private abbrev mulhu := CompCert4Lean.Lib.Integers.Int.mulhu
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int.min_signed
private abbrev and := CompCert4Lean.Lib.Integers.Int.and
private abbrev or := CompCert4Lean.Lib.Integers.Int.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int.shr
private abbrev rol := CompCert4Lean.Lib.Integers.Int.rol
private abbrev ror := CompCert4Lean.Lib.Integers.Int.ror
private abbrev shrx := CompCert4Lean.Lib.Integers.Int.shrx
end Int

namespace Int64
private abbrev repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int64.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int64.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int64.mone
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
private abbrev mods := CompCert4Lean.Lib.Integers.Int64.mods
private abbrev divu := CompCert4Lean.Lib.Integers.Int64.divu
private abbrev modu := CompCert4Lean.Lib.Integers.Int64.modu
private abbrev negative := CompCert4Lean.Lib.Integers.Int64.negative
private abbrev add_carry := CompCert4Lean.Lib.Integers.Int64.add_carry
private abbrev sub_overflow := CompCert4Lean.Lib.Integers.Int64.sub_overflow
private abbrev mulhs := CompCert4Lean.Lib.Integers.Int64.mulhs
private abbrev mulhu := CompCert4Lean.Lib.Integers.Int64.mulhu
private abbrev min_signed := CompCert4Lean.Lib.Integers.Int64.min_signed
private abbrev and := CompCert4Lean.Lib.Integers.Int64.and
private abbrev or := CompCert4Lean.Lib.Integers.Int64.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int64.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int64.not
private abbrev shl' := CompCert4Lean.Lib.Integers.Int64.shl'
private abbrev shru' := CompCert4Lean.Lib.Integers.Int64.shru'
private abbrev shr' := CompCert4Lean.Lib.Integers.Int64.shr'
private abbrev rol := CompCert4Lean.Lib.Integers.Int64.rol
private abbrev ror := CompCert4Lean.Lib.Integers.Int64.ror
private abbrev shrx' := CompCert4Lean.Lib.Integers.Int64.shrx'
private abbrev loword := CompCert4Lean.Lib.Integers.Int64.loword
private abbrev hiword := CompCert4Lean.Lib.Integers.Int64.hiword
private abbrev ofwords := CompCert4Lean.Lib.Integers.Int64.ofwords
private abbrev mul' := CompCert4Lean.Lib.Integers.Int64.mul'
end Int64

namespace Float
private abbrev neg := CompCert4Lean.Lib.Floats.Float.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float.cmp
private abbrev to_int := CompCert4Lean.Lib.Floats.Float.to_int
private abbrev to_intu := CompCert4Lean.Lib.Floats.Float.to_intu
private abbrev to_long := CompCert4Lean.Lib.Floats.Float.to_long
private abbrev to_longu := CompCert4Lean.Lib.Floats.Float.to_longu
private abbrev of_int := CompCert4Lean.Lib.Floats.Float.of_int
private abbrev of_intu := CompCert4Lean.Lib.Floats.Float.of_intu
private abbrev of_long := CompCert4Lean.Lib.Floats.Float.of_long
private abbrev of_longu := CompCert4Lean.Lib.Floats.Float.of_longu
private abbrev to_single := CompCert4Lean.Lib.Floats.Float.to_single
private abbrev of_single := CompCert4Lean.Lib.Floats.Float.of_single
end Float

namespace Float32
private abbrev neg := CompCert4Lean.Lib.Floats.Float32.neg
private abbrev abs := CompCert4Lean.Lib.Floats.Float32.abs
private abbrev add := CompCert4Lean.Lib.Floats.Float32.add
private abbrev sub := CompCert4Lean.Lib.Floats.Float32.sub
private abbrev mul := CompCert4Lean.Lib.Floats.Float32.mul
private abbrev div := CompCert4Lean.Lib.Floats.Float32.div
private abbrev cmp := CompCert4Lean.Lib.Floats.Float32.cmp
private abbrev to_int := CompCert4Lean.Lib.Floats.Float32.to_int
private abbrev to_intu := CompCert4Lean.Lib.Floats.Float32.to_intu
private abbrev to_long := CompCert4Lean.Lib.Floats.Float32.to_long
private abbrev to_longu := CompCert4Lean.Lib.Floats.Float32.to_longu
private abbrev of_int := CompCert4Lean.Lib.Floats.Float32.of_int
private abbrev of_intu := CompCert4Lean.Lib.Floats.Float32.of_intu
private abbrev of_long := CompCert4Lean.Lib.Floats.Float32.of_long
private abbrev of_longu := CompCert4Lean.Lib.Floats.Float32.of_longu
end Float32

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32

private abbrev z0 : Z := ZArith.BinInt.Z.Z0
private abbrev z1 : Z := ZArith.BinInt.Z.Zpos xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zOpp := ZArith.BinInt.Z.opp
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zQuot := ZArith.BinInt.Z.quot
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLtb := ZArith.BinInt.Z.ltb
private abbrev zTwoP := two_p
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private def boolOfSumbool {P Q : Prop} (d : Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

private abbrev intZeroExt := CompCert4Lean.Lib.Integers.Int.zero_ext

private abbrev intSignExt := CompCert4Lean.Lib.Integers.Int.sign_ext

private abbrev int64SignExt := CompCert4Lean.Lib.Integers.Int64.sign_ext

private def intMulhs (x y : CCInt) : CCInt := Int.mulhs x y
private def intMulhu (x y : CCInt) : CCInt := Int.mulhu x y
private def int64Mulhs (x y : CCInt64) : CCInt64 := Int64.mulhs x y
private def int64Mulhu (x y : CCInt64) : CCInt64 := Int64.mulhu x y
private def intShrCarry (x y : CCInt) : CCInt := Int.shr x y
private def int64ShrCarry (x : CCInt64) (y : CCInt) : CCInt64 := Int64.shr' x y
private def intRolm (x amount mask : CCInt) : CCInt := Int.or (Int.rol x amount) mask
private def int64Rolm (x amount : CCInt) (mask : CCInt64) : CCInt64 :=
  Int64.or (Int64.rol (Int64.repr (Int.unsigned x)) (Int64.repr (Int.unsigned amount))) mask

abbrev block : Type := positive

def eq_block (x y : block) : Sumbool (x = y) (x ≠ y) :=
  CompCert4Lean.Lib.Coqlib.peq x y

inductive val : Type where
  | Vundef : val
  | Vint : CCInt → val
  | Vlong : CCInt64 → val
  | Vfloat : CCFloat → val
  | Vsingle : CCFloat32 → val
  | Vptr : block → Ptrofs → val
deriving DecidableEq

export val (Vundef Vint Vlong Vfloat Vsingle Vptr)

def Vzero : val := Vint Int.zero
def Vone : val := Vint Int.one
def Vtrue : val := Vint Int.one
def Vfalse : val := Vint Int.zero

def Vnullptr : val := if CompCert4Lean.X86_64.Archi.ptr64 then Vlong Int64.zero else Vint Int.zero

def Vptrofs (n : Ptrofs) : val :=
  if CompCert4Lean.X86_64.Archi.ptr64 then Vlong (Ptrofs.to_int64 n) else Vint (Ptrofs.to_int n)

namespace Val

def eq (x y : val) : Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

def has_type (v : val) (t : typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _, Tint => True
  | Vlong _, Tlong => True
  | Vfloat _, Tfloat => True
  | Vsingle _, Tsingle => True
  | Vptr _ _, Tint => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Vptr _ _, Tlong => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Vint _, Tany32 | Vsingle _, Tany32 => True
  | Vptr _ _, Tany32 => CompCert4Lean.X86_64.Archi.ptr64 = false
  | _, Tany64 => True
  | _, _ => False

def has_type_list : List val → List typ → Prop
  | [], [] => True
  | v :: vs, t :: ts => has_type v t ∧ has_type_list vs ts
  | _, _ => False

def Vptr_has_typeStatement : Prop := ∀ b ofs, has_type (Vptr b ofs) Tptr
def Vnullptr_has_typeStatement : Prop := has_type Vnullptr Tptr

def has_argtype (v : val) (x : xtype) : Prop :=
  match x, v with
  | Xbool, Vint n => n = Int.zero ∨ n = Int.one
  | Xint8signed, Vint n => n = intSignExt (zOfNat 8) n
  | Xint8unsigned, Vint n => n = intZeroExt (zOfNat 8) n
  | Xint16signed, Vint n => n = intSignExt (zOfNat 16) n
  | Xint16unsigned, Vint n => n = intZeroExt (zOfNat 16) n
  | Xint, Vint _ => True
  | Xint, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xlong, Vlong _ => True
  | Xlong, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Xfloat, Vfloat _ => True
  | Xsingle, Vsingle _ => True
  | Xptr, Vptr _ _ => True
  | Xptr, Vint _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xptr, Vlong _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Xany32, Vint _ | Xany32, Vsingle _ => True
  | Xany32, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xany64, Vint _ | Xany64, Vlong _ | Xany64, Vptr _ _
  | Xany64, Vsingle _ | Xany64, Vfloat _ => True
  | Xvoid, _ => True
  | _, _ => False

def has_argtype_list (vl : List val) (xl : List xtype) : Prop :=
  CompCert4Lean.Lib.Coqlib.list_forall2 has_argtype vl xl

def has_rettype (v : val) (r : xtype) : Prop :=
  match r, v with
  | Xbool, Vint n => n = Int.zero ∨ n = Int.one
  | Xint8signed, Vint n => n = intSignExt (zOfNat 8) n
  | Xint8unsigned, Vint n => n = intZeroExt (zOfNat 8) n
  | Xint16signed, Vint n => n = intSignExt (zOfNat 16) n
  | Xint16unsigned, Vint n => n = intZeroExt (zOfNat 16) n
  | Xint, Vint _ => True
  | Xint, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xlong, Vlong _ => True
  | Xlong, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Xfloat, Vfloat _ => True
  | Xsingle, Vsingle _ => True
  | Xptr, Vptr _ _ => True
  | Xptr, Vint _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xptr, Vlong _ => CompCert4Lean.X86_64.Archi.ptr64 = true
  | Xany32, Vint _ | Xany32, Vsingle _ => True
  | Xany32, Vptr _ _ => CompCert4Lean.X86_64.Archi.ptr64 = false
  | Xany64, _ => True
  | _, Vundef => True
  | _, _ => False

def has_subtypeStatement : Prop :=
  ∀ ty1 ty2 v,
    subtype ty1 ty2 = true → has_type v ty1 → has_type v ty2

def has_proj_xtypeStatement : Prop :=
  ∀ v t, has_rettype v t → has_type v (proj_xtype t)

def has_inj_typeStatement : Prop :=
  ∀ v t, has_type v t → has_rettype v (inj_type t)

inductive bool_of_val : val → Bool → Prop where
  | bool_of_val_int (n : CCInt) : bool_of_val (Vint n) (!(Int.eq n Int.zero))

abbrev bool_of_val_int (n : CCInt) : bool_of_val (Vint n) (!(Int.eq n Int.zero)) :=
  @bool_of_val.bool_of_val_int n

def neg (v : val) : val := match v with | Vint n => Vint (Int.neg n) | _ => Vundef
def negf (v : val) : val := match v with | Vfloat f => Vfloat (Float.neg f) | _ => Vundef
def absf (v : val) : val := match v with | Vfloat f => Vfloat (Float.abs f) | _ => Vundef
def negfs (v : val) : val := match v with | Vsingle f => Vsingle (Float32.neg f) | _ => Vundef
def absfs (v : val) : val := match v with | Vsingle f => Vsingle (Float32.abs f) | _ => Vundef
def maketotal (ov : Option val) : val := match ov with | some v => v | none => Vundef
def intoffloat (v : val) : Option val := match v with | Vfloat f => (Float.to_int f).map Vint | _ => none
def intuoffloat (v : val) : Option val := match v with | Vfloat f => (Float.to_intu f).map Vint | _ => none
def floatofint (v : val)
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 53) (zOfNat 1024)] : Option val :=
  match v with | Vint n => some (Vfloat (Float.of_int n)) | _ => none
def floatofintu (v : val)
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 53) (zOfNat 1024)] : Option val :=
  match v with | Vint n => some (Vfloat (Float.of_intu n)) | _ => none
def intofsingle (v : val) : Option val := match v with | Vsingle f => (Float32.to_int f).map Vint | _ => none
def intuofsingle (v : val) : Option val := match v with | Vsingle f => (Float32.to_intu f).map Vint | _ => none
def singleofint (v : val)
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 24) (zOfNat 128)] : Option val :=
  match v with | Vint n => some (Vsingle (Float32.of_int n)) | _ => none
def singleofintu (v : val)
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 24) (zOfNat 128)] : Option val :=
  match v with | Vint n => some (Vsingle (Float32.of_intu n)) | _ => none
def negint (v : val) : val := match v with | Vint n => Vint (Int.neg n) | _ => Vundef
def notint (v : val) : val := match v with | Vint n => Vint (Int.not n) | _ => Vundef
def of_bool (b : Bool) : val := if b then Vtrue else Vfalse
def is_bool (v : val) : Bool := boolOfSumbool (eq v Vtrue) || boolOfSumbool (eq v Vfalse)
def norm_bool (v : val) : val := if is_bool v then v else Vundef
def zero_ext (nbits : Z) (v : val) : val := match v with | Vint n => Vint (intZeroExt nbits n) | _ => Vundef
def sign_ext (nbits : Z) (v : val) : val := match v with | Vint n => Vint (intSignExt nbits n) | _ => Vundef
def singleoffloat (v : val) : val := match v with | Vfloat f => Vsingle (Float.to_single f) | _ => Vundef
def floatofsingle (v : val) : val := match v with | Vsingle f => Vfloat (Float.of_single f) | _ => Vundef

def add (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint (Int.add n1 n2)
  | Vptr b ofs, Vint n => if Archi.ptr64 then Vundef else Vptr b (Ptrofs.add ofs (Ptrofs.of_int n))
  | Vint n, Vptr b ofs => if Archi.ptr64 then Vundef else Vptr b (Ptrofs.add ofs (Ptrofs.of_int n))
  | _, _ => Vundef

def sub (v1 v2 : val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint (Int.sub n1 n2)
  | Vptr b ofs, Vint n => if Archi.ptr64 then Vundef else Vptr b (Ptrofs.sub ofs (Ptrofs.of_int n))
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if Archi.ptr64 then Vundef else
        if boolOfSumbool (eq_block b1 b2) then
          Vint (Ptrofs.to_int (Ptrofs.sub ofs1 ofs2))
        else Vundef
  | _, _ => Vundef

def mul (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.mul n1 n2) | _, _ => Vundef
def mulhs (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (intMulhs n1 n2) | _, _ => Vundef
def mulhu (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (intMulhu n1 n2) | _, _ => Vundef

def divs (v1 v2 : val) : Option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero ||
          (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone)
      then none
      else some (Vint (Int.divs n1 n2))
  | _, _ => none
def mods (v1 v2 : val) : Option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero ||
          (Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone)
      then none
      else some (Vint (Int.mods n1 n2))
  | _, _ => none
def divu (v1 v2 : val) : Option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => if Int.eq n2 Int.zero then none else some (Vint (Int.divu n1 n2))
  | _, _ => none
def modu (v1 v2 : val) : Option val :=
  match v1, v2 with
  | Vint n1, Vint n2 => if Int.eq n2 Int.zero then none else some (Vint (Int.modu n1 n2))
  | _, _ => none

def sub_overflow (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.sub_overflow n1 n2 Int.zero) | _, _ => Vundef
def negative (v : val) : val := match v with | Vint n => Vint (Int.negative n) | _ => Vundef
def and (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.and n1 n2) | _, _ => Vundef
def or (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.or n1 n2) | _, _ => Vundef
def xor (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.xor n1 n2) | _, _ => Vundef
def shl (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => if Int.ltu n2 Int.iwordsize then Vint (Int.shl n1 n2) else Vundef | _, _ => Vundef
def shr (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => if Int.ltu n2 Int.iwordsize then Vint (Int.shr n1 n2) else Vundef | _, _ => Vundef
def shru (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => if Int.ltu n2 Int.iwordsize then Vint (Int.shru n1 n2) else Vundef | _, _ => Vundef
def shrx (v1 v2 : val) : Option val := match v1, v2 with | Vint n1, Vint n2 => if Int.ltu n2 (Int.repr (zOfNat 31)) then some (Vint (Int.shrx n1 n2)) else none | _, _ => none
def ror (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vint (Int.ror n1 n2) | _, _ => Vundef

def addf (v1 v2 : val) : val := match v1, v2 with | Vfloat f1, Vfloat f2 => Vfloat (Float.add f1 f2) | _, _ => Vundef
def subf (v1 v2 : val) : val := match v1, v2 with | Vfloat f1, Vfloat f2 => Vfloat (Float.sub f1 f2) | _, _ => Vundef
def mulf (v1 v2 : val) : val := match v1, v2 with | Vfloat f1, Vfloat f2 => Vfloat (Float.mul f1 f2) | _, _ => Vundef
def divf (v1 v2 : val) : val := match v1, v2 with | Vfloat f1, Vfloat f2 => Vfloat (Float.div f1 f2) | _, _ => Vundef
def addfs (v1 v2 : val) : val := match v1, v2 with | Vsingle f1, Vsingle f2 => Vsingle (Float32.add f1 f2) | _, _ => Vundef
def subfs (v1 v2 : val) : val := match v1, v2 with | Vsingle f1, Vsingle f2 => Vsingle (Float32.sub f1 f2) | _, _ => Vundef
def mulfs (v1 v2 : val) : val := match v1, v2 with | Vsingle f1, Vsingle f2 => Vsingle (Float32.mul f1 f2) | _, _ => Vundef
def divfs (v1 v2 : val) : val := match v1, v2 with | Vsingle f1, Vsingle f2 => Vsingle (Float32.div f1 f2) | _, _ => Vundef

def longofwords (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vlong (Int64.ofwords n1 n2) | _, _ => Vundef
def loword (v : val) : val := match v with | Vlong n => Vint (Int64.loword n) | _ => Vundef
def hiword (v : val) : val := match v with | Vlong n => Vint (Int64.hiword n) | _ => Vundef
def negl (v : val) : val := match v with | Vlong n => Vlong (Int64.neg n) | _ => Vundef
def notl (v : val) : val := match v with | Vlong n => Vlong (Int64.not n) | _ => Vundef
def longofint (v : val) : val := match v with | Vint n => Vlong (Int64.repr (Int.signed n)) | _ => Vundef
def longofintu (v : val) : val := match v with | Vint n => Vlong (Int64.repr (Int.unsigned n)) | _ => Vundef
def longoffloat (v : val) : Option val := match v with | Vfloat f => (Float.to_long f).map Vlong | _ => none
def longuoffloat (v : val) : Option val := match v with | Vfloat f => (Float.to_longu f).map Vlong | _ => none
def longofsingle (v : val) : Option val := match v with | Vsingle f => (Float32.to_long f).map Vlong | _ => none
def longuofsingle (v : val) : Option val := match v with | Vsingle f => (Float32.to_longu f).map Vlong | _ => none
def floatoflong (v : val)
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 53) (zOfNat 1024)] : Option val :=
  match v with | Vlong n => some (Vfloat (Float.of_long n)) | _ => none
def floatoflongu (v : val)
    [binary64_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 53) (zOfNat 1024)] : Option val :=
  match v with | Vlong n => some (Vfloat (Float.of_longu n)) | _ => none
def singleoflong (v : val)
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 24) (zOfNat 128)] : Option val :=
  match v with | Vlong n => some (Vsingle (Float32.of_long n)) | _ => none
def singleoflongu (v : val)
    [binary32_certificate :
      CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
        (zOfNat 24) (zOfNat 128)] : Option val :=
  match v with | Vlong n => some (Vsingle (Float32.of_longu n)) | _ => none

def addl (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong (Int64.add n1 n2)
  | Vptr b ofs, Vlong n => if Archi.ptr64 then Vptr b (Ptrofs.add ofs (Ptrofs.of_int64 n)) else Vundef
  | Vlong n, Vptr b ofs => if Archi.ptr64 then Vptr b (Ptrofs.add ofs (Ptrofs.of_int64 n)) else Vundef
  | _, _ => Vundef
def subl (v1 v2 : val) : val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong (Int64.sub n1 n2)
  | Vptr b ofs, Vlong n => if Archi.ptr64 then Vptr b (Ptrofs.sub ofs (Ptrofs.of_int64 n)) else Vundef
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if !Archi.ptr64 then Vundef
      else if boolOfSumbool (eq_block b1 b2) then
        Vlong (Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2))
      else Vundef
  | _, _ => Vundef
def mull (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (Int64.mul n1 n2) | _, _ => Vundef
def mull' (v1 v2 : val) : val := match v1, v2 with | Vint n1, Vint n2 => Vlong (Int64.mul' n1 n2) | _, _ => Vundef
def mullhs (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (int64Mulhs n1 n2) | _, _ => Vundef
def mullhu (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (int64Mulhu n1 n2) | _, _ => Vundef
def divls (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vlong n2 => if Int64.eq n2 Int64.zero || (Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone) then none else some (Vlong (Int64.divs n1 n2)) | _, _ => none
def modls (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vlong n2 => if Int64.eq n2 Int64.zero || (Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone) then none else some (Vlong (Int64.mods n1 n2)) | _, _ => none
def divlu (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vlong n2 => if Int64.eq n2 Int64.zero then none else some (Vlong (Int64.divu n1 n2)) | _, _ => none
def modlu (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vlong n2 => if Int64.eq n2 Int64.zero then none else some (Vlong (Int64.modu n1 n2)) | _, _ => none
def subl_overflow (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vint (Int.repr (Int64.unsigned (Int64.sub_overflow n1 n2 Int64.zero))) | _, _ => Vundef
def negativel (v : val) : val := match v with | Vlong n => Vint (Int.repr (Int64.unsigned (Int64.negative n))) | _ => Vundef
def andl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (Int64.and n1 n2) | _, _ => Vundef
def orl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (Int64.or n1 n2) | _, _ => Vundef
def xorl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vlong n2 => Vlong (Int64.xor n1 n2) | _, _ => Vundef
def shll (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vint n2 => if Int.ltu n2 Int64.iwordsize' then Vlong (Int64.shl' n1 n2) else Vundef | _, _ => Vundef
def shrl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vint n2 => if Int.ltu n2 Int64.iwordsize' then Vlong (Int64.shr' n1 n2) else Vundef | _, _ => Vundef
def shrlu (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vint n2 => if Int.ltu n2 Int64.iwordsize' then Vlong (Int64.shru' n1 n2) else Vundef | _, _ => Vundef
def shrxl (v1 v2 : val) : Option val := match v1, v2 with | Vlong n1, Vint n2 => if Int.ltu n2 (Int.repr (zOfNat 63)) then some (Vlong (Int64.shrx' n1 n2)) else none | _, _ => none
def rorl (v1 v2 : val) : val := match v1, v2 with | Vlong n1, Vint n2 => Vlong (Int64.ror n1 (Int64.repr (Int.unsigned n2))) | _, _ => Vundef

def cmp_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | Vint n1, Vint n2 => some (CompCert4Lean.Lib.Integers.Int.cmp c n1 n2)
  | _, _ => none
def cmp_different_blocks (c : comparison) : Option Bool := match c with | .Ceq => some false | .Cne => some true | _ => none
def cmpu_bool (valid_ptr : block → Z → Bool) (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | Vint n1, Vint n2 => some (CompCert4Lean.Lib.Integers.Int.cmpu c n1 n2)
  | Vint n, Vptr b ofs => if !Archi.ptr64 && Int.eq n Int.zero && (valid_ptr b (Ptrofs.unsigned ofs) || valid_ptr b (zSub (Ptrofs.unsigned ofs) z1)) then cmp_different_blocks c else none
  | Vptr b ofs, Vint n => if !Archi.ptr64 && Int.eq n Int.zero && (valid_ptr b (Ptrofs.unsigned ofs) || valid_ptr b (zSub (Ptrofs.unsigned ofs) z1)) then cmp_different_blocks c else none
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if !Archi.ptr64 then
        if boolOfSumbool (eq_block b1 b2) then
          if (valid_ptr b1 (Ptrofs.unsigned ofs1) || valid_ptr b1 (zSub (Ptrofs.unsigned ofs1) z1)) &&
             (valid_ptr b2 (Ptrofs.unsigned ofs2) || valid_ptr b2 (zSub (Ptrofs.unsigned ofs2) z1))
          then some (CompCert4Lean.Lib.Integers.Ptrofs.cmpu c ofs1 ofs2) else none
        else if valid_ptr b1 (Ptrofs.unsigned ofs1) && valid_ptr b2 (Ptrofs.unsigned ofs2) then cmp_different_blocks c else none
      else none
  | _, _ => none
def cmpf_bool (c : comparison) (v1 v2 : val) : Option Bool := match v1, v2 with | Vfloat f1, Vfloat f2 => some (Float.cmp c f1 f2) | _, _ => none
def cmpfs_bool (c : comparison) (v1 v2 : val) : Option Bool := match v1, v2 with | Vsingle f1, Vsingle f2 => some (Float32.cmp c f1 f2) | _, _ => none
def cmpl_bool (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => some (CompCert4Lean.Lib.Integers.Int64.cmp c n1 n2)
  | _, _ => none
def cmplu_bool (valid_ptr : block → Z → Bool) (c : comparison) (v1 v2 : val) : Option Bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => some (CompCert4Lean.Lib.Integers.Int64.cmpu c n1 n2)
  | Vlong n, Vptr b ofs =>
      if Archi.ptr64 && Int64.eq n Int64.zero &&
        (valid_ptr b (Ptrofs.unsigned ofs) || valid_ptr b (zSub (Ptrofs.unsigned ofs) z1))
      then cmp_different_blocks c else none
  | Vptr b ofs, Vlong n =>
      if Archi.ptr64 && Int64.eq n Int64.zero &&
        (valid_ptr b (Ptrofs.unsigned ofs) || valid_ptr b (zSub (Ptrofs.unsigned ofs) z1))
      then cmp_different_blocks c else none
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if Archi.ptr64 then
        if boolOfSumbool (eq_block b1 b2) then
          if (valid_ptr b1 (Ptrofs.unsigned ofs1) || valid_ptr b1 (zSub (Ptrofs.unsigned ofs1) z1)) &&
             (valid_ptr b2 (Ptrofs.unsigned ofs2) || valid_ptr b2 (zSub (Ptrofs.unsigned ofs2) z1))
          then some (CompCert4Lean.Lib.Integers.Ptrofs.cmpu c ofs1 ofs2) else none
        else if valid_ptr b1 (Ptrofs.unsigned ofs1) && valid_ptr b2 (Ptrofs.unsigned ofs2)
        then cmp_different_blocks c else none
      else none
  | _, _ => none
def of_optbool (ob : Option Bool) : val := match ob with | some true => Vtrue | some false => Vfalse | none => Vundef
def cmp (c : comparison) (v1 v2 : val) : val := of_optbool (cmp_bool c v1 v2)
def cmpu (valid_ptr : block → Z → Bool) (c : comparison) (v1 v2 : val) : val := of_optbool (cmpu_bool valid_ptr c v1 v2)
def cmpf (c : comparison) (v1 v2 : val) : val := of_optbool (cmpf_bool c v1 v2)
def cmpfs (c : comparison) (v1 v2 : val) : val := of_optbool (cmpfs_bool c v1 v2)
def cmpl (c : comparison) (v1 v2 : val) : Option val := (cmpl_bool c v1 v2).map of_bool
def cmplu (valid_ptr : block → Z → Bool) (c : comparison) (v1 v2 : val) : Option val := (cmplu_bool valid_ptr c v1 v2).map of_bool
def maskzero_bool (v : val) (mask : CCInt) : Option Bool := match v with | Vint n => some (Int.eq (Int.and n mask) Int.zero) | _ => none

def offset_ptr (v : val) (delta : Ptrofs) : val := match v with | Vptr b ofs => Vptr b (Ptrofs.add ofs delta) | _ => Vundef
def normalize (v : val) (ty : typ) : val :=
  match v, ty with
  | Vundef, _ => Vundef
  | Vint _, Tint | Vlong _, Tlong | Vfloat _, Tfloat | Vsingle _, Tsingle => v
  | Vptr _ _, Tint | Vptr _ _, Tany32 => if Archi.ptr64 then Vundef else v
  | Vptr _ _, Tlong => if Archi.ptr64 then v else Vundef
  | Vint _, Tany32 | Vsingle _, Tany32 => v
  | _, Tany64 => v
  | _, _ => Vundef
def select (cmp : Option Bool) (v1 v2 : val) (ty : typ) : val := match cmp with | some b => normalize (if b then v1 else v2) ty | none => Vundef
def load_result (chunk : memory_chunk) (v : val) : val :=
  match chunk, v with
  | Mbool, Vint n => norm_bool (Vint (intZeroExt (zOfNat 8) n))
  | Mint8signed, Vint n => Vint (intSignExt (zOfNat 8) n)
  | Mint8unsigned, Vint n => Vint (intZeroExt (zOfNat 8) n)
  | Mint16signed, Vint n => Vint (intSignExt (zOfNat 16) n)
  | Mint16unsigned, Vint n => Vint (intZeroExt (zOfNat 16) n)
  | Mint32, Vint n => Vint n
  | Mint32, Vptr b ofs => if Archi.ptr64 then Vundef else Vptr b ofs
  | Mint64, Vlong n => Vlong n
  | Mint64, Vptr b ofs => if Archi.ptr64 then Vptr b ofs else Vundef
  | Mfloat32, Vsingle f => Vsingle f
  | Mfloat64, Vfloat f => Vfloat f
  | Many32, Vint _ | Many32, Vsingle _ => v
  | Many32, Vptr _ _ => if Archi.ptr64 then Vundef else v
  | Many64, _ => v
  | _, _ => Vundef

inductive lessdef : val → val → Prop where
  | lessdef_refl (v : val) : lessdef v v
  | lessdef_undef (v : val) : lessdef Vundef v

abbrev lessdef_refl (v : val) : lessdef v v :=
  @lessdef.lessdef_refl v

abbrev lessdef_undef (v : val) : lessdef Vundef v :=
  @lessdef.lessdef_undef v

inductive lessdef_list : List val → List val → Prop where
  | lessdef_list_nil : lessdef_list [] []
  | lessdef_list_cons (v1 v2 : val) (vl1 vl2 : List val) : lessdef v1 v2 → lessdef_list vl1 vl2 → lessdef_list (v1 :: vl1) (v2 :: vl2)

abbrev lessdef_list_nil : lessdef_list [] [] :=
  @lessdef_list.lessdef_list_nil

abbrev lessdef_list_cons (v1 v2 : val) (vl1 vl2 : List val)
    (hhead : lessdef v1 v2) (htail : lessdef_list vl1 vl2) :
    lessdef_list (v1 :: vl1) (v2 :: vl2) :=
  @lessdef_list.lessdef_list_cons v1 v2 vl1 vl2 hhead htail

def meminj : Type := block → Option (block × Z)

inductive inject (mi : meminj) : val → val → Prop where
  | inject_int (i : CCInt) : inject mi (Vint i) (Vint i)
  | inject_long (i : CCInt64) : inject mi (Vlong i) (Vlong i)
  | inject_float (f : CCFloat) : inject mi (Vfloat f) (Vfloat f)
  | inject_single (f : CCFloat32) : inject mi (Vsingle f) (Vsingle f)
  | inject_ptr (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs) (delta : Z) :
      mi b1 = some (b2, delta) →
      ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta) →
      inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_undef (v : val) : inject mi Vundef v

abbrev inject_int (mi : meminj) (i : CCInt) : inject mi (Vint i) (Vint i) :=
  @inject.inject_int mi i

abbrev inject_long (mi : meminj) (i : CCInt64) : inject mi (Vlong i) (Vlong i) :=
  @inject.inject_long mi i

abbrev inject_float (mi : meminj) (f : CCFloat) : inject mi (Vfloat f) (Vfloat f) :=
  @inject.inject_float mi f

abbrev inject_single (mi : meminj) (f : CCFloat32) : inject mi (Vsingle f) (Vsingle f) :=
  @inject.inject_single mi f

abbrev inject_ptr (mi : meminj) (b1 : block) (ofs1 : Ptrofs) (b2 : block)
    (ofs2 : Ptrofs) (delta : Z) (hmap : mi b1 = some (b2, delta))
    (hofs : ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta)) :
    inject mi (Vptr b1 ofs1) (Vptr b2 ofs2) :=
  @inject.inject_ptr mi b1 ofs1 b2 ofs2 delta hmap hofs

abbrev val_inject_undef (mi : meminj) (v : val) : inject mi Vundef v :=
  @inject.val_inject_undef mi v

def addl_injectStatement : Prop :=
  ∀ (f : meminj) v1 v1' v2 v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (addl v1 v2) (addl v1' v2')

theorem addl_inject : addl_injectStatement := by
  intro f v1 v1' v2 v2' h1 h2
  cases h1 <;> cases h2 <;>
    simp [addl, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64] <;>
    constructor <;>
    try assumption
  all_goals
    subst_vars
    rw [Ptrofs.add_assoc_proof_api, Ptrofs.add_assoc_proof_api]
    congr 1
    exact Ptrofs.add_commut_proof_api _ _

def subl_injectStatement : Prop :=
  ∀ (f : meminj) v1 v1' v2 v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (subl v1 v2) (subl v1' v2')

theorem subl_inject : subl_injectStatement := by
  intro f v1 v1' v2 v2' h1 h2
  cases h1 <;> cases h2 <;>
    simp [subl, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64] <;>
    try constructor <;>
    try assumption
  case inject_ptr.inject_long.a =>
    subst_vars
    exact Ptrofs.sub_add_l_proof_api _ _ _
  case inject_ptr.inject_ptr =>
    rename_i srcB1 srcOfs1 dstB1 dstOfs1 delta1 map1 ofsEq1
      srcB2 srcOfs2 dstB2 dstOfs2 delta2 map2 ofsEq2
    by_cases hsrc : srcB1 = srcB2
    · subst srcB2
      have hpair : (dstB1, delta1) = (dstB2, delta2) :=
        Option.some.inj (map1.symm.trans map2)
      have hdst : dstB1 = dstB2 := congrArg Prod.fst hpair
      have hdelta : delta1 = delta2 := congrArg Prod.snd hpair
      subst dstB2
      subst delta2
      have hsrcEq : boolOfSumbool (eq_block srcB1 srcB1) = true := by
        cases h : eq_block srcB1 srcB1 with
        | left _ => rfl
        | right hne => exact (hne rfl).elim
      have hdstEq : boolOfSumbool (eq_block dstB1 dstB1) = true := by
        cases h : eq_block dstB1 dstB1 with
        | left _ => rfl
        | right hne => exact (hne rfl).elim
      rw [hsrcEq, hdstEq]
      simp
      rw [ofsEq1, ofsEq2, Ptrofs.sub_shifted_proof_api]
      exact inject.inject_long _
    · have hsrcEq : boolOfSumbool (eq_block srcB1 srcB2) = false := by
        cases h : eq_block srcB1 srcB2 with
        | left heq => exact (hsrc heq).elim
        | right _ => rfl
      rw [hsrcEq]
      exact inject.val_inject_undef _

inductive inject_list (mi : meminj) : List val → List val → Prop where
  | inject_list_nil : inject_list mi [] []
  | inject_list_cons (v1 v2 : val) (vl1 vl2 : List val) :
      inject mi v1 v2 →
      inject_list mi vl1 vl2 →
      inject_list mi (v1 :: vl1) (v2 :: vl2)

abbrev inject_list_nil (mi : meminj) : inject_list mi [] [] :=
  @inject_list.inject_list_nil mi

abbrev inject_list_cons (mi : meminj) (v1 v2 : val) (vl1 vl2 : List val)
    (hhead : inject mi v1 v2) (htail : inject_list mi vl1 vl2) :
    inject_list mi (v1 :: vl1) (v2 :: vl2) :=
  @inject_list.inject_list_cons mi v1 v2 vl1 vl2 hhead htail

def bool_of_val_of_optboolStatement : Prop :=
  ∀ ob b, bool_of_val (of_optbool ob) b → ob = some b

def norm_bool_casesStatement : Prop :=
  ∀ v, norm_bool v = Vundef ∨ norm_bool v = Vfalse ∨ norm_bool v = Vtrue

def norm_bool_idemStatement : Prop :=
  ∀ v, norm_bool (norm_bool v) = norm_bool v

def norm_bool_is_lessdefStatement : Prop :=
  ∀ v, lessdef (norm_bool v) v

def norm_bool_lessdefStatement : Prop :=
  ∀ v1 v2, lessdef v1 v2 → lessdef (norm_bool v1) (norm_bool v2)

def load_result_xtypeStatement : Prop :=
  ∀ chunk v, has_rettype (load_result chunk v) (xtype_of_chunk chunk)

def load_result_typeStatement : Prop :=
  ∀ chunk v, has_type (load_result chunk v) (type_of_chunk chunk)

def load_result_sameStatement : Prop :=
  ∀ v ty, has_type v ty → load_result (chunk_of_type ty) v = v

def load_result_lessdefStatement : Prop :=
  ∀ chunk v1 v2,
    lessdef v1 v2 → lessdef (load_result chunk v1) (load_result chunk v2)

def load_result_injectStatement : Prop :=
  ∀ (f : meminj) chunk v1 v2,
    inject f v1 v2 → inject f (load_result chunk v1) (load_result chunk v2)

def add_commutStatement : Prop :=
  ∀ x y, add x y = add y x

def add_assocStatement : Prop :=
  ∀ x y z, add (add x y) z = add x (add y z)

def add_permutStatement : Prop :=
  ∀ x y z, add x (add y z) = add y (add x z)

def add_permut_4Statement : Prop :=
  ∀ x y z t, add (add x y) (add z t) = add (add x z) (add y t)

def add_lessdefStatement : Prop :=
  ∀ v1 v1' v2 v2',
    lessdef v1 v1' → lessdef v2 v2' → lessdef (add v1 v2) (add v1' v2')

def add_injectStatement : Prop :=
  ∀ (f : meminj) v1 v1' v2 v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (add v1 v2) (add v1' v2')

def sub_add_oppStatement : Prop :=
  ∀ x y, sub x (Vint y) = add x (Vint (Int.neg y))

def sub_add_lStatement : Prop :=
  ∀ v1 v2 i, sub (add v1 (Vint i)) v2 = add (sub v1 v2) (Vint i)

def sub_add_rStatement : Prop :=
  ∀ v1 v2 i,
    sub v1 (add v2 (Vint i)) = add (sub v1 v2) (Vint (Int.neg i))

def sub_injectStatement : Prop :=
  ∀ (f : meminj) v1 v1' v2 v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (sub v1 v2) (sub v1' v2')

def mul_commutStatement : Prop :=
  ∀ x y, mul x y = mul y x

def mul_add_distr_lStatement : Prop :=
  ∀ x y z, mul (add x y) z = add (mul x z) (mul y z)

def mul_add_distr_rStatement : Prop :=
  ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)

def mul_pow2Statement : Prop :=
  ∀ x n logn,
    Int.is_power2 n = some logn →
    mul x (Vint n) = shl x (Vint logn)

def and_commutStatement : Prop :=
  ∀ x y, and x y = and y x

def and_assocStatement : Prop :=
  ∀ x y z, and (and x y) z = and x (and y z)

def or_commutStatement : Prop :=
  ∀ x y, or x y = or y x

def or_assocStatement : Prop :=
  ∀ x y z, or (or x y) z = or x (or y z)

def xor_commutStatement : Prop :=
  ∀ x y, xor x y = xor y x

def xor_assocStatement : Prop :=
  ∀ x y z, xor (xor x y) z = xor x (xor y z)

def not_xorStatement : Prop :=
  ∀ x, notint x = xor x (Vint Int.mone)

def shl_mulStatement : Prop :=
  ∀ x y, mul x (shl Vone y) = shl x y

def addl_commutStatement : Prop :=
  ∀ x y, addl x y = addl y x

def addl_assocStatement : Prop :=
  ∀ x y z, addl (addl x y) z = addl x (addl y z)

def addl_permutStatement : Prop :=
  ∀ x y z, addl x (addl y z) = addl y (addl x z)

def addl_permut_4Statement : Prop :=
  ∀ x y z t, addl (addl x y) (addl z t) = addl (addl x z) (addl y t)

def addl_lessdefStatement : Prop :=
  ∀ v1 v1' v2 v2',
    lessdef v1 v1' → lessdef v2 v2' → lessdef (addl v1 v2) (addl v1' v2')

def andl_commutStatement : Prop :=
  ∀ x y, andl x y = andl y x

def andl_assocStatement : Prop :=
  ∀ x y z, andl (andl x y) z = andl x (andl y z)

def orl_commutStatement : Prop :=
  ∀ x y, orl x y = orl y x

def orl_assocStatement : Prop :=
  ∀ x y z, orl (orl x y) z = orl x (orl y z)

def xorl_commutStatement : Prop :=
  ∀ x y, xorl x y = xorl y x

def xorl_assocStatement : Prop :=
  ∀ x y z, xorl (xorl x y) z = xorl x (xorl y z)

def notl_xorlStatement : Prop :=
  ∀ x, notl x = xorl x (Vlong Int64.mone)

def divs_pow2Statement : Prop :=
  ∀ x n logn y,
    Int.is_power2 n = some logn →
    Int.ltu logn (Int.repr (zOfNat 31)) = true →
    divs x (Vint n) = some y →
    shrx x (Vint logn) = some y

def divs_oneStatement : Prop :=
  ∀ s, divs (Vint s) (Vint Int.one) = some (Vint s)

def divu_pow2Statement : Prop :=
  ∀ x n logn y,
    Int.is_power2 n = some logn →
    divu x (Vint n) = some y →
    shru x (Vint logn) = y

def divu_oneStatement : Prop :=
  ∀ s, divu (Vint s) (Vint Int.one) = some (Vint s)

def divls_pow2Statement : Prop :=
  ∀ x n logn y,
    Int64.is_power2' n = some logn →
    Int.ltu logn (Int.repr (zOfNat 63)) = true →
    divls x (Vlong n) = some y →
    shrxl x (Vint logn) = some y

def divlu_pow2Statement : Prop :=
  ∀ x n logn y,
    Int64.is_power2' n = some logn →
    divlu x (Vlong n) = some y →
    shrlu x (Vint logn) = y

def modlu_pow2Statement : Prop :=
  ∀ x n logn y,
    Int64.is_power2 n = some logn →
    modlu x (Vlong n) = some y →
    andl x (Vlong (Int64.sub n Int64.one)) = y

def mods_divsStatement : Prop :=
  ∀ x y z,
    mods x y = some z → ∃ v, divs x y = some v ∧ z = sub x (mul v y)

def modu_pow2Statement : Prop :=
  ∀ x n logn y,
    Int.is_power2 n = some logn →
    modu x (Vint n) = some y →
    and x (Vint (Int.sub n Int.one)) = y

def negate_cmp_boolStatement : Prop :=
  ∀ c x y,
    cmp_bool (negate_comparison c) x y =
      CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmp_bool c x y)

def negate_cmpu_boolStatement : Prop :=
  ∀ valid_ptr c x y,
    cmpu_bool valid_ptr (negate_comparison c) x y =
      CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmpu_bool valid_ptr c x y)

def negate_cmpl_boolStatement : Prop :=
  ∀ c x y,
    cmpl_bool (negate_comparison c) x y =
      CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmpl_bool c x y)

def negate_cmplu_boolStatement : Prop :=
  ∀ valid_ptr c x y,
    cmplu_bool valid_ptr (negate_comparison c) x y =
      CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmplu_bool valid_ptr c x y)

def swap_cmp_boolStatement : Prop :=
  ∀ c x y, cmp_bool (swap_comparison c) x y = cmp_bool c y x

def swap_cmpu_boolStatement : Prop :=
  ∀ valid_ptr c x y,
    cmpu_bool valid_ptr (swap_comparison c) x y = cmpu_bool valid_ptr c y x

def swap_cmpl_boolStatement : Prop :=
  ∀ c x y, cmpl_bool (swap_comparison c) x y = cmpl_bool c y x

def swap_cmplu_boolStatement : Prop :=
  ∀ valid_ptr c x y,
    cmplu_bool valid_ptr (swap_comparison c) x y = cmplu_bool valid_ptr c y x

def cmpu_bool_lessdefStatement : Prop :=
  ∀ (valid_ptr valid_ptr' : block → Z → Bool) c v1 v1' v2 v2' b,
    (∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true) →
    lessdef v1 v1' →
    lessdef v2 v2' →
    cmpu_bool valid_ptr c v1 v2 = some b →
    cmpu_bool valid_ptr' c v1' v2' = some b

def cmplu_bool_lessdefStatement : Prop :=
  ∀ (valid_ptr valid_ptr' : block → Z → Bool) c v1 v1' v2 v2' b,
    (∀ b ofs, valid_ptr b ofs = true → valid_ptr' b ofs = true) →
    lessdef v1 v1' →
    lessdef v2 v2' →
    cmplu_bool valid_ptr c v1 v2 = some b →
    cmplu_bool valid_ptr' c v1' v2' = some b

def cmpu_bool_injectStatement : Prop :=
  ∀ (f : meminj) (valid_ptr1 valid_ptr2 : block → Z → Bool),
    let weak_valid_ptr1 := fun (b : block) (ofs : Z) =>
      valid_ptr1 b ofs || valid_ptr1 b (zSub ofs z1)
    let weak_valid_ptr2 := fun (b : block) (ofs : Z) =>
      valid_ptr2 b ofs || valid_ptr2 b (zSub ofs z1)
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))
        Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
        (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      valid_ptr1 b1 (Ptrofs.unsigned ofs1) = true →
      valid_ptr1 b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ c v1 v2 v1' v2' b,
      inject f v1 v1' →
      inject f v2 v2' →
      cmpu_bool valid_ptr1 c v1 v2 = some b →
      cmpu_bool valid_ptr2 c v1' v2' = some b

def cmplu_bool_injectStatement : Prop :=
  ∀ (f : meminj) (valid_ptr1 valid_ptr2 : block → Z → Bool),
    let weak_valid_ptr1 := fun (b : block) (ofs : Z) =>
      valid_ptr1 b ofs || valid_ptr1 b (zSub ofs z1)
    let weak_valid_ptr2 := fun (b : block) (ofs : Z) =>
      valid_ptr2 b ofs || valid_ptr2 b (zSub ofs z1)
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true) →
    (∀ (b1 : block) (ofs : Ptrofs) (b2 : block) (delta : Z),
      f b1 = some (b2, delta) →
      weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true →
      zLe z0 (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta))) ∧
      zLe (zAdd (Ptrofs.unsigned ofs) (Ptrofs.unsigned (Ptrofs.repr delta)))
        Ptrofs.max_unsigned) →
    (∀ (b1 : block) (ofs1 : Ptrofs) (b2 : block) (ofs2 : Ptrofs)
        (b1' : block) (delta1 : Z) (b2' : block) (delta2 : Z),
      b1 ≠ b2 →
      valid_ptr1 b1 (Ptrofs.unsigned ofs1) = true →
      valid_ptr1 b2 (Ptrofs.unsigned ofs2) = true →
      f b1 = some (b1', delta1) →
      f b2 = some (b2', delta2) →
      b1' ≠ b2' ∨
      Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) ≠
        Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2))) →
    ∀ c v1 v2 v1' v2' b,
      inject f v1 v1' →
      inject f v2 v2' →
      cmplu_bool valid_ptr1 c v1 v2 = some b →
      cmplu_bool valid_ptr2 c v1' v2' = some b

def offset_ptr_injectStatement : Prop :=
  ∀ (f : meminj) v v' ofs,
    inject f v v' → inject f (offset_ptr v ofs) (offset_ptr v' ofs)

def normalize_typeStatement : Prop :=
  ∀ v ty, has_type (normalize v ty) ty

def normalize_idemStatement : Prop :=
  ∀ v ty, has_type v ty → normalize v ty = v

def normalize_lessdefStatement : Prop :=
  ∀ v v' ty, lessdef v v' → lessdef (normalize v ty) (normalize v' ty)

def normalize_injectStatement : Prop :=
  ∀ (f : meminj) v v' ty,
    inject f v v' → inject f (normalize v ty) (normalize v' ty)

def lessdef_normalizeStatement : Prop :=
  ∀ v ty, lessdef (normalize v ty) v

def select_injectStatement : Prop :=
  ∀ (f : meminj) (ob ob' : Option Bool) v1 v1' v2 v2' ty,
    (ob = none ∨ ob = ob') →
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (select ob v1 v2 ty) (select ob' v1' v2' ty)

def of_optbool_lessdefStatement : Prop :=
  ∀ (ob ob' : Option Bool),
    (∀ b, ob = some b → ob' = some b) →
    lessdef (of_optbool ob) (of_optbool ob')

def longofwords_lessdefStatement : Prop :=
  ∀ v1 v2 v1' v2',
    lessdef v1 v1' →
    lessdef v2 v2' →
    lessdef (longofwords v1 v2) (longofwords v1' v2')

def longofwords_injectStatement : Prop :=
  ∀ (f : meminj) v1 v2 v1' v2',
    inject f v1 v1' →
    inject f v2 v2' →
    inject f (longofwords v1 v2) (longofwords v1' v2')

def loword_lessdefStatement : Prop :=
  ∀ v v', lessdef v v' → lessdef (loword v) (loword v')

def loword_injectStatement : Prop :=
  ∀ (f : meminj) v v', inject f v v' → inject f (loword v) (loword v')

def hiword_lessdefStatement : Prop :=
  ∀ v v', lessdef v v' → lessdef (hiword v) (hiword v')

def hiword_injectStatement : Prop :=
  ∀ (f : meminj) v v', inject f v v' → inject f (hiword v) (hiword v')

def has_argtype_lessdefStatement : Prop :=
  ∀ v r v', has_argtype v r → lessdef v v' → has_argtype v' r

def has_argtype_injectStatement : Prop :=
  ∀ (f : meminj) v r v', has_argtype v r → inject f v v' → has_argtype v' r

def has_argtype_list_lessdefStatement : Prop :=
  ∀ vl rl vl',
    has_argtype_list vl rl → lessdef_list vl vl' → has_argtype_list vl' rl

def has_argtype_list_injectStatement : Prop :=
  ∀ (f : meminj) vl rl vl',
    has_argtype_list vl rl → inject_list f vl vl' → has_argtype_list vl' rl

def lessdef_sameStatement : Prop :=
  ∀ v1 v2, v1 = v2 → lessdef v1 v2

def lessdef_transStatement : Prop :=
  ∀ v1 v2 v3, lessdef v1 v2 → lessdef v2 v3 → lessdef v1 v3

def lessdef_list_transStatement : Prop :=
  ∀ vl1 vl2,
    lessdef_list vl1 vl2 → ∀ vl3, lessdef_list vl2 vl3 → lessdef_list vl1 vl3

def mull_commutStatement : Prop :=
  ∀ x y, mull x y = mull y x

def shrx_shrStatement : Prop :=
  ∀ x y z,
    shrx x y = some z →
    ∃ p q,
      x = Vint p ∧
      y = Vint q ∧
      z = shr
        (if Int.lt p Int.zero then
          add x (Vint (Int.sub (Int.shl Int.one q) Int.one))
        else x)
        (Vint q)

def shrxl_shrl_2Statement : Prop :=
  ∀ n x z,
    shrxl x (Vint n) = some z →
    z = if Int.eq n Int.zero then x else
      shrl
        (addl x
          (shrlu (shrl x (Vint (Int.repr (zOfNat 63))))
            (Vint (Int.sub (Int.repr (zOfNat 64)) n))))
        (Vint n)

def subl_addl_lStatement : Prop :=
  ∀ v1 v2 i, subl (addl v1 (Vlong i)) v2 = addl (subl v1 v2) (Vlong i)

def subl_addl_oppStatement : Prop :=
  ∀ x y, subl x (Vlong y) = addl x (Vlong (Int64.neg y))

def subl_addl_rStatement : Prop :=
  ∀ v1 v2 i,
    subl v1 (addl v2 (Vlong i)) = addl (subl v1 v2) (Vlong (Int64.neg i))

def zero_ext_andStatement : Prop :=
  ∀ n v,
    zLe z0 n → zero_ext n v = and v (Vint (Int.repr (zSub (zTwoP n) z1)))

end Val

abbrev meminj := Val.meminj

def inject_incr (f1 f2 : meminj) : Prop :=
  ∀ b b' delta, f1 b = some (b', delta) → f2 b = some (b', delta)

def inject_id : meminj := fun b => some (b, z0)

def inject_incr_reflStatement : Prop :=
  ∀ f : meminj, inject_incr f f

def inject_incr_transStatement : Prop :=
  ∀ f1 f2 f3,
    inject_incr f1 f2 → inject_incr f2 f3 → inject_incr f1 f3

def val_inject_incrStatement : Prop :=
  ∀ f1 f2 v v',
    inject_incr f1 f2 → Val.inject f1 v v' → Val.inject f2 v v'

def val_inject_list_incrStatement : Prop :=
  ∀ f1 f2 vl vl',
    inject_incr f1 f2 → Val.inject_list f1 vl vl' → Val.inject_list f2 vl vl'

def val_inject_lessdefStatement : Prop :=
  ∀ v1 v2,
    Val.lessdef v1 v2 ↔ Val.inject (fun b => some (b, z0)) v1 v2

def val_inject_list_lessdefStatement : Prop :=
  ∀ vl1 vl2,
    Val.lessdef_list vl1 vl2 ↔ Val.inject_list (fun b => some (b, z0)) vl1 vl2

def val_inject_idStatement : Prop :=
  ∀ v1 v2, Val.inject inject_id v1 v2 ↔ Val.lessdef v1 v2

end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

theorem inject_incr_refl : inject_incr_reflStatement := by
  intro f b b' delta h
  exact h

namespace Val

theorem Vptr_has_type : Vptr_has_typeStatement := by
  intro b ofs
  rfl

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

namespace Val

private theorem repr_val_of_lt (n : Nat) (hn : n < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) :
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n := by
  have hn0 : (0 : Int) ≤ n := Int.natCast_nonneg n
  have hnmax : (n : Int) ≤ (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Nat) - 1 := by omega
  have hnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) =
      (n : Int) := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat] using
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat n))
  have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int.max_unsigned =
      (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Int) - 1 := by rfl
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n := by
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 = 0 by rfl, hnat]
      exact hn0
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int.max_unsigned
      rw [hnat, hmax]
      exact hnmax
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    ((CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).intval) = n
  change CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) = _ at hu
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    (CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n))) = n
  rw [hu]
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id n

theorem and_assoc : and_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [and]
  rename_i a b c
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.and
      (CompCert4Lean.Lib.Integers.WordCore.and _ _) _).val =
    (CompCert4Lean.Lib.Integers.WordCore.and _
      (CompCert4Lean.Lib.Integers.WordCore.and _ _)).val
  simp only [CompCert4Lean.Lib.Integers.WordCore.and]
  have ha : a.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := a.toFin.isLt
  have hb : b.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := b.toFin.isLt
  have hc : c.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := c.toFin.isLt
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.land
          (CompCert4Lean.Lib.Integers.WordCore.Word.val
            (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                (Nat.land a.val b.val)))) c.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.land a.val
            (CompCert4Lean.Lib.Integers.WordCore.Word.val
              (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                  (Nat.land b.val c.val))))))).val
  simp only [repr_val_of_lt (Nat.land a.val b.val) (Nat.and_lt_two_pow a.val hb),
    repr_val_of_lt (Nat.land b.val c.val) (Nat.and_lt_two_pow b.val hc),
    repr_val_of_lt (Nat.land (Nat.land a.val b.val) c.val)
      (Nat.and_lt_two_pow (Nat.land a.val b.val) hc),
    repr_val_of_lt (Nat.land a.val (Nat.land b.val c.val))
      (Nat.and_lt_two_pow a.val (Nat.and_lt_two_pow b.val hc))]
  exact Nat.and_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

namespace Val

private theorem or_assoc_repr_val_of_lt (n : Nat)
    (hn : n < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) :
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n := by
  have hn0 : (0 : Int) ≤ n := Int.natCast_nonneg n
  have hnmax : (n : Int) ≤ (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Nat) - 1 := by omega
  have hnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) =
      (n : Int) := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat] using
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat n))
  have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int.max_unsigned =
      (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Int) - 1 := by rfl
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n := by
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 = 0 by rfl, hnat]
      exact hn0
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Lib.Integers.Int.max_unsigned
      rw [hnat, hmax]
      exact hnmax
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    ((CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).intval) = n
  change CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) = _ at hu
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    (CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n))) = n
  rw [hu]
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id n

theorem or_assoc : or_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [or]
  rename_i a b c
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.or
      (CompCert4Lean.Lib.Integers.WordCore.or _ _) _).val =
    (CompCert4Lean.Lib.Integers.WordCore.or _
      (CompCert4Lean.Lib.Integers.WordCore.or _ _)).val
  simp only [CompCert4Lean.Lib.Integers.WordCore.or]
  have ha : a.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := a.toFin.isLt
  have hb : b.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := b.toFin.isLt
  have hc : c.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := c.toFin.isLt
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.lor
          (CompCert4Lean.Lib.Integers.WordCore.Word.val
            (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                (Nat.lor a.val b.val)))) c.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.lor a.val
            (CompCert4Lean.Lib.Integers.WordCore.Word.val
              (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                  (Nat.lor b.val c.val))))))).val
  simp only [or_assoc_repr_val_of_lt (Nat.lor a.val b.val) (Nat.or_lt_two_pow ha hb),
    or_assoc_repr_val_of_lt (Nat.lor b.val c.val) (Nat.or_lt_two_pow hb hc),
    or_assoc_repr_val_of_lt (Nat.lor (Nat.lor a.val b.val) c.val)
      (Nat.or_lt_two_pow (Nat.or_lt_two_pow ha hb) hc),
    or_assoc_repr_val_of_lt (Nat.lor a.val (Nat.lor b.val c.val))
      (Nat.or_lt_two_pow ha (Nat.or_lt_two_pow hb hc))]
  exact Nat.or_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem xor_assoc_repr_val_of_lt' (n : Nat)
    (hn : n < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize) :
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n := by
  have hn0 : (0 : Int) ≤ n := Int.natCast_nonneg n
  have hnmax : (n : Int) ≤ (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Nat) - 1 := by omega
  have hnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) = (n : Int) := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat] using
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat n))
  have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int.max_unsigned =
      (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize : Int) - 1 := by rfl
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n := by
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 ≤ _
      rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z0 = 0 by rfl, hnat]
      exact hn0
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n) ≤ _
      rw [hnat, hmax]
      exact hnmax
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    ((CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).intval) = n
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat
    (CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n))) = n
  rw [hu]
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id n

theorem xor_assoc : xor_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [xor]
  rename_i a b c
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.xor
      (CompCert4Lean.Lib.Integers.WordCore.xor _ _) _).val =
    (CompCert4Lean.Lib.Integers.WordCore.xor _
      (CompCert4Lean.Lib.Integers.WordCore.xor _ _)).val
  simp only [CompCert4Lean.Lib.Integers.WordCore.xor]
  have ha : a.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := a.toFin.isLt
  have hb : b.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := b.toFin.isLt
  have hc : c.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := c.toFin.isLt
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.xor
          (CompCert4Lean.Lib.Integers.WordCore.Word.val
            (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                (Nat.xor a.val b.val)))) c.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.xor a.val
            (CompCert4Lean.Lib.Integers.WordCore.Word.val
              (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
                  (Nat.xor b.val c.val))))))).val
  simp only [xor_assoc_repr_val_of_lt' (Nat.xor a.val b.val) (Nat.xor_lt_two_pow ha hb),
    xor_assoc_repr_val_of_lt' (Nat.xor b.val c.val) (Nat.xor_lt_two_pow hb hc),
    xor_assoc_repr_val_of_lt' (Nat.xor (Nat.xor a.val b.val) c.val)
      (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ha hb) hc),
    xor_assoc_repr_val_of_lt' (Nat.xor a.val (Nat.xor b.val c.val))
      (Nat.xor_lt_two_pow ha (Nat.xor_lt_two_pow hb hc))]
  exact Nat.xor_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

open CompCert4Lean.Common.AST

namespace Val

theorem Vnullptr_has_type : Vnullptr_has_typeStatement := by
  change Val.has_type Vnullptr CompCert4Lean.Common.AST.Tptr
  cases hptr : CompCert4Lean.X86_64.Archi.ptr64 <;>
    simp [Vnullptr, CompCert4Lean.Common.AST.Tptr, Val.has_type, hptr]

private theorem has_subtype_local (ty1 ty2 : CompCert4Lean.Common.AST.typ) (v : val) :
    CompCert4Lean.Common.AST.subtype ty1 ty2 = true → Val.has_type v ty1 → Val.has_type v ty2 := by
  intro hsub hv
  cases ty1 <;> cases ty2 <;> cases v <;>
    simp [CompCert4Lean.Common.AST.subtype, Val.has_type] at hsub hv ⊢
  all_goals exact hv

theorem has_subtype : has_subtypeStatement := by
  intro ty1 ty2 v hsub hv
  exact has_subtype_local ty1 ty2 v hsub hv

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

namespace Val

theorem has_proj_xtype : has_proj_xtypeStatement := by
  intro v t h
  cases t <;> cases v <;>
    simp [has_rettype, has_type, CompCert4Lean.Common.AST.proj_xtype,
      CompCert4Lean.Common.AST.Tptr,
      CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

theorem has_inj_type : has_inj_typeStatement := by
  intro v t h
  cases v <;> cases t <;>
    simp [has_type, has_rettype, CompCert4Lean.Common.AST.inj_type,
      CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

theorem normalize_type : normalize_typeStatement := by
  intro v ty
  cases v <;> cases ty <;>
    simp [normalize, has_type, CompCert4Lean.X86_64.Archi.ptr64]

theorem normalize_idem : normalize_idemStatement := by
  intro v ty h
  cases v <;> cases ty <;>
    simp [normalize, has_type, CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem norm_bool_cases : norm_bool_casesStatement := by
  intro v
  unfold norm_bool
  unfold is_bool
  by_cases h₁ : v = Vtrue
  · simp [eq, h₁, boolOfSumbool]
  · by_cases h₂ : v = Vfalse
    · simp [eq, h₁, h₂, boolOfSumbool]
    · simp [eq, h₁, h₂, boolOfSumbool]

theorem load_result_type : load_result_typeStatement := by
  intro chunk v
  cases chunk <;> cases v <;>
    simp [load_result, has_type, CompCert4Lean.Common.AST.type_of_chunk,
      CompCert4Lean.X86_64.Archi.ptr64]
  case Mbool.Vint n =>
    rcases norm_bool_cases (Vint (intZeroExt (zOfNat 8) n)) with h | h | h <;>
      simp [h, has_type, Vfalse, Vtrue]

theorem load_result_same : load_result_sameStatement := by
  intro v ty h
  cases v <;> cases ty <;>
    simp [has_type, load_result, CompCert4Lean.Common.AST.chunk_of_type,
      CompCert4Lean.X86_64.Archi.ptr64] at h ⊢

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem bool_of_val_of_optbool : bool_of_val_of_optboolStatement := by
  intro ob b h
  cases ob with
  | none => cases h
  | some x => cases x <;> cases h <;> rfl

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem norm_bool_idem : norm_bool_idemStatement := by
  intro v
  unfold norm_bool
  by_cases h : is_bool v
  · simp [h]
  · simp [h]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_commut : add_commutStatement := by
  intro x y
  cases x <;> cases y <;>
    simp [add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint a b =>
    change CompCert4Lean.Lib.Integers.WordCore.repr 32
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add a.intval b.intval) =
      CompCert4Lean.Lib.Integers.WordCore.repr 32
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add b.intval a.intval)
    apply congrArg (CompCert4Lean.Lib.Integers.WordCore.repr 32)
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact Int.add_comm _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_assoc : add_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;>
    simp [add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint.Vint a b c =>
    exact CompCert4Lean.Lib.Integers.Int.add_assoc_proof a b c

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_permut : add_permutStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;>
    simp [add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint.Vint a b c =>
    change Int.add a (Int.add b c) = Int.add b (Int.add a c)
    calc
      Int.add a (Int.add b c) = Int.add (Int.add a b) c :=
        (CompCert4Lean.Lib.Integers.Int.add_assoc_proof a b c).symm
      _ = Int.add (Int.add b a) c := by
        have h := add_commut (Vint a) (Vint b)
        have h' : Int.add a b = Int.add b a := by
          injection h
        exact congrArg (fun q => Int.add q c) h'
      _ = Int.add b (Int.add a c) :=
        CompCert4Lean.Lib.Integers.Int.add_assoc_proof b a c

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_permut_4 : add_permut_4Statement := by
  intro x y z t
  calc
    add (add x y) (add z t) = add x (add y (add z t)) :=
      add_assoc x y (add z t)
    _ = add x (add z (add y t)) := by
      exact congrArg (fun q => add x q) (add_permut y z t)
    _ = add (add x z) (add y t) :=
      (add_assoc x z (add y t)).symm

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem sub_add_opp : sub_add_oppStatement := by
  intro x y
  cases x <;> simp [sub, add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint a =>
    exact CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof a y

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem int_add_commut_local (a b : CompCert4Lean.Lib.Integers.int) :
    Int.add a b = Int.add b a := by
  have h := add_commut (Vint a) (Vint b)
  injection h

private theorem int_sub_add_l_local
    (x y z : CompCert4Lean.Lib.Integers.int) :
    Int.sub (Int.add x y) z = Int.add (Int.sub x z) y := by
  calc
    Int.sub (Int.add x y) z = Int.add (Int.add x y) (Int.neg z) :=
      CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof (Int.add x y) z
    _ = Int.add x (Int.add y (Int.neg z)) :=
      CompCert4Lean.Lib.Integers.Int.add_assoc_proof x y (Int.neg z)
    _ = Int.add x (Int.add (Int.neg z) y) := by
      exact congrArg (fun q => Int.add x q) (int_add_commut_local y (Int.neg z))
    _ = Int.add (Int.add x (Int.neg z)) y :=
      (CompCert4Lean.Lib.Integers.Int.add_assoc_proof x (Int.neg z) y).symm
    _ = Int.add (Int.sub x z) y := by
      exact congrArg (fun q => Int.add q y)
        (CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof x z).symm

theorem sub_add_l : sub_add_lStatement := by
  intro v1 v2 i
  cases v1 <;> cases v2 <;>
    simp [sub, add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint a b =>
    exact int_sub_add_l_local a i b

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem mul_commut : mul_commutStatement := by
  intro x y
  cases x <;> cases y <;>
    simp [mul]
  case Vint.Vint a b =>
    change CompCert4Lean.Lib.Integers.WordCore.repr 32
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul a.intval b.intval) =
      CompCert4Lean.Lib.Integers.WordCore.repr 32
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul b.intval a.intval)
    apply congrArg (CompCert4Lean.Lib.Integers.WordCore.repr 32)
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact Int.mul_comm _ _

theorem mul_add_distr_r : mul_add_distr_rStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;>
    simp [mul, add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint.Vint a b c =>
    exact CompCert4Lean.Lib.Integers.Int.mul_add_distr_r_proof a b c

theorem mul_add_distr_l : mul_add_distr_lStatement := by
  intro x y z
  calc
    mul (add x y) z = mul z (add x y) := mul_commut _ _
    _ = add (mul z x) (mul z y) := mul_add_distr_r _ _ _
    _ = add (mul x z) (mul y z) := by
      rw [mul_commut z x, mul_commut z y]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem int_sub_self_local (x : CompCert4Lean.Lib.Integers.int) :
    Int.sub x x = Int.zero := by
  change CompCert4Lean.Lib.Integers.WordCore.repr 32
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub x.intval x.intval) =
    CompCert4Lean.Lib.Integers.WordCore.repr 32
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0
  apply congrArg (CompCert4Lean.Lib.Integers.WordCore.repr 32)
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Int.sub_self _

private theorem int_add_zero_l_local (x : CompCert4Lean.Lib.Integers.int) :
    Int.add Int.zero x = x := by
  calc
    Int.add Int.zero x = Int.add x Int.zero := int_add_commut_local _ _
    _ = x := CompCert4Lean.Lib.Integers.Int.add_zero_proof x

private theorem int_add_neg_self_local (x : CompCert4Lean.Lib.Integers.int) :
    Int.add x (Int.neg x) = Int.zero := by
  calc
    Int.add x (Int.neg x) = Int.sub x x :=
      (CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof x x).symm
    _ = Int.zero := int_sub_self_local x

private theorem int_add_neg_self_left_local (x : CompCert4Lean.Lib.Integers.int) :
    Int.add (Int.neg x) x = Int.zero := by
  calc
    Int.add (Int.neg x) x = Int.add x (Int.neg x) := int_add_commut_local _ _
    _ = Int.zero := int_add_neg_self_local x

private theorem int_add_permut_local
    (x y z : CompCert4Lean.Lib.Integers.int) :
    Int.add x (Int.add y z) = Int.add y (Int.add x z) := by
  calc
    Int.add x (Int.add y z) = Int.add (Int.add x y) z :=
      (CompCert4Lean.Lib.Integers.Int.add_assoc_proof x y z).symm
    _ = Int.add (Int.add y x) z := by rw [int_add_commut_local x y]
    _ = Int.add y (Int.add x z) :=
      CompCert4Lean.Lib.Integers.Int.add_assoc_proof y x z

private theorem int_neg_unique_local
    (a b : CompCert4Lean.Lib.Integers.int) (h : Int.add a b = Int.zero) :
    b = Int.neg a := by
  calc
    b = Int.add Int.zero b := (int_add_zero_l_local b).symm
    _ = Int.add (Int.add (Int.neg a) a) b := by
      rw [int_add_neg_self_left_local a]
    _ = Int.add (Int.neg a) (Int.add a b) :=
      CompCert4Lean.Lib.Integers.Int.add_assoc_proof (Int.neg a) a b
    _ = Int.add (Int.neg a) Int.zero := by rw [h]
    _ = Int.neg a := CompCert4Lean.Lib.Integers.Int.add_zero_proof (Int.neg a)

private theorem int_neg_add_distr_local
    (y z : CompCert4Lean.Lib.Integers.int) :
    Int.neg (Int.add y z) = Int.add (Int.neg y) (Int.neg z) := by
  apply Eq.symm
  apply int_neg_unique_local
  calc
    Int.add (Int.add y z) (Int.add (Int.neg y) (Int.neg z)) =
        Int.add y (Int.add z (Int.add (Int.neg y) (Int.neg z))) :=
      CompCert4Lean.Lib.Integers.Int.add_assoc_proof y z _
    _ = Int.add y (Int.add (Int.neg y) (Int.add z (Int.neg z))) := by
      exact congrArg (fun q => Int.add y q)
        (int_add_permut_local z (Int.neg y) (Int.neg z))
    _ = Int.add (Int.add y (Int.neg y)) (Int.add z (Int.neg z)) :=
      (CompCert4Lean.Lib.Integers.Int.add_assoc_proof y (Int.neg y) _).symm
    _ = Int.add Int.zero Int.zero := by
      rw [int_add_neg_self_local y, int_add_neg_self_local z]
    _ = Int.zero := CompCert4Lean.Lib.Integers.Int.add_zero_proof Int.zero

private theorem int_sub_add_r_local
    (x y z : CompCert4Lean.Lib.Integers.int) :
    Int.sub x (Int.add y z) = Int.add (Int.sub x y) (Int.neg z) := by
  calc
    Int.sub x (Int.add y z) = Int.add x (Int.neg (Int.add y z)) :=
      CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof x (Int.add y z)
    _ = Int.add x (Int.add (Int.neg y) (Int.neg z)) := by
      rw [int_neg_add_distr_local]
    _ = Int.add (Int.add x (Int.neg y)) (Int.neg z) :=
      (CompCert4Lean.Lib.Integers.Int.add_assoc_proof x (Int.neg y) (Int.neg z)).symm
    _ = Int.add (Int.sub x y) (Int.neg z) := by
      exact congrArg (fun q => Int.add q (Int.neg z))
        (CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof x y).symm

theorem sub_add_r : sub_add_rStatement := by
  intro v1 v2 i
  cases v1 <;> cases v2 <;>
    simp [sub, add, CompCert4Lean.X86_64.Archi.ptr64]
  case Vint.Vint a b =>
    exact int_sub_add_r_local a b i

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem and_commut : and_commutStatement := by
  intro x y
  cases x <;> cases y <;>
    simp [and]
  case Vint.Vint a b =>
    change Int.and a b = Int.and b a
    exact CompCert4Lean.Lib.Integers.Int.and_commut_proof a b

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem or_commut : or_commutStatement := by
  intro x y
  cases x <;> cases y <;> simp [or]
  rename_i a b
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.or a b).val =
    (CompCert4Lean.Lib.Integers.WordCore.or b a).val
  simp only [CompCert4Lean.Lib.Integers.WordCore.or]
  have ha : a.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := a.toFin.isLt
  have hb : b.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := b.toFin.isLt
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.lor a.val b.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.lor b.val a.val))).val
  simp only [repr_val_of_lt (Nat.lor a.val b.val) (Nat.or_lt_two_pow ha hb),
    repr_val_of_lt (Nat.lor b.val a.val) (Nat.or_lt_two_pow hb ha)]
  exact Nat.or_comm _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem xor_commut : xor_commutStatement := by
  intro x y
  cases x <;> cases y <;> simp [xor]
  rename_i a b
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.xor a b).val =
    (CompCert4Lean.Lib.Integers.WordCore.xor b a).val
  simp only [CompCert4Lean.Lib.Integers.WordCore.xor]
  have ha : a.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := a.toFin.isLt
  have hb : b.val < 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize := b.toFin.isLt
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.xor a.val b.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.xor b.val a.val))).val
  simp only [repr_val_of_lt (Nat.xor a.val b.val) (Nat.xor_lt_two_pow ha hb),
    repr_val_of_lt (Nat.xor b.val a.val) (Nat.xor_lt_two_pow hb ha)]
  exact Nat.xor_comm _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem not_xor : not_xorStatement := by
  intro x
  cases x <;> simp [notint, xor]
  rename_i a
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.not a).val =
    (CompCert4Lean.Lib.Integers.WordCore.xor a Int.mone).val
  have hmone : Int.mone.val = 2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1 := by
    rfl
  simp only [CompCert4Lean.Lib.Integers.WordCore.not,
    CompCert4Lean.Lib.Integers.WordCore.xor]
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.xor a.val (2 ^ CompCert4Lean.Lib.Integers.Int.wordsize - 1)))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr
        CompCert4Lean.Lib.Integers.Int.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.xor a.val Int.mone.val))).val
  rw [hmone]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem int64_add_commut_local
    (a b : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.add a b =
      CompCert4Lean.Lib.Integers.Int64.add b a := by
  unfold CompCert4Lean.Lib.Integers.Int64.add
  unfold CompCert4Lean.Lib.Integers.WordCore.add
  apply congrArg
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Lib.Integers.WordCore.unsigned,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  exact Int.add_comm _ _

theorem addl_commut : addl_commutStatement := by
  intro x y
  cases x <;> cases y <;> try rfl
  case Vlong.Vlong a b =>
    exact congrArg Vlong (int64_add_commut_local a b)

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open Lean Elab Tactic Meta

private theorem int64_add_assoc_local
    (a b c : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.add
        (CompCert4Lean.Lib.Integers.Int64.add a b) c =
      CompCert4Lean.Lib.Integers.Int64.add a
        (CompCert4Lean.Lib.Integers.Int64.add b c) := by
  change CompCert4Lean.Lib.Integers.Ptrofs.add
      (CompCert4Lean.Lib.Integers.Ptrofs.add a b) c =
    CompCert4Lean.Lib.Integers.Ptrofs.add a
      (CompCert4Lean.Lib.Integers.Ptrofs.add b c)
  exact CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api a b c

private theorem int64_repr_unsigned_local
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  have hnonneg :
      0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) := by
    have hx := x.intrange.1
    change (-1 : Int) <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned x) at hx
    omega
  have hmax :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned x) ≤
        (2 ^ 64 : Int) - 1 := by
    have hx := x.intrange.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int64.modulus at hx
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Lib.Integers.Int64.unsigned x) < (2 ^ 64 : Int) at hx
    omega
  have hrepr :
      CompCert4Lean.Lib.Integers.WordCore.unsigned
        (CompCert4Lean.Lib.Integers.Int64.repr
          (CompCert4Lean.Lib.Integers.Int64.unsigned x)) =
        CompCert4Lean.Lib.Integers.Int64.unsigned x := by
    have hzi : CompCert4Lean.Lib.Integers.Int64.unsigned x =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int64.unsigned x)) :=
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ _).symm
    rw [hzi]
    change (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned x)))).intval =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned x))
    let w := CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned x)))
    have hi : w.val =
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Lib.Integers.Int64.unsigned x) %
          ((2 ^ 64 : Nat) : Int)).toNat := by
      dsimp [w]
      run_tac
        let env ← getEnv
        let some (n, _) := env.constants.toList.find?
            (fun (n, _) => (toString n).endsWith "WordCore.val_repr")
          | throwError "frozen WordCore.val_repr helper not found"
        let stx := Lean.mkIdent n
        let arg := Lean.mkIdent `x
        evalTactic
          (← `(tactic| exact $stx 64
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
              (CompCert4Lean.Lib.Integers.Int64.unsigned $arg))))
    have hwi : w.intval =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat w.val := by
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
    have hlt :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int64.unsigned x) <
          ((2 ^ 64 : Nat) : Int) := by
      omega
    rw [Int.emod_eq_of_lt hnonneg hlt]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (↑(Int.toNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int64.unsigned x))) : Int) = _
    rw [Int.toNat_of_nonneg hnonneg]
  exact hrepr

private theorem ptrofs_of_int64_add_local
    (a b : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.of_int64
        (CompCert4Lean.Lib.Integers.Int64.add a b) =
      CompCert4Lean.Lib.Integers.Ptrofs.add
        (CompCert4Lean.Lib.Integers.Ptrofs.of_int64 a)
        (CompCert4Lean.Lib.Integers.Ptrofs.of_int64 b) := by
  have ha : CompCert4Lean.Lib.Integers.Ptrofs.of_int64 a = a := by
    unfold CompCert4Lean.Lib.Integers.Ptrofs.of_int64
    change CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned a) = a
    exact int64_repr_unsigned_local a
  have hb : CompCert4Lean.Lib.Integers.Ptrofs.of_int64 b = b := by
    unfold CompCert4Lean.Lib.Integers.Ptrofs.of_int64
    change CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned b) = b
    exact int64_repr_unsigned_local b
  have hab : CompCert4Lean.Lib.Integers.Ptrofs.of_int64
        (CompCert4Lean.Lib.Integers.Int64.add a b) =
      CompCert4Lean.Lib.Integers.Int64.add a b := by
    unfold CompCert4Lean.Lib.Integers.Ptrofs.of_int64
    change CompCert4Lean.Lib.Integers.Int64.repr
        (CompCert4Lean.Lib.Integers.Int64.unsigned
          (CompCert4Lean.Lib.Integers.Int64.add a b)) = _
    exact int64_repr_unsigned_local _
  rw [ha, hb, hab]
  rfl

private theorem ptrofs_permut_local
    (a b c : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add a
        (CompCert4Lean.Lib.Integers.Ptrofs.add b c) =
      CompCert4Lean.Lib.Integers.Ptrofs.add b
        (CompCert4Lean.Lib.Integers.Ptrofs.add a c) := by
  calc
    CompCert4Lean.Lib.Integers.Ptrofs.add a
          (CompCert4Lean.Lib.Integers.Ptrofs.add b c) =
        CompCert4Lean.Lib.Integers.Ptrofs.add
          (CompCert4Lean.Lib.Integers.Ptrofs.add a b) c :=
      (CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api _ _ _).symm
    _ = CompCert4Lean.Lib.Integers.Ptrofs.add
          (CompCert4Lean.Lib.Integers.Ptrofs.add b a) c := by
      exact congrArg
        (fun t => CompCert4Lean.Lib.Integers.Ptrofs.add t c)
        (CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api a b)
    _ = CompCert4Lean.Lib.Integers.Ptrofs.add b
          (CompCert4Lean.Lib.Integers.Ptrofs.add a c) :=
      CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api _ _ _

theorem addl_assoc : addl_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;>
    simp [addl, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64]
  all_goals try exact int64_add_assoc_local _ _ _
  all_goals try rw [ptrofs_of_int64_add_local]
  all_goals
    simp [CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api,
      CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api]
  all_goals
    exact ptrofs_permut_local _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem addl_permut : addl_permutStatement := by
  intro x y z
  rw [← addl_assoc, addl_commut x y, addl_assoc]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem addl_permut_4 : addl_permut_4Statement := by
  intro x y z t
  rw [addl_permut, addl_assoc, addl_permut]
  exact (addl_assoc _ _ _).symm

open Lean Elab Tactic Meta
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_wordcore_val_repr_local (bits : Nat) (i : _root_.Int) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits (zOfInt i)).val =
      _root_.Int.toNat (i % (((2 ^ bits : Nat) : _root_.Int))) := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "WordCore.val_repr")
      | throwError "frozen WordCore.val_repr helper not found"
    let stx := Lean.mkIdent n
    let bitsArg := Lean.mkIdent `bits
    let iArg := Lean.mkIdent `i
    evalTactic (← `(tactic| exact $stx $bitsArg $iArg))

private theorem pg_wordcore_intval_eq_zOfNat_val_local {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    x.intval = zOfNat x.val := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "WordCore.intval_eq_zOfNat_val")
      | throwError "frozen WordCore.intval_eq_zOfNat_val helper not found"
    let stx := Lean.mkIdent n
    let xArg := Lean.mkIdent `x
    evalTactic (← `(tactic| exact $stx $xArg))

private theorem pg_wordcore_add_val_int_local {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    _root_.Int.ofNat (CompCert4Lean.Lib.Integers.WordCore.add x y).val =
      (_root_.Int.ofNat x.val + _root_.Int.ofNat y.val) %
        _root_.Int.ofNat (2 ^ bits) := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "WordCore.add_val_int")
      | throwError "frozen WordCore.add_val_int helper not found"
    let stx := Lean.mkIdent n
    let xArg := Lean.mkIdent `x
    let yArg := Lean.mkIdent `y
    evalTactic (← `(tactic| exact $stx $xArg $yArg))

private theorem pg_wordcore_sub_val_int_local {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    _root_.Int.ofNat (CompCert4Lean.Lib.Integers.WordCore.sub x y).val =
      (_root_.Int.ofNat x.val - _root_.Int.ofNat y.val) %
        _root_.Int.ofNat (2 ^ bits) := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "WordCore.sub_val_int")
      | throwError "frozen WordCore.sub_val_int helper not found"
    let stx := Lean.mkIdent n
    let xArg := Lean.mkIdent `x
    let yArg := Lean.mkIdent `y
    evalTactic (← `(tactic| exact $stx $xArg $yArg))

private theorem pg_wordcore_neg_val_int_local {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    _root_.Int.ofNat (CompCert4Lean.Lib.Integers.WordCore.neg x).val =
      (-_root_.Int.ofNat x.val) % _root_.Int.ofNat (2 ^ bits) := by
  unfold CompCert4Lean.Lib.Integers.WordCore.neg
  have hrepr : zOpp (CompCert4Lean.Lib.Integers.WordCore.unsigned x) =
      zOfInt (-_root_.Int.ofNat x.val) := by
    change zOfInt (-intOfZ x.intval) = zOfInt (-_root_.Int.ofNat x.val)
    rw [pg_wordcore_intval_eq_zOfNat_val_local x]
    simp only [zOfNat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      intOfZ_zOfInt]
  change _root_.Int.ofNat
      (CompCert4Lean.Lib.Integers.WordCore.repr bits
        (zOpp (CompCert4Lean.Lib.Integers.WordCore.unsigned x))).val = _
  rw [hrepr, pg_wordcore_val_repr_local]
  exact _root_.Int.toNat_of_nonneg
    (_root_.Int.emod_nonneg _ (_root_.Int.ne_of_gt
      (_root_.Int.natCast_pos.mpr (Nat.two_pow_pos bits))))

private theorem pg_wordcore_sub_add_opp_local {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.sub x y =
      CompCert4Lean.Lib.Integers.WordCore.add x
        (CompCert4Lean.Lib.Integers.WordCore.neg y) := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  apply _root_.Int.ofNat.inj
  rw [pg_wordcore_sub_val_int_local, pg_wordcore_add_val_int_local,
    pg_wordcore_neg_val_int_local]
  rw [_root_.Int.sub_eq_add_neg, _root_.Int.add_emod_emod]

private theorem pg_ptrofs_of_int64_eq_local
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.of_int64 x = x := by
  unfold CompCert4Lean.Lib.Integers.Ptrofs.of_int64
  change CompCert4Lean.Lib.Integers.Int64.repr
      (CompCert4Lean.Lib.Integers.Int64.unsigned x) = x
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "int64_repr_unsigned_local")
      | throwError "frozen Int64 repr-unsigned helper not found"
    let stx := Lean.mkIdent n
    let xArg := Lean.mkIdent `x
    evalTactic (← `(tactic| exact $stx $xArg))

theorem subl_addl_opp : subl_addl_oppStatement := by
  intro x y
  cases x <;>
    simp [subl, addl, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64,
      pg_ptrofs_of_int64_eq_local]
  all_goals
    exact pg_wordcore_sub_add_opp_local _ _

private theorem pg_ptrofs_to_int64_eq_local
    (x : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.to_int64 x = x := by
  unfold CompCert4Lean.Lib.Integers.Ptrofs.to_int64
  change CompCert4Lean.Lib.Integers.Int64.repr
      (CompCert4Lean.Lib.Integers.Int64.unsigned x) = x
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "int64_repr_unsigned_local")
      | throwError "frozen Int64 repr-unsigned helper not found"
    let stx := Lean.mkIdent n
    let xArg := Lean.mkIdent `x
    evalTactic (← `(tactic| exact $stx $xArg))

theorem subl_addl_l : subl_addl_lStatement := by
  intro v1 v2 i
  cases v1 <;> cases v2 <;>
    simp [subl, addl, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64,
      pg_ptrofs_of_int64_eq_local, pg_ptrofs_to_int64_eq_local]
  case Vlong.Vlong a b =>
    change CompCert4Lean.Lib.Integers.Ptrofs.sub
        (CompCert4Lean.Lib.Integers.Ptrofs.add a i) b =
      CompCert4Lean.Lib.Integers.Ptrofs.add
        (CompCert4Lean.Lib.Integers.Ptrofs.sub a b) i
    exact CompCert4Lean.Lib.Integers.Ptrofs.sub_add_l_proof_api a i b
  case Vptr.Vlong b ofs n =>
    exact CompCert4Lean.Lib.Integers.Ptrofs.sub_add_l_proof_api ofs i n
  case Vptr.Vptr b1 ofs1 b2 ofs2 =>
    split <;> simp_all [pg_ptrofs_to_int64_eq_local]
    exact congrArg Vlong
      (CompCert4Lean.Lib.Integers.Ptrofs.sub_add_l_proof_api ofs1 i ofs2)

private theorem pg_wordcore_sub_add_r_swapped_local {bits : Nat}
    (x y z : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.sub x
        (CompCert4Lean.Lib.Integers.WordCore.add y z) =
      CompCert4Lean.Lib.Integers.WordCore.add
        (CompCert4Lean.Lib.Integers.WordCore.sub x y)
        (CompCert4Lean.Lib.Integers.WordCore.neg z) := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  apply _root_.Int.ofNat.inj
  rw [pg_wordcore_sub_val_int_local, pg_wordcore_add_val_int_local,
    pg_wordcore_add_val_int_local, pg_wordcore_sub_val_int_local,
    pg_wordcore_neg_val_int_local]
  simp only [_root_.Int.emod_sub_emod, _root_.Int.sub_emod_emod,
    _root_.Int.emod_add_emod, _root_.Int.add_emod_emod]
  congr 1
  omega

theorem subl_addl_r : subl_addl_rStatement := by
  intro v1 v2 i
  cases v1 <;> cases v2 <;>
    simp [subl, addl, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64,
      pg_ptrofs_of_int64_eq_local, pg_ptrofs_to_int64_eq_local]
  case Vlong.Vlong a b =>
    change CompCert4Lean.Lib.Integers.WordCore.sub a
        (CompCert4Lean.Lib.Integers.WordCore.add b i) =
      CompCert4Lean.Lib.Integers.WordCore.add
        (CompCert4Lean.Lib.Integers.WordCore.sub a b)
        (CompCert4Lean.Lib.Integers.WordCore.neg i)
    exact pg_wordcore_sub_add_r_swapped_local a b i
  case Vptr.Vlong b ofs n =>
    change CompCert4Lean.Lib.Integers.WordCore.sub ofs
        (CompCert4Lean.Lib.Integers.WordCore.add n i) =
      CompCert4Lean.Lib.Integers.WordCore.add
        (CompCert4Lean.Lib.Integers.WordCore.sub ofs n)
        (CompCert4Lean.Lib.Integers.WordCore.neg i)
    exact pg_wordcore_sub_add_r_swapped_local ofs n i
  case Vptr.Vptr b1 ofs1 b2 ofs2 =>
    split <;> simp_all [pg_ptrofs_to_int64_eq_local]
    exact congrArg Vlong (pg_wordcore_sub_add_r_swapped_local ofs1 ofs2 i)

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private abbrev pg_mull_zMul :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul

private theorem pg_int64_mul_commut_local
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.mul x y =
      CompCert4Lean.Lib.Integers.Int64.mul y x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  unfold CompCert4Lean.Lib.Integers.Int64.mul
    CompCert4Lean.Lib.Integers.WordCore.mul
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (pg_mull_zMul x.intval y.intval)).val =
    (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (pg_mull_zMul y.intval x.intval)).val
  rw [pg_wordcore_intval_eq_zOfNat_val_local x,
    pg_wordcore_intval_eq_zOfNat_val_local y]
  simp only [pg_mull_zMul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul]
  have hxz :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val) =
        (x.val : Int) := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat] using
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat x.val))
  have hyz :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat y.val) =
        (y.val : Int) := by
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat] using
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat y.val))
  rw [hxz, hyz]
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      ((x.val : Int) * (y.val : Int)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        ((y.val : Int) * (x.val : Int)) by rw [Int.mul_comm]]

theorem mull_commut : mull_commutStatement := by
  intro x y
  cases x <;> cases y <;> simp [mull]
  exact pg_int64_mul_commut_local _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open Lean Elab Tactic Meta

private def pg_andl_suffix_private_name (suffix : String) : Name :=
  let p := Name.str (Name.str (Name.str (Name.str Name.anonymous "_private") "CompCert4Lean") "Lib") "Integers"
  let base := Name.num p 0
  suffix.splitOn "." |>.foldl Name.str base

private theorem pg_andl_suffix_word_val_repr64 (bits : Nat) (i : Int) :
    (CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  run_tac
    let lctx ← getLCtx
    let bitsF := (lctx.findFromUserName? `bits).get!
    let iF := (lctx.findFromUserName? `i).get!
    let bitsE := mkFVar bitsF.fvarId
    let iE := mkFVar iF.fvarId
    let e ← mkAppM
      (pg_andl_suffix_private_name "CompCert4Lean.Lib.Integers.WordCore.val_repr")
      #[bitsE, iE]
    closeMainGoal Name.anonymous e

private theorem pg_andl_repr_val_of_lt64 (n : Nat) (hn : n < 2 ^ 64) :
    (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n)).val = n := by
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n) by rfl,
    pg_andl_suffix_word_val_repr64]
  have hmod :
      Int.ofNat n % ((2 ^ 64 : Nat) : Int) = Int.ofNat n := by
    apply Int.emod_eq_of_lt
    · exact Int.natCast_nonneg n
    · exact Int.ofNat_lt.mpr hn
  rw [hmod]
  rfl

private theorem pg_andl_int64_commut
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.and x y =
      CompCert4Lean.Lib.Integers.Int64.and y x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  unfold CompCert4Lean.Lib.Integers.Int64.and
    CompCert4Lean.Lib.Integers.WordCore.and
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.land x.val y.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr 64
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.land y.val x.val))).val
  rw [pg_andl_repr_val_of_lt64 (Nat.land x.val y.val)
        (Nat.and_lt_two_pow _ y.toFin.isLt),
      pg_andl_repr_val_of_lt64 (Nat.land y.val x.val)
        (Nat.and_lt_two_pow _ x.toFin.isLt)]
  exact Nat.and_comm _ _

theorem andl_commut : andl_commutStatement := by
  intro x y
  cases x <;> cases y <;> try rfl
  case Vlong.Vlong x y =>
    change Vlong (CompCert4Lean.Lib.Integers.Int64.and x y) =
      Vlong (CompCert4Lean.Lib.Integers.Int64.and y x)
    rw [pg_andl_int64_commut]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem pg_orl_int64_commut
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.or x y =
      CompCert4Lean.Lib.Integers.Int64.or y x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  unfold CompCert4Lean.Lib.Integers.Int64.or
    CompCert4Lean.Lib.Integers.WordCore.or
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.lor x.val y.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr 64
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.lor y.val x.val))).val
  rw [pg_andl_repr_val_of_lt64 (Nat.lor x.val y.val)
        (Nat.or_lt_two_pow x.toFin.isLt y.toFin.isLt),
      pg_andl_repr_val_of_lt64 (Nat.lor y.val x.val)
        (Nat.or_lt_two_pow y.toFin.isLt x.toFin.isLt)]
  exact Nat.or_comm _ _

theorem orl_commut : orl_commutStatement := by
  intro x y
  cases x <;> cases y <;> try rfl
  case Vlong.Vlong x y =>
    change Vlong (CompCert4Lean.Lib.Integers.Int64.or x y) =
      Vlong (CompCert4Lean.Lib.Integers.Int64.or y x)
    rw [pg_orl_int64_commut]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem pg_xorl_int64_commut
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.xor x y =
      CompCert4Lean.Lib.Integers.Int64.xor y x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  unfold CompCert4Lean.Lib.Integers.Int64.xor
    CompCert4Lean.Lib.Integers.WordCore.xor
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr 64
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.xor x.val y.val))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr 64
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.xor y.val x.val))).val
  rw [pg_andl_repr_val_of_lt64 (Nat.xor x.val y.val)
        (Nat.xor_lt_two_pow x.toFin.isLt y.toFin.isLt),
      pg_andl_repr_val_of_lt64 (Nat.xor y.val x.val)
        (Nat.xor_lt_two_pow y.toFin.isLt x.toFin.isLt)]
  simpa only [Nat.xor_eq] using (Nat.xor_comm x.val y.val)

theorem xorl_commut : xorl_commutStatement := by
  intro x y
  cases x <;> cases y <;> try rfl
  case Vlong.Vlong x y =>
    change Vlong (CompCert4Lean.Lib.Integers.Int64.xor x y) =
      Vlong (CompCert4Lean.Lib.Integers.Int64.xor y x)
    rw [pg_xorl_int64_commut]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem notl_xorl : notl_xorlStatement := by
  intro x
  cases x <;> simp [notl, xorl]
  rename_i a
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  change (CompCert4Lean.Lib.Integers.WordCore.not a).val =
    (CompCert4Lean.Lib.Integers.WordCore.xor a Int64.mone).val
  have hmone : Int64.mone.val = 2 ^ CompCert4Lean.Lib.Integers.Int64.wordsize - 1 := by
    rfl
  simp only [CompCert4Lean.Lib.Integers.WordCore.not,
    CompCert4Lean.Lib.Integers.WordCore.xor]
  change
    (CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.xor a.val (2 ^ CompCert4Lean.Lib.Integers.Int64.wordsize - 1)))).val =
      (CompCert4Lean.Lib.Integers.WordCore.repr
        CompCert4Lean.Lib.Integers.Int64.wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
          (Nat.xor a.val Int64.mone.val))).val
  rw [hmone]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open Lean Elab Tactic Meta

private theorem pg_values_int64_is_power2'_correct
    (n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.unsigned n =
      two_p (CompCert4Lean.Lib.Integers.Int.unsigned logn) := by
  unfold CompCert4Lean.Lib.Integers.Int64.is_power2' at hpow
  generalize hbits : CompCert4Lean.Lib.Zbits.Z_one_bits
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (CompCert4Lean.Lib.Integers.Int64.unsigned n) Z0 = bits at hpow
  cases bits with
  | nil => simp at hpow
  | cons i rest =>
      cases rest with
      | nil =>
          simp only at hpow
          cases hpow
          have hirange := CompCert4Lean.Lib.Zbits.Z_one_bits_range
            CompCert4Lean.Lib.Integers.Int64.wordsize
            (CompCert4Lean.Lib.Integers.Int64.unsigned n) i
            (by rw [hbits]; simp)
          have himax : ZArith.BinInt.Z.le i
              CompCert4Lean.Lib.Integers.Int.max_unsigned := by
            have hlt := hirange.2
            change intOfZ i < 64 at hlt
            change intOfZ i ≤ 2 ^ 32 - 1
            omega
          have hi : CompCert4Lean.Lib.Integers.Int.unsigned
              (CompCert4Lean.Lib.Integers.Int.repr i) = i :=
            CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api i
              ⟨hirange.1, himax⟩
          rw [hi]
          have hn0 : ZArith.BinInt.Z.le Z0
              (CompCert4Lean.Lib.Integers.Int64.unsigned n) := by
            have h := n.intrange.1
            change (-1 : Int) < intOfZ n.intval at h
            change 0 ≤ intOfZ n.intval
            omega
          have hnrange : ZArith.BinInt.Z.le Z0
                (CompCert4Lean.Lib.Integers.Int64.unsigned n) ∧
              ZArith.BinInt.Z.lt (CompCert4Lean.Lib.Integers.Int64.unsigned n)
                CompCert4Lean.Lib.Integers.Int64.modulus :=
            ⟨hn0, n.intrange.2⟩
          have hseries := CompCert4Lean.Lib.Zbits.Z_one_bits_powerserie
            CompCert4Lean.Lib.Integers.Int64.wordsize
            (CompCert4Lean.Lib.Integers.Int64.unsigned n) hnrange
          rw [hbits] at hseries
          rw [hseries]
          apply intOfZ_injective
          simp only [CompCert4Lean.Lib.Zbits.powerserie, ZArith.BinInt.Z.add,
            intOfZ_zOfInt]
          change intOfZ (two_p i) + 0 = intOfZ (two_p i)
          omega
      | cons j rest => simp at hpow

private theorem pg_values_int64_one_mul
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.mul
        CompCert4Lean.Lib.Integers.Int64.one x = x := by
  unfold CompCert4Lean.Lib.Integers.Int64.mul
    CompCert4Lean.Lib.Integers.WordCore.mul
  rw [show CompCert4Lean.Lib.Integers.WordCore.unsigned
      CompCert4Lean.Lib.Integers.Int64.one = Zpos xH by rfl]
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (ZArith.BinInt.Z.mul (Zpos xH)
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x)) = x
  rw [ZArith.BinInt.Zmult_1_l_proof]
  have hu : CompCert4Lean.Lib.Integers.Int64.repr
      (CompCert4Lean.Lib.Integers.Int64.unsigned x) = x := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "int64_repr_unsigned_local")
        | throwError "frozen Int64 repr-unsigned helper not found"
      let stx := Lean.mkIdent n
      let xArg := Lean.mkIdent `x
      evalTactic (← `(tactic| exact $stx $xArg))
  exact hu

private theorem pg_values_int64_mul_pow2
    (x n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.mul x n =
      CompCert4Lean.Lib.Integers.Int64.shl' x logn := by
  have hc := pg_values_int64_is_power2'_correct n logn hpow
  have hc' : CompCert4Lean.Lib.Integers.WordCore.unsigned n =
      two_p (CompCert4Lean.Lib.Integers.Int.unsigned logn) := hc
  unfold CompCert4Lean.Lib.Integers.Int64.mul
    CompCert4Lean.Lib.Integers.WordCore.mul
    CompCert4Lean.Lib.Integers.Int64.shl'
  rw [hc']
  change CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (ZArith.BinInt.Z.mul
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (two_p (CompCert4Lean.Lib.Integers.Int.unsigned logn))) =
    CompCert4Lean.Lib.Integers.WordCore.repr
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (ZArith.BinInt.Z.shiftl
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int.unsigned logn))
  rw [ZArith.BinInt.Z.shiftl_mul_pow2
    (CompCert4Lean.Lib.Integers.Int64.unsigned x)
    (CompCert4Lean.Lib.Integers.Int.unsigned logn) (by
      have h := logn.intrange.1
      change (-1 : Int) < intOfZ logn.intval at h
      change 0 ≤ intOfZ logn.intval
      omega)]
  rfl

private theorem pg_values_int64_divs_pow2
    (x n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.divs x n =
      CompCert4Lean.Lib.Integers.Int64.shrx' x logn := by
  unfold CompCert4Lean.Lib.Integers.Int64.shrx'
  rw [← pg_values_int64_mul_pow2
    CompCert4Lean.Lib.Integers.Int64.one n logn hpow]
  rw [pg_values_int64_one_mul]

theorem divls_pow2 : divls_pow2Statement := by
  intro x n logn y hpow hlt hdiv
  cases x with
  | Vlong i =>
      simp only [divls] at hdiv
      split at hdiv
      · cases hdiv
      · cases hdiv
        simp only [shrxl, hlt, if_true, Option.some.injEq,
          val.Vlong.injEq]
        exact (pg_values_int64_divs_pow2 i n logn hpow).symm
  | Vundef => simp [divls] at hdiv
  | Vint i => simp [divls] at hdiv
  | Vfloat f => simp [divls] at hdiv
  | Vsingle f => simp [divls] at hdiv
  | Vptr b ofs => simp [divls] at hdiv

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_values_zshiftr_div_two_p (x y : Z)
    (hy : ZArith.BinInt.Z.le Z0 y) :
    ZArith.BinInt.Z.shiftr x y = ZArith.BinInt.Z.div x (two_p y) := by
  change 0 ≤ intOfZ y at hy
  have hpow : intOfZ (two_p y) =
      Int.pow 2 (Int.toNat (intOfZ y)) := by
    unfold two_p ZArith.Zpower.two_p ZArith.BinInt.Z.pow
    rw [if_neg (by omega)]
    simp only [intOfZ_zOfInt]
    have hbase : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
    rw [hbase]
  apply intOfZ_injective
  simp [ZArith.BinInt.Z.shiftr, ZArith.BinInt.Z.div, hy]
  rw [intOfZ_zOfInt, intOfZ_zOfInt, hpow]
  change Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y))) =
    (if Int.pow 2 (Int.toNat (intOfZ y)) = 0 then 0
      else if 0 < Int.pow 2 (Int.toNat (intOfZ y)) then
        Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y)))
      else
        let d := -(Int.pow 2 (Int.toNat (intOfZ y)))
        let q := Int.ediv (intOfZ x) d
        let r := Int.emod (intOfZ x) d
        if r = 0 then -q else -(q + 1))
  have hp : 0 < Int.pow 2 (Int.toNat (intOfZ y)) :=
    Int.pow_pos (by omega)
  simp [hp, Int.ne_of_gt hp]

private theorem pg_values_int64_shru'_div_two_p
    (x : CompCert4Lean.Lib.Integers.Int64.int)
    (y : CompCert4Lean.Lib.Integers.Int.int) :
    CompCert4Lean.Lib.Integers.Int64.shru' x y =
      CompCert4Lean.Lib.Integers.Int64.repr
        (ZArith.BinInt.Z.div (CompCert4Lean.Lib.Integers.Int64.unsigned x)
          (two_p (CompCert4Lean.Lib.Integers.Int.unsigned y))) := by
  unfold CompCert4Lean.Lib.Integers.Int64.shru'
  change CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.shiftr
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int.unsigned y)) = _
  rw [pg_values_zshiftr_div_two_p]
  have h := y.intrange.1
  change (-1 : Int) < intOfZ y.intval at h
  change 0 ≤ intOfZ y.intval
  omega

private theorem pg_values_int64_divu_pow2
    (x n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.divu x n =
      CompCert4Lean.Lib.Integers.Int64.shru' x logn := by
  have hc := pg_values_int64_is_power2'_correct n logn hpow
  unfold CompCert4Lean.Lib.Integers.Int64.divu
    CompCert4Lean.Lib.Integers.WordCore.divu
  change CompCert4Lean.Lib.Integers.Int64.repr
      (ZArith.BinInt.Z.div
        (CompCert4Lean.Lib.Integers.Int64.unsigned x)
        (CompCert4Lean.Lib.Integers.Int64.unsigned n)) =
    CompCert4Lean.Lib.Integers.Int64.shru' x logn
  rw [hc, pg_values_int64_shru'_div_two_p]

private theorem pg_values_int_ltu_repr_64 (p : Z)
    (hp : ZArith.BinInt.Z.le Z0 p ∧ ZArith.BinInt.Z.lt p (zOfNat 64)) :
    CompCert4Lean.Lib.Integers.Int.ltu (CompCert4Lean.Lib.Integers.Int.repr p)
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
  have hpmax : ZArith.BinInt.Z.le p CompCert4Lean.Lib.Integers.Int.max_unsigned := by
    change intOfZ p ≤ 2 ^ 32 - 1
    have h := hp.2
    change intOfZ p < 64 at h
    omega
  have hu : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr p) = p :=
    CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api p ⟨hp.1, hpmax⟩
  have hi : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = zOfNat 64 := by
    unfold CompCert4Lean.Lib.Integers.Int64.iwordsize'
    apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
    constructor
    · change (0 : Int) ≤ 64
      omega
    · change (64 : Int) ≤ 2 ^ 32 - 1
      omega
  have hrev : CompCert4Lean.Lib.Integers.Int.ltu
      CompCert4Lean.Lib.Integers.Int64.iwordsize'
      (CompCert4Lean.Lib.Integers.Int.repr p) = false := by
    cases hval : CompCert4Lean.Lib.Integers.Int.ltu
        CompCert4Lean.Lib.Integers.Int64.iwordsize'
        (CompCert4Lean.Lib.Integers.Int.repr p) with
    | false => rfl
    | true =>
        have hr := CompCert4Lean.Lib.Integers.Int.ltu_inv_proof
          CompCert4Lean.Lib.Integers.Int64.iwordsize'
          (CompCert4Lean.Lib.Integers.Int.repr p) hval
        rw [hi, hu] at hr
        have hge := hr.2
        have hlt := hp.2
        change intOfZ (zOfNat 64) < intOfZ p at hge
        change intOfZ p < intOfZ (zOfNat 64) at hlt
        omega
  have hneq : CompCert4Lean.Lib.Integers.Int.repr p ≠
      CompCert4Lean.Lib.Integers.Int64.iwordsize' := by
    intro h
    have he := congrArg CompCert4Lean.Lib.Integers.Int.unsigned h
    rw [hu, hi] at he
    have hlt := hp.2
    change intOfZ p < intOfZ (zOfNat 64) at hlt
    rw [he] at hlt
    exact (Int.lt_irrefl _ hlt).elim
  have hvalneq : (CompCert4Lean.Lib.Integers.Int.repr p).intval ≠
      CompCert4Lean.Lib.Integers.Int64.iwordsize'.intval := by
    intro h
    exact hneq (CompCert4Lean.Lib.Integers.WordCore.ext h)
  have heq : CompCert4Lean.Lib.Integers.Int.eq
      (CompCert4Lean.Lib.Integers.Int.repr p)
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = false := by
    unfold CompCert4Lean.Lib.Integers.Int.eq CompCert4Lean.Lib.Integers.WordCore.eq
    simp [hvalneq]
  have hnot := CompCert4Lean.Lib.Integers.Int.not_ltu_proof
    (CompCert4Lean.Lib.Integers.Int.repr p)
    CompCert4Lean.Lib.Integers.Int64.iwordsize'
  rw [hrev, heq] at hnot
  simpa using hnot.symm

private theorem pg_values_int64_is_power2'_range
    (n : CompCert4Lean.Lib.Integers.Int64.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2' n = some logn) :
    CompCert4Lean.Lib.Integers.Int.ltu logn
      CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
  unfold CompCert4Lean.Lib.Integers.Int64.is_power2' at hpow
  generalize hbits : CompCert4Lean.Lib.Zbits.Z_one_bits
      CompCert4Lean.Lib.Integers.Int64.wordsize
      (CompCert4Lean.Lib.Integers.Int64.unsigned n) Z0 = bits at hpow
  cases bits with
  | nil => simp at hpow
  | cons i rest =>
      cases rest with
      | nil =>
          simp only at hpow
          cases hpow
          apply pg_values_int_ltu_repr_64
          exact CompCert4Lean.Lib.Zbits.Z_one_bits_range
            CompCert4Lean.Lib.Integers.Int64.wordsize
            (CompCert4Lean.Lib.Integers.Int64.unsigned n) i
            (by rw [hbits]; simp)
      | cons j rest => simp at hpow

theorem divlu_pow2 : divlu_pow2Statement := by
  intro x n logn y hpow hdiv
  cases x with
  | Vlong i =>
      simp only [divlu] at hdiv
      split at hdiv
      · cases hdiv
      · cases hdiv
        simp only [shrlu, pg_values_int64_is_power2'_range n logn hpow,
          if_true, val.Vlong.injEq]
        exact (pg_values_int64_divu_pow2 i n logn hpow).symm
  | Vundef => simp [divlu] at hdiv
  | Vint i => simp [divlu] at hdiv
  | Vfloat f => simp [divlu] at hdiv
  | Vsingle f => simp [divlu] at hdiv
  | Vptr b ofs => simp [divlu] at hdiv

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open Lean Elab Tactic Meta

private theorem pg_values_int64_zOfNat_val
    (x : CompCert4Lean.Lib.Integers.Int64.int) :
    zOfNat x.val = CompCert4Lean.Lib.Integers.Int64.unsigned x := by
  exact (pg_wordcore_intval_eq_zOfNat_val_local x).symm

private theorem pg_values_positive_is_power2
    (p : positive) (h : CompCert4Lean.Lib.Zbits.P_is_power2 p = true) :
    ∃ k : Nat, posToNat p = 2 ^ k := by
  induction p with
  | xH => exact ⟨0, rfl⟩
  | xI p ih => simp [CompCert4Lean.Lib.Zbits.P_is_power2] at h
  | xO p ih =>
      have hp : CompCert4Lean.Lib.Zbits.P_is_power2 p = true := by
        simpa [CompCert4Lean.Lib.Zbits.P_is_power2] using h
      rcases ih hp with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [posToNat, hk, Nat.pow_succ]
      omega

private theorem pg_values_int64_is_power2_nat
    (n logn : CompCert4Lean.Lib.Integers.Int64.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2 n = some logn) :
    ∃ k : Nat, n.val = 2 ^ k := by
  unfold CompCert4Lean.Lib.Integers.Int64.is_power2 at hpow
  cases hu : CompCert4Lean.Lib.Integers.Int64.unsigned n with
  | Z0 =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zneg p =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zpos p =>
      cases hp : CompCert4Lean.Lib.Zbits.P_is_power2 p with
      | false =>
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu, hp,
            Bool.false_eq_true, ↓reduceIte] at hpow
          cases hpow
      | true =>
          rcases pg_values_positive_is_power2 p hp with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          have hz := (pg_values_int64_zOfNat_val n).trans hu
          have hi : Int.ofNat n.val = Int.ofNat (posToNat p) := by
            calc
              Int.ofNat n.val = intOfZ (zOfNat n.val) := by
                exact (intOfZ_zOfInt (Int.ofNat n.val)).symm
              _ = intOfZ (Zpos p) := congrArg intOfZ hz
              _ = Int.ofNat (posToNat p) := rfl
          exact (Int.ofNat.inj hi).trans hk

private theorem pg_values_word_sub_val {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    (CompCert4Lean.Lib.Integers.WordCore.sub x y).val =
      (2 ^ bits - y.val + x.val) % (2 ^ bits) := by
  run_tac
    let lctx ← getLCtx
    let xF := (lctx.findFromUserName? `x).get!
    let yF := (lctx.findFromUserName? `y).get!
    let e ← mkAppM
      (pg_andl_suffix_private_name "CompCert4Lean.Lib.Integers.WordCore.sub_val")
      #[mkFVar xF.fvarId, mkFVar yF.fvarId]
    closeMainGoal Name.anonymous e

private theorem pg_values_int64_sub_one_val
    (n : CompCert4Lean.Lib.Integers.Int64.int) (hnpos : 0 < n.val) :
    (CompCert4Lean.Lib.Integers.Int64.sub n
      CompCert4Lean.Lib.Integers.Int64.one).val = n.val - 1 := by
  change (CompCert4Lean.Lib.Integers.WordCore.sub n
      CompCert4Lean.Lib.Integers.Int64.one).val = n.val - 1
  rw [pg_values_word_sub_val]
  change (2 ^ 64 - 1 + n.val) % (2 ^ 64) = n.val - 1
  have hnlt : n.val < 2 ^ 64 := n.toFin.isLt
  have hadd : 2 ^ 64 - 1 + n.val = (n.val - 1) + 2 ^ 64 := by omega
  rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem pg_values_int64_and_val
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    (CompCert4Lean.Lib.Integers.Int64.and x y).val = Nat.land x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.and
    CompCert4Lean.Lib.Integers.WordCore.and
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
    (zOfNat (Nat.land x.val y.val))).val = Nat.land x.val y.val
  exact pg_andl_repr_val_of_lt64 _ (Nat.and_lt_two_pow _ y.toFin.isLt)

private theorem pg_values_modulo_nat (a b : Nat) (hb : 0 < b) :
    ZArith.BinInt.Z.modulo (zOfNat a) (zOfNat b) = zOfNat (a % b) := by
  run_tac
    let env ← getEnv
    let some (n, _) := env.constants.toList.find?
        (fun (n, _) => (toString n).endsWith "suffix_modulo_nat")
      | throwError "frozen modulo helper not found"
    let stx := Lean.mkIdent n
    let aArg := Lean.mkIdent `a
    let bArg := Lean.mkIdent `b
    let hbArg := Lean.mkIdent `hb
    evalTactic (← `(tactic| exact $stx $aArg $bArg $hbArg))

private theorem pg_values_int64_modu_val
    (x n : CompCert4Lean.Lib.Integers.Int64.int) (hnpos : 0 < n.val) :
    (CompCert4Lean.Lib.Integers.Int64.modu x n).val = x.val % n.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.modu
    CompCert4Lean.Lib.Integers.WordCore.modu
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
    (ZArith.BinInt.Z.modulo
      (CompCert4Lean.Lib.Integers.Int64.unsigned x)
      (CompCert4Lean.Lib.Integers.Int64.unsigned n))).val = x.val % n.val
  rw [← pg_values_int64_zOfNat_val x, ← pg_values_int64_zOfNat_val n,
    pg_values_modulo_nat _ _ hnpos]
  exact pg_andl_repr_val_of_lt64 _ (by
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hnpos)
      (Nat.le_of_lt n.toFin.isLt))

private theorem pg_values_int64_modu_and
    (x n logn : CompCert4Lean.Lib.Integers.Int64.int)
    (hpow : CompCert4Lean.Lib.Integers.Int64.is_power2 n = some logn) :
    CompCert4Lean.Lib.Integers.Int64.modu x n =
      CompCert4Lean.Lib.Integers.Int64.and x
        (CompCert4Lean.Lib.Integers.Int64.sub n
          CompCert4Lean.Lib.Integers.Int64.one) := by
  rcases pg_values_int64_is_power2_nat n logn hpow with ⟨k, hnk⟩
  have hnpos : 0 < n.val := by
    rw [hnk]
    exact Nat.two_pow_pos k
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [pg_values_int64_modu_val x n hnpos, pg_values_int64_and_val,
    pg_values_int64_sub_one_val n hnpos, hnk]
  exact (Nat.and_two_pow_sub_one_eq_mod x.val k).symm

theorem modlu_pow2 : modlu_pow2Statement := by
  intro x n logn y hpow hmod
  cases x with
  | Vlong i =>
      simp only [modlu] at hmod
      split at hmod
      · cases hmod
      · cases hmod
        simp only [andl, val.Vlong.injEq]
        exact (pg_values_int64_modu_and i n logn hpow).symm
  | Vundef => simp [modlu] at hmod
  | Vint i => simp [modlu] at hmod
  | Vfloat f => simp [modlu] at hmod
  | Vsingle f => simp [modlu] at hmod
  | Vptr b ofs => simp [modlu] at hmod

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Lib.Integers

theorem negate_cmp_bool : negate_cmp_boolStatement := by
  intro c x y
  cases c <;> cases x <;> cases y <;>
    simp [cmp_bool, negate_comparison, CompCert4Lean.Lib.Integers.Int.cmp,
      CompCert4Lean.Lib.Integers.WordCore.cmp,
      CompCert4Lean.Lib.Coqlib.option_map]

theorem negate_cmpu_bool : negate_cmpu_boolStatement := by
  intro valid_ptr c x y
  cases c <;> cases x <;> cases y <;>
    simp [cmpu_bool, negate_comparison, cmp_different_blocks,
      CompCert4Lean.Lib.Integers.Int.cmp,
      CompCert4Lean.Lib.Integers.Int.cmpu,
      CompCert4Lean.Lib.Integers.Int64.cmp,
      CompCert4Lean.Lib.Integers.Int64.cmpu,
      CompCert4Lean.Lib.Integers.Ptrofs.cmpu,
      CompCert4Lean.Lib.Integers.WordCore.cmp,
      CompCert4Lean.Lib.Integers.WordCore.cmpu,
      CompCert4Lean.X86_64.Archi.ptr64,
      CompCert4Lean.Lib.Coqlib.option_map]

theorem negate_cmpl_bool : negate_cmpl_boolStatement := by
  intro c x y
  cases c <;> cases x <;> cases y <;>
    simp [cmpl_bool, negate_comparison, CompCert4Lean.Lib.Integers.Int64.cmp,
      CompCert4Lean.Lib.Integers.WordCore.cmp,
      CompCert4Lean.Lib.Coqlib.option_map]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Lib.Integers

theorem negate_cmplu_bool : negate_cmplu_boolStatement := by
  have hneg : ∀ c,
      cmp_different_blocks (negate_comparison c) =
        CompCert4Lean.Lib.Coqlib.option_map Bool.not (cmp_different_blocks c) := by
    intro c
    cases c <;> rfl
  intro valid_ptr c x y
  unfold cmplu_bool
  simp only [hneg]
  cases harch : CompCert4Lean.X86_64.Archi.ptr64 <;>
    cases c <;> cases x <;> cases y <;>
      simp [harch, negate_comparison,
        CompCert4Lean.Lib.Integers.Int64.cmp,
        CompCert4Lean.Lib.Integers.Int64.cmpu,
        CompCert4Lean.Lib.Integers.Ptrofs.cmpu,
        CompCert4Lean.Lib.Integers.WordCore.cmp,
        CompCert4Lean.Lib.Integers.WordCore.cmpu,
        CompCert4Lean.Lib.Coqlib.option_map]
  all_goals
    repeat first | split | simp_all [cmp_different_blocks]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Lib.Integers

theorem swap_cmp_bool : swap_cmp_boolStatement := by
  intro c x y
  cases c <;> cases x <;> cases y <;>
    simp [cmp_bool, swap_comparison,
      CompCert4Lean.Lib.Integers.Int.cmp,
      CompCert4Lean.Lib.Integers.WordCore.cmp,
      CompCert4Lean.Lib.Integers.WordCore.eq, eq_comm]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Lib.Integers

theorem swap_cmpu_bool : swap_cmpu_boolStatement := by
  intro valid_ptr c x y
  cases c <;> cases x <;> cases y <;>
    simp [cmpu_bool, CompCert4Lean.X86_64.Archi.ptr64, swap_comparison,
      CompCert4Lean.Lib.Integers.Int.cmpu,
      CompCert4Lean.Lib.Integers.WordCore.cmpu,
      CompCert4Lean.Lib.Integers.WordCore.eq, eq_comm]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Lib.Integers

theorem swap_cmpl_bool : swap_cmpl_boolStatement := by
  intro c x y
  cases c <;> cases x <;> cases y <;>
    simp [cmpl_bool, swap_comparison, Int64.cmp, WordCore.cmp,
      WordCore.eq, eq_comm]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Lib.Integers

theorem lessdef_same : lessdef_sameStatement := by
  intro v1 v2 h
  cases h
  exact lessdef_refl v1

theorem lessdef_trans : lessdef_transStatement := by
  intro v1 v2 v3 h12 h23
  cases h12 with
  | lessdef_refl => exact h23
  | lessdef_undef => exact lessdef_undef _

theorem zero_ext_and : zero_ext_andStatement := by
  intro n v hn
  cases v with
  | Vundef => rfl
  | Vint x =>
      simp only [zero_ext, and]
      congr 1
      exact CompCert4Lean.Lib.Integers.Int.zero_ext_and_proof n x hn
  | Vlong _ => rfl
  | Vfloat _ => rfl
  | Vsingle _ => rfl
  | Vptr _ _ => rfl

theorem swap_cmplu_bool : swap_cmplu_boolStatement := by
  have hcmp64 : ∀ c (x y : CompCert4Lean.Lib.Integers.Int64.int),
      CompCert4Lean.Lib.Integers.Int64.cmpu (swap_comparison c) x y =
        CompCert4Lean.Lib.Integers.Int64.cmpu c y x := by
    intro c x y
    cases c with
    | Ceq =>
        change decide (x.intval = y.intval) = decide (y.intval = x.intval)
        by_cases h : x.intval = y.intval
        · simp [h]
        · have h' : ¬y.intval = x.intval := by
            intro hyx
            exact h hyx.symm
          simp [h, h']
    | Cne =>
        change (!decide (x.intval = y.intval)) = (!decide (y.intval = x.intval))
        by_cases h : x.intval = y.intval
        · simp [h]
        · have h' : ¬y.intval = x.intval := by
            intro hyx
            exact h hyx.symm
          simp [h, h']
    | Clt => rfl
    | Cle => rfl
    | Cgt => rfl
    | Cge => rfl
  have hcmpPtrofs : ∀ c (x y : CompCert4Lean.Lib.Integers.Ptrofs.int),
      CompCert4Lean.Lib.Integers.Ptrofs.cmpu (swap_comparison c) x y =
        CompCert4Lean.Lib.Integers.Ptrofs.cmpu c y x := by
    intro c x y
    cases c with
    | Ceq =>
        change decide (x.intval = y.intval) = decide (y.intval = x.intval)
        by_cases h : x.intval = y.intval
        · simp [h]
        · have h' : ¬y.intval = x.intval := by
            intro hyx
            exact h hyx.symm
          simp [h, h']
    | Cne =>
        change (!decide (x.intval = y.intval)) = (!decide (y.intval = x.intval))
        by_cases h : x.intval = y.intval
        · simp [h]
        · have h' : ¬y.intval = x.intval := by
            intro hyx
            exact h hyx.symm
          simp [h, h']
    | Clt => rfl
    | Cle => rfl
    | Cgt => rfl
    | Cge => rfl
  have hdiff : ∀ c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c := by
    intro c
    cases c <;> rfl
  have hblock : ∀ (b1 b2 : block),
      boolOfSumbool (eq_block b1 b2) = boolOfSumbool (eq_block b2 b1) := by
    intro b1 b2
    by_cases h : b1 = b2
    · subst b2
      rfl
    · have h' : b2 ≠ b1 := by
        intro h'
        exact h h'.symm
      change boolOfSumbool (CompCert4Lean.Lib.Coqlib.peq b1 b2) =
        boolOfSumbool (CompCert4Lean.Lib.Coqlib.peq b2 b1)
      cases heq : CompCert4Lean.Lib.Coqlib.peq b1 b2 with
      | left hab => exact (h hab).elim
      | right hne =>
          cases heq' : CompCert4Lean.Lib.Coqlib.peq b2 b1 with
          | left hba => exact (h' hba).elim
          | right hne' => rfl
  intro valid_ptr c x y
  unfold cmplu_bool
  simp only [hdiff]
  cases harch : CompCert4Lean.X86_64.Archi.ptr64 <;>
    cases c <;> cases x <;> cases y <;>
      simp [harch, hcmp64, hcmpPtrofs, hblock]
  all_goals
    repeat first | split | simp_all [cmp_different_blocks, hcmp64, hcmpPtrofs]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem lessdef_list_trans : lessdef_list_transStatement := by
  intro vl1 vl2 h12 vl3 h23
  induction h12 generalizing vl3 with
  | lessdef_list_nil =>
      cases h23
      exact lessdef_list_nil
  | lessdef_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      cases h23 with
      | lessdef_list_cons _ v3 _ vl3 hhead23 htail23 =>
          exact lessdef_list_cons _ _ _ _
            (lessdef_trans _ _ _ hhead hhead23) (ih vl3 htail23)

theorem load_result_lessdef : load_result_lessdefStatement := by
  intro chunk v1 v2 h
  cases h with
  | lessdef_refl =>
      exact lessdef_refl _
  | lessdef_undef =>
      cases chunk <;> cases v2 <;> simp [load_result]
      all_goals exact lessdef_undef _

theorem norm_bool_is_lessdef : norm_bool_is_lessdefStatement := by
  intro v
  unfold norm_bool
  by_cases h : is_bool v
  · simp [h]
    exact lessdef_refl v
  · simp [h]
    exact lessdef_undef v

theorem norm_bool_lessdef : norm_bool_lessdefStatement := by
  intro v1 v2 h
  cases h with
  | lessdef_refl =>
      exact lessdef_refl _
  | lessdef_undef =>
      have hu : norm_bool Vundef = Vundef := by
        rfl
      rw [hu]
      exact lessdef_undef _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem add_lessdef : add_lessdefStatement := by
  intro v1 v1' v2 v2' h1 h2
  cases h1 with
  | lessdef_refl v1 =>
      cases h2 with
      | lessdef_refl v2 => exact lessdef_refl _
      | lessdef_undef =>
          cases v1 <;> simp [add] <;> exact lessdef_undef _
  | lessdef_undef =>
      exact lessdef_undef _

theorem addl_lessdef : addl_lessdefStatement := by
  intro v1 v1' v2 v2' h1 h2
  cases h1 with
  | lessdef_refl v1 =>
      cases h2 with
      | lessdef_refl v2 => exact lessdef_refl _
      | lessdef_undef =>
          cases v1 <;> simp [addl] <;> exact lessdef_undef _
  | lessdef_undef =>
      exact lessdef_undef _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem cmpu_bool_lessdef : cmpu_bool_lessdefStatement := by
  intro valid_ptr valid_ptr' c v1 v1' v2 v2' b hvalid h1 h2 hcmp
  have hvalid_or : ∀ b ofs,
      (valid_ptr b ofs = true ∨ valid_ptr b (zSub ofs z1) = true) →
      (valid_ptr' b ofs = true ∨ valid_ptr' b (zSub ofs z1) = true) := by
    intro b ofs h
    rcases h with h | h
    · exact Or.inl (hvalid b ofs h)
    · exact Or.inr (hvalid b (zSub ofs z1) h)
  cases h1 with
  | lessdef_undef =>
      cases v1' <;> simp [cmpu_bool] at hcmp
  | lessdef_refl =>
      cases h2 with
      | lessdef_undef =>
          cases v1 <;> simp [cmpu_bool] at hcmp
      | lessdef_refl =>
          cases harch : CompCert4Lean.X86_64.Archi.ptr64 <;>
            cases c <;> cases v1 <;> cases v2 <;>
              simp [cmpu_bool, harch, cmp_different_blocks, hvalid_or, hvalid] at hcmp ⊢ <;>
              try assumption
          all_goals
            repeat first | split at hcmp | simp_all [hvalid_or, hvalid]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem cmplu_bool_lessdef : cmplu_bool_lessdefStatement := by
  intro valid_ptr valid_ptr' c v1 v1' v2 v2' b hvalid h1 h2 hcmp
  have hvalid_or : ∀ b ofs,
      (valid_ptr b ofs = true ∨ valid_ptr b (zSub ofs z1) = true) →
      (valid_ptr' b ofs = true ∨ valid_ptr' b (zSub ofs z1) = true) := by
    intro b ofs h
    rcases h with h | h
    · exact Or.inl (hvalid b ofs h)
    · exact Or.inr (hvalid b (zSub ofs z1) h)
  cases h1 with
  | lessdef_undef =>
      cases v1' <;> simp [cmplu_bool] at hcmp
  | lessdef_refl =>
      cases h2 with
      | lessdef_undef =>
          cases v1 <;> simp [cmplu_bool] at hcmp
      | lessdef_refl =>
          cases harch : CompCert4Lean.X86_64.Archi.ptr64 <;>
            cases c <;> cases v1 <;> cases v2 <;>
              simp [cmplu_bool, harch, cmp_different_blocks, hvalid_or, hvalid] at hcmp ⊢ <;>
              try assumption
          all_goals
            repeat first | split at hcmp | simp_all [hvalid_or, hvalid]

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem of_optbool_lessdef : of_optbool_lessdefStatement := by
  intro ob ob' h
  cases ob with
  | none => exact lessdef_undef _
  | some b =>
      have hb : ob' = some b := h b rfl
      cases hb
      exact lessdef_refl _

theorem longofwords_lessdef : longofwords_lessdefStatement := by
  intro v1 v2 v1' v2' h1 h2
  cases h1 with
  | lessdef_refl =>
      cases h2 with
      | lessdef_refl => exact lessdef_refl _
      | lessdef_undef =>
          cases v1 <;> simp [longofwords] <;> exact lessdef_undef _
  | lessdef_undef =>
      exact lessdef_undef _

theorem loword_lessdef : loword_lessdefStatement := by
  intro v v' h
  cases h with
  | lessdef_refl => exact lessdef_refl _
  | lessdef_undef => exact lessdef_undef _

theorem hiword_lessdef : hiword_lessdefStatement := by
  intro v v' h
  cases h with
  | lessdef_refl => exact lessdef_refl _
  | lessdef_undef => exact lessdef_undef _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem lessdef_normalize : lessdef_normalizeStatement := by
  intro v ty
  cases v with
  | Vundef => exact lessdef_refl _
  | Vint n =>
      cases ty <;> simp [normalize] <;>
        first | exact lessdef_refl _ | exact lessdef_undef _
  | Vlong n =>
      cases ty <;> simp [normalize] <;>
        first | exact lessdef_refl _ | exact lessdef_undef _
  | Vfloat f =>
      cases ty <;> simp [normalize] <;>
        first | exact lessdef_refl _ | exact lessdef_undef _
  | Vsingle f =>
      cases ty <;> simp [normalize] <;>
        first | exact lessdef_refl _ | exact lessdef_undef _
  | Vptr b ofs =>
      cases ty <;> cases harch : CompCert4Lean.X86_64.Archi.ptr64 <;>
        simp [normalize, harch] <;>
        first | exact lessdef_refl _ | exact lessdef_undef _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem normalize_lessdef : normalize_lessdefStatement := by
  intro v v' ty h
  cases h with
  | lessdef_refl v => exact lessdef_refl _
  | lessdef_undef v => exact lessdef_undef _

theorem has_argtype_lessdef : has_argtype_lessdefStatement := by
  intro v r v' harg hld
  cases hld with
  | lessdef_refl => exact harg
  | lessdef_undef =>
      cases r <;> simp [has_argtype] at harg ⊢

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem has_argtype_list_lessdef : has_argtype_list_lessdefStatement := by
  intro vl rl vl' harg hld
  induction hld generalizing rl with
  | lessdef_list_nil =>
      cases harg
      exact CompCert4Lean.Lib.Coqlib.list_forall2.nil _
  | lessdef_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      cases harg with
      | cons _ _ hheadArg htailArg =>
          exact CompCert4Lean.Lib.Coqlib.list_forall2.cons _ _
            (has_argtype_lessdef _ _ _ hheadArg hhead)
            (ih _ htailArg)

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem load_result_inject : load_result_injectStatement := by
  intro f chunk v1 v2 h
  cases h with
  | inject_int i =>
      cases chunk with
      | Mbool =>
          by_cases hb : is_bool (Vint (intZeroExt (zOfNat 8) i)) = true
          · simp [load_result, norm_bool, hb]
            exact inject_int _ _
          · simp [load_result, norm_bool, hb]
            exact val_inject_undef _ _
      | Mint8signed => simp [load_result]; exact inject_int _ _
      | Mint8unsigned => simp [load_result]; exact inject_int _ _
      | Mint16signed => simp [load_result]; exact inject_int _ _
      | Mint16unsigned => simp [load_result]; exact inject_int _ _
      | Mint32 => exact inject_int _ _
      | Mint64 => simp [load_result]; exact val_inject_undef _ _
      | Mfloat32 => simp [load_result]; exact val_inject_undef _ _
      | Mfloat64 => simp [load_result]; exact val_inject_undef _ _
      | Many32 => exact inject_int _ _
      | Many64 => exact inject_int _ _
  | inject_long i =>
      cases chunk <;>
        simp [load_result, norm_bool] <;>
        first | exact inject_long _ _ | exact val_inject_undef _ _
  | inject_float x =>
      cases chunk <;>
        simp [load_result, norm_bool] <;>
        first | exact inject_float _ _ | exact val_inject_undef _ _
  | inject_single x =>
      cases chunk <;>
        simp [load_result, norm_bool] <;>
        first | exact inject_single _ _ | exact val_inject_undef _ _
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      cases chunk <;>
        simp [load_result, norm_bool, CompCert4Lean.X86_64.Archi.ptr64] <;>
        first | exact inject_ptr _ _ _ _ _ _ hmap hofs | exact val_inject_undef _ _
  | val_inject_undef v =>
      cases chunk <;> exact val_inject_undef _ _

theorem add_inject : add_injectStatement := by
  intro f v1 v1' v2 v2' h1 h2
  cases h1 <;> cases h2 <;>
    simp [add, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64] <;>
    constructor <;>
    try assumption
  all_goals
    subst_vars
    rw [Ptrofs.add_assoc_proof_api, Ptrofs.add_assoc_proof_api]
    congr 1
    exact Ptrofs.add_comm_proof_api _ _

theorem sub_inject : sub_injectStatement := by
  intro f v1 v1' v2 v2' h1 h2
  cases h1 <;> cases h2 <;>
    simp [sub, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64] <;>
    try constructor <;>
    try assumption

theorem offset_ptr_inject : offset_ptr_injectStatement := by
  intro f v v' ofs h
  cases h with
  | inject_int i =>
      simpa [offset_ptr] using (val_inject_undef f (offset_ptr (Vint i) ofs))
  | inject_long i =>
      simpa [offset_ptr] using (val_inject_undef f (offset_ptr (Vlong i) ofs))
  | inject_float x =>
      simpa [offset_ptr] using (val_inject_undef f (offset_ptr (Vfloat x) ofs))
  | inject_single x =>
      simpa [offset_ptr] using (val_inject_undef f (offset_ptr (Vsingle x) ofs))
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      simp [offset_ptr]
      apply Val.inject_ptr f b1 _ b2 _ delta hmap
      subst ofs2
      rw [CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api,
        CompCert4Lean.Lib.Integers.Ptrofs.add_assoc_proof_api]
      congr 1
      exact CompCert4Lean.Lib.Integers.Ptrofs.add_commut_proof_api _ _
  | val_inject_undef v =>
      simpa [offset_ptr] using (val_inject_undef f (offset_ptr v' ofs))

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem longofwords_inject : longofwords_injectStatement := by
  intro f v1 v2 v1' v2' h1 h2
  cases h1 with
  | inject_int i1 =>
      cases h2 with
      | inject_int i2 => simpa [longofwords] using (inject_long f (Int64.ofwords i1 i2))
      | inject_long _ => exact val_inject_undef _ _
      | inject_float _ => exact val_inject_undef _ _
      | inject_single _ => exact val_inject_undef _ _
      | inject_ptr _ _ _ _ _ _ _ => exact val_inject_undef _ _
      | val_inject_undef _ => exact val_inject_undef _ _
  | inject_long _ => exact val_inject_undef _ _
  | inject_float _ => exact val_inject_undef _ _
  | inject_single _ => exact val_inject_undef _ _
  | inject_ptr _ _ _ _ _ _ _ => exact val_inject_undef _ _
  | val_inject_undef _ => exact val_inject_undef _ _

theorem loword_inject : loword_injectStatement := by
  intro f v v' h
  cases h with
  | inject_int _ => exact val_inject_undef _ _
  | inject_long i => simpa [loword] using (inject_int f (Int64.loword i))
  | inject_float _ => exact val_inject_undef _ _
  | inject_single _ => exact val_inject_undef _ _
  | inject_ptr _ _ _ _ _ _ _ => exact val_inject_undef _ _
  | val_inject_undef _ => exact val_inject_undef _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem cmpu_bool_inject : cmpu_bool_injectStatement := by
  intro f valid_ptr1 valid_ptr2
  dsimp only
  intro _ _ _ _ c v1 v2 v1' v2' b h1 h2 hcmp
  cases h1 <;> cases h2 <;>
    simp [cmpu_bool, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64] at hcmp ⊢ <;>
    assumption

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem hiword_inject : hiword_injectStatement := by
  intro f v v' h
  cases h with
  | inject_int _ => exact val_inject_undef _ _
  | inject_long i => simpa [hiword] using (inject_int f (Int64.hiword i))
  | inject_float _ => exact val_inject_undef _ _
  | inject_single _ => exact val_inject_undef _ _
  | inject_ptr _ _ _ _ _ _ _ => exact val_inject_undef _ _
  | val_inject_undef _ => exact val_inject_undef _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem normalize_inject : normalize_injectStatement := by
  intro f v v' ty h
  cases h <;> cases ty <;>
    simp [normalize, Archi.ptr64, CompCert4Lean.X86_64.Archi.ptr64] <;>
    constructor <;> try assumption

theorem select_inject : select_injectStatement := by
  intro f ob ob' v1 v1' v2 v2' ty hob h1 h2
  unfold select
  rcases hob with hnone | heq
  · subst ob
    cases ob' <;> simp [normalize] <;> exact val_inject_undef _ _
  · subst ob'
    cases ob with
    | none => exact val_inject_undef _ _
    | some b => cases b <;> simp [normalize] <;> apply normalize_inject <;> assumption

theorem has_argtype_inject : has_argtype_injectStatement := by
  intro f v r v' harg hinj
  cases hinj with
  | inject_int i => cases r <;> simp [has_argtype] at harg ⊢ <;> assumption
  | inject_long i => cases r <;> simp [has_argtype] at harg ⊢ <;> assumption
  | inject_float x => cases r <;> simp [has_argtype] at harg ⊢ <;> assumption
  | inject_single x => cases r <;> simp [has_argtype] at harg ⊢ <;> assumption
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs => cases r <;> simp [has_argtype] at harg ⊢ <;> assumption
  | val_inject_undef v => cases r <;> simp [has_argtype] at harg ⊢

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

theorem inject_incr_trans : inject_incr_transStatement := by
  intro f1 f2 f3 h12 h23 b b' delta hmap
  exact h23 b b' delta (h12 b b' delta hmap)

theorem val_inject_incr : val_inject_incrStatement := by
  intro f1 f2 v v' hincr hinj
  cases hinj with
  | inject_int i => exact Val.inject_int f2 i
  | inject_long i => exact Val.inject_long f2 i
  | inject_float x => exact Val.inject_float f2 x
  | inject_single x => exact Val.inject_single f2 x
  | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
      exact Val.inject_ptr f2 b1 ofs1 b2 ofs2 delta
        (hincr b1 b2 delta hmap) hofs
  | val_inject_undef => exact Val.val_inject_undef f2 v'

theorem val_inject_list_incr : val_inject_list_incrStatement := by
  intro f1 f2 vl vl' hincr hinj
  induction hinj with
  | inject_list_nil => exact Val.inject_list_nil f2
  | inject_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      exact Val.inject_list_cons f2 v1 v2 vl1 vl2
        (val_inject_incr f1 f2 v1 v2 hincr hhead) ih

namespace Val

theorem has_argtype_list_inject : has_argtype_list_injectStatement := by
  intro f vl rl vl' harg hinj
  induction hinj generalizing rl with
  | inject_list_nil =>
      cases harg
      exact CompCert4Lean.Lib.Coqlib.list_forall2.nil _
  | inject_list_cons v1 v2 vl1 vl2 hhead htail ih =>
      cases harg with
      | cons _ _ hheadArg htailArg =>
          exact CompCert4Lean.Lib.Coqlib.list_forall2.cons _ _
            (has_argtype_inject _ _ _ _ hheadArg hhead)
            (ih _ htailArg)

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

open Lean Elab Tactic Meta
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem values_ptrofs_add_zero
    (ofs : CompCert4Lean.Lib.Integers.Ptrofs.int) :
    CompCert4Lean.Lib.Integers.Ptrofs.add ofs
        (CompCert4Lean.Lib.Integers.Ptrofs.repr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 : Z)) = ofs := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  apply _root_.Int.ofNat.inj
  change _root_.Int.ofNat
      (CompCert4Lean.Lib.Integers.WordCore.add ofs
        (CompCert4Lean.Lib.Integers.Ptrofs.repr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 : Z))).val =
    _root_.Int.ofNat ofs.val
  have hadd :
      _root_.Int.ofNat
          (CompCert4Lean.Lib.Integers.WordCore.add ofs
            (CompCert4Lean.Lib.Integers.Ptrofs.repr
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 : Z))).val =
        (_root_.Int.ofNat ofs.val +
            _root_.Int.ofNat
              (CompCert4Lean.Lib.Integers.Ptrofs.repr
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 : Z)).val) %
          _root_.Int.ofNat (2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize) := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "pg_wordcore_add_val_int_local")
        | throwError "frozen WordCore add-value helper not found"
      let stx := Lean.mkIdent n
      let xArg := Lean.mkIdent `ofs
      evalTactic (← `(tactic| exact $stx $xArg
        (CompCert4Lean.Lib.Integers.Ptrofs.repr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 : Z))))
  rw [hadd]
  have hz :
      (CompCert4Lean.Lib.Integers.Ptrofs.repr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.Z0 : Z)).val = 0 := by
    rfl
  rw [hz]
  simp only [_root_.Int.ofNat_eq_natCast, _root_.Int.natCast_zero,
    _root_.Int.add_zero]
  have hlt : ofs.val < 2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize := by
    run_tac
      let env ← getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "WordCore.val_lt")
        | throwError "frozen WordCore value-range helper not found"
      let stx := Lean.mkIdent n
      let xArg := Lean.mkIdent `ofs
      evalTactic (← `(tactic| exact $stx $xArg))
  have hlt' : (ofs.val : Int) <
      (2 ^ CompCert4Lean.Lib.Integers.Ptrofs.wordsize : Int) :=
    Int.ofNat_lt.mpr hlt
  exact Int.emod_eq_of_lt (Int.natCast_nonneg ofs.val) hlt'

end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

theorem val_inject_lessdef : val_inject_lessdefStatement := by
  intro v1 v2
  constructor
  · intro h
    cases h with
    | lessdef_refl =>
        cases v1 with
        | Vundef => exact Val.val_inject_undef _ _
        | Vint i => exact Val.inject_int _ _
        | Vlong i => exact Val.inject_long _ _
        | Vfloat f => exact Val.inject_float _ _
        | Vsingle f => exact Val.inject_single _ _
        | Vptr b ofs =>
            exact Val.inject_ptr _ _ _ _ _ _ rfl
              (values_ptrofs_add_zero ofs).symm
    | lessdef_undef => exact Val.val_inject_undef _ _
  · intro h
    cases h with
    | inject_int i => exact Val.lessdef_refl _
    | inject_long i => exact Val.lessdef_refl _
    | inject_float f => exact Val.lessdef_refl _
    | inject_single f => exact Val.lessdef_refl _
    | inject_ptr b1 ofs1 b2 ofs2 delta hmap hofs =>
        have hp : (b1, z0) = (b2, delta) := Option.some.inj hmap
        have hb : b1 = b2 := congrArg Prod.fst hp
        have hd : z0 = delta := congrArg Prod.snd hp
        subst b2
        subst delta
        rw [values_ptrofs_add_zero] at hofs
        subst ofs2
        exact Val.lessdef_refl _
    | val_inject_undef v => exact Val.lessdef_undef _

end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

theorem val_inject_list_lessdef : val_inject_list_lessdefStatement := by
  intro vl1 vl2
  constructor
  · intro h
    induction h with
    | lessdef_list_nil => exact Val.inject_list_nil _
    | lessdef_list_cons v1 v2 vl1 vl2 hhead htail ih =>
        exact Val.inject_list_cons (fun b => some (b, z0)) v1 v2 vl1 vl2
          (val_inject_lessdef v1 v2 |>.mp hhead) ih
  · intro h
    induction h with
    | inject_list_nil => exact Val.lessdef_list_nil
    | inject_list_cons v1 v2 vl1 vl2 hhead htail ih =>
        exact Val.lessdef_list_cons v1 v2 vl1 vl2
          (val_inject_lessdef v1 v2 |>.mpr hhead) ih

end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values

theorem val_inject_id : val_inject_idStatement := by
  intro v1 v2
  change Val.inject (fun b => some (b, z0)) v1 v2 ↔ Val.lessdef v1 v2
  exact (val_inject_lessdef v1 v2).symm

end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

theorem andl_assoc : andl_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [andl]
  case Vlong.Vlong.Vlong a b c =>
    apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
    rw [pg_values_int64_and_val, pg_values_int64_and_val,
      pg_values_int64_and_val, pg_values_int64_and_val]
    exact Nat.and_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem pg_values_int64_or_val
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    (CompCert4Lean.Lib.Integers.Int64.or x y).val = Nat.lor x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.or
    CompCert4Lean.Lib.Integers.WordCore.or
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
      (Nat.lor x.val y.val))).val = Nat.lor x.val y.val
  exact pg_andl_repr_val_of_lt64 _
    (Nat.or_lt_two_pow x.toFin.isLt y.toFin.isLt)

theorem orl_assoc : orl_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [orl]
  case Vlong.Vlong.Vlong a b c =>
    apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
    rw [pg_values_int64_or_val, pg_values_int64_or_val,
      pg_values_int64_or_val, pg_values_int64_or_val]
    exact Nat.or_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values
namespace Val

private theorem pg_values_int64_xor_val
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    (CompCert4Lean.Lib.Integers.Int64.xor x y).val = Nat.xor x.val y.val := by
  unfold CompCert4Lean.Lib.Integers.Int64.xor
    CompCert4Lean.Lib.Integers.WordCore.xor
  change (CompCert4Lean.Lib.Integers.WordCore.repr 64
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
      (Nat.xor x.val y.val))).val = Nat.xor x.val y.val
  exact CompCert4Lean.Common.Values.Val.pg_andl_repr_val_of_lt64 _
    (Nat.xor_lt_two_pow x.toFin.isLt y.toFin.isLt)

theorem xorl_assoc : xorl_assocStatement := by
  intro x y z
  cases x <;> cases y <;> cases z <;> simp [xorl]
  case Vlong.Vlong.Vlong a b c =>
    apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
    rw [pg_values_int64_xor_val, pg_values_int64_xor_val,
      pg_values_int64_xor_val, pg_values_int64_xor_val]
    exact Nat.xor_assoc _ _ _

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values.Val

theorem load_result_xtype : load_result_xtypeStatement := by
  intro chunk v
  cases chunk <;> cases v <;>
    simp [load_result, has_rettype, CompCert4Lean.Common.AST.xtype_of_chunk,
      CompCert4Lean.X86_64.Archi.ptr64]
  case Mbool.Vint n =>
    rcases norm_bool_cases (Vint (intZeroExt (zOfNat 8) n)) with h | h | h <;>
      simp [h, Vfalse, Vtrue]
  case Mint8signed.Vint n =>
    exact (CompCert4Lean.Lib.Integers.Int.sign_ext_idem_proof
      (zOfNat 8) n (by change (0 : _root_.Int) < 8; decide)).symm
  case Mint8unsigned.Vint n =>
    exact (CompCert4Lean.Lib.Integers.Int.zero_ext_idem_proof_api
      (zOfNat 8) n (by change (0 : _root_.Int) ≤ 8; decide)).symm
  case Mint16signed.Vint n =>
    exact (CompCert4Lean.Lib.Integers.Int.sign_ext_idem_proof
      (zOfNat 16) n (by change (0 : _root_.Int) < 16; decide)).symm
  case Mint16unsigned.Vint n =>
    exact (CompCert4Lean.Lib.Integers.Int.zero_ext_idem_proof_api
      (zOfNat 16) n (by change (0 : _root_.Int) ≤ 16; decide)).symm

end CompCert4Lean.Common.Values.Val

namespace CompCert4Lean.Common.Values.Val

theorem mul_pow2 : mul_pow2Statement := by
  intro x n logn hpow
  have hn : CompCert4Lean.Lib.Integers.Int.shl
      CompCert4Lean.Lib.Integers.Int.one logn = n := by
    run_tac
      let env ← Lean.getEnv
      let some (correct, _) := env.constants.toList.find?
          (fun (name, _) => (toString name).endsWith
            "CompCert4Lean.Lib.Integers.Int.suffix_is_power2_correct")
        | throwError "frozen integer power-of-two correctness helper not found"
      let some (shift, _) := env.constants.toList.find?
          (fun (name, _) => (toString name).endsWith
            "CompCert4Lean.Lib.Integers.Int.suffix_shl_one_eq_of_power2")
        | throwError "frozen integer shift-of-one helper not found"
      let correctId := Lean.mkIdent correct
      let shiftId := Lean.mkIdent shift
      let nId := Lean.mkIdent `n
      let lognId := Lean.mkIdent `logn
      let hpowId := Lean.mkIdent `hpow
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| exact $shiftId $nId $lognId ($correctId $nId $lognId $hpowId)))
  cases x <;> simp only [mul, shl]
  case Vint a =>
    change Vint (CompCert4Lean.Lib.Integers.Int.mul a n) =
      if CompCert4Lean.Lib.Integers.Int.ltu logn
          CompCert4Lean.Lib.Integers.Int.iwordsize then
        Vint (CompCert4Lean.Lib.Integers.Int.shl a logn) else Vundef
    rw [CompCert4Lean.Lib.Integers.Int.is_power2_range_proof n logn hpow]
    simp only [↓reduceIte]
    congr 1
    rw [CompCert4Lean.Lib.Integers.Int.shl_mul_proof, hn]

end CompCert4Lean.Common.Values.Val

namespace CompCert4Lean.Common.Values
namespace Val

theorem mods_divs : mods_divsStatement := by
  intro x y z h
  cases x <;> cases y <;> simp [mods] at h
  case Vint.Vint a b =>
    rcases h with ⟨hcond, hz⟩
    refine ⟨Vint (Int.divs a b), ?_, ?_⟩
    · simp only [divs]
      by_cases ha : Int.eq a (Int.repr Int.min_signed) = true
      · have hb := hcond.2 ha
        simp [hcond.1, ha, hb]
      · simp [hcond.1, ha]
    · subst z
      simp only [sub, mul, CompCert4Lean.X86_64.Archi.ptr64]
      change Vint (Int.mods a b) =
        Vint (Int.sub a (Int.mul (Int.divs a b) b))
      congr 1
      exact CompCert4Lean.Lib.Integers.Int.mods_divs_proof a b

end Val
end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values.Val

theorem divs_pow2 : divs_pow2Statement := by
  intro x n logn y hpow hlt hdiv
  cases x <;> cases y <;> simp [divs, shrx] at hdiv ⊢
  case Vint.Vint =>
    exact ⟨hlt, (CompCert4Lean.Lib.Integers.Int.divs_pow2_proof _ _ _ hpow).symm.trans hdiv.2⟩

end CompCert4Lean.Common.Values.Val


namespace CompCert4Lean.Common.Values.Val

theorem divs_one : divs_oneStatement := by
  intro s
  simp only [divs]
  have hzero : CompCert4Lean.Lib.Integers.Int.eq Int.one Int.zero = false := by decide
  have hmone : CompCert4Lean.Lib.Integers.Int.eq Int.one Int.mone = false := by decide
  have hdiv : CompCert4Lean.Lib.Integers.Int.divs s Int.one = s :=
    CompCert4Lean.Lib.Integers.Int.divs_one_proof s (by
      change (1 : _root_.Int) < 32
      decide)
  simp [hzero, hmone, hdiv]

end CompCert4Lean.Common.Values.Val

namespace CompCert4Lean.Common.Values.Val

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open Lean Elab Tactic Meta

private theorem pg_values_int_is_power2_correct
    (n : CompCert4Lean.Lib.Integers.Int.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int.is_power2 n = some logn) :
    CompCert4Lean.Lib.Integers.Int.unsigned n = two_p
      (CompCert4Lean.Lib.Integers.Int.unsigned logn) := by
  run_tac
    let env ← Lean.getEnv
    let some (correct, _) := env.constants.toList.find?
        (fun (name, _) => (toString name).endsWith
          "CompCert4Lean.Lib.Integers.Int.suffix_is_power2_correct")
      | throwError "frozen integer power-of-two correctness helper not found"
    let correctId := Lean.mkIdent correct
    let nId := Lean.mkIdent `n
    let lognId := Lean.mkIdent `logn
    let hpowId := Lean.mkIdent `hpow
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| exact $correctId $nId $lognId $hpowId))

private theorem pg_values_int_divu_pow2
    (x n logn : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : CompCert4Lean.Lib.Integers.Int.is_power2 n = some logn) :
    CompCert4Lean.Lib.Integers.Int.divu x n =
      CompCert4Lean.Lib.Integers.Int.shru x logn := by
  have hc := pg_values_int_is_power2_correct n logn hpow
  unfold CompCert4Lean.Lib.Integers.Int.divu
    CompCert4Lean.Lib.Integers.WordCore.divu
  change CompCert4Lean.Lib.Integers.Int.repr
      (ZArith.BinInt.Z.div
        (CompCert4Lean.Lib.Integers.Int.unsigned x)
        (CompCert4Lean.Lib.Integers.Int.unsigned n)) =
    CompCert4Lean.Lib.Integers.Int.shru x logn
  rw [hc, CompCert4Lean.Lib.Integers.Int.shru_div_two_p_proof]

theorem divu_pow2 : divu_pow2Statement := by
  intro x n logn y hpow hdiv
  cases x <;> simp [divu] at hdiv ⊢
  case Vint a =>
    rcases hdiv with ⟨hneq, hdiv⟩
    cases hdiv
    simp only [shru,
      CompCert4Lean.Lib.Integers.Int.is_power2_range_proof n logn hpow,
      if_true, val.Vint.injEq]
    exact (pg_values_int_divu_pow2 a n logn hpow).symm

end CompCert4Lean.Common.Values.Val

namespace CompCert4Lean.Common.Values.Val

theorem divu_one : divu_oneStatement := by
  intro s
  simp only [divu]
  have hzero : CompCert4Lean.Lib.Integers.Int.eq Int.one Int.zero = false := by decide
  have hdiv : CompCert4Lean.Lib.Integers.Int.divu s Int.one = s :=
    CompCert4Lean.Lib.Integers.Int.divu_one_proof s
  simp [hzero, hdiv]

end CompCert4Lean.Common.Values.Val
namespace CompCert4Lean.Common.Values
open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats

private theorem modu_pow2_p_pow (p : positive)
    (h : CompCert4Lean.Lib.Zbits.P_is_power2 p = true) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p =
      2 ^ Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
  induction p with
  | xH => decide
  | xO p ih =>
      simp only [CompCert4Lean.Lib.Zbits.P_is_power2] at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hlog : Nat.log2 (2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) =
          Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) + 1 :=
        Nat.log2_two_mul (Nat.ne_of_gt hp)
      calc
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (.xO p) =
            2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by rfl
        _ = 2 * (2 ^ Nat.log2
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) := by
              exact congrArg (fun t => 2 * t) (ih h)
        _ = 2 ^ (Nat.log2
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) + 1) := by
              rw [Nat.pow_succ]
              omega
        _ = 2 ^ Nat.log2
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (.xO p)) := by
              rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat (.xO p) =
                2 * CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p by rfl, hlog]
  | xI p ih =>
      simp only [CompCert4Lean.Lib.Zbits.P_is_power2] at h
      cases h

private theorem modu_pow2_int_pow (n : CompCert4Lean.Lib.Integers.Int.int)
    (logn : CompCert4Lean.Lib.Integers.Int.int)
    (h : CompCert4Lean.Lib.Integers.Int.is_power2 n = some logn) :
    ∃ k : Nat, n.val = 2 ^ k := by
  unfold CompCert4Lean.Lib.Integers.Int.is_power2 at h
  cases n with
  | mkint v hv =>
      simp only [CompCert4Lean.Lib.Integers.Int.unsigned,
        CompCert4Lean.Lib.Integers.WordCore.unsigned] at h
      cases v with
      | Z0 => simp [CompCert4Lean.Lib.Zbits.Z_is_power2] at h
      | Zneg p => simp [CompCert4Lean.Lib.Zbits.Z_is_power2] at h
      | Zpos p =>
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2] at h
          by_cases hpow : CompCert4Lean.Lib.Zbits.P_is_power2 p = true
          · simp [hpow] at h
            refine ⟨Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p), ?_⟩
            have hpw := modu_pow2_p_pow p hpow
            exact hpw
          · simp [hpow] at h

private theorem modu_pow2_intval_eq_zOfNat_val
    (x : CompCert4Lean.Lib.Integers.Int.int) :
    x.intval = CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val := by
  have hx : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval := by
    have h := x.intrange.1
    change (-1 : Int) < CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    omega
  exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
    x.intval hx).symm

private theorem modu_pow2_unsigned_eq_zOfNat_val
    (x : CompCert4Lean.Lib.Integers.Int.int) :
    CompCert4Lean.Lib.Integers.Int.unsigned x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat x.val := by
  exact modu_pow2_intval_eq_zOfNat_val x

private theorem modu_pow2_sub_one_repr (n : CompCert4Lean.Lib.Integers.Int.int)
    (hn : 0 < n.val) :
    CompCert4Lean.Lib.Integers.Int.sub n CompCert4Lean.Lib.Integers.Int.one =
      CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n.val - 1)) := by
  unfold CompCert4Lean.Lib.Integers.Int.sub CompCert4Lean.Lib.Integers.WordCore.sub
  congr 1
  rw [show CompCert4Lean.Lib.Integers.WordCore.unsigned n =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat n.val by
        exact modu_pow2_unsigned_eq_zOfNat_val n]
  have hone : CompCert4Lean.Lib.Integers.Int.unsigned
      CompCert4Lean.Lib.Integers.Int.one =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1 := by rfl
  rw [show CompCert4Lean.Lib.Integers.WordCore.unsigned
      (CompCert4Lean.Lib.Integers.Int.one) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat 1 by exact hone]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hs := Int.ofNat_sub (m := 1) (n := n.val) hn
  simpa only [Int.ofNat_eq_natCast] using hs.symm

private theorem modu_pow2_unsigned_and (x y : CompCert4Lean.Lib.Integers.Int.int) :
    CompCert4Lean.Lib.Integers.Int.unsigned
        (CompCert4Lean.Lib.Integers.Int.and x y) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.land x.val y.val) := by
  unfold CompCert4Lean.Lib.Integers.Int.and CompCert4Lean.Lib.Integers.WordCore.and
  apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
  constructor
  · change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.land x.val y.val))
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact Int.natCast_nonneg _
  · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (Nat.land x.val y.val)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int.max_unsigned
    have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int.max_unsigned = (2 ^ 32 : Int) - 1 := by rfl
    rw [hmax]
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hlt := Nat.and_lt_two_pow x.val
      (by
        have hy := y.intrange.2
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y.intval <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int.modulus) at hy
        change y.val < 2 ^ 32
        have hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
            (CompCert4Lean.Lib.Integers.Int.modulus) = (2 ^ 32 : Int) := by rfl
        have hy' : (y.val : Int) < (2 ^ 32 : Int) := by
          rw [modu_pow2_intval_eq_zOfNat_val y] at hy
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hy
          rw [hz] at hy
          exact hy
        exact (Int.ofNat_lt).mp hy'
        )
    have hltI : (Int.ofNat (Nat.land x.val y.val)) < (2 ^ 32 : Int) :=
      (Int.ofNat_lt).2 hlt
    have hnonneg : (0 : Int) ≤ Int.ofNat (Nat.land x.val y.val) := Int.natCast_nonneg _
    omega

private theorem modu_pow2_mod_z (x n : CompCert4Lean.Lib.Integers.Int.int)
    (hn : 0 < n.val) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
        (CompCert4Lean.Lib.Integers.Int.unsigned x)
        (CompCert4Lean.Lib.Integers.Int.unsigned n) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (x.val % n.val) := by
  rw [modu_pow2_unsigned_eq_zOfNat_val x, modu_pow2_unsigned_eq_zOfNat_val n]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change (if (Int.ofNat n.val) = 0 then Int.ofNat x.val else
    if 0 < Int.ofNat n.val then (Int.ofNat x.val) % Int.ofNat n.val else
      (if (Int.ofNat x.val) % (-(Int.ofNat n.val)) = 0 then 0 else
        (Int.ofNat x.val) % (-(Int.ofNat n.val)) - (-(Int.ofNat n.val)))) =
    Int.ofNat (x.val % n.val)
  have hnI : (0 : Int) < Int.ofNat n.val := (Int.ofNat_lt).2 hn
  rw [if_neg (by omega), if_pos hnI]
  exact (Int.natCast_emod x.val n.val).symm

private theorem modu_pow2_val_lt (x : CompCert4Lean.Lib.Integers.Int.int) :
    x.val < 2 ^ 32 := by
  have hx := x.intrange.2
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int.modulus at hx
  rw [modu_pow2_intval_eq_zOfNat_val x] at hx
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hx
  have hm : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      CompCert4Lean.Lib.Integers.Int.modulus = (2 ^ 32 : Int) := by rfl
  rw [hm] at hx
  exact (Int.ofNat_lt).mp hx

private theorem modu_pow2_unsigned_modu (x n : CompCert4Lean.Lib.Integers.Int.int)
    (hn : 0 < n.val) :
    CompCert4Lean.Lib.Integers.Int.unsigned
        (CompCert4Lean.Lib.Integers.Int.modu x n) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (x.val % n.val) := by
  unfold CompCert4Lean.Lib.Integers.Int.modu CompCert4Lean.Lib.Integers.WordCore.modu
  change CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.modulo
          (CompCert4Lean.Lib.Integers.Int.unsigned x)
          (CompCert4Lean.Lib.Integers.Int.unsigned n))) = _
  rw [modu_pow2_mod_z x n hn]
  apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
  constructor
  · change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (x.val % n.val))
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact Int.natCast_nonneg _
  · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (x.val % n.val)) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int.max_unsigned
    have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int.max_unsigned = (2 ^ 32 : Int) - 1 := by rfl
    rw [hmax]
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hmod : x.val % n.val < n.val := Nat.mod_lt _ hn
    have hnle : n.val ≤ 2 ^ 32 := Nat.le_of_lt (modu_pow2_val_lt n)
    have hlt : x.val % n.val < 2 ^ 32 := Nat.lt_of_lt_of_le hmod hnle
    have hltI : (Int.ofNat (x.val % n.val)) < (2 ^ 32 : Int) :=
      (Int.ofNat_lt).2 hlt
    have hnonneg : (0 : Int) ≤ Int.ofNat (x.val % n.val) := Int.natCast_nonneg _
    omega

private theorem modu_pow2_repr_nat (m : Nat) (hm : m < 2 ^ 32) :
    CompCert4Lean.Lib.Integers.Int.unsigned
        (CompCert4Lean.Lib.Integers.Int.repr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat m)) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat m := by
  apply CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api
  constructor
  · change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat m)
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact Int.natCast_nonneg _
  · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat m) ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int.max_unsigned
    have hmax : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        CompCert4Lean.Lib.Integers.Int.max_unsigned = (2 ^ 32 : Int) - 1 := by rfl
    rw [hmax]
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    have hmI : (Int.ofNat m) < (2 ^ 32 : Int) := (Int.ofNat_lt).2 hm
    omega

private theorem modu_pow2_sub_one_val (n : CompCert4Lean.Lib.Integers.Int.int)
    (hn : 0 < n.val) :
    (CompCert4Lean.Lib.Integers.Int.sub n CompCert4Lean.Lib.Integers.Int.one).val = n.val - 1 := by
  have hsub := modu_pow2_sub_one_repr n hn
  have hm : n.val - 1 < 2 ^ 32 := by
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (modu_pow2_val_lt n)
  have hu := modu_pow2_repr_nat (n.val - 1) hm
  have hu' := modu_pow2_unsigned_eq_zOfNat_val
    (CompCert4Lean.Lib.Integers.Int.sub n CompCert4Lean.Lib.Integers.Int.one)
  rw [hsub] at hu'
  rw [hu] at hu'
  have hz := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hu'
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hz
  have hvr :
      (CompCert4Lean.Lib.Integers.Int.repr
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (n.val - 1))).val =
        n.val - 1 := (Int.ofNat.inj hz).symm
  simpa [hsub] using hvr

private theorem modu_pow2_int_and (x n : CompCert4Lean.Lib.Integers.Int.int)
    (hpow : ∃ k : Nat, n.val = 2 ^ k) :
    CompCert4Lean.Lib.Integers.Int.modu x n =
      CompCert4Lean.Lib.Integers.Int.and x
        (CompCert4Lean.Lib.Integers.Int.sub n CompCert4Lean.Lib.Integers.Int.one) := by
  rcases hpow with ⟨k, hk⟩
  have hn : 0 < n.val := by rw [hk]; exact Nat.two_pow_pos k
  apply CompCert4Lean.Lib.Integers.WordCore.ext
  change CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.modu x n) =
    CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.and x
        (CompCert4Lean.Lib.Integers.Int.sub n CompCert4Lean.Lib.Integers.Int.one))
  rw [modu_pow2_unsigned_modu x n hn, modu_pow2_unsigned_and x
    (CompCert4Lean.Lib.Integers.Int.sub n CompCert4Lean.Lib.Integers.Int.one),
    modu_pow2_sub_one_val n hn, hk]
  congr 1
  exact (Nat.and_two_pow_sub_one_eq_mod x.val k).symm

namespace Val

theorem modu_pow2 : modu_pow2Statement := by
  intro x n logn y hp hm
  cases x with
  | Vint x =>
      simp only [CompCert4Lean.Common.Values.Val.modu] at hm
      split at hm
      next hzero => cases hm
      next hnonzero =>
        cases hm
        simp only [CompCert4Lean.Common.Values.Val.and]
        congr 1
        exact (modu_pow2_int_and x n (modu_pow2_int_pow n logn hp)).symm
  | Vlong i => simp [CompCert4Lean.Common.Values.Val.modu] at hm
  | Vfloat f => simp [CompCert4Lean.Common.Values.Val.modu] at hm
  | Vsingle f => simp [CompCert4Lean.Common.Values.Val.modu] at hm
  | Vptr b ofs => simp [CompCert4Lean.Common.Values.Val.modu] at hm
  | Vundef => simp [CompCert4Lean.Common.Values.Val.modu] at hm

end Val
end CompCert4Lean.Common.Values


namespace CompCert4Lean.Common.Values.Val

theorem shl_mul : shl_mulStatement := by
  intro x y
  cases x <;> cases y <;> simp [shl, mul, Vone]
  case Vint.Vint a b =>
    by_cases h : Int.ltu b Int.iwordsize = true
    · simp [h]
      apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
      change (CompCert4Lean.Lib.Integers.Int.mul a
        (CompCert4Lean.Lib.Integers.Int.shl
          CompCert4Lean.Lib.Integers.Int.one b)).val =
        (CompCert4Lean.Lib.Integers.Int.shl a b).val
      exact congrArg (fun z => z.val)
        (CompCert4Lean.Lib.Integers.Int.shl_mul_proof a b).symm
    · simp [h]

end CompCert4Lean.Common.Values.Val

namespace CompCert4Lean.Common.Values.Val

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shrx_shr : shrx_shrStatement := by
  intro x y z h
  cases x <;> cases y <;> simp only [shrx, reduceCtorEq] at h
  case Vint.Vint p q =>
    split at h
    next hq =>
      cases h
      have hlt := (CompCert4Lean.Lib.Integers.Int.ltu_inv_proof q
        (Int.repr (zOfNat 31)) hq).2
      have hword : Int.ltu q Int.iwordsize = true := by
        apply CompCert4Lean.Lib.Coqlib.zlt_true
        change intOfZ (Int.unsigned q) < (32 : _root_.Int)
        change intOfZ (Int.unsigned q) < (31 : _root_.Int) at hlt
        omega
      refine ⟨p, q, rfl, rfl, ?_⟩
      have hs := CompCert4Lean.Lib.Integers.Int.shrx_shr_proof p q hq
      by_cases hp : Int.lt p Int.zero = true
      · simpa [hp, shr, add, hword] using congrArg Vint hs
      · simpa [hp, shr, hword] using congrArg Vint hs
    next hq => cases h

end CompCert4Lean.Common.Values.Val


namespace CompCert4Lean.Common.Values

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Common.Values

private theorem shrxlimm_uint_val {bits : Nat} (x : WordCore.Word bits) :
    intOfZ (WordCore.unsigned x) = (x.val : _root_.Int) := by
  have h := x.intrange.1
  change (-1 : _root_.Int) < intOfZ x.intval at h
  change intOfZ x.intval = _root_.Int.ofNat (_root_.Int.toNat (intOfZ x.intval))
  exact (_root_.Int.toNat_of_nonneg (by omega)).symm

private theorem shrxlimm_repr_val (bits : Nat) (i : _root_.Int) :
    (WordCore.repr bits (zOfInt i)).val =
      _root_.Int.toNat (i % ((2 ^ bits : Nat) : _root_.Int)) := by
  run_tac
    let env ← Lean.getEnv
    let ns := env.constants.toList.filterMap fun (n, _) =>
      if n.toString.endsWith ".WordCore.val_repr" then some n else none
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent ns.head!) _ _))

private theorem shrxlimm_uint_repr (bits : Nat) (z : Z) :
    intOfZ (WordCore.unsigned (WordCore.repr bits z)) =
      intOfZ z % ((2 ^ bits : Nat) : _root_.Int) := by
  rw [shrxlimm_uint_val]
  have h := shrxlimm_repr_val bits (intOfZ z)
  rw [zOfInt_intOfZ] at h
  rw [h]
  exact _root_.Int.toNat_of_nonneg
    (_root_.Int.emod_nonneg _ (_root_.Int.ne_of_gt
      (_root_.Int.natCast_pos.mpr (Nat.two_pow_pos bits))))

private theorem shrxlimm_signed (x : int64) :
    intOfZ (CompCert4Lean.Lib.Integers.Int64.signed x) =
      if intOfZ x.intval < 9223372036854775808 then intOfZ x.intval
      else intOfZ x.intval - 18446744073709551616 := by
  unfold CompCert4Lean.Lib.Integers.Int64.signed WordCore.signed
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Meta.transform (← g.getType) (post := fun e => do
      if e.getAppFn.constName?.any (fun n =>
          n.toString.startsWith "_private.CompCert4Lean.Lib.Integers.") then
        return .visit (← Lean.Meta.unfoldDefinition e)
      else return .continue)
    Lean.Elab.Tactic.replaceMainGoal [← g.replaceTargetDefEq t]
  dsimp only
  cases CompCert4Lean.Lib.Coqlib.zlt (WordCore.unsigned x) (two_power_nat (CompCert4Lean.Lib.Integers.Int64.wordsize - 1)) with
  | left h =>
      change intOfZ x.intval < 9223372036854775808 at h
      simp [h]
      rfl
  | right h =>
      change 9223372036854775808 ≤ intOfZ x.intval at h
      simp [show ¬intOfZ x.intval < 9223372036854775808 by omega,
        ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      rfl

private theorem shrxlimm_ltu (x y : int) :
    CompCert4Lean.Lib.Integers.Int.ltu x y =
      decide (intOfZ x.intval < intOfZ y.intval) := by
  unfold CompCert4Lean.Lib.Integers.Int.ltu WordCore.ltu
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Meta.transform (← g.getType) (post := fun e => do
      if e.getAppFn.constName?.any (fun n =>
          n.toString.startsWith "_private.CompCert4Lean.Lib.Integers.") then
        return .visit (← Lean.Meta.unfoldDefinition e)
      else return .continue)
    Lean.Elab.Tactic.replaceMainGoal [← g.replaceTargetDefEq t]
  dsimp only
  cases CompCert4Lean.Lib.Coqlib.zlt (WordCore.unsigned x) (WordCore.unsigned y) with
  | left h => simp [show intOfZ x.intval < intOfZ y.intval from h]
  | right h => simp [show ¬intOfZ x.intval < intOfZ y.intval by exact _root_.Int.not_lt.mpr h]

private theorem shrxlimm_repr_intval (bits : Nat) (z : Z) :
    intOfZ (WordCore.repr bits z).intval =
      intOfZ z % ((2 ^ bits : Nat) : _root_.Int) := shrxlimm_uint_repr bits z

private theorem shrxlimm_signed_core (x : WordCore.Word 64) :
    intOfZ (WordCore.signed x) =
      if intOfZ x.intval < 9223372036854775808 then intOfZ x.intval
      else intOfZ x.intval - 18446744073709551616 := shrxlimm_signed x

set_option maxHeartbeats 16000000 in
private theorem shrxlimm_word (x : int64) (n : int)
    (hrange : 0 < intOfZ n.intval ∧ intOfZ n.intval < 63) :
    CompCert4Lean.Lib.Integers.Int64.shrx' x n =
      CompCert4Lean.Lib.Integers.Int64.shr'
        (CompCert4Lean.Lib.Integers.Int64.add x
          (CompCert4Lean.Lib.Integers.Int64.shru'
            (CompCert4Lean.Lib.Integers.Int64.shr' x
              (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63)))
            (CompCert4Lean.Lib.Integers.Int.sub
              (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 64)) n))) n := by
  change WordCore.Word 64 at x
  change WordCore.Word 32 at n
  have hx := x.intrange
  change (-1 : _root_.Int) < intOfZ x.intval ∧
    intOfZ x.intval < 18446744073709551616 at hx
  have hcases : intOfZ n.intval = 1 ∨
      intOfZ n.intval = 2 ∨
      intOfZ n.intval = 3 ∨
      intOfZ n.intval = 4 ∨
      intOfZ n.intval = 5 ∨
      intOfZ n.intval = 6 ∨
      intOfZ n.intval = 7 ∨
      intOfZ n.intval = 8 ∨
      intOfZ n.intval = 9 ∨
      intOfZ n.intval = 10 ∨
      intOfZ n.intval = 11 ∨
      intOfZ n.intval = 12 ∨
      intOfZ n.intval = 13 ∨
      intOfZ n.intval = 14 ∨
      intOfZ n.intval = 15 ∨
      intOfZ n.intval = 16 ∨
      intOfZ n.intval = 17 ∨
      intOfZ n.intval = 18 ∨
      intOfZ n.intval = 19 ∨
      intOfZ n.intval = 20 ∨
      intOfZ n.intval = 21 ∨
      intOfZ n.intval = 22 ∨
      intOfZ n.intval = 23 ∨
      intOfZ n.intval = 24 ∨
      intOfZ n.intval = 25 ∨
      intOfZ n.intval = 26 ∨
      intOfZ n.intval = 27 ∨
      intOfZ n.intval = 28 ∨
      intOfZ n.intval = 29 ∨
      intOfZ n.intval = 30 ∨
      intOfZ n.intval = 31 ∨
      intOfZ n.intval = 32 ∨
      intOfZ n.intval = 33 ∨
      intOfZ n.intval = 34 ∨
      intOfZ n.intval = 35 ∨
      intOfZ n.intval = 36 ∨
      intOfZ n.intval = 37 ∨
      intOfZ n.intval = 38 ∨
      intOfZ n.intval = 39 ∨
      intOfZ n.intval = 40 ∨
      intOfZ n.intval = 41 ∨
      intOfZ n.intval = 42 ∨
      intOfZ n.intval = 43 ∨
      intOfZ n.intval = 44 ∨
      intOfZ n.intval = 45 ∨
      intOfZ n.intval = 46 ∨
      intOfZ n.intval = 47 ∨
      intOfZ n.intval = 48 ∨
      intOfZ n.intval = 49 ∨
      intOfZ n.intval = 50 ∨
      intOfZ n.intval = 51 ∨
      intOfZ n.intval = 52 ∨
      intOfZ n.intval = 53 ∨
      intOfZ n.intval = 54 ∨
      intOfZ n.intval = 55 ∨
      intOfZ n.intval = 56 ∨
      intOfZ n.intval = 57 ∨
      intOfZ n.intval = 58 ∨
      intOfZ n.intval = 59 ∨
      intOfZ n.intval = 60 ∨
      intOfZ n.intval = 61 ∨
      intOfZ n.intval = 62 := by omega
  rcases hcases with hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn | hn
  all_goals
    apply WordCore.ext
    apply intOfZ_injective
    simp [CompCert4Lean.Lib.Integers.Int64.shrx',
      CompCert4Lean.Lib.Integers.Int64.divs, WordCore.divs,
      CompCert4Lean.Lib.Integers.Int64.signed,
      CompCert4Lean.Lib.Integers.Int64.shr',
      CompCert4Lean.Lib.Integers.Int64.shru',
      CompCert4Lean.Lib.Integers.Int64.shl',
      CompCert4Lean.Lib.Integers.Int64.add, WordCore.add,
      CompCert4Lean.Lib.Integers.Int64.repr,
      CompCert4Lean.Lib.Integers.Int.sub, WordCore.sub,
      CompCert4Lean.Lib.Integers.Int.repr, shrxlimm_repr_intval,
      shrxlimm_signed, shrxlimm_signed_core,
      CompCert4Lean.Lib.Integers.Int.unsigned,
      CompCert4Lean.Lib.Integers.Int64.unsigned,
      CompCert4Lean.Lib.Integers.Int.wordsize,
      CompCert4Lean.Lib.Integers.Int64.wordsize,
      show CompCert4Lean.Lib.Integers.Int64.one =
        WordCore.repr 64 (zOfInt 1) from rfl,
      WordCore.unsigned, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.sub, ZArith.BinInt.Z.shiftr,
      ZArith.BinInt.Z.shiftl, ZArith.BinInt.Z.quot, intOfZ_zOfInt,
      hn]
    simp [shrxlimm_signed_core, shrxlimm_signed, shrxlimm_repr_intval,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, _root_.Int.pow,
      show intOfZ (WordCore.unsigned (WordCore.one 64)) = 1 from rfl]
    simp only [_root_.Int.tdiv_cases, ← _root_.Int.div_def]
    omega

private theorem shrxlimm_word_zero (x : int64) (n : int)
    (hn : intOfZ n.intval = 0) :
    CompCert4Lean.Lib.Integers.Int64.shrx' x n = x := by
  change WordCore.Word 64 at x
  change WordCore.Word 32 at n
  have hx := x.intrange
  change (-1 : _root_.Int) < intOfZ x.intval ∧
    intOfZ x.intval < 18446744073709551616 at hx
  apply WordCore.ext
  apply intOfZ_injective
  simp [CompCert4Lean.Lib.Integers.Int64.shrx',
    CompCert4Lean.Lib.Integers.Int64.divs, WordCore.divs,
    CompCert4Lean.Lib.Integers.Int64.signed,
    CompCert4Lean.Lib.Integers.Int64.shl',
    CompCert4Lean.Lib.Integers.Int64.repr,
    CompCert4Lean.Lib.Integers.Int.unsigned,
    CompCert4Lean.Lib.Integers.Int64.unsigned, WordCore.unsigned,
    CompCert4Lean.Lib.Integers.Int64.wordsize,
    show CompCert4Lean.Lib.Integers.Int64.one =
      WordCore.repr 64 (zOfInt 1) from rfl,
    shrxlimm_repr_intval, shrxlimm_signed_core,
    ZArith.BinInt.Z.shiftl, ZArith.BinInt.Z.quot, intOfZ_zOfInt, hn]
  simp [shrxlimm_signed_core, shrxlimm_repr_intval, intOfZ_zOfInt,
    _root_.Int.pow]
  omega

private theorem shrxlimm_eq_zero (n : int) :
    CompCert4Lean.Lib.Integers.Int.eq n CompCert4Lean.Lib.Integers.Int.zero =
      decide (intOfZ n.intval = 0) := by
  change decide (n.intval = Z0) = decide (intOfZ n.intval = 0)
  congr 1
  apply propext
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    apply intOfZ_injective
    exact h

private theorem shrxl_shrl_2_core : Val.shrxl_shrl_2Statement := by
  intro n x z h
  cases x <;> try { simp [Val.shrxl] at h }
  rename_i x
  have hn : CompCert4Lean.Lib.Integers.Int.ltu n
      (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63)) = true := by
    cases hc : CompCert4Lean.Lib.Integers.Int.ltu n
        (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63))
    · simp [Val.shrxl, hc] at h
    · rfl
  simp only [Val.shrxl, hn, if_true, Option.some.injEq] at h
  subst z
  have hlt : intOfZ n.intval < 63 := by
    rw [shrxlimm_ltu] at hn
    change decide (intOfZ n.intval < 63) = true at hn
    exact of_decide_eq_true hn
  by_cases hz : CompCert4Lean.Lib.Integers.Int.eq n
      CompCert4Lean.Lib.Integers.Int.zero = true
  · rw [if_pos hz]
    have hz0 : intOfZ n.intval = 0 := by
      rw [shrxlimm_eq_zero] at hz
      exact of_decide_eq_true hz
    exact congrArg Vlong (shrxlimm_word_zero x n hz0)
  · rw [if_neg hz]
    have hn0 : intOfZ n.intval ≠ 0 := by
      rw [shrxlimm_eq_zero] at hz
      simpa only [decide_eq_true_eq] using hz
    have hr := n.intrange.1
    change (-1 : _root_.Int) < intOfZ n.intval at hr
    have hrange : 0 < intOfZ n.intval ∧ intOfZ n.intval < 63 := by omega
    have hn64 : CompCert4Lean.Lib.Integers.Int.ltu n
        CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
      rw [shrxlimm_ltu]
      change decide (intOfZ n.intval < 64) = true
      exact decide_eq_true (by omega)
    have hs64 : CompCert4Lean.Lib.Integers.Int.ltu
        (CompCert4Lean.Lib.Integers.Int.sub
          (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 64)) n)
        CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by
      rw [shrxlimm_ltu]
      change decide (intOfZ (WordCore.repr 32
        (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.of_nat 64) n.intval)).intval < 64) = true
      rw [shrxlimm_repr_intval]
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      change decide ((64 - intOfZ n.intval) % 4294967296 < 64) = true
      exact decide_eq_true (by omega)
    have h63 : CompCert4Lean.Lib.Integers.Int.ltu
        (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.of_nat 63))
        CompCert4Lean.Lib.Integers.Int64.iwordsize' = true := by decide
    simp only [Val.shrl, Val.shrlu, Val.addl, hn64, hs64, h63, if_true]
    exact congrArg Vlong (shrxlimm_word x n hrange)

end CompCert4Lean.Common.Values

namespace CompCert4Lean.Common.Values.Val

theorem shrxl_shrl_2 : shrxl_shrl_2Statement :=
  CompCert4Lean.Common.Values.shrxl_shrl_2_core

end CompCert4Lean.Common.Values.Val

namespace CompCert4Lean.Common.Values
namespace Val

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Lib.Integers

private abbrev cmplu_z0 : Z := .Z0
private abbrev cmplu_zAdd := ZArith.BinInt.Z.add
private abbrev cmplu_zLe := ZArith.BinInt.Z.le

private theorem cmplu_bool_inject_unsigned_add (x d : CompCert4Lean.Lib.Integers.ptrofs)
    (h : cmplu_zLe cmplu_z0 (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) ∧
      cmplu_zLe (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned) :
    CompCert4Lean.Lib.Integers.Ptrofs.unsigned (CompCert4Lean.Lib.Integers.Ptrofs.add x d) = cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d) := by
  change Int64.unsigned (Int64.repr (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d))) = _
  have hu : Int64.unsigned (Int64.repr (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d))) =
      ZArith.BinInt.Z.modulo (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) Int64.modulus := by
    run_tac
      let env ← Lean.getEnv
      let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "Integers.Int64.suffix_int64_unsigned_repr_eq_exact")
        | throwError "helper not found"
      let stx := Lean.mkIdent n
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $stx _))
  rw [hu]
  apply ZArith.BinInt.Z.mod_small
  refine ⟨h.1, ?_⟩
  have hh := h.2
  change intOfZ (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) ≤
    intOfZ Int64.modulus - 1 at hh
  change intOfZ (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) < intOfZ Int64.modulus
  omega

private theorem cmplu_bool_inject_cmpu_shift (c : CompCert4Lean.Lib.Integers.comparison) (x y d : CompCert4Lean.Lib.Integers.ptrofs)
    (hx : cmplu_zLe cmplu_z0 (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) ∧
      cmplu_zLe (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned)
    (hy : cmplu_zLe cmplu_z0 (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned y) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) ∧
      cmplu_zLe (cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned y) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) CompCert4Lean.Lib.Integers.Ptrofs.max_unsigned) :
    CompCert4Lean.Lib.Integers.Ptrofs.cmpu c (CompCert4Lean.Lib.Integers.Ptrofs.add x d) (CompCert4Lean.Lib.Integers.Ptrofs.add y d) = CompCert4Lean.Lib.Integers.Ptrofs.cmpu c x y := by
  have heq : CompCert4Lean.Lib.Integers.Ptrofs.eq (CompCert4Lean.Lib.Integers.Ptrofs.add x d) (CompCert4Lean.Lib.Integers.Ptrofs.add y d) = CompCert4Lean.Lib.Integers.Ptrofs.eq x y := by
    change decide (CompCert4Lean.Lib.Integers.Ptrofs.unsigned (CompCert4Lean.Lib.Integers.Ptrofs.add x d) = CompCert4Lean.Lib.Integers.Ptrofs.unsigned (CompCert4Lean.Lib.Integers.Ptrofs.add y d)) =
      decide (CompCert4Lean.Lib.Integers.Ptrofs.unsigned x = CompCert4Lean.Lib.Integers.Ptrofs.unsigned y)
    rw [cmplu_bool_inject_unsigned_add x d hx, cmplu_bool_inject_unsigned_add y d hy]
    congr 1
    apply propext
    constructor
    · intro h
      apply intOfZ_injective
      have h' := congrArg intOfZ h
      simp only [cmplu_zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at h'
      omega
    · intro h; rw [h]
  have he (a b : CompCert4Lean.Lib.Integers.ptrofs) : CompCert4Lean.Lib.Integers.Ptrofs.ltu a b =
      decide (intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned a) < intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned b)) := by
    by_cases h : intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned a) < intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned b)
    · rw [show decide (intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned a) < intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned b)) = true by simp [h]]
      exact CompCert4Lean.Lib.Coqlib.zlt_true Bool _ _ true false h
    · rw [show decide (intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned a) < intOfZ (CompCert4Lean.Lib.Integers.Ptrofs.unsigned b)) = false by simp [h]]
      exact CompCert4Lean.Lib.Coqlib.zlt_false Bool _ _ true false (Int.le_of_not_gt h)
  have hlt (a b : CompCert4Lean.Lib.Integers.ptrofs)
      (ha : CompCert4Lean.Lib.Integers.Ptrofs.unsigned (CompCert4Lean.Lib.Integers.Ptrofs.add a d) = cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned a) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d))
      (hb : CompCert4Lean.Lib.Integers.Ptrofs.unsigned (CompCert4Lean.Lib.Integers.Ptrofs.add b d) = cmplu_zAdd (CompCert4Lean.Lib.Integers.Ptrofs.unsigned b) (CompCert4Lean.Lib.Integers.Ptrofs.unsigned d)) :
      CompCert4Lean.Lib.Integers.Ptrofs.ltu (CompCert4Lean.Lib.Integers.Ptrofs.add a d) (CompCert4Lean.Lib.Integers.Ptrofs.add b d) = CompCert4Lean.Lib.Integers.Ptrofs.ltu a b := by
    rw [he, he, ha, hb]
    simp only [cmplu_zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt, Int.add_lt_add_iff_right]
  cases c <;> simp only [CompCert4Lean.Lib.Integers.Ptrofs.cmpu, heq,
    hlt x y (cmplu_bool_inject_unsigned_add x d hx) (cmplu_bool_inject_unsigned_add y d hy),
    hlt y x (cmplu_bool_inject_unsigned_add y d hy) (cmplu_bool_inject_unsigned_add x d hx)]

theorem cmplu_bool_inject : cmplu_bool_injectStatement := by
  intro f vp1 vp2
  dsimp only
  intro hv hw hb hd c v1 v2 v1' v2' b h1 h2 heval
  cases h1 <;> cases h2 <;>
    simp only [cmplu_bool, CompCert4Lean.X86_64.Archi.ptr64,
      Bool.true_and, if_true] at heval ⊢ <;> try contradiction
  case inject_long.inject_long => exact heval
  case inject_long.inject_ptr i b1 o1 b2 o2 d hm ho =>
    subst o2
    split at heval
    · rename_i h
      obtain ⟨hz, hp⟩ := Bool.and_eq_true_iff.mp h
      rw [hz, hw b1 o1 b2 d hm hp]
      exact heval
    · contradiction
  case inject_ptr.inject_long b1 o1 b2 o2 d hm ho i =>
    subst o2
    split at heval
    · rename_i h
      obtain ⟨hz, hp⟩ := Bool.and_eq_true_iff.mp h
      rw [hz, hw b1 o1 b2 d hm hp]
      exact heval
    · contradiction
  case inject_ptr.inject_ptr b1 o1 b1' o1' d1 hm1 ho1 b2 o2 b2' o2' d2 hm2 ho2 =>
    subst o1' o2'
    cases hs : eq_block b1 b2 with
    | left heq =>
      subst b2
      have hh : (b1', d1) = (b2', d2) := Option.some.inj (hm1.symm.trans hm2)
      cases hh
      cases ht : eq_block b1' b1' with
      | left heq' =>
        simp only [hs, ht] at heval ⊢
        run_tac
          let env ← Lean.getEnv
          let some (n, _) := env.constants.toList.find?
            (fun (n, _) => (toString n).endsWith "Common.Values.boolOfSumbool")
            | throwError "boolean projection helper unavailable"
          Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent n) at $(Lean.mkIdent `heval):ident ⊢))
        simp only [if_true] at heval ⊢
        split at heval
        · rename_i hp
          obtain ⟨hp1, hp2⟩ := Bool.and_eq_true_iff.mp hp
          rw [hw b1 o1 b1' d1 hm1 hp1, hw b1 o2 b1' d1 hm1 hp2]
          rw [cmplu_bool_inject_cmpu_shift c o1 o2 (CompCert4Lean.Lib.Integers.Ptrofs.repr d1)
            (hb b1 o1 b1' d1 hm1 hp1) (hb b1 o2 b1' d1 hm1 hp2)]
          exact heval
        · contradiction
      | right hne => exact (hne rfl).elim
    | right hne =>
      simp only [hs] at heval
      run_tac
        let env ← Lean.getEnv
        let some (n, _) := env.constants.toList.find?
          (fun (n, _) => (toString n).endsWith "Common.Values.boolOfSumbool")
          | throwError "boolean projection helper unavailable"
        Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent n) at $(Lean.mkIdent `heval):ident))
      simp only [Bool.false_eq_true, if_false] at heval
      split at heval
      · rename_i hp
        obtain ⟨hp1, hp2⟩ := Bool.and_eq_true_iff.mp hp
        have hp1' := hv b1 o1 b1' d1 hm1 hp1
        have hp2' := hv b2 o2 b2' d2 hm2 hp2
        cases ht : eq_block b1' b2' with
        | right hne' =>
          simp only [ht, hp1', hp2', Bool.true_and, if_true]
          run_tac
            let env ← Lean.getEnv
            let some (n, _) := env.constants.toList.find?
              (fun (n, _) => (toString n).endsWith "Common.Values.boolOfSumbool")
              | throwError "boolean projection helper unavailable"
            Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent n)))
          simp only [Bool.false_eq_true, if_false, if_true]
          exact heval
        | left heq' =>
          subst b2'
          have hd' := hd b1 o1 b2 o2 b1' d1 b1' d2 hne hp1 hp2 hm1 hm2
          have hofs : CompCert4Lean.Lib.Integers.Ptrofs.unsigned (CompCert4Lean.Lib.Integers.Ptrofs.add o1 (CompCert4Lean.Lib.Integers.Ptrofs.repr d1)) ≠
              CompCert4Lean.Lib.Integers.Ptrofs.unsigned (CompCert4Lean.Lib.Integers.Ptrofs.add o2 (CompCert4Lean.Lib.Integers.Ptrofs.repr d2)) :=
            hd'.resolve_left (fun h => h rfl)
          simp only [ht, hp1', hp2', Bool.true_or, Bool.true_and, if_true]
          run_tac
            let env ← Lean.getEnv
            let some (n, _) := env.constants.toList.find?
              (fun (n, _) => (toString n).endsWith "Common.Values.boolOfSumbool")
              | throwError "boolean projection helper unavailable"
            Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent n)))
          simp only [Bool.false_eq_true, if_false, if_true]
          cases c <;> simp only [cmp_different_blocks, Option.some.injEq] at heval <;>
            try contradiction
          all_goals subst b
          all_goals simp [CompCert4Lean.Lib.Integers.Ptrofs.cmpu, CompCert4Lean.Lib.Integers.Ptrofs.eq, CompCert4Lean.Lib.Integers.WordCore.eq, CompCert4Lean.Lib.Integers.Ptrofs.unsigned, CompCert4Lean.Lib.Integers.WordCore.unsigned] at hofs ⊢
          all_goals exact hofs
      · contradiction

end Val
end CompCert4Lean.Common.Values
