import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Linking
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.X86_64.Archi

/-!
# C types

Definition-bearing translation of CompCert's `cfrontend/Ctypes.v`.  Theorems
assigned to the later proof phase are represented by exact proposition or
type descriptors.  Composite values retain the source proof-carrying fields.
-/

namespace CompCert4Lean.Cfrontend.Ctypes

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common
open CompCert4Lean.Lib.Maps

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev calling_convention := CompCert4Lean.Common.AST.calling_convention
private abbrev external_function := CompCert4Lean.Common.AST.external_function
private abbrev memory_chunk := CompCert4Lean.Common.AST.memory_chunk
private abbrev xtype := CompCert4Lean.Common.AST.xtype
private abbrev signature := CompCert4Lean.Common.AST.signature

private abbrev z0 : Z := .Z0
private abbrev z1 : Z := .Zpos .xH
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zOfN := ZArith.BinInt.Z.of_N
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zMin := ZArith.BinInt.Z.min
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zGt := ZArith.BinInt.Z.gt
private abbrev zDivide := ZArith.BinInt.Z.divide
private abbrev align := CompCert4Lean.Lib.Coqlib.align
private abbrev floor := CompCert4Lean.Lib.Coqlib.floor
private abbrev two_p := ZArith.Zpower.two_p
private abbrev two_power_nat := ZArith.Zpower.two_power_nat

private def rocqStringOfBytes : List UInt8 -> RocqString
  | [] => .EmptyString
  | b :: bs => .String b (rocqStringOfBytes bs)

private def zeroWidthBitfieldText : RocqString :=
  rocqStringOfBytes [97, 99, 99, 101, 115, 115, 105, 110, 103, 32, 122, 101,
    114, 111, 45, 119, 105, 100, 116, 104, 32, 98, 105, 116, 102, 105, 101,
    108, 100]

private def bitfieldTooWideText : RocqString :=
  rocqStringOfBytes [98, 105, 116, 102, 105, 101, 108, 100, 32, 116, 111, 111,
    32, 119, 105, 100, 101]

private def unknownFieldText : RocqString :=
  rocqStringOfBytes [85, 110, 107, 110, 111, 119, 110, 32, 102, 105, 101, 108,
    100, 32]

private def duplicateCompositeText : RocqString :=
  rocqStringOfBytes [77, 117, 108, 116, 105, 112, 108, 101, 32, 100, 101, 102,
    105, 110, 105, 116, 105, 111, 110, 115, 32, 111, 102, 32, 115, 116, 114,
    117, 99, 116, 32, 111, 114, 32, 117, 110, 105, 111, 110, 32]

private def incompleteCompositeText : RocqString :=
  rocqStringOfBytes [73, 110, 99, 111, 109, 112, 108, 101, 116, 101, 32, 115,
    116, 114, 117, 99, 116, 32, 111, 114, 32, 117, 110, 105, 111, 110, 32]

/-! ## Type syntax -/

inductive signedness : Type where
  | Signed
  | Unsigned
deriving DecidableEq

export signedness (Signed Unsigned)

inductive intsize : Type where
  | I8
  | I16
  | I32
  | IBool
deriving DecidableEq

export intsize (I8 I16 I32 IBool)

inductive floatsize : Type where
  | F32
  | F64
deriving DecidableEq

export floatsize (F32 F64)

structure attr : Type where
  attr_volatile : Bool
  attr_alignas : Option N
deriving DecidableEq

export attr (attr_volatile attr_alignas)

def noattr : attr :=
  { attr_volatile := false, attr_alignas := none }

inductive type : Type where
  | Tvoid
  | Tint (size : intsize) (signed : signedness) (attributes : attr)
  | Tlong (signed : signedness) (attributes : attr)
  | Tfloat (size : floatsize) (attributes : attr)
  | Tpointer (element : type) (attributes : attr)
  | Tarray (element : type) (length : Z) (attributes : attr)
  | Tfunction (args : List type) (result : type) (cc : calling_convention)
  | Tstruct (id : ident) (attributes : attr)
  | Tunion (id : ident) (attributes : attr)

export type (Tvoid Tint Tlong Tfloat Tpointer Tarray Tfunction Tstruct Tunion)


mutual
  private def typeDecEq : (t1 t2 : type) → Decidable (t1 = t2)
    | .Tvoid, t2 =>
        match t2 with
        | .Tvoid => isTrue rfl
        | .Tint _ _ _ | .Tlong _ _ | .Tfloat _ _ | .Tpointer _ _ | .Tarray _ _ _ |
          .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ =>
            isFalse (by intro h; cases h)
    | .Tint s1 sg1 a1, t2 =>
        match t2 with
        | .Tint s2 sg2 a2 =>
            if hs : s1 = s2 then
              if hsg : sg1 = sg2 then
                if ha : a1 = a2 then
                  isTrue (by cases hs; cases hsg; cases ha; rfl)
                else
                  isFalse (by intro h; cases h; exact ha rfl)
              else
                isFalse (by intro h; cases h; exact hsg rfl)
            else
              isFalse (by intro h; cases h; exact hs rfl)
        | .Tvoid | .Tlong _ _ | .Tfloat _ _ | .Tpointer _ _ | .Tarray _ _ _ |
          .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ =>
            isFalse (by intro h; cases h)
    | .Tlong sg1 a1, t2 =>
        match t2 with
        | .Tlong sg2 a2 =>
            if hsg : sg1 = sg2 then
              if ha : a1 = a2 then
                isTrue (by cases hsg; cases ha; rfl)
              else
                isFalse (by intro h; cases h; exact ha rfl)
            else
              isFalse (by intro h; cases h; exact hsg rfl)
        | .Tvoid | .Tint _ _ _ | .Tfloat _ _ | .Tpointer _ _ | .Tarray _ _ _ |
          .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ =>
            isFalse (by intro h; cases h)
    | .Tfloat s1 a1, t2 =>
        match t2 with
        | .Tfloat s2 a2 =>
            if hs : s1 = s2 then
              if ha : a1 = a2 then
                isTrue (by cases hs; cases ha; rfl)
              else
                isFalse (by intro h; cases h; exact ha rfl)
            else
              isFalse (by intro h; cases h; exact hs rfl)
        | .Tvoid | .Tint _ _ _ | .Tlong _ _ | .Tpointer _ _ | .Tarray _ _ _ |
          .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ =>
            isFalse (by intro h; cases h)
    | .Tpointer t1 a1, t2 =>
        match t2 with
        | .Tpointer t2 a2 =>
            match typeDecEq t1 t2 with
            | isTrue ht =>
                if ha : a1 = a2 then
                  isTrue (by cases ht; cases ha; rfl)
                else
                  isFalse (by intro h; cases h; exact ha rfl)
            | isFalse ht => isFalse (by intro h; cases h; exact ht rfl)
        | .Tvoid | .Tint _ _ _ | .Tlong _ _ | .Tfloat _ _ | .Tarray _ _ _ |
          .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ =>
            isFalse (by intro h; cases h)
    | .Tarray t1 n1 a1, t2 =>
        match t2 with
        | .Tarray t2 n2 a2 =>
            match typeDecEq t1 t2 with
            | isTrue ht =>
                if hn : n1 = n2 then
                  if ha : a1 = a2 then
                    isTrue (by cases ht; cases hn; cases ha; rfl)
                  else
                    isFalse (by intro h; cases h; exact ha rfl)
                else
                  isFalse (by intro h; cases h; exact hn rfl)
            | isFalse ht => isFalse (by intro h; cases h; exact ht rfl)
        | .Tvoid | .Tint _ _ _ | .Tlong _ _ | .Tfloat _ _ | .Tpointer _ _ |
          .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ =>
            isFalse (by intro h; cases h)
    | .Tfunction args1 res1 cc1, t2 =>
        match t2 with
        | .Tfunction args2 res2 cc2 =>
            match typeListDecEq args1 args2 with
            | isTrue hargs =>
                match typeDecEq res1 res2 with
                | isTrue hres =>
                    if hcc : cc1 = cc2 then
                      isTrue (by cases hargs; cases hres; cases hcc; rfl)
                    else
                      isFalse (by intro h; cases h; exact hcc rfl)
                | isFalse hres => isFalse (by intro h; cases h; exact hres rfl)
            | isFalse hargs => isFalse (by intro h; cases h; exact hargs rfl)
        | .Tvoid | .Tint _ _ _ | .Tlong _ _ | .Tfloat _ _ | .Tpointer _ _ |
          .Tarray _ _ _ | .Tstruct _ _ | .Tunion _ _ =>
            isFalse (by intro h; cases h)
    | .Tstruct id1 a1, t2 =>
        match t2 with
        | .Tstruct id2 a2 =>
            if hid : id1 = id2 then
              if ha : a1 = a2 then
                isTrue (by cases hid; cases ha; rfl)
              else
                isFalse (by intro h; cases h; exact ha rfl)
            else
              isFalse (by intro h; cases h; exact hid rfl)
        | .Tvoid | .Tint _ _ _ | .Tlong _ _ | .Tfloat _ _ | .Tpointer _ _ |
          .Tarray _ _ _ | .Tfunction _ _ _ | .Tunion _ _ =>
            isFalse (by intro h; cases h)
    | .Tunion id1 a1, t2 =>
        match t2 with
        | .Tunion id2 a2 =>
            if hid : id1 = id2 then
              if ha : a1 = a2 then
                isTrue (by cases hid; cases ha; rfl)
              else
                isFalse (by intro h; cases h; exact ha rfl)
            else
              isFalse (by intro h; cases h; exact hid rfl)
        | .Tvoid | .Tint _ _ _ | .Tlong _ _ | .Tfloat _ _ | .Tpointer _ _ |
          .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ =>
            isFalse (by intro h; cases h)

  private def typeListDecEq : (xs ys : List type) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match typeDecEq x y with
        | isTrue hxy =>
            match typeListDecEq xs ys with
            | isTrue hrest => isTrue (by cases hxy; cases hrest; rfl)
            | isFalse hrest => isFalse (by intro h; cases h; exact hrest rfl)
        | isFalse hxy => isFalse (by intro h; cases h; exact hxy rfl)
end

private instance typeDecidableEq : DecidableEq type := typeDecEq
private instance typeListDecidableEq : DecidableEq (List type) := typeListDecEq

def intsize_eqStatement :=
  forall s1 s2 : intsize, Sumbool (s1 = s2) (s1 ≠ s2)

private def decEqSumbool {A : Type} [DecidableEq A] (x y : A) :
    Sumbool (x = y) (x ≠ y) := by
  by_cases h : x = y
  · exact .left h
  · exact .right h

def intsize_eq (s1 s2 : intsize) : Sumbool (s1 = s2) (s1 ≠ s2) :=
  decEqSumbool s1 s2

def signedness_eq (s1 s2 : signedness) : Sumbool (s1 = s2) (s1 ≠ s2) :=
  decEqSumbool s1 s2

def floatsize_eq (s1 s2 : floatsize) : Sumbool (s1 = s2) (s1 ≠ s2) :=
  decEqSumbool s1 s2

def attr_eq (a1 a2 : attr) : Sumbool (a1 = a2) (a1 ≠ a2) :=
  decEqSumbool a1 a2

def type_eq (t1 t2 : type) : Sumbool (t1 = t2) (t1 ≠ t2) :=
  decEqSumbool t1 t2

def typelist_eq (tyl1 tyl2 : List type) :
    Sumbool (tyl1 = tyl2) (tyl1 ≠ tyl2) :=
  decEqSumbool tyl1 tyl2

def signedness_eqStatement :=
  forall s1 s2 : signedness, Sumbool (s1 = s2) (s1 ≠ s2)

def floatsize_eqStatement :=
  forall s1 s2 : floatsize, Sumbool (s1 = s2) (s1 ≠ s2)

def attr_eqStatement :=
  forall a1 a2 : attr, Sumbool (a1 = a2) (a1 ≠ a2)

def type_eqStatement :=
  forall t1 t2 : type, Sumbool (t1 = t2) (t1 ≠ t2)

def typelist_eqStatement :=
  forall tyl1 tyl2 : List type, Sumbool (tyl1 = tyl2) (tyl1 ≠ tyl2)

def attr_of_type : type -> attr
  | .Tvoid => noattr
  | .Tint _ _ a => a
  | .Tlong _ a => a
  | .Tfloat _ a => a
  | .Tpointer _ a => a
  | .Tarray _ _ a => a
  | .Tfunction _ _ _ => noattr
  | .Tstruct _ a => a
  | .Tunion _ a => a

def change_attributes (f : attr -> attr) : type -> type
  | .Tvoid => .Tvoid
  | .Tint sz sg a => .Tint sz sg (f a)
  | .Tlong sg a => .Tlong sg (f a)
  | .Tfloat sz a => .Tfloat sz (f a)
  | .Tpointer t a => .Tpointer t (f a)
  | .Tarray t n a => .Tarray t n (f a)
  | .Tfunction args res cc => .Tfunction args res cc
  | .Tstruct id a => .Tstruct id (f a)
  | .Tunion id a => .Tunion id (f a)

def remove_attributes (t : type) : type :=
  change_attributes (fun _ => noattr) t

def bitsize_intsize : intsize -> Z
  | .I8 => zOfNat 8
  | .I16 => zOfNat 16
  | .I32 => zOfNat 32
  | .IBool => zOfNat 1

inductive struct_or_union : Type where
  | Struct
  | Union
deriving DecidableEq

export struct_or_union (Struct Union)

inductive member : Type where
  | Member_plain (id : ident) (t : type)
  | Member_bitfield (id : ident) (size : intsize) (signed : signedness)
      (attributes : attr) (width : Z) (padding : Bool)
deriving DecidableEq

export member (Member_plain Member_bitfield)

def members : Type := List member

private instance membersDecidableEq : DecidableEq members := by
  unfold members
  infer_instance

inductive composite_definition : Type where
  | Composite (id : ident) (su : struct_or_union) (members : members) (attributes : attr)
deriving DecidableEq

export composite_definition (Composite)

def name_composite_def : composite_definition → ident
  | .Composite id _ _ _ => id

def composite_def_eq (x y : composite_definition) : Sumbool (x = y) (x ≠ y) :=
  decEqSumbool x y

def name_member : member -> ident
  | .Member_plain id _ => id
  | .Member_bitfield id _ _ _ _ _ => id

def type_member : member -> type
  | .Member_plain _ t => t
  | .Member_bitfield _ sz sg a width _ =>
      match CompCert4Lean.Lib.Coqlib.zlt width (bitsize_intsize sz) with
      | .left _ => .Tint sz .Signed a
      | .right _ => .Tint sz sg a

def member_is_padding : member -> Bool
  | .Member_plain _ _ => false
  | .Member_bitfield _ _ _ _ _ padding => padding

structure composite : Type where
  co_su : struct_or_union
  co_members : members
  co_attr : attr
  co_sizeof : Z
  co_alignof : Z
  co_rank : Nat
  co_sizeof_pos : zLe z0 co_sizeof
  co_alignof_two_p : Exists fun n : Nat => co_alignof = two_power_nat n
  co_sizeof_alignof : zDivide co_alignof co_sizeof

export composite (co_su co_members co_attr co_sizeof co_alignof co_rank
  co_sizeof_pos co_alignof_two_p co_sizeof_alignof)

def composite_env : Type := PTree.t composite

inductive bitfield : Type where
  | Full
  | Bits (size : intsize) (signed : signedness) (pos : Z) (width : Z)
deriving DecidableEq

export bitfield (Full Bits)

def type_int32s : type := .Tint .I32 .Signed noattr
def type_bool : type := .Tint .IBool .Signed noattr

def typeconv : type -> type
  | .Tint .I8 _ _ => type_int32s
  | .Tint .I16 _ _ => type_int32s
  | .Tint .IBool _ _ => type_int32s
  | .Tarray t _ _ => .Tpointer t noattr
  | t@(.Tfunction _ _ _) => .Tpointer t noattr
  | t => remove_attributes t

def default_argument_conversion : type -> type
  | .Tint .I8 _ _ => type_int32s
  | .Tint .I16 _ _ => type_int32s
  | .Tint .IBool _ _ => type_int32s
  | .Tfloat _ _ => .Tfloat .F64 noattr
  | .Tarray t _ _ => .Tpointer t noattr
  | t@(.Tfunction _ _ _) => .Tpointer t noattr
  | t => remove_attributes t

/-! ## Completeness, alignment, and size -/

def complete_type (env : composite_env) : type -> Bool
  | .Tvoid => false
  | .Tint _ _ _ => true
  | .Tlong _ _ => true
  | .Tfloat _ _ => true
  | .Tpointer _ _ => true
  | .Tarray t _ _ => complete_type env t
  | .Tfunction _ _ _ => false
  | .Tstruct id _ | .Tunion id _ => (PTree.get id env).isSome

def align_attr (a : attr) (al : Z) : Z :=
  match a.attr_alignas with
  | some l => two_power_nat (NArith.BinNat.N.to_nat l)
  | none => al

def alignof (env : composite_env) : type -> Z
  | .Tvoid => align_attr noattr (zOfNat 1)
  | .Tint .I8 _ a => align_attr a (zOfNat 1)
  | .Tint .I16 _ a => align_attr a (zOfNat 2)
  | .Tint .I32 _ a => align_attr a (zOfNat 4)
  | .Tint .IBool _ a => align_attr a (zOfNat 1)
  | .Tlong _ a => align_attr a CompCert4Lean.X86_64.Archi.align_int64
  | .Tfloat .F32 a => align_attr a (zOfNat 4)
  | .Tfloat .F64 a => align_attr a CompCert4Lean.X86_64.Archi.align_float64
  | .Tpointer _ a =>
      align_attr a (if CompCert4Lean.X86_64.Archi.ptr64 then zOfNat 8 else zOfNat 4)
  | .Tarray t _ a => align_attr a (alignof env t)
  | .Tfunction _ _ _ => align_attr noattr (zOfNat 1)
  | .Tstruct id a | .Tunion id a =>
      align_attr a (match PTree.get id env with | some co => co.co_alignof | none => zOfNat 1)

def sizeof (env : composite_env) : type -> Z
  | .Tvoid => zOfNat 1
  | .Tint .I8 _ _ => zOfNat 1
  | .Tint .I16 _ _ => zOfNat 2
  | .Tint .I32 _ _ => zOfNat 4
  | .Tint .IBool _ _ => zOfNat 1
  | .Tlong _ _ => zOfNat 8
  | .Tfloat .F32 _ => zOfNat 4
  | .Tfloat .F64 _ => zOfNat 8
  | .Tpointer _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then zOfNat 8 else zOfNat 4
  | .Tarray t n _ => zMul (sizeof env t) (zMax z0 n)
  | .Tfunction _ _ _ => zOfNat 1
  | .Tstruct id _ | .Tunion id _ =>
      match PTree.get id env with | some co => co.co_sizeof | none => z0

def align_attr_two_pStatement : Prop :=
  forall al a, (Exists fun n : Nat => al = two_power_nat n) ->
    Exists fun n : Nat => align_attr a al = two_power_nat n

def alignof_two_pStatement : Prop :=
  forall env t, Exists fun n : Nat => alignof env t = two_power_nat n

def alignof_posStatement : Prop :=
  forall env t, zGt (alignof env t) z0

def sizeof_posStatement : Prop :=
  forall env t, zLe z0 (sizeof env t)

/-! ## Layout -/

def bitalignof (env : composite_env) (t : type) : Z :=
  zMul (alignof env t) (zOfNat 8)

def bitsizeof (env : composite_env) (t : type) : Z :=
  zMul (sizeof env t) (zOfNat 8)

def bitalignof_intsize : intsize -> Z
  | .I8 | .IBool => zOfNat 8
  | .I16 => zOfNat 16
  | .I32 => zOfNat 32

def next_field (env : composite_env) (pos : Z) : member -> Z
  | .Member_plain _ t => zAdd (align pos (bitalignof env t)) (bitsizeof env t)
  | .Member_bitfield _ sz _ _ width _ =>
      let s := bitalignof_intsize sz
      match CompCert4Lean.Lib.Coqlib.zle width z0 with
      | .left _ => align pos s
      | .right _ =>
          let current := floor pos s
          let next := zAdd current s
          match CompCert4Lean.Lib.Coqlib.zle (zAdd pos width) next with
          | .left _ => zAdd pos width
          | .right _ => zAdd next width

def layout_field (env : composite_env) (pos : Z) : member -> Errors.res (Z × bitfield)
  | .Member_plain _ t =>
      .OK (zDiv (align pos (bitalignof env t)) (zOfNat 8), Full)
  | .Member_bitfield _ sz sg _ width _ =>
      match CompCert4Lean.Lib.Coqlib.zle width z0 with
      | .left _ => .Error (Errors.msg zeroWidthBitfieldText)
      | .right _ =>
          match CompCert4Lean.Lib.Coqlib.zlt (bitsize_intsize sz) width with
          | .left _ => .Error (Errors.msg bitfieldTooWideText)
          | .right _ =>
              let s := bitalignof_intsize sz
              let start := floor pos s
              let next := zAdd start s
              match CompCert4Lean.Lib.Coqlib.zle (zAdd pos width) next with
              | .left _ => .OK (zDiv start (zOfNat 8), Bits sz sg (zSub pos start) width)
              | .right _ => .OK (zDiv next (zOfNat 8), Bits sz sg z0 width)

def bitalignof_intsize_posStatement : Prop :=
  forall sz, zGt (bitalignof_intsize sz) z0

def next_field_incrStatement : Prop :=
  forall env pos m, zLe pos (next_field env pos m)

def alignof_composite (env : composite_env) : members -> Z
  | [] => zOfNat 1
  | m :: ms =>
      if member_is_padding m then alignof_composite env ms
      else zMax (alignof env (type_member m)) (alignof_composite env ms)

def bitsizeof_struct (env : composite_env) : Z -> members -> Z
  | current, [] => current
  | current, m :: ms => bitsizeof_struct env (next_field env current m) ms

def bytes_of_bits (n : Z) : Z :=
  zDiv (zAdd n (zOfNat 7)) (zOfNat 8)

def sizeof_struct (env : composite_env) (ms : members) : Z :=
  bytes_of_bits (bitsizeof_struct env z0 ms)

def sizeof_union (env : composite_env) : members -> Z
  | [] => z0
  | m :: ms => zMax (sizeof env (type_member m)) (sizeof_union env ms)

def alignof_composite_two_pStatement : Prop :=
  forall env m, Exists fun n : Nat => alignof_composite env m = two_power_nat n

def alignof_composite_posStatement : Prop :=
  forall env m a, zGt (align_attr a (alignof_composite env m)) z0

def bitsizeof_struct_incrStatement : Prop :=
  forall env m current, zLe current (bitsizeof_struct env current m)

def sizeof_union_posStatement : Prop :=
  forall env m, zLe z0 (sizeof_union env m)

def field_offset_rec (env : composite_env) (id : ident) : members -> Z -> Errors.res (Z × bitfield)
  | [], _ => .Error (Errors.MSG unknownFieldText :: Errors.CTX id :: [])
  | m :: ms, pos =>
      match AST.ident_eq id (name_member m) with
      | .left _ => layout_field env pos m
      | .right _ => field_offset_rec env id ms (next_field env pos m)

def field_offset (env : composite_env) (id : ident) (ms : members) : Errors.res (Z × bitfield) :=
  field_offset_rec env id ms z0

def union_field_offset (env : composite_env) (id : ident) : members -> Errors.res (Z × bitfield)
  | [] => .Error (Errors.MSG unknownFieldText :: Errors.CTX id :: [])
  | m :: ms =>
      match AST.ident_eq id (name_member m) with
      | .left _ => layout_field env z0 m
      | .right _ => union_field_offset env id ms

/-! ## Access modes and back-end types -/

inductive mode : Type where
  | By_value (chunk : memory_chunk)
  | By_reference
  | By_copy
  | By_nothing
deriving DecidableEq

export mode (By_value By_reference By_copy By_nothing)

def access_mode : type -> mode
  | .Tint .I8 .Signed _ => .By_value .Mint8signed
  | .Tint .I8 .Unsigned _ => .By_value .Mint8unsigned
  | .Tint .I16 .Signed _ => .By_value .Mint16signed
  | .Tint .I16 .Unsigned _ => .By_value .Mint16unsigned
  | .Tint .I32 _ _ => .By_value .Mint32
  | .Tint .IBool _ _ => .By_value .Mbool
  | .Tlong _ _ => .By_value .Mint64
  | .Tfloat .F32 _ => .By_value .Mfloat32
  | .Tfloat .F64 _ => .By_value .Mfloat64
  | .Tvoid => .By_nothing
  | .Tpointer _ _ => .By_value AST.Mptr
  | .Tarray _ _ _ => .By_reference
  | .Tfunction _ _ _ => .By_reference
  | .Tstruct _ _ => .By_copy
  | .Tunion _ _ => .By_copy

def type_is_volatile (t : type) : Bool :=
  match access_mode t with
  | .By_value _ => (attr_of_type t).attr_volatile
  | _ => false

def alignof_blockcopy (env : composite_env) : type -> Z
  | .Tvoid => zOfNat 1
  | .Tint .I8 _ _ => zOfNat 1
  | .Tint .I16 _ _ => zOfNat 2
  | .Tint .I32 _ _ => zOfNat 4
  | .Tint .IBool _ _ => zOfNat 1
  | .Tlong _ _ => zOfNat 8
  | .Tfloat .F32 _ => zOfNat 4
  | .Tfloat .F64 _ => zOfNat 8
  | .Tpointer _ _ => if CompCert4Lean.X86_64.Archi.ptr64 then zOfNat 8 else zOfNat 4
  | .Tarray t _ _ => alignof_blockcopy env t
  | .Tfunction _ _ _ => zOfNat 1
  | .Tstruct id _ | .Tunion id _ =>
      match PTree.get id env with
      | some co => zMin (zOfNat 8) co.co_alignof
      | none => zOfNat 1

def alignof_blockcopy_1248Statement : Prop :=
  forall env t,
    let a := alignof_blockcopy env t
    a = zOfNat 1 ∨ a = zOfNat 2 ∨ a = zOfNat 4 ∨ a = zOfNat 8

def sizeof_alignof_blockcopy_compatStatement : Prop :=
  forall env t, zDivide (alignof_blockcopy env t) (sizeof env t)

def rank_type (env : composite_env) : type -> Nat
  | .Tarray t _ _ => Nat.succ (rank_type env t)
  | .Tstruct id _ | .Tunion id _ =>
      match PTree.get id env with
      | none => 0
      | some co => Nat.succ co.co_rank
  | _ => 0

def rank_members (env : composite_env) : members -> Nat
  | [] => 0
  | .Member_plain _ t :: ms => Nat.max (rank_type env t) (rank_members env ms)
  | .Member_bitfield _ _ _ _ _ _ :: ms => rank_members env ms

def type_of_params (params : List (ident × type)) : List type :=
  params.map Prod.snd

def typ_of_type : type -> AST.typ
  | .Tvoid => .Tint
  | .Tint _ _ _ => .Tint
  | .Tlong _ _ => .Tlong
  | .Tfloat .F32 _ => .Tsingle
  | .Tfloat .F64 _ => .Tfloat
  | .Tpointer _ _ | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => AST.Tptr

def argtype_of_type : type -> xtype
  | .Tvoid => .Xvoid
  | .Tint .I32 _ _ => .Xint
  | .Tint .I8 .Signed _ => .Xint8signed
  | .Tint .I8 .Unsigned _ => .Xint8unsigned
  | .Tint .I16 .Signed _ => .Xint16signed
  | .Tint .I16 .Unsigned _ => .Xint16unsigned
  | .Tint .IBool _ _ => .Xbool
  | .Tlong _ _ => .Xlong
  | .Tfloat .F32 _ => .Xsingle
  | .Tfloat .F64 _ => .Xfloat
  | .Tpointer _ _ | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => .Xptr

def rettype_of_type : type -> xtype
  | .Tvoid => .Xvoid
  | .Tint .I32 _ _ => .Xint
  | .Tint .I8 .Signed _ => .Xint8signed
  | .Tint .I8 .Unsigned _ => .Xint8unsigned
  | .Tint .I16 .Signed _ => .Xint16signed
  | .Tint .I16 .Unsigned _ => .Xint16unsigned
  | .Tint .IBool _ _ => .Xbool
  | .Tlong _ _ => .Xlong
  | .Tfloat .F32 _ => .Xsingle
  | .Tfloat .F64 _ => .Xfloat
  | .Tpointer _ _ => .Xptr
  | .Tarray _ _ _ | .Tfunction _ _ _ | .Tstruct _ _ | .Tunion _ _ => .Xvoid

def signature_of_type (args : List type) (result : type) (cc : calling_convention) : signature :=
  { sig_args := args.map argtype_of_type, sig_res := rettype_of_type result, sig_cc := cc }

/-! ## Composite environments -/

def sizeof_composite (env : composite_env) (su : struct_or_union) (ms : members) : Z :=
  match su with
  | .Struct => sizeof_struct env ms
  | .Union => sizeof_union env ms

def sizeof_composite_posStatement : Prop :=
  forall env su ms, zLe z0 (sizeof_composite env su ms)

def complete_members (env : composite_env) : members -> Bool
  | [] => true
  | m :: ms => complete_type env (type_member m) && complete_members env ms

private theorem posToNat_positive (p : positive) : 0 < PArith.BinPos.Pos.to_nat p := by
  induction p with
  | xH => decide
  | xI p ih =>
      change 0 < 2 * PArith.BinPos.Pos.to_nat p + 1
      omega
  | xO p ih =>
      change 0 < 2 * PArith.BinPos.Pos.to_nat p
      omega

private theorem zPos_positive (p : positive) : zGt (.Zpos p) z0 := by
  change (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat p)
  exact Int.natCast_pos.mpr (posToNat_positive p)

private theorem zNeg_not_nonneg (p : positive) : Not (zLe z0 (.Zneg p)) := by
  change Not ((0 : Int) <= -Int.ofNat (PArith.BinPos.Pos.to_nat p))
  have hp : (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat p) :=
    Int.natCast_pos.mpr (posToNat_positive p)
  omega

private def zInt : Z -> Int
  | .Z0 => 0
  | .Zpos p => Int.ofNat (PArith.BinPos.Pos.to_nat p)
  | .Zneg p => -Int.ofNat (PArith.BinPos.Pos.to_nat p)

private def zFromInt : Int -> Z
  | .ofNat 0 => .Z0
  | .ofNat (n + 1) => .Zpos (PArith.BinPos.Pos.of_nat (n + 1))
  | .negSucc n => .Zneg (PArith.BinPos.Pos.of_nat (n + 1))

private theorem zLe_iff_zInt (x y : Z) : zLe x y <-> zInt x <= zInt y := by
  cases x <;> cases y <;> rfl

private theorem zLt_iff_zInt (x y : Z) : zLt x y <-> zInt x < zInt y := by
  cases x <;> cases y <;> rfl

private theorem zFromInt_nonneg (i : Int) (h : 0 <= i) : zLe z0 (zFromInt i) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change (0 : Int) <= 0
          omega
      | succ n => exact Int.le_of_lt (zPos_positive _)
  | negSucc n => omega

private theorem zFromInt_positive (i : Int) (h : 0 < i) : zGt (zFromInt i) z0 := by
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change (0 : Int) < 0 at h
          omega
      | succ n => exact zPos_positive _
  | negSucc n =>
      change (0 : Int) < -Int.ofNat (n + 1) at h
      have hn : (0 : Int) < Int.ofNat (n + 1) :=
        Int.natCast_pos.mpr (Nat.zero_lt_succ n)
      omega

private theorem zAdd_fromInt (x y : Z) :
    zAdd x y = zFromInt (zInt x + zInt y) := by
  cases x <;> cases y <;> rfl

private theorem zSub_fromInt (x y : Z) :
    zSub x y = zFromInt (zInt x - zInt y) := by
  cases x <;> cases y <;> rfl

private theorem zMul_fromInt (x y : Z) :
    zMul x y = zFromInt (zInt x * zInt y) := by
  cases x <;> cases y <;> rfl

private def intDivEucl (a b : Int) : Int :=
  if b = 0 then 0
  else if 0 < b then Int.ediv a b
  else
    let d := -b
    let q := Int.ediv a d
    let r := Int.emod a d
    if r = 0 then -q else -(q + 1)

private theorem zDiv_fromInt (x y : Z) :
    zDiv x y = zFromInt (intDivEucl (zInt x) (zInt y)) := by
  cases x <;> cases y <;> rfl

private theorem intDivEucl_nonneg (a b : Int) (ha : 0 <= a) (hb : 0 < b) :
    0 <= intDivEucl a b := by
  unfold intDivEucl
  rw [if_neg (Int.ne_of_gt hb), if_pos hb]
  exact Int.ediv_nonneg ha (Int.le_of_lt hb)

private theorem zDiv_nonneg (x y : Z) (hx : zLe z0 x) (hy : zGt y z0) :
    zLe z0 (zDiv x y) := by
  rw [zDiv_fromInt]
  exact zFromInt_nonneg _ (intDivEucl_nonneg _ _
    ((zLe_iff_zInt _ _).mp hx) ((zLt_iff_zInt _ _).mp hy))

private theorem zSub_nonneg (x y : Z) (h : zLe y x) : zLe z0 (zSub x y) := by
  rw [zSub_fromInt]
  exact zFromInt_nonneg _ (Int.sub_nonneg.mpr ((zLe_iff_zInt _ _).mp h))

private theorem zAdd_positive (x y : Z) (hx : zLe z0 x) (hy : zGt y z0) :
    zGt (zAdd x y) z0 := by
  rw [zAdd_fromInt]
  exact zFromInt_positive _ (Int.add_pos_of_nonneg_of_pos
    ((zLe_iff_zInt _ _).mp hx) ((zLt_iff_zInt _ _).mp hy))

private theorem zPositive_ge_one (x : Z) (h : zGt x z0) : zLe z1 x := by
  apply (zLe_iff_zInt _ _).mpr
  have hx := (zLt_iff_zInt _ _).mp h
  have hz0 : zInt z0 = 0 := rfl
  have hz1 : zInt z1 = 1 := rfl
  rw [hz0] at hx
  rw [hz1]
  cases x with
  | Z0 => omega
  | Zpos p =>
      have hp : (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat p) :=
        Int.natCast_pos.mpr (posToNat_positive p)
      change (1 : Int) <= Int.ofNat (PArith.BinPos.Pos.to_nat p)
      omega
  | Zneg p =>
      have hp : (0 : Int) < Int.ofNat (PArith.BinPos.Pos.to_nat p) :=
        Int.natCast_pos.mpr (posToNat_positive p)
      omega

private def zPowInt (x y : Int) : Z :=
  if y < 0 then .Z0 else zFromInt (Int.pow x y.toNat)

private theorem zPow_fromInt (x y : Z) :
    ZArith.BinInt.Z.pow x y = zPowInt (zInt x) (zInt y) := by
  cases x <;> cases y <;> rfl

private theorem zOfNat_nonneg (n : Nat) : zLe z0 (zOfNat n) := by
  cases n with
  | zero =>
      change (0 : Int) <= 0
      omega
  | succ n =>
      change zLe z0 (.Zpos (PArith.BinPos.Pos.of_nat (n + 1)))
      exact Int.le_of_lt (zPos_positive _)

private theorem zOfNat_positive (n : Nat) (h : 0 < n) : zGt (zOfNat n) z0 := by
  cases n with
  | zero => omega
  | succ n =>
      change zGt (.Zpos (PArith.BinPos.Pos.of_nat (n + 1))) z0
      exact zPos_positive _

private theorem twoPowerNat_positive (n : Nat) : zGt (two_power_nat n) z0 := by
  unfold two_power_nat ZArith.Zpower.two_power_nat
  rw [zPow_fromInt]
  unfold zPowInt
  have hn : 0 <= zInt (zOfNat n) :=
    (zLe_iff_zInt _ _).mp (zOfNat_nonneg n)
  have hnot : Not (zInt (ZArith.BinInt.Z.of_nat n) < 0) := by
    change Not (zInt (zOfNat n) < 0)
    omega
  rw [if_neg hnot]
  apply zFromInt_positive
  apply Int.pow_pos
  change (0 : Int) < 2
  omega

private theorem alignAttrPositive (a : attr) (al : Z) (hal : zGt al z0) :
    zGt (align_attr a al) z0 := by
  cases a with
  | mk volatile alignas =>
      cases alignas with
      | none => exact hal
      | some n => exact twoPowerNat_positive _

private theorem alignof_positive (env : composite_env) :
    forall t : type, zGt (alignof env t) z0
  | .Tvoid => alignAttrPositive noattr _ (zOfNat_positive 1 (by omega))
  | .Tint sz _ a => by
      cases sz with
      | I8 | IBool => exact alignAttrPositive a _ (zOfNat_positive 1 (by omega))
      | I16 => exact alignAttrPositive a _ (zOfNat_positive 2 (by omega))
      | I32 => exact alignAttrPositive a _ (zOfNat_positive 4 (by omega))
  | .Tlong _ a => alignAttrPositive a _ (zPos_positive _)
  | .Tfloat sz a => by
      cases sz with
      | F32 => exact alignAttrPositive a _ (zOfNat_positive 4 (by omega))
      | F64 => exact alignAttrPositive a _ (zPos_positive _)
  | .Tpointer _ a => by
      apply alignAttrPositive
      simp only [CompCert4Lean.X86_64.Archi.ptr64, if_true]
      exact zOfNat_positive 8 (by omega)
  | .Tarray t _ a => alignAttrPositive a _ (alignof_positive env t)
  | .Tfunction _ _ _ => alignAttrPositive noattr _ (zOfNat_positive 1 (by omega))
  | .Tstruct id a => by
      simp only [alignof]
      cases h : PTree.get id env with
      | none => exact alignAttrPositive a _ (zOfNat_positive 1 (by omega))
      | some co =>
          apply alignAttrPositive
          simp only
          rcases co.co_alignof_two_p with ⟨n, hn⟩
          rw [hn]
          exact twoPowerNat_positive n
  | .Tunion id a => by
      simp only [alignof]
      cases h : PTree.get id env with
      | none => exact alignAttrPositive a _ (zOfNat_positive 1 (by omega))
      | some co =>
          apply alignAttrPositive
          simp only
          rcases co.co_alignof_two_p with ⟨n, hn⟩
          rw [hn]
          exact twoPowerNat_positive n

private theorem zMul_nonneg (x y : Z) (hx : zLe z0 x) (hy : zLe z0 y) :
    zLe z0 (zMul x y) := by
  rw [zMul_fromInt]
  exact zFromInt_nonneg _ (Int.mul_nonneg
    ((zLe_iff_zInt _ _).mp hx) ((zLe_iff_zInt _ _).mp hy))

private theorem zAdd_nonneg (x y : Z) (hx : zLe z0 x) (hy : zLe z0 y) :
    zLe z0 (zAdd x y) := by
  rw [zAdd_fromInt]
  exact zFromInt_nonneg _ (Int.add_nonneg
    ((zLe_iff_zInt _ _).mp hx) ((zLe_iff_zInt _ _).mp hy))

private theorem zMul_positive (x y : Z) (hx : zGt x z0) (hy : zGt y z0) :
    zGt (zMul x y) z0 := by
  rw [zMul_fromInt]
  exact zFromInt_positive _ (Int.mul_pos
    ((zLt_iff_zInt _ _).mp hx) ((zLt_iff_zInt _ _).mp hy))

private theorem alignNonnegative (n amount : Z) (hn : zLe z0 n)
    (ha : zGt amount z0) : zLe z0 (align n amount) := by
  simp only [align, CompCert4Lean.Lib.Coqlib.align]
  apply zMul_nonneg
  · apply zDiv_nonneg
    · apply zSub_nonneg
      exact zPositive_ge_one _ (zAdd_positive _ _ hn ha)
    · exact ha
  · exact Int.le_of_lt ha

private theorem floorNonnegative (n amount : Z) (hn : zLe z0 n)
    (ha : zGt amount z0) : zLe z0 (floor n amount) := by
  simp only [floor, CompCert4Lean.Lib.Coqlib.floor]
  exact zMul_nonneg _ _ (zDiv_nonneg _ _ hn ha) (Int.le_of_lt ha)

private theorem zMax_nonneg_right (x y : Z) (hy : zLe z0 y) : zLe z0 (zMax x y) := by
  unfold zLe zMax ZArith.BinInt.Z.le ZArith.BinInt.Z.max at *
  split <;> omega

private theorem zMax_nonneg_left (x y : Z) (hx : zLe z0 x) : zLe z0 (zMax x y) := by
  unfold zLe zMax ZArith.BinInt.Z.le ZArith.BinInt.Z.max at *
  split <;> omega

private theorem sizeof_nonneg (env : composite_env) :
    forall t : type, zLe z0 (sizeof env t)
  | .Tvoid => zOfNat_nonneg 1
  | .Tint sz _ _ => by cases sz <;> exact zOfNat_nonneg _
  | .Tlong _ _ => zOfNat_nonneg 8
  | .Tfloat sz _ => by cases sz <;> exact zOfNat_nonneg _
  | .Tpointer _ _ => by
      simp only [sizeof]
      split <;> exact zOfNat_nonneg _
  | .Tarray t n _ => by
      have ih := sizeof_nonneg env t
      simp only [sizeof]
      apply zMul_nonneg _ _ ih
      exact zMax_nonneg_left _ _ (zOfNat_nonneg 0)
  | .Tfunction _ _ _ => zOfNat_nonneg 1
  | .Tstruct id _ => by
      simp only [sizeof]
      cases h : PTree.get id env with
      | none => exact zOfNat_nonneg 0
      | some co => exact co.co_sizeof_pos
  | .Tunion id _ => by
      simp only [sizeof]
      cases h : PTree.get id env with
      | none => exact zOfNat_nonneg 0
      | some co => exact co.co_sizeof_pos

private theorem sizeof_union_nonneg (env : composite_env) (ms : members) :
    zLe z0 (sizeof_union env ms) := by
  induction ms with
  | nil => exact zOfNat_nonneg 0
  | cons m ms ih =>
      simp only [sizeof_union]
      exact zMax_nonneg_right _ _ ih

private theorem bitsizeof_nonneg (env : composite_env) (t : type) :
    zLe z0 (bitsizeof env t) := by
  simp only [bitsizeof]
  exact zMul_nonneg _ _ (sizeof_nonneg env t) (zOfNat_nonneg 8)

private theorem bitalignof_positive (env : composite_env) (t : type) :
    zGt (bitalignof env t) z0 := by
  simp only [bitalignof]
  exact zMul_positive _ _ (alignof_positive env t) (zOfNat_positive 8 (by omega))

private theorem bitalignof_intsize_positive (sz : intsize) :
    zGt (bitalignof_intsize sz) z0 := by
  cases sz <;> exact zOfNat_positive _ (by omega)

private theorem nextFieldNonnegative (env : composite_env) (pos : Z) (m : member)
    (hpos : zLe z0 pos) : zLe z0 (next_field env pos m) := by
  cases m with
  | Member_plain id t =>
      simp only [next_field]
      exact zAdd_nonneg _ _
        (alignNonnegative _ _ hpos (bitalignof_positive env t))
        (bitsizeof_nonneg env t)
  | Member_bitfield id sz sg a width padding =>
      simp only [next_field]
      cases hwidth : CompCert4Lean.Lib.Coqlib.zle width z0 with
      | left hw =>
          simp only [hwidth]
          exact alignNonnegative _ _ hpos (bitalignof_intsize_positive sz)
      | right hw =>
          simp only [hwidth]
          let s := bitalignof_intsize sz
          let current := floor pos s
          let next := zAdd current s
          have hs : zGt s z0 := bitalignof_intsize_positive sz
          have hwidth_nonneg : zLe z0 width := Int.le_of_lt hw
          have hcurrent : zLe z0 current := floorNonnegative _ _ hpos hs
          have hnext : zLe z0 next := zAdd_nonneg _ _ hcurrent (Int.le_of_lt hs)
          cases hfit : CompCert4Lean.Lib.Coqlib.zle (zAdd pos width) next with
          | left hle =>
              simp only [hfit]
              exact zAdd_nonneg _ _ hpos hwidth_nonneg
          | right hgt =>
              simp only [hfit]
              exact zAdd_nonneg _ _ hnext hwidth_nonneg

private theorem bitsizeofStructNonnegative (env : composite_env) :
    forall (ms : members) (current : Z), zLe z0 current ->
      zLe z0 (bitsizeof_struct env current ms)
  | [], current, hcurrent => hcurrent
  | m :: ms, current, hcurrent => by
      simp only [bitsizeof_struct]
      exact bitsizeofStructNonnegative env ms (next_field env current m)
        (nextFieldNonnegative env current m hcurrent)

private theorem sizeof_struct_nonneg (env : composite_env) (ms : members) :
    zLe z0 (sizeof_struct env ms) := by
  simp only [sizeof_struct, bytes_of_bits]
  apply zDiv_nonneg
  · exact zAdd_nonneg _ _
      (bitsizeofStructNonnegative env ms z0 (zOfNat_nonneg 0))
      (zOfNat_nonneg 7)
  · exact zOfNat_positive 8 (by omega)

private theorem sizeof_composite_nonneg (env : composite_env) (su : struct_or_union)
    (ms : members) : zLe z0 (sizeof_composite env su ms) := by
  cases su with
  | Struct => exact sizeof_struct_nonneg env ms
  | Union => exact sizeof_union_nonneg env ms

private theorem zMax_positive_right (x y : Z) (hy : zGt y z0) :
    zGt (zMax x y) z0 := by
  unfold zMax ZArith.BinInt.Z.max
  split
  · exact hy
  · exact Int.lt_trans hy (Int.lt_of_not_ge (by assumption))

private theorem alignof_composite_positive (env : composite_env) :
    forall ms : members, zGt (alignof_composite env ms) z0
  | [] => by
      simp only [alignof_composite]
      change zGt (.Zpos (PArith.BinPos.Pos.of_nat 1)) z0
      exact zPos_positive _
  | m :: ms => by
      have ih := alignof_composite_positive env ms
      simp only [alignof_composite]
      split
      · exact ih
      · exact zMax_positive_right _ _ ih

private theorem alignAttrTwoPower (a : attr) (al : Z)
    (h : Exists fun n : Nat => al = two_power_nat n) :
    Exists fun n : Nat => align_attr a al = two_power_nat n := by
  cases a with
  | mk volatile alignas =>
      cases alignas with
      | none => exact h
      | some n => exact Exists.intro (NArith.BinNat.N.to_nat n) rfl

private theorem alignofTwoPower (env : composite_env) :
    forall t : type, Exists fun n : Nat => alignof env t = two_power_nat n
  | .Tvoid => alignAttrTwoPower noattr _ (Exists.intro 0 rfl)
  | .Tint sz _ a => by
      cases sz with
      | I8 | IBool => exact alignAttrTwoPower a _ (Exists.intro 0 rfl)
      | I16 => exact alignAttrTwoPower a _ (Exists.intro 1 rfl)
      | I32 => exact alignAttrTwoPower a _ (Exists.intro 2 rfl)
  | .Tlong _ a => alignAttrTwoPower a _ (Exists.intro 3 rfl)
  | .Tfloat sz a => by
      cases sz with
      | F32 => exact alignAttrTwoPower a _ (Exists.intro 2 rfl)
      | F64 => exact alignAttrTwoPower a _ (Exists.intro 3 rfl)
  | .Tpointer _ a => alignAttrTwoPower a _ (Exists.intro 3 rfl)
  | .Tarray t _ a => alignAttrTwoPower a _ (alignofTwoPower env t)
  | .Tfunction _ _ _ => alignAttrTwoPower noattr _ (Exists.intro 0 rfl)
  | .Tstruct id a => by
      cases h : PTree.get id env with
      | none =>
          simp only [alignof, h]
          exact alignAttrTwoPower a _ (Exists.intro 0 rfl)
      | some co =>
          simp only [alignof, h]
          exact alignAttrTwoPower a _ co.co_alignof_two_p
  | .Tunion id a => by
      cases h : PTree.get id env with
      | none =>
          simp only [alignof, h]
          exact alignAttrTwoPower a _ (Exists.intro 0 rfl)
      | some co =>
          simp only [alignof, h]
          exact alignAttrTwoPower a _ co.co_alignof_two_p

private theorem alignofCompositeTwoPower (env : composite_env) :
    forall ms : members, Exists fun n : Nat => alignof_composite env ms = two_power_nat n
  | [] => Exists.intro 0 rfl
  | m :: ms => by
      simp only [alignof_composite]
      split
      · exact alignofCompositeTwoPower env ms
      · rcases alignofCompositeTwoPower env ms with ⟨n, hn⟩
        rcases alignofTwoPower env (type_member m) with ⟨k, hk⟩
        rw [hk, hn]
        unfold zMax ZArith.BinInt.Z.max
        split
        · exact Exists.intro n rfl
        · exact Exists.intro k rfl

private theorem align_nonneg (n amount : Z) (hn : zLe z0 n) (ha : zGt amount z0) :
    zLe z0 (align n amount) := by
  exact alignNonnegative n amount hn ha

private theorem align_divisible (n amount : Z) : zDivide amount (align n amount) := by
  unfold zDivide align CompCert4Lean.Lib.Coqlib.align ZArith.BinInt.Z.divide
  refine Exists.intro (zDiv (zSub (zAdd n amount) z1) amount) ?_
  simp [ZArith.BinInt.Z.mul, Int.mul_comm]

def composite_of_def (env : composite_env) (id : ident) (su : struct_or_union)
    (ms : members) (a : attr) : Errors.res composite :=
  match hget : PTree.get id env with
  | some _ => .Error (Errors.MSG duplicateCompositeText :: Errors.CTX id :: [])
  | none =>
      match hcomplete : complete_members env ms with
      | false => .Error (Errors.MSG incompleteCompositeText :: Errors.CTX id :: [])
      | true =>
          let al := align_attr a (alignof_composite env ms)
          let sz := align (sizeof_composite env su ms) al
          .OK
            { co_su := su
              co_members := ms
              co_attr := a
              co_sizeof := sz
              co_alignof := al
              co_rank := rank_members env ms
              co_sizeof_pos := align_nonneg _ _ (sizeof_composite_nonneg env su ms)
                (alignAttrPositive a _ (alignof_composite_positive env ms))
              co_alignof_two_p := alignAttrTwoPower a _ (alignofCompositeTwoPower env ms)
              co_sizeof_alignof := align_divisible _ _ }

def add_composite_definitions (env : composite_env) :
    List composite_definition -> Errors.res composite_env
  | [] => .OK env
  | .Composite id su ms a :: defs =>
      match composite_of_def env id su ms a with
      | .Error msg => .Error msg
      | .OK co => add_composite_definitions (PTree.set id co env) defs

def build_composite_env (defs : List composite_definition) : Errors.res composite_env :=
  add_composite_definitions (PTree.empty composite) defs

/-! ## Stability and consistency statement surface -/

def add_composite_definitions_incrStatement : Prop :=
  ∀ id co defs env1 env2,
    add_composite_definitions env1 defs = .OK env2 →
    PTree.get id env1 = some co →
    PTree.get id env2 = some co

def alignof_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall t, complete_type env t = true -> alignof env' t = alignof env t

def sizeof_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall t, complete_type env t = true -> sizeof env' t = sizeof env t

def complete_type_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall t, complete_type env t = true -> complete_type env' t = true

def rank_type_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall t, complete_type env t = true -> rank_type env' t = rank_type env t

def alignof_composite_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms, complete_members env ms = true ->
      alignof_composite env' ms = alignof_composite env ms

def next_field_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall pos m, complete_type env (type_member m) = true ->
      next_field env' pos m = next_field env pos m

def bitsizeof_struct_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms pos, complete_members env ms = true ->
      bitsizeof_struct env' pos ms = bitsizeof_struct env pos ms

def sizeof_union_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms, complete_members env ms = true -> sizeof_union env' ms = sizeof_union env ms

def sizeof_composite_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall su ms, complete_members env ms = true ->
      sizeof_composite env' su ms = sizeof_composite env su ms

def complete_members_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms, complete_members env ms = true -> complete_members env' ms = true

def rank_members_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall ms, complete_members env ms = true -> rank_members env' ms = rank_members env ms

def layout_field_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall pos m, complete_type env (type_member m) = true ->
      layout_field env' pos m = layout_field env pos m

def field_offset_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall f ms, complete_members env ms = true ->
      field_offset env' f ms = field_offset env f ms

def union_field_offset_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall f ms, complete_members env ms = true ->
      union_field_offset env' f ms = union_field_offset env f ms

structure composite_consistent (env : composite_env) (co : composite) : Prop where
  co_consistent_complete : complete_members env co.co_members = true
  co_consistent_alignof :
    co.co_alignof = align_attr co.co_attr (alignof_composite env co.co_members)
  co_consistent_sizeof :
    co.co_sizeof = align (sizeof_composite env co.co_su co.co_members) co.co_alignof
  co_consistent_rank : co.co_rank = rank_members env co.co_members

export composite_consistent (co_consistent_complete co_consistent_alignof
  co_consistent_sizeof co_consistent_rank)

def Build_composite_consistent (env : composite_env) (co : composite)
    (h_complete : complete_members env co.co_members = true)
    (h_alignof : co.co_alignof = align_attr co.co_attr (alignof_composite env co.co_members))
    (h_sizeof : co.co_sizeof = align (sizeof_composite env co.co_su co.co_members) co.co_alignof)
    (h_rank : co.co_rank = rank_members env co.co_members) : composite_consistent env co :=
  { co_consistent_complete := h_complete
    co_consistent_alignof := h_alignof
    co_consistent_sizeof := h_sizeof
    co_consistent_rank := h_rank }

def composite_env_consistent (env : composite_env) : Prop :=
  forall id co, PTree.get id env = some co -> composite_consistent env co

def composite_consistent_stableStatement : Prop :=
  forall env env',
    (forall id co, PTree.get id env = some co -> PTree.get id env' = some co) ->
    forall co, composite_consistent env co -> composite_consistent env' co

def composite_of_def_consistentStatement : Prop :=
  forall env id su ms a co,
    composite_of_def env id su ms a = .OK co -> composite_consistent env co

def build_composite_env_consistentStatement : Prop :=
  forall defs env,
    build_composite_env defs = .OK env -> composite_env_consistent env

def build_composite_env_charactStatement : Prop :=
  ∀ id su m a defs env,
    build_composite_env defs = .OK env →
    Composite id su m a ∈ defs →
    ∃ co,
      PTree.get id env = some co ∧
      co.co_members = m ∧ co.co_attr = a ∧ co.co_su = su

def build_composite_env_domainStatement : Prop :=
  ∀ env defs id co,
    build_composite_env defs = .OK env →
    PTree.get id env = some co →
    Composite id co.co_su co.co_members co.co_attr ∈ defs

/-! ## Programs and compilation units -/

inductive fundef (F : Type) : Type where
  | Internal (f : F)
  | External (ef : external_function) (args : List type) (result : type)
      (cc : calling_convention)

export fundef (Internal External)

structure program (F : Type) : Type where
  prog_defs : List (ident × AST.globdef (fundef F) type)
  prog_public : List ident
  prog_main : ident
  prog_types : List composite_definition
  prog_comp_env : composite_env
  prog_comp_env_eq : build_composite_env prog_types = .OK prog_comp_env

export program (prog_defs prog_public prog_main prog_types prog_comp_env prog_comp_env_eq)

def program_of_program {F : Type} (p : program F) : AST.program (fundef F) type :=
  { prog_defs := p.prog_defs, prog_public := p.prog_public, prog_main := p.prog_main }

/-! ## Separate compilation and linking -/

private def boolOfSumbool {P Q : Prop} : Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

def check_compat_composite (l : List composite_definition)
    (cd : composite_definition) : Bool :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb
    (fun cd' =>
      match AST.ident_eq (name_composite_def cd') (name_composite_def cd) with
      | .left _ => boolOfSumbool (composite_def_eq cd cd')
      | .right _ => true)
    l

def filter_redefs (l1 l2 : List composite_definition) : List composite_definition :=
  let names1 := l1.map name_composite_def
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.filter
    (fun cd =>
      match CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
          AST.ident_eq (name_composite_def cd) names1 with
      | .left _ => false
      | .right _ => true)
    l2

def link_composite_defs (l1 l2 : List composite_definition) :
    Option (List composite_definition) :=
  match CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb
      (check_compat_composite l2) l1 with
  | true => some (l1 ++ filter_redefs l1 l2)
  | false => none

def link_composite_def_invStatement : Prop :=
  ∀ l1 l2 l,
    link_composite_defs l1 l2 = some l →
      (∀ cd1 cd2, cd1 ∈ l1 → cd2 ∈ l2 →
        name_composite_def cd2 = name_composite_def cd1 → cd2 = cd1) ∧
      l = l1 ++ filter_redefs l1 l2 ∧
      (∀ x, x ∈ l ↔ x ∈ l1 ∨ x ∈ l2)

def link_composite_def_inv : Prop := link_composite_def_invStatement

def add_composite_definitions_appendStatement : Prop :=
  ∀ l1 l2 env env'',
    add_composite_definitions env (l1 ++ l2) = .OK env'' ↔
      ∃ env',
        add_composite_definitions env l1 = .OK env' ∧
        add_composite_definitions env' l2 = .OK env''

def composite_eqStatement : Prop :=
  ∀ (su1 : struct_or_union) (m1 : members) (a1 : attr) (sz1 al1 : Z) (r1 : Nat)
      (pos1 : zLe z0 sz1)
      (al2p1 : ∃ n : Nat, al1 = two_power_nat n)
      (szal1 : zDivide al1 sz1)
      (su2 : struct_or_union) (m2 : members) (a2 : attr) (sz2 al2 : Z) (r2 : Nat)
      (pos2 : zLe z0 sz2)
      (al2p2 : ∃ n : Nat, al2 = two_power_nat n)
      (szal2 : zDivide al2 sz2),
    su1 = su2 → m1 = m2 → a1 = a2 → sz1 = sz2 → al1 = al2 → r1 = r2 →
    composite.mk su1 m1 a1 sz1 al1 r1 pos1 al2p1 szal1 =
      composite.mk su2 m2 a2 sz2 al2 r2 pos2 al2p2 szal2

def composite_of_def_eqStatement : Prop :=
  ∀ env id co,
    composite_consistent env co →
    PTree.get id env = none →
    composite_of_def env id co.co_su co.co_members co.co_attr = .OK co

def composite_consistent_uniqueStatement : Prop :=
  ∀ env co1 co2,
    composite_consistent env co1 →
    composite_consistent env co2 →
    co1.co_su = co2.co_su →
    co1.co_members = co2.co_members →
    co1.co_attr = co2.co_attr →
    co1 = co2

def composite_of_def_stableStatement : Prop :=
  ∀ (env env' : composite_env)
      (EXTENDS : ∀ id co, PTree.get id env = some co → PTree.get id env' = some co)
      id su m a co,
    PTree.get id env' = none →
    composite_of_def env id su m a = .OK co →
    composite_of_def env' id su m a = .OK co

def link_add_composite_definitionsStatement : Type :=
  ∀ l0 env0,
    build_composite_env l0 = .OK env0 →
    ∀ l env1 env1' env2,
      add_composite_definitions env1 l = .OK env1' →
      (∀ id co, PTree.get id env1 = some co → PTree.get id env2 = some co) →
      (∀ id co, PTree.get id env0 = some co → PTree.get id env2 = some co) →
      (∀ id,
        PTree.get id env2 =
          match CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
              AST.ident_eq id (l0.map name_composite_def) with
          | .left _ => PTree.get id env0
          | .right _ => PTree.get id env1) →
      (∀ cd1 cd2,
        cd1 ∈ l0 → cd2 ∈ l → name_composite_def cd2 = name_composite_def cd1 → cd2 = cd1) →
      Subtype fun env2' =>
        add_composite_definitions env2 (filter_redefs l0 l) = .OK env2' ∧
        (∀ id co, PTree.get id env1' = some co → PTree.get id env2' = some co) ∧
        (∀ id co, PTree.get id env0 = some co → PTree.get id env2' = some co)

def link_build_composite_envStatement : Type :=
  ∀ l1 l2 l env1 env2,
    build_composite_env l1 = .OK env1 →
    build_composite_env l2 = .OK env2 →
    link_composite_defs l1 l2 = some l →
    Subtype fun env =>
      build_composite_env l = .OK env ∧
      (∀ id co, PTree.get id env1 = some co → PTree.get id env = some co) ∧
      (∀ id co, PTree.get id env2 = some co → PTree.get id env = some co)

def link_build_composite_env : Type := link_build_composite_envStatement

/-!
The source [Program Instance] declarations carry proof obligations which are
intentionally discharged in the later proof-grinding phase.  Keep those
obligations explicit instead of manufacturing inhabited proof fields or making
the instances global.  The executable link functions remain the source
operations; these records carry their exact theorem-facing laws and the
source Type-valued composite-environment witness operation.
-/
def link_composite_defs_link_linkorderStatement : Prop :=
  ∀ l1 l2 l,
    link_composite_defs l1 l2 = some l →
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl l1 l ∧
      CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl l2 l

structure Linker_composite_defs_obligations : Type where
  link_composite_def_inv : link_composite_def_invStatement
  link_build_composite_env : link_build_composite_envStatement
  link_linkorder : link_composite_defs_link_linkorderStatement

abbrev LinkerCompositeDefsCertificate := Linker_composite_defs_obligations

def lift_option {A : Type} (opt : Option A) :
    CompCert4Lean.Foundation.Logic.Support.Sumor
      (Subtype (fun x : A => opt = some x)) (opt = none) :=
  match opt with
  | some x => .inleft ⟨x, rfl⟩
  | none => .inright rfl

instance Linker_types : CompCert4Lean.Common.Linking.Linker type where
  link := fun t1 t2 =>
    match type_eq t1 t2 with
    | .left _ => some t1
    | .right _ => none
  linkorder := Eq
  linkorder_refl := fun _ => rfl
  linkorder_trans := by
    intro x y z hxy hyz
    exact hxy.trans hyz
  link_linkorder := by
    intro x y z h
    cases hdec : type_eq x y with
    | left hxy =>
        simp only [hdec] at h
        cases Option.some.inj h
        exact ⟨rfl, hxy.symm⟩
    | right _ =>
        simp only [hdec] at h
        cases h

def link_fundef {F : Type} (fd1 fd2 : fundef F) : Option (fundef F) :=
  match fd1, fd2 with
  | .Internal _, .Internal _ => none
  | .External ef1 args1 result1 cc1, .External ef2 args2 result2 cc2 =>
      match CompCert4Lean.Common.AST.external_function_eq ef1 ef2 with
      | .right _ => none
      | .left _ =>
          match typelist_eq args1 args2 with
          | .right _ => none
          | .left _ =>
              match type_eq result1 result2 with
              | .right _ => none
              | .left _ =>
                  match CompCert4Lean.Common.AST.calling_convention_eq cc1 cc2 with
                  | .right _ => none
                  | .left _ => some (.External ef1 args1 result1 cc1)
  | .Internal f, .External (.EF_external _ _) _ _ _ => some (.Internal f)
  | .External (.EF_external _ _) _ _ _, .Internal f => some (.Internal f)
  | _, _ => none

inductive linkorder_fundef {F : Type} : fundef F → fundef F → Prop where
  | linkorder_fundef_refl (fd : fundef F) : linkorder_fundef fd fd
  | linkorder_fundef_ext_int (f : F) (id : RocqString) (sg : signature)
      (args : List type) (result : type) (cc : calling_convention) :
      linkorder_fundef (.External (.EF_external id sg) args result cc) (.Internal f)

export linkorder_fundef (linkorder_fundef_refl linkorder_fundef_ext_int)

instance Linker_fundef (F : Type) :
    CompCert4Lean.Common.Linking.Linker (fundef F) where
  link := link_fundef
  linkorder := linkorder_fundef
  linkorder_refl := linkorder_fundef.linkorder_fundef_refl
  linkorder_trans := by
    intro x y z hxy hyz
    cases hxy <;> cases hyz <;> constructor
  link_linkorder := by
    intro x y z h
    cases x with
    | Internal f1 =>
        cases y with
        | Internal f2 => simp [link_fundef] at h
        | External ef args result cc =>
            cases ef <;> simp [link_fundef] at h
            case EF_external id sg =>
              subst z
              exact ⟨linkorder_fundef.linkorder_fundef_refl _,
                linkorder_fundef.linkorder_fundef_ext_int f1 id sg args result cc⟩
    | External ef1 args1 result1 cc1 =>
        cases y with
        | Internal f2 =>
            cases ef1 <;> simp [link_fundef] at h
            case EF_external id sg =>
              subst z
              exact ⟨linkorder_fundef.linkorder_fundef_ext_int f2 id sg args1 result1 cc1,
                linkorder_fundef.linkorder_fundef_refl _⟩
        | External ef2 args2 result2 cc2 =>
            cases hefEq : CompCert4Lean.Common.AST.external_function_eq ef1 ef2 with
            | right _ =>
                simp [link_fundef, hefEq] at h
            | left hef =>
                subst ef2
                cases hargsEq : typelist_eq args1 args2 with
                | right _ =>
                    simp [link_fundef, hefEq, hargsEq] at h
                | left hargs =>
                    subst args2
                    cases hresultEq : type_eq result1 result2 with
                    | right _ =>
                        simp [link_fundef, hefEq, hargsEq, hresultEq] at h
                    | left hresult =>
                        subst result2
                        cases hccEq : CompCert4Lean.Common.AST.calling_convention_eq cc1 cc2 with
                        | right _ =>
                            simp [link_fundef, hefEq, hargsEq, hresultEq, hccEq] at h
                        | left hcc =>
                            subst cc2
                            simp [link_fundef, hefEq, hargsEq, hresultEq, hccEq] at h
                            cases h
                            exact ⟨linkorder_fundef.linkorder_fundef_refl _,
                              linkorder_fundef.linkorder_fundef_refl _⟩

def linkorder_program {F : Type} (p1 p2 : program F) : Prop :=
  CompCert4Lean.Common.Linking.linkorder
      (program_of_program p1) (program_of_program p2) ∧
    ∀ id co, PTree.get id p1.prog_comp_env = some co →
      PTree.get id p2.prog_comp_env = some co

def link_program {F : Type} (certificate : Linker_composite_defs_obligations)
    (p1 p2 : program F) : Option (program F) :=
  match CompCert4Lean.Common.Linking.link
      (program_of_program p1) (program_of_program p2) with
  | none => none
  | some p =>
      match lift_option (link_composite_defs p1.prog_types p2.prog_types) with
      | .inright _ => none
      | .inleft typs =>
          let env := certificate.link_build_composite_env
            p1.prog_types p2.prog_types typs.val
            p1.prog_comp_env p2.prog_comp_env
            p1.prog_comp_env_eq p2.prog_comp_env_eq typs.property
          some
            { prog_defs := p.prog_defs
              prog_public := p.prog_public
              prog_main := p.prog_main
              prog_types := typs.val
              prog_comp_env := env.val
              prog_comp_env_eq := env.property.1 }

def link_program_link_linkorderStatement
    (certificate : Linker_composite_defs_obligations) : Prop :=
  ∀ {F : Type} (p1 p2 p : program F),
    link_program certificate p1 p2 = some p →
      linkorder_program p1 p ∧ linkorder_program p2 p

structure Linker_program_obligations : Type where
  composite_defs : Linker_composite_defs_obligations
  link_linkorder : link_program_link_linkorderStatement composite_defs

abbrev LinkerProgramCertificate := Linker_program_obligations

def link_program_with_certificate {F : Type}
    (certificate : Linker_program_obligations) (p1 p2 : program F) : Option (program F) :=
  link_program certificate.composite_defs p1 p2

def Linker_composite_defs (certificate : Linker_composite_defs_obligations) :
    CompCert4Lean.Common.Linking.Linker (List composite_definition) where
  link := link_composite_defs
  linkorder := CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl
  linkorder_refl := by
    intro l
    exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl_refl l
  linkorder_trans := by
    intro l1 l2 l3 h12 h23
    exact CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.incl_tran h12 h23
  link_linkorder := certificate.link_linkorder

def Linker_program (F : Type) (certificate : Linker_program_obligations) :
    CompCert4Lean.Common.Linking.Linker (program F) where
  link := link_program_with_certificate certificate
  linkorder := linkorder_program
  linkorder_refl := by
    intro p
    refine ⟨(CompCert4Lean.Common.Linking.Linker.linkorder_refl
      (A := CompCert4Lean.Common.AST.program (fundef F) type) (program_of_program p)), ?_⟩
    intro id co hget
    exact hget
  linkorder_trans := by
    intro p1 p2 p3 h12 h23
    rcases h12 with ⟨h12defs, h12env⟩
    rcases h23 with ⟨h23defs, h23env⟩
    refine ⟨
      CompCert4Lean.Common.Linking.Linker.linkorder_trans
        (A := CompCert4Lean.Common.AST.program (fundef F) type)
        (program_of_program p1) (program_of_program p2) (program_of_program p3)
        h12defs h23defs,
      ?_⟩
    intro id co hget
    exact h23env id co (h12env id co hget)
  link_linkorder := by
    simpa [link_program_with_certificate] using certificate.link_linkorder

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem align_attr_two_p : align_attr_two_pStatement := by
  intro al a h
  exact alignAttrTwoPower a al h

theorem alignof_two_p : alignof_two_pStatement := by
  exact alignofTwoPower

theorem alignof_pos : alignof_posStatement := by
  exact alignof_positive

theorem sizeof_pos : sizeof_posStatement := by
  exact sizeof_nonneg

theorem bitalignof_intsize_pos : bitalignof_intsize_posStatement := by
  exact bitalignof_intsize_positive

theorem alignof_composite_two_p : alignof_composite_two_pStatement := by
  exact alignofCompositeTwoPower

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem alignof_composite_pos : alignof_composite_posStatement := by
  intro env m a
  exact alignAttrPositive a _ (alignof_composite_positive env m)

theorem sizeof_union_pos : sizeof_union_posStatement := by
  intro env m
  exact sizeof_union_nonneg env m

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_zInt_zFromInt (i : Int) : zInt (zFromInt i) = i := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i) = i
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt i

private theorem suffix_alignLe (x y : Z) (hy : zGt y z0) : zLe x (align x y) := by
  apply (zLe_iff_zInt _ _).mpr
  simp only [align, CompCert4Lean.Lib.Coqlib.align, zMul_fromInt, zDiv_fromInt,
    zSub_fromInt, zAdd_fromInt, suffix_zInt_zFromInt]
  unfold intDivEucl
  have hy0 : zInt y ≠ 0 := Int.ne_of_gt ((zLt_iff_zInt _ _).mp hy)
  have hyp : 0 < zInt y := (zLt_iff_zInt _ _).mp hy
  rw [if_neg hy0, if_pos hyp]
  have hr := Int.emod_nonneg (zInt x + zInt y - 1) hy0
  have hrlt := Int.emod_lt_of_pos (zInt x + zInt y - 1) hyp
  have hdecomp : (zInt x + zInt y - 1).ediv (zInt y) * zInt y +
      (zInt x + zInt y - 1) % zInt y = zInt x + zInt y - 1 := by
    rw [Int.mul_comm]
    exact Int.mul_ediv_add_emod (zInt x + zInt y - 1) (zInt y)
  have hone : zInt z1 = 1 := rfl
  rw [hone]
  omega

private theorem suffix_floorInterval (x y : Z) (hy : zGt y z0) :
    zLe (floor x y) x ∧ zLt x (zAdd (floor x y) y) := by
  have hyi : 0 < zInt y := (zLt_iff_zInt _ _).mp hy
  have hy0 : zInt y ≠ 0 := Int.ne_of_gt hyi
  have hr := Int.emod_nonneg (zInt x) hy0
  have hrlt := Int.emod_lt_of_pos (zInt x) hyi
  have hdecomp : (zInt x).ediv (zInt y) * zInt y + (zInt x) % zInt y = zInt x := by
    rw [Int.mul_comm]
    exact Int.mul_ediv_add_emod (zInt x) (zInt y)
  constructor
  · apply (zLe_iff_zInt _ _).mpr
    simp only [floor, CompCert4Lean.Lib.Coqlib.floor, zMul_fromInt, zDiv_fromInt,
      suffix_zInt_zFromInt]
    unfold intDivEucl
    rw [if_neg hy0, if_pos hyi]
    omega
  · apply (zLt_iff_zInt _ _).mpr
    simp only [floor, CompCert4Lean.Lib.Coqlib.floor, zMul_fromInt, zDiv_fromInt,
      zAdd_fromInt, suffix_zInt_zFromInt]
    unfold intDivEucl
    rw [if_neg hy0, if_pos hyi]
    omega

private theorem suffix_leAdd (x y z : Z) (hxy : zLe x y) (hz : zLe z0 z) :
    zLe x (zAdd y z) := by
  apply (zLe_iff_zInt _ _).mpr
  rw [zAdd_fromInt, suffix_zInt_zFromInt]
  exact Int.le_trans ((zLe_iff_zInt _ _).mp hxy)
    (Int.le_add_of_nonneg_right ((zLe_iff_zInt _ _).mp hz))

theorem next_field_incr : next_field_incrStatement := by
  intro env pos m
  cases m with
  | Member_plain id t =>
      simp only [next_field]
      exact suffix_leAdd _ _ _ (suffix_alignLe _ _ (bitalignof_positive env t))
        (bitsizeof_nonneg env t)
  | Member_bitfield id sz sg a width padding =>
      simp only [next_field]
      cases hwidth : CompCert4Lean.Lib.Coqlib.zle width z0 with
      | left hw =>
          simp only [hwidth]
          exact suffix_alignLe _ _ (bitalignof_intsize_positive sz)
      | right hw =>
          simp only [hwidth]
          let s := bitalignof_intsize sz
          let current := floor pos s
          let next := zAdd current s
          have hs : zGt s z0 := bitalignof_intsize_positive sz
          have hwidth0 : zLe z0 width := Int.le_of_lt hw
          have hinterval := suffix_floorInterval pos s hs
          cases hfit : CompCert4Lean.Lib.Coqlib.zle (zAdd pos width) next with
          | left hle =>
              simp only [hfit]
              exact suffix_leAdd _ _ _ (Int.le_refl _) hwidth0
          | right hgt =>
              simp only [hfit]
              exact suffix_leAdd _ _ _ (Int.le_of_lt hinterval.2) hwidth0

theorem bitsizeof_struct_incr : bitsizeof_struct_incrStatement := by
  intro env m current
  induction m generalizing current with
  | nil =>
      simp only [bitsizeof_struct]
      exact Int.le_refl _
  | cons a ms ih =>
      simp only [bitsizeof_struct]
      exact Int.le_trans (next_field_incr env current a) (ih (next_field env current a))

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_intOfZ_two_power_nat (n : Nat) :
    intOfZ (two_power_nat n) = (2 : Int) ^ n := by
  unfold two_power_nat ZArith.Zpower.two_power_nat
  unfold ZArith.BinInt.Z.pow ZArith.BinInt.Z.of_nat
  simp only [intOfZ_zOfInt]
  have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  rw [h2]
  split
  · next h => exact (Int.not_lt_of_ge (Int.natCast_nonneg _) h).elim
  · next h => rw [intOfZ_zOfInt]; rfl

private theorem suffix_two_power_nat_ge_eight (n : Nat) (h : 4 ≤ n) :
    (8 : Int) ≤ intOfZ (two_power_nat n) := by
  rw [suffix_intOfZ_two_power_nat]
  have hp : ∀ m : Nat, (2 : Int) ^ m = Int.ofNat (2 ^ m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [Int.pow_succ, ih]
        rfl
  rw [hp n]
  change Int.ofNat 8 ≤ Int.ofNat (2 ^ n)
  exact Int.ofNat_le.mpr
    (Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) h))

private theorem suffix_min_eight_two_power_nat (n : Nat) (h : 4 ≤ n) :
    zMin (zOfNat 8) (two_power_nat n) = zOfNat 8 := by
  unfold zMin ZArith.BinInt.Z.min
  split
  · rfl
  · next hnot =>
      exfalso
      exact hnot (by
        change (8 : Int) ≤ intOfZ (two_power_nat n)
        exact suffix_two_power_nat_ge_eight n h)

theorem alignof_blockcopy_1248 : alignof_blockcopy_1248Statement := by
  intro env t
  cases t with
  | Tvoid => exact Or.inl rfl
  | Tint sz _ _ =>
      cases sz with
      | I8 => exact Or.inl rfl
      | I16 => exact Or.inr (Or.inl rfl)
      | I32 => exact Or.inr (Or.inr (Or.inl rfl))
      | IBool => exact Or.inl rfl
  | Tlong _ _ => exact Or.inr (Or.inr (Or.inr rfl))
  | Tfloat sz _ =>
      cases sz with
      | F32 => exact Or.inr (Or.inr (Or.inl rfl))
      | F64 => exact Or.inr (Or.inr (Or.inr rfl))
  | Tpointer _ _ =>
      simp [alignof_blockcopy, CompCert4Lean.X86_64.Archi.ptr64]
  | Tarray t _ _ => exact alignof_blockcopy_1248 env t
  | Tfunction _ _ _ => exact Or.inl rfl
  | Tstruct id _ =>
      simp only [alignof_blockcopy]
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => exact Or.inl rfl
      | some co =>
          change zMin (zOfNat 8) co.co_alignof = zOfNat 1 ∨
            zMin (zOfNat 8) co.co_alignof = zOfNat 2 ∨
              zMin (zOfNat 8) co.co_alignof = zOfNat 4 ∨
                zMin (zOfNat 8) co.co_alignof = zOfNat 8
          rcases co.co_alignof_two_p with ⟨n, hn⟩
          rw [hn]
          by_cases hsmall : n < 4
          · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
            rcases hcases with rfl | rfl | rfl | rfl <;> decide
          · exact Or.inr (Or.inr (Or.inr (suffix_min_eight_two_power_nat n (by omega))))
  | Tunion id _ =>
      simp only [alignof_blockcopy]
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => exact Or.inl rfl
      | some co =>
          change zMin (zOfNat 8) co.co_alignof = zOfNat 1 ∨
            zMin (zOfNat 8) co.co_alignof = zOfNat 2 ∨
              zMin (zOfNat 8) co.co_alignof = zOfNat 4 ∨
                zMin (zOfNat 8) co.co_alignof = zOfNat 8
          rcases co.co_alignof_two_p with ⟨n, hn⟩
          rw [hn]
          by_cases hsmall : n < 4
          · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
            rcases hcases with rfl | rfl | rfl | rfl <;> decide
          · exact Or.inr (Or.inr (Or.inr (suffix_min_eight_two_power_nat n (by omega))))

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem sizeof_composite_pos : sizeof_composite_posStatement := by
  intro env su ms
  exact sizeof_composite_nonneg env su ms

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem alignof_stable : alignof_stableStatement := by
  intro env env' henv t hcomplete
  induction t using type.rec (motive_2 := fun _ => True) with
  | Tvoid => rfl
  | Tint sz sg a => cases sz <;> rfl
  | Tlong sg a => rfl
  | Tfloat sz a => cases sz <;> rfl
  | Tpointer t a => rfl
  | Tarray t n a ih =>
      simp only [complete_type] at hcomplete
      simp [alignof, ih hcomplete]
  | Tfunction args res cc ihargs ihres => rfl
  | Tstruct id a =>
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => simp [complete_type, hget] at hcomplete
      | some co =>
          have hget' := henv id co hget
          simp [alignof, hget, hget']
  | Tunion id a =>
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => simp [complete_type, hget] at hcomplete
      | some co =>
          have hget' := henv id co hget
          simp [alignof, hget, hget']
  | nil => trivial
  | cons head tail ihhead ihtail => trivial

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem sizeof_stable : sizeof_stableStatement := by
  intro env env' henv t hcomplete
  induction t using type.rec (motive_2 := fun _ => True) with
  | Tvoid => rfl
  | Tint sz sg a => cases sz <;> rfl
  | Tlong sg a => rfl
  | Tfloat sz a => cases sz <;> rfl
  | Tpointer t a => rfl
  | Tarray t n a ih =>
      simp only [complete_type] at hcomplete
      simp [sizeof, ih hcomplete]
  | Tfunction args res cc ihargs ihres => rfl
  | Tstruct id a =>
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => simp [complete_type, hget] at hcomplete
      | some co =>
          have hget' := henv id co hget
          simp [sizeof, hget, hget']
  | Tunion id a =>
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => simp [complete_type, hget] at hcomplete
      | some co =>
          have hget' := henv id co hget
          simp [sizeof, hget, hget']
  | nil => trivial
  | cons head tail ihhead ihtail => trivial

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem complete_type_stable : complete_type_stableStatement := by
  intro env env' henv t hcomplete
  induction t using type.rec (motive_2 := fun _ => True) with
  | Tvoid => simp only [complete_type] at hcomplete; exact Bool.noConfusion hcomplete
  | Tint sz sg a => simp [complete_type]
  | Tlong sg a => simp [complete_type]
  | Tfloat sz a => simp [complete_type]
  | Tpointer t a => simp [complete_type]
  | Tarray t n a ih =>
      simp only [complete_type] at hcomplete ⊢
      exact ih hcomplete
  | Tfunction args res cc => simp only [complete_type] at hcomplete; exact Bool.noConfusion hcomplete
  | Tstruct id a =>
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => simp [complete_type, hget] at hcomplete
      | some co =>
          have hget' := henv id co hget
          simp [complete_type, hget, hget']
  | Tunion id a =>
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => simp [complete_type, hget] at hcomplete
      | some co =>
          have hget' := henv id co hget
          simp [complete_type, hget, hget']
  | nil => trivial
  | cons head tail ihhead ihtail => trivial

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem rank_type_stable : rank_type_stableStatement := by
  intro env env' henv t hcomplete
  induction t using type.rec (motive_2 := fun _ => True) with
  | Tvoid => rfl
  | Tint sz sg a => cases sz <;> rfl
  | Tlong sg a => rfl
  | Tfloat sz a => cases sz <;> rfl
  | Tpointer t a => rfl
  | Tarray t n a ih =>
      simp only [complete_type] at hcomplete
      simp [rank_type, ih hcomplete]
  | Tfunction args res cc ihargs ihres => rfl
  | Tstruct id a =>
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => simp [complete_type, hget] at hcomplete
      | some co =>
          have hget' := henv id co hget
          simp [rank_type, hget, hget']
  | Tunion id a =>
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => simp [complete_type, hget] at hcomplete
      | some co =>
          have hget' := henv id co hget
          simp [rank_type, hget, hget']
  | nil => trivial
  | cons head tail ihhead ihtail => trivial

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem alignof_composite_stable : alignof_composite_stableStatement := by
  intro env env' henv ms hcomplete
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      simp only [complete_members, Bool.and_eq_true] at hcomplete
      simp only [alignof_composite]
      by_cases hpadding : member_is_padding m
      · simp only [hpadding, ↓reduceIte]
        exact ih hcomplete.2
      · simp only [hpadding, ↓reduceIte]
        rw [alignof_stable env env' henv (type_member m) hcomplete.1,
          ih hcomplete.2]

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem next_field_stable : next_field_stableStatement := by
  intro env env' henv pos m hcomplete
  cases m with
  | Member_plain id t =>
      simp only [next_field, bitalignof, bitsizeof]
      rw [alignof_stable env env' henv t hcomplete,
        sizeof_stable env env' henv t hcomplete]
  | Member_bitfield id sz sg a width padding =>
      rfl

theorem bitsizeof_struct_stable : bitsizeof_struct_stableStatement := by
  intro env env' henv ms pos hcomplete
  induction ms generalizing pos with
  | nil => rfl
  | cons m ms ih =>
      simp only [complete_members, Bool.and_eq_true] at hcomplete
      simp only [bitsizeof_struct]
      rw [next_field_stable env env' henv pos m hcomplete.1]
      exact ih (next_field env pos m) hcomplete.2

theorem sizeof_union_stable : sizeof_union_stableStatement := by
  intro env env' henv ms hcomplete
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      simp only [complete_members, Bool.and_eq_true] at hcomplete
      simp only [sizeof_union]
      rw [sizeof_stable env env' henv (type_member m) hcomplete.1,
        ih hcomplete.2]

theorem sizeof_composite_stable : sizeof_composite_stableStatement := by
  intro env env' henv su ms hcomplete
  cases su with
  | Struct =>
      simp only [sizeof_composite, sizeof_struct]
      rw [bitsizeof_struct_stable env env' henv ms z0 hcomplete]
  | Union =>
      simp only [sizeof_composite]
      exact sizeof_union_stable env env' henv ms hcomplete

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem complete_members_stable : complete_members_stableStatement := by
  intro env env' henv ms hcomplete
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      simp only [complete_members, Bool.and_eq_true] at hcomplete ⊢
      exact ⟨complete_type_stable env env' henv (type_member m) hcomplete.1,
        ih hcomplete.2⟩

theorem rank_members_stable : rank_members_stableStatement := by
  intro env env' henv ms hcomplete
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      simp only [complete_members, Bool.and_eq_true] at hcomplete
      cases m with
      | Member_plain id t =>
          simp only [rank_members]
          rw [rank_type_stable env env' henv t hcomplete.1,
            ih hcomplete.2]
      | Member_bitfield id sz sg a width padding =>
          simp only [rank_members]
          exact ih hcomplete.2

theorem layout_field_stable : layout_field_stableStatement := by
  intro env env' henv pos m hcomplete
  cases m with
  | Member_plain id t =>
      simp only [layout_field, bitalignof]
      rw [alignof_stable env env' henv t hcomplete]
  | Member_bitfield id sz sg a width padding =>
      rfl

theorem field_offset_stable : field_offset_stableStatement := by
  intro env env' henv f ms hcomplete
  have aux : ∀ (xs : members) (pos : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z),
      complete_members env xs = true →
        field_offset_rec env' f xs pos = field_offset_rec env f xs pos := by
    intro xs
    induction xs with
    | nil =>
        intro pos hxs
        rfl
    | cons m ms ih =>
        intro pos hxs
        simp only [complete_members, Bool.and_eq_true] at hxs
        cases hident : CompCert4Lean.Common.AST.ident_eq f (name_member m) with
        | left hEq =>
            simp only [field_offset_rec, hident]
            exact layout_field_stable env env' henv pos m hxs.1
        | right hNe =>
            simp only [field_offset_rec, hident]
            rw [next_field_stable env env' henv pos m hxs.1]
            exact ih (next_field env pos m) hxs.2
  exact aux ms z0 hcomplete

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem union_field_offset_stable : union_field_offset_stableStatement := by
  intro env env' henv f ms hcomplete
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      simp only [complete_members, Bool.and_eq_true] at hcomplete
      cases hident : CompCert4Lean.Common.AST.ident_eq f (name_member m) with
      | left hEq =>
          simp only [union_field_offset, hident]
          exact layout_field_stable env env' henv z0 m hcomplete.1
      | right hNe =>
          simp only [union_field_offset, hident]
          exact ih hcomplete.2

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem add_composite_definitions_incr : add_composite_definitions_incrStatement := by
  unfold add_composite_definitions_incrStatement composite_env
  intro id co defs env1 env2 hadd hget
  induction defs generalizing env1 env2 with
  | nil =>
      simp only [add_composite_definitions] at hadd
      cases hadd
      exact hget
  | cons d defs ih =>
      cases d with
      | Composite did su ms a =>
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at did
          simp only [add_composite_definitions] at hadd
          cases hco : composite_of_def env1 did su ms a with
          | Error msg =>
              simp [hco] at hadd
          | OK co' =>
              simp only [hco] at hadd
              apply ih (env1 := CompCert4Lean.Lib.Maps.PTree.set did co' env1)
                (env2 := env2) hadd
              rw [CompCert4Lean.Lib.Maps.PTree.gsspec_proof]
              cases hpeq : CompCert4Lean.Lib.Coqlib.peq id did with
              | left heq =>
                  subst did
                  simp only [hget]
                  have hcontra : composite_of_def env1 id su ms a ≠ .OK co' := by
                    unfold composite_of_def
                    rw [hget]
                    simp
                  exact False.elim (hcontra hco)
              | right hne =>
                  exact hget

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem composite_consistent_stable : composite_consistent_stableStatement := by
  intro env env' henv co hco
  rcases hco with ⟨hcomplete, halignof, hsizeof, hrank⟩
  refine ⟨complete_members_stable env env' henv co.co_members hcomplete, ?_, ?_, ?_⟩
  · rw [halignof, alignof_composite_stable env env' henv _ hcomplete]
  · rw [hsizeof, sizeof_composite_stable env env' henv _ _ hcomplete]
  · rw [hrank, rank_members_stable env env' henv _ hcomplete]

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem composite_of_def_consistent : composite_of_def_consistentStatement := by
  intro env id su ms a co hco
  unfold composite_of_def at hco
  cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
  | some existing =>
      rw [hget] at hco
      cases hco
  | none =>
      cases hcomplete : complete_members env ms with
      | false =>
          rw [hget, hcomplete] at hco
          cases hco
      | true =>
          rw [hget, hcomplete] at hco
          cases hco
          exact ⟨by simpa using hcomplete, rfl, rfl, rfl⟩

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

private theorem build_composite_env_consistent_aux :
    ∀ (defs : List composite_definition) (env1 env2 : composite_env),
      add_composite_definitions env1 defs = .OK env2 →
      composite_env_consistent env1 →
      composite_env_consistent env2 := by
  intro defs
  induction defs with
  | nil =>
      intro env1 env2 hadd hbase
      simp only [add_composite_definitions] at hadd
      cases hadd
      exact hbase
  | cons d defs ih =>
      intro env1 env2 hadd hbase
      change CompCert4Lean.Lib.Maps.PTree.tree composite at env1 env2
      cases d with
      | Composite id su ms a =>
          cases hco : composite_of_def env1 id su ms a with
          | Error msg =>
              simp [add_composite_definitions, hco] at hadd
          | OK co =>
              have hrest :
                  add_composite_definitions (CompCert4Lean.Lib.Maps.PTree.set id co env1) defs =
                    .OK env2 := by
                simpa [add_composite_definitions, hco] using hadd
              have hco_cons : composite_consistent env1 co :=
                composite_of_def_consistent env1 id su ms a co hco
              have hnone : CompCert4Lean.Lib.Maps.PTree.get
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  env1 = none := by
                unfold composite_of_def at hco
                split at hco
                · rename_i hdup
                  cases hco
                · rename_i hnone
                  exact hnone
              have hincr : ∀ j cj, CompCert4Lean.Lib.Maps.PTree.get j env1 = some cj →
                  CompCert4Lean.Lib.Maps.PTree.get j
                    (CompCert4Lean.Lib.Maps.PTree.set id co env1) = some cj := by
                intro j cj hj
                have hs := CompCert4Lean.Lib.Maps.PTree.getSet_equation
                  (A := composite) j
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  co env1
                rw [hs]
                split
                · rename_i hEq
                  exfalso
                  cases hEq
                  have hbad : (none : Option composite) = some cj :=
                    hnone.symm.trans hj
                  cases hbad
                · exact hj
              have hset : composite_env_consistent
                  (CompCert4Lean.Lib.Maps.PTree.set id co env1) := by
                intro j cj hj
                have hspec := CompCert4Lean.Lib.Maps.PTree.getSet_equation
                  (A := composite)
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from j)
                  (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
                  co env1
                rw [hspec] at hj
                split at hj
                · rename_i hEq
                  cases hEq
                  cases hj
                  exact composite_consistent_stable env1
                    (CompCert4Lean.Lib.Maps.PTree.set id co env1) hincr co hco_cons
                · exact composite_consistent_stable env1
                    (CompCert4Lean.Lib.Maps.PTree.set id co env1) hincr cj (hbase j cj hj)
              exact ih (CompCert4Lean.Lib.Maps.PTree.set id co env1) env2 hrest hset

theorem build_composite_env_consistent : build_composite_env_consistentStatement := by
  unfold build_composite_env_consistentStatement build_composite_env
  intro defs env hadd
  have hempty : composite_env_consistent
      (show composite_env from CompCert4Lean.Lib.Maps.PTree.empty composite) := by
    intro id co hget
    change CompCert4Lean.Lib.Maps.PTree.get
      (show CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive from id)
      (CompCert4Lean.Lib.Maps.PTree.empty composite) = some co at hget
    simp only [CompCert4Lean.Lib.Maps.PTree.empty, CompCert4Lean.Lib.Maps.PTree.get] at hget
    cases hget
  exact build_composite_env_consistent_aux defs
    (show composite_env from CompCert4Lean.Lib.Maps.PTree.empty composite)
    env hadd hempty

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

private theorem build_composite_env_charact_aux :
    ∀ (defs : List composite_definition) (env0 env : composite_env),
      add_composite_definitions env0 defs = .OK env →
      ∀ (id : ident) (su : struct_or_union) (ms : members) (a : attr),
        Composite id su ms a ∈ defs →
        ∃ co, CompCert4Lean.Lib.Maps.PTree.get id env = some co ∧
          co.co_members = ms ∧ co.co_attr = a ∧ co.co_su = su := by
  intro defs
  induction defs with
  | nil =>
      intro env0 env hadd id su ms a hmem
      cases hmem
  | cons d defs ih =>
      intro env0 env hadd id su ms a hmem
      change CompCert4Lean.Lib.Maps.PTree.tree composite at env0 env
      cases d with
      | Composite did dsu dms da =>
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at did
          simp only [add_composite_definitions] at hadd
          cases hco : composite_of_def env0 did dsu dms da with
          | Error msg =>
              simp [hco] at hadd
          | OK co =>
              have hrest :
                  add_composite_definitions
                      (CompCert4Lean.Lib.Maps.PTree.set did co env0) defs =
                    .OK env := by
                simpa [hco] using hadd
              simp only [List.mem_cons] at hmem
              cases hmem with
              | inl hhead =>
                  have hset :
                      CompCert4Lean.Lib.Maps.PTree.get did
                          (CompCert4Lean.Lib.Maps.PTree.set did co env0) = some co := by
                    rw [CompCert4Lean.Lib.Maps.PTree.getSet_equation]
                    split
                    · rfl
                    · rename_i hne
                      exact (hne rfl).elim
                  have hfinal := add_composite_definitions_incr
                    did co defs
                    (CompCert4Lean.Lib.Maps.PTree.set did co env0) env hrest hset
                  have hfields : co.co_members = dms ∧ co.co_attr = da ∧ co.co_su = dsu := by
                    unfold composite_of_def at hco
                    cases hget : CompCert4Lean.Lib.Maps.PTree.get did env0 with
                    | some existing =>
                        rw [hget] at hco
                        cases hco
                    | none =>
                        cases hcomplete : complete_members env0 dms with
                        | false =>
                            rw [hget, hcomplete] at hco
                            cases hco
                        | true =>
                            rw [hget, hcomplete] at hco
                            cases hco
                            exact ⟨rfl, rfl, rfl⟩
                  cases hhead
                  exact ⟨co, hfinal, hfields.1, hfields.2.1, hfields.2.2⟩
              | inr htail =>
                  exact ih
                    (CompCert4Lean.Lib.Maps.PTree.set did co env0) env hrest id su ms a htail

theorem build_composite_env_charact : build_composite_env_charactStatement := by
  unfold build_composite_env_charactStatement build_composite_env
  intro id su ms a defs env hbuild hmem
  exact build_composite_env_charact_aux defs
    (CompCert4Lean.Lib.Maps.PTree.empty composite) env hbuild id su ms a hmem

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

private theorem add_composite_definitions_domain_aux :
    ∀ (defs : List composite_definition) (env0 env : composite_env)
      (id : ident) (co : composite),
      add_composite_definitions env0 defs = .OK env →
      CompCert4Lean.Lib.Maps.PTree.get id env = some co →
      CompCert4Lean.Lib.Maps.PTree.get id env0 = some co ∨
        Composite id co.co_su co.co_members co.co_attr ∈ defs := by
  intro defs
  induction defs with
  | nil =>
      intro env0 env id co hadd hget
      simp only [add_composite_definitions] at hadd
      cases hadd
      exact Or.inl hget
  | cons d defs ih =>
      intro env0 env id co hadd hget
      cases d with
      | Composite did su ms a =>
          simp only [add_composite_definitions] at hadd
          cases hco : composite_of_def env0 did su ms a with
          | Error msg =>
              simp [hco] at hadd
          | OK co' =>
              have hrest :
                  add_composite_definitions
                      (CompCert4Lean.Lib.Maps.PTree.set did co' env0) defs =
                    .OK env := by
                simpa [hco] using hadd
              have hfields :
                  co'.co_members = ms ∧ co'.co_attr = a ∧ co'.co_su = su := by
                unfold composite_of_def at hco
                cases hget0 : CompCert4Lean.Lib.Maps.PTree.get did env0 with
                | some existing =>
                    rw [hget0] at hco
                    cases hco
                | none =>
                    cases hcomplete : complete_members env0 ms with
                    | false =>
                        rw [hget0, hcomplete] at hco
                        cases hco
                    | true =>
                        rw [hget0, hcomplete] at hco
                        cases hco
                        exact ⟨rfl, rfl, rfl⟩
              have hstep := ih (CompCert4Lean.Lib.Maps.PTree.set did co' env0)
                env id co hrest hget
              cases hstep with
              | inr htail =>
                  exact Or.inr (by simp [htail])
              | inl hbase =>
                  have hset := CompCert4Lean.Lib.Maps.PTree.getSet_equation
                    (A := composite) id did co' env0
                  rw [hset] at hbase
                  split at hbase
                  · rename_i heq
                    cases hbase
                    subst id
                    exact Or.inr (by
                      simp only [List.mem_cons]
                      left
                      cases hfields.2.2
                      cases hfields.1
                      cases hfields.2.1
                      rfl)
                  · exact Or.inl hbase

theorem build_composite_env_domain : build_composite_env_domainStatement := by
  unfold build_composite_env_domainStatement build_composite_env
  intro env defs id co hbuild hget
  have hresult := add_composite_definitions_domain_aux defs
    (CompCert4Lean.Lib.Maps.PTree.empty composite) env id co hbuild hget
  cases hresult with
  | inl hempty =>
      change CompCert4Lean.Lib.Maps.PTree.get id
        (CompCert4Lean.Lib.Maps.PTree.empty composite) = some co at hempty
      simp only [CompCert4Lean.Lib.Maps.PTree.empty,
        CompCert4Lean.Lib.Maps.PTree.get] at hempty
      cases hempty
  | inr hdefs =>
      exact hdefs

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem link_composite_def_inv_proof : link_composite_def_invStatement := by
  unfold link_composite_def_invStatement
  intro l1 l2 l hlink
  unfold link_composite_defs at hlink
  cases hq : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb
      (check_compat_composite l2) l1 with
  | false =>
      simp [hq] at hlink
  | true =>
      have hcompat : ∀ cd1, cd1 ∈ l1 → check_compat_composite l2 cd1 = true :=
        (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb_forall
          (check_compat_composite l2) l1).mp hq
      have hinv : ∀ cd1 cd2, cd1 ∈ l1 → cd2 ∈ l2 →
          name_composite_def cd2 = name_composite_def cd1 → cd2 = cd1 := by
        intro cd1 cd2 hcd1 hcd2 hnames
        have hc := hcompat cd1 hcd1
        unfold check_compat_composite at hc
        have hc2 :=
          (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb_forall
            (fun cd' =>
              match CompCert4Lean.Common.AST.ident_eq
                (name_composite_def cd') (name_composite_def cd1) with
              | .left _ => boolOfSumbool (composite_def_eq cd1 cd')
              | .right _ => true) l2).mp hc cd2 hcd2
        cases hident : CompCert4Lean.Common.AST.ident_eq
            (name_composite_def cd2) (name_composite_def cd1) with
        | left heq =>
            have hc3 : boolOfSumbool (composite_def_eq cd1 cd2) = true := by
              simpa [hident] using hc2
            cases hdeq : composite_def_eq cd1 cd2 with
            | left hcd => exact hcd.symm
            | right hcd =>
                have : (false : Bool) = true := by
                  simpa [boolOfSumbool, hdeq] using hc3
                cases this
        | right hneq =>
            exact (hneq hnames).elim
      have hlist : l1 ++ filter_redefs l1 l2 = l := by
        simpa [hq] using hlink
      refine ⟨hinv, hlist.symm, ?_⟩
      intro x
      rw [← hlist]
      change CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In x
          (l1 ++ filter_redefs l1 l2) ↔ _
      rw [CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_app_iff]
      constructor
      · intro hx
        cases hx with
        | inl hx1 => exact Or.inl hx1
        | inr hxf =>
            dsimp [filter_redefs] at hxf
            rw [CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.filter_In] at hxf
            exact Or.inr hxf.1
      · intro hx
        cases hx with
        | inl hx1 => exact Or.inl hx1
        | inr hx2 =>
            by_cases hx1 : x ∈ l1
            · exact Or.inl hx1
            · right
              dsimp [filter_redefs]
              rw [CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.filter_In]
              constructor
              · exact hx2
              · cases hdec :
                  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                    CompCert4Lean.Common.AST.ident_eq
                    (name_composite_def x) (l1.map name_composite_def) with
                | right hnot => simp [hdec]
                | left hmem =>
                    rcases _root_.List.mem_map.mp hmem with ⟨y, hy, hname⟩
                    have hxy := hinv y x hy hx2 hname.symm
                    cases hxy
                    exact (hx1 hy).elim

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem add_composite_definitions_append : add_composite_definitions_appendStatement := by
  unfold add_composite_definitions_appendStatement
  intro l1 l2 env env''
  induction l1 generalizing env env'' with
  | nil =>
      simp only [List.nil_append, add_composite_definitions]
      constructor
      · intro h
        exact ⟨env, rfl, h⟩
      · rintro ⟨env', h1, h2⟩
        cases h1
        exact h2
  | cons d ds ih =>
      cases d with
      | Composite id su ms a =>
          simp only [List.cons_append, add_composite_definitions]
          cases hco : composite_of_def env id su ms a with
          | Error msg =>
              simp [hco]
          | OK co =>
              simp only [hco]
              exact ih (env := CompCert4Lean.Lib.Maps.PTree.set id co env)
                (env'' := env'')

theorem composite_eq : composite_eqStatement := by
  unfold composite_eqStatement
  intro su1 m1 a1 sz1 al1 r1 pos1 al2p1 szal1 su2 m2 a2 sz2 al2 r2 pos2 al2p2 szal2
    hsu hm ha hsz hal hr
  cases hsu
  cases hm
  cases ha
  cases hsz
  cases hal
  cases hr
  have hp : pos1 = pos2 := Subsingleton.elim _ _
  have hpow : al2p1 = al2p2 := Subsingleton.elim _ _
  have hdiv : szal1 = szal2 := Subsingleton.elim _ _
  cases hp
  cases hpow
  cases hdiv
  rfl

theorem composite_of_def_eq : composite_of_def_eqStatement := by
  unfold composite_of_def_eqStatement
  intro env id co hco hnone
  rcases hco with ⟨hcc, hca, hcs, hcr⟩
  unfold composite_of_def
  cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
  | some existing =>
      simp [hget] at hnone
  | none =>
      cases hcomplete : complete_members env co.co_members with
      | false =>
          have hbad : true = false := hcc.symm.trans hcomplete
          cases hbad
      | true =>
          simp only [hget, hcomplete]
          cases co with
          | mk su ms a sz al r hp hpow hdiv =>
              dsimp at hca hcs hcr ⊢
              have hal : align_attr a (alignof_composite env ms) = al := hca.symm
              have hsz : align (sizeof_composite env su ms)
                  (align_attr a (alignof_composite env ms)) = sz := by
                rw [hal]
                exact hcs.symm
              have hrank : rank_members env ms = r := hcr.symm
              cases hal
              cases hsz
              cases hrank
              congr

theorem composite_consistent_unique : composite_consistent_uniqueStatement := by
  unfold composite_consistent_uniqueStatement
  intro env co1 co2 h1 h2 hsu hm ha
  rcases co1 with ⟨su1, m1, a1, sz1, al1, r1, p1, pow1, div1⟩
  rcases co2 with ⟨su2, m2, a2, sz2, al2, r2, p2, pow2, div2⟩
  dsimp at h1 h2 hsu hm ha ⊢
  cases hsu
  cases hm
  cases ha
  rcases h1 with ⟨hc1, hal_1, hsz_1, hrk_1⟩
  rcases h2 with ⟨hc2, hal_2, hsz_2, hrk_2⟩
  have hal : al1 = al2 := by
    calc
      al1 = align_attr a1 (alignof_composite env m1) := hal_1
      _ = al2 := hal_2.symm
  have hsz : sz1 = sz2 := by
    calc
      sz1 = align (sizeof_composite env su1 m1) al1 := hsz_1
      _ = align (sizeof_composite env su1 m1) al2 := by rw [hal]
      _ = sz2 := hsz_2.symm
  have hrk : r1 = r2 := by
    exact hrk_1.trans hrk_2.symm
  cases hal
  cases hsz
  cases hrk
  congr

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

theorem composite_of_def_stable : composite_of_def_stableStatement := by
  unfold composite_of_def_stableStatement
  intro env env' henv id su m a co hnone hco
  have hco_cons : composite_consistent env co :=
    composite_of_def_consistent env id su m a co hco
  cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
  | some existing =>
      have hget' := henv id existing hget
      rw [hget'] at hnone
      cases hnone
  | none =>
      cases hcomplete : complete_members env m with
      | false =>
          unfold composite_of_def at hco
          rw [hget, hcomplete] at hco
          cases hco
      | true =>
          have hco' := hco
          unfold composite_of_def at hco'
          rw [hget, hcomplete] at hco'
          have hco_val :
              { co_su := su
                co_members := m
                co_attr := a
                co_sizeof := align (sizeof_composite env su m)
                  (align_attr a (alignof_composite env m))
                co_alignof := align_attr a (alignof_composite env m)
                co_rank := rank_members env m
                co_sizeof_pos := _
                co_alignof_two_p := _
                co_sizeof_alignof := _ } = co :=
            CompCert4Lean.Common.Errors.res.OK.inj hco'
          have hsu : co.co_su = su :=
            (congrArg (fun c : composite => c.co_su) hco_val).symm
          have hm : co.co_members = m :=
            (congrArg (fun c : composite => c.co_members) hco_val).symm
          have ha : co.co_attr = a :=
            (congrArg (fun c : composite => c.co_attr) hco_val).symm
          have hstable : composite_consistent env' co :=
            composite_consistent_stable env env' henv co hco_cons
          simpa only [hsu, hm, ha] using
            (composite_of_def_eq env' id co hstable hnone)

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

private theorem composite_of_def_fields :
    ∀ (env : composite_env) (id : ident) (su : struct_or_union)
      (ms : members) (a : attr) (co : composite),
      composite_of_def env id su ms a = .OK co →
      co.co_members = ms ∧ co.co_attr = a ∧ co.co_su = su := by
  intro env id su ms a co hco
  unfold composite_of_def at hco
  cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
  | some existing =>
      rw [hget] at hco
      cases hco
  | none =>
      cases hcomplete : complete_members env ms with
      | false =>
          rw [hget, hcomplete] at hco
          cases hco
      | true =>
          rw [hget, hcomplete] at hco
          cases hco
          exact ⟨rfl, rfl, rfl⟩

private theorem composite_of_def_none :
    ∀ (env : composite_env) (id : ident) (su : struct_or_union)
      (ms : members) (a : attr) (co : composite),
      composite_of_def env id su ms a = .OK co →
      CompCert4Lean.Lib.Maps.PTree.get id env = none := by
  intro env id su ms a co hco
  unfold composite_of_def at hco
  split at hco
  · rename_i hdup
    cases hco
  · rename_i hnone
    exact hnone

private theorem ptree_get_set_spec (i j : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (x : composite) (m : CompCert4Lean.Lib.Maps.PTree.tree composite) :
    CompCert4Lean.Lib.Maps.PTree.get i (CompCert4Lean.Lib.Maps.PTree.set j x m) =
      match CompCert4Lean.Lib.Coqlib.peq i j with
      | .left _ => some x
      | .right _ => CompCert4Lean.Lib.Maps.PTree.get i m :=
  CompCert4Lean.Lib.Maps.PTree.gsspec_proof i j x m

noncomputable def link_add_composite_definitions : link_add_composite_definitionsStatement := by
  unfold link_add_composite_definitionsStatement
  intro l0 env0 hbuild l
  induction l with
  | nil =>
      intro env1 env1' env2 hadd agree1 agree0 agree2 unique
      change CompCert4Lean.Lib.Maps.PTree.tree composite at env1 env1' env2
      simp only [add_composite_definitions] at hadd
      cases hadd
      refine ⟨env2, ?_, agree1, agree0⟩
      rfl
  | cons d ds ih =>
      intro env1 env1' env2 hadd agree1 agree0 agree2 unique
      cases d with
      | Composite id su ms a =>
          change CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive at id
          simp only [add_composite_definitions] at hadd
          cases hco : composite_of_def env1 id su ms a with
          | Error msg =>
              simp [hco] at hadd
          | OK co =>
              simp only [hco] at hadd
              have hnone1 :
                  CompCert4Lean.Lib.Maps.PTree.get id env1 = none :=
                composite_of_def_none env1 id su ms a co hco
              have hfields : co.co_members = ms ∧ co.co_attr = a ∧ co.co_su = su :=
                composite_of_def_fields env1 id su ms a co hco
              cases hdec : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                  CompCert4Lean.Common.AST.ident_eq id (l0.map name_composite_def) with
              | left hmem =>
                  have hmem0 : Composite id su ms a ∈ l0 := by
                    rcases _root_.List.mem_map.mp hmem with ⟨cd, hcd, hname⟩
                    have heq := unique cd (Composite id su ms a) hcd
                      (_root_.List.Mem.head ds) hname.symm
                    cases heq
                    exact hcd
                  have hchar := build_composite_env_charact id su ms a l0 env0
                    hbuild hmem0
                  let co0 := Classical.choose hchar
                  have hchar' := Classical.choose_spec hchar
                  have hget0 := hchar'.1
                  have hmembers0 := hchar'.2.1
                  have hattr0 := hchar'.2.2.1
                  have hsu0 := hchar'.2.2.2
                  have hcons0 : composite_consistent env0 co0 :=
                    build_composite_env_consistent l0 env0 hbuild id co0 hget0
                  have hcons0' : composite_consistent env2 co0 :=
                    composite_consistent_stable env0 env2 agree0 co0 hcons0
                  have hcons1 : composite_consistent env2 co :=
                    composite_consistent_stable env1 env2 agree1 co
                      (composite_of_def_consistent env1 id su ms a co hco)
                  have hcoeq : co0 = co :=
                    composite_consistent_unique env2 co0 co hcons0' hcons1
                      (hsu0.trans hfields.2.2.symm)
                      (hmembers0.trans hfields.1.symm)
                      (hattr0.trans hfields.2.1.symm)
                  have hset_agree1 :
                      ∀ j cj,
                        CompCert4Lean.Lib.Maps.PTree.get j
                            (CompCert4Lean.Lib.Maps.PTree.set id co env1) = some cj →
                          CompCert4Lean.Lib.Maps.PTree.get j env2 = some cj := by
                    intro j cj hj
                    have hs := ptree_get_set_spec j id co
                      (show CompCert4Lean.Lib.Maps.PTree.tree composite from env1)
                    rw [hs] at hj
                    cases hpeq : CompCert4Lean.Lib.Coqlib.peq j id with
                    | left heq =>
                        subst j
                        simp [hpeq] at hj
                        cases hj
                        simpa [hcoeq] using agree0 id co0 hget0
                    | right hne =>
                        apply agree1 j cj
                        simpa [hpeq] using hj
                  have hunique_tail :
                      ∀ cd1 cd2, cd1 ∈ l0 → cd2 ∈ ds →
                        name_composite_def cd2 = name_composite_def cd1 → cd2 = cd1 := by
                    intro cd1 cd2 hcd1 hcd2 hnames
                    exact unique cd1 cd2 hcd1 (_root_.List.Mem.tail _ hcd2) hnames
                  have hset_agree2 :
                      ∀ j,
                        CompCert4Lean.Lib.Maps.PTree.get j env2 =
                          match CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                              CompCert4Lean.Common.AST.ident_eq j (l0.map name_composite_def) with
                          | .left _ => CompCert4Lean.Lib.Maps.PTree.get j env0
                          | .right _ =>
                              CompCert4Lean.Lib.Maps.PTree.get j
                                (CompCert4Lean.Lib.Maps.PTree.set id co env1) := by
                    intro j
                    have hagree := agree2 j
                    cases hpeq : CompCert4Lean.Lib.Coqlib.peq j id with
                    | left heq =>
                        subst j
                        cases hdec' : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                            CompCert4Lean.Common.AST.ident_eq id (l0.map name_composite_def) with
                        | left h =>
                            simpa [hdec', hpeq] using hagree
                        | right h =>
                            exact (h hmem).elim
                    | right hne =>
                        cases hdec' : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                            CompCert4Lean.Common.AST.ident_eq j (l0.map name_composite_def) with
                        | left h =>
                            simpa [hdec', hpeq] using hagree
                        | right h =>
                            rw [ptree_get_set_spec j id co
                              (show CompCert4Lean.Lib.Maps.PTree.tree composite from env1)]
                            simpa [hdec', hpeq] using hagree
                  have hrec := ih (env1 := CompCert4Lean.Lib.Maps.PTree.set id co env1)
                    (env1' := env1') (env2 := env2) hadd hset_agree1 agree0 hset_agree2
                    hunique_tail
                  change CompCert4Lean.Common.AST.ident at id
                  have hfilter :
                      filter_redefs l0 (Composite id su ms a :: ds) =
                        filter_redefs l0 ds := by
                    unfold filter_redefs
                    dsimp
                    unfold CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.filter
                    rw [_root_.List.filter_cons]
                    cases hhead : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                        CompCert4Lean.Common.AST.ident_eq
                          (name_composite_def (Composite id su ms a))
                          (l0.map name_composite_def) with
                    | left hp => simp [hhead]
                    | right hp =>
                        have hmem' :
                            CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In id
                              (l0.map name_composite_def) := by
                          exact hmem
                        have :
                            CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In
                              (name_composite_def (Composite id su ms a))
                              (l0.map name_composite_def) := by
                          exact hmem'
                        exact (hp this).elim
                  rcases hrec with ⟨env2', hadd2, hagree1', hagree0'⟩
                  refine ⟨env2', ?_, hagree1', hagree0'⟩
                  rw [hfilter]
                  exact hadd2
              | right hmem =>
                  have hnone0 :
                      CompCert4Lean.Lib.Maps.PTree.get id env0 = none := by
                    cases h0 : CompCert4Lean.Lib.Maps.PTree.get id env0 with
                    | none => rfl
                    | some co0 =>
                        have hdom := build_composite_env_domain env0 l0 id co0 hbuild h0
                        exact (hmem (_root_.List.mem_map.mpr
                          ⟨Composite id co0.co_su co0.co_members co0.co_attr, hdom, rfl⟩)).elim
                  have hnone2 :
                      CompCert4Lean.Lib.Maps.PTree.get id env2 = none := by
                    rw [agree2 id]
                    cases hdec' : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                        CompCert4Lean.Common.AST.ident_eq id (l0.map name_composite_def) with
                    | left h => exact (hmem h).elim
                    | right h => simp [hdec', hnone1]
                  have hco2 : composite_of_def env2 id su ms a = .OK co :=
                    composite_of_def_stable env1 env2 agree1 id su ms a co hnone2 hco
                  have hset_agree1 :
                      ∀ j cj,
                        CompCert4Lean.Lib.Maps.PTree.get j
                            (CompCert4Lean.Lib.Maps.PTree.set id co env1) = some cj →
                          CompCert4Lean.Lib.Maps.PTree.get j
                            (CompCert4Lean.Lib.Maps.PTree.set id co env2) = some cj := by
                    intro j cj hj
                    have hs1 := ptree_get_set_spec j id co
                      (show CompCert4Lean.Lib.Maps.PTree.tree composite from env1)
                    have hs2 := ptree_get_set_spec j id co
                      (show CompCert4Lean.Lib.Maps.PTree.tree composite from env2)
                    rw [hs1] at hj
                    rw [hs2]
                    cases hpeq : CompCert4Lean.Lib.Coqlib.peq j id with
                    | left heq =>
                        subst j
                        simpa [hpeq] using hj
                    | right hne =>
                        apply agree1 j cj
                        simpa [hpeq] using hj
                  have hset_agree0 :
                      ∀ j cj, CompCert4Lean.Lib.Maps.PTree.get j env0 = some cj →
                        CompCert4Lean.Lib.Maps.PTree.get j
                            (CompCert4Lean.Lib.Maps.PTree.set id co env2) = some cj := by
                    intro j cj hj
                    have hs2 := ptree_get_set_spec j id co
                      (show CompCert4Lean.Lib.Maps.PTree.tree composite from env2)
                    rw [hs2]
                    cases hpeq : CompCert4Lean.Lib.Coqlib.peq j id with
                    | left heq =>
                        subst j
                        exact (by rw [hnone0] at hj; cases hj)
                    | right hne =>
                        simpa [hpeq] using agree0 j cj hj
                  have hset_agree2 :
                      ∀ j,
                        CompCert4Lean.Lib.Maps.PTree.get j
                            (CompCert4Lean.Lib.Maps.PTree.set id co env2) =
                          match CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                              CompCert4Lean.Common.AST.ident_eq j (l0.map name_composite_def) with
                          | .left _ => CompCert4Lean.Lib.Maps.PTree.get j env0
                          | .right _ =>
                              CompCert4Lean.Lib.Maps.PTree.get j
                                (CompCert4Lean.Lib.Maps.PTree.set id co env1) := by
                    intro j
                    have hs2 := ptree_get_set_spec j id co
                      (show CompCert4Lean.Lib.Maps.PTree.tree composite from env2)
                    rw [hs2]
                    cases hpeq : CompCert4Lean.Lib.Coqlib.peq j id with
                    | left heq =>
                        subst j
                        cases hdec' : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                            CompCert4Lean.Common.AST.ident_eq id (l0.map name_composite_def) with
                        | left h => exact (hmem h).elim
                        | right h =>
                            rw [ptree_get_set_spec id id co
                              (show CompCert4Lean.Lib.Maps.PTree.tree composite from env1)]
                            simp [hdec', hpeq, hnone1]
                    | right hne =>
                        have hs1 := ptree_get_set_spec j id co
                          (show CompCert4Lean.Lib.Maps.PTree.tree composite from env1)
                        cases hdec' : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                            CompCert4Lean.Common.AST.ident_eq j (l0.map name_composite_def) with
                        | left h =>
                            simpa [hdec', hpeq] using agree2 j
                        | right h =>
                            rw [hs1]
                            simpa [hdec', hpeq] using agree2 j
                  have hunique_tail :
                      ∀ cd1 cd2, cd1 ∈ l0 → cd2 ∈ ds →
                        name_composite_def cd2 = name_composite_def cd1 → cd2 = cd1 := by
                    intro cd1 cd2 hcd1 hcd2 hnames
                    exact unique cd1 cd2 hcd1 (_root_.List.Mem.tail _ hcd2) hnames
                  have hrec := ih (env1 := CompCert4Lean.Lib.Maps.PTree.set id co env1)
                    (env1' := env1') (env2 := CompCert4Lean.Lib.Maps.PTree.set id co env2)
                    hadd hset_agree1 hset_agree0 hset_agree2 hunique_tail
                  change CompCert4Lean.Common.AST.ident at id
                  have hfilter :
                      filter_redefs l0 (Composite id su ms a :: ds) =
                        Composite id su ms a :: filter_redefs l0 ds := by
                    unfold filter_redefs
                    dsimp
                    unfold CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.filter
                    rw [_root_.List.filter_cons]
                    cases hhead : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
                        CompCert4Lean.Common.AST.ident_eq
                          (name_composite_def (Composite id su ms a))
                          (l0.map name_composite_def) with
                    | left hp =>
                        have hp' :
                            CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In id
                              (l0.map name_composite_def) := by
                          simpa only [name_composite_def] using hp
                        exact (hmem hp').elim
                    | right hp => simp [hhead]
                  rcases hrec with ⟨env2', hadd2, hagree1', hagree0'⟩
                  refine ⟨env2', ?_, hagree1', hagree0'⟩
                  rw [hfilter]
                  simp only [add_composite_definitions, hco2]
                  exact hadd2

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

noncomputable def link_build_composite_env_proof : link_build_composite_envStatement := by
  unfold link_build_composite_envStatement
  intro l1 l2 l env1 env2 hbuild1 hbuild2 hlink
  have hinv := link_composite_def_inv_proof l1 l2 l hlink
  have hunique := hinv.1
  have hlist := hinv.2.1
  have hresult := link_add_composite_definitions
    (l0 := l1) (env0 := env1) hbuild1
    (l := l2) (env1 := CompCert4Lean.Lib.Maps.PTree.empty composite)
    (env1' := env2) (env2 := env1)
    (by simpa [build_composite_env] using hbuild2)
    (by
      intro id co hget
      simp only [CompCert4Lean.Lib.Maps.PTree.empty,
        CompCert4Lean.Lib.Maps.PTree.get] at hget
      cases hget)
    (by
      intro id co hget
      exact hget)
    (by
      intro id
      cases hdec : CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.in_dec
          CompCert4Lean.Common.AST.ident_eq id (l1.map name_composite_def) with
      | left hmem => simp [hdec]
      | right hmem =>
          cases hget : CompCert4Lean.Lib.Maps.PTree.get id env1 with
          | none =>
              simp only [CompCert4Lean.Lib.Maps.PTree.empty,
                CompCert4Lean.Lib.Maps.PTree.get]
          | some co =>
              have hdom := build_composite_env_domain env1 l1 id co hbuild1 hget
              have hmap :
                  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.In id
                    (l1.map name_composite_def) := by
                apply _root_.List.mem_map.mpr
                exact ⟨Composite id co.co_su co.co_members co.co_attr, hdom, rfl⟩
              exact (hmem hmap).elim)
    hunique
  rcases hresult with ⟨env, hadd, hsecond, hfirst⟩
  refine ⟨env, ?_, hfirst, hsecond⟩
  rw [hlist]
  unfold build_composite_env
  exact (add_composite_definitions_append l1 (filter_redefs l1 l2)
    (CompCert4Lean.Lib.Maps.PTree.empty composite) env).2
    ⟨env1, hbuild1, hadd⟩

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

open CompCert4Lean.Common
open CompCert4Lean.Common.Linking
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List

noncomputable def linker_program_certificate_proof : Linker_program_obligations := by
  let c : Linker_composite_defs_obligations := {
    link_composite_def_inv := link_composite_def_inv_proof
    link_build_composite_env := link_build_composite_env_proof
    link_linkorder := by
      intro l1 l2 l hlink
      have hi := link_composite_def_inv_proof l1 l2 l hlink
      rcases hi with ⟨_, hlist, hmem⟩
      constructor
      · intro x hx
        exact (hmem x).mpr (Or.inl hx)
      · intro x hx
        exact (hmem x).mpr (Or.inr hx)
  }
  exact { composite_defs := c, link_linkorder := (by
    intro F p1 p2 p h
    unfold link_program at h
    cases hbase : CompCert4Lean.Common.Linking.link
      (program_of_program p1) (program_of_program p2) with
    | none => simp [hbase] at h
    | some q =>
      cases htypes : lift_option (link_composite_defs p1.prog_types p2.prog_types) with
      | inright hn => simp [hbase, htypes] at h
      | inleft ht =>
        cases henv : c.link_build_composite_env
            p1.prog_types p2.prog_types ht.val
            p1.prog_comp_env p2.prog_comp_env
            p1.prog_comp_env_eq p2.prog_comp_env_eq ht.property with
        | mk env henvprop =>
          simp [hbase, htypes, henv] at h
          cases h
          unfold linkorder_program
          have hp := CompCert4Lean.Common.Linking.Linker_prog_link_linkorder_proof
            (fundef F) type (program_of_program p1) (program_of_program p2) q hbase
          refine ⟨?_, ?_⟩
          · constructor
            · simpa [program_of_program] using hp.1
            · simpa using henvprop.2.1
          · constructor
            · simpa [program_of_program] using hp.2
            · simpa using henvprop.2.2) }

end CompCert4Lean.Cfrontend.Ctypes

namespace CompCert4Lean.Cfrontend.Ctypes

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem compat_two_power_succ (n : Nat) :
    two_power_nat (n + 1) =
      ZArith.BinInt.Z.mul (zOfNat 2) (two_power_nat n) := by
  apply intOfZ_injective
  unfold two_power_nat ZArith.Zpower.two_power_nat
  simp only [ZArith.BinInt.Z.pow, ZArith.BinInt.Z.of_nat,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  have h2 : intOfZ (Zpos (.xO .xH)) = (2 : Int) := by decide
  rw [h2]
  have hnonneg_succ : ¬ (Int.ofNat (n + 1) < 0) :=
    Int.not_lt_of_ge (Int.ofNat_nonneg _)
  have hnonneg : ¬ (Int.ofNat n < 0) :=
    Int.not_lt_of_ge (Int.ofNat_nonneg _)
  simp only [if_neg hnonneg_succ, if_neg hnonneg, intOfZ_zOfInt]
  change (2 : Int) ^ n.succ = 2 * (2 : Int) ^ n
  rw [Int.pow_succ]
  simp [Int.mul_comm]

private theorem compat_divide_eight_two_power (n : Nat) (h : 3 ≤ n) :
    ZArith.BinInt.Z.divide (zOfNat 8) (two_power_nat n) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn : 3 ≤ n
      · rcases ih hn with ⟨k, hk⟩
        refine ⟨ZArith.BinInt.Z.mul (zOfNat 2) k, ?_⟩
        rw [compat_two_power_succ, hk]
        apply intOfZ_injective
        simp [zOfInt_intOfZ, intOfZ_zOfInt, ZArith.BinInt.Z.mul,
          ZArith.BinInt.Z.of_nat,
          Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      · have hn2 : n = 2 := by omega
        subst n
        refine ⟨zOfNat 1, ?_⟩
        decide

private theorem compat_min_align_divides (co : composite) :
    ZArith.BinInt.Z.divide
      (zMin (zOfNat 8) co.co_alignof) co.co_alignof := by
  rcases co.co_alignof_two_p with ⟨n, hn⟩
  rw [hn]
  by_cases hs : n < 4
  · have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      simp [zMin, ZArith.BinInt.Z.min] <;>
      exact ZArith.BinInt.Z.divide_refl _
  · rw [suffix_min_eight_two_power_nat n (by omega)]
    exact compat_divide_eight_two_power n (by omega)

private theorem compat_sizeof_alignof_blockcopy (env : composite_env) :
    ∀ t, ZArith.BinInt.Z.divide
      (alignof_blockcopy env t) (sizeof env t) := by
  intro t
  cases t with
  | Tvoid => exact ZArith.BinInt.Z.divide_refl _
  | Tint sz sg a => cases sz <;> exact ZArith.BinInt.Z.divide_refl _
  | Tlong sg a => exact ZArith.BinInt.Z.divide_refl _
  | Tfloat sz a => cases sz <;> exact ZArith.BinInt.Z.divide_refl _
  | Tpointer t a =>
      simp [alignof_blockcopy, sizeof,
        CompCert4Lean.X86_64.Archi.ptr64]
      exact ZArith.BinInt.Z.divide_refl _
  | Tarray t n a =>
      simpa [alignof_blockcopy, sizeof] using
        (ZArith.BinInt.Z.divide_mul_l _ _ _ (compat_sizeof_alignof_blockcopy env t))
  | Tfunction args res cc => exact ZArith.BinInt.Z.divide_refl _
  | Tstruct id a =>
      simp only [alignof_blockcopy, sizeof]
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => exact ZArith.BinInt.Z.divide_0_r _
      | some co =>
          exact ZArith.BinInt.Z.divide_trans _ _ _
            (compat_min_align_divides co) co.co_sizeof_alignof
  | Tunion id a =>
      simp only [alignof_blockcopy, sizeof]
      cases hget : CompCert4Lean.Lib.Maps.PTree.get id env with
      | none => exact ZArith.BinInt.Z.divide_0_r _
      | some co =>
          exact ZArith.BinInt.Z.divide_trans _ _ _
            (compat_min_align_divides co) co.co_sizeof_alignof

theorem sizeof_alignof_blockcopy_compat : sizeof_alignof_blockcopy_compatStatement := by
  exact compat_sizeof_alignof_blockcopy

end CompCert4Lean.Cfrontend.Ctypes
