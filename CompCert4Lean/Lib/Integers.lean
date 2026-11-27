import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Zbits
import CompCert4Lean.X86_64.Archi

/-!
# Fixed-width CompCert integers

This file provides the definition-translation surface selected from
`compcert.lib.Integers`.  Fixed-width values retain the source's proof-carrying
record carrier (`intval` together with `intrange`).  The executable bitvector
operations use the normalized natural-number view of that carrier.
-/

namespace CompCert4Lean.Lib.Integers

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private abbrev zZero : Z := Z0
private abbrev zOne : Z := Zpos xH
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zOpp := ZArith.BinInt.Z.opp
private abbrev zDiv := ZArith.BinInt.Z.div
private abbrev zMod := ZArith.BinInt.Z.modulo
private abbrev zQuot := ZArith.BinInt.Z.quot
private abbrev zShiftl := ZArith.BinInt.Z.shiftl
private abbrev zShiftr := ZArith.BinInt.Z.shiftr
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev zLtb := ZArith.BinInt.Z.ltb
private abbrev zDivide := ZArith.BinInt.Z.divide
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zToNat := ZArith.BinInt.Z.to_nat
private abbrev zTestbit := ZArith.BinInt.Z.testbit
private abbrev zTwoP := two_p
private abbrev zTwoPowerNat := two_power_nat

private def sumboolSelect {P Q : Prop} {A : Type}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q)
    (ifso ifnot : A) : A :=
  match d with
  | .left _ => ifso
  | .right _ => ifnot

private abbrev zltSelect (x y : Z) {A : Type} (ifso ifnot : A) : A :=
  sumboolSelect (CompCert4Lean.Lib.Coqlib.zlt x y) ifso ifnot

inductive comparison : Type where
  | Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge
deriving DecidableEq

export comparison (Ceq Cne Clt Cle Cgt Cge)

def negate_comparison : comparison → comparison
  | .Ceq => .Cne
  | .Cne => .Ceq
  | .Clt => .Cge
  | .Cle => .Cgt
  | .Cgt => .Cle
  | .Cge => .Clt

def swap_comparison : comparison → comparison
  | .Ceq => .Ceq
  | .Cne => .Cne
  | .Clt => .Cgt
  | .Cle => .Cge
  | .Cgt => .Clt
  | .Cge => .Cle

namespace WordCore

private theorem twoPowerNat_eq_zOfNat_twoPow (bits : Nat) :
    zTwoPowerNat bits = zOfNat (2 ^ bits) := by
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
      (Zpos (.xO .xH))
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat bits) =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat (2 ^ bits)
  unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
  rw [show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat bits =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat bits) by rfl]
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hnonneg : ¬Int.ofNat bits < 0 :=
    Int.not_lt.mpr (Int.natCast_nonneg bits)
  rw [if_neg hnonneg]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    show CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat
        (2 ^ bits) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (2 ^ bits)) by rfl,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change (2 : Int) ^ bits = Int.ofNat (2 ^ bits)
  exact (Int.natCast_pow 2 bits).symm

structure Word (bits : Nat) where
  mkint ::
  intval : Z
  intrange : zLt (zOpp zOne) intval ∧ zLt intval (zTwoPowerNat bits)
deriving DecidableEq

theorem ext {bits : Nat} {x y : Word bits} (h : x.intval = y.intval) : x = y := by
  cases x with
  | mkint xv xh =>
    cases y with
    | mkint yv yh =>
      cases h
      rfl

private def positiveToNat : positive → Nat
  | .xH => 1
  | .xI p => 2 * positiveToNat p + 1
  | .xO p => 2 * positiveToNat p

private theorem positiveToNat_eq_posToNat (p : positive) :
    positiveToNat p = CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
  induction p with
  | xH => rfl
  | xI p ih => simp [positiveToNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, ih]
  | xO p ih => simp [positiveToNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, ih]

@[simp] private theorem zToNat_zOfNat (n : Nat) : zToNat (zOfNat n) = n := by
  exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id n

def Word.val {bits : Nat} (x : Word bits) : Nat := zToNat x.intval

private abbrev natVal {bits : Nat} (x : Word bits) : Nat := Word.val x

private theorem intval_eq_zOfNat_val {bits : Nat} (x : Word bits) :
    x.intval = zOfNat x.val := by
  have hx : zLe zZero x.intval := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  exact (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id
    x.intval hx).symm

theorem ext_of_val_eq {bits : Nat} {x y : Word bits} (h : x.val = y.val) : x = y := by
  apply ext
  rw [intval_eq_zOfNat_val x, intval_eq_zOfNat_val y, h]

private theorem val_lt {bits : Nat} (x : Word bits) : x.val < 2 ^ bits := by
  have h := x.intrange.2
  rw [twoPowerNat_eq_zOfNat_twoPow] at h
  rw [intval_eq_zOfNat_val x] at h
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat x.val)) <
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (2 ^ bits))) at h
  rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at h
  exact Int.ofNat_lt.mp h

/-- Computational finite residue view used at the bitvector boundary. -/
def Word.toFin {bits : Nat} (x : Word bits) : Fin (2 ^ bits) :=
  ⟨x.val, val_lt x⟩

private def residue (bits : Nat) : Z → Nat
  | .Z0 => 0
  | .Zpos p => positiveToNat p % (2 ^ bits)
  | .Zneg p =>
      let modulus := 2 ^ bits
      let r := positiveToNat p % modulus
      if r = 0 then 0 else modulus - r

private theorem residue_range (bits : Nat) (x : Z) :
    residue bits x < 2 ^ bits := by
  cases x with
  | Z0 => exact Nat.two_pow_pos bits
  | Zpos p => exact Nat.mod_lt _ (Nat.two_pow_pos bits)
  | Zneg p =>
      dsimp [residue]
      split <;> omega

private theorem repr_intrange (bits : Nat) (x : Z) :
    zLt (zOpp zOne) (zOfNat (residue bits x)) ∧
      zLt (zOfNat (residue bits x)) (zTwoPowerNat bits) := by
  have hr := residue_range bits x
  constructor
  · have hnonneg : (0 : Int) ≤ Int.ofNat (residue bits x) :=
      Int.natCast_nonneg _
    have h : (-1 : Int) < Int.ofNat (residue bits x) := by omega
    have hneg : zOpp zOne = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-1) := by rfl
    have hn : zOfNat (residue bits x) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (residue bits x)) := by rfl
    rw [hneg, hn]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-1)) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (residue bits x)))
    simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using h
  · have h : Int.ofNat (residue bits x) < Int.ofNat (2 ^ bits) :=
      Int.ofNat_lt.mpr hr
    have hn : zOfNat (residue bits x) =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (residue bits x)) := by rfl
    have hm : zTwoPowerNat bits =
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (2 ^ bits)) := by
      rw [twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hn, hm]
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (Int.ofNat (residue bits x))) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat (2 ^ bits)))
    simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using h

private theorem residue_zOfNat (bits n : Nat) :
    residue bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat n)) =
      n % (2 ^ bits) := by
  cases n with
  | zero => rfl
  | succ n =>
      simp [residue, CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt,
        positiveToNat_eq_posToNat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
          (n := n + 1) (Nat.succ_pos n)]

private theorem nat_sub_of_eq_sub {m r t : Nat} (h : r = m - t) (ht : t < m) :
    m - r = t := by
  omega

private theorem residue_zOfInt (bits : Nat) (i : Int) :
    residue bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i) =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  cases i with
  | ofNat n =>
    rw [residue_zOfNat]
    simpa using
      (Int.emod_natAbs_of_nonneg (x := Int.ofNat n) (n := 2 ^ bits)
        (Int.natCast_nonneg n))
  | negSucc n =>
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt, residue,
        positiveToNat_eq_posToNat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
          (n := n + 1) (Nat.succ_pos n)]
    have hm : 2 ^ bits ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos bits)
    have hneg : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    have hbridge :=
      Int.emod_natAbs_of_neg (x := Int.negSucc n) hneg (n := 2 ^ bits) hm
    by_cases hdvd : ((2 ^ bits : Nat) : Int) ∣ Int.negSucc n
    · rw [if_pos hdvd] at hbridge
      have hz : Int.negSucc n % ((2 ^ bits : Nat) : Int) = 0 :=
        Int.emod_eq_zero_of_dvd hdvd
      have hrem : (n + 1) % (2 ^ bits) = 0 := by
        simpa only [Int.natAbs_negSucc] using hbridge
      rw [if_pos hrem, hz]
      rfl
    · rw [if_neg hdvd] at hbridge
      simp only [Int.natAbs_negSucc] at hbridge
      have hmpos : (0 : Int) < Int.ofNat (2 ^ bits) :=
        by simpa only [Int.ofNat_eq_natCast] using
          Int.natCast_pos.mpr (Nat.two_pow_pos bits)
      have hmodlt :
          Int.negSucc n % ((2 ^ bits : Nat) : Int) < ((2 ^ bits : Nat) : Int) :=
        Int.emod_lt_of_pos _ (by simpa only [Int.ofNat_eq_natCast] using hmpos)
      have hmodnonneg : 0 ≤ Int.negSucc n % ((2 ^ bits : Nat) : Int) :=
        Int.emod_nonneg _ (Int.ne_of_gt (by simpa only [Int.ofNat_eq_natCast] using hmpos))
      have hmodnatlt :
          Int.toNat (Int.negSucc n % ((2 ^ bits : Nat) : Int)) < 2 ^ bits :=
        (Int.toNat_lt hmodnonneg).mpr hmodlt
      have hrem : (n + 1) % (2 ^ bits) ≠ 0 := by
        intro hzero
        rw [hzero] at hbridge
        omega
      rw [if_neg hrem]
      exact nat_sub_of_eq_sub hbridge hmodnatlt

def repr (bits : Nat) (x : Z) : Word bits :=
  Word.mkint (zOfNat (residue bits x)) (repr_intrange bits x)

/-- Re-embed a finite residue into the source-shaped proof-carrying carrier. -/
def Word.ofFin {bits : Nat} (x : Fin (2 ^ bits)) : Word bits :=
  repr bits (zOfNat x.val)

@[simp] private theorem val_repr_residue (bits : Nat) (x : Z) :
    (repr bits x).val = residue bits x := by
  exact zToNat_zOfNat (residue bits x)

def unsigned {bits : Nat} (x : Word bits) : Z :=
  x.intval

private theorem val_repr (bits : Nat) (i : Int) :
    (repr bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := by
  rw [val_repr_residue, residue_zOfInt]

def signed {bits : Nat} (x : Word bits) : Z :=
  let modulus := zTwoPowerNat bits
  let half := zTwoPowerNat (bits - 1)
  let u := unsigned x
  zltSelect u half u (zSub u modulus)

def zero (bits : Nat) : Word bits := repr bits zZero
def one (bits : Nat) : Word bits := repr bits zOne
def mone (bits : Nat) : Word bits := repr bits (zOpp zOne)
def iwordsize (bits : Nat) : Word bits := repr bits (zOfNat bits)

def eq {bits : Nat} (x y : Word bits) : Bool := decide (x.intval = y.intval)
def lt {bits : Nat} (x y : Word bits) : Bool :=
  zltSelect (signed x) (signed y) true false
def ltu {bits : Nat} (x y : Word bits) : Bool :=
  zltSelect (unsigned x) (unsigned y) true false

def neg {bits : Nat} (x : Word bits) : Word bits :=
  repr bits (zOpp (unsigned x))
def add {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zAdd (unsigned x) (unsigned y))

private theorem add_val {bits : Nat} (x y : Word bits) :
    (add x y).val = (x.val + y.val) % (2 ^ bits) := by
  rw [add, val_repr_residue]
  simp only [unsigned]
  rw [intval_eq_zOfNat_val x, intval_eq_zOfNat_val y]
  simp only [zAdd, zOfNat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have hadd :
      Int.ofNat x.val + Int.ofNat y.val = Int.ofNat (x.val + y.val) := by
    rfl
  rw [hadd]
  rw [residue_zOfNat]

private theorem add_val_int {bits : Nat} (x y : Word bits) :
    Int.ofNat (add x y).val =
      (Int.ofNat x.val + Int.ofNat y.val) % Int.ofNat (2 ^ bits) := by
  rw [add_val]
  simp only [Int.ofNat_eq_natCast, Int.natCast_emod, Int.natCast_add]

def sub {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zSub (unsigned x) (unsigned y))

private theorem sub_val {bits : Nat} (x y : Word bits) :
    (sub x y).val = (2 ^ bits - y.val + x.val) % (2 ^ bits) := by
  rw [sub, val_repr_residue]
  simp only [unsigned]
  rw [intval_eq_zOfNat_val x, intval_eq_zOfNat_val y]
  simp only [zSub, zOfNat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [residue_zOfInt]
  have hmpos : (0 : Int) < ((2 ^ bits : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.two_pow_pos bits)
  have hnonneg :
      0 ≤ ((x.val : Int) - (y.val : Int)) % ((2 ^ bits : Nat) : Int) :=
    Int.emod_nonneg _ (Int.ne_of_gt hmpos)
  have hlt :
      ((x.val : Int) - (y.val : Int)) % ((2 ^ bits : Nat) : Int) <
        ((2 ^ bits : Nat) : Int) :=
    Int.emod_lt_of_pos _ hmpos
  apply Int.ofNat.inj
  simp only [Int.ofNat_eq_natCast]
  rw [Int.toNat_of_nonneg hnonneg, Int.natCast_emod]
  have hinside :
      (((2 ^ bits - y.val + x.val : Nat) : Int)) =
        ((x.val : Int) - (y.val : Int)) + ((2 ^ bits : Nat) : Int) := by
    rw [Int.natCast_add, Int.ofNat_sub (Nat.le_of_lt (val_lt y))]
    omega
  rw [hinside, Int.add_emod_right]

private theorem sub_val_int {bits : Nat} (x y : Word bits) :
    Int.ofNat (sub x y).val =
      (Int.ofNat x.val - Int.ofNat y.val) % Int.ofNat (2 ^ bits) := by
  rw [sub, val_repr_residue]
  simp only [unsigned]
  rw [intval_eq_zOfNat_val x, intval_eq_zOfNat_val y]
  simp only [zSub, zOfNat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  rw [residue_zOfInt]
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (Int.ne_of_gt (Int.natCast_pos.mpr (Nat.two_pow_pos bits)))

def mul {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zMul (unsigned x) (unsigned y))
def divs {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zQuot (signed x) (signed y))
def mods {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zSub (signed x) (zMul (zQuot (signed x) (signed y)) (signed y)))
def divu {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zDiv (unsigned x) (unsigned y))
def modu {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zMod (unsigned x) (unsigned y))

def negative {bits : Nat} (x : Word bits) : Word bits :=
  if lt x (zero bits) then one bits else zero bits

def add_carry {bits : Nat} (x y cin : Word bits) : Word bits :=
  let sum := zAdd (zAdd (unsigned x) (unsigned y)) (unsigned cin)
  zltSelect sum (zTwoPowerNat bits) (zero bits) (one bits)

def sub_overflow {bits : Nat} (x y bin : Word bits) : Word bits :=
  let difference := zSub (zSub (signed x) (signed y)) (signed bin)
  let halfModulus := zTwoPowerNat (bits - 1)
  let minSigned := zOpp halfModulus
  let maxSigned := zSub halfModulus zOne
  zltSelect difference minSigned (one bits)
    (zltSelect maxSigned difference (one bits) (zero bits))

def and {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zOfNat (Nat.land (natVal x) (natVal y)))
def or {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zOfNat (Nat.lor (natVal x) (natVal y)))
def xor {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zOfNat (Nat.xor (natVal x) (natVal y)))
def not {bits : Nat} (x : Word bits) : Word bits :=
  repr bits (zOfNat (Nat.xor (natVal x) (2 ^ bits - 1)))

def shl {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftl (unsigned x) (unsigned y))
def shru {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftr (unsigned x) (unsigned y))
def shr {bits : Nat} (x y : Word bits) : Word bits :=
  repr bits (zShiftr (signed x) (unsigned y))

def rol {bits : Nat} (x y : Word bits) : Word bits :=
  let amount := if bits = 0 then 0 else natVal y % bits
  repr bits (zOfNat
    (Nat.lor (Nat.shiftLeft (natVal x) amount)
      (Nat.shiftRight (natVal x) (bits - amount))))

def ror {bits : Nat} (x y : Word bits) : Word bits :=
  let amount := if bits = 0 then 0 else natVal y % bits
  repr bits (zOfNat
    (Nat.lor (Nat.shiftRight (natVal x) amount)
      (Nat.shiftLeft (natVal x) (bits - amount))))

def shrx {bits : Nat} (x y : Word bits) : Word bits :=
  divs x (shl (one bits) y)

def zero_ext {bits : Nat} (n : Z) (x : Word bits) : Word bits :=
  repr bits (CompCert4Lean.Lib.Zbits.Zzero_ext n (unsigned x))

def sign_ext {bits : Nat} (n : Z) (x : Word bits) : Word bits :=
  let step : (Z → Z) → (Z → Z) :=
    fun rec y =>
      CompCert4Lean.Lib.Zbits.Zshiftin
        (ZArith.BinInt.Z.odd y)
        (rec (ZArith.BinInt.Z.div2 y))
  let base : Z → Z :=
    fun y =>
      if ZArith.BinInt.Z.odd y then
        sumboolSelect (CompCert4Lean.Lib.Coqlib.zlt zZero n) (zOpp zOne) zZero
      else
        zZero
  repr bits
    (ZArith.BinInt.Z.iter (ZArith.BinInt.Z.pred n) step base (unsigned x))

def testbit {bits : Nat} (x : Word bits) : Z → Bool
  | .Zneg _ => false
  | .Z0 => Nat.testBit (natVal x) 0
  | .Zpos p => Nat.testBit (natVal x) (positiveToNat p)

def eqm (bits : Nat) (x y : Z) : Prop :=
  CompCert4Lean.Lib.Zbits.eqmod (zTwoPowerNat bits) x y

def cmp {bits : Nat} (c : comparison) (x y : Word bits) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !(eq x y)
  | .Clt => lt x y
  | .Cle => !(lt y x)
  | .Cgt => lt y x
  | .Cge => !(lt x y)

def cmpu {bits : Nat} (c : comparison) (x y : Word bits) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !(eq x y)
  | .Clt => ltu x y
  | .Cle => !(ltu y x)
  | .Cgt => ltu y x
  | .Cge => !(ltu x y)

def unsigned_bitfield_extract {bits : Nat} (pos width : Z) (n : Word bits) : Word bits :=
  zero_ext width (shru n (repr bits pos))

def signed_bitfield_extract {bits : Nat} (pos width : Z) (n : Word bits) : Word bits :=
  sign_ext width (shru n (repr bits pos))

def bitfield_insert {bits : Nat} (pos width : Z) (n p : Word bits) : Word bits :=
  let mask := shl (repr bits (zSub (zTwoP width) zOne)) (repr bits pos)
  or (shl (zero_ext width p) (repr bits pos)) (and n (not mask))

/--
The concrete member correspondence for a source application of `Make`.
Its dependent carrier fields retain the generated constructor, projections,
and exact `intrange` proposition; the remaining fields identify the selected
executable surface shared by the four owned applications.
-/
structure GeneratedApplication where
  wordsize : Nat
  modulus : Z
  int : Type
  mkint : (intval : Z) →
    zLt (zOpp zOne) intval ∧ zLt intval (zTwoPowerNat wordsize) → int
  intval : int → Z
  intrange : ∀ x : int,
    zLt (zOpp zOne) (intval x) ∧ zLt (intval x) (zTwoPowerNat wordsize)
  repr : Z → int
  unsigned : int → Z
  signed : int → Z
  size : int → Z
  zero : int
  one : int
  eq : int → int → Bool
  lt : int → int → Bool
  ltu : int → int → Bool
  neg : int → int
  add : int → int → int
  sub : int → int → int
  mul : int → int → int
  divs : int → int → int
  mods : int → int → int
  divu : int → int → int
  modu : int → int → int
  cmp : comparison → int → int → Bool
  cmpu : comparison → int → int → Bool
  and : int → int → int
  or : int → int → int
  xor : int → int → int
  shl : int → int → int
  shru : int → int → int
  shr : int → int → int
  zero_ext : Z → int → int
  sign_ext : Z → int → int
  unsigned_bitfield_extract : Z → Z → int → int
  signed_bitfield_extract : Z → Z → int → int
  bitfield_insert : Z → Z → int → int → int

def makeGeneratedApplication (bits : Nat) : GeneratedApplication where
  wordsize := bits
  modulus := zTwoPowerNat bits
  int := Word bits
  mkint := fun intval intrange => Word.mkint intval intrange
  intval := Word.intval
  intrange := Word.intrange
  repr := repr bits
  unsigned := unsigned
  signed := signed
  size := fun x => CompCert4Lean.Lib.Zbits.Zsize (unsigned x)
  zero := zero bits
  one := one bits
  eq := eq
  lt := lt
  ltu := ltu
  neg := neg
  add := add
  sub := sub
  mul := mul
  divs := divs
  mods := mods
  divu := divu
  modu := modu
  cmp := cmp
  cmpu := cmpu
  and := and
  or := or
  xor := xor
  shl := shl
  shru := shru
  shr := shr
  zero_ext := zero_ext
  sign_ext := sign_ext
  unsigned_bitfield_extract := unsigned_bitfield_extract
  signed_bitfield_extract := signed_bitfield_extract
  bitfield_insert := bitfield_insert

/-! ## Residue view

Public statements of the residue lemmas above, for clients that reason about
words through `Nat`, `Int` or `BitVec`. -/

theorem val_lt_two_pow {bits : Nat} (x : Word bits) : x.val < 2 ^ bits := val_lt x

theorem intval_eq_of_nat_val {bits : Nat} (x : Word bits) :
    x.intval = ZArith.BinInt.Z.of_nat x.val := intval_eq_zOfNat_val x

theorem zToNat_of_nat (n : Nat) : zToNat (ZArith.BinInt.Z.of_nat n) = n := zToNat_zOfNat n

theorem val_repr_of_nat (bits n : Nat) :
    (repr bits (ZArith.BinInt.Z.of_nat n)).val = n % 2 ^ bits := by
  rw [val_repr_residue]
  exact residue_zOfNat bits n

theorem val_repr_of_int (bits : Nat) (i : Int) :
    (repr bits (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt i)).val =
      Int.toNat (i % ((2 ^ bits : Nat) : Int)) := val_repr bits i

theorem val_add {bits : Nat} (x y : Word bits) :
    (add x y).val = (x.val + y.val) % (2 ^ bits) := add_val x y

/-- The comparison underlying `lt`, `ltu`, `signed` and the carry operations. -/
theorem zltSelect_eq {A : Type} (x y : Z) (a b : A) :
    zltSelect x y a b =
      if CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y then a else b := by
  unfold zltSelect sumboolSelect
  split
  · rename_i h _
    have h' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x <
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y := h
    simp [h']
  · rename_i h _
    have h' : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y ≤
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x := h
    simp [Int.not_lt.mpr h']

end WordCore

namespace Int

def wordsize : Nat := 32
def zwordsize : Z := zOfNat wordsize
def modulus : Z := zTwoPowerNat wordsize
def half_modulus : Z := zTwoPowerNat (wordsize - 1)
def max_unsigned : Z := zSub modulus zOne
def max_signed : Z := zSub half_modulus zOne
def min_signed : Z := zOpp half_modulus

abbrev int := WordCore.Word wordsize

def repr (x : Z) : int := WordCore.repr wordsize x
def ofFin (x : Fin (2 ^ wordsize)) : int := WordCore.Word.ofFin x
def toFin (x : int) : Fin (2 ^ wordsize) := x.toFin
def unsigned (x : int) : Z := WordCore.unsigned x
def signed (x : int) : Z := WordCore.signed x
def size (x : int) : Z := CompCert4Lean.Lib.Zbits.Zsize (unsigned x)
def zero : int := WordCore.zero wordsize
def one : int := WordCore.one wordsize
def mone : int := WordCore.mone wordsize
def iwordsize : int := WordCore.iwordsize wordsize
def eq : int → int → Bool := WordCore.eq
def eq_dec (x y : int) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  if h : x = y then .left h else .right h
def lt : int → int → Bool := WordCore.lt
def ltu : int → int → Bool := WordCore.ltu
def neg : int → int := WordCore.neg
def add : int → int → int := WordCore.add
def sub : int → int → int := WordCore.sub
def mul : int → int → int := WordCore.mul
def mulhs (x y : int) : int :=
  repr (zDiv (zMul (signed x) (signed y)) modulus)
def mulhu (x y : int) : int :=
  repr (zDiv (zMul (unsigned x) (unsigned y)) modulus)
def divs : int → int → int := WordCore.divs
def mods : int → int → int := WordCore.mods
def divu : int → int → int := WordCore.divu
def modu : int → int → int := WordCore.modu
def negative : int → int := WordCore.negative
def add_carry : int → int → int → int := WordCore.add_carry
def sub_overflow : int → int → int → int := WordCore.sub_overflow
def and : int → int → int := WordCore.and
def or : int → int → int := WordCore.or
def xor : int → int → int := WordCore.xor
def not : int → int := WordCore.not
def shl : int → int → int := WordCore.shl
def shru : int → int → int := WordCore.shru
def shr : int → int → int := WordCore.shr
def sign_ext (n : Z) (x : int) : int := WordCore.sign_ext n x
def zero_ext (n : Z) (x : int) : int :=
  WordCore.zero_ext n x
def rol : int → int → int := WordCore.rol
def ror : int → int → int := WordCore.ror
def shrx : int → int → int := WordCore.shrx
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

def is_power2 (x : int) : Option int :=
  match CompCert4Lean.Lib.Zbits.Z_is_power2 (unsigned x) with
  | some i => some (repr i)
  | none => none

def one_bits (x : int) : List int :=
  List.map repr
    (CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned x) zZero)

def cmp : comparison → int → int → Bool := WordCore.cmp
def cmpu : comparison → int → int → Bool := WordCore.cmpu

def divmodu2 (nhi nlo d : int) : Option (int × int) :=
  match eq_dec d zero with
  | .left _ => none
  | .right _ =>
      let qr := ZArith.BinInt.Z.div_eucl
        (zAdd (zMul (unsigned nhi) modulus) (unsigned nlo)) (unsigned d)
      match CompCert4Lean.Lib.Coqlib.zle qr.1 max_unsigned with
      | .left _ => some (repr qr.1, repr qr.2)
      | .right _ => none

def divmods2 (nhi nlo d : int) : Option (int × int) :=
  match eq_dec d zero with
  | .left _ => none
  | .right _ =>
      let n := zAdd (zMul (signed nhi) modulus) (unsigned nlo)
      let sd := signed d
      let q := zQuot n sd
      let r := zSub n (zMul q sd)
      match CompCert4Lean.Lib.Coqlib.zle min_signed q,
          CompCert4Lean.Lib.Coqlib.zle q max_signed with
      | .left _, .left _ => some (repr q, repr r)
      | _, _ => none

def unsigned_bitfield_extract (pos width : Z) (n : int) : int :=
  WordCore.unsigned_bitfield_extract pos width n

def signed_bitfield_extract (pos width : Z) (n : int) : int :=
  WordCore.signed_bitfield_extract pos width n

def bitfield_insert (pos width : Z) (n p : int) : int :=
  WordCore.bitfield_insert pos width n p

/-! Selected generated members of `Make(Wordsize_32)` retain their exact
    source propositions here; proof discharge remains a later phase. -/
def add_unsigned : Prop :=
  ∀ x y : int, add x y = repr (zAdd (unsigned x) (unsigned y))

def bits_above : Prop :=
  ∀ (x : int) (i : Z), zLe zwordsize i → testbit x i = false

def bits_and : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (and x y) i = (testbit x i && testbit y i)

def bits_or : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (or x y) i = (testbit x i || testbit y i)

def bits_shl : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shl x y) i =
      zltSelect i (unsigned y) false (testbit x (zSub i (unsigned y)))

def bits_shr : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shr x y) i =
      testbit x (zltSelect (zAdd i (unsigned y)) zwordsize
        (zAdd i (unsigned y)) (zSub zwordsize zOne))

def bits_shru : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shru x y) i =
      zltSelect (zAdd i (unsigned y)) zwordsize
        (testbit x (zAdd i (unsigned y))) false

def bits_xor : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (xor x y) i = Bool.xor (testbit x i) (testbit y i)

def bits_zero : Prop := ∀ i : Z, testbit zero i = false

def eq_signed : Prop :=
  ∀ x y : int,
    eq x y = sumboolSelect (CompCert4Lean.Lib.Coqlib.zeq (signed x) (signed y))
      true false

def eq_sym : Prop := ∀ x y : int, eq x y = eq y x

def eqm_add : Prop :=
  ∀ a b c d : Z, eqm a b → eqm c d → eqm (zAdd a c) (zAdd b d)

def eqm_refl : Prop := ∀ x : Z, eqm x x

def eqm_signed_unsigned : Prop :=
  ∀ x : int, eqm (signed x) (unsigned x)

def eqm_sym : Prop := ∀ x y : Z, eqm x y → eqm y x

def eqm_unsigned_repr : Prop :=
  ∀ z : Z, eqm z (unsigned (repr z))

def eqm_unsigned_repr_l : Prop :=
  ∀ a b : Z, eqm a b → eqm (unsigned (repr a)) b

def ltu_inv : Prop :=
  ∀ x y : int, ltu x y = true →
    zLe zZero (unsigned x) ∧ zLt (unsigned x) (unsigned y)

def modulus_pos : Prop := zLt zZero modulus

def repr_unsigned : Prop := ∀ i : int, repr (unsigned i) = i

def same_bits_eq : Prop :=
  ∀ x y : int,
    (∀ i : Z, zLe zZero i ∧ zLt i zwordsize → testbit x i = testbit y i) →
      x = y

def signed_range : Prop :=
  ∀ i : int, zLe min_signed (signed i) ∧ zLe (signed i) max_signed

def testbit_repr : Prop :=
  ∀ x i : Z, zLe zZero i ∧ zLt i zwordsize →
    testbit (repr x) i = zTestbit x i

def unsigned_range : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus

def unsigned_range_2 : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLe (unsigned i) max_unsigned

def unsigned_repr : Prop :=
  ∀ z : Z, zLe zZero z ∧ zLe z max_unsigned → unsigned (repr z) = z

def unsigned_repr_eq : Prop :=
  ∀ x : Z, unsigned (repr x) = zMod x modulus

def unsigned_repr_wordsize : Prop := unsigned iwordsize = zwordsize

def wordsize_max_unsigned : Prop := zLe zwordsize max_unsigned

def modulus_power : Prop := modulus = zTwoP zwordsize

def half_modulus_pos : Prop := zLt zZero half_modulus

def min_signed_neg : Prop := zLt min_signed zZero

def signed_repr_eq : Prop :=
  ∀ x : Z,
    signed (repr x) =
      zltSelect (zMod x modulus) half_modulus (zMod x modulus)
        (zSub (zMod x modulus) modulus)

def eqm_refl2 : Prop := ∀ x y : Z, x = y → eqm x y

def eqm_trans : Prop :=
  ∀ x y z : Z, eqm x y → eqm y z → eqm x z

def eqm_samerepr : Prop :=
  ∀ x y : Z, eqm x y → repr x = repr y

def eqm_unsigned_repr_r : Prop :=
  ∀ a b : Z, eqm a b → eqm a (unsigned (repr b))

def repr_signed : Prop := ∀ i : int, repr (signed i) = i

def signed_repr : Prop :=
  ∀ z : Z, zLe min_signed z ∧ zLe z max_signed → signed (repr z) = z

def signed_zero : Prop := signed zero = zZero

def signed_mone : Prop := signed mone = zOpp zOne

def one_not_zero : Prop := one ≠ zero

def eq_spec : Prop :=
  ∀ x y : int, if eq x y then x = y else x ≠ y

def eq_true : Prop := ∀ x : int, eq x x = true

def eq_false : Prop := ∀ x y : int, x ≠ y → eq x y = false

def add_signed : Prop :=
  ∀ x y : int, add x y = repr (zAdd (signed x) (signed y))

def add_commut : Prop := ∀ x y : int, add x y = add y x

def add_zero : Prop := ∀ x : int, add x zero = x

def add_zero_l : Prop := ∀ x : int, add zero x = x

def add_assoc : Prop :=
  ∀ x y z : int, add (add x y) z = add x (add y z)

def add_neg_zero : Prop := ∀ x : int, add x (neg x) = zero

def neg_involutive : Prop := ∀ x : int, neg (neg x) = x

def sub_add_opp : Prop :=
  ∀ x y : int, sub x y = add x (neg y)

def sub_idem : Prop := ∀ x : int, sub x x = zero

def sub_add_l : Prop :=
  ∀ x y z : int, sub (add x y) z = add (sub x z) y

def sub_add_r : Prop :=
  ∀ x y z : int, sub x (add y z) = add (sub x z) (neg y)

def mul_commut : Prop := ∀ x y : int, mul x y = mul y x

def mul_zero : Prop := ∀ x : int, mul x zero = zero

def mul_one : Prop := ∀ x : int, mul x one = x

def mul_add_distr_l : Prop :=
  ∀ x y z : int, mul (add x y) z = add (mul x z) (mul y z)

def mul_add_distr_r : Prop :=
  ∀ x y z : int, mul x (add y z) = add (mul x y) (mul x z)

def modu_divu : Prop :=
  ∀ x y : int, y ≠ zero → modu x y = sub x (mul (divu x y) y)

def mods_divs : Prop :=
  ∀ x y : int, mods x y = sub x (mul (divs x y) y)

def divu_one : Prop := ∀ x : int, divu x one = x

def divs_one : Prop :=
  ∀ x : int, zLt zOne zwordsize → divs x one = x

def divmodu2_divu_modu : Prop :=
  ∀ n d : int, d ≠ zero →
    divmodu2 zero n d = some (divu n d, modu n d)

def divmods2_divs_mods : Prop :=
  ∀ n d : int,
    d ≠ zero → n ≠ repr min_signed ∨ d ≠ mone →
      divmods2 (if lt n zero then mone else zero) n d =
        some (divs n d, mods n d)

def bits_one : Prop :=
  ∀ n : Z,
    testbit one n =
      sumboolSelect (CompCert4Lean.Lib.Coqlib.zeq n zZero) true false

def bits_mone : Prop :=
  ∀ i : Z, zLe zZero i ∧ zLt i zwordsize → testbit mone i = true

def bits_signed : Prop :=
  ∀ (x : int) (i : Z), zLe zZero i →
    zTestbit (signed x) i =
      testbit x (zltSelect i zwordsize i (zSub zwordsize zOne))

def bits_not : Prop :=
  ∀ (x : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (not x) i = !(testbit x i)

def and_commut : Prop := ∀ x y : int, and x y = and y x

def and_assoc : Prop :=
  ∀ x y z : int, and (and x y) z = and x (and y z)

def and_zero : Prop := ∀ x : int, and x zero = zero

def and_mone : Prop := ∀ x : int, and x mone = x

def and_idem : Prop := ∀ x : int, and x x = x

def or_commut : Prop := ∀ x y : int, or x y = or y x

def or_assoc : Prop :=
  ∀ x y z : int, or (or x y) z = or x (or y z)

def or_zero : Prop := ∀ x : int, or x zero = x

def or_mone : Prop := ∀ x : int, or x mone = mone

def xor_commut : Prop := ∀ x y : int, xor x y = xor y x

def xor_assoc : Prop :=
  ∀ x y z : int, xor (xor x y) z = xor x (xor y z)

def xor_zero : Prop := ∀ x : int, xor x zero = x

def xor_is_zero : Prop :=
  ∀ x y : int, eq (xor x y) zero = eq x y

def not_involutive : Prop := ∀ x : int, not (not x) = x

def not_or_and_not : Prop :=
  ∀ x y : int, not (or x y) = and (not x) (not y)

def shl_zero : Prop := ∀ x : int, shl x zero = x

def ltu_iwordsize_inv : Prop :=
  ∀ x : int, ltu x iwordsize = true →
    zLe zZero (unsigned x) ∧ zLt (unsigned x) zwordsize

def shl_shl : Prop :=
  ∀ x y z : int,
    ltu y iwordsize = true →
    ltu z iwordsize = true →
    ltu (add y z) iwordsize = true →
      shl (shl x y) z = shl x (add y z)

def shru_zero : Prop := ∀ x : int, shru x zero = x

def shru_shru : Prop :=
  ∀ x y z : int,
    ltu y iwordsize = true →
    ltu z iwordsize = true →
    ltu (add y z) iwordsize = true →
      shru (shru x y) z = shru x (add y z)

def shr_zero : Prop := ∀ x : int, shr x zero = x

def shr_shr : Prop :=
  ∀ x y z : int,
    ltu y iwordsize = true →
    ltu z iwordsize = true →
    ltu (add y z) iwordsize = true →
      shr (shr x y) z = shr x (add y z)

def shru_lt_zero : Prop :=
  ∀ x : int,
    shru x (repr (zSub zwordsize zOne)) =
      if lt x zero then one else zero

def shr_lt_zero : Prop :=
  ∀ x : int,
    shr x (repr (zSub zwordsize zOne)) =
      if lt x zero then mone else zero

def bits_rol : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (rol x y) i = testbit x (zMod (zSub i (unsigned y)) zwordsize)

def bits_ror : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (ror x y) i = testbit x (zMod (zAdd i (unsigned y)) zwordsize)

def ror_rol_neg : Prop :=
  ∀ x y : int, zDivide zwordsize modulus → ror x y = rol x (neg y)

def or_ror : Prop :=
  ∀ x y z : int,
    ltu y iwordsize = true →
    ltu z iwordsize = true →
    add y z = iwordsize →
      ror x z = or (shl x y) (shru x z)

def is_power2_range : Prop :=
  ∀ n logn : int,
    is_power2 n = some logn → ltu logn iwordsize = true

def shl_mul : Prop :=
  ∀ x y : int, shl x y = mul x (shl one y)

def mul_pow2 : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → mul x n = shl x logn

def shru_div_two_p : Prop :=
  ∀ x y : int, shru x y = repr (zDiv (unsigned x) (zTwoP (unsigned y)))

def divu_pow2 : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → divu x n = shru x logn

def shr_div_two_p : Prop :=
  ∀ x y : int, shr x y = repr (zDiv (signed x) (zTwoP (unsigned y)))

def divs_pow2 : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → divs x n = shrx x logn

def modu_and : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → modu x n = and x (sub n one)

def shrx_shr : Prop :=
  ∀ x y : int,
    ltu y (repr (zSub zwordsize zOne)) = true →
      shrx x y =
        shr (if lt x zero then add x (sub (shl one y) one) else x) y

def bits_zero_ext : Prop :=
  ∀ (n : Z) (x : int) (i : Z), zLe zZero i →
    testbit (zero_ext n x) i =
      zltSelect i n (testbit x i) false

def bits_sign_ext : Prop :=
  ∀ (n : Z) (x : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (sign_ext n x) i =
      testbit x (zltSelect i n i (zSub n zOne))

def zero_ext_and : Prop :=
  ∀ (n : Z) (x : int), zLe zZero n →
    zero_ext n x = and x (repr (zSub (zTwoP n) zOne))

def sign_ext_widen : Prop :=
  ∀ (x : int) (n n' : Z), zLt zZero n ∧ zLe n n' →
    sign_ext n' (sign_ext n x) = sign_ext n x

def zero_ext_idem : Prop :=
  ∀ (n : Z) (x : int), zLe zZero n →
    zero_ext n (zero_ext n x) = zero_ext n x

def sign_ext_idem : Prop :=
  ∀ (n : Z) (x : int), zLt zZero n →
    sign_ext n (sign_ext n x) = sign_ext n x

def sign_ext_shr_shl : Prop :=
  ∀ (n : Z) (x : int), zLt zZero n ∧ zLe n zwordsize →
    let y := repr (zSub zwordsize n)
    sign_ext n x = shr (shl x y) y

def one_bits_range : Prop :=
  ∀ x i : int, i ∈ one_bits x → ltu i iwordsize = true

def one_bits_decomp : Prop :=
  let rec intOfOneBits : List int → int
    | [] => zero
    | a :: rest => add (shl one a) (intOfOneBits rest)
  ∀ x : int, x = intOfOneBits (one_bits x)

def negate_cmp : Prop :=
  ∀ (c : comparison) (x y : int),
    cmp (negate_comparison c) x y = !(cmp c x y)

def negate_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (negate_comparison c) x y = !(cmpu c x y)

def swap_cmp : Prop :=
  ∀ (c : comparison) (x y : int),
    cmp (swap_comparison c) x y = cmp c y x

def swap_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (swap_comparison c) x y = cmpu c y x

def lt_sub_overflow : Prop :=
  ∀ x y : int,
    xor (sub_overflow x y zero) (negative (sub x y)) =
      if lt x y then one else zero

def not_lt : Prop :=
  ∀ x y : int, !(lt y x) = (lt x y || eq x y)

def lt_not : Prop :=
  ∀ x y : int, lt y x = (!(lt x y) && !(eq x y))

def not_ltu : Prop :=
  ∀ x y : int, !(ltu y x) = (ltu x y || eq x y)

def ltu_not : Prop :=
  ∀ x y : int, ltu y x = (!(ltu x y) && !(eq x y))

def bits_size_2 : Prop :=
  ∀ (x : int) (i : Z), zLe (size x) i → testbit x i = false

def size_range : Prop :=
  ∀ x : int, zLe zZero (size x) ∧ zLe (size x) zwordsize

def bits_size_4 : Prop :=
  ∀ (x : int) (n : Z),
    zLe zZero n →
    testbit x (zSub n zOne) = true →
    (∀ i : Z, zLe n i ∧ zLt i zwordsize → testbit x i = false) →
      size x = n

def unsigned_bitfield_extract_by_shifts : Prop :=
  ∀ (pos width : Z) (n : int),
    zLe zZero pos → zLt zZero width → zLe (zAdd pos width) zwordsize →
      unsigned_bitfield_extract pos width n =
        shru (shl n (repr (zSub (zSub zwordsize pos) width)))
          (repr (zSub zwordsize width))

def signed_bitfield_extract_by_shifts : Prop :=
  ∀ (pos width : Z) (n : int),
    zLe zZero pos → zLt zZero width → zLe (zAdd pos width) zwordsize →
      signed_bitfield_extract pos width n =
        shr (shl n (repr (zSub (zSub zwordsize pos) width)))
          (repr (zSub zwordsize width))

def bitfield_insert_alternative : Prop :=
  let bitfieldInsert := fun (pos width : Z) (n p : int) =>
    let mask := shl (repr (zSub (zTwoP width) zOne)) (repr pos)
    or (shl (zero_ext width p) (repr pos)) (and n (not mask))
  ∀ (pos width : Z) (n p : int), zLe zZero width →
    bitfieldInsert pos width n p =
      let mask := shl (repr (zSub (zTwoP width) zOne)) (repr pos)
      or (and (shl p (repr pos)) mask) (and n (not mask))

private theorem zero_ext_modulo (n : Z) (x : int) (hn : zLe zZero n) :
    ZArith.BinInt.Z.modulo (unsigned x) (two_p n) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (Int.ofNat (x.val % (2 ^ zToNat n))) := by
  change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n at hn
  let p : Nat := 2 ^ zToNat n
  let r : Nat := x.val % p
  let q : Nat := x.val / p
  have hp : 0 < p := Nat.two_pow_pos _
  have htwo :
      two_p n = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat p) := by
    cases n with
    | Z0 => rfl
    | Zpos exponent =>
        have hexp : ¬(Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent) < 0) :=
          _root_.Int.not_lt.mpr (_root_.Int.natCast_nonneg _)
        simp only [p, zToNat, two_p, ZArith.Zpower.two_p, ZArith.BinInt.Z.pow,
          ZArith.BinInt.Z.to_nat,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, hexp, if_false]
        apply congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        change (2 : Int) ^
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent =
          (2 : Int) ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent
        rfl
    | Zneg exponent =>
        have := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive exponent
        simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hn
        omega
  have hdecomp :
      unsigned x =
        ZArith.BinInt.Z.add
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r))
            (ZArith.BinInt.Z.mul
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat q))
            (two_p n)) := by
    change x.intval = _
    rw [WordCore.intval_eq_zOfNat_val x]
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    simp only [unsigned, WordCore.unsigned, zOfNat,
      ZArith.BinInt.Z.of_nat, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, htwo]
    have hnat : x.val = r + q * p := by
      simpa [r, q, Nat.mul_comm] using (Nat.mod_add_div x.val p).symm
    change Int.ofNat x.val = Int.ofNat (r + q * p)
    exact congrArg Int.ofNat hnat
  have hrange :
      zLe zZero (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r)) ∧
        zLt (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r)) (two_p n) := by
    constructor
    · change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r))
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      exact Int.natCast_nonneg r
    · change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat r)) <
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (two_p n)
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt, htwo]
      exact Int.ofNat_lt.mpr (Nat.mod_lt _ hp)
  rw [hdecomp]
  rw [ZArith.BinInt.Z.modulo_add_mul]
  exact ZArith.BinInt.Z.mod_small _ _ hrange

private theorem ziter_unfold_succ {A : Type} (f : A → A) (x : A) (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat (k + 1)) f x =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat k) f (f x) := by
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter,
    zOfNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
    Int.ofNat_eq_natCast, Int.toNat_natCast]
  rfl

private theorem ziter_commute {A : Type} (f : A → A) (x : A) (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat k) f (f x) =
      f (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat k) f x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [ziter_unfold_succ, ziter_unfold_succ]
      rw [ih (f x), ih x]

private theorem ziter_succ {A : Type} (f : A → A) (x : A) (k : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat (k + 1)) f x =
      f (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
        (zOfNat k) f x) := by
  rw [ziter_unfold_succ, ziter_commute]

private theorem zdiv2_nat (a : Nat) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2 (zOfNat a) =
      zOfNat (a / 2) := by
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div,
    zOfNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ediv (Int.ofNat a) (Int.ofNat 2) = Int.ofNat (a / 2)
  exact Int.ofNat_ediv_ofNat

private theorem zshiftin_nat (b : Bool) (a : Nat) :
    CompCert4Lean.Lib.Zbits.Zshiftin b (zOfNat a) =
      zOfNat (2 * a + if b then 1 else 0) := by
  cases b <;>
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective <;>
    simp only [CompCert4Lean.Lib.Zbits.Zshiftin,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.double,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.succ_double,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.succ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      zOfNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt,
      Bool.false_eq_true, ↓reduceIte]
  · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat,
      Nat.mul_comm, Nat.add_comm,
      Int.mul_comm]
  · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat,
      Nat.mul_comm, Nat.add_comm,
      Int.mul_comm, Int.add_comm]

private theorem zNatAbs_nat (a : Nat) :
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat a)).natAbs = a := by
  have hcast :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat a) = Int.ofNat a := by
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt (Int.ofNat a)
  rw [hcast]
  simp

private theorem zzero_ext_nat (k a : Nat) :
    CompCert4Lean.Lib.Zbits.Zzero_ext (zOfNat k) (zOfNat a) =
      zOfNat (a % (2 ^ k)) := by
  induction k generalizing a with
  | zero =>
      change zOfNat 0 = zOfNat (a % 1)
      rw [Nat.mod_one]
  | succ k ih =>
      have hstep :
          CompCert4Lean.Lib.Zbits.Zzero_ext (zOfNat (k + 1)) (zOfNat a) =
            CompCert4Lean.Lib.Zbits.Zshiftin
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
                (zOfNat a))
              (CompCert4Lean.Lib.Zbits.Zzero_ext (zOfNat k)
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2
                  (zOfNat a))) := by
        change CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
            (zOfNat (k + 1))
            (fun rec y =>
              CompCert4Lean.Lib.Zbits.Zshiftin
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd y)
                (rec (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2 y)))
            (fun _ => zZero) (zOfNat a) = _
        rw [ziter_succ]
        rfl
      rw [hstep]
      rw [zdiv2_nat]
      rw [ih]
      rw [zshiftin_nat]
      congr 1
      by_cases h : a % 2 = 0
      · have hodd :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
                (zOfNat a) = false := by
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
          rw [zNatAbs_nat]
          simp [h]
        rw [hodd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hmod := Nat.mod_mul (a := 2) (b := 2 ^ k) (x := a)
        simpa [Nat.pow_succ, Nat.add_comm, Nat.mul_comm, h] using hmod.symm
      · have hrem : a % 2 = 1 := by omega
        have hodd :
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
                (zOfNat a) = true := by
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd
          unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.even
          rw [zNatAbs_nat]
          simp [hrem]
        rw [hodd]
        simp only [↓reduceIte]
        have hmod := Nat.mod_mul (a := 2) (b := 2 ^ k) (x := a)
        simpa [Nat.pow_succ, Nat.add_comm, Nat.mul_comm, hrem] using hmod.symm

private theorem zzero_ext_nonneg (n : Z) (x : int) (hn : zLe zZero n) :
    CompCert4Lean.Lib.Zbits.Zzero_ext n (unsigned x) =
      zOfNat (x.val % (2 ^ zToNat n)) := by
  have hn' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Z2Nat.id n hn
  rw [← hn']
  change CompCert4Lean.Lib.Zbits.Zzero_ext (zOfNat (zToNat n)) x.intval = _
  rw [WordCore.intval_eq_zOfNat_val x]
  simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Znat.Nat2Z.id] using
    zzero_ext_nat (zToNat n) x.val

private theorem zero_ext_val (n : Z) (x : int) (hn : zLe zZero n) :
    (zero_ext n x).val =
      (x.val % (2 ^ zToNat n)) % (2 ^ wordsize) := by
  unfold zero_ext WordCore.zero_ext
  change (WordCore.repr wordsize
    (CompCert4Lean.Lib.Zbits.Zzero_ext n (unsigned x))).val = _
  rw [zzero_ext_nonneg n x hn]
  change (WordCore.repr wordsize
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (Int.ofNat (x.val % (2 ^ zToNat n))))).val = _
  rw [WordCore.val_repr]
  change Int.toNat
      (Int.ofNat (x.val % (2 ^ zToNat n)) % ((2 ^ wordsize : Nat) : Int)) =
        (x.val % (2 ^ zToNat n)) % (2 ^ wordsize)
  have hbridge := Int.emod_natAbs_of_nonneg
    (x := ((x.val % (2 ^ zToNat n) : Nat) : Int)) (n := 2 ^ wordsize)
    (Int.natCast_nonneg _)
  simp only [Int.natAbs_natCast] at hbridge
  simp only [Int.ofNat_eq_natCast]
  rw [← hbridge]

theorem unsigned_repr_proof_api (z : Z)
    (hz : zLe zZero z ∧ zLe z max_unsigned) :
    unsigned (repr z) = z := by
  have hznonneg : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z := hz.1
  have hzlt :
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z <
        ((2 ^ wordsize : Nat) : _root_.Int) := by
    have hzmax := hz.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ max_unsigned at hzmax
    unfold max_unsigned modulus at hzmax
    rw [WordCore.twoPowerNat_eq_zOfNat_twoPow] at hzmax
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
      _root_.Int.ofNat (2 ^ wordsize) - 1 at hzmax
    have hzmax' :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z ≤
          ((2 ^ wordsize : Nat) : _root_.Int) - 1 := by
      simpa only [_root_.Int.ofNat_eq_natCast] using hzmax
    omega
  change (WordCore.repr wordsize z).intval = z
  rw [WordCore.intval_eq_zOfNat_val]
  have hval :
      (WordCore.repr wordsize z).val =
        _root_.Int.toNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z %
            ((2 ^ wordsize : Nat) : _root_.Int)) := by
    rw [← CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ z]
    simpa only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using
      WordCore.val_repr wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z)
  rw [hval, _root_.Int.emod_eq_of_lt hznonneg hzlt]
  change CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (_root_.Int.ofNat
        (_root_.Int.toNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z))) = z
  calc
    _ = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ z) :=
      congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (_root_.Int.toNat_of_nonneg hznonneg)
    _ = z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt_intOfZ z

theorem zero_ext_mod_proof_api (n : Z) (x : int)
    (hn : zLe zZero n ∧ zLt n zwordsize) :
    unsigned (zero_ext n x) =
      ZArith.BinInt.Z.modulo (unsigned x) (two_p n) := by
  have hnnonneg : 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n := hn.1
  have hnlt : zToNat n < wordsize := by
    change _root_.Int.toNat
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n) < wordsize
    apply (_root_.Int.toNat_lt hnnonneg).2
    have hnltInt := hn.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zOfNat wordsize) at hnltInt
    have hnltInt' :
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ n <
          _root_.Int.ofNat wordsize := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] using hnltInt
    simpa only [_root_.Int.ofNat_eq_natCast] using hnltInt'
  have hpow : 2 ^ zToNat n ≤ 2 ^ wordsize :=
    Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_lt hnlt)
  have hvalLt : x.val % (2 ^ zToNat n) < 2 ^ wordsize :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hpow
  change (zero_ext n x).intval = _
  rw [WordCore.intval_eq_zOfNat_val, zero_ext_val n x hn.1,
    Nat.mod_eq_of_lt hvalLt, zero_ext_modulo n x hn.1]
  rfl

private theorem nested_power_mod_idem (a k w : Nat) :
    ((((a % (2 ^ k)) % (2 ^ w)) % (2 ^ k)) % (2 ^ w)) =
      (a % (2 ^ k)) % (2 ^ w) := by
  by_cases hkw : k ≤ w
  · have hpLe : 2 ^ k ≤ 2 ^ w :=
      Nat.pow_le_pow_right Nat.zero_lt_two hkw
    have haLt : a % (2 ^ k) < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have haLtW : a % (2 ^ k) < 2 ^ w := Nat.lt_of_lt_of_le haLt hpLe
    rw [Nat.mod_eq_of_lt haLtW, Nat.mod_mod, Nat.mod_eq_of_lt haLtW]
  · have hwk : w ≤ k := Nat.le_of_not_ge hkw
    have hpLe : 2 ^ w ≤ 2 ^ k :=
      Nat.pow_le_pow_right Nat.zero_lt_two hwk
    have haLt : (a % (2 ^ k)) % (2 ^ w) < 2 ^ w :=
      Nat.mod_lt _ (Nat.two_pow_pos w)
    have haLtK : (a % (2 ^ k)) % (2 ^ w) < 2 ^ k :=
      Nat.lt_of_lt_of_le haLt hpLe
    rw [Nat.mod_eq_of_lt haLtK, Nat.mod_mod]

theorem zero_ext_idem_proof_api (n : Z) (x : int) (hn : zLe zZero n) :
    zero_ext n (zero_ext n x) = zero_ext n x := by
  apply WordCore.ext_of_val_eq
  rw [zero_ext_val n (zero_ext n x) hn, zero_ext_val n x hn]
  exact nested_power_mod_idem x.val (zToNat n) wordsize

/-- `GENAPP-COMPCERT-LIB-INTEGERS-3562-ASSIGNMENT`: `Make(Wordsize_32)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

theorem generatedApplication_zero_ext_idem
    (n : Z) (x : generatedApplication.int) (hn : zLe zZero n) :
    generatedApplication.zero_ext n (generatedApplication.zero_ext n x) =
      generatedApplication.zero_ext n x := by
  change zero_ext n (zero_ext n x) = zero_ext n x
  exact zero_ext_idem_proof_api n x hn

end Int

namespace Byte

def wordsize : Nat := 8
def modulus : Z := zTwoPowerNat wordsize
abbrev int := WordCore.Word wordsize
def repr (x : Z) : int := WordCore.repr wordsize x
def unsigned (x : int) : Z := WordCore.unsigned x
def zero : int := WordCore.zero wordsize

def eqm_samerepr : Prop :=
  ∀ x y : Z, WordCore.eqm wordsize x y → repr x = repr y

def unsigned_range : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus

theorem unsigned_range_proof_api (i : int) :
    zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus := by
  constructor
  · have h := i.intrange.1
    change (-1 : _root_.Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ i.intval
    omega
  · exact i.intrange.2

/-- `GENAPP-COMPCERT-LIB-INTEGERS-3582-ASSIGNMENT`: `Make(Wordsize_8)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

end Byte

abbrev int := Int.int
abbrev byte := Byte.int

def int_wordsize_divides_modulusStatement : Prop :=
  zDivide (zOfNat Int.wordsize) Int.modulus

def int_wordsize_divides_modulus : Prop :=
  int_wordsize_divides_modulusStatement

namespace Int64

def wordsize : Nat := 64
def zwordsize : Z := zOfNat wordsize
def modulus : Z := zTwoPowerNat wordsize
def half_modulus : Z := zTwoPowerNat (wordsize - 1)
def max_unsigned : Z := zSub modulus zOne
def max_signed : Z := zSub half_modulus zOne
def min_signed : Z := zOpp half_modulus

abbrev int := WordCore.Word wordsize

def repr (x : Z) : int := WordCore.repr wordsize x
def ofFin (x : Fin (2 ^ wordsize)) : int := WordCore.Word.ofFin x
def toFin (x : int) : Fin (2 ^ wordsize) := x.toFin
def unsigned (x : int) : Z := WordCore.unsigned x
def signed (x : int) : Z := WordCore.signed x
def size (x : int) : Z := CompCert4Lean.Lib.Zbits.Zsize (unsigned x)
def zero : int := WordCore.zero wordsize
def one : int := WordCore.one wordsize
def mone : int := WordCore.mone wordsize
def iwordsize : int := WordCore.iwordsize wordsize
def eq : int → int → Bool := WordCore.eq
def eq_dec (x y : int) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  if h : x = y then .left h else .right h
def lt : int → int → Bool := WordCore.lt
def ltu : int → int → Bool := WordCore.ltu
def neg : int → int := WordCore.neg
def add : int → int → int := WordCore.add
def sub : int → int → int := WordCore.sub
def mul : int → int → int := WordCore.mul
def mulhs (x y : int) : int :=
  repr (zDiv (zMul (signed x) (signed y)) modulus)
def mulhu (x y : int) : int :=
  repr (zDiv (zMul (unsigned x) (unsigned y)) modulus)
def divs : int → int → int := WordCore.divs
def mods : int → int → int := WordCore.mods
def divu : int → int → int := WordCore.divu
def modu : int → int → int := WordCore.modu
def negative : int → int := WordCore.negative
def add_carry : int → int → int → int := WordCore.add_carry
def sub_overflow : int → int → int → int := WordCore.sub_overflow
def and : int → int → int := WordCore.and
def or : int → int → int := WordCore.or
def xor : int → int → int := WordCore.xor
def not : int → int := WordCore.not
def shl : int → int → int := WordCore.shl
def shru : int → int → int := WordCore.shru
def shr : int → int → int := WordCore.shr
def sign_ext (n : Z) (x : int) : int := WordCore.sign_ext n x
def zero_ext (n : Z) (x : int) : int :=
  WordCore.zero_ext n x
def rol : int → int → int := WordCore.rol
def ror : int → int → int := WordCore.ror
def shrx : int → int → int := WordCore.shrx
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

def is_power2 (x : int) : Option int :=
  match CompCert4Lean.Lib.Zbits.Z_is_power2 (unsigned x) with
  | some i => some (repr i)
  | none => none

def cmp : comparison → int → int → Bool := WordCore.cmp
def cmpu : comparison → int → int → Bool := WordCore.cmpu

def divmodu2 (nhi nlo d : int) : Option (int × int) :=
  match eq_dec d zero with
  | .left _ => none
  | .right _ =>
      let qr := ZArith.BinInt.Z.div_eucl
        (zAdd (zMul (unsigned nhi) modulus) (unsigned nlo)) (unsigned d)
      match CompCert4Lean.Lib.Coqlib.zle qr.1 max_unsigned with
      | .left _ => some (repr qr.1, repr qr.2)
      | .right _ => none

def divmods2 (nhi nlo d : int) : Option (int × int) :=
  match eq_dec d zero with
  | .left _ => none
  | .right _ =>
      let n := zAdd (zMul (signed nhi) modulus) (unsigned nlo)
      let sd := signed d
      let q := zQuot n sd
      let r := zSub n (zMul q sd)
      match CompCert4Lean.Lib.Coqlib.zle min_signed q,
          CompCert4Lean.Lib.Coqlib.zle q max_signed with
      | .left _, .left _ => some (repr q, repr r)
      | _, _ => none

def unsigned_bitfield_extract (pos width : Z) (n : int) : int :=
  WordCore.unsigned_bitfield_extract pos width n

def signed_bitfield_extract (pos width : Z) (n : int) : int :=
  WordCore.signed_bitfield_extract pos width n

def bitfield_insert (pos width : Z) (n p : int) : int :=
  WordCore.bitfield_insert pos width n p

def iwordsize' : Int.int := Int.repr zwordsize

def shl' (x : int) (y : Int.int) : int :=
  repr (zShiftl (unsigned x) (Int.unsigned y))

def shru' (x : int) (y : Int.int) : int :=
  repr (zShiftr (unsigned x) (Int.unsigned y))

def shr' (x : int) (y : Int.int) : int :=
  repr (zShiftr (signed x) (Int.unsigned y))

def rol' (x : int) (y : Int.int) : int :=
  rol x (repr (Int.unsigned y))

def ror' (x : int) (y : Int.int) : int :=
  ror x (repr (Int.unsigned y))

def shrx' (x : int) (y : Int.int) : int :=
  divs x (shl' one y)

def one_bits' (x : int) : List Int.int :=
  List.map Int.repr (CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned x) zZero)

def is_power2' (x : int) : Option Int.int :=
  match CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned x) zZero with
  | [i] => some (Int.repr i)
  | _ => none

def int_of_one_bits' : List Int.int → int
  | [] => zero
  | a :: rest => add (shl' one a) (int_of_one_bits' rest)

def loword (n : int) : Int.int :=
  Int.repr (unsigned n)

def hiword (n : int) : Int.int :=
  Int.repr (unsigned (shru n (repr Int.zwordsize)))

def ofwords (hi lo : Int.int) : int :=
  or (shl (repr (Int.unsigned hi)) (repr Int.zwordsize))
    (repr (Int.unsigned lo))

def mul' (x y : Int.int) : int :=
  repr (zMul (Int.unsigned x) (Int.unsigned y))

/-! Selected generated members of `Include Make(Wordsize_64)` retain their
    exact source propositions; proof discharge remains a later phase. -/
def bits_above : Prop :=
  ∀ (x : int) (i : Z), zLe zwordsize i → testbit x i = false

def bits_and : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (and x y) i = (testbit x i && testbit y i)

def bits_or : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (or x y) i = (testbit x i || testbit y i)

def bits_shl : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shl x y) i =
      zltSelect i (unsigned y) false (testbit x (zSub i (unsigned y)))

def bits_shru : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (shru x y) i =
      zltSelect (zAdd i (unsigned y)) zwordsize
        (testbit x (zAdd i (unsigned y))) false

def bits_signed : Prop :=
  ∀ (x : int) (i : Z), zLe zZero i →
    zTestbit (signed x) i =
      testbit x (zltSelect i zwordsize i (zSub zwordsize zOne))

def bits_xor : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (xor x y) i = Bool.xor (testbit x i) (testbit y i)

def eqm_add : Prop :=
  ∀ a b c d : Z, eqm a b → eqm c d → eqm (zAdd a c) (zAdd b d)

def eqm_mult : Prop :=
  ∀ a b c d : Z, eqm a c → eqm b d → eqm (zMul a b) (zMul c d)

def eqm_refl : Prop := ∀ x : Z, eqm x x

def eqm_samerepr : Prop :=
  ∀ x y : Z, eqm x y → repr x = repr y

def eqm_sym : Prop := ∀ x y : Z, eqm x y → eqm y x

def eqm_unsigned_repr : Prop :=
  ∀ z : Z, eqm z (unsigned (repr z))

def eqm_unsigned_repr_l : Prop :=
  ∀ a b : Z, eqm a b → eqm (unsigned (repr a)) b

def mul_commut : Prop := ∀ x y : int, mul x y = mul y x

def mul_one : Prop := ∀ x : int, mul x one = x

def or_ror : Prop :=
  ∀ x y z : int, ltu y iwordsize = true → ltu z iwordsize = true →
    add y z = iwordsize → ror x z = or (shl x y) (shru x z)

def repr_unsigned : Prop := ∀ i : int, repr (unsigned i) = i

def same_bits_eq : Prop :=
  ∀ x y : int,
    (∀ i : Z, zLe zZero i ∧ zLt i zwordsize → testbit x i = testbit y i) →
      x = y

def shifted_or_is_add : Prop :=
  ∀ (x y : int) (n : Z), zLe zZero n ∧ zLt n zwordsize →
    zLt (unsigned y) (zTwoP n) →
      or (shl x (repr n)) y =
        repr (zAdd (zMul (unsigned x) (zTwoP n)) (unsigned y))

def shl_shl : Prop :=
  ∀ x y z : int, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shl (shl x y) z = shl x (add y z)

def shr_shr : Prop :=
  ∀ x y z : int, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shr (shr x y) z = shr x (add y z)

def shru_shru : Prop :=
  ∀ x y z : int, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shru (shru x y) z = shru x (add y z)

def shrx_shr_2 : Prop :=
  ∀ x y : int,
    ltu y (repr (zSub zwordsize zOne)) = true →
      shrx x y =
        shr (add x (shru (shr x (repr (zSub zwordsize zOne)))
          (sub iwordsize y))) y

def shrx_zero : Prop :=
  ∀ x : int, zLt zOne zwordsize → shrx x zero = x

def signed_repr : Prop :=
  ∀ z : Z, zLe min_signed z ∧ zLe z max_signed → signed (repr z) = z

def testbit_repr : Prop :=
  ∀ x i : Z, zLe zZero i ∧ zLt i zwordsize →
    testbit (repr x) i = zTestbit x i

def unsigned_range : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus

def unsigned_repr : Prop :=
  ∀ z : Z, zLe zZero z ∧ zLe z max_unsigned → unsigned (repr z) = z

def unsigned_repr_eq : Prop :=
  ∀ x : Z, unsigned (repr x) = zMod x modulus

def modulus_power : Prop := modulus = zTwoP zwordsize
def modulus_pos : Prop := zLt zZero modulus
def half_modulus_pos : Prop := zLt zZero half_modulus
def min_signed_neg : Prop := zLt min_signed zZero

def signed_repr_eq : Prop :=
  ∀ x : Z,
    signed (repr x) =
      zltSelect (zMod x modulus) half_modulus (zMod x modulus)
        (zSub (zMod x modulus) modulus)

def eqm_refl2 : Prop := ∀ x y : Z, x = y → eqm x y

def eqm_trans : Prop :=
  ∀ x y z : Z, eqm x y → eqm y z → eqm x z

def eqm_unsigned_repr_r : Prop :=
  ∀ a b : Z, eqm a b → eqm a (unsigned (repr b))

def eqm_signed_unsigned : Prop :=
  ∀ x : int, eqm (signed x) (unsigned x)

def signed_range : Prop :=
  ∀ i : int, zLe min_signed (signed i) ∧ zLe (signed i) max_signed

def repr_signed : Prop := ∀ i : int, repr (signed i) = i
def signed_zero : Prop := signed zero = zZero
def signed_mone : Prop := signed mone = zOpp zOne
def one_not_zero : Prop := one ≠ zero

def eq_spec : Prop :=
  ∀ x y : int, if eq x y then x = y else x ≠ y

def eq_true : Prop := ∀ x : int, eq x x = true
def eq_sym : Prop := ∀ x y : int, eq x y = eq y x

def add_signed : Prop :=
  ∀ x y : int, add x y = repr (zAdd (signed x) (signed y))

def add_commut : Prop := ∀ x y : int, add x y = add y x
def add_zero : Prop := ∀ x : int, add x zero = x
def add_zero_l : Prop := ∀ x : int, add zero x = x

def add_assoc : Prop :=
  ∀ x y z : int, add (add x y) z = add x (add y z)

def neg_involutive : Prop := ∀ x : int, neg (neg x) = x
def sub_zero_l : Prop := ∀ x : int, sub x zero = x

def sub_add_opp : Prop :=
  ∀ x y : int, sub x y = add x (neg y)

def sub_add_l : Prop :=
  ∀ x y z : int, sub (add x y) z = add (sub x z) y

def sub_add_r : Prop :=
  ∀ x y z : int, sub x (add y z) = add (sub x z) (neg y)

def mul_zero : Prop := ∀ x : int, mul x zero = zero

def mul_add_distr_l : Prop :=
  ∀ x y z : int, mul (add x y) z = add (mul x z) (mul y z)

def mul_add_distr_r : Prop :=
  ∀ x y z : int, mul x (add y z) = add (mul x y) (mul x z)

def modu_divu : Prop :=
  ∀ x y : int, y ≠ zero → modu x y = sub x (mul (divu x y) y)

def mods_divs : Prop :=
  ∀ x y : int, mods x y = sub x (mul (divs x y) y)

def divmodu2_divu_modu : Prop :=
  ∀ n d : int, d ≠ zero →
    divmodu2 zero n d = some (divu n d, modu n d)

def divmods2_divs_mods : Prop :=
  ∀ n d : int,
    d ≠ zero → n ≠ repr min_signed ∨ d ≠ mone →
      divmods2 (if lt n zero then mone else zero) n d =
        some (divs n d, mods n d)

def bits_zero : Prop := ∀ i : Z, testbit zero i = false

def bits_mone : Prop :=
  ∀ i : Z, zLe zZero i ∧ zLt i zwordsize → testbit mone i = true

def and_commut : Prop := ∀ x y : int, and x y = and y x

def and_assoc : Prop :=
  ∀ x y z : int, and (and x y) z = and x (and y z)

def and_zero : Prop := ∀ x : int, and x zero = zero
def and_mone : Prop := ∀ x : int, and x mone = x
def and_idem : Prop := ∀ x : int, and x x = x
def or_commut : Prop := ∀ x y : int, or x y = or y x

def or_assoc : Prop :=
  ∀ x y z : int, or (or x y) z = or x (or y z)

def or_zero : Prop := ∀ x : int, or x zero = x
def or_mone : Prop := ∀ x : int, or x mone = mone
def xor_commut : Prop := ∀ x y : int, xor x y = xor y x

def xor_assoc : Prop :=
  ∀ x y z : int, xor (xor x y) z = xor x (xor y z)

def xor_zero : Prop := ∀ x : int, xor x zero = x
def xor_idem : Prop := ∀ x : int, xor x x = zero

def xor_zero_equal : Prop :=
  ∀ x y : int, xor x y = zero → x = y

def not_involutive : Prop := ∀ x : int, not (not x) = x

def not_or_and_not : Prop :=
  ∀ x y : int, not (or x y) = and (not x) (not y)

def shl_zero : Prop := ∀ x : int, shl x zero = x

def ltu_inv : Prop :=
  ∀ x y : int, ltu x y = true →
    zLe zZero (unsigned x) ∧ zLt (unsigned x) (unsigned y)

def shru_zero : Prop := ∀ x : int, shru x zero = x
def shr_zero : Prop := ∀ x : int, shr x zero = x

def shru_lt_zero : Prop :=
  ∀ x : int,
    shru x (repr (zSub zwordsize zOne)) =
      if lt x zero then one else zero

def shr_lt_zero : Prop :=
  ∀ x : int,
    shr x (repr (zSub zwordsize zOne)) =
      if lt x zero then mone else zero

def bits_rol : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (rol x y) i = testbit x (zMod (zSub i (unsigned y)) zwordsize)

def bits_ror : Prop :=
  ∀ (x y : int) (i : Z), zLe zZero i ∧ zLt i zwordsize →
    testbit (ror x y) i = testbit x (zMod (zAdd i (unsigned y)) zwordsize)

def ror_rol_neg : Prop :=
  ∀ x y : int, zDivide zwordsize modulus → ror x y = rol x (neg y)

def modu_and : Prop :=
  ∀ x n logn : int,
    is_power2 n = some logn → modu x n = and x (sub n one)

def bits_zero_ext : Prop :=
  ∀ (n : Z) (x : int) (i : Z), zLe zZero i →
    testbit (zero_ext n x) i = zltSelect i n (testbit x i) false

def negate_cmp : Prop :=
  ∀ (c : comparison) (x y : int),
    cmp (negate_comparison c) x y = !(cmp c x y)

def negate_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (negate_comparison c) x y = !(cmpu c x y)

def swap_cmp : Prop :=
  ∀ (c : comparison) (x y : int),
    cmp (swap_comparison c) x y = cmp c y x

def swap_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (swap_comparison c) x y = cmpu c y x

def lt_sub_overflow : Prop :=
  ∀ x y : int,
    xor (sub_overflow x y zero) (negative (sub x y)) =
      if lt x y then one else zero

def not_lt : Prop :=
  ∀ x y : int, !(lt y x) = (lt x y || eq x y)

def lt_not : Prop :=
  ∀ x y : int, lt y x = (!(lt x y) && !(eq x y))

def not_ltu : Prop :=
  ∀ x y : int, !(ltu y x) = (ltu x y || eq x y)

def ltu_not : Prop :=
  ∀ x y : int, ltu y x = (!(ltu x y) && !(eq x y))

def size_range : Prop :=
  ∀ x : int, zLe zZero (size x) ∧ zLe (size x) zwordsize

def bits_size_2 : Prop :=
  ∀ (x : int) (i : Z), zLe (size x) i → testbit x i = false

def bits_size_4 : Prop :=
  ∀ (x : int) (n : Z),
    zLe zZero n →
    testbit x (zSub n zOne) = true →
    (∀ i : Z, zLe n i ∧ zLt i zwordsize → testbit x i = false) →
      size x = n

/-! ## Exact statement descriptors for the deferred Int64 proofs -/

def bits_shl'Statement : Prop :=
  ∀ (x : int) (y : Int.int) (i : Z),
    zLe zZero i ∧ zLt i zwordsize →
      testbit (shl' x y) i =
        zltSelect i (Int.unsigned y) false
          (testbit x (zSub i (Int.unsigned y)))

def bits_shru'Statement : Prop :=
  ∀ (x : int) (y : Int.int) (i : Z),
    zLe zZero i ∧ zLt i zwordsize →
      testbit (shru' x y) i =
        zltSelect (zAdd i (Int.unsigned y)) zwordsize
          (testbit x (zAdd i (Int.unsigned y))) false

def bits_shr'Statement : Prop :=
  ∀ (x : int) (y : Int.int) (i : Z),
    zLe zZero i ∧ zLt i zwordsize →
      testbit (shr' x y) i =
        testbit x
          (zltSelect (zAdd i (Int.unsigned y)) zwordsize
            (zAdd i (Int.unsigned y)) (zSub zwordsize zOne))

def shl'_mul_two_pStatement : Prop :=
  ∀ (x : int) (y : Int.int),
    shl' x y = mul x (repr (zTwoP (Int.unsigned y)))

def shl'_one_two_pStatement : Prop :=
  ∀ y : Int.int, shl' one y = repr (zTwoP (Int.unsigned y))

def shl'_mulStatement : Prop :=
  ∀ (x : int) (y : Int.int), shl' x y = mul x (shl' one y)

def shrx'_zeroStatement : Prop :=
  ∀ x : int, shrx' x Int.zero = x

def shrx'_shr_2Statement : Prop :=
  ∀ (x : int) (y : Int.int),
    Int.ltu y (Int.repr (zOfNat 63)) = true →
      shrx' x y =
        shr'
          (add x
            (shru' (shr' x (Int.repr (zOfNat 63)))
              (Int.sub (Int.repr (zOfNat 64)) y))) y

def int_ltu_2_invStatement : Prop :=
  ∀ y z : Int.int,
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    zLe (Int.unsigned (Int.add y z)) (Int.unsigned iwordsize') →
      let y' := repr (Int.unsigned y)
      let z' := repr (Int.unsigned z)
      Int.unsigned y = unsigned y' ∧
      Int.unsigned z = unsigned z' ∧
      ltu y' iwordsize = true ∧
      ltu z' iwordsize = true ∧
      Int.unsigned (Int.add y z) = unsigned (add y' z') ∧
      add y' z' = repr (Int.unsigned (Int.add y z))

def or_ror'Statement : Prop :=
  ∀ (x : int) (y z : Int.int),
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    Int.add y z = iwordsize' →
      ror x (repr (Int.unsigned z)) = or (shl' x y) (shru' x z)

def shl'_shl'Statement : Prop :=
  ∀ (x : int) (y z : Int.int),
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    Int.ltu (Int.add y z) iwordsize' = true →
      shl' (shl' x y) z = shl' x (Int.add y z)

def shru'_shru'Statement : Prop :=
  ∀ (x : int) (y z : Int.int),
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    Int.ltu (Int.add y z) iwordsize' = true →
      shru' (shru' x y) z = shru' x (Int.add y z)

def shr'_shr'Statement : Prop :=
  ∀ (x : int) (y z : Int.int),
    Int.ltu y iwordsize' = true →
    Int.ltu z iwordsize' = true →
    Int.ltu (Int.add y z) iwordsize' = true →
      shr' (shr' x y) z = shr' x (Int.add y z)

def one_bits'_rangeStatement : Prop :=
  ∀ (x : int) (i : Int.int),
    i ∈ one_bits' x → Int.ltu i iwordsize' = true

def one_bits'_decompStatement : Prop :=
  ∀ x : int, x = int_of_one_bits' (one_bits' x)

def is_power2'_rngStatement : Prop :=
  ∀ (n : int) (logn : Int.int),
    is_power2' n = some logn →
      zLe zZero (Int.unsigned logn) ∧ zLt (Int.unsigned logn) zwordsize

def is_power2'_rangeStatement : Prop :=
  ∀ (n : int) (logn : Int.int),
    is_power2' n = some logn → Int.ltu logn iwordsize' = true

def is_power2'_correctStatement : Prop :=
  ∀ (n : int) (logn : Int.int),
    is_power2' n = some logn →
      unsigned n = zTwoP (Int.unsigned logn)

def mul_pow2'Statement : Prop :=
  ∀ (x n : int) (logn : Int.int),
    is_power2' n = some logn → mul x n = shl' x logn

def divu_pow2'Statement : Prop :=
  ∀ (x n : int) (logn : Int.int),
    is_power2' n = some logn → divu x n = shru' x logn

def bits_lowordStatement : Prop :=
  ∀ (n : int) (i : Z),
    zLe zZero i ∧ zLt i Int.zwordsize →
      Int.testbit (loword n) i = testbit n i

def bits_hiwordStatement : Prop :=
  ∀ (n : int) (i : Z),
    zLe zZero i ∧ zLt i Int.zwordsize →
      Int.testbit (hiword n) i = testbit n (zAdd i Int.zwordsize)

def bits_ofwordsStatement : Prop :=
  ∀ (hi lo : Int.int) (i : Z),
    zLe zZero i ∧ zLt i zwordsize →
      testbit (ofwords hi lo) i =
        zltSelect i Int.zwordsize (Int.testbit lo i)
          (Int.testbit hi (zSub i Int.zwordsize))

def lo_ofwordsStatement : Prop :=
  ∀ hi lo : Int.int, loword (ofwords hi lo) = lo

def hi_ofwordsStatement : Prop :=
  ∀ hi lo : Int.int, hiword (ofwords hi lo) = hi

def ofwords_recomposeStatement : Prop :=
  ∀ n : int, ofwords (hiword n) (loword n) = n

def ofwords_addStatement : Prop :=
  ∀ lo hi : Int.int,
    ofwords hi lo =
      repr (zAdd (zMul (Int.unsigned hi) (zTwoP (zOfNat 32)))
        (Int.unsigned lo))

def ofwords_add'Statement : Prop :=
  ∀ lo hi : Int.int,
    unsigned (ofwords hi lo) =
      zAdd (zMul (Int.unsigned hi) (zTwoP (zOfNat 32)))
        (Int.unsigned lo)

def eqm_mul_2p32Statement : Prop :=
  ∀ x y : Z,
    Int.eqm x y →
      eqm (zMul x (zTwoP (zOfNat 32))) (zMul y (zTwoP (zOfNat 32)))

def ofwords_add''Statement : Prop :=
  ∀ lo hi : Int.int,
    signed (ofwords hi lo) =
      zAdd (zMul (Int.signed hi) (zTwoP (zOfNat 32)))
        (Int.unsigned lo)

def decompose_bitwise_binopStatement : Prop :=
  ∀ (f : Bool → Bool → Bool)
    (f64 : int → int → int) (f32 : Int.int → Int.int → Int.int)
    (xh xl yh yl : Int.int),
    (∀ (x y : int) (i : Z),
      zLe zZero i ∧ zLt i zwordsize →
        testbit (f64 x y) i = f (testbit x i) (testbit y i)) →
    (∀ (x y : Int.int) (i : Z),
      zLe zZero i ∧ zLt i Int.zwordsize →
        Int.testbit (f32 x y) i = f (Int.testbit x i) (Int.testbit y i)) →
      f64 (ofwords xh xl) (ofwords yh yl) =
        ofwords (f32 xh yh) (f32 xl yl)

def decompose_andStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    and (ofwords xh xl) (ofwords yh yl) =
      ofwords (Int.and xh yh) (Int.and xl yl)

def decompose_orStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    or (ofwords xh xl) (ofwords yh yl) =
      ofwords (Int.or xh yh) (Int.or xl yl)

def decompose_xorStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    xor (ofwords xh xl) (ofwords yh yl) =
      ofwords (Int.xor xh yh) (Int.xor xl yl)

def decompose_shl_1Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe zZero (Int.unsigned y) ∧ zLt (Int.unsigned y) Int.zwordsize →
      shl' (ofwords xh xl) y =
        ofwords
          (Int.or (Int.shl xh y)
            (Int.shru xl (Int.sub Int.iwordsize y)))
          (Int.shl xl y)

def decompose_shl_2Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe Int.zwordsize (Int.unsigned y) ∧ zLt (Int.unsigned y) zwordsize →
      shl' (ofwords xh xl) y =
        ofwords (Int.shl xl (Int.sub y Int.iwordsize)) Int.zero

def decompose_shru_1Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe zZero (Int.unsigned y) ∧ zLt (Int.unsigned y) Int.zwordsize →
      shru' (ofwords xh xl) y =
        ofwords (Int.shru xh y)
          (Int.or (Int.shru xl y)
            (Int.shl xh (Int.sub Int.iwordsize y)))

def decompose_shru_2Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe Int.zwordsize (Int.unsigned y) ∧ zLt (Int.unsigned y) zwordsize →
      shru' (ofwords xh xl) y =
        ofwords Int.zero (Int.shru xh (Int.sub y Int.iwordsize))

def decompose_shr_1Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe zZero (Int.unsigned y) ∧ zLt (Int.unsigned y) Int.zwordsize →
      shr' (ofwords xh xl) y =
        ofwords (Int.shr xh y)
          (Int.or (Int.shru xl y)
            (Int.shl xh (Int.sub Int.iwordsize y)))

def decompose_shr_2Statement : Prop :=
  ∀ xh xl y : Int.int,
    zLe Int.zwordsize (Int.unsigned y) ∧ zLt (Int.unsigned y) zwordsize →
      shr' (ofwords xh xl) y =
        ofwords (Int.shr xh (Int.sub Int.iwordsize Int.one))
          (Int.shr xh (Int.sub y Int.iwordsize))

def decompose_mulStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    mul (ofwords xh xl) (ofwords yh yl) =
      ofwords
        (Int.add
          (Int.add (hiword (mul' xl yl)) (Int.mul xl yh))
          (Int.mul xh yl))
        (loword (mul' xl yl))

def decompose_ltuStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    ltu (ofwords xh xl) (ofwords yh yl) =
      (if Int.eq xh yh then Int.ltu xl yl else Int.ltu xh yh)

def decompose_leuStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    (! (ltu (ofwords yh yl) (ofwords xh xl))) =
      (if Int.eq xh yh then !(Int.ltu yl xl) else Int.ltu xh yh)

def decompose_ltStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    lt (ofwords xh xl) (ofwords yh yl) =
      (if Int.eq xh yh then Int.ltu xl yl else Int.lt xh yh)

def decompose_leStatement : Prop :=
  ∀ xh xl yh yl : Int.int,
    (! (lt (ofwords yh yl) (ofwords xh xl))) =
      (if Int.eq xh yh then !(Int.ltu yl xl) else Int.lt xh yh)

def bits_hiword : Prop := bits_hiwordStatement
def bits_loword : Prop := bits_lowordStatement
def bits_ofwords : Prop := bits_ofwordsStatement
def bits_shl' : Prop := bits_shl'Statement
def bits_shr' : Prop := bits_shr'Statement
def bits_shru' : Prop := bits_shru'Statement
def decompose_and : Prop := decompose_andStatement
def decompose_bitwise_binop : Prop := decompose_bitwise_binopStatement
def decompose_le : Prop := decompose_leStatement
def decompose_leu : Prop := decompose_leuStatement
def decompose_lt : Prop := decompose_ltStatement
def decompose_ltu : Prop := decompose_ltuStatement
def decompose_mul : Prop := decompose_mulStatement
def decompose_or : Prop := decompose_orStatement
def decompose_shl_1 : Prop := decompose_shl_1Statement
def decompose_shl_2 : Prop := decompose_shl_2Statement
def decompose_shr_1 : Prop := decompose_shr_1Statement
def decompose_shr_2 : Prop := decompose_shr_2Statement
def decompose_shru_1 : Prop := decompose_shru_1Statement
def decompose_shru_2 : Prop := decompose_shru_2Statement
def decompose_xor : Prop := decompose_xorStatement
def divu_pow2' : Prop := divu_pow2'Statement
def eqm_mul_2p32 : Prop := eqm_mul_2p32Statement
def hi_ofwords : Prop := hi_ofwordsStatement
def int_ltu_2_inv : Prop := int_ltu_2_invStatement
def is_power2'_correct : Prop := is_power2'_correctStatement
def is_power2'_range : Prop := is_power2'_rangeStatement
def is_power2'_rng : Prop := is_power2'_rngStatement
def lo_ofwords : Prop := lo_ofwordsStatement
def mul_pow2' : Prop := mul_pow2'Statement
def ofwords_add : Prop := ofwords_addStatement
def ofwords_add' : Prop := ofwords_add'Statement
def ofwords_add'' : Prop := ofwords_add''Statement
def ofwords_recompose : Prop := ofwords_recomposeStatement
def one_bits'_decomp : Prop := one_bits'_decompStatement
def one_bits'_range : Prop := one_bits'_rangeStatement
def or_ror' : Prop := or_ror'Statement
def shl'_mul : Prop := shl'_mulStatement
def shl'_mul_two_p : Prop := shl'_mul_two_pStatement
def shl'_one_two_p : Prop := shl'_one_two_pStatement
def shl'_shl' : Prop := shl'_shl'Statement
def shr'_shr' : Prop := shr'_shr'Statement
def shru'_shru' : Prop := shru'_shru'Statement
def shrx'_shr_2 : Prop := shrx'_shr_2Statement
def shrx'_zero : Prop := shrx'_zeroStatement

/-- `GENAPP-COMPCERT-LIB-INTEGERS-3598-INCLUDE`: `Include Make(Wordsize_64)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

end Int64

abbrev int64 := Int64.int

namespace Wordsize_Ptrofs

def wordsize : Nat :=
  if CompCert4Lean.X86_64.Archi.ptr64 then 64 else 32

end Wordsize_Ptrofs

namespace Ptrofs

def wordsize : Nat := Wordsize_Ptrofs.wordsize
def zwordsize : Z := zOfNat wordsize
def modulus : Z := zTwoPowerNat wordsize
def half_modulus : Z := zTwoPowerNat (wordsize - 1)
def max_unsigned : Z := zSub modulus zOne
def max_signed : Z := zSub half_modulus zOne
def min_signed : Z := zOpp half_modulus

abbrev int := WordCore.Word wordsize

def repr (x : Z) : int := WordCore.repr wordsize x
def unsigned (x : int) : Z := WordCore.unsigned x
def signed (x : int) : Z := WordCore.signed x
def zero : int := WordCore.zero wordsize
def one : int := WordCore.one wordsize
def eq : int → int → Bool := WordCore.eq
def eq_dec (x y : int) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (x = y) (x ≠ y) :=
  if h : x = y then .left h else .right h
def lt : int → int → Bool := WordCore.lt
def ltu : int → int → Bool := WordCore.ltu
def cmpu (c : comparison) (x y : int) : Bool :=
  match c with
  | .Ceq => eq x y
  | .Cne => !(eq x y)
  | .Clt => ltu x y
  | .Cle => !(ltu y x)
  | .Cgt => ltu y x
  | .Cge => !(ltu x y)
def neg : int → int := WordCore.neg
def add : int → int → int := WordCore.add
def sub : int → int → int := WordCore.sub
def mul : int → int → int := WordCore.mul
def divs : int → int → int := WordCore.divs
def divu : int → int → int := WordCore.divu
def and : int → int → int := WordCore.and
def or : int → int → int := WordCore.or
def xor : int → int → int := WordCore.xor
def shl : int → int → int := WordCore.shl
def shru : int → int → int := WordCore.shru
def shr : int → int → int := WordCore.shr
def sign_ext (n : Z) (x : int) : int := WordCore.sign_ext n x
def testbit : int → Z → Bool := WordCore.testbit
def eqm : Z → Z → Prop := WordCore.eqm wordsize

/-! Selected generated members of `Include Make(Wordsize_Ptrofs)` retain their
    exact source propositions; proof discharge remains a later phase. -/
def eqm_repr_eq : Prop :=
  ∀ (x : Z) (y : int), eqm x (unsigned y) → repr x = y

def unsigned_repr_eq : Prop :=
  ∀ x : Z, unsigned (repr x) = zMod x modulus

def modulus_pos : Prop := zLt zZero modulus
def min_signed_neg : Prop := zLt min_signed zZero

def eqm_unsigned_repr : Prop :=
  ∀ z : Z, eqm z (unsigned (repr z))

def unsigned_range : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLt (unsigned i) modulus

def unsigned_range_2 : Prop :=
  ∀ i : int, zLe zZero (unsigned i) ∧ zLe (unsigned i) max_unsigned

def repr_unsigned : Prop := ∀ i : int, repr (unsigned i) = i

def unsigned_repr : Prop :=
  ∀ z : Z, zLe zZero z ∧ zLe z max_unsigned → unsigned (repr z) = z

def signed_repr : Prop :=
  ∀ z : Z, zLe min_signed z ∧ zLe z max_signed → signed (repr z) = z

def unsigned_zero : Prop := unsigned zero = zZero
def unsigned_one : Prop := unsigned one = zOne

def eq_spec : Prop :=
  ∀ x y : int, if eq x y then x = y else x ≠ y

def eq_true : Prop := ∀ x : int, eq x x = true
def eq_false : Prop := ∀ x y : int, x ≠ y → eq x y = false

def add_unsigned : Prop :=
  ∀ x y : int, add x y = repr (zAdd (unsigned x) (unsigned y))

def add_commut : Prop := ∀ x y : int, add x y = add y x
def add_zero : Prop := ∀ x : int, add x zero = x
def add_zero_l : Prop := ∀ x : int, add zero x = x

def add_assoc : Prop :=
  ∀ x y z : int, add (add x y) z = add x (add y z)

def sub_add_opp : Prop :=
  ∀ x y : int, sub x y = add x (neg y)

def sub_add_l : Prop :=
  ∀ x y z : int, sub (add x y) z = add (sub x z) y

def sub_add_r : Prop :=
  ∀ x y z : int, sub x (add y z) = add (sub x z) (neg y)

def sub_shifted : Prop :=
  ∀ x y z : int, sub (add x z) (add y z) = sub x y

def negate_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (negate_comparison c) x y = !(cmpu c x y)

def swap_cmpu : Prop :=
  ∀ (c : comparison) (x y : int),
    cmpu (swap_comparison c) x y = cmpu c y x

def translate_cmpu : Prop :=
  ∀ (c : comparison) (x y d : int),
    zLe zZero (zAdd (unsigned x) (unsigned d)) ∧
      zLe (zAdd (unsigned x) (unsigned d)) max_unsigned →
    zLe zZero (zAdd (unsigned y) (unsigned d)) ∧
      zLe (zAdd (unsigned y) (unsigned d)) max_unsigned →
      cmpu c (add x d) (add y d) = cmpu c x y

def not_ltu : Prop :=
  ∀ x y : int, !(ltu y x) = (ltu x y || eq x y)

def ltu_not : Prop :=
  ∀ x y : int, ltu y x = (!(ltu x y) && !(eq x y))

/-- `GENAPP-COMPCERT-LIB-INTEGERS-4725-INCLUDE`: `Include Make(Wordsize_Ptrofs)`. -/
def generatedApplication : WordCore.GeneratedApplication :=
  WordCore.makeGeneratedApplication wordsize

theorem add_commut_proof_api (x y : int) : add x y = add y x := by
  change WordCore.add x y = WordCore.add y x
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val, WordCore.add_val, Nat.add_comm]

theorem add_assoc_proof_api (x y z : int) :
    add (add x y) z = add x (add y z) := by
  change WordCore.add (WordCore.add x y) z = WordCore.add x (WordCore.add y z)
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val, WordCore.add_val, WordCore.add_val, WordCore.add_val]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem sub_add_l_proof_api (x y z : int) :
    sub (add x y) z = add (sub x z) y := by
  change WordCore.sub (WordCore.add x y) z = WordCore.add (WordCore.sub x z) y
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int, WordCore.add_val_int,
    WordCore.sub_val_int]
  simp only [Int.emod_sub_emod, Int.sub_emod_emod, Int.emod_add_emod,
    Int.add_emod_emod]
  congr 1
  omega

theorem sub_shifted_proof_api (x y z : int) :
    sub (add x z) (add y z) = sub x y := by
  change WordCore.sub (WordCore.add x z) (WordCore.add y z) = WordCore.sub x y
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int, WordCore.add_val_int,
    WordCore.sub_val_int]
  simp only [Int.emod_sub_emod, Int.sub_emod_emod, Int.emod_add_emod,
    Int.add_emod_emod]
  congr 1
  omega

theorem generatedApplication_add_commut
    (x y : generatedApplication.int) :
    generatedApplication.add x y = generatedApplication.add y x := by
  change add x y = add y x
  exact add_commut_proof_api x y

theorem generatedApplication_add_assoc
    (x y z : generatedApplication.int) :
    generatedApplication.add (generatedApplication.add x y) z =
      generatedApplication.add x (generatedApplication.add y z) := by
  change add (add x y) z = add x (add y z)
  exact add_assoc_proof_api x y z

theorem generatedApplication_sub_add_l
    (x y z : generatedApplication.int) :
    generatedApplication.sub (generatedApplication.add x y) z =
      generatedApplication.add (generatedApplication.sub x z) y := by
  change sub (add x y) z = add (sub x z) y
  exact sub_add_l_proof_api x y z

theorem generatedApplication_sub_shifted
    (x y z : generatedApplication.int) :
    generatedApplication.sub (generatedApplication.add x z)
        (generatedApplication.add y z) =
      generatedApplication.sub x y := by
  change sub (add x z) (add y z) = sub x y
  exact sub_shifted_proof_api x y z

def to_int (x : int) : Int.int := Int.repr (unsigned x)
def to_int64 (x : int) : Int64.int := Int64.repr (unsigned x)
def of_int (x : Int.int) : int := repr (Int.unsigned x)
def of_intu : Int.int → int := of_int
def of_ints (x : Int.int) : int := repr (Int.signed x)
def of_int64 (x : Int64.int) : int := repr (Int64.unsigned x)

def agree32 (a : int) (b : Int.int) : Prop :=
  unsigned a = Int.unsigned b

def agree64 (a : int) (b : Int64.int) : Prop :=
  unsigned a = Int64.unsigned b

def modulus_eq32Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false → modulus = Int.modulus

def eqm32Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∀ x y : Z, Int.eqm x y ↔ eqm x y

def agree32_reprStatement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∀ i : Z, agree32 (repr i) (Int.repr i)

def agree32_of_intStatement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∀ b : Int.int, agree32 (of_int b) b

def of_int_to_intStatement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = false →
    ∀ n : int, of_int (to_int n) = n

def modulus_eq64Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = true → modulus = Int64.modulus

def eqm64Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = true →
    ∀ x y : Z, Int64.eqm x y ↔ eqm x y

def agree64_reprStatement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = true →
    ∀ i : Z, agree64 (repr i) (Int64.repr i)

def of_int64_to_int64Statement : Prop :=
  CompCert4Lean.X86_64.Archi.ptr64 = true →
    ∀ n : int, of_int64 (to_int64 n) = n

def agree32_of_int : Prop := agree32_of_intStatement
def agree32_repr : Prop := agree32_reprStatement
def agree64_repr : Prop := agree64_reprStatement
def eqm32 : Prop := eqm32Statement
def eqm64 : Prop := eqm64Statement
def modulus_eq32 : Prop := modulus_eq32Statement
def modulus_eq64 : Prop := modulus_eq64Statement
def of_int64_to_int64 : Prop := of_int64_to_int64Statement
def of_int_to_int : Prop := of_int_to_intStatement

end Ptrofs

abbrev ptrofs := Ptrofs.int

end CompCert4Lean.Lib.Integers

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem signed_mone_proof : signed_mone := by
  rfl

theorem shru_zero_proof : shru_zero := by
  intro x
  have hx0 :
      ZArith.BinInt.Z.le
        Numbers.BinNums.Z.Z0 (unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  have hxlt : ZArith.BinInt.Z.lt (unsigned x) modulus := x.intrange.2
  have hxmax :
      ZArith.BinInt.Z.le (unsigned x) max_unsigned := by
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval ≤ _
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ modulus - 1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ modulus at hxlt
    omega
  apply WordCore.ext
  change
    (WordCore.repr wordsize
      (ZArith.BinInt.Z.shiftr (unsigned x) (unsigned zero))).intval = x.intval
  have hz : unsigned zero = Numbers.BinNums.Z.Z0 := by rfl
  rw [hz]
  rw [show ZArith.BinInt.Z.shiftr (unsigned x) Numbers.BinNums.Z.Z0 = unsigned x by
    unfold ZArith.BinInt.Z.shiftr
    change
      (if (0 : Int) ≤ 0 then
          zOfInt ((intOfZ (unsigned x)).ediv (Int.pow 2 (Int.toNat 0)))
        else zOfInt (intOfZ (unsigned x) * Int.pow 2 (-0).toNat)) = unsigned x
    rw [if_pos (by omega)]
    have hp : Int.pow 2 (Int.toNat 0) = 1 := by rfl
    rw [hp]
    exact congrArg zOfInt (Int.ediv_one (intOfZ (unsigned x))) |>.trans
      (zOfInt_intOfZ (unsigned x))]
  change (WordCore.repr wordsize (unsigned x)).intval = x.intval
  have hrepr := unsigned_repr_proof_api (unsigned x) ⟨hx0, hxmax⟩
  exact hrepr

private theorem suffix_val_lt_wordsize (x : int) : x.val < 2 ^ wordsize := by
  have hxnonneg : 0 ≤ intOfZ x.intval := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    omega
  have hxlt : intOfZ x.intval < (Int.ofNat (2 ^ wordsize)) := by
    have h := x.intrange.2
    change intOfZ x.intval < intOfZ (two_power_nat wordsize) at h
    have hp : intOfZ (two_power_nat wordsize) = Int.ofNat (2 ^ wordsize) := by rfl
    rw [hp] at h
    exact h
  have hvalz :
      ZArith.BinInt.Z.of_nat (ZArith.BinInt.Z.to_nat x.intval) = x.intval :=
    ZArith.Znat.Z2Nat.id x.intval (by
      change 0 ≤ intOfZ x.intval
      exact hxnonneg)
  have hint :
      Int.ofNat (ZArith.BinInt.Z.to_nat x.intval) = intOfZ x.intval := by
    have h := congrArg intOfZ hvalz
    simpa only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] using h
  have hnat : ZArith.BinInt.Z.to_nat x.intval = Int.toNat (intOfZ x.intval) := by
    rw [← Int.toNat_of_nonneg hxnonneg] at hint
    exact Int.ofNat.inj hint
  change ZArith.BinInt.Z.to_nat x.intval < 2 ^ wordsize
  rw [hnat]
  exact (Int.toNat_lt hxnonneg).mpr hxlt

private theorem suffix_xor_unsigned (x y : int) :
    unsigned (xor x y) =
      ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val) := by
  have hnlt : Nat.xor x.val y.val < 2 ^ wordsize :=
    Nat.xor_lt_two_pow (suffix_val_lt_wordsize x) (suffix_val_lt_wordsize y)
  have hz0 : ZArith.BinInt.Z.le Numbers.BinNums.Z.Z0
      (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val)) := by
    change 0 ≤ intOfZ (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val))
    have hnat : 0 ≤ (Nat.xor x.val y.val : Int) := by omega
    simpa only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast] using hnat
  have hzm : ZArith.BinInt.Z.le
      (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val)) max_unsigned := by
    change intOfZ (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val)) ≤ intOfZ max_unsigned
    have hmax : intOfZ max_unsigned = Int.ofNat (2 ^ wordsize) - 1 := by rfl
    rw [hmax]
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast]
    omega
  exact unsigned_repr_proof_api
    (ZArith.BinInt.Z.of_nat (Nat.xor x.val y.val)) ⟨hz0, hzm⟩

private theorem suffix_xor_zero_iff_nat (x y : int) :
    xor x y = zero ↔ Nat.xor x.val y.val = 0 := by
  constructor
  · intro h
    have hu := congrArg unsigned h
    rw [suffix_xor_unsigned] at hu
    have hz : unsigned zero = Numbers.BinNums.Z.Z0 := by rfl
    rw [hz] at hu
    have hi := congrArg intOfZ hu
    have hzero : intOfZ Numbers.BinNums.Z.Z0 = (0 : Int) := by rfl
    rw [hzero] at hi
    have hi' : Int.ofNat (Nat.xor x.val y.val) = 0 := by
      simpa only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] using hi
    exact Int.ofNat.inj hi'
  · intro h
    apply WordCore.ext
    change unsigned (xor x y) = unsigned zero
    rw [suffix_xor_unsigned]
    have hz : unsigned zero = Numbers.BinNums.Z.Z0 := by rfl
    rw [hz]
    rw [h]
    rfl

theorem xor_is_zero_proof : xor_is_zero := by
  intro x y
  change decide ((xor x y).intval = zero.intval) = decide (x.intval = y.intval)
  have hiff : (xor x y).intval = zero.intval ↔ x.intval = y.intval := by
    constructor
    · intro h
      have hxy : xor x y = zero := WordCore.ext h
      have hn : Nat.xor x.val y.val = 0 := suffix_xor_zero_iff_nat x y |>.mp hxy
      have hnat : x.val = y.val := by
        apply Nat.eq_of_testBit_eq
        intro i
        have hz : (Nat.xor x.val y.val).testBit i = false := by rw [hn]; simp
        rw [Nat.xor_eq, Nat.testBit_xor] at hz
        by_cases ha : x.val.testBit i = true <;>
          by_cases hb : y.val.testBit i = true <;> simp [ha, hb] at hz ⊢
      have hv : x = y := WordCore.ext_of_val_eq hnat
      exact congrArg (fun q => q.intval) hv
    · intro h
      have hxy : x = y := WordCore.ext h
      have hn : Nat.xor x.val y.val = 0 := by rw [hxy, Nat.xor_eq, Nat.xor_self]
      have hz : xor x y = zero := suffix_xor_zero_iff_nat x y |>.mpr hn
      exact congrArg (fun q => q.intval) hz
  by_cases hp : (xor x y).intval = zero.intval
  · have hq : x.intval = y.intval := hiff.mp hp
    simp [hp, hq]
  · have hq : ¬ x.intval = y.intval := by
      intro hq
      exact hp (hiff.mpr hq)
    simp [hp, hq]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_wordcore_neg_val_int (x : int) :
    Int.ofNat (WordCore.neg x).val =
      (-Int.ofNat x.val) % Int.ofNat (2 ^ wordsize) := by
  unfold WordCore.neg
  have hrepr : zOpp (WordCore.unsigned x) =
      zOfInt (-Int.ofNat x.val) := by
    change zOfInt (-intOfZ x.intval) = zOfInt (-Int.ofNat x.val)
    rw [WordCore.intval_eq_zOfNat_val x]
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  rw [hrepr, WordCore.val_repr]
  exact Int.toNat_of_nonneg
    (Int.emod_nonneg _ (Int.ne_of_gt
      (Int.natCast_pos.mpr (Nat.two_pow_pos wordsize))))

private theorem suffix_wordcore_mul_val_int (x y : int) :
    Int.ofNat (WordCore.mul x y).val =
      (Int.ofNat x.val * Int.ofNat y.val) % Int.ofNat (2 ^ wordsize) := by
  unfold WordCore.mul
  have hrepr : zMul (WordCore.unsigned x) (WordCore.unsigned y) =
      zOfInt (Int.ofNat x.val * Int.ofNat y.val) := by
    change zOfInt (intOfZ x.intval * intOfZ y.intval) =
      zOfInt (Int.ofNat x.val * Int.ofNat y.val)
    rw [WordCore.intval_eq_zOfNat_val x, WordCore.intval_eq_zOfNat_val y]
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  rw [hrepr, WordCore.val_repr]
  exact Int.toNat_of_nonneg
    (Int.emod_nonneg _ (Int.ne_of_gt
      (Int.natCast_pos.mpr (Nat.two_pow_pos wordsize))))

theorem sub_add_opp_proof : sub_add_opp := by
  intro x y
  change WordCore.sub x y = WordCore.add x (WordCore.neg y)
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int,
    suffix_wordcore_neg_val_int]
  rw [Int.sub_eq_add_neg, Int.add_emod_emod]

theorem mul_add_distr_r_proof : mul_add_distr_r := by
  intro x y z
  change WordCore.mul x (WordCore.add y z) =
    WordCore.add (WordCore.mul x y) (WordCore.mul x z)
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [suffix_wordcore_mul_val_int x (WordCore.add y z),
    WordCore.add_val_int y z,
    WordCore.add_val_int (WordCore.mul x y) (WordCore.mul x z),
    suffix_wordcore_mul_val_int x y, suffix_wordcore_mul_val_int x z]
  let m : Int := Int.ofNat (2 ^ wordsize)
  change
    (Int.ofNat x.val * ((Int.ofNat y.val + Int.ofNat z.val) % m)) % m =
      ((Int.ofNat x.val * Int.ofNat y.val) % m +
        (Int.ofNat x.val * Int.ofNat z.val) % m) % m
  calc
    (Int.ofNat x.val * ((Int.ofNat y.val + Int.ofNat z.val) % m)) % m =
        (Int.ofNat x.val % m *
          (((Int.ofNat y.val + Int.ofNat z.val) % m) % m)) % m :=
      Int.mul_emod _ _ _
    _ = (Int.ofNat x.val % m *
          ((Int.ofNat y.val + Int.ofNat z.val) % m)) % m := by
      rw [Int.emod_emod]
    _ = (Int.ofNat x.val * (Int.ofNat y.val + Int.ofNat z.val)) % m :=
      (Int.mul_emod _ _ _).symm
    _ = (Int.ofNat x.val * Int.ofNat y.val +
          Int.ofNat x.val * Int.ofNat z.val) % m := by
      rw [Int.mul_add]
    _ = ((Int.ofNat x.val * Int.ofNat y.val) % m +
          (Int.ofNat x.val * Int.ofNat z.val) % m) % m :=
      Int.add_emod _ _ _

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shl_zero_proof : shl_zero := by
  intro x
  change WordCore.shl x (WordCore.zero wordsize) = x
  apply WordCore.ext
  change (WordCore.repr wordsize
    (zShiftl (unsigned x) (unsigned (WordCore.zero wordsize)))).intval = x.intval
  have hz : unsigned (WordCore.zero wordsize) =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 := by
    rfl
  rw [hz]
  rw [show zShiftl (unsigned x)
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 = unsigned x by
    unfold zShiftl CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftl
    rw [show intOfZ Numbers.BinNums.Z.Z0 = 0 by rfl]
    rw [if_pos (by omega)]
    simp only [Int.toNat_zero]
    rw [show Int.pow 2 0 = 1 by rfl]
    simp
    exact zOfInt_intOfZ _]
  change (WordCore.repr wordsize (unsigned x)).intval = x.intval
  have hx0 : ZArith.BinInt.Z.le
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0 (unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval at h
    change 0 ≤ CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval
    omega
  have hxmax : ZArith.BinInt.Z.le (unsigned x) max_unsigned := by
    have h := x.intrange.2
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ modulus at h
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval ≤
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ max_unsigned
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval ≤
      (2 ^ wordsize : Int) - 1
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x.intval <
      (2 ^ wordsize : Int) at h
    omega
  exact unsigned_repr_proof_api (unsigned x) ⟨hx0, hxmax⟩

theorem swap_cmpu_proof : swap_cmpu := by
  intro c x y
  cases c <;> simp [cmpu, WordCore.cmpu, swap_comparison, WordCore.eq, eq_comm]

private theorem suffix_zshiftr_div (x y : Z)
    (hx : zLe zZero x) (hy : zLe zZero y) :
    zShiftr x y = zDiv x (zTwoP y) := by
  change 0 ≤ intOfZ x at hx
  change 0 ≤ intOfZ y at hy
  have hpow : intOfZ (zTwoP y) =
      Int.pow 2 (Int.toNat (intOfZ y)) := by
    unfold zTwoP two_p CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p
    change intOfZ (if intOfZ y < 0 then Numbers.BinNums.Z.Z0 else
      zOfInt (Int.pow (intOfZ (Numbers.BinNums.Z.Zpos (.xO .xH)))
        (Int.toNat (intOfZ y)))) = _
    rw [if_neg (by omega)]
    rw [intOfZ_zOfInt]
    rfl
  apply intOfZ_injective
  simp [zShiftr, zDiv,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div,
    hx, hy]
  rw [intOfZ_zOfInt, intOfZ_zOfInt]
  rw [hpow]
  change (Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y)))) =
    (if Int.pow 2 (Int.toNat (intOfZ y)) = 0 then 0
      else if 0 < Int.pow 2 (Int.toNat (intOfZ y)) then
        Int.ediv (intOfZ x) (Int.pow 2 (Int.toNat (intOfZ y)))
      else
        let d := -(Int.pow 2 (Int.toNat (intOfZ y)))
        let q := Int.ediv (intOfZ x) d
        let r := Int.emod (intOfZ x) d
        if r = 0 then -q else -(q + 1))
  have hp : 0 < Int.pow 2 (Int.toNat (intOfZ y)) := by
    exact Int.pow_pos (by omega)
  simp [hp, Int.ne_of_gt hp]

theorem shru_div_two_p_proof : shru_div_two_p := by
  intro x y
  change WordCore.repr wordsize
      (zShiftr (unsigned x) (unsigned y)) =
    WordCore.repr wordsize (zDiv (unsigned x) (zTwoP (unsigned y)))
  have hx : zLe zZero (unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ x.intval at h
    change 0 ≤ intOfZ x.intval
    omega
  have hy : zLe zZero (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega
  rw [suffix_zshiftr_div (unsigned x) (unsigned y) hx hy]

theorem eqm_samerepr_proof : eqm_samerepr := by
  intro x y h
  apply WordCore.ext_of_val_eq
  rw [show x = zOfInt (intOfZ x) by exact (zOfInt_intOfZ x).symm,
    show y = zOfInt (intOfZ y) by exact (zOfInt_intOfZ y).symm]
  change (WordCore.repr wordsize (zOfInt (intOfZ x))).val =
    (WordCore.repr wordsize (zOfInt (intOfZ y))).val
  rw [WordCore.val_repr, WordCore.val_repr]
  have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
    unfold modulus
    rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
    rfl
  unfold eqm WordCore.eqm Zbits.eqmod at h
  rcases h with ⟨k, hk⟩
  have hk' := congrArg intOfZ hk
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hk'
  change intOfZ x = intOfZ k * intOfZ modulus + intOfZ y at hk'
  have hrem : intOfZ x % intOfZ modulus = intOfZ y % intOfZ modulus := by
    rw [hk', Int.add_emod, Int.mul_emod]
    simp
  rw [hm] at hrem
  exact congrArg Int.toNat hrem

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

theorem sub_idem_proof : sub_idem := by
  intro x
  change WordCore.sub x x = WordCore.zero wordsize
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int]
  simp
  rfl

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_two_p_nonneg (n : Z) (hn : zLe zZero n) :
    zTwoP n = zOfInt (Int.ofNat (2 ^ zToNat n)) := by
  change 0 ≤ intOfZ n at hn
  cases n with
  | Z0 => rfl
  | Zpos exponent =>
      have hexp : ¬(Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent) < 0) := _root_.Int.not_lt.mpr (_root_.Int.natCast_nonneg _)
      simp only [zTwoP, two_p, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p, zToNat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.to_nat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ, CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, hexp, if_false]
      apply congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      change (2 : Int) ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent = (2 : Int) ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat exponent
      rfl
  | Zneg exponent =>
      have hpos := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive exponent
      simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ] at hn
      omega

private theorem suffix_mask_val (n : Z) (hn : zLe zZero n) :
    (WordCore.repr wordsize (zSub (zTwoP n) zOne)).val = (2 ^ zToNat n - 1) % (2 ^ wordsize) := by
  have htwo := suffix_two_p_nonneg n hn
  have hsub_nat (a b : Nat) (hba : b ≤ a) : zSub (zOfNat a) (zOfNat b) = zOfNat (a - b) := by
    apply intOfZ_injective
    simp only [zSub, ZArith.BinInt.Z.sub, zOfNat, ZArith.BinInt.Z.of_nat, CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
    exact (Int.ofNat_sub hba).symm
  have hsub : zSub (zTwoP n) zOne = zOfNat (2 ^ zToNat n - 1) := by
    have hq : 1 ≤ 2 ^ zToNat n := Nat.one_le_two_pow
    have hqrepr : zOfInt (Int.ofNat (2 ^ zToNat n)) = zOfNat (2 ^ zToNat n) := by rfl
    have hOne : zOne = zOfNat 1 := by rfl
    rw [htwo, hqrepr, hOne, hsub_nat _ _ hq]
  rw [hsub]
  change (WordCore.repr wordsize (zOfNat (2 ^ zToNat n - 1))).val = _
  have hznat : zOfNat (2 ^ zToNat n - 1) = zOfInt (Int.ofNat (2 ^ zToNat n - 1)) := by rfl
  rw [hznat, WordCore.val_repr_residue, WordCore.residue_zOfNat]

private theorem suffix_and_val (x y : int) : (WordCore.and x y).val = Nat.land x.val y.val := by
  unfold WordCore.and
  have hz : zOfNat (Nat.land x.val y.val) = zOfInt (Int.ofNat (Nat.land x.val y.val)) := by rfl
  rw [hz, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (WordCore.val_lt y))

private theorem suffix_nat_zero_ext_and (a k w : Nat) (ha : a < 2 ^ w) : (a % (2 ^ k)) % (2 ^ w) = Nat.land a ((2 ^ k - 1) % (2 ^ w)) := by
  by_cases hkw : k ≤ w
  · have hpow : 2 ^ k ≤ 2 ^ w := Nat.pow_le_pow_right Nat.zero_lt_two hkw
    have hklt : 2 ^ k - 1 < 2 ^ w := by omega
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos k)) hpow), Nat.mod_eq_of_lt hklt]
    exact (Nat.and_two_pow_sub_one_eq_mod a k).symm
  · have hwk : w ≤ k := Nat.le_of_not_ge hkw
    have hpow : 2 ^ w ≤ 2 ^ k := Nat.pow_le_pow_right Nat.zero_lt_two hwk
    have h1 : a % (2 ^ k) = a := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hpow)
    have h2 : a % (2 ^ w) = a := Nat.mod_eq_of_lt ha
    rw [h1, h2]
    have hmask : (2 ^ k - 1) % (2 ^ w) = 2 ^ w - 1 := by
      have hpoww : 0 < 2 ^ w := Nat.two_pow_pos w
      have hpowd : 0 < 2 ^ (k - w) := Nat.two_pow_pos _
      have hkpow : 2 ^ k = 2 ^ w * 2 ^ (k - w) := by rw [← Nat.pow_add]; congr 1; omega
      have hdecomp : 2 ^ k - 1 = 2 ^ w * (2 ^ (k - w) - 1) + (2 ^ w - 1) := by
        rw [hkpow, Nat.mul_sub_left_distrib]
        have hmul : 2 ^ w ≤ 2 ^ w * 2 ^ (k - w) := Nat.le_mul_of_pos_right _ hpowd
        omega
      rw [hdecomp, Nat.add_comm, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmask]
    exact (Nat.and_two_pow_sub_one_of_lt_two_pow ha).symm

theorem zero_ext_and_proof : zero_ext_and := by
  intro n x hn
  change WordCore.zero_ext n x = WordCore.and x (WordCore.repr wordsize (zSub (zTwoP n) zOne))
  apply WordCore.ext_of_val_eq
  change (zero_ext n x).val = (WordCore.and x (WordCore.repr wordsize (zSub (zTwoP n) zOne))).val
  rw [zero_ext_val n x hn, suffix_and_val, suffix_mask_val n hn]
  exact suffix_nat_zero_ext_and x.val (zToNat n) wordsize (WordCore.val_lt x)

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

theorem unsigned_repr_wordsize_proof : unsigned_repr_wordsize := by
  unfold unsigned_repr_wordsize iwordsize zwordsize
  apply unsigned_repr_proof_api
  constructor
  · change (0 : Int) ≤ 32
    omega
  · change (32 : Int) ≤ (2 ^ wordsize : Int) - 1
    decide

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ltu_inv_proof : ltu_inv := by
  intro x y h
  change zltSelect (unsigned x) (unsigned y) true false = true at h
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
  | left hxy =>
      simp [zltSelect, sumboolSelect, hlt] at h
      constructor
      · have hx := x.intrange.1
        change (-1 : Int) < intOfZ (unsigned x) at hx
        change 0 ≤ intOfZ (unsigned x)
        omega
      · exact hxy
  | right hxy =>
      simp [zltSelect, sumboolSelect, hlt] at h

theorem add_assoc_proof : add_assoc := by
  intro x y z
  change WordCore.add (WordCore.add x y) z = WordCore.add x (WordCore.add y z)
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val, WordCore.add_val, WordCore.add_val, WordCore.add_val]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

private theorem signed_injective_try {x y : int} (h : signed x = signed y) : x = y := by
  dsimp [signed, WordCore.signed] at h
  simp [zltSelect, sumboolSelect] at h
  split at h <;> split at h
  · apply WordCore.ext
    exact h
  · exfalso
    have hx0 : 0 ≤ intOfZ (unsigned x) := by
      have hx := x.intrange.1
      change (-1 : Int) < intOfZ (unsigned x) at hx
      omega
    have hymod := y.intrange.2
    change intOfZ (unsigned y) < intOfZ modulus at hymod
    change intOfZ (unsigned y) < intOfZ (zTwoPowerNat wordsize) at hymod
    have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hymod hh
    have hh' : intOfZ (unsigned x) =
        intOfZ (unsigned y) - (2 ^ wordsize : Int) := by
      exact hh
    have hneg : intOfZ (unsigned y) - (2 ^ wordsize : Int) < 0 := by
      omega
    rw [← hh'] at hneg
    exact (Int.not_lt_of_ge hx0 hneg).elim
  · exfalso
    have hy0 : 0 ≤ intOfZ (unsigned y) := by
      have hy := y.intrange.1
      change (-1 : Int) < intOfZ (unsigned y) at hy
      omega
    have hxmod := x.intrange.2
    change intOfZ (unsigned x) < intOfZ modulus at hxmod
    change intOfZ (unsigned x) < intOfZ (zTwoPowerNat wordsize) at hxmod
    have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hxmod hh
    have hh' : intOfZ (unsigned x) - (2 ^ wordsize : Int) =
        intOfZ (unsigned y) := by
      exact hh
    have hneg : intOfZ (unsigned x) - (2 ^ wordsize : Int) < 0 := by
      omega
    rw [hh'] at hneg
    exact (Int.not_lt_of_ge hy0 hneg).elim
  · have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hh
    have hu : unsigned x = unsigned y := by
      apply intOfZ_injective
      exact (Int.sub_left_inj _).mp hh
    apply WordCore.ext
    exact hu

theorem lt_not_proof : lt_not := by
  intro x y
  by_cases hxy : x = y
  · subst y
    cases h : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed x) with
    | left hlt => exact (Int.lt_irrefl _ hlt).elim
    | right hge =>
        change zltSelect (signed x) (signed x) true false =
          (!zltSelect (signed x) (signed x) true false && !eq x x)
        simp only [zltSelect, sumboolSelect]
        rw [h]
        simp [eq, WordCore.eq]
  · have heq : eq x y = false := by
      have hxy' : x.intval ≠ y.intval := by
        intro hval
        apply hxy
        exact WordCore.ext hval
      simp [eq, WordCore.eq, hxy']
    cases h1 : CompCert4Lean.Lib.Coqlib.zlt (signed y) (signed x) with
    | left h1lt =>
        cases h2 : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed y) with
        | left h2lt => exact (Int.lt_asymm h1lt h2lt).elim
        | right h2ge =>
            change zltSelect (signed y) (signed x) true false =
              (!zltSelect (signed x) (signed y) true false && !eq x y)
            simp only [zltSelect, sumboolSelect]
            rw [h1, h2]
            simp [heq]
    | right h1ge =>
        cases h2 : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed y) with
        | left h2lt =>
            change zltSelect (signed y) (signed x) true false =
              (!zltSelect (signed x) (signed y) true false && !eq x y)
            simp only [zltSelect, sumboolSelect]
            rw [h1, h2]
            simp [heq]
        | right h2ge =>
            have hs : signed x = signed y := intOfZ_injective
              (Int.le_antisymm h1ge h2ge)
            exact (hxy (signed_injective_try hs)).elim

theorem shru_lt_zero_proof : shru_lt_zero := by
  intro x
  rw [shru_div_two_p_proof]
  have hy : unsigned (repr (zSub zwordsize zOne)) = zSub zwordsize zOne := by
    apply unsigned_repr_proof_api
    constructor
    · change (0 : Int) ≤ 31
      omega
    · change (31 : Int) ≤ (2 ^ wordsize : Int) - 1
      decide
  rw [hy]
  by_cases hlt : lt x zero = true
  · simp [hlt]
    have hn : zLe zZero (zSub zwordsize zOne) := by
      change (0 : Int) ≤ 31
      omega
    have hpow := suffix_two_p_nonneg (zSub zwordsize zOne) hn
    have hnval : zToNat (zSub zwordsize zOne) = wordsize - 1 := by
      decide
    have hpow' : zTwoP (zSub zwordsize zOne) =
        zOfInt (Int.ofNat (2 ^ (wordsize - 1))) := by
      simpa [hnval] using hpow
    rw [hpow']
    have hq : zDiv (unsigned x)
        (zOfInt (Int.ofNat (2 ^ (wordsize - 1)))) = zOne := by
      apply intOfZ_injective
      simp only [zDiv,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div]
      rw [intOfZ_zOfInt]
      change Int.ediv (intOfZ (unsigned x))
          (Int.ofNat (2 ^ (wordsize - 1))) = 1
      have hslt : zLt (signed x) (signed zero) := by
        change zltSelect (signed x) (signed zero) true false = true at hlt
        cases hs : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
        | left hs' => exact hs'
        | right hs' => simp [zltSelect, sumboolSelect, hs] at hlt
      have hz : signed zero = zZero := by
        rfl
      rw [hz] at hslt
      have hxr : intOfZ (unsigned x) ≥ (2 ^ (wordsize - 1) : Int) := by
        cases hx : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) half_modulus with
        | left hx' =>
            exfalso
            have hx0 : 0 ≤ intOfZ (unsigned x) := by
              have h := x.intrange.1
              change (-1 : Int) < intOfZ (unsigned x) at h
              omega
            have hxs : signed x = unsigned x := by
              unfold signed
              dsimp [WordCore.signed]
              simp only [zltSelect, sumboolSelect]
              have hx'' : CompCert4Lean.Lib.Coqlib.zlt
                  (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) =
                  Foundation.Logic.Support.Sumbool.left hx' := by
                exact hx
              rw [hx'']
              rfl
            rw [hxs] at hslt
            change intOfZ (unsigned x) < 0 at hslt
            omega
        | right hx' =>
            change intOfZ (unsigned x) ≥ intOfZ half_modulus at hx'
            have hh : intOfZ half_modulus = (2 ^ (wordsize - 1) : Int) := by
              unfold half_modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            rw [hh] at hx'
            exact hx'
      have hxmod : intOfZ (unsigned x) < (2 ^ wordsize : Int) := by
        have h := x.intrange.2
        change intOfZ (unsigned x) < intOfZ modulus at h
        have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
          unfold modulus
          rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
          rfl
        rw [hm] at h
        exact h
      have hdpos : (0 : Int) < Int.ofNat (2 ^ (wordsize - 1)) := by
        exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
      have hpowrel : (2 ^ wordsize : Int) =
          2 * Int.ofNat (2 ^ (wordsize - 1)) := by
        decide
      have hqge : (1 : Int) ≤ Int.ediv (intOfZ (unsigned x))
          (Int.ofNat (2 ^ (wordsize - 1))) := by
        apply (Int.le_ediv_iff_mul_le hdpos).2
        simpa using hxr
      have hqlt : Int.ediv (intOfZ (unsigned x))
          (Int.ofNat (2 ^ (wordsize - 1))) < 2 := by
        apply (Int.ediv_lt_iff_lt_mul hdpos).2
        rw [hpowrel] at hxmod
        omega
      omega
    change WordCore.repr wordsize
        (zDiv (unsigned x) (zOfInt (Int.ofNat (2 ^ (wordsize - 1))))) =
      WordCore.repr wordsize zOne
    rw [hq]
  · simp [hlt]
    have hn : zLe zZero (zSub zwordsize zOne) := by
      change (0 : Int) ≤ 31
      omega
    have hpow := suffix_two_p_nonneg (zSub zwordsize zOne) hn
    have hnval : zToNat (zSub zwordsize zOne) = wordsize - 1 := by
      decide
    have hpow' : zTwoP (zSub zwordsize zOne) =
        zOfInt (Int.ofNat (2 ^ (wordsize - 1))) := by
      simpa [hnval] using hpow
    rw [hpow']
    have hq : zDiv (unsigned x)
        (zOfInt (Int.ofNat (2 ^ (wordsize - 1)))) = zZero := by
      apply intOfZ_injective
      simp only [zDiv,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div]
      rw [intOfZ_zOfInt]
      change Int.ediv (intOfZ (unsigned x))
          (Int.ofNat (2 ^ (wordsize - 1))) = 0
      have hsge : zLe zZero (signed x) := by
        have hlt' := hlt
        change ¬(zltSelect (signed x) (signed zero) true false = true) at hlt'
        cases hs : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
        | left hs' => simp [zltSelect, sumboolSelect, hs] at hlt'
        | right hs' =>
            change intOfZ (signed x) ≥ intOfZ (signed zero) at hs'
            have hz : signed zero = zZero := by rfl
            rw [hz] at hs'
            exact hs'
      have hxl : intOfZ (unsigned x) < (2 ^ (wordsize - 1) : Int) := by
        cases hx : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) half_modulus with
        | left hx' =>
            change intOfZ (unsigned x) < intOfZ half_modulus at hx'
            have hh : intOfZ half_modulus = (2 ^ (wordsize - 1) : Int) := by
              unfold half_modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            rw [hh] at hx'
            exact hx'
        | right hx' =>
            exfalso
            have hxs : signed x = zSub (unsigned x) modulus := by
              unfold signed WordCore.signed
              simp only [zltSelect, sumboolSelect]
              have hx'' : CompCert4Lean.Lib.Coqlib.zlt
                  (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) =
                  Foundation.Logic.Support.Sumbool.right hx' := by
                exact hx
              rw [hx'']
              rfl
            rw [hxs] at hsge
            change intOfZ (zSub (unsigned x) modulus) ≥ 0 at hsge
            have hxmod := x.intrange.2
            change intOfZ (unsigned x) < intOfZ modulus at hxmod
            have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
              unfold modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            have hh : intOfZ half_modulus = (2 ^ (wordsize - 1) : Int) := by
              unfold half_modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            have hxge : intOfZ (unsigned x) ≥ intOfZ half_modulus := hx'
            rw [hm] at hxmod
            rw [hh] at hxge
            have hsge' := hsge
            simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hsge'
            rw [hm] at hsge'
            omega
      have hx0 : 0 ≤ intOfZ (unsigned x) := by
        have h := x.intrange.1
        change (-1 : Int) < intOfZ (unsigned x) at h
        omega
      exact Int.ediv_eq_zero_of_lt hx0 hxl
    change WordCore.repr wordsize
        (zDiv (unsigned x) (zOfInt (Int.ofNat (2 ^ (wordsize - 1))))) =
      WordCore.repr wordsize zZero
    rw [hq]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_zero_proof : add_zero := by
  intro x
  change WordCore.add x (WordCore.zero wordsize) = x
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val]
  change (x.val + 0) % (2 ^ wordsize) = x.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt (WordCore.val_lt x)]

theorem eq_sym_proof : eq_sym := by
  intro x y
  change decide (x.intval = y.intval) = decide (y.intval = x.intval)
  by_cases h : x.intval = y.intval
  · simp [h]
  · have h' : ¬ y.intval = x.intval := by
      intro hyx
      exact h hyx.symm
    simp [h, h']

theorem not_ltu_proof : not_ltu := by
  intro x y
  change !(zltSelect (unsigned y) (unsigned x) true false) =
    (zltSelect (unsigned x) (unsigned y) true false ||
      decide (x.intval = y.intval))
  cases hxy : CompCert4Lean.Lib.Coqlib.zlt (unsigned y) (unsigned x) with
  | left hlt =>
      cases hrev : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
      | left hrevlt =>
          exact (Int.lt_asymm hlt hrevlt).elim
      | right hrevge =>
          have hne : x.intval ≠ y.intval := by
            intro heq
            have hlt' : intOfZ (unsigned y) < intOfZ (unsigned x) := hlt
            change intOfZ y.intval < intOfZ x.intval at hlt'
            rw [heq] at hlt'
            exact (Int.lt_irrefl _ hlt').elim
          have heq : eq x y = false := by
            change decide (x.intval = y.intval) = false
            simp [hne]
          simp [zltSelect, sumboolSelect, hxy, hrev, heq, hne]
  | right hge =>
      cases hrev : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
      | left hrevlt =>
          simp [zltSelect, sumboolSelect, hxy, hrev]
      | right hrevge =>
          have hge' : intOfZ (unsigned x) ≤ intOfZ (unsigned y) := by
            change intOfZ (unsigned x) ≤ intOfZ (unsigned y)
            exact hge
          have hrevge' : intOfZ (unsigned y) ≤ intOfZ (unsigned x) := by
            change intOfZ (unsigned y) ≤ intOfZ (unsigned x)
            exact hrevge
          have huv : unsigned y = unsigned x := by
            apply intOfZ_injective
            exact Int.le_antisymm hrevge' hge'
          have heqv : x.intval = y.intval := by
            simpa only [unsigned, WordCore.unsigned] using huv.symm
          have heq : eq x y = true := by
            change decide (x.intval = y.intval) = true
            rw [heqv]
            simp
          simp [zltSelect, sumboolSelect, hxy, hrev, heq, heqv]

theorem and_mone_proof : and_mone := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.and x (WordCore.mone wordsize)).val = x.val
  rw [suffix_and_val]
  unfold WordCore.mone
  rw [WordCore.val_repr_residue]
  have hz : zOpp zOne = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-1) := by
    rfl
  rw [hz, WordCore.residue_zOfInt]
  have hmask : ((-1 : Int) % Int.ofNat (2 ^ wordsize)).toNat =
      2 ^ wordsize - 1 := by
    change ((-1 : Int) % Int.ofNat (2 ^ 32)).toNat = 2 ^ 32 - 1
    decide
  change x.val.land ((-1 % Int.ofNat (2 ^ wordsize)).toNat) = x.val
  rw [hmask]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (WordCore.val_lt x)

theorem repr_unsigned_proof : repr_unsigned := by
  intro i
  have hnonneg : zLe zZero (unsigned i) := by
    have h := i.intrange.1
    change (-1 : Int) < intOfZ (unsigned i) at h
    change 0 ≤ intOfZ (unsigned i)
    omega
  have hlt : zLt (unsigned i) modulus := i.intrange.2
  have hmax : zLe (unsigned i) max_unsigned := by
    change intOfZ (unsigned i) ≤ intOfZ max_unsigned
    change intOfZ (unsigned i) < intOfZ modulus at hlt
    change intOfZ (unsigned i) < (2 ^ wordsize : Int) at hlt
    change intOfZ (unsigned i) ≤ (2 ^ wordsize : Int) - 1
    omega
  apply WordCore.ext
  exact unsigned_repr_proof_api (unsigned i) ⟨hnonneg, hmax⟩

theorem and_commut_proof : and_commut := by
  intro x y
  apply WordCore.ext_of_val_eq
  change (WordCore.and x y).val = (WordCore.and y x).val
  rw [suffix_and_val, suffix_and_val, Nat.land_eq, Nat.land_eq, Nat.and_comm]

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_shl_val (x y : int) :
    (WordCore.shl x y).val = (x.val * 2 ^ y.val) % (2 ^ wordsize) := by
  change (WordCore.repr wordsize
    (zShiftl (unsigned x) (unsigned y))).val = _
  have hunsigned (w : int) :
      unsigned w = zOfNat w.val := by
    have hw : zLe zZero (unsigned w) := by
      have h := w.intrange.1
      change (-1 : Int) < intOfZ (unsigned w) at h
      change 0 ≤ intOfZ (unsigned w)
      omega
    exact (ZArith.Znat.Z2Nat.id (unsigned w) hw).symm
  rw [hunsigned x, hunsigned y]
  rw [show zShiftl (zOfNat x.val) (zOfNat y.val) =
      zOfNat (x.val * 2 ^ y.val) by
    unfold zShiftl ZArith.BinInt.Z.shiftl
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte]
    rw [Int.natCast_mul, Int.natCast_pow]
    rfl]
  rw [WordCore.val_repr_residue]
  have hz : zOfNat (x.val * 2 ^ y.val) =
      zOfInt (Int.ofNat (x.val * 2 ^ y.val)) := by rfl
  rw [hz, WordCore.residue_zOfNat]

private theorem suffix_shl_and (x m y : int) :
    shl (and x m) y = and (shl x y) (shl m y) := by
  change WordCore.shl (WordCore.and x m) y =
    WordCore.and (WordCore.shl x y) (WordCore.shl m y)
  apply WordCore.ext_of_val_eq
  rw [suffix_shl_val, suffix_and_val]
  rw [suffix_and_val (WordCore.shl x y) (WordCore.shl m y)]
  rw [suffix_shl_val x y, suffix_shl_val m y]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.land_eq]
  rw [Nat.testBit_mod_two_pow]
  rw [Nat.testBit_and]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq]
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  rw [Nat.testBit_and]
  by_cases hi : i < wordsize
  · by_cases hshift : decide (y.val ≤ i) = true
    · simp [hi, hshift, Bool.and_assoc]
    · simp [hi, hshift, Bool.and_assoc]
  · simp [hi]

theorem bitfield_insert_alternative_proof : bitfield_insert_alternative := by
  dsimp [bitfield_insert_alternative]
  intro pos width n p hwidth
  let mask := shl (repr (zSub (zTwoP width) zOne)) (repr pos)
  change or (shl (zero_ext width p) (repr pos)) (and n (not mask)) =
    or (and (shl p (repr pos)) mask) (and n (not mask))
  rw [zero_ext_and_proof width p hwidth]
  exact congrArg (fun q => or q (and n (not mask)))
    (suffix_shl_and p (repr (zSub (zTwoP width) zOne)) (repr pos))

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_zshiftr_div_any (x y : Z) (hy : zLe zZero y) :
    zShiftr x y = zDiv x (zTwoP y) := by
  change 0 ≤ intOfZ y at hy
  have hpow : intOfZ (zTwoP y) =
      Int.pow 2 (Int.toNat (intOfZ y)) := by
    unfold zTwoP two_p CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p
    change intOfZ (if intOfZ y < 0 then Numbers.BinNums.Z.Z0 else
      zOfInt (Int.pow 2 (Int.toNat (intOfZ y)))) = _
    rw [if_neg (by omega)]
    rw [intOfZ_zOfInt]
  apply intOfZ_injective
  simp [zShiftr, zDiv,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.shiftr,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div, hy]
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
  have hp : 0 < Int.pow 2 (Int.toNat (intOfZ y)) := by
    exact Int.pow_pos (by omega)
  simp [hp, Int.ne_of_gt hp]

theorem shr_div_two_p_proof : shr_div_two_p := by
  intro x y
  change WordCore.repr wordsize
      (zShiftr (signed x) (unsigned y)) =
    WordCore.repr wordsize (zDiv (signed x) (zTwoP (unsigned y)))
  have hy : zLe zZero (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega
  rw [suffix_zshiftr_div_any (signed x) (unsigned y) hy]

private theorem suffix_or_val (x y : int) :
    (WordCore.or x y).val = Nat.lor x.val y.val := by
  unfold WordCore.or
  have hz : zOfNat (Nat.lor x.val y.val) =
      zOfInt (Int.ofNat (Nat.lor x.val y.val)) := by rfl
  rw [hz, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt
    (Nat.or_lt_two_pow (WordCore.val_lt x) (WordCore.val_lt y))

private theorem suffix_not_val (x : int) :
    (WordCore.not x).val = Nat.xor x.val (2 ^ wordsize - 1) := by
  unfold WordCore.not
  have hz : zOfNat (Nat.xor x.val (2 ^ wordsize - 1)) =
      zOfInt (Int.ofNat (Nat.xor x.val (2 ^ wordsize - 1))) := by rfl
  rw [hz, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  apply Nat.mod_eq_of_lt
  apply Nat.xor_lt_two_pow (WordCore.val_lt x)
  have hpow : 0 < 2 ^ wordsize := Nat.two_pow_pos wordsize
  omega

private theorem suffix_nat_not_or (x y n : Nat)
    (hxlt : x < 2 ^ n) (hylt : y < 2 ^ n) :
    Nat.xor (Nat.lor x y) (2 ^ n - 1) =
      Nat.land (Nat.xor x (2 ^ n - 1)) (Nat.xor y (2 ^ n - 1)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.xor_eq, Nat.lor_eq, Nat.land_eq]
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and]
  rw [Nat.testBit_xor, Nat.testBit_xor]
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hi : i < n
  · by_cases hx : x.testBit i = true <;>
      by_cases hy : y.testBit i = true <;> simp [hi, hx, hy]
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    have hpow : 2 ^ n ≤ 2 ^ i :=
      Nat.pow_le_pow_right Nat.zero_lt_two hni
    have hxi : x < 2 ^ i := Nat.lt_of_lt_of_le hxlt hpow
    have hyi : y < 2 ^ i := Nat.lt_of_lt_of_le hylt hpow
    rw [Nat.testBit_lt_two_pow hxi, Nat.testBit_lt_two_pow hyi]
    simp [hi]

theorem not_or_and_not_proof : not_or_and_not := by
  intro x y
  apply WordCore.ext_of_val_eq
  change (WordCore.not (WordCore.or x y)).val =
    (WordCore.and (WordCore.not x) (WordCore.not y)).val
  rw [suffix_not_val, suffix_or_val, suffix_and_val,
    suffix_not_val, suffix_not_val]
  exact suffix_nat_not_or x.val y.val wordsize
    (WordCore.val_lt x) (WordCore.val_lt y)

theorem divu_one_proof : divu_one := by
  intro x
  change WordCore.repr wordsize
      (zDiv (unsigned x) (unsigned one)) = x
  have hone : unsigned one = zOne := by rfl
  rw [hone]
  have hdiv : zDiv (unsigned x) zOne = unsigned x := by
    apply intOfZ_injective
    simp only [zDiv, ZArith.BinInt.Z.div, intOfZ_zOfInt]
    change (intOfZ (unsigned x)).ediv 1 = intOfZ (unsigned x)
    exact Int.ediv_one _
  rw [hdiv]
  exact repr_unsigned_proof x

theorem signed_range_proof : signed_range := by
  intro x
  unfold signed WordCore.signed
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left h =>
      simp only [zltSelect, sumboolSelect, hlt]
      constructor
      · have hx0 : 0 ≤ intOfZ (unsigned x) := by
          have hx := x.intrange.1
          change (-1 : Int) < intOfZ (unsigned x) at hx
          omega
        change intOfZ min_signed ≤ intOfZ (unsigned x)
        change (-2147483648 : Int) ≤ intOfZ (unsigned x)
        omega
      · change intOfZ (unsigned x) ≤ intOfZ max_signed
        change intOfZ (unsigned x) < intOfZ half_modulus at h
        change intOfZ (unsigned x) < (2147483648 : Int) at h
        change intOfZ (unsigned x) ≤ (2147483647 : Int)
        omega
  | right h =>
      simp only [zltSelect, sumboolSelect, hlt]
      have hxlt := x.intrange.2
      change intOfZ (unsigned x) < intOfZ modulus at hxlt
      change intOfZ (unsigned x) < (4294967296 : Int) at hxlt
      change intOfZ half_modulus ≤ intOfZ (unsigned x) at h
      change (2147483648 : Int) ≤ intOfZ (unsigned x) at h
      constructor
      · change intOfZ min_signed ≤ intOfZ (zSub (unsigned x) modulus)
        simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change (-2147483648 : Int) ≤
          intOfZ (unsigned x) - (4294967296 : Int)
        omega
      · change intOfZ (zSub (unsigned x) modulus) ≤ intOfZ max_signed
        simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change intOfZ (unsigned x) - (4294967296 : Int) ≤
          (2147483647 : Int)
        omega

private theorem suffix_shru_val (x y : int) :
    (shru x y).val = x.val / 2 ^ y.val := by
  unfold shru WordCore.shru
  change (WordCore.repr wordsize
      (ZArith.BinInt.Z.shiftr x.intval y.intval)).val = _
  rw [WordCore.intval_eq_zOfNat_val x, WordCore.intval_eq_zOfNat_val y]
  have hshift : ZArith.BinInt.Z.shiftr (zOfNat x.val) (zOfNat y.val) =
      zOfNat (x.val / 2 ^ y.val) := by
    unfold ZArith.BinInt.Z.shiftr
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
      Int.toNat_natCast, Int.natCast_pow]
    exact congrArg zOfInt Int.ofNat_ediv_ofNat
  rw [hshift, WordCore.val_repr_residue]
  have hzof : zOfNat (x.val / 2 ^ y.val) =
      zOfInt (Int.ofNat (x.val / 2 ^ y.val)) := by rfl
  rw [hzof, WordCore.residue_zOfNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self x.val _) (WordCore.val_lt x)

private theorem suffix_ltu_iwordsize_val (n : int)
    (h : ltu n iwordsize = true) : n.val < wordsize := by
  have hlt := (ltu_inv_proof n iwordsize h).2
  change ZArith.BinInt.Z.lt n.intval iwordsize.intval at hlt
  rw [WordCore.intval_eq_zOfNat_val n,
    WordCore.intval_eq_zOfNat_val iwordsize] at hlt
  have hi : iwordsize.val = wordsize := rfl
  rw [hi] at hlt
  change intOfZ (ZArith.BinInt.Z.of_nat n.val) <
    intOfZ (ZArith.BinInt.Z.of_nat wordsize) at hlt
  rw [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
  exact Int.ofNat_lt.mp hlt

theorem shru_shru_proof : shru_shru := by
  intro x y z hy hz _hsum
  have hyv := suffix_ltu_iwordsize_val y hy
  have hzv := suffix_ltu_iwordsize_val z hz
  have hyzlt : y.val + z.val < 2 ^ wordsize := by
    change y.val < 32 at hyv
    change z.val < 32 at hzv
    change y.val + z.val < 2 ^ 32
    omega
  apply WordCore.ext_of_val_eq
  rw [suffix_shru_val, suffix_shru_val, suffix_shru_val]
  change x.val / 2 ^ y.val / 2 ^ z.val =
    x.val / 2 ^ (WordCore.add y z).val
  rw [WordCore.add_val, Nat.mod_eq_of_lt hyzlt]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

private def suffixSignStep : (Z → Z) → Z → Z :=
  fun rec y => CompCert4Lean.Lib.Zbits.Zshiftin
    (ZArith.BinInt.Z.odd y) (rec (ZArith.BinInt.Z.div2 y))

private def suffixSignBase : Z → Z :=
  fun y => if ZArith.BinInt.Z.odd y then zOpp zOne else zZero

private theorem suffix_intOfZ_shiftin (b : Bool) (x : Z) :
    intOfZ (CompCert4Lean.Lib.Zbits.Zshiftin b x) =
      2 * intOfZ x + if b then 1 else 0 := by
  rw [CompCert4Lean.Lib.Zbits.Zshiftin_spec]
  simp only [zAdd, zMul, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  cases b <;> rfl

private theorem suffix_odd_zOfNat (a : Nat) :
    ZArith.BinInt.Z.odd (zOfNat a) = decide (a % 2 = 1) := by
  unfold ZArith.BinInt.Z.odd ZArith.BinInt.Z.even
  rw [zNatAbs_nat]
  have hrange := Nat.mod_lt a (by decide : 0 < 2)
  by_cases h : a % 2 = 1
  · simp [h]
  · have hz : a % 2 = 0 := by omega
    simp [h, hz]

private theorem suffix_sign_iter_nat (k a : Nat) :
    intOfZ (ZArith.BinInt.Z.iter (zOfNat k)
      suffixSignStep suffixSignBase (zOfNat a)) =
      if a % (2 ^ (k + 1)) < 2 ^ k then
        Int.ofNat (a % (2 ^ (k + 1)))
      else
        Int.ofNat (a % (2 ^ (k + 1))) - Int.ofNat (2 ^ (k + 1)) := by
  induction k generalizing a with
  | zero =>
      change intOfZ (suffixSignBase (zOfNat a)) = _
      unfold suffixSignBase
      rw [suffix_odd_zOfNat]
      by_cases h : a % 2 = 1
      · have hr : a % 2 = 1 := h
        simp [suffixSignBase, h, hr]
        rfl
      · have hr : a % 2 = 0 := by omega
        simp [suffixSignBase, h, hr]
        rfl
  | succ k ih =>
      rw [ziter_succ suffixSignStep suffixSignBase k]
      change intOfZ (CompCert4Lean.Lib.Zbits.Zshiftin
        (ZArith.BinInt.Z.odd (zOfNat a))
        (ZArith.BinInt.Z.iter (zOfNat k) suffixSignStep suffixSignBase
          (ZArith.BinInt.Z.div2 (zOfNat a)))) = _
      rw [zdiv2_nat, suffix_intOfZ_shiftin, ih]
      rw [suffix_odd_zOfNat]
      let q := (a / 2) % 2 ^ (k + 1)
      let r := a % 2 ^ (k + 2)
      change 2 * (if q < 2 ^ k then Int.ofNat q
          else Int.ofNat q - Int.ofNat (2 ^ (k + 1))) +
          (if decide (a % 2 = 1) then 1 else 0) =
        if r < 2 ^ (k + 1) then Int.ofNat r
          else Int.ofNat r - Int.ofNat (2 ^ (k + 2))
      have hr : 2 * q + a % 2 = r := by
        have hm := Nat.mod_mul (a := 2) (b := 2 ^ (k + 1)) (x := a)
        simpa [q, r, Nat.pow_succ, Nat.add_comm, Nat.mul_comm,
          Nat.mul_left_comm] using hm.symm
      have hpNat : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
        rw [show k + 2 = (k + 1) + 1 by omega, Nat.pow_succ]
        omega
      have hpInt := congrArg Int.ofNat hpNat
      simp only [Int.ofNat_eq_natCast, Int.natCast_mul] at hpInt
      have hbit : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases hbit with hbit | hbit
      · have hodd : decide (a % 2 = 1) = false := by simp [hbit]
        rw [hodd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hq : q < 2 ^ k
        · have hrl : r < 2 ^ (k + 1) := by
            rw [← hr, hbit]
            simp only [Nat.add_zero]
            omega
          rw [if_pos hq, if_pos hrl]
          have hrInt := congrArg Int.ofNat hr
          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
            Int.natCast_mul] at hrInt
          simp only [Int.ofNat_eq_natCast]
          omega

        · have hrl : ¬ r < 2 ^ (k + 1) := by
            intro hrl
            rw [← hr, hbit] at hrl
            simp only [Nat.add_zero] at hrl
            omega
          rw [if_neg hq, if_neg hrl]
          have hrInt := congrArg Int.ofNat hr
          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
            Int.natCast_mul] at hrInt
          simp only [Int.ofNat_eq_natCast]
          omega
      · have hodd : decide (a % 2 = 1) = true := by simp [hbit]
        rw [hodd]
        simp only [↓reduceIte]
        by_cases hq : q < 2 ^ k
        · have hrl : r < 2 ^ (k + 1) := by
            rw [← hr, hbit]
            omega
          rw [if_pos hq, if_pos hrl]
          have hrInt := congrArg Int.ofNat hr
          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
            Int.natCast_mul] at hrInt
          simp only [Int.ofNat_eq_natCast]
          omega
        · have hrl : ¬ r < 2 ^ (k + 1) := by
            intro hrl
            rw [← hr, hbit] at hrl
            omega
          rw [if_neg hq, if_neg hrl]
          have hrInt := congrArg Int.ofNat hr
          simp only [Int.ofNat_eq_natCast, Int.natCast_add,
            Int.natCast_mul] at hrInt
          simp only [Int.ofNat_eq_natCast]
          omega

private theorem suffix_sign_ext_nat (k : Nat) (x : int) :
    sign_ext (zOfNat (k + 1)) x =
      WordCore.repr wordsize (zOfInt
        (if x.val % (2 ^ (k + 1)) < 2 ^ k then
          Int.ofNat (x.val % (2 ^ (k + 1)))
        else
          Int.ofNat (x.val % (2 ^ (k + 1))) - Int.ofNat (2 ^ (k + 1)))) := by
  have hpred : ZArith.BinInt.Z.pred (zOfNat (k + 1)) = zOfNat k := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.pred, ZArith.BinInt.Z.sub,
      intOfZ_zOfInt, zOfNat, ZArith.BinInt.Z.of_nat]
    change Int.ofNat (k + 1) - 1 = Int.ofNat k
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
    omega
  have hsel : sumboolSelect
      (CompCert4Lean.Lib.Coqlib.zlt zZero (zOfNat (k + 1)))
      (zOpp zOne) zZero = zOpp zOne := by
    cases hs : CompCert4Lean.Lib.Coqlib.zlt zZero (zOfNat (k + 1)) with
    | left _ => rfl
    | right h =>
        exfalso
        change intOfZ (zOfNat (k + 1)) ≤ 0 at h
        have hz : intOfZ (zOfNat (k + 1)) = Int.ofNat (k + 1) := by
          simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
            intOfZ_zOfInt (Int.ofNat (k + 1))
        rw [hz] at h
        have hk : 0 < Int.ofNat (k + 1) := by
          rw [Int.ofNat_eq_natCast]
          exact Int.natCast_pos.mpr (by omega)
        exact (Int.not_le_of_gt hk) h
  unfold sign_ext WordCore.sign_ext
  rw [hpred]
  dsimp only
  simp only [hsel]
  unfold WordCore.unsigned
  rw [WordCore.intval_eq_zOfNat_val x]
  change WordCore.repr wordsize
      (ZArith.BinInt.Z.iter (zOfNat k) suffixSignStep suffixSignBase
        (zOfNat x.val)) = _
  apply congrArg (WordCore.repr wordsize)
  apply intOfZ_injective
  rw [intOfZ_zOfInt]
  exact suffix_sign_iter_nat k x.val

private theorem suffix_signed_int (x : int) :
    intOfZ (signed x) =
      if x.val < 2 ^ (wordsize - 1) then Int.ofNat x.val
      else Int.ofNat x.val - Int.ofNat (2 ^ wordsize) := by
  unfold signed WordCore.signed
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left h =>
      simp only [zltSelect, sumboolSelect, hlt]
      have hvlt : x.val < 2 ^ (wordsize - 1) := by
        change intOfZ x.intval < intOfZ (zTwoPowerNat (wordsize - 1)) at h
        rw [WordCore.intval_eq_zOfNat_val x] at h
        have hval : intOfZ (zOfNat x.val) = Int.ofNat x.val := by
          simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
            intOfZ_zOfInt (Int.ofNat x.val)
        have hpow : intOfZ (zTwoPowerNat (wordsize - 1)) =
            Int.ofNat (2 ^ (wordsize - 1)) := by rfl
        rw [hval, hpow] at h
        exact Int.ofNat_lt.mp h
      rw [if_pos hvlt]
      change intOfZ x.intval = Int.ofNat x.val
      rw [WordCore.intval_eq_zOfNat_val x]
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat x.val)
  | right h =>
      simp only [zltSelect, sumboolSelect, hlt]
      have hvge : ¬ x.val < 2 ^ (wordsize - 1) := by
        intro hvlt
        change intOfZ (zTwoPowerNat (wordsize - 1)) ≤ intOfZ x.intval at h
        rw [WordCore.intval_eq_zOfNat_val x] at h
        have hval : intOfZ (zOfNat x.val) = Int.ofNat x.val := by
          simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
            intOfZ_zOfInt (Int.ofNat x.val)
        have hpow : intOfZ (zTwoPowerNat (wordsize - 1)) =
            Int.ofNat (2 ^ (wordsize - 1)) := by rfl
        rw [hval, hpow] at h
        exact (Int.not_le_of_gt (Int.ofNat_lt.mpr hvlt)) h
      rw [if_neg hvge]
      simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      change intOfZ x.intval - intOfZ (zTwoPowerNat wordsize) = _
      rw [WordCore.intval_eq_zOfNat_val x]
      have hval : intOfZ (zOfNat x.val) = Int.ofNat x.val := by
        simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
          intOfZ_zOfInt (Int.ofNat x.val)
      have hpow : intOfZ (zTwoPowerNat wordsize) =
          Int.ofNat (2 ^ wordsize) := by rfl
      rw [hval, hpow]

private theorem suffix_shr_shl_nat (k : Nat) (hk : k < 32) (x : int) :
    let y := repr (zOfNat (31 - k))
    shr (shl x y) y =
      WordCore.repr wordsize (zOfInt
        (if x.val % (2 ^ (k + 1)) < 2 ^ k then
          Int.ofNat (x.val % (2 ^ (k + 1)))
        else
          Int.ofNat (x.val % (2 ^ (k + 1))) - Int.ofNat (2 ^ (k + 1)))) := by
  let s := 31 - k
  let y := repr (zOfNat s)
  change shr (shl x y) y = _
  have hks : k + s = 31 := by dsimp [s]; omega
  have hk1s : (k + 1) + s = 32 := by omega
  have hpHalf : 2 ^ 31 = 2 ^ k * 2 ^ s := by
    rw [← Nat.pow_add, hks]
  have hpFull : 2 ^ 32 = 2 ^ (k + 1) * 2 ^ s := by
    rw [← Nat.pow_add, hk1s]
  have hyval : y.val = s := by
    dsimp [y]
    unfold repr
    change (WordCore.repr wordsize (zOfNat s)).val = s
    rw [WordCore.val_repr_residue]
    have hzof : zOfNat s = zOfInt (Int.ofNat s) := by rfl
    rw [hzof, WordCore.residue_zOfNat]
    apply Nat.mod_eq_of_lt
    change s < 2 ^ 32
    dsimp [s]
    omega
  have hyunsigned : unsigned y = zOfNat s := by
    change y.intval = zOfNat s
    rw [WordCore.intval_eq_zOfNat_val y, hyval]
  let r := x.val % 2 ^ (k + 1)
  have hrange : r < 2 ^ (k + 1) := by
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hb : (shl x y).val = r * 2 ^ s := by
    change (WordCore.shl x y).val = _
    rw [suffix_shl_val, hyval]
    change (x.val * 2 ^ s) % 2 ^ 32 = r * 2 ^ s
    rw [hpFull]
    exact Nat.mul_mod_mul_right (2 ^ s) x.val (2 ^ (k + 1))
  change WordCore.repr wordsize
      (zShiftr (signed (shl x y)) (unsigned y)) = _
  apply congrArg (WordCore.repr wordsize)
  apply intOfZ_injective
  rw [hyunsigned, intOfZ_zOfInt]
  unfold zShiftr ZArith.BinInt.Z.shiftr
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
    Int.ofNat_eq_natCast, Int.natCast_nonneg, ↓reduceIte,
    Int.toNat_natCast]
  rw [suffix_signed_int, hb]
  change (if r * 2 ^ s < 2 ^ 31 then Int.ofNat (r * 2 ^ s)
      else Int.ofNat (r * 2 ^ s) - Int.ofNat (2 ^ 32)) /
      Int.pow 2 s =
    if r < 2 ^ k then Int.ofNat r
      else Int.ofNat r - Int.ofNat (2 ^ (k + 1))
  have hpowpos : 0 < Int.pow 2 s := Int.pow_pos (by omega)
  have hcastmul (a : Nat) : Int.ofNat (a * 2 ^ s) =
      Int.ofNat a * Int.pow 2 s := by
    calc
      Int.ofNat (a * 2 ^ s) = Int.ofNat a * Int.ofNat (2 ^ s) := by
        exact Int.natCast_mul a (2 ^ s)
      _ = Int.ofNat a * Int.pow 2 s :=
        congrArg (fun q : Int => Int.ofNat a * q) (Int.natCast_pow 2 s)
  have hbInt := hcastmul r
  have hpFullInt : Int.ofNat (2 ^ 32) =
      Int.ofNat (2 ^ (k + 1)) * Int.pow 2 s := by
    calc
      Int.ofNat (2 ^ 32) = Int.ofNat (2 ^ (k + 1) * 2 ^ s) :=
        congrArg Int.ofNat hpFull
      _ = _ := hcastmul (2 ^ (k + 1))
  by_cases hrlt : r < 2 ^ k
  · have hblt : r * 2 ^ s < 2 ^ 31 := by
      rw [hpHalf]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos s)).2 hrlt
    rw [if_pos hblt, if_pos hrlt, hbInt]
    exact Int.mul_ediv_cancel _ (Int.ne_of_gt hpowpos)
  · have hrge : 2 ^ k ≤ r := Nat.le_of_not_gt hrlt
    have hbge : 2 ^ 31 ≤ r * 2 ^ s := by
      rw [hpHalf]
      exact Nat.mul_le_mul_right (2 ^ s) hrge
    have hbnlt : ¬ r * 2 ^ s < 2 ^ 31 := Nat.not_lt_of_ge hbge
    rw [if_neg hbnlt, if_neg hrlt, hbInt, hpFullInt, ← Int.sub_mul]
    exact Int.mul_ediv_cancel _ (Int.ne_of_gt hpowpos)

theorem sign_ext_shr_shl_proof : sign_ext_shr_shl := by
  intro n x hn
  have hn0 : zLe zZero n := by
    change 0 ≤ intOfZ n
    have h := hn.1
    change 0 < intOfZ n at h
    exact Int.le_of_lt h
  let m := zToNat n
  have hnrepr : n = zOfNat m := by
    exact (ZArith.Znat.Z2Nat.id n hn0).symm
  have hmpos : 0 < m := by
    have h := hn.1
    rw [hnrepr] at h
    change 0 < intOfZ (zOfNat m) at h
    have hz : intOfZ (zOfNat m) = Int.ofNat m := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat m)
    rw [hz] at h
    exact Int.ofNat_lt.mp h
  have hmle : m ≤ 32 := by
    have h := hn.2
    rw [hnrepr] at h
    change intOfZ (zOfNat m) ≤ intOfZ zwordsize at h
    have hz : intOfZ (zOfNat m) = Int.ofNat m := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat m)
    rw [hz] at h
    change Int.ofNat m ≤ 32 at h
    exact Int.ofNat_le.mp h
  let k := m - 1
  have hk : k < 32 := by dsimp [k]; omega
  have hmk : k + 1 = m := by dsimp [k]; omega
  have hnk : n = zOfNat (k + 1) := by rw [hnrepr, hmk]
  have hdiff : zSub zwordsize n = zOfNat (31 - k) := by
    rw [hnk]
    apply intOfZ_injective
    simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    have hw : intOfZ zwordsize = (32 : Int) := by rfl
    have hkz : intOfZ (zOfNat (k + 1)) = Int.ofNat (k + 1) := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat (k + 1))
    have hrz : intOfZ (zOfNat (31 - k)) = Int.ofNat (31 - k) := by
      simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
        intOfZ_zOfInt (Int.ofNat (31 - k))
    rw [hw, hkz, hrz]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
    omega
  rw [hdiff, hnk]
  exact (suffix_sign_ext_nat k x).trans (suffix_shr_shl_nat k hk x).symm

theorem bits_one_proof : bits_one := by
  intro n
  cases n with
  | Zneg p =>
      rfl
  | Z0 =>
      rfl
  | Zpos p =>
      unfold testbit one WordCore.testbit
      have hneq : (Numbers.BinNums.Z.Zpos p) ≠ zZero := by
        intro h
        cases h
      cases hz : CompCert4Lean.Lib.Coqlib.zeq
          (Numbers.BinNums.Z.Zpos p) zZero with
      | left heq => exact (hneq heq).elim
      | right hne =>
          simp only [sumboolSelect, hz]
          change Nat.testBit (WordCore.one wordsize).val
              (WordCore.positiveToNat p) = false
          have hone : (WordCore.one wordsize).val = 1 := by
            unfold WordCore.one
            rw [WordCore.val_repr_residue]
            rfl
          rw [hone]
          have hp : 0 < WordCore.positiveToNat p := by
            rw [WordCore.positiveToNat_eq_posToNat]
            exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
          rw [Nat.testBit_lt_two_pow
            (Nat.one_lt_two_pow (Nat.ne_of_gt hp))]

private theorem suffix_mone_val : (WordCore.mone wordsize).val = 2 ^ wordsize - 1 := by
  unfold WordCore.mone
  rw [WordCore.val_repr_residue]
  have hz : zOpp zOne =
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (-1) := by
    rfl
  rw [hz, WordCore.residue_zOfInt]
  change ((-1 : Int) % Int.ofNat (2 ^ wordsize)).toNat = 2 ^ wordsize - 1
  decide

theorem bits_mone_proof : bits_mone := by
  intro i hi
  have hmone := suffix_mone_val
  cases i with
  | Zneg p =>
      have h := hi.1
      have hp := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      simp only [zLe, ZArith.BinInt.Z.le, intOfZ, posToNat] at h
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      have hneg : -Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) < 0 := by
        omega
      exact ((Int.not_lt_of_ge h) hneg).elim
  | Z0 =>
      unfold testbit WordCore.testbit
      change Nat.testBit (WordCore.mone wordsize).val 0 = true
      rw [hmone]
      decide
  | Zpos p =>
      unfold testbit WordCore.testbit
      change Nat.testBit (WordCore.mone wordsize).val
        (WordCore.positiveToNat p) = true
      rw [WordCore.positiveToNat_eq_posToNat]
      rw [hmone]
      have hlt := hi.2
      change intOfZ (Numbers.BinNums.Z.Zpos p) < intOfZ (zOfNat wordsize) at hlt
      simp only [intOfZ, posToNat, zOfNat,
        ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
      have hnat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize :=
        Int.ofNat_lt.mp hlt
      simpa [hnat] using Nat.testBit_two_pow_sub_one wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

theorem is_power2_range_proof : is_power2_range := by
  intro n logn hpow
  unfold is_power2 at hpow
  cases hu : unsigned n with
  | Z0 =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zneg p =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zpos p =>
      cases hp : CompCert4Lean.Lib.Zbits.P_is_power2 p with
      | false =>
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu, hp] at hpow
          cases hpow
      | true =>
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu, hp, ↓reduceIte] at hpow
          injection hpow with hlogn
          subst logn
          change ltu (repr (ZArith.BinInt.Z.log2
            (Numbers.BinNums.Z.Zpos p))) iwordsize = true
          have hbound : zLt (unsigned n) modulus := n.intrange.2
          rw [hu] at hbound
          change intOfZ (Numbers.BinNums.Z.Zpos p) < intOfZ modulus at hbound
          unfold modulus at hbound
          rw [WordCore.twoPowerNat_eq_zOfNat_twoPow] at hbound
          simp only [intOfZ, posToNat, zOfNat,
            ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hbound
          have hpbound :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p <
                2 ^ wordsize := Int.ofNat_lt.mp hbound
          have hpne :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p ≠ 0 :=
            Nat.ne_of_gt
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
          have hlog :
              Nat.log2 (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) <
                wordsize := (Nat.log2_lt hpne).2 hpbound
          have hzlog : ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p) =
              zOfInt (Int.ofNat (Nat.log2
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))) := by
            unfold ZArith.BinInt.Z.log2
            have hpcast : intOfZ (Numbers.BinNums.Z.Zpos p) =
                Int.ofNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
              rfl
            rw [hpcast]
            have htoNat : Int.toNat
                (Int.ofNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
              simp
            rw [htoNat]
          have hzrange :
              zLe zZero (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)) ∧
                zLe (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)) max_unsigned := by
            rw [hzlog]
            constructor
            · change (0 : Int) ≤ intOfZ
                (zOfInt (Int.ofNat (Nat.log2
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))))
              rw [intOfZ_zOfInt]
              exact Int.natCast_nonneg _
            · change intOfZ (zOfInt (Int.ofNat (Nat.log2
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))) ≤
                intOfZ max_unsigned
              rw [intOfZ_zOfInt]
              have hmax : intOfZ max_unsigned =
                  (2 ^ wordsize : Int) - 1 := by
                unfold max_unsigned
                unfold modulus
                rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
                simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
                  ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
                have hone : intOfZ zOne = (1 : Int) := by rfl
                rw [hone]
                rfl
              rw [hmax]
              have hword : wordsize = 32 := by rfl
              rw [hword] at hlog ⊢
              have hpowcast : (2 ^ 32 : Int) - 1 =
                  Int.ofNat (2 ^ 32 - 1) := by decide
              rw [hpowcast]
              apply Int.ofNat_le.mpr
              omega
          have hrepr := unsigned_repr_proof_api
            (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)) hzrange
          have hword : unsigned iwordsize = zwordsize := by
            exact unsigned_repr_wordsize_proof
          have hlt : zLt
              (unsigned (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p))))
              (unsigned iwordsize) := by
            rw [hrepr, hword, hzlog]
            change intOfZ (zOfInt (Int.ofNat (Nat.log2
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)))) <
              intOfZ zwordsize
            rw [intOfZ_zOfInt]
            unfold zwordsize
            simp only [zOfNat, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt]
            exact Int.ofNat_lt.mpr hlog
          change zltSelect
            (unsigned (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p))))
            (unsigned iwordsize) true false = true
          cases hs : CompCert4Lean.Lib.Coqlib.zlt
              (unsigned (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p))))
              (unsigned iwordsize) with
          | left hslt =>
              simp [zltSelect, sumboolSelect, hs]
          | right hsge =>
              change intOfZ (unsigned iwordsize) ≤
                intOfZ (unsigned
                  (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)))) at hsge
              change intOfZ (unsigned
                  (repr (ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p)))) <
                intOfZ (unsigned iwordsize) at hlt
              exact ((Int.not_lt_of_ge hsge) hlt).elim

theorem sign_ext_idem_proof : sign_ext_idem := by
  intro n x hn
  have hn0 : zLe zZero n := by
    change 0 ≤ intOfZ n
    exact Int.le_of_lt hn
  have hnrepr : n = zOfNat (zToNat n) :=
    (ZArith.Znat.Z2Nat.id n hn0).symm
  let m := zToNat n
  have hmpos : 0 < m := by
    rw [show m = zToNat n by rfl]
    have h := hn
    rw [hnrepr] at h
    change 0 < intOfZ (zOfNat m) at h
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at h
    exact Int.ofNat_lt.mp h
  let k := m - 1
  have hmk : k + 1 = m := by dsimp [k]; omega
  have hnk : n = zOfNat (k + 1) := by rw [hnrepr, hmk]
  rw [hnk]
  by_cases hk : k < wordsize
  · have h1 := suffix_sign_ext_nat k x
    have h2 := suffix_sign_ext_nat k (sign_ext (zOfNat (k + 1)) x)
    have hvalmod :
        (sign_ext (zOfNat (k + 1)) x).val % 2 ^ (k + 1) =
          x.val % 2 ^ (k + 1) := by
      rw [h1, WordCore.val_repr]
      by_cases hrlt : x.val % 2 ^ (k + 1) < 2 ^ k
      · rw [if_pos hrlt]
        change Int.toNat
            (Int.ofNat (x.val % 2 ^ (k + 1)) % Int.ofNat (2 ^ wordsize)) %
              2 ^ (k + 1) = x.val % 2 ^ (k + 1)
        have hr32 : x.val % 2 ^ (k + 1) < 2 ^ wordsize := by
          have hk1 : k + 1 ≤ wordsize := by omega
          exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.pow_le_pow_right Nat.zero_lt_two hk1)
        have hmod : Int.ofNat (x.val % 2 ^ (k + 1)) %
            Int.ofNat (2 ^ wordsize) =
              Int.ofNat ((x.val % 2 ^ (k + 1)) % 2 ^ wordsize) := by
          exact (Int.natCast_emod _ _).symm
        rw [hmod, Nat.mod_eq_of_lt hr32]
        change (x.val % 2 ^ (k + 1)) % 2 ^ (k + 1) = x.val % 2 ^ (k + 1)
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))
      · rw [if_neg hrlt]
        change Int.toNat
            ((Int.ofNat (x.val % 2 ^ (k + 1)) - Int.ofNat (2 ^ (k + 1))) %
              Int.ofNat (2 ^ wordsize)) % 2 ^ (k + 1) =
          x.val % 2 ^ (k + 1)
        have hk1 : k + 1 ≤ wordsize := by omega
        let r : Nat := x.val % 2 ^ (k + 1)
        let mm : Nat := 2 ^ (k + 1)
        let ww : Nat := 2 ^ wordsize
        have hrlt' : r < mm := by
          dsimp [r, mm]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        have hmmpos : 0 < mm := Nat.two_pow_pos _
        have hmmle : mm ≤ ww := by
          dsimp [mm, ww]
          exact Nat.pow_le_pow_right Nat.zero_lt_two hk1
        have hwdiv : ww % mm = 0 := by
          have hp : ww = mm * 2 ^ (wordsize - (k + 1)) := by
            dsimp [mm, ww]
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [hp, Nat.mul_mod_right]
        have ht0 : 0 ≤ (ww : Int) - mm + r := by
          have := Int.natCast_nonneg r
          have := Int.natCast_nonneg mm
          have := Int.natCast_nonneg ww
          omega
        have htw : (ww : Int) - mm + r < ww := by
          have := Int.natCast_nonneg r
          have := Int.natCast_nonneg mm
          have := Int.natCast_nonneg ww
          omega
        have hsmod :
            (Int.ofNat r - Int.ofNat mm) % Int.ofNat ww =
              (Int.ofNat ww - Int.ofNat mm + Int.ofNat r) := by
          calc
            (Int.ofNat r - Int.ofNat mm) % Int.ofNat ww =
                ((Int.ofNat r - Int.ofNat mm) + Int.ofNat ww) % Int.ofNat ww := by
                  rw [Int.add_emod_right]
            _ = (Int.ofNat ww - Int.ofNat mm + Int.ofNat r) % Int.ofNat ww := by
              congr 1 <;> omega
            _ = Int.ofNat ww - Int.ofNat mm + Int.ofNat r := by
              exact Int.emod_eq_of_lt ht0 htw
        rw [show x.val % 2 ^ (k + 1) = r by rfl,
          show 2 ^ (k + 1) = mm by rfl,
          show 2 ^ wordsize = ww by rfl, hsmod]
        have htnat : Int.toNat
            (Int.ofNat ww - Int.ofNat mm + Int.ofNat r) = ww - mm + r := by
          have heq : Int.ofNat (ww - mm + r) =
              Int.ofNat ww - Int.ofNat mm + Int.ofNat r := by
            simp only [Int.ofNat_eq_natCast, Int.natCast_add]
            rw [Int.ofNat_sub hmmle]
          rw [← heq]
          exact Int.toNat_natCast _
        rw [htnat]
        have hqpos : 0 < ww / mm := Nat.div_pos (by omega) hmmpos
        have hwmul : mm * (ww / mm) = ww := by
          have hd := Nat.mod_add_div ww mm
          rw [hwdiv] at hd
          omega
        have hdecomp : ww - mm + r = r + mm * (ww / mm - 1) := by
          rw [Nat.mul_sub_left_distrib]
          omega
        rw [hdecomp, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hrlt']
    have hR :
        WordCore.repr wordsize
            (zOfInt
              (if (sign_ext (zOfNat (k + 1)) x).val % 2 ^ (k + 1) < 2 ^ k then
                Int.ofNat ((sign_ext (zOfNat (k + 1)) x).val % 2 ^ (k + 1))
              else
                Int.ofNat ((sign_ext (zOfNat (k + 1)) x).val % 2 ^ (k + 1)) -
                  Int.ofNat (2 ^ (k + 1)))) =
          WordCore.repr wordsize
            (zOfInt
              (if x.val % 2 ^ (k + 1) < 2 ^ k then
                Int.ofNat (x.val % 2 ^ (k + 1))
              else
                Int.ofNat (x.val % 2 ^ (k + 1)) - Int.ofNat (2 ^ (k + 1)))) := by
      rw [hvalmod]
    exact (h2.trans hR).trans h1.symm
  · have hkge : wordsize ≤ k := Nat.le_of_not_gt hk
    have hxlt : x.val < 2 ^ wordsize := WordCore.val_lt x
    have hpow : 2 ^ wordsize ≤ 2 ^ k :=
      Nat.pow_le_pow_right Nat.zero_lt_two hkge
    have hr : x.val % (2 ^ (k + 1)) = x.val := by
      apply Nat.mod_eq_of_lt
      exact Nat.lt_of_lt_of_le hxlt (Nat.le_trans hpow
        (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_succ k)))
    have hcond : x.val < 2 ^ k := Nat.lt_of_lt_of_le hxlt hpow
    have h1 := suffix_sign_ext_nat k x
    have hsign : sign_ext (zOfNat (k + 1)) x =
        WordCore.repr wordsize (zOfInt (Int.ofNat x.val)) := by
      simpa [hr, hcond] using h1
    have hrepr : WordCore.repr wordsize
        (zOfInt (Int.ofNat x.val)) = x := by
      apply WordCore.ext_of_val_eq
      rw [WordCore.val_repr]
      change Int.toNat (Int.ofNat x.val % Int.ofNat (2 ^ wordsize)) = x.val
      simp only [Int.ofNat_eq_natCast]
      have hbridge := Int.emod_natAbs_of_nonneg
        (x := (x.val : Int)) (n := 2 ^ wordsize)
        (Int.natCast_nonneg _)
      simp only [Int.natAbs_natCast] at hbridge
      rw [← hbridge]
      exact Nat.mod_eq_of_lt (WordCore.val_lt x)
    rw [hrepr] at hsign
    exact congrArg (sign_ext (zOfNat (k + 1))) hsign

theorem add_commut_proof : add_commut := by
  intro x y
  change WordCore.add x y = WordCore.add y x
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val, WordCore.add_val, Nat.add_comm]

theorem and_assoc_proof : and_assoc := by
  intro x y z
  apply WordCore.ext_of_val_eq
  change (WordCore.and (WordCore.and x y) z).val =
    (WordCore.and x (WordCore.and y z)).val
  rw [suffix_and_val, suffix_and_val, suffix_and_val, suffix_and_val]
  exact Nat.and_assoc _ _ _

theorem wordsize_max_unsigned_proof : wordsize_max_unsigned := by
  change (32 : _root_.Int) ≤ (2 ^ 32 : _root_.Int) - 1
  decide

private theorem suffix_unsigned_repr_eq_exact (x : Z) :
    unsigned (repr x) = zMod x modulus := by
  change (WordCore.repr wordsize x).intval = zMod x modulus
  rw [WordCore.intval_eq_zOfNat_val]
  have hval : (WordCore.repr wordsize x).val =
      _root_.Int.toNat
        (intOfZ x % _root_.Int.ofNat (2 ^ wordsize)) := by
    have h := WordCore.val_repr wordsize (intOfZ x)
    rw [zOfInt_intOfZ x] at h
    simpa only [_root_.Int.ofNat_eq_natCast] using h
  rw [hval]
  apply intOfZ_injective
  have hmpos : (0 : _root_.Int) < intOfZ modulus := by
    change (0 : _root_.Int) < _root_.Int.ofNat (2 ^ wordsize)
    exact _root_.Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hm : intOfZ modulus = _root_.Int.ofNat (2 ^ wordsize) := by
    rfl
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  have hmod : intOfZ (zMod x modulus) =
      intOfZ x % _root_.Int.ofNat (2 ^ wordsize) := by
    have hrange := ZArith.BinInt.Z.modulo_range x modulus (by
      change (0 : _root_.Int) < intOfZ modulus
      exact hmpos)
    have hr0 : (0 : _root_.Int) ≤ intOfZ (zMod x modulus) := hrange.1
    have hrlt : intOfZ (zMod x modulus) < intOfZ modulus := hrange.2
    have hd := ZArith.Zdiv.Z_div_mod_eq_full x modulus
    have hdInt := congrArg intOfZ hd
    simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
      intOfZ_zOfInt] at hdInt
    let q := intOfZ (ZArith.BinInt.Z.div x modulus)
    let r := intOfZ (zMod x modulus)
    let m := intOfZ modulus
    have hcalc : intOfZ x % m = r := by
      calc
        intOfZ x % m = (m * q + r) % m := congrArg (fun a => a % m) hdInt
        _ = (r + q * m) % m := by rw [_root_.Int.add_comm, _root_.Int.mul_comm]
        _ = r % m := _root_.Int.add_mul_emod_self_right r q m
        _ = r := _root_.Int.emod_eq_of_lt hr0 hrlt
    simpa [m, r, hm] using hcalc.symm
  rw [hmod]
  exact _root_.Int.toNat_of_nonneg
    (_root_.Int.emod_nonneg (intOfZ x) (_root_.Int.ne_of_gt hmpos))

theorem signed_repr_eq_proof : signed_repr_eq := by
  intro x
  change zltSelect (unsigned (repr x)) half_modulus
      (unsigned (repr x)) (zSub (unsigned (repr x)) modulus) =
    zltSelect (zMod x modulus) half_modulus (zMod x modulus)
      (zSub (zMod x modulus) modulus)
  rw [suffix_unsigned_repr_eq_exact]

theorem eqm_trans_proof : eqm_trans := by
  intro x y z hxy hyz
  exact CompCert4Lean.Lib.Zbits.eqmod_trans modulus x y z hxy hyz

theorem xor_commut_proof : xor_commut := by
  intro x y
  change WordCore.repr wordsize (zOfNat (Nat.xor x.val y.val)) =
    WordCore.repr wordsize (zOfNat (Nat.xor y.val x.val))
  exact congrArg (fun n : Nat => WordCore.repr wordsize (zOfNat n))
    (Nat.xor_comm x.val y.val)

private theorem suffix_testbit_nat (x : int) (n : Nat) :
    testbit x (zOfNat n) = x.val.testBit n := by
  cases n with
  | zero => rfl
  | succ n =>
      have hp :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) = n + 1 :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (Nat.succ_pos n)
      have hz : zOfNat (Nat.succ n) =
          .Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) := by
        rfl
      rw [hz]
      simp only [testbit, WordCore.testbit,
        WordCore.positiveToNat_eq_posToNat, hp]

private theorem suffix_ror_val (x y : int) :
    (WordCore.ror x y).val =
      Nat.lor (x.val >>> (y.val % wordsize))
        (x.val <<< (wordsize - (y.val % wordsize))) % (2 ^ wordsize) := by
  unfold WordCore.ror
  dsimp
  rw [WordCore.val_repr_residue]
  exact WordCore.residue_zOfNat _ _

private theorem suffix_ror_bit (x y : int) (i : Nat)
    (hi : i < wordsize) :
    ((WordCore.ror x y).val).testBit i =
      x.val.testBit ((i + y.val) % wordsize) := by
  rw [suffix_ror_val]
  rw [Nat.lor_eq]
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, Bool.true_and]
  let a := y.val % wordsize
  have ha : a < wordsize := Nat.mod_lt _ (by omega)
  have htarget : (i + y.val) % wordsize = (i + a) % wordsize := by
    dsimp [a]
    exact (Nat.add_mod_mod i y.val wordsize).symm
  rw [htarget]
  simp only [decide_true, Bool.true_and]
  dsimp [a] at ⊢
  by_cases hsum : i + a < wordsize
  · have hright : (x.val >>> a).testBit i = x.val.testBit (i + a) := by
      simpa [Nat.add_comm] using
        (Nat.testBit_shiftRight x.val a i)
    have hleft : (x.val <<< (wordsize - a)).testBit i = false := by
      rw [Nat.testBit_shiftLeft]
      simp [show ¬ wordsize - a ≤ i by omega]
    dsimp [a] at hright hleft
    simp only [Nat.testBit_or, hright, hleft, Bool.or_false, decide_true,
      Bool.true_and]
    rw [Nat.mod_eq_of_lt hsum]
  · have hsum' : wordsize ≤ i + a := Nat.le_of_not_gt hsum
    have hright : (x.val >>> a).testBit i = false := by
      rw [Nat.testBit_shiftRight]
      apply Nat.testBit_lt_two_pow
      have hpow : 2 ^ wordsize ≤ 2 ^ (a + i) :=
        Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      exact Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
    have hleft : (x.val <<< (wordsize - a)).testBit i =
        x.val.testBit (i + a - wordsize) := by
      rw [Nat.testBit_shiftLeft]
      simp [show wordsize - a ≤ i by omega]
      congr 1 <;> omega
    dsimp [a] at hright hleft
    simp only [Nat.testBit_or, hright, Bool.false_or, hleft, decide_true,
      Bool.true_and]
    rw [Nat.mod_eq_sub_mod hsum']
    have hidx : i + a - wordsize < wordsize := by omega
    rw [Nat.mod_eq_of_lt hidx]

private theorem suffix_zmod_add_nat (i : Nat) (y : int) :
    zMod (zAdd (zOfNat i) (unsigned y)) zwordsize =
      zOfNat ((i + y.val) % wordsize) := by
  have hy : unsigned y = zOfNat y.val := by
    change y.intval = zOfNat y.val
    exact WordCore.intval_eq_zOfNat_val y
  rw [hy]
  apply intOfZ_injective
  simp only [zMod, zAdd, zwordsize, zOfNat,
    ZArith.BinInt.Z.modulo, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change (if (Int.ofNat wordsize) = 0 then
      Int.ofNat i + Int.ofNat y.val
    else if 0 < Int.ofNat wordsize then
      (Int.ofNat i + Int.ofNat y.val) % Int.ofNat wordsize
    else _) = Int.ofNat ((i + y.val) % wordsize)
  simp [wordsize, Int.natCast_add, Int.natCast_emod]

theorem bits_ror_proof : bits_ror := by
  intro x y i hi
  cases i with
  | Zneg p =>
      exfalso
      have hi0 := hi.1
      change 0 ≤ -(Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) at hi0
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      have hbit := suffix_ror_bit x y 0 (by decide)
      have hmod := suffix_zmod_add_nat 0 y
      have hmod' := hmod
      change zMod (zAdd (.Z0 : Z) (unsigned y)) zwordsize =
        zOfNat ((0 + y.val) % wordsize) at hmod'
      calc
        testbit (ror x y) .Z0 = (WordCore.ror x y).val.testBit 0 := by
          rfl
        _ = x.val.testBit ((0 + y.val) % wordsize) := hbit
        _ = testbit x (zOfNat ((0 + y.val) % wordsize)) :=
          (suffix_testbit_nat x ((0 + y.val) % wordsize)).symm
        _ = testbit x (zMod (zAdd .Z0 (unsigned y)) zwordsize) := by
          rw [hmod']
  | Zpos p =>
      have hkZ := hi.2
      change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
        Int.ofNat wordsize at hkZ
      have hk :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize :=
        Int.ofNat_lt.mp hkZ
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        apply intOfZ_injective
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        rfl
      rw [← hz] at hi ⊢
      have hbit := suffix_ror_bit x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) hk
      have hmod := suffix_zmod_add_nat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) y
      calc
        testbit (ror x y) (zOfNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
            (WordCore.ror x y).val.testBit
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
          suffix_testbit_nat (WordCore.ror x y)
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        _ = x.val.testBit
            ((CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + y.val) %
              wordsize) := hbit
        _ = testbit x (zOfNat
            ((CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + y.val) %
              wordsize)) :=
          (suffix_testbit_nat x _).symm
        _ = testbit x (zMod (zAdd
            (zOfNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
            (unsigned y)) zwordsize) := by
          rw [hmod]

private theorem suffix_ltu_last_val (y : int)
    (h : ltu y (repr (zSub zwordsize zOne)) = true) : y.val < wordsize - 1 := by
  have hlt := (ltu_inv_proof y (repr (zSub zwordsize zOne)) h).2
  have hrepr : unsigned (repr (zSub zwordsize zOne)) =
      zSub zwordsize zOne := by
    apply unsigned_repr_proof_api
    constructor
    · change (0 : Int) ≤ 31
      omega
    · change (31 : Int) ≤ (2 ^ wordsize : Int) - 1
      decide
  rw [hrepr] at hlt
  change intOfZ y.intval < intOfZ (zSub zwordsize zOne) at hlt
  rw [WordCore.intval_eq_zOfNat_val y] at hlt
  simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
  exact Int.ofNat_lt.mp hlt

private theorem suffix_signed_shl_one (y : int)
    (hyv : y.val < wordsize - 1) :
    signed (shl one y) = zTwoP (unsigned y) := by
  have hyunsigned : unsigned y = zOfNat y.val := by
    change y.intval = zOfNat y.val
    exact WordCore.intval_eq_zOfNat_val y
  have hone : (one : int).val = 1 := by rfl
  have hshlval : (shl one y).val = 2 ^ y.val := by
    change (WordCore.shl one y).val = 2 ^ y.val
    rw [suffix_shl_val, hone]
    simp only [Nat.one_mul]
    apply Nat.mod_eq_of_lt
    have hpowle : 2 ^ y.val ≤ 2 ^ (wordsize - 1) := by
      apply Nat.pow_le_pow_right Nat.zero_lt_two
      omega
    have hhalf : 2 ^ (wordsize - 1) < 2 ^ wordsize := by
      change 2 ^ 31 < 2 ^ 32
      decide
    exact Nat.lt_of_le_of_lt hpowle hhalf
  have hsmall : (shl one y).val < 2 ^ (wordsize - 1) := by
    rw [hshlval]
    apply Nat.pow_lt_pow_right
    · decide
    · omega
  have hs := suffix_signed_int (shl one y)
  rw [if_pos hsmall, hshlval] at hs
  have hy0 : zLe zZero (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega
  have htwo : zTwoP (unsigned y) = zOfInt (Int.ofNat (2 ^ y.val)) := by
    have h := suffix_two_p_nonneg (unsigned y) hy0
    simpa [hyunsigned] using h
  apply intOfZ_injective
  rw [hs, htwo, intOfZ_zOfInt]

private theorem suffix_tdiv_adjust (a b : Int) (hb : 0 < b) :
    a.tdiv b = (if a < 0 then (a + b - 1) / b else a / b) := by
  by_cases ha : 0 ≤ a
  · have hna : ¬ a < 0 := by omega
    rw [if_neg hna, Int.tdiv_eq_ediv_of_nonneg ha]
  · have ha' : a < 0 := by omega
    rw [if_pos ha']
    rw [Int.tdiv_cases]
    simp only [if_neg ha, if_pos (Int.le_of_lt hb)]
    have hq : (-a) / b * b ≤ -a ∧ -a < (-a) / b * b + b :=
      (Int.ediv_eq_iff_of_pos hb).mp rfl
    symm
    apply (Int.ediv_eq_iff_of_pos hb).mpr
    constructor <;> simp only [Int.neg_mul] <;> omega

private theorem suffix_zdiv_pos (a b : Z) (hb : 0 < intOfZ b) :
    zDiv a b = zOfInt (Int.ediv (intOfZ a) (intOfZ b)) := by
  change zOfInt (if intOfZ b = 0 then 0 else if 0 < intOfZ b then
    Int.ediv (intOfZ a) (intOfZ b) else
      let d := -(intOfZ b)
      let q := Int.ediv (intOfZ a) d
      let r := Int.emod (intOfZ a) d
      if r = 0 then -q else -(q + 1)) = _
  simp [Int.ne_of_gt hb, hb]

private theorem suffix_signed_add_shift (x y : int)
    (hyv : y.val < wordsize - 1)
    (hx : intOfZ (signed x) < 0) :
    intOfZ (signed (add x (sub (shl one y) one))) =
      intOfZ (signed x) + Int.ofNat (2 ^ y.val) - 1 := by
  have hshlval : (shl one y).val = 2 ^ y.val := by
    change (WordCore.shl one y).val = 2 ^ y.val
    rw [suffix_shl_val]
    have hone : (one : int).val = 1 := by rfl
    rw [hone, Nat.one_mul]
    apply Nat.mod_eq_of_lt
    have hpowle : 2 ^ y.val ≤ 2 ^ (wordsize - 1) := by
      apply Nat.pow_le_pow_right Nat.zero_lt_two
      omega
    have hhalf : 2 ^ (wordsize - 1) < 2 ^ wordsize := by
      change 2 ^ 31 < 2 ^ 32
      decide
    exact Nat.lt_of_le_of_lt hpowle hhalf
  have hsubval : (sub (shl one y) one).val = 2 ^ y.val - 1 := by
    change (WordCore.sub (shl one y) one).val = 2 ^ y.val - 1
    have hone : (one : int).val = 1 := by rfl
    rw [WordCore.sub_val, hshlval, hone]
    have hpow : 1 ≤ 2 ^ y.val := Nat.one_le_two_pow
    have hlt : 2 ^ y.val - 1 < 2 ^ wordsize := by
      have hpowle : 2 ^ y.val ≤ 2 ^ (wordsize - 1) := by
        apply Nat.pow_le_pow_right Nat.zero_lt_two
        omega
      have hhalf : 2 ^ (wordsize - 1) < 2 ^ wordsize := by
        change 2 ^ 31 < 2 ^ 32
        decide
      omega
    have hge : 2 ^ wordsize ≤ 2 ^ wordsize - 1 + 2 ^ y.val := by
      have hpow : 1 ≤ 2 ^ y.val := Nat.one_le_two_pow
      omega
    rw [Nat.mod_eq_sub_mod hge]
    have heq : 2 ^ wordsize - 1 + 2 ^ y.val - 2 ^ wordsize =
        2 ^ y.val - 1 := by
      rw [show 2 ^ wordsize - 1 + 2 ^ y.val =
          2 ^ wordsize + (2 ^ y.val - 1) by omega]
      rw [Nat.add_sub_cancel_left]
    rw [heq, Nat.mod_eq_of_lt]
    exact hlt
  have haddval : (add x (sub (shl one y) one)).val =
      (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize := by
    change (WordCore.add x (sub (shl one y) one)).val = _
    rw [WordCore.add_val, hsubval]
  have hsx := suffix_signed_int x
  have hst := suffix_signed_int (add x (sub (shl one y) one))
  have hxlt : ¬ x.val < 2 ^ (wordsize - 1) := by
    intro hxl
    rw [hsx, if_pos hxl] at hx
    have hx' : (0 : Int) ≤ Int.ofNat x.val := Int.natCast_nonneg _
    omega
  have hsx' : intOfZ (signed x) =
      Int.ofNat x.val - Int.ofNat (2 ^ wordsize) := by
    rw [hsx, if_neg hxlt]
  have hM : 0 < 2 ^ wordsize := Nat.two_pow_pos _
  have hH : 2 ^ (wordsize - 1) ≤ 2 ^ wordsize := by
    apply Nat.pow_le_pow_right Nat.zero_lt_two
    omega
  have hnlt : 2 ^ y.val - 1 < 2 ^ (wordsize - 1) := by
    change 2 ^ y.val - 1 < 2 ^ 31
    have hpowle : 2 ^ y.val ≤ 2 ^ (wordsize - 1) := by
      apply Nat.pow_le_pow_right Nat.zero_lt_two
      omega
    change 2 ^ y.val ≤ 2 ^ 31 at hpowle
    omega
  have hxval_lt : x.val < 2 ^ wordsize := WordCore.val_lt x
  have hsumlt2 : x.val + (2 ^ y.val - 1) < 2 * 2 ^ wordsize := by
    omega
  by_cases hsum : x.val + (2 ^ y.val - 1) < 2 ^ wordsize
  · have hmod : (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize =
        x.val + (2 ^ y.val - 1) := Nat.mod_eq_of_lt hsum
    have htge : 2 ^ (wordsize - 1) ≤
        x.val + (2 ^ y.val - 1) := by
      have hxge : 2 ^ (wordsize - 1) ≤ x.val := Nat.le_of_not_gt hxlt
      omega
    have hst' : intOfZ (signed (add x (sub (shl one y) one))) =
        Int.ofNat (x.val + (2 ^ y.val - 1)) - Int.ofNat (2 ^ wordsize) := by
      have htge' : ¬ (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize <
          2 ^ (wordsize - 1) := by
        rw [hmod]
        omega
      rw [hst, haddval, if_neg htge', hmod]
    rw [hsx', hst']
    have hcastP : Int.ofNat (2 ^ y.val - 1) =
        Int.ofNat (2 ^ y.val) - 1 := by
      exact Int.ofNat_sub (Nat.one_le_two_pow)
    have hcastsum : Int.ofNat (x.val + (2 ^ y.val - 1)) =
        Int.ofNat x.val + Int.ofNat (2 ^ y.val - 1) := by
      simpa only [Int.ofNat_eq_natCast] using Int.natCast_add x.val (2 ^ y.val - 1)
    rw [hcastsum, hcastP]
    omega
  · have hsumge : 2 ^ wordsize ≤ x.val + (2 ^ y.val - 1) :=
      Nat.le_of_not_gt hsum
    have hsublt : x.val + (2 ^ y.val - 1) - 2 ^ wordsize < 2 ^ wordsize := by
      omega
    have hmod : (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize =
        x.val + (2 ^ y.val - 1) - 2 ^ wordsize := by
      rw [Nat.mod_eq_sub_mod hsumge, Nat.mod_eq_of_lt hsublt]
    have htlt : x.val + (2 ^ y.val - 1) - 2 ^ wordsize <
        2 ^ (wordsize - 1) := by
      have hsublt' : x.val + (2 ^ y.val - 1) - 2 ^ wordsize <
          2 ^ y.val - 1 := by
        omega
      exact Nat.lt_trans hsublt' hnlt
    have hst' : intOfZ (signed (add x (sub (shl one y) one))) =
        Int.ofNat (x.val + (2 ^ y.val - 1) - 2 ^ wordsize) := by
      have htlt' : (x.val + (2 ^ y.val - 1)) % 2 ^ wordsize <
          2 ^ (wordsize - 1) := by
        rw [hmod]
        exact htlt
      rw [hst, haddval, if_pos htlt', hmod]
    rw [hsx', hst']
    have hcastsub : Int.ofNat (x.val + (2 ^ y.val - 1) - 2 ^ wordsize) =
        Int.ofNat (x.val + (2 ^ y.val - 1)) - Int.ofNat (2 ^ wordsize) := by
      exact Int.ofNat_sub hsumge
    have hcastP : Int.ofNat (2 ^ y.val - 1) =
        Int.ofNat (2 ^ y.val) - 1 := by
      exact Int.ofNat_sub (Nat.one_le_two_pow)
    have hcastsum : Int.ofNat (x.val + (2 ^ y.val - 1)) =
        Int.ofNat x.val + Int.ofNat (2 ^ y.val - 1) := by
      simpa only [Int.ofNat_eq_natCast] using Int.natCast_add x.val (2 ^ y.val - 1)
    rw [hcastsub, hcastsum, hcastP]
    omega

theorem shrx_shr_proof : shrx_shr := by
  intro x y hy
  have hyv := suffix_ltu_last_val y hy
  have hy0 : zLe zZero (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    change 0 ≤ intOfZ y.intval
    omega
  have hpow := suffix_two_p_nonneg (unsigned y) hy0
  have htwo : zTwoP (unsigned y) = zOfInt (Int.ofNat (2 ^ y.val)) := by
    have hyunsigned : unsigned y = zOfNat y.val := by
      change y.intval = zOfNat y.val
      exact WordCore.intval_eq_zOfNat_val y
    simpa [hyunsigned] using hpow
  have hdpos : 0 < intOfZ (zTwoP (unsigned y)) := by
    rw [htwo, intOfZ_zOfInt]
    have htwoInt : (0 : Int) < 2 := by decide
    exact Int.pow_pos htwoInt
  have hs := suffix_signed_shl_one y hyv
  have hdint : intOfZ (zTwoP (unsigned y)) = Int.ofNat (2 ^ y.val) := by
    rw [htwo, intOfZ_zOfInt]
  have hltzero : signed zero = zZero := by rfl
  change WordCore.repr wordsize (zQuot (signed x) (signed (shl one y))) =
    WordCore.repr wordsize
      (zShiftr (signed (if lt x zero = true then
        add x (sub (shl one y) one) else x)) (unsigned y))
  by_cases hlt : lt x zero = true
  · have hneg : intOfZ (signed x) < 0 := by
      change zltSelect (signed x) (signed zero) true false = true at hlt
      cases hz : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
      | left hlt' =>
          change intOfZ (signed x) < intOfZ (signed zero) at hlt'
          rw [hltzero] at hlt'
          exact hlt'
      | right hge =>
          simp [zltSelect, sumboolSelect, hz] at hlt
    have hsigned := suffix_signed_add_shift x y hyv hneg
    have hquot : zQuot (signed x) (zTwoP (unsigned y)) =
        zDiv (signed (add x (sub (shl one y) one)))
          (zTwoP (unsigned y)) := by
      rw [suffix_zdiv_pos _ _ hdpos]
      apply intOfZ_injective
      simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
      rw [suffix_tdiv_adjust _ _ hdpos]
      simp only [if_pos hneg]
      rw [hsigned, hdint]
      exact Int.div_def _ _
    simp [hlt]
    rw [hs]
    rw [suffix_zshiftr_div_any _ _ hy0]
    rw [hquot]
  · have hnonneg : 0 ≤ intOfZ (signed x) := by
      have hltfalse : lt x zero = false := by
        cases hxlt : lt x zero with
        | false => simpa using hxlt
        | true => exact (hlt hxlt).elim
      change zltSelect (signed x) (signed zero) true false = false at hltfalse
      cases hz : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
      | left hlt' =>
          simp [zltSelect, sumboolSelect, hz] at hltfalse
      | right hge =>
          change intOfZ (signed zero) ≤ intOfZ (signed x) at hge
          rw [hltzero] at hge
          exact hge
    have hquot : zQuot (signed x) (zTwoP (unsigned y)) =
        zDiv (signed x) (zTwoP (unsigned y)) := by
      rw [suffix_zdiv_pos _ _ hdpos]
      apply intOfZ_injective
      simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
      rw [suffix_tdiv_adjust _ _ hdpos]
      rw [if_neg (by omega)]
      exact Int.div_def _ _
    rw [if_neg hlt]
    rw [hs]
    rw [suffix_zshiftr_div_any _ _ hy0]
    rw [hquot]

theorem signed_zero_proof : signed_zero := by
  rfl

theorem bits_above_proof : bits_above := by
  intro x i hi
  cases i with
  | Zneg p =>
      exfalso
      change (32 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hi
      have hp : (0 : Int) ≤ Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_nonneg _
      omega
  | Z0 =>
      exfalso
      change (32 : Int) ≤ 0 at hi
      omega
  | Zpos p =>
      simp only [testbit, WordCore.testbit]
      rw [WordCore.positiveToNat_eq_posToNat]
      change Nat.testBit x.val
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = false
      change intOfZ (zOfNat wordsize) ≤
        intOfZ (Numbers.BinNums.Z.Zpos p) at hi
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
        intOfZ, posToNat] at hi
      have hidx : wordsize ≤
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        Int.ofNat_le.mp hi
      have hpow : 2 ^ wordsize ≤
          2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        Nat.pow_le_pow_right Nat.zero_lt_two hidx
      have hval : x.val <
          2 ^ CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
      exact Nat.testBit_lt_two_pow hval

private theorem suffix_modulo_int (a : Z) :
    intOfZ (zMod a modulus) = intOfZ a % (2 ^ wordsize : Int) := by
  have hmpos : (0 : Int) < intOfZ modulus := by
    change (0 : Int) < Int.ofNat (2 ^ wordsize)
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
    rfl
  have hrange := ZArith.BinInt.Z.modulo_range a modulus (by
    change (0 : Int) < intOfZ modulus
    exact hmpos)
  have hr0 : (0 : Int) ≤ intOfZ (zMod a modulus) := hrange.1
  have hrlt : intOfZ (zMod a modulus) < intOfZ modulus := hrange.2
  have hd := ZArith.Zdiv.Z_div_mod_eq_full a modulus
  have hdInt := congrArg intOfZ hd
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hdInt
  let q := intOfZ (ZArith.BinInt.Z.div a modulus)
  let r := intOfZ (zMod a modulus)
  let m := intOfZ modulus
  have hcalc : intOfZ a % m = r := by
    calc
      intOfZ a % m = (m * q + r) % m := congrArg (fun v => v % m) hdInt
      _ = (r + q * m) % m := by rw [Int.add_comm, Int.mul_comm]
      _ = r % m := Int.add_mul_emod_self_right r q m
      _ = r := Int.emod_eq_of_lt hr0 hrlt
  simpa [m, r, hm] using hcalc.symm

private theorem suffix_signed_mod (x : int) :
    intOfZ (signed x) % (2 ^ wordsize : Int) =
      intOfZ (unsigned x) % (2 ^ wordsize : Int) := by
  unfold signed WordCore.signed
  cases h : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left _ =>
      simp only [zltSelect, sumboolSelect, h]
      rfl
  | right _ =>
      simp only [zltSelect, sumboolSelect, h]
      simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      have hm : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
        rfl
      rw [hm, Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod]
      rfl

theorem mods_divs_proof : mods_divs := by
  intro x y
  apply WordCore.ext
  change unsigned (mods x y) = unsigned (sub x (mul (divs x y) y))
  change unsigned (repr
      (zSub (signed x) (zMul (zQuot (signed x) (signed y)) (signed y)))) =
    unsigned (repr
      (zSub (unsigned x)
        (unsigned (repr (zMul
          (unsigned (repr (zQuot (signed x) (signed y)))) (unsigned y))))))
  rw [suffix_unsigned_repr_eq_exact, suffix_unsigned_repr_eq_exact]
  rw [suffix_unsigned_repr_eq_exact, suffix_unsigned_repr_eq_exact]
  apply intOfZ_injective
  simp only [zSub, zMul, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt]
  rw [suffix_modulo_int]
  rw [suffix_modulo_int]
  rw [suffix_modulo_int]
  simp only [intOfZ_zOfInt]
  have hsubL :
      (intOfZ (signed x) - intOfZ (zQuot (signed x) (signed y)) *
          intOfZ (signed y)) %
          (2 ^ wordsize : Int) =
        (intOfZ (signed x) % (2 ^ wordsize : Int) -
          (intOfZ (zQuot (signed x) (signed y)) * intOfZ (signed y)) %
            (2 ^ wordsize : Int)) %
          (2 ^ wordsize : Int) := by
    rw [Int.sub_emod]
  have hsubR :
      (intOfZ (unsigned x) -
          (intOfZ (zMod (zQuot (signed x) (signed y)) modulus) *
            intOfZ (unsigned y)) % (2 ^ wordsize : Int)) %
          (2 ^ wordsize : Int) =
        (intOfZ (unsigned x) % (2 ^ wordsize : Int) -
          (intOfZ (zMod (zQuot (signed x) (signed y)) modulus) *
            intOfZ (unsigned y)) % (2 ^ wordsize : Int)) %
          (2 ^ wordsize : Int) := by
    rw [Int.sub_emod, Int.emod_emod]
  rw [hsubL, hsubR]
  have hsx := suffix_signed_mod x
  have hsy := suffix_signed_mod y
  have hqmod := suffix_modulo_int (zQuot (signed x) (signed y))
  have hprod :
      (intOfZ (zQuot (signed x) (signed y)) * intOfZ (signed y)) %
          (2 ^ wordsize : Int) =
        (intOfZ (zMod (zQuot (signed x) (signed y)) modulus) *
          intOfZ (unsigned y)) % (2 ^ wordsize : Int) := by
    rw [hqmod]
    calc
      (intOfZ (zQuot (signed x) (signed y)) * intOfZ (signed y)) %
          (2 ^ wordsize : Int) =
        (intOfZ (zQuot (signed x) (signed y)) % (2 ^ wordsize : Int) *
          (intOfZ (signed y) % (2 ^ wordsize : Int))) %
            (2 ^ wordsize : Int) := Int.mul_emod _ _ _
      _ = (intOfZ (zQuot (signed x) (signed y)) %
          (2 ^ wordsize : Int) *
          (intOfZ (unsigned y) % (2 ^ wordsize : Int))) %
            (2 ^ wordsize : Int) := by rw [hsy]
      _ = (intOfZ (zQuot (signed x) (signed y)) %
          (2 ^ wordsize : Int) * intOfZ (unsigned y)) %
            (2 ^ wordsize : Int) := by
        calc
          (intOfZ (zQuot (signed x) (signed y)) %
              (2 ^ wordsize : Int) *
              (intOfZ (unsigned y) % (2 ^ wordsize : Int))) %
              (2 ^ wordsize : Int) =
            ((intOfZ (zQuot (signed x) (signed y)) %
                (2 ^ wordsize : Int)) % (2 ^ wordsize : Int) *
              (intOfZ (unsigned y) % (2 ^ wordsize : Int) %
                (2 ^ wordsize : Int))) % (2 ^ wordsize : Int) :=
            Int.mul_emod _ _ _
          _ = (intOfZ (zQuot (signed x) (signed y)) %
              (2 ^ wordsize : Int) *
              (intOfZ (unsigned y) % (2 ^ wordsize : Int))) %
              (2 ^ wordsize : Int) := by
            rw [Int.emod_emod, Int.emod_emod]
          _ = (intOfZ (zQuot (signed x) (signed y)) %
              (2 ^ wordsize : Int) * intOfZ (unsigned y)) %
              (2 ^ wordsize : Int) := by
            simpa only [Int.emod_emod] using
              (Int.mul_emod
                (intOfZ (zQuot (signed x) (signed y)) %
                  (2 ^ wordsize : Int))
                (intOfZ (unsigned y)) (2 ^ wordsize : Int)).symm
  rw [hsx, hprod]
  repeat rw [Int.emod_emod]

private theorem suffix_divmods2_n_eq (n : int) :
    zAdd (zMul (signed (if lt n zero = true then mone else zero)) modulus)
        (unsigned n) = signed n := by
  have hux : intOfZ (unsigned n) = Int.ofNat n.val := by
    change intOfZ n.intval = Int.ofNat n.val
    rw [WordCore.intval_eq_zOfNat_val n]
    simpa only [zOfNat, ZArith.BinInt.Z.of_nat] using
      intOfZ_zOfInt (Int.ofNat n.val)
  have hsx := suffix_signed_int n
  have hM : intOfZ modulus = (2 ^ wordsize : Int) := by
    rfl
  have hcastM : Int.ofNat (2 ^ wordsize) = (2 ^ wordsize : Int) := by
    change Int.ofNat (2 ^ wordsize) = Int.ofNat 2 ^ wordsize
    exact Int.natCast_pow 2 wordsize
  have hcastH : Int.ofNat (2 ^ (wordsize - 1)) =
      (2 ^ (wordsize - 1) : Int) := by
    change Int.ofNat (2 ^ (wordsize - 1)) = Int.ofNat 2 ^ (wordsize - 1)
    exact Int.natCast_pow 2 (wordsize - 1)
  by_cases hlt : lt n zero = true
  · have hneg : intOfZ (signed n) < 0 := by
      change zltSelect (signed n) (signed zero) true false = true at hlt
      cases hz : CompCert4Lean.Lib.Coqlib.zlt (signed n) (signed zero) with
      | left hlt' =>
          change intOfZ (signed n) < intOfZ (signed zero) at hlt'
          have hz0 : signed zero = zZero := by rfl
          rw [hz0] at hlt'
          exact hlt'
      | right hge =>
          simp [zltSelect, sumboolSelect, hz] at hlt
    have hval : ¬ n.val < 2 ^ (wordsize - 1) := by
      intro hv
      have hneg' :
          (if n.val < 2 ^ (wordsize - 1) then Int.ofNat n.val
          else Int.ofNat n.val - Int.ofNat (2 ^ wordsize)) < 0 := by
        simpa only [hsx] using hneg
      rw [hcastM] at hneg'
      simp [hv] at hneg'
      omega
    rw [if_pos hlt]
    apply intOfZ_injective
    simp only [zMul, zAdd, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.add,
      zOpp, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
    rw [hux, hM]
    have hsxval : intOfZ (signed n) =
        Int.ofNat n.val - Int.ofNat (2 ^ wordsize) := by
      simpa only [hsx, if_neg hval]
    rw [hcastM] at hsxval
    have hmone : intOfZ (signed mone) = (-1 : Int) := by
      rfl
    rw [hsxval, hmone]
    clear hsx
    omega
  · have hnonneg : 0 ≤ intOfZ (signed n) := by
      have hltfalse : lt n zero = false := by
        cases hq : lt n zero with
        | false => simpa using hq
        | true => exact (hlt hq).elim
      change zltSelect (signed n) (signed zero) true false = false at hltfalse
      cases hz : CompCert4Lean.Lib.Coqlib.zlt (signed n) (signed zero) with
      | left hlt' =>
          simp [zltSelect, sumboolSelect, hz] at hltfalse
      | right hge =>
          change intOfZ (signed zero) ≤ intOfZ (signed n) at hge
          have hz0 : signed zero = zZero := by rfl
          rw [hz0] at hge
          exact hge
    have hval : n.val < 2 ^ (wordsize - 1) := by
      by_cases hv : n.val < 2 ^ (wordsize - 1)
      · exact hv
      · exfalso
        have hv' : 2 ^ (wordsize - 1) ≤ n.val := Nat.le_of_not_gt hv
        have hvInt : (2 ^ (wordsize - 1) : Int) ≤ Int.ofNat n.val := by
          rw [← hcastH]
          exact (Int.ofNat_le).2 hv'
        have hsxval_neg : intOfZ (signed n) =
            Int.ofNat n.val - Int.ofNat (2 ^ wordsize) := by
          simpa only [hsx, if_neg hv]
        rw [hcastM] at hsxval_neg
        have hnonneg' := hnonneg
        rw [hsxval_neg] at hnonneg'
        have hnlt := WordCore.val_lt n
        have hnltInt : Int.ofNat n.val < (2 ^ wordsize : Int) := by
          rw [← hcastM]
          exact (Int.ofNat_lt).2 hnlt
        have hpow : 2 ^ (wordsize - 1) < 2 ^ wordsize := by
          change 2 ^ 31 < 2 ^ 32
          decide
        clear hsx
        omega
    rw [if_neg hlt]
    apply intOfZ_injective
    simp only [zMul, zAdd, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.add,
      intOfZ_zOfInt]
    rw [hux, hM]
    have hsxval : intOfZ (signed n) = Int.ofNat n.val := by
      simpa only [hsx, if_pos hval]
    have hzero : intOfZ (signed zero) = (0 : Int) := by
      rfl
    rw [hsxval, hzero]
    clear hsx
    omega

private theorem suffix_divmods2_q_bounds (n d : int) (hd : d ≠ zero)
    (hcond : n ≠ repr min_signed ∨ d ≠ mone) :
    zLe min_signed (zQuot (signed n) (signed d)) ∧
      zLe (zQuot (signed n) (signed d)) max_signed := by
  have hD0 : intOfZ (signed d) ≠ 0 := by
    intro hzero
    apply hd
    apply signed_injective_try
    apply intOfZ_injective
    have hz : signed zero = zZero := by rfl
    rw [hz]
    exact hzero
  have hNr := signed_range_proof n
  change (-2147483648 : Int) ≤ intOfZ (signed n) ∧
      intOfZ (signed n) ≤ (2147483647 : Int) at hNr
  have hqeq : intOfZ (zQuot (signed n) (signed d)) =
      Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) := by
    simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
  by_cases hDpos : 0 < intOfZ (signed d)
  · by_cases hNnonneg : 0 ≤ intOfZ (signed n)
    · have hQlo : (0 : Int) ≤ Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) := by
        exact Int.tdiv_nonneg hNnonneg (Int.le_of_lt hDpos)
      have hQhi : Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) ≤ (2147483647 : Int) := by
        simpa [hNnonneg] using
          (Int.tdiv_le_of_le_mul (a := intOfZ (signed n))
            (b := (2147483647 : Int)) hDpos (by omega))
      constructor
      · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
        rw [hqeq]
        exact Int.le_trans (by omega) hQlo
      · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
        rw [hqeq]
        exact hQhi
    · have hNneg : intOfZ (signed n) < 0 := by omega
      have hA0 : 0 ≤ -intOfZ (signed n) := by omega
      have hAhi : -intOfZ (signed n) ≤ (2147483648 : Int) := by omega
      have hQlo' : (-intOfZ (signed n)).tdiv (intOfZ (signed d)) ≤ (2147483648 : Int) := by
        simpa [show intOfZ (signed n) ≤ 0 by omega] using
          (Int.tdiv_le_of_le_mul (a := -intOfZ (signed n))
            (b := (2147483648 : Int)) hDpos (by omega))
      have hQhi' : 0 ≤ (-intOfZ (signed n)).tdiv (intOfZ (signed d)) := by
        exact Int.tdiv_nonneg hA0 (Int.le_of_lt hDpos)
      constructor
      · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
        rw [hqeq]
        have hform : Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) =
            -((-intOfZ (signed n)).tdiv (intOfZ (signed d))) := by
          simpa using (Int.neg_tdiv (-intOfZ (signed n)) (intOfZ (signed d)))
        rw [hform]
        omega
      · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
        rw [hqeq]
        have hform : Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) =
            -((-intOfZ (signed n)).tdiv (intOfZ (signed d))) := by
          simpa using (Int.neg_tdiv (-intOfZ (signed n)) (intOfZ (signed d)))
        rw [hform]
        omega
  · have hDneg : intOfZ (signed d) < 0 := by omega
    let c : Int := -intOfZ (signed d)
    have hcpos : 0 < c := by
      dsimp [c]
      omega
    have hqnegden : Int.tdiv (intOfZ (signed n)) (intOfZ (signed d)) =
        -(Int.tdiv (intOfZ (signed n)) c) := by
      dsimp [c]
      simp [Int.tdiv_neg]
    by_cases hNnonneg : 0 ≤ intOfZ (signed n)
    · have hQlo' : Int.tdiv (intOfZ (signed n)) c ≤ (2147483648 : Int) := by
        simpa [hNnonneg] using
          (Int.tdiv_le_of_le_mul (a := intOfZ (signed n))
            (b := (2147483648 : Int)) hcpos (by omega))
      have hQhi' : 0 ≤ Int.tdiv (intOfZ (signed n)) c := by
        exact Int.tdiv_nonneg hNnonneg (Int.le_of_lt hcpos)
      constructor
      · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
        rw [hqeq, hqnegden]
        omega
      · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
        rw [hqeq, hqnegden]
        omega
    · have hNneg : intOfZ (signed n) < 0 := by omega
      have hA0 : 0 ≤ -intOfZ (signed n) := by omega
      have hAhi : -intOfZ (signed n) ≤ (2147483648 : Int) := by omega
      have hQlo' : 0 ≤ (-intOfZ (signed n)).tdiv c := by
        exact Int.tdiv_nonneg hA0 (Int.le_of_lt hcpos)
      by_cases hc_one : c = 1
      · have hQeq : (-intOfZ (signed n)).tdiv c = -intOfZ (signed n) := by
          rw [hc_one]
          exact Int.tdiv_one _
        have hQhi : (-intOfZ (signed n)).tdiv c ≤ (2147483647 : Int) := by
          rw [hQeq]
          by_cases hbad : -intOfZ (signed n) ≤ (2147483647 : Int)
          · exact hbad
          · exfalso
            have hNmin : intOfZ (signed n) = (-2147483648 : Int) := by omega
            have hnmin : n = repr min_signed := by
              apply signed_injective_try
              have hsmin : signed (repr min_signed) = min_signed := by
                rw [signed_repr_eq_proof]
                decide
              apply intOfZ_injective
              change intOfZ (signed n) = intOfZ (signed (repr min_signed))
              rw [hNmin, hsmin]
              rfl
            have hDminus : signed d = zOpp zOne := by
              apply intOfZ_injective
              simp only [zOpp, ZArith.BinInt.Z.opp, intOfZ_zOfInt]
              dsimp [c] at hc_one
              have hone : intOfZ zOne = (1 : Int) := by rfl
              rw [hone]
              omega
            have hdminus : d = mone := by
              apply signed_injective_try
              rw [hDminus, signed_mone_proof]
            exact hcond.elim (fun hn => hn hnmin) (fun hd' => hd' hdminus)
        constructor
        · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
          rw [hqeq, hqnegden]
          have hform : Int.tdiv (intOfZ (signed n)) c =
              -((-intOfZ (signed n)).tdiv c) := by
            simpa using (Int.neg_tdiv (-intOfZ (signed n)) c)
          rw [hform, hQeq]
          omega
        · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
          rw [hqeq, hqnegden]
          have hform : Int.tdiv (intOfZ (signed n)) c =
              -((-intOfZ (signed n)).tdiv c) := by
            simpa using (Int.neg_tdiv (-intOfZ (signed n)) c)
          rw [hform, hQeq]
          omega
      · have hc_two : (2 : Int) ≤ c := by omega
        have hQhi : (-intOfZ (signed n)).tdiv c ≤ (2147483647 : Int) := by
          simpa [show intOfZ (signed n) ≤ 0 by omega] using
            (Int.tdiv_le_of_le_mul (a := -intOfZ (signed n))
              (b := (2147483647 : Int)) hcpos (by omega))
        constructor
        · change (-2147483648 : Int) ≤ intOfZ (zQuot (signed n) (signed d))
          rw [hqeq, hqnegden]
          have hform : Int.tdiv (intOfZ (signed n)) c =
              -((-intOfZ (signed n)).tdiv c) := by
            simpa using (Int.neg_tdiv (-intOfZ (signed n)) c)
          rw [hform]
          omega
        · change intOfZ (zQuot (signed n) (signed d)) ≤ (2147483647 : Int)
          rw [hqeq, hqnegden]
          have hform : Int.tdiv (intOfZ (signed n)) c =
              -((-intOfZ (signed n)).tdiv c) := by
            simpa using (Int.neg_tdiv (-intOfZ (signed n)) c)
          rw [hform]
          omega

theorem divmods2_divs_mods_proof : divmods2_divs_mods := by
  intro n d hd hcond
  unfold divmods2 divs mods
  by_cases hdz : d = zero
  · exact (hd hdz).elim
  · simp [eq_dec, hdz]
    rw [suffix_divmods2_n_eq n]
    have hqb := suffix_divmods2_q_bounds n d hdz hcond
    rcases hqb with ⟨hqbLo, hqbHi⟩
    cases hlo : CompCert4Lean.Lib.Coqlib.zle
        min_signed (zQuot (signed n) (signed d)) with
    | left hlo' =>
        cases hhi : CompCert4Lean.Lib.Coqlib.zle
            (zQuot (signed n) (signed d)) max_signed with
        | left hhi' => rfl
        | right hhi' =>
            exfalso
            change intOfZ max_signed <
                intOfZ (zQuot (signed n) (signed d)) at hhi'
            change intOfZ (zQuot (signed n) (signed d)) ≤ intOfZ max_signed at hqbHi
            omega
    | right hlo' =>
        exfalso
        change intOfZ (zQuot (signed n) (signed d)) < intOfZ min_signed at hlo'
        change intOfZ min_signed ≤ intOfZ (zQuot (signed n) (signed d)) at hqbLo
        omega

theorem bits_zero_proof : bits_zero := by
  intro i
  have hz : zero.val = 0 := by rfl
  cases i with
  | Zneg _ => rfl
  | Z0 =>
      change zero.val.testBit 0 = false
      simp [hz]
  | Zpos p =>
      change zero.val.testBit (WordCore.positiveToNat p) = false
      simp [hz]

theorem swap_cmp_proof : swap_cmp := by
  intro c x y
  cases c <;>
    simp [cmp, WordCore.cmp, swap_comparison, WordCore.eq, eq_comm]

theorem or_zero_proof : or_zero := by
  intro x
  unfold or WordCore.or
  change repr (zOfNat (Nat.lor x.val zero.val)) = x
  rw [show zero.val = 0 by rfl]
  rw [show Nat.lor x.val 0 = x.val by
    simpa only [Nat.lor_eq] using Nat.or_zero x.val]
  rw [show zOfNat x.val = unsigned x by
    exact (WordCore.intval_eq_zOfNat_val x).symm]
  exact repr_unsigned_proof x

private theorem suffix_bits_shru_nat (x y : int) (n : Nat) :
    testbit (shru x y) (zOfNat n) =
      zltSelect (zAdd (zOfNat n) (unsigned y)) zwordsize
        (testbit x (zAdd (zOfNat n) (unsigned y))) false := by
  have hy : unsigned y = zOfNat y.val :=
    WordCore.intval_eq_zOfNat_val y
  have hadd : zAdd (zOfNat n) (unsigned y) = zOfNat (n + y.val) := by
    rw [hy]
    apply intOfZ_injective
    simp only [zAdd, ZArith.BinInt.Z.add, zOfNat,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast,
      Int.natCast_add]
  rw [hadd, suffix_testbit_nat, suffix_shru_val]
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  rw [Nat.add_comm y.val n]
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt (zOfNat (n + y.val)) zwordsize with
  | left hlt' =>
      simp only [zltSelect, sumboolSelect, hlt]
      exact (suffix_testbit_nat x (n + y.val)).symm
  | right hlt' =>
      simp only [zltSelect, sumboolSelect, hlt]
      apply Nat.testBit_lt_two_pow
      have hsum : wordsize ≤ n + y.val := by
        change zLe zwordsize (zOfNat (n + y.val)) at hlt'
        change intOfZ zwordsize ≤ intOfZ (zOfNat (n + y.val)) at hlt'
        simp only [zwordsize, zOfNat, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt] at hlt'
        exact Int.ofNat_le.mp hlt'
      have hpow : 2 ^ wordsize ≤ 2 ^ (n + y.val) :=
        Nat.pow_le_pow_right Nat.zero_lt_two hsum
      exact Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow

theorem bits_shru_proof : bits_shru := by
  intro x y i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_shru_nat x y 0
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      exact suffix_bits_shru_nat x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

theorem half_modulus_pos_proof : half_modulus_pos := by
  change zLt zZero (zTwoPowerNat (wordsize - 1))
  change (0 : Int) < Int.ofNat (2 ^ (wordsize - 1))
  decide

theorem same_bits_eq_proof : same_bits_eq := by
  intro x y h
  apply WordCore.ext_of_val_eq
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < wordsize
  · have hi0 : zLe zZero (zOfNat i) := by
      change 0 ≤ intOfZ (zOfNat i)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact Int.natCast_nonneg _
    have hil : zLt (zOfNat i) zwordsize := by
      change intOfZ (zOfNat i) < intOfZ (zOfNat wordsize)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact Int.ofNat_lt.mpr (by simpa [wordsize] using hi)
    have hh := h (zOfNat i) ⟨hi0, hil⟩
    rw [suffix_testbit_nat, suffix_testbit_nat] at hh
    exact hh
  · have hle : wordsize ≤ i := Nat.le_of_not_gt hi
    have hpow : 2 ^ wordsize ≤ 2 ^ i :=
      Nat.pow_le_pow_right Nat.zero_lt_two hle
    have hxlt : x.val < 2 ^ i :=
      Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
    have hylt : y.val < 2 ^ i :=
      Nat.lt_of_lt_of_le (WordCore.val_lt y) hpow
    rw [Nat.testBit_lt_two_pow hxlt, Nat.testBit_lt_two_pow hylt]

theorem ltu_not_proof : ltu_not := by
  intro x y
  change zltSelect (unsigned y) (unsigned x) true false =
    (!zltSelect (unsigned x) (unsigned y) true false &&
      !decide (x.intval = y.intval))
  cases hxy : CompCert4Lean.Lib.Coqlib.zlt (unsigned y) (unsigned x) with
  | left hlt =>
      cases hrev : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
      | left hrevlt =>
          exact (Int.lt_asymm hlt hrevlt).elim
      | right hrevge =>
          have hne : x.intval ≠ y.intval := by
            intro heq
            have hlt' : intOfZ (unsigned y) < intOfZ (unsigned x) := hlt
            change intOfZ y.intval < intOfZ x.intval at hlt'
            rw [heq] at hlt'
            exact (Int.lt_irrefl _ hlt').elim
          simp [zltSelect, sumboolSelect, hxy, hrev, hne]
  | right hge =>
      cases hrev : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
      | left hrevlt =>
          simp [zltSelect, sumboolSelect, hxy, hrev]
      | right hrevge =>
          have hge' : intOfZ (unsigned x) ≤ intOfZ (unsigned y) := by
            exact hge
          have hrevge' : intOfZ (unsigned y) ≤ intOfZ (unsigned x) := by
            exact hrevge
          have huv : unsigned y = unsigned x := by
            apply intOfZ_injective
            exact Int.le_antisymm hrevge' hge'
          have heqv : x.intval = y.intval := by
            simpa only [unsigned, WordCore.unsigned] using huv.symm
          simp [zltSelect, sumboolSelect, hxy, hrev, heqv]

theorem divmodu2_divu_modu_proof : divmodu2_divu_modu := by
  intro n d hd
  unfold divmodu2 divu modu
  by_cases hdz : d = zero
  · exact (hd hdz).elim
  · have hsum :
        zAdd (zMul (unsigned zero) modulus) (unsigned n) = unsigned n := by
      apply intOfZ_injective
      simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
        intOfZ_zOfInt]
      have hz : intOfZ (unsigned zero) = (0 : Int) := by rfl
      rw [hz]
      omega
    rw [hsum]
    simp [eq_dec, hdz]
    have hn0 : (0 : Int) ≤ intOfZ (unsigned n) := by
      have hn := n.intrange.1
      change (-1 : Int) < intOfZ n.intval at hn
      change 0 ≤ intOfZ n.intval
      omega
    have hnmax : intOfZ (unsigned n) ≤ intOfZ max_unsigned := by
      have hn := n.intrange.2
      change intOfZ n.intval < intOfZ modulus at hn
      change intOfZ n.intval ≤ intOfZ modulus - 1
      omega
    have hd0 : (0 : Int) ≤ intOfZ (unsigned d) := by
      have hd' := d.intrange.1
      change (-1 : Int) < intOfZ d.intval at hd'
      change 0 ≤ intOfZ d.intval
      omega
    have hdpos : (0 : Int) < intOfZ (unsigned d) := by
      have hdne : intOfZ (unsigned d) ≠ 0 := by
        intro hzero
        apply hd
        apply WordCore.ext
        apply intOfZ_injective
        change intOfZ d.intval = 0 at hzero
        have hz0 : intOfZ zero.intval = 0 := by rfl
        exact hzero.trans hz0.symm
      omega
    have hqbound : zLe (ZArith.BinInt.Z.div_eucl
        (unsigned n) (unsigned d)).1 max_unsigned := by
      have hb := CompCert4Lean.Lib.Coqlib.Zdiv_interval_1
        zZero (zAdd max_unsigned zOne) (unsigned n) (unsigned d)
        (by
          change (0 : Int) ≤ 0
          omega) (by
          change (0 : Int) < intOfZ (zAdd max_unsigned zOne)
          simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
          change (0 : Int) < (2 ^ wordsize : Int)
          exact Int.pow_pos (by omega))
        (by exact hdpos)
        (by
          constructor
          · change intOfZ (zMul zZero (unsigned d)) ≤ intOfZ (unsigned n)
            simp only [zMul, ZArith.BinInt.Z.mul]
            simp only [intOfZ_zOfInt]
            have hz0 : intOfZ zZero = (0 : Int) := by rfl
            rw [hz0, Int.zero_mul]
            exact hn0
          · change intOfZ (unsigned n) < intOfZ
              (zMul (zAdd max_unsigned zOne) (unsigned d))
            have hmax : intOfZ max_unsigned = (2 ^ wordsize : Int) - 1 := by
              rfl
            have hone : intOfZ zOne = (1 : Int) := by rfl
            have hmul : intOfZ (unsigned n) ≤
                ((2 ^ wordsize : Int) - 1) * intOfZ (unsigned d) := by
              have hnd := Int.mul_le_mul_of_nonneg_left
                (show (1 : Int) ≤ intOfZ (unsigned d) by omega) hn0
              have hmaxd := Int.mul_le_mul_of_nonneg_right hnmax hd0
              exact Int.le_trans (by simpa using hnd) (by simpa [hmax] using hmaxd)
            have hstrict : ((2 ^ wordsize : Int) - 1) * intOfZ (unsigned d) <
                (((2 ^ wordsize : Int) - 1) + 1) * intOfZ (unsigned d) := by
              apply Int.mul_lt_mul_of_pos_right _ hdpos
              omega
            have hlt : intOfZ (unsigned n) <
                (((2 ^ wordsize : Int) - 1) + 1) * intOfZ (unsigned d) :=
              Int.lt_of_le_of_lt hmul hstrict
            simpa [zMul, zAdd, ZArith.BinInt.Z.mul,
              ZArith.BinInt.Z.add, intOfZ_zOfInt, hmax, hone] using hlt)
      have hqhi := hb.2
      change intOfZ (ZArith.BinInt.Z.div_eucl
          (unsigned n) (unsigned d)).1 <
        intOfZ (zAdd max_unsigned zOne) at hqhi
      change intOfZ (ZArith.BinInt.Z.div_eucl
          (unsigned n) (unsigned d)).1 ≤ intOfZ max_unsigned
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hqhi ⊢
      have hmax : intOfZ max_unsigned = (2 ^ wordsize : Int) - 1 := by
        rfl
      have hone : intOfZ zOne = (1 : Int) := by rfl
      rw [hmax] at hqhi ⊢
      rw [hone] at hqhi
      omega
    cases hle : CompCert4Lean.Lib.Coqlib.zle
        (ZArith.BinInt.Z.div_eucl (unsigned n) (unsigned d)).1 max_unsigned with
    | left hle' =>
        simp [hle, ZArith.BinInt.Z.div_eucl]
        constructor <;> rfl
    | right hle' =>
        exfalso
        exact (Int.not_lt_of_ge hqbound hle').elim

theorem eq_false_proof : eq_false := by
  intro x y hxy
  change decide (x.intval = y.intval) = false
  have hval : x.intval ≠ y.intval := by
    intro h
    exact hxy (WordCore.ext h)
  simp [hval]

theorem negate_cmp_proof : negate_cmp := by
  intro c x y
  cases c <;> simp [cmp, WordCore.cmp, negate_comparison]

theorem eq_signed_proof : eq_signed := by
  intro x y
  change decide (x.intval = y.intval) =
    sumboolSelect (CompCert4Lean.Lib.Coqlib.zeq (signed x) (signed y)) true false
  cases h : CompCert4Lean.Lib.Coqlib.zeq (signed x) (signed y) with
  | left hs =>
      have hxy : x = y := signed_injective_try hs
      subst y
      simp [sumboolSelect]
  | right hs =>
      have hxy : x ≠ y := by
        intro heq
        apply hs
        simpa [heq]
      have hval : x.intval ≠ y.intval := by
        intro hv
        exact hxy (WordCore.ext hv)
      simp [sumboolSelect, hval]

private theorem suffix_xor_val_exact (x y : int) :
    (xor x y).val = Nat.xor x.val y.val := by
  have hu := suffix_xor_unsigned x y
  change (xor x y).intval = zOfNat (Nat.xor x.val y.val) at hu
  rw [WordCore.intval_eq_zOfNat_val] at hu
  have hi := congrArg intOfZ hu
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hi
  exact Int.ofNat.inj hi

private theorem suffix_bits_xor_nat (x y : int) (n : Nat) :
    testbit (xor x y) (zOfNat n) =
      Bool.xor (testbit x (zOfNat n)) (testbit y (zOfNat n)) := by
  rw [suffix_testbit_nat, suffix_testbit_nat, suffix_testbit_nat]
  rw [suffix_xor_val_exact, Nat.xor_eq, Nat.testBit_xor]

theorem bits_xor_proof : bits_xor := by
  intro x y i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_xor_nat x y 0
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      exact suffix_bits_xor_nat x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

theorem eq_true_proof : eq_true := by
  intro x
  change decide (x.intval = x.intval) = true
  simp

theorem unsigned_range_2_proof : unsigned_range_2 := by
  intro i
  constructor
  · have h := i.intrange.1
    change (-1 : Int) < intOfZ (unsigned i) at h
    change 0 ≤ intOfZ (unsigned i)
    omega
  · have h := i.intrange.2
    change intOfZ (unsigned i) < intOfZ modulus at h
    change intOfZ (unsigned i) ≤ intOfZ max_unsigned
    change intOfZ (unsigned i) ≤ (2 ^ wordsize : Int) - 1
    change intOfZ (unsigned i) < (2 ^ wordsize : Int) at h
    omega

theorem eqm_signed_unsigned_proof : eqm_signed_unsigned := by
  intro x
  unfold eqm WordCore.eqm signed WordCore.signed
  cases h : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left hlt =>
      simp only [zltSelect, sumboolSelect, h]
      exact CompCert4Lean.Lib.Zbits.eqmod_refl modulus (unsigned x)
  | right hge =>
      simp only [zltSelect, sumboolSelect, h]
      unfold CompCert4Lean.Lib.Zbits.eqmod
      refine ⟨zOpp zOne, ?_⟩
      apply intOfZ_injective
      simp only [unsigned, zOne, modulus, ZArith.BinInt.Z.add,
        ZArith.BinInt.Z.mul, ZArith.BinInt.Z.sub,
        ZArith.BinInt.Z.opp, intOfZ_zOfInt]
      have hone : intOfZ (Numbers.BinNums.Z.Zpos xH) = (1 : Int) := by rfl
      rw [hone]
      omega

private theorem suffix_repr_nat_val (a : Nat) (ha : a < 2 ^ wordsize) :
    (WordCore.repr wordsize (zOfInt (Int.ofNat a))).val = a := by
  rw [WordCore.val_repr]
  change Int.toNat (Int.ofNat a % Int.ofNat (2 ^ wordsize)) = a
  simp only [Int.ofNat_eq_natCast]
  have hbridge := Int.emod_natAbs_of_nonneg
    (x := (a : Int)) (n := 2 ^ wordsize) (Int.natCast_nonneg _)
  simp only [Int.natAbs_natCast] at hbridge
  rw [← hbridge, Nat.mod_eq_of_lt ha]

private theorem suffix_repr_testbit_nat (a i : Nat) (hi : i < wordsize) :
    testbit (WordCore.repr wordsize (zOfInt (Int.ofNat a))) (zOfNat i) =
      a.testBit i := by
  rw [suffix_testbit_nat, WordCore.val_repr]
  change (Int.toNat (Int.ofNat a % Int.ofNat (2 ^ wordsize))).testBit i = a.testBit i
  simp only [Int.ofNat_eq_natCast]
  have hbridge := Int.emod_natAbs_of_nonneg
    (x := (a : Int)) (n := 2 ^ wordsize) (Int.natCast_nonneg _)
  simp only [Int.natAbs_natCast] at hbridge
  rw [← hbridge, Nat.testBit_mod_two_pow]
  simp [hi]

private theorem suffix_repr_val_testbit_nat (a i : Nat) (hi : i < wordsize) :
    (WordCore.repr wordsize (zOfInt (Int.ofNat a))).val.testBit i =
      a.testBit i := by
  rw [WordCore.val_repr]
  change (Int.toNat (Int.ofNat a % Int.ofNat (2 ^ wordsize))).testBit i = a.testBit i
  simp only [Int.ofNat_eq_natCast]
  have hbridge := Int.emod_natAbs_of_nonneg
    (x := (a : Int)) (n := 2 ^ wordsize) (Int.natCast_nonneg _)
  simp only [Int.natAbs_natCast] at hbridge
  rw [← hbridge, Nat.testBit_mod_two_pow]
  simp [hi]


private theorem suffix_repr_sub_nat_val (r m : Nat)
    (hrm : r < m) (hmw : m ≤ 2 ^ wordsize) :
    (WordCore.repr wordsize
      (zOfInt (Int.ofNat r - Int.ofNat m))).val =
      2 ^ wordsize - (m - r) := by
  rw [WordCore.val_repr]
  change Int.toNat
      ((Int.ofNat r - Int.ofNat m) % Int.ofNat (2 ^ wordsize)) =
    2 ^ wordsize - (m - r)
  have hsub : (Int.ofNat r - Int.ofNat m) = -Int.ofNat (m - r) := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_sub (Nat.le_of_lt hrm)]
    omega
  rw [hsub, Int.neg_emod_eq_sub_emod]
  have hnonneg : (0 : Int) ≤ Int.ofNat (2 ^ wordsize) - Int.ofNat (m - r) := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hlt : Int.ofNat (2 ^ wordsize) - Int.ofNat (m - r) <
      Int.ofNat (2 ^ wordsize) := by
    simp only [Int.ofNat_eq_natCast]
    have hmr : 0 < m - r := Nat.sub_pos_of_lt hrm
    omega
  rw [Int.emod_eq_of_lt hnonneg hlt]
  have hmr_le : m - r ≤ 2 ^ wordsize := by omega
  have hcast := Int.ofNat_sub hmr_le
  exact (congrArg Int.toNat hcast).symm.trans (Int.toNat_natCast _)

private theorem suffix_sign_ext_testbit_nat (k : Nat) (x : int) (i : Nat)
    (hi : i < wordsize) :
    testbit (sign_ext (zOfNat (k + 1)) x) (zOfNat i) =
      if i < k + 1 then x.val.testBit i else x.val.testBit k := by
  rw [suffix_testbit_nat, suffix_sign_ext_nat]
  by_cases hr : x.val % 2 ^ (k + 1) < 2 ^ k
  · rw [if_pos hr, suffix_repr_val_testbit_nat]
    rw [Nat.testBit_mod_two_pow]
    by_cases hik : i < k + 1
    · simp [hik]
    · simp [hik]
      have hmod := Nat.testBit_mod_two_pow x.val (k + 1) k
      have hkm : k < k + 1 := by omega
      simp only [hkm, decide_true] at hmod
      have hmod' : (x.val % 2 ^ (k + 1)).testBit k = x.val.testBit k := by
        simpa using hmod
      have hrbit : (x.val % 2 ^ (k + 1)).testBit k = false :=
        Nat.testBit_lt_two_pow (by omega)
      rw [← hmod', hrbit]
    exact hi
  ·
    have hxlt : x.val < 2 ^ wordsize := WordCore.val_lt x
    have hrlt : x.val % 2 ^ (k + 1) < 2 ^ (k + 1) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hkmw : k + 1 ≤ wordsize := by
      by_cases hkmw : k + 1 ≤ wordsize
      · exact hkmw
      · have hkw : wordsize ≤ k := by omega
        have hpow : 2 ^ wordsize ≤ 2 ^ k :=
          Nat.pow_le_pow_right Nat.zero_lt_two hkw
        have hxM : x.val < 2 ^ (k + 1) := by
          exact Nat.lt_of_lt_of_le hxlt
            (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
        have hrx : x.val % 2 ^ (k + 1) = x.val := Nat.mod_eq_of_lt hxM
        have hrge : 2 ^ k ≤ x.val := by
          rw [← hrx]
          exact Nat.le_of_not_gt hr
        omega
    have hmle : 2 ^ (k + 1) ≤ 2 ^ wordsize :=
      Nat.pow_le_pow_right Nat.zero_lt_two hkmw
    have hrepr := suffix_repr_sub_nat_val
      (x.val % 2 ^ (k + 1)) (2 ^ (k + 1)) hrlt hmle
    rw [if_neg hr, hrepr]
    let r := x.val % 2 ^ (k + 1)
    let m := 2 ^ (k + 1)
    let w := 2 ^ wordsize
    have hrm : r < m := by exact hrlt
    have hkm : k < k + 1 := by omega
    have hwm : w = m * 2 ^ (wordsize - (k + 1)) := by
      dsimp [w, m]
      rw [← Nat.pow_add]
      congr 1
      omega
    have hbase : w - m = m * (2 ^ (wordsize - (k + 1)) - 1) := by
      rw [hwm]
      calc
        m * 2 ^ (wordsize - (k + 1)) - m =
            m * 2 ^ (wordsize - (k + 1)) - m * 1 := by rw [Nat.mul_one]
        _ = m * (2 ^ (wordsize - (k + 1)) - 1) :=
          (Nat.mul_sub_left_distrib m (2 ^ (wordsize - (k + 1))) 1).symm
    have hout : (w - (m - r)) % m = r := by
      have hmw : m ≤ w := by exact hmle
      have hdecomp : w - (m - r) = (w - m) + r := by omega
      rw [hdecomp, hbase, Nat.add_mod, Nat.mul_mod_right]
      simp only [Nat.zero_add]
      rw [Nat.mod_mod, Nat.mod_eq_of_lt hrm]
    by_cases hik : i < k + 1
    · have hlow : (w - (m - r)).testBit i = r.testBit i := by
        have hh := Nat.testBit_mod_two_pow (w - (m - r)) (k + 1) i
        simp only [hik, decide_true, true_and] at hh
        rw [hout] at hh
        exact hh.symm
      have hxr := Nat.testBit_mod_two_pow x.val (k + 1) i
      have hxr' : (x.val % 2 ^ (k + 1)).testBit i = x.val.testBit i := by
        simpa [hik] using hxr
      rw [hlow]
      simpa [hik, hxr']
    · have hq : m - r - 1 < 2 ^ i := by
        have hrpos : 0 < r := by
          have hrge : 2 ^ k ≤ r := Nat.le_of_not_gt hr
          omega
        have hpowi : 2 ^ (k + 1) ≤ 2 ^ i :=
          Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt hik)
        exact Nat.lt_of_lt_of_le (by omega) hpowi
      have hqbit : (m - r - 1).testBit i = false :=
        Nat.testBit_lt_two_pow hq
      have hmrpos : 0 < m - r := Nat.sub_pos_of_lt hrm
      have hform : w - (m - r) = 2 ^ wordsize - ((m - r - 1) + 1) := by
        omega
      have hhigh : (w - (m - r)).testBit i = true := by
        have hqW : m - r - 1 < 2 ^ wordsize :=
          Nat.lt_of_lt_of_le hq
            (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_lt hi))
        have htb := Nat.testBit_two_pow_sub_succ hqW i
        rw [hform, htb]
        simp [hi, hqbit]
      have hrbit : r.testBit k = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        apply decide_eq_true
        have hdiv := Nat.div_eq_of_lt_le
          (k := 1) (n := 2 ^ k) (m := r) (by omega)
          (by
            rw [show (1 + 1) * 2 ^ k = 2 ^ (k + 1) by
              rw [Nat.pow_succ]
              omega]
            exact hrm)
        rw [hdiv]
      have hxbit : x.val.testBit k = true := by
        have hxr := Nat.testBit_mod_two_pow x.val (k + 1) k
        have hxr' : (x.val % 2 ^ (k + 1)).testBit k = x.val.testBit k := by
          simpa [hkm] using hxr
        rw [← hxr', hrbit]
      rw [hhigh]
      simp [hik, hxbit]

private theorem suffix_zltSelect_nat_index (i n : Nat) (hn : 0 < n) :
    zltSelect (zOfNat i) (zOfNat n) (zOfNat i)
        (zSub (zOfNat n) zOne) =
      if i < n then zOfNat i else zOfNat (n - 1) := by
  have hsub : zSub (zOfNat n) zOne = zOfNat (n - 1) := by
    apply intOfZ_injective
    simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
      ZArith.BinInt.Z.of_nat, zOne, intOfZ_zOfInt]
    change Int.ofNat n - 1 = Int.ofNat (n - 1)
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [hsub]
  cases hs : CompCert4Lean.Lib.Coqlib.zlt (zOfNat i) (zOfNat n) with
  | left hlt =>
      have hin : i < n := by
        change intOfZ (zOfNat i) < intOfZ (zOfNat n) at hlt
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
        exact Int.ofNat_lt.mp hlt
      simp [zltSelect, sumboolSelect, hs, hin]
  | right hge =>
      have hin : ¬ i < n := by
        change intOfZ (zOfNat n) ≤ intOfZ (zOfNat i) at hge
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hge
        exact Nat.not_lt.mpr (Int.ofNat_le.mp hge)
      simp [zltSelect, sumboolSelect, hs, hin]

private theorem suffix_sign_ext_testbit_pos_nat (n : Nat) (hn : 0 < n)
    (x : int) (i : Nat) (hi : i < wordsize) :
    testbit (sign_ext (zOfNat n) x) (zOfNat i) =
      testbit x
        (zltSelect (zOfNat i) (zOfNat n) (zOfNat i)
          (zSub (zOfNat n) zOne)) := by
  have hnstep : n = (n - 1) + 1 := by omega
  have hmain := suffix_sign_ext_testbit_nat (n - 1) x i hi
  rw [← hnstep] at hmain
  rw [suffix_zltSelect_nat_index i n hn]
  by_cases hin : i < n
  · simpa [hin, suffix_testbit_nat] using hmain
  · simpa [hin, suffix_testbit_nat] using hmain

private theorem suffix_sign_ext_nonpos (n : Z) (x : int)
    (hn : zLe n zZero) : sign_ext n x = zero := by
  unfold sign_ext WordCore.sign_ext
  have hpred : Int.toNat (intOfZ (ZArith.BinInt.Z.pred n)) = 0 := by
    rw [Int.toNat_eq_zero]
    change intOfZ (ZArith.BinInt.Z.sub n zOne) ≤ 0
    simp only [ZArith.BinInt.Z.sub, zOne, intOfZ_zOfInt]
    have hone : intOfZ (Numbers.BinNums.Z.Zpos xH) = (1 : Int) := by rfl
    rw [hone]
    change intOfZ n ≤ 0 at hn
    omega
  have hsel : sumboolSelect (CompCert4Lean.Lib.Coqlib.zlt zZero n)
      (zOpp zOne) zZero = zZero := by
    cases hs : CompCert4Lean.Lib.Coqlib.zlt zZero n with
    | left hlt =>
        exfalso
        change 0 < intOfZ n at hlt
        change intOfZ n ≤ 0 at hn
        omega
    | right _ => rfl
  simp [ZArith.BinInt.Z.iter, hpred, hsel]
  change WordCore.repr wordsize zZero = zero
  rfl

private theorem suffix_testbit_negative_index (x : int) (j : Z)
    (hj : intOfZ j < 0) : testbit x j = false := by
  cases j with
  | Z0 =>
      change (0 : Int) < 0 at hj
      omega
  | Zpos p =>
      change Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) < 0 at hj
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Zneg _ => rfl

private theorem suffix_bits_sign_ext_nat (n : Z) (x : int) (i : Nat)
    (hi : i < wordsize) :
    testbit (sign_ext n x) (zOfNat i) =
      testbit x
        (zltSelect (zOfNat i) n (zOfNat i) (zSub n zOne)) := by
  by_cases hnpos : zLt zZero n
  · have hnnonneg : zLe zZero n := by
      change 0 ≤ intOfZ n
      change 0 < intOfZ n at hnpos
      omega
    have hnrepr : zOfNat (zToNat n) = n :=
      ZArith.Znat.Z2Nat.id n hnnonneg
    have hnNat : 0 < zToNat n := by
      change 0 < Int.toNat (intOfZ n)
      by_cases hz : Int.toNat (intOfZ n) = 0
      · rw [Int.toNat_eq_zero] at hz
        change 0 < intOfZ n at hnpos
        omega
      · exact Nat.pos_of_ne_zero hz
    rw [← hnrepr]
    exact suffix_sign_ext_testbit_pos_nat (zToNat n) hnNat x i hi
  · have hnle : zLe n zZero := by
      change intOfZ n ≤ 0
      change ¬ 0 < intOfZ n at hnpos
      omega
    have hsel : zltSelect (zOfNat i) n (zOfNat i) (zSub n zOne) =
        zSub n zOne := by
      cases hs : CompCert4Lean.Lib.Coqlib.zlt (zOfNat i) n with
      | left hlt =>
          exfalso
          change intOfZ (zOfNat i) < intOfZ n at hlt
          simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
          change intOfZ n ≤ 0 at hnle
          have hi0 : (0 : Int) ≤ Int.ofNat i := Int.natCast_nonneg i
          omega
      | right _ => simp [zltSelect, sumboolSelect, hs]
    have hidxneg : intOfZ (zSub n zOne) < 0 := by
      simp only [zSub, ZArith.BinInt.Z.sub, zOne, intOfZ_zOfInt]
      have hone : intOfZ (Numbers.BinNums.Z.Zpos xH) = (1 : Int) := by rfl
      rw [hone]
      change intOfZ n ≤ 0 at hnle
      omega
    rw [suffix_sign_ext_nonpos n x hnle, hsel]
    rw [suffix_testbit_negative_index x (zSub n zOne) hidxneg]
    rw [suffix_testbit_nat]
    have hz : zero.val = 0 := by rfl
    simp [hz]

theorem bits_sign_ext_proof : bits_sign_ext := by
  intro n x i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_sign_ext_nat n x 0 (by decide)
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p :=
        ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      have hiNat : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p <
          wordsize := by
        have hb := hi.2
        change intOfZ (zOfNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) <
          intOfZ (zOfNat wordsize) at hb
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hb
        exact Int.ofNat_lt.mp hb
      exact suffix_bits_sign_ext_nat n x
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) hiNat

theorem mul_add_distr_l_proof : mul_add_distr_l := by
  intro x y z
  change WordCore.mul (WordCore.add x y) z =
    WordCore.add (WordCore.mul x z) (WordCore.mul y z)
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [suffix_wordcore_mul_val_int (WordCore.add x y) z,
    WordCore.add_val_int x y,
    WordCore.add_val_int (WordCore.mul x z) (WordCore.mul y z),
    suffix_wordcore_mul_val_int x z, suffix_wordcore_mul_val_int y z]
  let m : Int := Int.ofNat (2 ^ wordsize)
  change
    (((Int.ofNat x.val + Int.ofNat y.val) % m) * Int.ofNat z.val) % m =
      ((Int.ofNat x.val * Int.ofNat z.val) % m +
        (Int.ofNat y.val * Int.ofNat z.val) % m) % m
  calc
    (((Int.ofNat x.val + Int.ofNat y.val) % m) * Int.ofNat z.val) % m =
        ((((Int.ofNat x.val + Int.ofNat y.val) % m) % m) *
          (Int.ofNat z.val % m)) % m := Int.mul_emod _ _ _
    _ = (((Int.ofNat x.val + Int.ofNat y.val) % m) *
          (Int.ofNat z.val % m)) % m := by
      rw [Int.emod_emod]
    _ = ((Int.ofNat x.val + Int.ofNat y.val) * Int.ofNat z.val) % m :=
      (Int.mul_emod _ _ _).symm
    _ = (Int.ofNat x.val * Int.ofNat z.val +
          Int.ofNat y.val * Int.ofNat z.val) % m := by
      rw [Int.add_mul]
    _ = ((Int.ofNat x.val * Int.ofNat z.val) % m +
          (Int.ofNat y.val * Int.ofNat z.val) % m) % m :=
      Int.add_emod _ _ _

theorem not_involutive_proof : not_involutive := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.not (WordCore.not x)).val = x.val
  rw [suffix_not_val, suffix_not_val, Nat.xor_eq, Nat.xor_eq, Nat.xor_assoc,
    Nat.xor_self, Nat.xor_zero]

theorem ltu_iwordsize_inv_proof : ltu_iwordsize_inv := by
  intro x h
  have hx := ltu_inv_proof x iwordsize h
  rw [unsigned_repr_wordsize_proof] at hx
  exact hx

theorem shl_shl_proof : shl_shl := by
  intro x y z hy hz _hyz
  have hyv := suffix_ltu_iwordsize_val y hy
  have hzv := suffix_ltu_iwordsize_val z hz
  have hyzlt : y.val + z.val < 2 ^ wordsize := by
    change y.val < 32 at hyv
    change z.val < 32 at hzv
    change y.val + z.val < 2 ^ 32
    omega
  apply WordCore.ext_of_val_eq
  change (WordCore.shl (WordCore.shl x y) z).val =
    (WordCore.shl x (WordCore.add y z)).val
  rw [suffix_shl_val, suffix_shl_val, suffix_shl_val]
  rw [WordCore.add_val, Nat.mod_eq_of_lt hyzlt]
  rw [Nat.pow_add]
  rw [← Nat.mul_assoc]
  exact Nat.mod_mul_mod _ _ _

theorem unsigned_repr_eq_proof : unsigned_repr_eq := by
  intro x
  exact suffix_unsigned_repr_eq_exact x

theorem eqm_sym_proof : eqm_sym := by
  intro x y h
  unfold eqm WordCore.eqm CompCert4Lean.Lib.Zbits.eqmod at h ⊢
  rcases h with ⟨k, hk⟩
  refine ⟨zOpp k, ?_⟩
  apply intOfZ_injective
  have hk' := congrArg intOfZ hk
  simp only [zAdd, zMul, zOpp, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.mul, ZArith.BinInt.Z.opp, intOfZ_zOfInt] at hk' ⊢
  change intOfZ y = -intOfZ k * intOfZ modulus + intOfZ x
  change intOfZ x = intOfZ k * intOfZ modulus + intOfZ y at hk'
  rw [hk']
  simp only [Int.neg_mul]
  omega

theorem sub_add_l_proof : sub_add_l := by
  intro x y z
  change WordCore.sub (WordCore.add x y) z =
    WordCore.add (WordCore.sub x z) y
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int, WordCore.add_val_int,
    WordCore.sub_val_int]
  simp only [Int.emod_sub_emod, Int.sub_emod_emod, Int.emod_add_emod,
    Int.add_emod_emod]
  congr 1
  omega

theorem xor_assoc_proof : xor_assoc := by
  intro x y z
  apply WordCore.ext_of_val_eq
  rw [suffix_xor_val_exact, suffix_xor_val_exact,
    suffix_xor_val_exact, suffix_xor_val_exact]
  exact Nat.xor_assoc _ _ _

theorem eqm_refl_proof : eqm_refl := by
  intro x
  exact CompCert4Lean.Lib.Zbits.eqmod_refl modulus x

theorem or_commut_proof : or_commut := by
  intro x y
  apply WordCore.ext_of_val_eq
  change (WordCore.or x y).val = (WordCore.or y x).val
  rw [suffix_or_val, suffix_or_val, Nat.lor_eq, Nat.lor_eq]
  exact Nat.or_comm _ _

private theorem suffix_bits_or_nat (x y : int) (n : Nat) :
    testbit (or x y) (zOfNat n) =
      (testbit x (zOfNat n) || testbit y (zOfNat n)) := by
  change testbit (WordCore.or x y) (zOfNat n) =
    (testbit x (zOfNat n) || testbit y (zOfNat n))
  rw [suffix_testbit_nat, suffix_testbit_nat, suffix_testbit_nat]
  rw [suffix_or_val, Nat.lor_eq, Nat.testBit_or]

theorem bits_or_proof : bits_or := by
  intro x y i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_or_nat x y 0
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      exact suffix_bits_or_nat x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

private theorem suffix_positive_is_power2
    (p : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive)
    (h : CompCert4Lean.Lib.Zbits.P_is_power2 p = true) :
    ∃ k : Nat,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p = 2 ^ k := by
  induction p with
  | xH => exact ⟨0, rfl⟩
  | xI p ih => simp [CompCert4Lean.Lib.Zbits.P_is_power2] at h
  | xO p ih =>
      rcases ih h with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat, hk,
        Nat.pow_succ]
      omega

private theorem suffix_is_power2_nat
    (n logn : int) (hpow : is_power2 n = some logn) :
    ∃ k : Nat, n.val = 2 ^ k := by
  unfold is_power2 at hpow
  cases hu : unsigned n with
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
          rcases suffix_positive_is_power2 p hp with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          have hz : zOfNat n.val = .Zpos p := by
            exact (WordCore.intval_eq_zOfNat_val n).symm.trans hu
          have hi : Int.ofNat n.val = Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
            calc
              Int.ofNat n.val = intOfZ (zOfNat n.val) := by
                exact (intOfZ_zOfInt (Int.ofNat n.val)).symm
              _ = intOfZ (.Zpos p) := congrArg intOfZ hz
              _ = Int.ofNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
                rfl
          exact (Int.ofNat.inj hi).trans hk

private theorem suffix_sub_one_val
    (n : int) (hnpos : 0 < n.val) :
    (sub n one).val = n.val - 1 := by
  change (WordCore.sub n (WordCore.one wordsize)).val = n.val - 1
  rw [WordCore.sub_val]
  change (2 ^ wordsize - 1 + n.val) % (2 ^ wordsize) = n.val - 1
  have hnlt : n.val < 2 ^ wordsize := WordCore.val_lt n
  have hadd : 2 ^ wordsize - 1 + n.val =
      (n.val - 1) + 2 ^ wordsize := by omega
  rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem suffix_modulo_nat (a b : Nat) (hb : 0 < b) :
    ZArith.BinInt.Z.modulo (zOfNat a) (zOfNat b) = zOfNat (a % b) := by
  have hdecompNat : a = a % b + b * (a / b) := by
    exact (Nat.mod_add_div a b).symm
  have hdecompNat' : a = a % b + (a / b) * b := by
    simpa [Nat.mul_comm] using hdecompNat
  have hdecomp : zOfNat a =
      zAdd (zOfNat (a % b)) (zMul (zOfNat (a / b)) (zOfNat b)) := by
    apply intOfZ_injective
    simp only [zAdd, zMul, zOfNat, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.mul, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
    exact congrArg Int.ofNat hdecompNat'
  have hbZ : zLt zZero (zOfNat b) := by
    change (0 : Int) < intOfZ (zOfNat b)
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    exact Int.natCast_pos.mpr hb
  have hsmall : zLe zZero (zOfNat (a % b)) ∧
      zLt (zOfNat (a % b)) (zOfNat b) := by
    constructor
    · change (0 : Int) ≤ intOfZ (zOfNat (a % b))
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact Int.natCast_nonneg _
    · change intOfZ (zOfNat (a % b)) < intOfZ (zOfNat b)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact Int.ofNat_lt.mpr (Nat.mod_lt _ hb)
  rw [show ZArith.BinInt.Z.modulo (zOfNat a) (zOfNat b) =
      ZArith.BinInt.Z.modulo
        (zAdd (zOfNat (a % b)) (zMul (zOfNat (a / b)) (zOfNat b)))
        (zOfNat b) by rw [hdecomp]]
  rw [ZArith.Zdiv.Z_mod_plus _ _ _ hbZ]
  exact ZArith.Zdiv.Zmod_small _ _ hsmall

private theorem suffix_modu_val
    (x n : int) (hnpos : 0 < n.val) :
    (modu x n).val = x.val % n.val := by
  unfold modu WordCore.modu
  change (WordCore.repr wordsize
    (ZArith.BinInt.Z.modulo (unsigned x) (unsigned n))).val = x.val % n.val
  have hx : unsigned x = zOfNat x.val :=
    WordCore.intval_eq_zOfNat_val x
  have hn : unsigned n = zOfNat n.val :=
    WordCore.intval_eq_zOfNat_val n
  rw [hx, hn, suffix_modulo_nat _ _ hnpos]
  rw [show zOfNat (x.val % n.val) =
      zOfInt (Int.ofNat (x.val % n.val)) by rfl]
  rw [WordCore.val_repr]
  have hrem : x.val % n.val < 2 ^ wordsize :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hnpos)
      (Nat.le_of_lt (WordCore.val_lt n))
  have hmod : Int.ofNat (x.val % n.val) %
      ((2 ^ wordsize : Nat) : Int) = Int.ofNat (x.val % n.val) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by
        change Int.ofNat (x.val % n.val) < Int.ofNat (2 ^ wordsize)
        exact Int.ofNat_lt.mpr hrem)
  rw [hmod]
  exact Int.toNat_natCast _

theorem modu_and_proof : modu_and := by
  intro x n logn hpow
  rcases suffix_is_power2_nat n logn hpow with ⟨k, hnk⟩
  have hnpos : 0 < n.val := by
    rw [hnk]
    exact Nat.two_pow_pos k
  apply WordCore.ext_of_val_eq
  rw [suffix_modu_val x n hnpos]
  change _ = (WordCore.and x (WordCore.sub n (WordCore.one wordsize))).val
  rw [suffix_and_val]
  have hs : (WordCore.sub n (WordCore.one wordsize)).val = n.val - 1 := by
    exact suffix_sub_one_val n hnpos
  rw [hs, hnk]
  exact (Nat.and_two_pow_sub_one_eq_mod x.val k).symm

private theorem suffix_eqm_unsigned_repr :
    ∀ a : Z, eqm a (unsigned (repr a)) := by
  intro a
  unfold eqm WordCore.eqm CompCert4Lean.Lib.Zbits.eqmod
  refine ⟨ZArith.BinInt.Z.div a modulus, ?_⟩
  rw [unsigned_repr_eq_proof]
  have hd := ZArith.Zdiv.Z_div_mod_eq_full a modulus
  apply intOfZ_injective
  have hd' := congrArg intOfZ hd
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hd' ⊢
  change intOfZ a = intOfZ (ZArith.BinInt.Z.div a modulus) *
      intOfZ modulus + intOfZ (zMod a modulus)
  change intOfZ a = intOfZ modulus *
      intOfZ (ZArith.BinInt.Z.div a modulus) + intOfZ (zMod a modulus) at hd'
  rw [Int.mul_comm]
  exact hd'

theorem eqm_unsigned_repr_l_proof : eqm_unsigned_repr_l := by
  intro a b hab
  apply eqm_trans_proof (unsigned (repr a)) a b
  · exact eqm_sym_proof _ _ (suffix_eqm_unsigned_repr a)
  · exact hab

theorem and_idem_proof : and_idem := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.and x x).val = x.val
  rw [suffix_and_val]
  exact Nat.and_self x.val

theorem bits_not_proof : bits_not := by
  intro x i hi
  have hnot : not x = xor x mone := by
    apply WordCore.ext_of_val_eq
    change (WordCore.not x).val =
      (xor x mone).val
    rw [suffix_not_val, suffix_xor_val_exact]
    congr 1
  rw [hnot, bits_xor_proof x mone i hi, bits_mone_proof i hi]
  cases testbit x i <;> rfl

theorem xor_zero_proof : xor_zero := by
  intro x
  apply WordCore.ext_of_val_eq
  change (xor x zero).val = x.val
  rw [suffix_xor_val_exact]
  change x.val ^^^ 0 = x.val
  exact Nat.xor_zero _

theorem one_not_zero_proof : one_not_zero := by
  intro h
  have hv := congrArg (fun q : int => q.val) h
  change (WordCore.one wordsize).val = (WordCore.zero wordsize).val at hv
  change (WordCore.repr wordsize zOne).val =
    (WordCore.repr wordsize zZero).val at hv
  rw [WordCore.val_repr_residue, WordCore.val_repr_residue] at hv
  change 1 = 0 at hv
  omega

theorem add_zero_l_proof : add_zero_l := by
  intro x
  rw [add_commut_proof]
  exact add_zero_proof x

theorem shr_lt_zero_proof : shr_lt_zero := by
  intro x
  rw [shr_div_two_p_proof]
  have hy : unsigned (repr (zSub zwordsize zOne)) =
      zSub zwordsize zOne := by
    apply unsigned_repr_proof_api
    constructor
    · change (0 : Int) ≤ 31
      omega
    · change (31 : Int) ≤ (2 ^ wordsize : Int) - 1
      decide
  rw [hy]
  have hn : zLe zZero (zSub zwordsize zOne) := by
    change (0 : Int) ≤ 31
    omega
  have hpow := suffix_two_p_nonneg (zSub zwordsize zOne) hn
  have hnval : zToNat (zSub zwordsize zOne) = wordsize - 1 := by
    decide
  have hpow' : zTwoP (zSub zwordsize zOne) =
      zOfInt (Int.ofNat (2 ^ (wordsize - 1))) := by
    simpa [hnval] using hpow
  rw [hpow']
  have hdpos : (0 : Int) < Int.ofNat (2 ^ (wordsize - 1)) := by
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  by_cases hlt : lt x zero = true
  · simp [hlt]
    have hslt : zLt (signed x) zZero := by
      change zltSelect (signed x) (signed zero) true false = true at hlt
      cases hs : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
      | left hs' =>
          have hz : signed zero = zZero := by rfl
          simpa [hz] using hs'
      | right hs' => simp [zltSelect, sumboolSelect, hs] at hlt
    have hq : zDiv (signed x)
        (zOfInt (Int.ofNat (2 ^ (wordsize - 1)))) = zOpp zOne := by
      apply intOfZ_injective
      simp only [zDiv, zOpp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        intOfZ_zOfInt]
      change Int.ediv (intOfZ (signed x))
          (Int.ofNat (2 ^ (wordsize - 1))) = -1
      apply (Int.ediv_eq_iff_of_pos hdpos).2
      constructor
      · have hlo := (signed_range_proof x).1
        change (-2147483648 : Int) ≤ intOfZ (signed x) at hlo
        change (-1 : Int) * Int.ofNat (2 ^ (wordsize - 1)) ≤
          intOfZ (signed x)
        exact hlo
      · change intOfZ (signed x) < 0 at hslt
        have hd : Int.ofNat (2 ^ (wordsize - 1)) = 2147483648 := by
          decide
        rw [hd]
        omega
    change WordCore.repr wordsize
        (zDiv (signed x) (zOfInt (Int.ofNat (2 ^ (wordsize - 1))))) =
      WordCore.repr wordsize (zOpp zOne)
    rw [hq]

  · simp [hlt]
    have hsge : zLe zZero (signed x) := by
      have hlt' := hlt
      change ¬(zltSelect (signed x) (signed zero) true false = true) at hlt'
      cases hs : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed zero) with
      | left hs' => simp [zltSelect, sumboolSelect, hs] at hlt'
      | right hs' =>
          have hz : signed zero = zZero := by rfl
          have hle : zLe (signed zero) (signed x) := hs'
          simpa [hz] using hle
    have hq : zDiv (signed x)
        (zOfInt (Int.ofNat (2 ^ (wordsize - 1)))) = zZero := by
      apply intOfZ_injective
      simp only [zDiv,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div,
        intOfZ_zOfInt]
      change Int.ediv (intOfZ (signed x))
          (Int.ofNat (2 ^ (wordsize - 1))) = 0
      apply (Int.ediv_eq_iff_of_pos hdpos).2
      constructor
      · change (0 : Int) ≤ intOfZ (signed x) at hsge
        simpa using hsge
      · have hhi := (signed_range_proof x).2
        change intOfZ (signed x) ≤ (2147483647 : Int) at hhi
        change intOfZ (signed x) <
          (0 : Int) * Int.ofNat (2 ^ (wordsize - 1)) +
            Int.ofNat (2 ^ (wordsize - 1))
        have hd : Int.ofNat (2 ^ (wordsize - 1)) = 2147483648 := by
          decide
        rw [hd]
        omega
    change WordCore.repr wordsize
        (zDiv (signed x) (zOfInt (Int.ofNat (2 ^ (wordsize - 1))))) =
      WordCore.repr wordsize zZero
    rw [hq]

private theorem suffix_zsub_nat (a b : Nat) (hba : b ≤ a) :
    zSub (zOfNat a) (zOfNat b) = zOfNat (a - b) := by
  apply intOfZ_injective
  simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  exact (Int.ofNat_sub hba).symm

private theorem suffix_bitfield_nat_arith (a p w : Nat)
    (hpw : p + w ≤ 32) (hw : 0 < w) (ha : a < 2 ^ 32) :
    (a / 2 ^ p) % 2 ^ w =
      (a * 2 ^ (32 - p - w) % 2 ^ 32) / 2 ^ (32 - w) := by
  let A := 2 ^ p
  let B := 2 ^ w
  let C := 2 ^ (32 - p - w)
  let M := 2 ^ 32
  let D := 2 ^ (32 - w)
  let q := a / A
  let r := a % A
  let s := q % B
  have hp : p ≤ 32 := by omega
  have hApos : 0 < A := by dsimp [A]; exact Nat.two_pow_pos _
  have hBpos : 0 < B := by dsimp [B]; exact Nat.two_pow_pos _
  have hCpos : 0 < C := by dsimp [C]; exact Nat.two_pow_pos _
  have hDpos : 0 < D := by dsimp [D]; exact Nat.two_pow_pos _
  have hMpos : 0 < M := by dsimp [M]; exact Nat.two_pow_pos 32
  have hpow : A * B * C = M := by
    dsimp [A, B, C, M]
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    rw [Nat.sub_sub]
    rw [Nat.add_sub_of_le hpw]
  have hpow' : A * C = D := by
    dsimp [A, C, D]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hBD : B * D = M := by
    rw [← hpow']
    calc
      B * (A * C) = A * B * C := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = M := hpow
  have hqdecomp : q = (q / B) * B + s := by
    exact (Nat.div_add_mod' q B).symm
  have hadecomp : a = q * A + r := by
    exact (Nat.div_add_mod' a A).symm
  have hqa : q * A + r = (q / B * B + s) * A + r := by
    exact congrArg (fun t => t * A + r) hqdecomp
  have hcalc : a * C = (q / B) * M + s * D + r * C := by
    calc
      a * C = (q * A + r) * C := by rw [hadecomp]
      _ = ((q / B * B + s) * A + r) * C := congrArg (fun t => t * C) hqa
      _ = (q / B) * (A * B * C) + s * (A * C) + r * C := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm]
      _ = (q / B) * M + s * D + r * C := by rw [hpow, hpow']
  have hrA : r < A := by
    dsimp [r]
    exact Nat.mod_lt _ hApos
  have hsB : s < B := by
    dsimp [s]
    exact Nat.mod_lt _ hBpos
  have hrC : r * C < D := by
    have h := Nat.mul_lt_mul_of_pos_right hrA hCpos
    rw [hpow'] at h
    exact h
  have hsDadd : s * D + D ≤ M := by
    have hs1 : s + 1 ≤ B := by omega
    have h := Nat.mul_le_mul_right D hs1
    rw [Nat.add_mul, hBD] at h
    simpa only [Nat.one_mul] using h
  have hrestlt : s * D + r * C < M := by omega
  have hmod : a * C % M = s * D + r * C := by
    calc
      a * C % M = (q / B * M + s * D + r * C) % M := by rw [hcalc]
      _ = (s * D + r * C + M * (q / B)) % M := by
        congr 1
        simp only [Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = (s * D + r * C) % M := Nat.add_mul_mod_self_left _ _ _
      _ = s * D + r * C := Nat.mod_eq_of_lt hrestlt
  have hquotlo : s * D ≤ s * D + r * C := by omega
  have hquothi : s * D + r * C < (s + 1) * D := by
    rw [Nat.add_mul]
    omega
  have hquot : (a * C % M) / D = s := by
    rw [hmod]
    exact Nat.div_eq_of_lt_le hquotlo hquothi
  dsimp [A, B, C, M, D, q, r, s] at hquot ⊢
  exact hquot.symm

theorem unsigned_bitfield_extract_by_shifts_proof :
    unsigned_bitfield_extract_by_shifts := by
  intro pos width n hpos hwidth hsum
  let p := zToNat pos
  let w := zToNat width
  have hposrepr : pos = zOfNat p := by
    dsimp [p]
    exact (ZArith.Znat.Z2Nat.id pos hpos).symm
  have hwidth0 : zLe zZero width := by
    change 0 ≤ intOfZ width
    have h := hwidth
    change 0 < intOfZ width at h
    omega
  have hwrepr : width = zOfNat w := by
    dsimp [w]
    exact (ZArith.Znat.Z2Nat.id width hwidth0).symm
  have hpw : p + w ≤ 32 := by
    have hs := hsum
    rw [hposrepr, hwrepr] at hs
    change intOfZ (zAdd (zOfNat p) (zOfNat w)) ≤ intOfZ zwordsize at hs
    simp only [zAdd, ZArith.BinInt.Z.add, zOfNat,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, zwordsize] at hs
    exact Int.ofNat_le.mp hs
  have hwpos : 0 < w := by
    have h := hwidth
    rw [hwrepr] at h
    change 0 < intOfZ (zOfNat w) at h
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at h
    exact Int.ofNat_lt.mp h
  have hp_lt : p < 2 ^ 32 := by omega
  have hw_le : w ≤ 32 := by omega
  have hpval : (WordCore.repr wordsize pos).val = p := by
    rw [hposrepr, WordCore.val_repr_residue]
    have hz : zOfNat p = zOfInt (Int.ofNat p) := by rfl
    rw [hz, WordCore.residue_zOfNat]
    exact Nat.mod_eq_of_lt hp_lt
  have hwval : (WordCore.repr wordsize width).val = w := by
    rw [hwrepr, WordCore.val_repr_residue]
    have hz : zOfNat w = zOfInt (Int.ofNat w) := by rfl
    rw [hz, WordCore.residue_zOfNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hw_le (by decide : (32 : Nat) < 2 ^ 32))
  have hleft1 :
      (WordCore.zero_ext width (WordCore.shru n (WordCore.repr wordsize pos))).val =
        ((n.val / 2 ^ p) % 2 ^ w) := by
    change (zero_ext width (WordCore.shru n (WordCore.repr wordsize pos))).val = _
    rw [zero_ext_val width (WordCore.shru n (WordCore.repr wordsize pos)) hwidth0]
    change (WordCore.shru n (WordCore.repr wordsize pos)).val % 2 ^ w % 2 ^ wordsize = _
    have hshru : (WordCore.shru n (WordCore.repr wordsize pos)).val =
        n.val / 2 ^ (WordCore.repr wordsize pos).val :=
      suffix_shru_val n (WordCore.repr wordsize pos)
    rw [hshru, hpval]
    rw [Nat.mod_eq_of_lt (by
      have h := Nat.mod_lt (n.val / 2 ^ p) (Nat.two_pow_pos w)
      have hle : 2 ^ w ≤ 2 ^ wordsize :=
        Nat.pow_le_pow_right Nat.zero_lt_two hw_le
      exact Nat.lt_of_lt_of_le h hle)]
  have hsub1 :
      zSub (zSub zwordsize pos) width =
        zOfNat (32 - p - w) := by
    have hzws : zwordsize = zOfNat 32 := by rfl
    rw [hzws, hposrepr, hwrepr]
    have hinner : zSub (zOfNat 32) (zOfNat p) = zOfNat (32 - p) := by
      apply suffix_zsub_nat
      omega
    rw [hinner]
    apply suffix_zsub_nat
    omega
  have hsub2 : zSub zwordsize width = zOfNat (32 - w) := by
    have hzws : zwordsize = zOfNat 32 := by rfl
    rw [hzws, hwrepr]
    apply suffix_zsub_nat
    omega
  have hright :
      (WordCore.shru
        (WordCore.shl n (WordCore.repr wordsize (zSub (zSub zwordsize pos) width)))
      (WordCore.repr wordsize (zSub zwordsize width))).val =
      ((n.val * 2 ^ (32 - p - w)) % 2 ^ 32) /
        2 ^ (32 - w) := by
    change (shru
      (shl n (WordCore.repr wordsize (zSub (zSub zwordsize pos) width)))
      (WordCore.repr wordsize (zSub zwordsize width))).val = _
    have hshru :
        (shru
          (shl n (WordCore.repr wordsize (zSub (zSub zwordsize pos) width)))
          (WordCore.repr wordsize (zSub zwordsize width))).val =
        (shl n (WordCore.repr wordsize (zSub (zSub zwordsize pos) width))).val /
          2 ^ (WordCore.repr wordsize (zSub zwordsize width)).val :=
      suffix_shru_val
      (shl n (WordCore.repr wordsize (zSub (zSub zwordsize pos) width)))
      (WordCore.repr wordsize (zSub zwordsize width))
    have hshl :
        (shl n (WordCore.repr wordsize (zSub (zSub zwordsize pos) width))).val =
          n.val * 2 ^ (WordCore.repr wordsize
            (zSub (zSub zwordsize pos) width)).val % 2 ^ wordsize :=
      suffix_shl_val n
      (WordCore.repr wordsize (zSub (zSub zwordsize pos) width))
    rw [hshru, hshl, hsub1, hsub2]
    have hz1 : zOfNat (32 - p - w) = zOfInt (Int.ofNat (32 - p - w)) := by rfl
    have hz2 : zOfNat (32 - w) = zOfInt (Int.ofNat (32 - w)) := by rfl
    rw [hz1, hz2, WordCore.val_repr_residue, WordCore.residue_zOfNat,
      WordCore.val_repr_residue, WordCore.residue_zOfNat]
    have hpowws : (2 ^ wordsize : Nat) = 2 ^ 32 := by rfl
    rw [hpowws]
    have hk1 : 32 - p - w < 2 ^ 32 := by
      have hk1le : 32 - p - w ≤ 32 := by omega
      exact Nat.lt_of_le_of_lt hk1le (by decide)
    have hk2 : 32 - w < 2 ^ 32 := by
      have hk2le : 32 - w ≤ 32 := by omega
      exact Nat.lt_of_le_of_lt hk2le (by decide)
    rw [Nat.mod_eq_of_lt hk1, Nat.mod_eq_of_lt hk2]
  change WordCore.unsigned_bitfield_extract pos width n = _
  apply WordCore.ext_of_val_eq
  change (WordCore.zero_ext width (WordCore.shru n (WordCore.repr wordsize pos))).val = _
  change (WordCore.zero_ext width (WordCore.shru n (WordCore.repr wordsize pos))).val =
    (WordCore.shru
      (WordCore.shl n (WordCore.repr wordsize (zSub (zSub zwordsize pos) width)))
      (WordCore.repr wordsize (zSub zwordsize width))).val
  rw [hleft1, hright]
  exact suffix_bitfield_nat_arith n.val p w
    hpw hwpos (WordCore.val_lt n)

theorem mul_one_proof : mul_one := by
  intro x
  change WordCore.mul x (WordCore.one wordsize) = x
  unfold WordCore.mul
  rw [show WordCore.unsigned (WordCore.one wordsize) = Zpos xH by rfl]
  change WordCore.repr wordsize
      (ZArith.BinInt.Z.mul (WordCore.unsigned x) (Zpos xH)) = x
  rw [ZArith.BinInt.Zmult_1_r_proof]
  exact repr_unsigned_proof x

theorem eqm_refl2_proof : eqm_refl2 := by
  intro x y hxy
  subst y
  exact eqm_refl_proof x

theorem eqm_add_proof : eqm_add := by
  intro a b c d hab hcd
  exact CompCert4Lean.Lib.Zbits.eqmod_add modulus a b c d hab hcd

theorem shr_zero_proof : shr_zero := by
  intro x
  change WordCore.repr wordsize
      (ZArith.BinInt.Z.shiftr (signed x) (unsigned (WordCore.zero wordsize))) = x
  rw [show unsigned (WordCore.zero wordsize) = Z0 by rfl]
  rw [ZArith.BinInt.Z.shiftr_0_r]
  have hsu : eqm (signed x) (unsigned x) := eqm_signed_unsigned_proof x
  change repr (signed x) = x
  rw [eqm_samerepr_proof _ _ hsu, repr_unsigned_proof]

theorem mul_zero_proof : mul_zero := by
  intro x
  change WordCore.mul x (WordCore.zero wordsize) = WordCore.zero wordsize
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [suffix_wordcore_mul_val_int]
  rfl

theorem modu_divu_proof : modu_divu := by
  intro x y hy
  have hy0 : unsigned y ≠ zZero := by
    intro hz
    apply hy
    apply WordCore.ext
    change unsigned y = unsigned (WordCore.zero wordsize)
    rw [hz]
    rfl
  apply WordCore.ext
  change unsigned (modu x y) =
    unsigned (sub x (mul (divu x y) y))
  change unsigned (repr (zMod (unsigned x) (unsigned y))) =
    unsigned (repr (zSub (unsigned x)
      (unsigned (repr (zMul (unsigned (repr (zDiv (unsigned x) (unsigned y))))
        (unsigned y))))))
  rw [suffix_unsigned_repr_eq_exact, suffix_unsigned_repr_eq_exact]
  rw [suffix_unsigned_repr_eq_exact, suffix_unsigned_repr_eq_exact]
  apply intOfZ_injective
  simp only [zSub, zMul, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt]
  rw [suffix_modulo_int, suffix_modulo_int, suffix_modulo_int]
  simp only [intOfZ_zOfInt]
  have huy : (0 : Int) < intOfZ (unsigned y) := by
    have h := y.intrange.1
    change (-1 : Int) < intOfZ y.intval at h
    have hnonneg : 0 ≤ intOfZ y.intval := by omega
    have hne : intOfZ y.intval ≠ 0 := by
      intro hz
      apply hy0
      apply intOfZ_injective
      exact hz
    change 0 < intOfZ y.intval
    omega
  have hdiv := CompCert4Lean.Lib.Coqlib.Z_div_mod_eq
    (unsigned x) (unsigned y) huy
  have hdiv' := congrArg intOfZ hdiv
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hdiv'
  have hqmod : intOfZ (zMod (zDiv (unsigned x) (unsigned y)) modulus) =
      intOfZ (zDiv (unsigned x) (unsigned y)) % (2 ^ wordsize : Int) :=
    suffix_modulo_int _
  rw [hqmod]
  rw [Int.sub_emod]
  have hprodmod :
      (intOfZ (zDiv (unsigned x) (unsigned y)) % (2 ^ wordsize : Int) *
          intOfZ (unsigned y)) % (2 ^ wordsize : Int) =
      (intOfZ (zDiv (unsigned x) (unsigned y)) *
          intOfZ (unsigned y)) % (2 ^ wordsize : Int) := by
    calc
      (intOfZ (zDiv (unsigned x) (unsigned y)) % (2 ^ wordsize : Int) *
          intOfZ (unsigned y)) % (2 ^ wordsize : Int) =
          ((intOfZ (zDiv (unsigned x) (unsigned y)) % (2 ^ wordsize : Int)) %
            (2 ^ wordsize : Int) *
            (intOfZ (unsigned y) % (2 ^ wordsize : Int))) %
              (2 ^ wordsize : Int) := Int.mul_emod _ _ _
      _ = (intOfZ (zDiv (unsigned x) (unsigned y)) % (2 ^ wordsize : Int) *
          (intOfZ (unsigned y) % (2 ^ wordsize : Int))) %
            (2 ^ wordsize : Int) := by rw [Int.emod_emod]
      _ = (intOfZ (zDiv (unsigned x) (unsigned y)) *
          intOfZ (unsigned y)) % (2 ^ wordsize : Int) :=
        (Int.mul_emod _ _ _).symm
  rw [hprodmod]
  rw [← Int.sub_emod]
  have hrem : intOfZ (zMod (unsigned x) (unsigned y)) =
      intOfZ (unsigned x) -
        intOfZ (zDiv (unsigned x) (unsigned y)) * intOfZ (unsigned y) := by
    have hdiv'' := hdiv'
    rw [Int.mul_comm (intOfZ (unsigned y))
      (intOfZ (ZArith.BinInt.Z.div (unsigned x) (unsigned y)))] at hdiv''
    change intOfZ (unsigned x) =
      intOfZ (ZArith.BinInt.Z.div (unsigned x) (unsigned y)) *
        intOfZ (unsigned y) + intOfZ (zMod (unsigned x) (unsigned y)) at hdiv''
    change intOfZ (zMod (unsigned x) (unsigned y)) =
      intOfZ (unsigned x) -
        intOfZ (ZArith.BinInt.Z.div (unsigned x) (unsigned y)) *
          intOfZ (unsigned y)
    omega
  rw [hrem]
  rw [Int.sub_emod]
  rw [Int.sub_emod (intOfZ (unsigned x))
    ((intOfZ (zDiv (unsigned x) (unsigned y)) * intOfZ (unsigned y)) %
      (2 ^ wordsize : Int)) (2 ^ wordsize : Int)]
  simp only [Int.emod_emod]

private theorem test_zero_ext_nonpos (n : Z) (x : int)
    (hn : intOfZ n ≤ 0) : (zero_ext n x).val = 0 := by
  unfold zero_ext WordCore.zero_ext CompCert4Lean.Lib.Zbits.Zzero_ext
  cases n with
  | Z0 => rfl
  | Zneg p =>
      rw [WordCore.val_repr_residue]
      change WordCore.residue wordsize
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter
          (.Zneg p)
          (fun rec y =>
            CompCert4Lean.Lib.Zbits.Zshiftin
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.odd y)
              (rec (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div2 y)))
          (fun _ => CompCert4Lean.Foundation.Numbers.Rocq.Coq.Numbers.BinNums.Z.Z0)
          (WordCore.unsigned x)) = 0
      simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.iter]
      have hz : (intOfZ (.Zneg p)).toNat = 0 := by
        simp [intOfZ]
      rw [hz]
      rfl
  | Zpos p =>
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hp' : (0 : Int) < intOfZ (.Zpos p) := by
        change (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        exact Int.natCast_pos.mpr hp
      exact (Int.not_le_of_gt hp' hn).elim

private theorem suffix_bits_zero_ext_nat (n : Z) (x : int) (k : Nat)
    (hk : k < wordsize) (hn : zLe zZero n) :
    testbit (zero_ext n x) (zOfNat k) =
      zltSelect (zOfNat k) n (testbit x (zOfNat k)) false := by
  rw [suffix_testbit_nat, zero_ext_val n x hn]
  rw [Nat.testBit_mod_two_pow]
  simp only [hk, decide_true]
  rw [suffix_testbit_nat]
  have hnrepr : zOfNat (zToNat n) = n :=
    ZArith.Znat.Z2Nat.id n hn
  cases hs : CompCert4Lean.Lib.Coqlib.zlt (zOfNat k) n with
  | left hlt =>
      have hlt' : k < zToNat n := by
        rw [← hnrepr] at hlt
        change intOfZ (zOfNat k) < intOfZ (zOfNat (zToNat n)) at hlt
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
        exact Int.ofNat_lt.mp hlt
      simp [zltSelect, sumboolSelect, hs]
      simp [hlt']
  | right hge =>
      have hge' : zToNat n ≤ k := by
        rw [← hnrepr] at hge
        change intOfZ (zOfNat (zToNat n)) ≤ intOfZ (zOfNat k) at hge
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hge
        exact Int.ofNat_le.mp hge
      simp [zltSelect, sumboolSelect, hs]
      intro hbad
      exact (Nat.not_lt_of_ge hge' hbad).elim

theorem bits_zero_ext_proof : bits_zero_ext := by
  intro n x i hi
  cases i with
  | Zneg p =>
      have h := hi
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      have hk : 0 < wordsize := by decide
      by_cases hn : 0 ≤ intOfZ n
      · exact suffix_bits_zero_ext_nat n x 0 hk hn
      · have hn' : intOfZ n ≤ 0 := by omega
        change testbit (zero_ext n x) (zOfNat 0) =
          zltSelect (zOfNat 0) n (testbit x (zOfNat 0)) false
        rw [suffix_testbit_nat, test_zero_ext_nonpos n x hn']
        cases hs : CompCert4Lean.Lib.Coqlib.zlt (zOfNat 0) n with
        | left hlt =>
            exfalso
            change intOfZ (zOfNat 0) < intOfZ n at hlt
            have hzero : intOfZ (zOfNat 0) = (0 : Int) := by rfl
            rw [hzero] at hlt
            omega
        | right hge =>
            simp [zltSelect, sumboolSelect, hs]
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p :=
        ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      let k := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p
      by_cases hk : k < wordsize
      · by_cases hn : 0 ≤ intOfZ n
        · exact suffix_bits_zero_ext_nat n x k hk hn
        · have hn' : intOfZ n ≤ 0 := by omega
          rw [suffix_testbit_nat, test_zero_ext_nonpos n x hn']
          cases hs : CompCert4Lean.Lib.Coqlib.zlt (zOfNat k) n with
          | left hlt =>
              exfalso
              change intOfZ (zOfNat k) < intOfZ n at hlt
              simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
              have hk0 : (0 : Int) ≤ Int.ofNat k := Int.natCast_nonneg _
              omega
          | right hge =>
              simp [k, zltSelect, sumboolSelect, hs]
      · have hk' : wordsize ≤ k := Nat.le_of_not_gt hk
        have hiword : zLe zwordsize (zOfNat k) := by
          change intOfZ (zOfNat wordsize) ≤ intOfZ (zOfNat k)
          simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
          exact Int.ofNat_le.mpr hk'
        have hleft := bits_above_proof (zero_ext n x) (zOfNat k) hiword
        have hright := bits_above_proof x (zOfNat k) hiword
        rw [hleft, hright]
        cases hs : CompCert4Lean.Lib.Coqlib.zlt (zOfNat k) n with
        | left _ => simp [k, zltSelect, sumboolSelect, hs]
        | right _ => simp [k, zltSelect, sumboolSelect, hs]

private theorem suffix_testbit_unsigned (w : int) (i : Z)
    (hi : zLe zZero i) :
    testbit w i = zTestbit (unsigned w) i := by
  cases i with
  | Zneg p =>
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hi
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      simp only [testbit, WordCore.testbit]
      change Nat.testBit w.val 0 = zTestbit (unsigned w) zZero
      rw [show unsigned w = zOfNat w.val by
        unfold unsigned WordCore.unsigned
        exact WordCore.intval_eq_zOfNat_val w]
      rw [Nat.testBit_zero]
      simp only [zTestbit, ZArith.BinInt.Z.testbit,
        ZArith.BinInt.Z.odd, ZArith.BinInt.Z.even,
        ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      have habs : (_root_.Int.ofNat w.val).natAbs = w.val := by
        apply _root_.Int.ofNat.inj
        exact _root_.Int.natAbs_of_nonneg (_root_.Int.natCast_nonneg _)
      rw [habs]
      rcases Nat.mod_two_eq_zero_or_one w.val with h | h <;> simp [h]
  | Zpos p =>
      simp only [testbit, WordCore.testbit,
        WordCore.positiveToNat_eq_posToNat]
      change Nat.testBit w.val (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) =
        zTestbit (unsigned w) (.Zpos p)
      rw [show unsigned w = zOfNat w.val by
        unfold unsigned WordCore.unsigned
        exact WordCore.intval_eq_zOfNat_val w]
      cases hw : w.val with
      | zero =>
          rw [show zOfNat 0 = (.Z0 : Z) by rfl]
          simp [zTestbit, ZArith.BinInt.Z.testbit]
      | succ n =>
          have hz : zOfNat (Nat.succ n) =
              .Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) := by
            rfl
          rw [hz]
          have hp :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) = n + 1 :=
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
              (Nat.succ_pos n)
          simp only [zTestbit, ZArith.BinInt.Z.testbit, hp]

theorem testbit_repr_proof : testbit_repr := by
  intro x i hi
  rw [suffix_testbit_unsigned (repr x) i hi.1]
  rw [unsigned_repr_eq_proof]
  have heq : CompCert4Lean.Lib.Zbits.eqmod
      (zTwoPowerNat wordsize) x (zMod x modulus) := by
    unfold CompCert4Lean.Lib.Zbits.eqmod
    refine ⟨ZArith.BinInt.Z.div x modulus, ?_⟩
    have hd := ZArith.Zdiv.Z_div_mod_eq_full x modulus
    apply intOfZ_injective
    have hd' := congrArg intOfZ hd
    simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
      intOfZ_zOfInt] at hd' ⊢
    change intOfZ x = intOfZ (ZArith.BinInt.Z.div x modulus) *
      intOfZ modulus + intOfZ (zMod x modulus)
    change intOfZ x = intOfZ modulus *
      intOfZ (ZArith.BinInt.Z.div x modulus) + intOfZ (zMod x modulus) at hd'
    rw [Int.mul_comm]
    exact hd'
  exact (CompCert4Lean.Lib.Zbits.same_bits_eqmod
    wordsize x (zMod x modulus) i heq hi).symm

theorem modulus_power_proof : modulus_power := by
  rfl

theorem add_unsigned_proof : add_unsigned := by
  intro x y
  rfl

theorem mul_commut_proof : mul_commut := by
  intro x y
  change WordCore.mul x y = WordCore.mul y x
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [suffix_wordcore_mul_val_int, suffix_wordcore_mul_val_int]
  rw [Int.mul_comm]

theorem sub_add_r_proof : sub_add_r := by
  intro x y z
  change WordCore.sub x (WordCore.add y z) =
    WordCore.add (WordCore.sub x z) (WordCore.neg y)
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int,
    WordCore.add_val_int, suffix_wordcore_neg_val_int,
    WordCore.sub_val_int]
  simp only [Int.emod_sub_emod, Int.sub_emod_emod,
    Int.emod_add_emod, Int.add_emod_emod]
  congr 1
  omega

theorem modulus_pos_proof : modulus_pos := by
  change (0 : Int) < intOfZ (zTwoPowerNat wordsize)
  exact CompCert4Lean.Lib.Coqlib.two_power_nat_pos wordsize

theorem signed_repr_proof : signed_repr := by
  intro z hz
  have hsr := signed_repr_eq_proof z
  rw [hsr]
  cases z with
  | Z0 =>
      rfl
  | Zpos p =>
      have hlt : zLt (.Zpos p) half_modulus := by
        have hmax := hz.2
        change Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) ≤
          intOfZ max_signed at hmax
        change Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) ≤
          (2 ^ (wordsize - 1) : Int) - 1 at hmax
        change Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) <
          intOfZ half_modulus
        have hh : intOfZ half_modulus = (2 ^ (wordsize - 1) : Int) := by
          unfold half_modulus
          rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
          rfl
        rw [hh]
        omega
      have hmod : zMod (.Zpos p) modulus = .Zpos p := by
        apply ZArith.BinInt.Z.mod_small
        constructor
        · change (0 : Int) ≤ Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
          exact Int.natCast_nonneg _
        · have hm := hlt
          change Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) <
            intOfZ half_modulus at hm
          change Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) <
            intOfZ modulus
          have hh : intOfZ half_modulus < intOfZ modulus := by
            have hhalf : intOfZ half_modulus = (2 ^ (wordsize - 1) : Int) := by
              unfold half_modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            have hmod : intOfZ modulus = (2 ^ wordsize : Int) := by
              unfold modulus
              rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
              rfl
            rw [hhalf, hmod]
            change (2 ^ 31 : Int) < 2 ^ 32
            decide
          exact Int.lt_trans hm hh
      rw [hmod]
      cases hs : CompCert4Lean.Lib.Coqlib.zlt (.Zpos p) half_modulus with
      | left hslt =>
          change sumboolSelect
            (CompCert4Lean.Lib.Coqlib.zlt (.Zpos p) half_modulus)
            (.Zpos p) (zSub (.Zpos p) modulus) = .Zpos p
          rw [hs]
          rfl
      | right hsge =>
          exfalso
          exact (Int.not_lt_of_ge hsge) hlt
  | Zneg p =>
      let pn : Nat :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p
      have hp : 0 < pn := by
        dsimp [pn]
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat pn := Int.natCast_pos.mpr hp
      have hbound : Int.ofNat pn ≤ (2 ^ (wordsize - 1) : Int) := by
        have hmin := hz.1
        change (- (2 ^ (wordsize - 1) : Int)) ≤ -Int.ofNat pn at hmin
        omega
      have hpnlt : Int.ofNat pn < (2 ^ wordsize : Int) := by
        have hhalf : (2 ^ (wordsize - 1) : Int) < (2 ^ wordsize : Int) := by
          change (2 ^ 31 : Int) < 2 ^ 32
          decide
        exact Int.lt_of_le_of_lt hbound hhalf
      have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
        unfold modulus
        rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
        rfl
      have hmod : zMod (.Zneg p) modulus = zSub modulus (.Zpos p) := by
        apply intOfZ_injective
        have hleft := suffix_modulo_int (.Zneg p)
        have hright : intOfZ (zSub modulus (.Zpos p)) =
            (2 ^ wordsize : Int) - Int.ofNat pn := by
          simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
          rw [hm]
          rfl
        rw [hleft, hright]
        change (-Int.ofNat pn) % (2 ^ wordsize : Int) =
          (2 ^ wordsize : Int) - Int.ofNat pn
        rw [Int.neg_emod_eq_sub_emod]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      have hge : zLe half_modulus (zSub modulus (.Zpos p)) := by
        change intOfZ half_modulus ≤ intOfZ (zSub modulus (.Zpos p))
        simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change (2 ^ 31 : Int) ≤ 2 ^ 32 - Int.ofNat pn
        have hb := hbound
        change Int.ofNat pn ≤ (2 ^ 31 : Int) at hb
        have hpow : (2 ^ 32 : Int) = 2 ^ 31 + 2 ^ 31 := by decide
        rw [hpow]
        omega
      rw [hmod]
      cases hs : CompCert4Lean.Lib.Coqlib.zlt
          (zSub modulus (.Zpos p)) half_modulus with
      | left hslt =>
          exfalso
          exact (Int.not_lt_of_ge hge) hslt
      | right hsge =>
          have hsel :
              zltSelect (zSub modulus (.Zpos p)) half_modulus
                (zSub modulus (.Zpos p))
                (zSub (zSub modulus (.Zpos p)) modulus) =
                zSub (zSub modulus (.Zpos p)) modulus := by
            unfold zltSelect
            rw [hs]
            rfl
          rw [hsel]
          apply intOfZ_injective
          simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
          rw [hm]
          change (2 ^ 32 - Int.ofNat pn) - 2 ^ 32 = -Int.ofNat pn
          omega

private theorem suffix_wordcore_mul_val_nat (x y : int) :
    (WordCore.mul x y).val =
      (x.val * y.val) % (2 ^ wordsize) := by
  apply Int.ofNat.inj
  rw [suffix_wordcore_mul_val_int]
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_emod]

theorem shl_mul_proof : shl_mul := by
  intro x y
  apply WordCore.ext_of_val_eq
  change (WordCore.shl x y).val = (WordCore.mul x (WordCore.shl one y)).val
  rw [suffix_shl_val, suffix_wordcore_mul_val_nat, suffix_shl_val]
  have hone : (WordCore.one wordsize).val = 1 := by
    unfold WordCore.one
    rw [WordCore.val_repr_residue]
    rfl
  have hone' : one.val = 1 := by
    unfold one
    exact hone
  rw [hone']
  rw [Nat.mul_mod]
  simp only [Nat.one_mul]
  symm
  rw [Nat.mul_mod]
  simp only [Nat.mod_mod]

private theorem suffix_bits_shl_nat (x y : int) (n : Nat)
    (hn : n < wordsize) :
    testbit (shl x y) (zOfNat n) =
      zltSelect (zOfNat n) (unsigned y) false
        (testbit x (zSub (zOfNat n) (unsigned y))) := by
  have hy : unsigned y = zOfNat y.val :=
    WordCore.intval_eq_zOfNat_val y
  rw [suffix_testbit_nat]
  change ((WordCore.shl x y).val).testBit n = _
  rw [suffix_shl_val]
  rw [Nat.testBit_mod_two_pow]
  simp only [hn, decide_true]
  rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt (zOfNat n) (unsigned y) with
  | left hlt' =>
      have hltNat : n < y.val := by
        rw [hy] at hlt'
        change intOfZ (zOfNat n) < intOfZ (zOfNat y.val) at hlt'
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt'
        exact Int.ofNat_lt.mp hlt'
      have hnle : ¬ y.val ≤ n := Nat.not_le.mpr hltNat
      simp [zltSelect, sumboolSelect, hlt, hnle]
  | right hge =>
      have hgeNat : y.val ≤ n := by
        rw [hy] at hge
        change intOfZ (zOfNat y.val) ≤ intOfZ (zOfNat n) at hge
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hge
        exact Int.ofNat_le.mp hge
      have hsub : zSub (zOfNat n) (unsigned y) = zOfNat (n - y.val) := by
        rw [hy]
        apply intOfZ_injective
        simp only [zSub, zOfNat, ZArith.BinInt.Z.sub,
          ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        exact (Int.ofNat_sub hgeNat).symm
      rw [hsub]
      simp [hgeNat]
      have hsel :
          zltSelect (zOfNat n) (unsigned y) false
            (testbit x (zOfNat (n - y.val))) =
            testbit x (zOfNat (n - y.val)) := by
        unfold zltSelect
        rw [hlt]
        rfl
      rw [hsel, suffix_testbit_nat]

theorem bits_shl_proof : bits_shl := by
  intro x y i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_shl_nat x y 0 (by decide)
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      have hn : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize := by
        have h := hi.2
        change intOfZ (zOfNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) <
          intOfZ zwordsize at h
        simp only [zOfNat, zwordsize, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt] at h
        exact Int.ofNat_lt.mp h
      exact suffix_bits_shl_nat x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) hn

private theorem suffix_bits_size_2_unsigned_eq (x : int) :
    unsigned x = zOfNat x.val := by
  unfold unsigned WordCore.unsigned
  exact WordCore.intval_eq_zOfNat_val x

theorem bits_size_2_proof : bits_size_2 := by
  intro x i hi
  have hi0 : zLe zZero i := by
    have hx0 : zLe zZero (size x) := by
      change ZArith.BinInt.Z.le Z0
        (CompCert4Lean.Lib.Zbits.Zsize (unsigned x))
      cases hu : unsigned x with
      | Z0 =>
          simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
          change (0 : Int) ≤ 0
          omega
      | Zpos p =>
          simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
          change (0 : Int) ≤ intOfZ (Zpos (PArith.BinPos.Pos.size p))
          simp only [intOfZ]
          exact Int.natCast_nonneg _
      | Zneg p =>
          simp only [CompCert4Lean.Lib.Zbits.Zsize, hu]
          change (0 : Int) ≤ 0
          omega
    change intOfZ (size x) ≤ intOfZ i at hi
    change (0 : Int) ≤ intOfZ i
    have hx0' := hx0
    change (0 : Int) ≤ intOfZ (size x) at hx0'
    omega
  cases i with
  | Zneg p =>
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hi0
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      change testbit x (zOfNat 0) = false
      rw [suffix_testbit_nat x 0]
      cases hval : x.val with
      | zero => rfl
      | succ n =>
          have hsizepos : zLt zZero (size x) := by
            change (0 : Int) < intOfZ (CompCert4Lean.Lib.Zbits.Zsize (unsigned x))
            rw [suffix_bits_size_2_unsigned_eq x, hval]
            rw [show zOfNat (n + 1) = Zpos (posOfNat (n + 1)) by rfl]
            simp only [CompCert4Lean.Lib.Zbits.Zsize]
            change (0 : Int) < Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                (PArith.BinPos.Pos.size (posOfNat (n + 1))))
            exact Int.natCast_pos.mpr
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive _)
          change intOfZ (size x) ≤ 0 at hi
          change (0 : Int) < intOfZ (size x) at hsizepos
          omega
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p :=
        ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      let k := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p
      rw [suffix_testbit_nat x k]
      cases hval : x.val with
      | zero => simp
      | succ n =>
          have hsize : Nat.log2 (n + 1) + 1 ≤ k := by
            change intOfZ (CompCert4Lean.Lib.Zbits.Zsize (unsigned x)) ≤
              intOfZ (zOfNat k) at hi
            rw [suffix_bits_size_2_unsigned_eq x, hval] at hi
            simp only [CompCert4Lean.Lib.Zbits.Zsize, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt] at hi
            change Int.ofNat
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                  (PArith.BinPos.Pos.size (posOfNat (n + 1)))) ≤
              Int.ofNat k at hi
            have hsz :
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                    (PArith.BinPos.Pos.size (posOfNat (n + 1))) =
                  Nat.log2 (n + 1) + 1 := by
              unfold PArith.BinPos.Pos.size
              rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
                (by omega : 0 < n + 1)]
              exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
                (by omega)
            rw [hsz] at hi
            exact Int.ofNat_le.mp hi
          change Nat.testBit (n + 1) k = false
          apply Nat.testBit_lt_two_pow
          apply (Nat.log2_lt (Nat.ne_of_gt (by omega : 0 < n + 1))).mp
          omega

theorem neg_involutive_proof : neg_involutive := by
  intro x
  change WordCore.neg (WordCore.neg x) = x
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [suffix_wordcore_neg_val_int, suffix_wordcore_neg_val_int]
  have hx0 : (0 : Int) ≤ Int.ofNat x.val := Int.natCast_nonneg _
  have hxm : Int.ofNat x.val < Int.ofNat (2 ^ wordsize) := by
    exact Int.ofNat_lt.mpr (WordCore.val_lt x)
  by_cases hxzero : Int.ofNat x.val = 0
  · rw [hxzero]
    simp
  · have hxpos : (0 : Int) < Int.ofNat x.val := by omega
    have hma0 : (0 : Int) ≤ Int.ofNat (2 ^ wordsize) - Int.ofNat x.val := by
      omega
    have hma_lt : Int.ofNat (2 ^ wordsize) - Int.ofNat x.val <
        Int.ofNat (2 ^ wordsize) := by
      omega
    rw [Int.neg_emod_eq_sub_emod, Int.neg_emod_eq_sub_emod]
    rw [Int.emod_eq_of_lt hma0 hma_lt]
    have hsub : Int.ofNat (2 ^ wordsize) -
        (Int.ofNat (2 ^ wordsize) - Int.ofNat x.val) = Int.ofNat x.val := by
      omega
    rw [hsub]
    exact Int.emod_eq_of_lt hx0 hxm

theorem eq_spec_proof : eq_spec := by
  intro x y
  by_cases h : x.intval = y.intval
  · have hxy : x = y := WordCore.ext h
    simp [eq, WordCore.eq, h, hxy]
  · have hxy : x ≠ y := by
      intro hxy
      apply h
      exact congrArg (fun q => q.intval) hxy
    simp [eq, WordCore.eq, h, hxy]

theorem min_signed_neg_proof : min_signed_neg := by
  change (-((2 : Int) ^ 31)) < 0
  decide

theorem repr_signed_proof : repr_signed := by
  intro i
  exact (eqm_samerepr_proof (signed i) (unsigned i)
    (eqm_signed_unsigned_proof i)).trans (repr_unsigned_proof i)

theorem or_mone_proof : or_mone := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.or x (WordCore.mone wordsize)).val =
    (WordCore.mone wordsize).val
  rw [suffix_or_val, suffix_mone_val]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.lor_eq, Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < wordsize
  · simp [hi]
  · have hpow : 2 ^ wordsize ≤ 2 ^ i :=
      Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow)]
    simp [hi]

theorem or_ror_proof : or_ror := by
  intro x y z hy hz hsum
  have hyv : y.val < wordsize := suffix_ltu_iwordsize_val y hy
  have hzv : z.val < wordsize := suffix_ltu_iwordsize_val z hz
  have hsum_nat : y.val + z.val = wordsize := by
    change y.val < 32 at hyv
    change z.val < 32 at hzv
    have hval := congrArg (fun q : int => q.val) hsum
    change (WordCore.add y z).val = iwordsize.val at hval
    rw [WordCore.add_val] at hval
    change (y.val + z.val) % (2 ^ wordsize) = iwordsize.val at hval
    have hiword : iwordsize.val = wordsize := rfl
    rw [hiword] at hval
    have hlt : y.val + z.val < 2 ^ wordsize := by
      change y.val + z.val < 2 ^ 32
      omega
    rw [Nat.mod_eq_of_lt hlt] at hval
    exact hval
  have hyu : unsigned y = zOfNat y.val := by
    change y.intval = zOfNat y.val
    exact WordCore.intval_eq_zOfNat_val y
  have hzu : unsigned z = zOfNat z.val := by
    change z.intval = zOfNat z.val
    exact WordCore.intval_eq_zOfNat_val z
  have hbits : ∀ n : Nat, n < wordsize →
      testbit (ror x z) (zOfNat n) =
        testbit (or (shl x y) (shru x z)) (zOfNat n) := by
    intro n hn
    calc
      testbit (ror x z) (zOfNat n) =
          (WordCore.ror x z).val.testBit n := suffix_testbit_nat _ _
      _ = x.val.testBit ((n + z.val) % wordsize) := suffix_ror_bit x z n hn
      _ = (testbit (shl x y) (zOfNat n) ||
        testbit (shru x z) (zOfNat n)) := by
        rw [suffix_bits_shl_nat x y n hn, suffix_bits_shru_nat x z n]
        by_cases hny : n < y.val
        · have hnz : n + z.val < wordsize := by omega
          have hYlt : zLt (zOfNat n) (unsigned y) := by
            rw [hyu]
            change intOfZ (zOfNat n) < intOfZ (zOfNat y.val)
            simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact Int.ofNat_lt.mpr hny
          have hWlt : zLt (zAdd (zOfNat n) (unsigned z)) zwordsize := by
            rw [hzu]
            change intOfZ (zAdd (zOfNat n) (zOfNat z.val)) < intOfZ zwordsize
            simp only [zAdd, zwordsize, ZArith.BinInt.Z.add,
              ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact Int.ofNat_lt.mpr hnz
          have haddz : zAdd (zOfNat n) (unsigned z) =
              zOfNat (n + z.val) := by
            rw [hzu]
            apply intOfZ_injective
            simp only [zAdd, ZArith.BinInt.Z.add, zOfNat,
              ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.natCast_add]
            exact (Int.ofNat_add_ofNat n z.val).symm
          have hidx : testbit x (zAdd (zOfNat n) (unsigned z)) =
              x.val.testBit ((n + z.val) % wordsize) := by
            rw [haddz, suffix_testbit_nat]
            rw [Nat.mod_eq_of_lt hnz]
          cases hYc : CompCert4Lean.Lib.Coqlib.zlt
              (zOfNat n) (unsigned y) with
          | left hYp =>
              cases hWc : CompCert4Lean.Lib.Coqlib.zlt
                  (zAdd (zOfNat n) (unsigned z)) zwordsize with
              | left hWp =>
                  simp [zltSelect, sumboolSelect, hYc, hWc, hidx,
                    Nat.mod_eq_of_lt hnz]
              | right hWp => exfalso; exact (Int.not_lt_of_ge hWp) hWlt
          | right hYp => exfalso; exact (Int.not_lt_of_ge hYp) hYlt
        · have hyn : y.val ≤ n := Nat.le_of_not_gt hny
          have hnz : wordsize ≤ n + z.val := by omega
          have hYge : zLe (unsigned y) (zOfNat n) := by
            rw [hyu]
            change intOfZ (zOfNat y.val) ≤ intOfZ (zOfNat n)
            simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact Int.ofNat_le.mpr hyn
          have hWge : zLe zwordsize (zAdd (zOfNat n) (unsigned z)) := by
            rw [hzu]
            change intOfZ zwordsize ≤ intOfZ (zAdd (zOfNat n) (zOfNat z.val))
            simp only [zAdd, zwordsize, ZArith.BinInt.Z.add,
              ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact Int.ofNat_le.mpr hnz
          have hsuby : zSub (zOfNat n) (unsigned y) =
              zOfNat (n - y.val) := by
            rw [hyu]
            apply intOfZ_injective
            simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
              ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact (Int.ofNat_sub hyn).symm
          have hidxNat : n - y.val = (n + z.val) % wordsize := by
            rw [Nat.mod_eq_sub_mod hnz, Nat.mod_eq_of_lt (by omega)]
            omega
          have hidx : testbit x (zSub (zOfNat n) (unsigned y)) =
              x.val.testBit ((n + z.val) % wordsize) := by
            rw [hsuby, suffix_testbit_nat, hidxNat]
          cases hYc : CompCert4Lean.Lib.Coqlib.zlt
              (zOfNat n) (unsigned y) with
          | left hYp => exfalso; exact (Int.not_lt_of_ge hYge) hYp
          | right hYp =>
              cases hWc : CompCert4Lean.Lib.Coqlib.zlt
                  (zAdd (zOfNat n) (unsigned z)) zwordsize with
              | left hWp => exfalso; exact (Int.not_lt_of_ge hWge) hWp
              | right hWp =>
                  simp [zltSelect, sumboolSelect, hYc, hWc, hidx,
                    Nat.mod_eq_sub_mod hnz]
      _ = testbit (or (shl x y) (shru x z)) (zOfNat n) :=
        (suffix_bits_or_nat (shl x y) (shru x z) n).symm
  apply same_bits_eq_proof
  intro i hi
  cases i with
  | Zneg p =>
      have hi0 := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hi0
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 => exact hbits 0 (by decide)
  | Zpos p =>
      have hnZ := hi.2
      change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
        Int.ofNat wordsize at hnZ
      have hn : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize :=
        Int.ofNat_lt.mp hnZ
      have hzpos : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hzpos] at hi ⊢
      exact hbits _ hn

theorem unsigned_range_proof : unsigned_range := by
  intro i
  constructor
  · have h := i.intrange.1
    change (-1 : Int) < intOfZ (unsigned i) at h
    change 0 ≤ intOfZ (unsigned i)
    omega
  · exact i.intrange.2

theorem eqm_unsigned_repr_r_proof : eqm_unsigned_repr_r := by
  intro a b hab
  exact eqm_trans_proof a b (unsigned (repr b)) hab
    (suffix_eqm_unsigned_repr b)

private theorem suffix_ltu_repr_of_lt_wordsize (j : Z)
    (hj : zLe zZero j ∧ zLt j (zOfNat wordsize)) :
    ltu (repr j) iwordsize = true := by
  unfold ltu WordCore.ltu
  have hjmod : zMod j modulus = j := by
    apply ZArith.BinInt.Z.mod_small
    constructor
    · exact hj.1
    · change intOfZ j < intOfZ modulus
      change intOfZ j < (2 ^ wordsize : Int)
      have hjs : intOfZ j < Int.ofNat wordsize := by
        exact hj.2
      change intOfZ j < Int.ofNat wordsize at hjs
      have hpow : (Int.ofNat wordsize : Int) < (2 ^ wordsize : Int) := by
        decide
      change intOfZ j < (2 ^ wordsize : Int)
      omega
  have hu : unsigned (repr j) = j := by
    rw [suffix_unsigned_repr_eq_exact, hjmod]
  have hi : unsigned iwordsize = zOfNat wordsize := by
    change unsigned (repr (zOfNat wordsize)) = zOfNat wordsize
    rw [suffix_unsigned_repr_eq_exact]
    apply ZArith.BinInt.Z.mod_small
    constructor
    · change 0 ≤ Int.ofNat wordsize
      exact Int.natCast_nonneg _
    · change (Int.ofNat wordsize : Int) < Int.ofNat (2 ^ wordsize)
      exact Int.ofNat_lt.mpr (by decide)
  change zltSelect (unsigned (repr j)) (unsigned iwordsize) true false = true
  rw [hu, hi]
  cases h : CompCert4Lean.Lib.Coqlib.zlt j (zOfNat wordsize) with
  | left hlt => simp [zltSelect, sumboolSelect, h]
  | right hge => exfalso; exact (Int.not_lt_of_ge hge) hj.2

theorem one_bits_range_proof : one_bits_range := by
  intro x i hi
  unfold one_bits at hi
  rcases List.mem_map.1 hi with ⟨j, hj, rfl⟩
  exact suffix_ltu_repr_of_lt_wordsize j
    (CompCert4Lean.Lib.Zbits.Z_one_bits_range wordsize (unsigned x) j hj)

theorem divs_one_proof : divs_one := by
  intro x _
  change WordCore.repr wordsize
      (zQuot (signed x) (signed one)) = x
  have hone : signed one = zOne := by
    rfl
  rw [hone]
  have hdiv : zQuot (signed x) zOne = signed x := by
    apply intOfZ_injective
    simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
    change (intOfZ (signed x)).tdiv 1 = intOfZ (signed x)
    exact Int.tdiv_one _
  rw [hdiv]
  exact repr_signed_proof x

private theorem suffix_bits_and_nat (x y : int) (n : Nat) :
    testbit (and x y) (zOfNat n) =
      (testbit x (zOfNat n) && testbit y (zOfNat n)) := by
  rw [suffix_testbit_nat, suffix_testbit_nat, suffix_testbit_nat]
  change (WordCore.and x y).val.testBit n =
    (x.val.testBit n && y.val.testBit n)
  rw [suffix_and_val, Nat.land_eq, Nat.testBit_and]

theorem bits_and_proof : bits_and := by
  intro x y i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_and_nat x y 0
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      exact suffix_bits_and_nat x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

theorem size_range_proof : size_range := by
  intro x
  change zLe zZero (CompCert4Lean.Lib.Zbits.Zsize (unsigned x)) ∧
    zLe (CompCert4Lean.Lib.Zbits.Zsize (unsigned x)) zwordsize
  rw [suffix_bits_size_2_unsigned_eq x]
  cases hval : x.val with
  | zero =>
      change (0 : Int) ≤ 0 ∧ (0 : Int) ≤ Int.ofNat wordsize
      constructor
      · omega
      · exact Int.natCast_nonneg _
  | succ n =>
      have hsz :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
              (PArith.BinPos.Pos.size (posOfNat (n + 1))) =
            Nat.log2 (n + 1) + 1 := by
        unfold PArith.BinPos.Pos.size
        rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
          (by omega : 0 < n + 1)]
        exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
          (by omega)
      have hxlt : n + 1 < 2 ^ wordsize := by
        have h := WordCore.val_lt x
        omega
      have hloglt : Nat.log2 (n + 1) < wordsize :=
        (Nat.log2_lt (Nat.ne_of_gt (by omega : 0 < n + 1))).mpr hxlt
      constructor
      · change (0 : Int) ≤ Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
            (PArith.BinPos.Pos.size (posOfNat (n + 1))))
        exact Int.natCast_nonneg _
      · change Int.ofNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
              (PArith.BinPos.Pos.size (posOfNat (n + 1)))) ≤
          Int.ofNat wordsize
        rw [hsz]
        exact Int.ofNat_le.mpr (by omega)

private theorem suffix_rol_val (x y : int) :
    (WordCore.rol x y).val =
      Nat.lor (x.val <<< (y.val % wordsize))
        (x.val >>> (wordsize - (y.val % wordsize))) % (2 ^ wordsize) := by
  unfold WordCore.rol
  dsimp
  rw [WordCore.val_repr_residue]
  exact WordCore.residue_zOfNat _ _

private theorem suffix_rol_bit (x y : int) (i : Nat)
    (hi : i < wordsize) :
    ((WordCore.rol x y).val).testBit i =
      x.val.testBit ((i + wordsize - (y.val % wordsize)) % wordsize) := by
  rw [suffix_rol_val]
  rw [Nat.lor_eq]
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, Bool.true_and]
  let a := y.val % wordsize
  have ha : a < wordsize := Nat.mod_lt _ (by omega)
  by_cases hia : a ≤ i
  · have hleft : (x.val <<< a).testBit i = x.val.testBit (i - a) := by
      rw [Nat.testBit_shiftLeft]
      simp [hia]
    have hright : (x.val >>> (wordsize - a)).testBit i = false := by
      rw [Nat.testBit_shiftRight]
      apply Nat.testBit_lt_two_pow
      have hpow : 2 ^ wordsize ≤ 2 ^ (wordsize - a + i) :=
        Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      exact Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
    dsimp [a] at hleft hright
    simp only [Nat.testBit_or, hleft, hright, Bool.false_or, decide_true,
      Bool.true_and]
    rw [Bool.or_false]
    change x.val.testBit (i - a) =
      x.val.testBit ((i + wordsize - a) % wordsize)
    rw [Nat.mod_eq_sub_mod (by omega : wordsize ≤ i + wordsize - a)]
    have hidx : i + wordsize - a - wordsize = i - a := by omega
    rw [hidx, Nat.mod_eq_of_lt (by omega : i - a < wordsize)]
  · have hia' : i < a := Nat.lt_of_not_ge hia
    have hleft : (x.val <<< a).testBit i = false := by
      rw [Nat.testBit_shiftLeft]
      simp [show ¬ a ≤ i by omega]
    have hright : (x.val >>> (wordsize - a)).testBit i =
        x.val.testBit (i + (wordsize - a)) := by
      rw [Nat.testBit_shiftRight]
      congr 1 <;> omega
    dsimp [a] at hleft hright
    simp only [Nat.testBit_or, hleft, Bool.false_or, hright, decide_true,
      Bool.true_and]
    change x.val.testBit (i + (wordsize - a)) =
      x.val.testBit ((i + wordsize - a) % wordsize)
    rw [Nat.mod_eq_of_lt (by omega : i + wordsize - a < wordsize)]
    congr 1 <;> omega

private theorem suffix_neg_mod_wordsize (y : int) :
    (WordCore.neg y).val % wordsize =
      (wordsize - (y.val % wordsize)) % wordsize := by
  have hdvd : (Int.ofNat wordsize : Int) ∣ Int.ofNat (2 ^ wordsize) := by
    decide
  have hrem : y.val % wordsize ≤ wordsize := by
    exact Nat.le_of_lt (Nat.mod_lt _ (by decide))
  have hInt :
      (Int.ofNat ((WordCore.neg y).val % wordsize) : Int) =
        Int.ofNat ((wordsize - (y.val % wordsize)) % wordsize) := by
    calc
      (Int.ofNat ((WordCore.neg y).val % wordsize) : Int) =
          (Int.ofNat (WordCore.neg y).val : Int) % Int.ofNat wordsize := by
        exact (Int.natCast_emod _ _).symm
      _ = ((-Int.ofNat y.val) % Int.ofNat (2 ^ wordsize)) %
          Int.ofNat wordsize := by
        rw [suffix_wordcore_neg_val_int]
      _ = (-Int.ofNat y.val) % Int.ofNat wordsize := by
        rw [Int.emod_emod_of_dvd _ hdvd]
      _ = (Int.ofNat wordsize -
          (Int.ofNat y.val % Int.ofNat wordsize)) % Int.ofNat wordsize := by
        rw [Int.neg_emod_eq_sub_emod]
        rw [Int.sub_emod, Int.emod_self, Int.zero_sub,
          Int.neg_emod_eq_sub_emod]
      _ = Int.ofNat ((wordsize - (y.val % wordsize)) % wordsize) := by
        simp only [Int.ofNat_eq_natCast, Int.natCast_emod]
        rw [← Int.natCast_emod y.val wordsize, ← Int.ofNat_sub hrem]
  exact Int.ofNat.inj hInt

private theorem suffix_rol_testbit_nat (x y : int) (n : Nat)
    (hn : n < wordsize) :
    testbit (rol x y) (zOfNat n) =
      testbit x (zOfNat ((n + wordsize - (y.val % wordsize)) % wordsize)) := by
  change testbit (WordCore.rol x y) (zOfNat n) =
    testbit x (zOfNat ((n + wordsize - (y.val % wordsize)) % wordsize))
  rw [suffix_testbit_nat (WordCore.rol x y) n]
  change (WordCore.rol x y).val.testBit n =
    testbit x (zOfNat ((n + wordsize - (y.val % wordsize)) % wordsize))
  rw [suffix_rol_bit x y n hn, suffix_testbit_nat]

private theorem suffix_rol_neg_index (y : int) (n : Nat) :
    (n + wordsize - ((WordCore.neg y).val % wordsize)) % wordsize =
      (n + y.val) % wordsize := by
  rw [suffix_neg_mod_wordsize]
  let r := y.val % wordsize
  have hr : r < wordsize := Nat.mod_lt _ (by decide)
  have hright : (n + wordsize - ((wordsize - r) % wordsize)) % wordsize =
      (n + r) % wordsize := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · have hsublt : wordsize - r < wordsize := by omega
      rw [Nat.mod_eq_of_lt hsublt]
      congr 1 <;> omega
  calc
    (n + wordsize - ((wordsize - (y.val % wordsize)) % wordsize)) % wordsize =
        (n + r) % wordsize := by simpa [r] using hright
    _ = (n + y.val) % wordsize := by
      simpa [r] using (Nat.add_mod_mod n y.val wordsize).symm

theorem ror_rol_neg_proof : ror_rol_neg := by
  intro x y _
  apply same_bits_eq_proof
  intro i hi
  cases i with
  | Zneg p =>
      have hi0 := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hi0
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      have hmod := suffix_zmod_add_nat 0 y
      have hmod' := hmod
      change zMod (zAdd (.Z0 : Z) (unsigned y)) zwordsize =
        zOfNat ((0 + y.val) % wordsize) at hmod'
      have hidx := suffix_rol_neg_index y 0
      calc
        testbit (ror x y) (.Z0 : Z) =
            testbit x (zMod (zAdd (.Z0 : Z) (unsigned y)) zwordsize) :=
          bits_ror_proof x y (.Z0 : Z) hi
        _ = testbit x (zOfNat ((0 + y.val) % wordsize)) := by
          rw [hmod']
        _ = testbit x
            (zOfNat ((0 + wordsize - ((WordCore.neg y).val % wordsize)) %
              wordsize)) := by
          rw [hidx]
        _ = testbit (rol x (neg y)) (.Z0 : Z) := by
          exact (suffix_rol_testbit_nat x (WordCore.neg y) 0 (by decide)).symm
  | Zpos p =>
      have hkZ := hi.2
      change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
        Int.ofNat wordsize at hkZ
      have hk :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize :=
        Int.ofNat_lt.mp hkZ
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      let n := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p
      have hmod := suffix_zmod_add_nat n y
      have hidx := suffix_rol_neg_index y n
      calc
        testbit (ror x y) (zOfNat n) =
            testbit x (zMod (zAdd (zOfNat n) (unsigned y)) zwordsize) :=
          bits_ror_proof x y (zOfNat n) hi
        _ = testbit x (zOfNat ((n + y.val) % wordsize)) := by
          rw [hmod]
        _ = testbit x
            (zOfNat ((n + wordsize - ((WordCore.neg y).val % wordsize)) %
              wordsize)) := by
          rw [hidx]
        _ = testbit (rol x (neg y)) (zOfNat n) := by
          exact (suffix_rol_testbit_nat x (WordCore.neg y) n hk).symm

theorem and_zero_proof : and_zero := by
  intro x
  apply same_bits_eq_proof
  intro i hi
  rw [bits_and_proof x zero i hi, bits_zero_proof]
  simp

theorem negate_cmpu_proof : negate_cmpu := by
  intro c x y
  cases c <;> simp [cmpu, WordCore.cmpu, negate_comparison]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers

theorem int_wordsize_divides_modulus_proof : int_wordsize_divides_modulusStatement := by
  unfold int_wordsize_divides_modulusStatement
  change ∃ k, Int.modulus =
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul
      (zOfNat Int.wordsize) k
  refine ⟨zOfNat (2 ^ (32 - 5)), ?_⟩
  rw [Int.modulus, WordCore.twoPowerNat_eq_zOfNat_twoPow]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change Int.ofNat (2 ^ 32) = Int.ofNat 32 * Int.ofNat (2 ^ (32 - 5))
  rfl

namespace Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_size_4_proof : bits_size_4 := by
  intro x n hn hbit hhigh
  cases n with
  | Zneg p =>
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hn
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      have hidx : intOfZ (zSub zZero zOne) < 0 := by
        change (0 : Int) - 1 < 0
        omega
      have hf := suffix_testbit_negative_index x (zSub zZero zOne) hidx
      rw [hf] at hbit
      cases hbit
  | Zpos p =>
      let k := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p
      have hkpos : 0 < k :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hz : zOfNat k = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      have hsub : zSub (.Zpos p) zOne = zOfNat (k - 1) := by
        rw [← hz]
        exact suffix_zsub_nat k 1 (by omega)
      rw [hsub] at hbit
      have hbitnat : x.val.testBit (k - 1) = true := by
        rw [suffix_testbit_nat] at hbit
        exact hbit
      have hhighNat : ∀ i : Nat, k ≤ i → x.val.testBit i = false := by
        intro i hik
        by_cases hi32 : i < wordsize
        · have hki : zLe (.Zpos p) (zOfNat i) := by
            change intOfZ (.Zpos p) ≤ intOfZ (zOfNat i)
            rw [← hz]
            simp only [zOfNat, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt]
            exact Int.ofNat_le.mpr hik
          have hil : zLt (zOfNat i) zwordsize := by
            change intOfZ (zOfNat i) < intOfZ zwordsize
            simp only [zOfNat, zwordsize, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt]
            exact Int.ofNat_lt.mpr hi32
          have hh := hhigh (zOfNat i) ⟨hki, hil⟩
          rw [suffix_testbit_nat] at hh
          exact hh
        · have hxlt : x.val < 2 ^ wordsize := WordCore.val_lt x
          have hpow : 2 ^ wordsize ≤ 2 ^ i :=
            Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi32)
          exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hxlt hpow)
      have hxne : x.val ≠ 0 := by
        intro hx
        rw [hx] at hbitnat
        simp at hbitnat
      have hlo : 2 ^ (k - 1) ≤ x.val :=
        Nat.ge_two_pow_of_testBit hbitnat
      have hkstep : k - 1 + 1 = k := by omega
      have hupp : x.val < 2 ^ ((k - 1) + 1) := by
        rw [hkstep]
        exact Nat.lt_pow_two_of_testBit x.val (by
          intro i hik
          exact hhighNat i hik)
      have hlog : Nat.log2 x.val = k - 1 :=
        (Nat.log2_eq_iff hxne).2 ⟨hlo, hupp⟩
      cases hval : x.val with
      | zero => exact (hxne hval).elim
      | succ m =>
          have hsz0 :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                  (PArith.BinPos.Pos.size (posOfNat (m + 1))) = k := by
            unfold PArith.BinPos.Pos.size
            rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
              (by omega : 0 < m + 1)]
            have hlog' : Nat.log2 (m + 1) = k - 1 := by
              simpa [hval] using hlog
            rw [hlog']
            rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
              (by omega : 0 < k - 1 + 1)]
            omega
          change CompCert4Lean.Lib.Zbits.Zsize (unsigned x) = .Zpos p
          rw [← hz]
          rw [suffix_bits_size_2_unsigned_eq x, hval]
          simp only [CompCert4Lean.Lib.Zbits.Zsize]
          change .Zpos (PArith.BinPos.Pos.size (posOfNat (m + 1))) = zOfNat k
          have hzk : zOfNat k = .Zpos (posOfNat k) := by
            cases hk : k with
            | zero => omega
            | succ q => rfl
          rw [hzk]
          have hpos : PArith.BinPos.Pos.size (posOfNat (m + 1)) =
              posOfNat k :=
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_injective
              (by
                rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hkpos]
                exact hsz0)
          exact congrArg
            (fun q => CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos q) hpos

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Byte

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_samerepr_proof : eqm_samerepr := by
  intro x y h
  apply WordCore.ext_of_val_eq
  rw [show x = zOfInt (intOfZ x) by exact (zOfInt_intOfZ x).symm,
    show y = zOfInt (intOfZ y) by exact (zOfInt_intOfZ y).symm]
  change (WordCore.repr wordsize (zOfInt (intOfZ x))).val =
    (WordCore.repr wordsize (zOfInt (intOfZ y))).val
  rw [WordCore.val_repr, WordCore.val_repr]
  have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
    unfold modulus
    rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
    rfl
  unfold WordCore.eqm CompCert4Lean.Lib.Zbits.eqmod at h
  rcases h with ⟨k, hk⟩
  have hk' := congrArg intOfZ hk
  simp only [zAdd, zMul, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt] at hk'
  change intOfZ x = intOfZ k * intOfZ modulus + intOfZ y at hk'
  have hrem : intOfZ x % intOfZ modulus = intOfZ y % intOfZ modulus := by
    rw [hk', Int.add_emod, Int.mul_emod]
    simp
  rw [hm] at hrem
  exact congrArg Int.toNat hrem

end CompCert4Lean.Lib.Integers.Byte

namespace CompCert4Lean.Lib.Integers.Int64

theorem signed_mone_proof : signed_mone := by
  rfl

theorem eqm_refl_proof : eqm_refl := by
  intro x
  exact CompCert4Lean.Lib.Zbits.eqmod_refl modulus x

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_int64_unsigned_repr_eq_exact (x : Z) :
    unsigned (repr x) = zMod x modulus := by
  change (WordCore.repr wordsize x).intval = zMod x modulus
  rw [WordCore.intval_eq_zOfNat_val]
  have hval : (WordCore.repr wordsize x).val =
      _root_.Int.toNat
        (intOfZ x % _root_.Int.ofNat (2 ^ wordsize)) := by
    have h := WordCore.val_repr wordsize (intOfZ x)
    rw [zOfInt_intOfZ x] at h
    simpa only [_root_.Int.ofNat_eq_natCast] using h
  rw [hval]
  apply intOfZ_injective
  have hmpos : (0 : _root_.Int) < intOfZ modulus := by
    change (0 : _root_.Int) < _root_.Int.ofNat (2 ^ wordsize)
    exact _root_.Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hm : intOfZ modulus = _root_.Int.ofNat (2 ^ wordsize) := by
    rfl
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  have hmod : intOfZ (zMod x modulus) =
      intOfZ x % _root_.Int.ofNat (2 ^ wordsize) := by
    have hrange := ZArith.BinInt.Z.modulo_range x modulus (by
      change (0 : _root_.Int) < intOfZ modulus
      exact hmpos)
    have hr0 : (0 : _root_.Int) ≤ intOfZ (zMod x modulus) := hrange.1
    have hrlt : intOfZ (zMod x modulus) < intOfZ modulus := hrange.2
    have hd := ZArith.Zdiv.Z_div_mod_eq_full x modulus
    have hdInt := congrArg intOfZ hd
    simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
      intOfZ_zOfInt] at hdInt
    let q := intOfZ (ZArith.BinInt.Z.div x modulus)
    let r := intOfZ (zMod x modulus)
    let m := intOfZ modulus
    have hcalc : intOfZ x % m = r := by
      calc
        intOfZ x % m = (m * q + r) % m :=
          congrArg (fun a => a % m) hdInt
        _ = (r + q * m) % m := by
          rw [_root_.Int.add_comm, _root_.Int.mul_comm]
        _ = r % m := _root_.Int.add_mul_emod_self_right r q m
        _ = r := _root_.Int.emod_eq_of_lt hr0 hrlt
    simpa [m, r, hm] using hcalc.symm
  rw [hmod]
  exact _root_.Int.toNat_of_nonneg
    (_root_.Int.emod_nonneg (intOfZ x) (_root_.Int.ne_of_gt hmpos))

theorem signed_repr_eq_proof : signed_repr_eq := by
  intro x
  change zltSelect (unsigned (repr x)) half_modulus
      (unsigned (repr x)) (zSub (unsigned (repr x)) modulus) =
    zltSelect (zMod x modulus) half_modulus (zMod x modulus)
      (zSub (zMod x modulus) modulus)
  rw [suffix_int64_unsigned_repr_eq_exact]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_is_power2_correct (n logn : int)
    (hpow : is_power2 n = some logn) :
    unsigned n = zTwoP (unsigned logn) := by
  unfold is_power2 at hpow
  cases hu : unsigned n with
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
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu, hp,
            ↓reduceIte] at hpow
          injection hpow with hlog
          rcases suffix_positive_is_power2 p hp with ⟨k, hk⟩
          have hnval_p : n.val =
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
            have hz : zOfNat n.val = Numbers.BinNums.Z.Zpos p :=
              (WordCore.intval_eq_zOfNat_val n).symm.trans hu
            have hi : Int.ofNat n.val = Int.ofNat
                (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
              calc
                Int.ofNat n.val = intOfZ (zOfNat n.val) := by
                  exact (intOfZ_zOfInt (Int.ofNat n.val)).symm
                _ = intOfZ (Numbers.BinNums.Z.Zpos p) := congrArg intOfZ hz
                _ = Int.ofNat
                    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
                  rfl
            exact Int.ofNat.inj hi
          have hpbound :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p <
                2 ^ wordsize := by
            rw [← hnval_p]
            exact WordCore.val_lt n
          rw [hk] at hpbound
          have hkpowlt : 2 ^ k < 2 ^ wordsize := hpbound
          have hklt : k < wordsize :=
            (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp hkpowlt
          have hzlog : ZArith.BinInt.Z.log2
              (Numbers.BinNums.Z.Zpos p) = zOfInt (Int.ofNat k) := by
            unfold ZArith.BinInt.Z.log2
            have hpcast : intOfZ (Numbers.BinNums.Z.Zpos p) =
                Int.ofNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
              rfl
            rw [hpcast]
            have htoNat : Int.toNat
                (Int.ofNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p := by
              simp
            rw [htoNat, hk, Nat.log2_two_pow]
          have hkpow : k < 2 ^ wordsize := by
            exact Nat.lt_of_lt_of_le hklt (by decide)
          have hlog_bounds :
              zLe zZero (ZArith.BinInt.Z.log2
                (Numbers.BinNums.Z.Zpos p)) ∧
                zLe (ZArith.BinInt.Z.log2
                  (Numbers.BinNums.Z.Zpos p)) max_unsigned := by
            rw [hzlog]
            constructor
            · change 0 ≤ intOfZ (zOfInt (Int.ofNat k))
              rw [intOfZ_zOfInt]
              exact Int.natCast_nonneg _
            · change intOfZ (zOfInt (Int.ofNat k)) ≤ intOfZ max_unsigned
              rw [intOfZ_zOfInt]
              have hmax : intOfZ max_unsigned =
                  (2 ^ wordsize : Int) - 1 := by
                unfold max_unsigned modulus
                rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
                simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
                  ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
                have hone : intOfZ zOne = (1 : Int) := by rfl
                rw [hone]
                rfl
              rw [hmax]
              have hkcast : (Int.ofNat k : Int) < Int.ofNat (2 ^ wordsize) :=
                Int.ofNat_lt.mpr hkpow
              have hpcast : Int.ofNat (2 ^ wordsize) = (2 ^ wordsize : Int) :=
                Int.natCast_pow 2 wordsize
              have hkcast' : (Int.ofNat k : Int) < (2 ^ wordsize : Int) := by
                rw [← hpcast]
                exact hkcast
              omega
          have hlog_unsigned :
              unsigned (repr (ZArith.BinInt.Z.log2
                (Numbers.BinNums.Z.Zpos p))) =
                ZArith.BinInt.Z.log2 (Numbers.BinNums.Z.Zpos p) :=
            unsigned_repr_proof_api _ hlog_bounds
          have htwo : zTwoP (zOfInt (Int.ofNat k)) =
              zOfInt (Int.ofNat (2 ^ k)) := by
            have hk0 : zLe zZero (zOfInt (Int.ofNat k)) := by
              change 0 ≤ intOfZ (zOfInt (Int.ofNat k))
              rw [intOfZ_zOfInt]
              exact Int.natCast_nonneg _
            have h := suffix_two_p_nonneg
              (zOfInt (Int.ofNat k)) hk0
            have hznat : zToNat (zOfInt (Int.ofNat k)) = k := by
              change Int.toNat (intOfZ (zOfInt (Int.ofNat k))) = k
              rw [intOfZ_zOfInt]
              exact Int.toNat_natCast _
            rw [hznat] at h
            exact h
          have hpz : (Numbers.BinNums.Z.Zpos p : Z) =
              zOfInt (Int.ofNat (2 ^ k)) := by
            apply intOfZ_injective
            calc
              intOfZ (Numbers.BinNums.Z.Zpos p) =
                  Int.ofNat
                    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) := by
                rfl
              _ = Int.ofNat (2 ^ k) := congrArg Int.ofNat hk
              _ = intOfZ (zOfInt (Int.ofNat (2 ^ k))) :=
                (intOfZ_zOfInt _).symm
          rw [← hlog, hlog_unsigned, hzlog]
          exact hpz.trans htwo.symm

private theorem suffix_shl_one_eq_of_power2 (n logn : int)
    (hcorrect : unsigned n = zTwoP (unsigned logn)) :
    shl one logn = n := by
  change WordCore.repr wordsize
      (zShiftl (unsigned one) (unsigned logn)) = n
  have hlog0 : zLe zZero (unsigned logn) := by
    have h := logn.intrange.1
    change (-1 : Int) < intOfZ logn.intval at h
    change 0 ≤ intOfZ logn.intval
    omega
  have hshift : zShiftl (unsigned one) (unsigned logn) =
      zMul (unsigned one) (zTwoP (unsigned logn)) :=
    CompCert4Lean.Lib.Zbits.Zshiftl_mul_two_p
      (unsigned one) (unsigned logn) hlog0
  rw [hshift]
  have hone : unsigned one = zOne := by rfl
  rw [hone]
  have hmul : zMul zOne (zTwoP (unsigned logn)) =
      zTwoP (unsigned logn) := by
    exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Zmult_1_l_proof _
  rw [hmul]
  change WordCore.repr wordsize (zTwoP (unsigned logn)) = n
  rw [← hcorrect]
  exact repr_unsigned_proof n

theorem divs_pow2_proof : divs_pow2 := by
  intro x n logn hpow
  have hcorrect := suffix_is_power2_correct n logn hpow
  have hshl := suffix_shl_one_eq_of_power2 n logn hcorrect
  change divs x n = divs x (shl one logn)
  rw [hshl]

end CompCert4Lean.Lib.Integers.Int


namespace CompCert4Lean.Lib.Integers.Int

theorem not_lt_proof : not_lt := by
  intro x y
  rw [lt_not_proof x y]
  cases hxy : lt x y <;> cases heq : eq x y <;> simp [hxy, heq]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_zmod_sub_nat (i : Nat) (y : int) :
    zMod (zSub (zOfNat i) (unsigned y)) zwordsize =
      zOfNat ((i + wordsize - (y.val % wordsize)) % wordsize) := by
  have hy : unsigned y = zOfNat y.val := by
    change y.intval = zOfNat y.val
    exact WordCore.intval_eq_zOfNat_val y
  rw [hy]
  apply intOfZ_injective
  simp only [zMod, zSub, zwordsize, zOfNat,
    ZArith.BinInt.Z.modulo, ZArith.BinInt.Z.sub,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change (if (Int.ofNat wordsize) = 0 then
      Int.ofNat i - Int.ofNat y.val
    else if 0 < Int.ofNat wordsize then
      (Int.ofNat i - Int.ofNat y.val) % Int.ofNat wordsize
    else _) = Int.ofNat ((i + wordsize - (y.val % wordsize)) % wordsize)
  have hr : y.val % wordsize ≤ i + wordsize := by
    have hlt : y.val % wordsize < wordsize := Nat.mod_lt _ (by decide)
    omega
  simp only [show (Int.ofNat wordsize) ≠ 0 by decide,
    show 0 < Int.ofNat wordsize by decide, if_false, if_true]
  simp only [Int.ofNat_eq_natCast, Int.natCast_emod,
    Int.natCast_sub hr, Int.natCast_add]
  have hshift : Int.ofNat i + Int.ofNat wordsize -
      (Int.ofNat y.val % Int.ofNat wordsize) =
      (Int.ofNat i - (Int.ofNat y.val % Int.ofNat wordsize)) +
        Int.ofNat wordsize := by omega
  simp only [Int.ofNat_eq_natCast] at hshift
  rw [hshift, Int.add_emod_right, Int.sub_emod_emod]

theorem bits_rol_proof : bits_rol := by
  intro x y i hi
  cases i with
  | Zneg p =>
      exfalso
      have hi0 := hi.1
      change 0 ≤ -(Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) at hi0
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      have hbit := suffix_rol_bit x y 0 (by decide)
      have hmod := suffix_zmod_sub_nat 0 y
      have hmod' := hmod
      change zMod (zSub (.Z0 : Z) (unsigned y)) zwordsize =
        zOfNat ((0 + wordsize - (y.val % wordsize)) % wordsize) at hmod'
      calc
        testbit (rol x y) .Z0 = (WordCore.rol x y).val.testBit 0 := by
          rfl
        _ = x.val.testBit ((0 + wordsize - (y.val % wordsize)) % wordsize) := hbit
        _ = testbit x (zOfNat ((0 + wordsize - (y.val % wordsize)) % wordsize)) :=
          (suffix_testbit_nat x ((0 + wordsize - (y.val % wordsize)) % wordsize)).symm
        _ = testbit x (zMod (zSub .Z0 (unsigned y)) zwordsize) := by
          rw [hmod']
  | Zpos p =>
      have hkZ := hi.2
      change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
        Int.ofNat wordsize at hkZ
      have hk :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize :=
        Int.ofNat_lt.mp hkZ
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        apply intOfZ_injective
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
        rfl
      rw [← hz] at hi ⊢
      have hbit := suffix_rol_bit x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) hk
      have hmod := suffix_zmod_sub_nat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) y
      calc
        testbit (rol x y) (zOfNat
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) =
            (WordCore.rol x y).val.testBit
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
          suffix_testbit_nat (WordCore.rol x y)
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)
        _ = x.val.testBit
            ((CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + wordsize -
              (y.val % wordsize)) % wordsize) := hbit
        _ = testbit x (zOfNat
            ((CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p + wordsize -
              (y.val % wordsize)) % wordsize)) :=
          (suffix_testbit_nat x _).symm
        _ = testbit x (zMod (zSub
            (zOfNat (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p))
            (unsigned y)) zwordsize) := by
          rw [hmod]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem sign_ext_widen_proof : sign_ext_widen := by
  intro x n n' hn
  have hnpos : (0 : Int) < intOfZ n := hn.1
  have hnn' : intOfZ n ≤ intOfZ n' := hn.2
  have hsub (k : Z) : intOfZ (zSub k zOne) = intOfZ k - 1 := by
    simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    rfl
  apply same_bits_eq_proof
  intro i hi
  rw [bits_sign_ext_proof n' (sign_ext n x) i hi]
  cases hsel : CompCert4Lean.Lib.Coqlib.zlt i n' with
  | left hlt =>
      simp only [zltSelect, sumboolSelect, hsel]
  | right hge =>
      simp only [zltSelect, sumboolSelect, hsel]
      have hge' : intOfZ n' ≤ intOfZ i := hge
      have hiw : intOfZ i < intOfZ zwordsize := hi.2
      have hpred : zLe zZero (zSub n' zOne) ∧
          zLt (zSub n' zOne) zwordsize := by
        change (0 : Int) ≤ intOfZ (zSub n' zOne) ∧
          intOfZ (zSub n' zOne) < intOfZ zwordsize
        rw [hsub]
        omega
      rw [bits_sign_ext_proof n x (zSub n' zOne) hpred,
        bits_sign_ext_proof n x i hi]
      cases hseln : CompCert4Lean.Lib.Coqlib.zlt i n with
      | left hlt =>
          have hlt' : intOfZ i < intOfZ n := hlt
          omega
      | right _ =>
          simp only [zltSelect, sumboolSelect, hseln]
          cases hselpred : CompCert4Lean.Lib.Coqlib.zlt (zSub n' zOne) n with
          | left hlt =>
              have hlt' : intOfZ (zSub n' zOne) < intOfZ n := hlt
              have heq : zSub n' zOne = zSub n zOne := by
                apply intOfZ_injective
                rw [hsub, hsub]
                rw [hsub] at hlt'
                omega
              simp only [hselpred, heq, sumboolSelect]
          | right _ =>
              simp only [hselpred, sumboolSelect]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_shl_one_repr (a : Z)
    (ha : zLe zZero a ∧ zLt a zwordsize) :
    shl one (repr a) = repr (zTwoP a) := by
  change WordCore.repr wordsize
      (zShiftl (unsigned one) (unsigned (repr a))) =
    WordCore.repr wordsize (zTwoP a)
  have hu : unsigned (repr a) = a := by
    rw [suffix_unsigned_repr_eq_exact]
    apply ZArith.BinInt.Z.mod_small
    constructor
    · exact ha.1
    · change intOfZ a < (2 ^ wordsize : Int)
      change intOfZ a < intOfZ (zTwoP zwordsize)
      rw [show intOfZ (zTwoP zwordsize) = (2 : Int) ^ wordsize by
        unfold zTwoP
        unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.two_p
        unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zpower.two_p
        unfold CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.pow
        rfl]
      have hw : intOfZ a < Int.ofNat wordsize := ha.2
      have hpow : (Int.ofNat wordsize : Int) < (2 : Int) ^ wordsize := by decide
      omega
  rw [hu]
  have hone : unsigned one = zOne := by rfl
  rw [hone]
  have hs := CompCert4Lean.Lib.Zbits.Zshiftl_mul_two_p zOne a ha.1
  have hsm : zShiftl zOne a = zMul zOne (zTwoP a) := by exact hs
  rw [hsm]
  simpa [zOne] using congrArg (WordCore.repr wordsize) (ZArith.BinInt.Zmult_1_l_proof (zTwoP a))

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int
open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem one_bits_decomp_proof : one_bits_decomp := by
  unfold one_bits_decomp
  intro x
  have hfold : ∀ (l : List Z),
      (∀ a ∈ l, zLe zZero a ∧ zLt a zwordsize) →
      repr (CompCert4Lean.Lib.Zbits.powerserie l) =
        one_bits_decomp.intOfOneBits (l.map repr) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
        have ha := hl a (by simp)
        have hl' : ∀ b ∈ l, zLe zZero b ∧ zLt b zwordsize := by
          intro b hb
          exact hl b (by simp [hb])
        have hi := ih hl'
        simp only [CompCert4Lean.Lib.Zbits.powerserie, List.map_cons,
          one_bits_decomp.intOfOneBits]
        rw [add_unsigned_proof]
        rw [suffix_shl_one_repr a ha]
        rw [← hi]
        apply eqm_samerepr_proof
        apply eqm_add_proof
        · exact suffix_eqm_unsigned_repr _
        · exact suffix_eqm_unsigned_repr _
  have hxr : zLe zZero (unsigned x) ∧
      zLt (unsigned x) (zTwoPowerNat wordsize) := by
    have hu := unsigned_range_proof x
    simpa [modulus] using hu
  have hp := CompCert4Lean.Lib.Zbits.Z_one_bits_powerserie
    wordsize (unsigned x) hxr
  have hx : x = repr (unsigned x) := (repr_unsigned_proof x).symm
  have hu : unsigned (repr (unsigned x)) = unsigned x := by
    rw [suffix_unsigned_repr_eq_exact]
    apply ZArith.BinInt.Z.mod_small
    exact ⟨hxr.1, hxr.2⟩
  rw [hx]
  unfold one_bits
  rw [hu]
  have hrepr : repr (unsigned x) = repr (CompCert4Lean.Lib.Zbits.powerserie
      (CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned x) zZero)) :=
    congrArg repr hp
  rw [hrepr]
  apply hfold
  intro a ha
  exact CompCert4Lean.Lib.Zbits.Z_one_bits_range wordsize (unsigned x) a ha

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

theorem mul_pow2_proof : mul_pow2 := by
  intro x n logn hpow
  have hcorrect := suffix_is_power2_correct n logn hpow
  have hshl := suffix_shl_one_eq_of_power2 n logn hcorrect
  calc
    mul x n = mul x (shl one logn) := by rw [hshl]
    _ = shl x logn := by symm; exact shl_mul_proof x logn

end CompCert4Lean.Lib.Integers.Int


namespace CompCert4Lean.Lib.Integers.Int

theorem add_signed_proof : add_signed := by
  intro x y
  rw [add_unsigned_proof]
  apply eqm_samerepr_proof
  apply eqm_add_proof
  · exact eqm_sym_proof _ _ (eqm_signed_unsigned_proof x)
  · exact eqm_sym_proof _ _ (eqm_signed_unsigned_proof y)

end CompCert4Lean.Lib.Integers.Int


namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem divu_pow2_proof : divu_pow2 := by
  intro x n logn hpow
  have hcorrect := suffix_is_power2_correct n logn hpow
  unfold divu WordCore.divu shru WordCore.shru
  change repr (zDiv (unsigned x) (unsigned n)) =
    repr (zShiftr (unsigned x) (unsigned logn))
  rw [hcorrect]
  exact (shru_div_two_p_proof x logn).symm

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_bits_signed_stable (z i : Z)
    (hz : (-2147483648 : _root_.Int) ≤ intOfZ z ∧ intOfZ z ≤ 2147483647)
    (hi : (32 : _root_.Int) ≤ intOfZ i) :
    zTestbit z i = zTestbit z (zSub zwordsize zOne) := by
  cases i with
  | Z0 =>
      change (32 : _root_.Int) ≤ 0 at hi
      omega
  | Zneg p =>
      change (32 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat p) at hi
      have hp := posToNat_positive p
      simp only [_root_.Int.ofNat_eq_natCast] at hi
      omega
  | Zpos p =>
      have hip : 31 ≤ posToNat p := by
        change (32 : _root_.Int) ≤ _root_.Int.ofNat (posToNat p) at hi
        simp only [_root_.Int.ofNat_eq_natCast] at hi
        omega
      have hpow : (2 : Nat) ^ 31 ≤ 2 ^ posToNat p :=
        Nat.pow_le_pow_right (by decide) hip
      cases z with
      | Z0 => rfl
      | Zpos q =>
          have hq : posToNat q < 2 ^ 31 := by
            change (-2147483648 : _root_.Int) ≤ _root_.Int.ofNat (posToNat q) ∧
              _root_.Int.ofNat (posToNat q) ≤ 2147483647 at hz
            change posToNat q < 2147483648
            simp only [_root_.Int.ofNat_eq_natCast] at hz
            omega
          change Nat.testBit (posToNat q) (posToNat p) =
            Nat.testBit (posToNat q) 31
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hq hpow),
            Nat.testBit_lt_two_pow hq]
      | Zneg q =>
          have hq : posToNat q - 1 < 2 ^ 31 := by
            change (-2147483648 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat q) ∧
              -_root_.Int.ofNat (posToNat q) ≤ 2147483647 at hz
            change posToNat q - 1 < 2147483648
            simp only [_root_.Int.ofNat_eq_natCast] at hz
            omega
          change (!Nat.testBit (posToNat q - 1) (posToNat p)) =
            (!Nat.testBit (posToNat q - 1) 31)
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hq hpow),
            Nat.testBit_lt_two_pow hq]

theorem bits_signed_proof : bits_signed := by
  intro x i hi
  cases hcmp : CompCert4Lean.Lib.Coqlib.zlt i zwordsize with
  | left hlt =>
      simp only [zltSelect, sumboolSelect, hcmp]
      rw [suffix_testbit_unsigned x i hi]
      exact CompCert4Lean.Lib.Zbits.same_bits_eqmod wordsize
        (signed x) (unsigned x) i (eqm_signed_unsigned_proof x) ⟨hi, hlt⟩
  | right hge =>
      simp only [zltSelect, sumboolSelect, hcmp]
      have hstable := suffix_bits_signed_stable (signed x) i
        (signed_range_proof x) hge
      rw [hstable]
      have htop := testbit_repr_proof (signed x) (zSub zwordsize zOne)
        (by change (0 : _root_.Int) ≤ 31 ∧ (31 : _root_.Int) < 32; omega)
      rw [repr_signed_proof] at htop
      exact htop.symm

end CompCert4Lean.Lib.Integers.Int


namespace CompCert4Lean.Lib.Integers.Int

theorem eqm_unsigned_repr_proof : eqm_unsigned_repr := by
  exact suffix_eqm_unsigned_repr

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_neg_zero_proof : add_neg_zero := by
  intro x
  change WordCore.add x (WordCore.neg x) = WordCore.zero wordsize
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.add_val_int, suffix_wordcore_neg_val_int]
  change
    (Int.ofNat x.val + (-Int.ofNat x.val) % Int.ofNat (2 ^ wordsize)) %
        Int.ofNat (2 ^ wordsize) = 0
  rw [Int.add_emod_emod]
  have hzero : Int.ofNat x.val + -Int.ofNat x.val = 0 := by omega
  rw [hzero]
  rfl

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_bits_shr_nat_worker (x y : int) (n : Nat) (hn : n < wordsize) :
    testbit (shr x y) (zOfNat n) =
      testbit x (zltSelect (zAdd (zOfNat n) (unsigned y)) zwordsize
        (zAdd (zOfNat n) (unsigned y)) (zSub zwordsize zOne)) := by
  have hn0 : zLe zZero (zOfNat n) := by
    change 0 ≤ intOfZ (zOfNat n)
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    exact Int.natCast_nonneg _
  have hnlt : zLt (zOfNat n) zwordsize := by
    change intOfZ (zOfNat n) < intOfZ zwordsize
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    change (Int.ofNat n : Int) < intOfZ zwordsize
    have hw : intOfZ zwordsize = (32 : Int) := by rfl
    rw [hw]
    exact Int.ofNat_lt.mpr (by simpa [wordsize] using hn)
  change testbit (repr (zShiftr (signed x) (unsigned y))) (zOfNat n) = _
  rw [testbit_repr_proof _ _ ⟨hn0, hnlt⟩]
  change ZArith.BinInt.Z.testbit
      (ZArith.BinInt.Z.shiftr (signed x) (unsigned y)) (zOfNat n) = _
  rw [ZArith.BinInt.Z.shiftr_spec (signed x) (unsigned y) (zOfNat n) hn0]
  have hsum0 : zLe zZero (zAdd (zOfNat n) (unsigned y)) := by
    change 0 ≤ intOfZ (zAdd (zOfNat n) (unsigned y))
    simp only [zAdd, ZArith.BinInt.Z.add, zOfNat,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    have hy0 := y.intrange.1
    change (-1 : Int) < intOfZ (unsigned y) at hy0
    have hy' : 0 ≤ intOfZ (unsigned y) := by omega
    change (0 : Int) ≤ Int.ofNat n + intOfZ (unsigned y)
    have hn' : (0 : Int) ≤ Int.ofNat n := Int.natCast_nonneg _
    omega
  have hs := bits_signed_proof x (zAdd (zOfNat n) (unsigned y)) hsum0
  exact hs

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_shr_proof_worker : bits_shr := by
  intro x y i hi
  cases i with
  | Zneg p =>
      have h := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at h
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      exact suffix_bits_shr_nat_worker x y 0 (by decide)
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      have hn : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize := by
        have hlt := hi.2
        change intOfZ (zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)) < intOfZ zwordsize at hlt
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at hlt
        have hw : intOfZ zwordsize = (32 : Int) := by rfl
        rw [hw] at hlt
        exact Int.ofNat_lt.mp hlt
      exact suffix_bits_shr_nat_worker x y _ hn

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem shr_shr_worker : shr_shr := by
  intro x y z hy hz hsum
  have hyv : y.val < wordsize := suffix_ltu_iwordsize_val y hy
  have hzv : z.val < wordsize := suffix_ltu_iwordsize_val z hz
  have hav : (add y z).val < wordsize := suffix_ltu_iwordsize_val (add y z) hsum
  have hyu : unsigned y = zOfNat y.val := WordCore.intval_eq_zOfNat_val y
  have hzu : unsigned z = zOfNat z.val := WordCore.intval_eq_zOfNat_val z
  have haddval : (add y z).val = y.val + z.val := by
    change (WordCore.add y z).val = _
    rw [WordCore.add_val]
    exact Nat.mod_eq_of_lt (by
      change y.val + z.val < 2 ^ wordsize
      change y.val < 32 at hyv
      change z.val < 32 at hzv
      change y.val + z.val < 2 ^ 32
      omega)
  have haddu : unsigned (add y z) = zOfNat (y.val + z.val) := by
    change (add y z).intval = zOfNat (y.val + z.val)
    rw [WordCore.intval_eq_zOfNat_val, haddval]
  have hadd_u : unsigned (add y z) = zAdd (unsigned y) (unsigned z) := by
    rw [hyu, hzu, haddu]
    apply intOfZ_injective
    simp only [zAdd, zOfNat, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  have hy0 : zLe zZero (unsigned y) := by
    change 0 ≤ intOfZ (unsigned y)
    have h := y.intrange.1
    change (-1 : Int) < intOfZ (unsigned y) at h
    omega
  have hz0 : zLe zZero (unsigned z) := by
    change 0 ≤ intOfZ (unsigned z)
    have h := z.intrange.1
    change (-1 : Int) < intOfZ (unsigned z) at h
    omega
  apply same_bits_eq_proof
  intro i hi
  rw [bits_shr_proof_worker (shr x y) z i hi,
    bits_shr_proof_worker x (add y z) i hi]
  cases houter : CompCert4Lean.Lib.Coqlib.zlt
      (zAdd i (unsigned z)) zwordsize with
  | left hout =>
      simp only [zltSelect, sumboolSelect, houter]
      have hj0 : zLe zZero (zAdd i (unsigned z)) := by
        change 0 ≤ intOfZ (zAdd i (unsigned z))
        simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
        have hi0 : 0 ≤ intOfZ i := hi.1
        have hz0' : 0 ≤ intOfZ (unsigned z) := hz0
        omega
      have hjlt : zLt (zAdd i (unsigned z)) zwordsize := hout
      have hinner := bits_shr_proof_worker x y (zAdd i (unsigned z))
        ⟨hj0, hjlt⟩
      rw [hinner]
      have hidx : zAdd (zAdd i (unsigned z)) (unsigned y) =
          zAdd i (unsigned (add y z)) := by
        rw [hadd_u]
        apply intOfZ_injective
        simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
        omega
      rw [hidx]
      cases hright : CompCert4Lean.Lib.Coqlib.zlt
          (zAdd i (unsigned (add y z))) zwordsize with
      | left hright' => simp only [zltSelect, sumboolSelect, hright]
      | right hright' => simp only [zltSelect, sumboolSelect, hright]
  | right hout =>
      simp only [zltSelect, sumboolSelect, houter]
      have htop0 : zLe zZero (zSub zwordsize zOne) := by
        change (0 : Int) ≤ 31
        decide
      have htoplt : zLt (zSub zwordsize zOne) zwordsize := by
        change (31 : Int) < 32
        decide
      have hinner := bits_shr_proof_worker x y (zSub zwordsize zOne)
        ⟨htop0, htoplt⟩
      rw [hinner]
      cases hleft : CompCert4Lean.Lib.Coqlib.zlt
          (zAdd (zSub zwordsize zOne) (unsigned y)) zwordsize with
      | left hleft' =>
          simp only [zltSelect, sumboolSelect, hleft]
          change intOfZ (zAdd (zSub zwordsize zOne) (unsigned y)) <
            intOfZ zwordsize at hleft'
          simp only [zAdd, zSub, zOne, ZArith.BinInt.Z.add,
            ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hleft'
          have hy0' : 0 ≤ intOfZ (unsigned y) := hy0
          have hw : intOfZ zwordsize = (32 : Int) := by rfl
          have hone : intOfZ (Numbers.BinNums.Z.Zpos xH) = (1 : Int) := by rfl
          rw [hw, hone] at hleft'
          have htopY : zAdd (zSub zwordsize zOne) (unsigned y) =
              zSub zwordsize zOne := by
            apply intOfZ_injective
            simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
            omega
          rw [htopY]
          cases hright : CompCert4Lean.Lib.Coqlib.zlt
              (zAdd i (unsigned (add y z))) zwordsize with
          | left hright' =>
              exfalso
              change intOfZ (zAdd i (unsigned (add y z))) <
                intOfZ zwordsize at hright'
              simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hright'
              have hout' := hout
              change intOfZ zwordsize ≤
                intOfZ (zAdd i (unsigned z)) at hout'
              simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hout'
              have hy0' : 0 ≤ intOfZ (unsigned y) := hy0
              have hadd' : intOfZ (unsigned (add y z)) =
                  intOfZ (unsigned y) + intOfZ (unsigned z) := by
                have hh := congrArg intOfZ hadd_u
                simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hh
                exact hh
              rw [hadd'] at hright'
              omega
          | right hright' =>
              simp only [zltSelect, sumboolSelect, hright]
      | right hleft' =>
          simp only [zltSelect, sumboolSelect, hleft]
          cases hright : CompCert4Lean.Lib.Coqlib.zlt
              (zAdd i (unsigned (add y z))) zwordsize with
          | left hright' =>
              exfalso
              change intOfZ (zAdd i (unsigned (add y z))) <
                intOfZ zwordsize at hright'
              simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hright'
              have hout' := hout
              change intOfZ zwordsize ≤
                intOfZ (zAdd i (unsigned z)) at hout'
              simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hout'
              have hy0' : 0 ≤ intOfZ (unsigned y) := hy0
              have hadd' : intOfZ (unsigned (add y z)) =
                  intOfZ (unsigned y) + intOfZ (unsigned z) := by
                have hh := congrArg intOfZ hadd_u
                simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hh
                exact hh
              rw [hadd'] at hright'
              omega
          | right hright' =>
              simp only [sumboolSelect, hright]

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

theorem shr_shr_proof : shr_shr := by
  exact shr_shr_worker

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

theorem or_assoc_proof : or_assoc := by
  intro x y z
  apply WordCore.ext_of_val_eq
  change (WordCore.or (WordCore.or x y) z).val =
    (WordCore.or x (WordCore.or y z)).val
  rw [suffix_or_val, suffix_or_val, suffix_or_val, suffix_or_val]
  exact Nat.or_assoc _ _ _

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int

theorem bits_shr_proof : bits_shr := by
  exact bits_shr_proof_worker

end CompCert4Lean.Lib.Integers.Int
namespace CompCert4Lean.Lib.Integers.Int64

theorem swap_cmpu_proof : swap_cmpu := by
  intro c x y
  cases c <;> simp [cmpu, WordCore.cmpu, swap_comparison, WordCore.eq, eq_comm]

theorem negate_cmp_proof : negate_cmp := by
  intro c x y
  cases c <;> simp [cmp, WordCore.cmp, negate_comparison]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_int64_eqm_unsigned_repr :
    ∀ a : Z, eqm a (unsigned (repr a)) := by
  intro a
  unfold eqm WordCore.eqm CompCert4Lean.Lib.Zbits.eqmod
  refine ⟨ZArith.BinInt.Z.div a modulus, ?_⟩
  rw [suffix_int64_unsigned_repr_eq_exact]
  have hd := ZArith.Zdiv.Z_div_mod_eq_full a modulus
  apply intOfZ_injective
  have hd' := congrArg intOfZ hd
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at hd' ⊢
  change intOfZ a = intOfZ (ZArith.BinInt.Z.div a modulus) *
      intOfZ modulus + intOfZ (zMod a modulus)
  change intOfZ a = intOfZ modulus *
      intOfZ (ZArith.BinInt.Z.div a modulus) + intOfZ (zMod a modulus) at hd'
  rw [Int.mul_comm]
  exact hd'

theorem eqm_unsigned_repr_proof : eqm_unsigned_repr := by
  exact suffix_int64_eqm_unsigned_repr

theorem eqm_samerepr_proof : eqm_samerepr := by
  intro x y h
  apply WordCore.ext_of_val_eq
  rw [show x = zOfInt (intOfZ x) by exact (zOfInt_intOfZ x).symm,
    show y = zOfInt (intOfZ y) by exact (zOfInt_intOfZ y).symm]
  change (WordCore.repr wordsize (zOfInt (intOfZ x))).val =
    (WordCore.repr wordsize (zOfInt (intOfZ y))).val
  rw [WordCore.val_repr, WordCore.val_repr]
  have hm : intOfZ modulus = (2 ^ wordsize : Int) := by
    unfold modulus
    rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
    rfl
  unfold eqm at h
  unfold WordCore.eqm CompCert4Lean.Lib.Zbits.eqmod at h
  rcases h with ⟨k, hk⟩
  have hk' := congrArg intOfZ hk
  simp only [zAdd, zMul, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.mul, intOfZ_zOfInt] at hk'
  change intOfZ x = intOfZ k * intOfZ modulus + intOfZ y at hk'
  have hrem : intOfZ x % intOfZ modulus = intOfZ y % intOfZ modulus := by
    rw [hk', Int.add_emod, Int.mul_emod]
    simp
  rw [hm] at hrem
  exact congrArg Int.toNat hrem

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_int64_wordcore_mul_val (x y : int) :
    Int.ofNat (WordCore.mul x y).val =
      (Int.ofNat x.val * Int.ofNat y.val) % Int.ofNat (2 ^ wordsize) := by
  unfold WordCore.mul
  have hrepr : zMul (WordCore.unsigned x) (WordCore.unsigned y) =
      zOfInt (Int.ofNat x.val * Int.ofNat y.val) := by
    change zOfInt (intOfZ x.intval * intOfZ y.intval) =
      zOfInt (Int.ofNat x.val * Int.ofNat y.val)
    rw [WordCore.intval_eq_zOfNat_val x, WordCore.intval_eq_zOfNat_val y]
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  rw [hrepr, WordCore.val_repr]
  exact Int.toNat_of_nonneg
    (Int.emod_nonneg _ (Int.ne_of_gt
      (Int.natCast_pos.mpr (Nat.two_pow_pos wordsize))))

private theorem suffix_int64_not_val (x : int) :
    (WordCore.not x).val = Nat.xor x.val (2 ^ wordsize - 1) := by
  unfold WordCore.not
  have hz : zOfNat (Nat.xor x.val (2 ^ wordsize - 1)) =
      zOfInt (Int.ofNat (Nat.xor x.val (2 ^ wordsize - 1))) := by rfl
  rw [hz, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  apply Nat.mod_eq_of_lt
  apply Nat.xor_lt_two_pow (WordCore.val_lt x)
  have hpow : 0 < 2 ^ wordsize := Nat.two_pow_pos wordsize
  omega

private theorem suffix_int64_signed_injective {x y : int}
    (h : signed x = signed y) : x = y := by
  dsimp [signed, WordCore.signed] at h
  simp [zltSelect, sumboolSelect] at h
  split at h <;> split at h
  · apply WordCore.ext
    exact h
  · exfalso
    have hx0 : 0 ≤ intOfZ (unsigned x) := by
      have hx := x.intrange.1
      change (-1 : Int) < intOfZ (unsigned x) at hx
      omega
    have hymod := y.intrange.2
    change intOfZ (unsigned y) < intOfZ modulus at hymod
    change intOfZ (unsigned y) < intOfZ (zTwoPowerNat wordsize) at hymod
    have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hymod hh
    have hh' : intOfZ (unsigned x) =
        intOfZ (unsigned y) - (2 ^ wordsize : Int) := by
      exact hh
    have hneg : intOfZ (unsigned y) - (2 ^ wordsize : Int) < 0 := by
      omega
    rw [← hh'] at hneg
    exact (Int.not_lt_of_ge hx0 hneg).elim
  · exfalso
    have hy0 : 0 ≤ intOfZ (unsigned y) := by
      have hy := y.intrange.1
      change (-1 : Int) < intOfZ (unsigned y) at hy
      omega
    have hxmod := x.intrange.2
    change intOfZ (unsigned x) < intOfZ modulus at hxmod
    change intOfZ (unsigned x) < intOfZ (zTwoPowerNat wordsize) at hxmod
    have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hxmod hh
    have hh' : intOfZ (unsigned x) - (2 ^ wordsize : Int) =
        intOfZ (unsigned y) := by
      exact hh
    have hneg : intOfZ (unsigned x) - (2 ^ wordsize : Int) < 0 := by
      omega
    rw [hh'] at hneg
    exact (Int.not_lt_of_ge hy0 hneg).elim
  · have hh := congrArg intOfZ h
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hh
    have hmod : intOfZ (zTwoPowerNat wordsize) = (2 ^ wordsize : Int) := by
      rw [WordCore.twoPowerNat_eq_zOfNat_twoPow]
      rfl
    rw [hmod] at hh
    have hu : unsigned x = unsigned y := by
      apply intOfZ_injective
      exact (Int.sub_left_inj _).mp hh
    apply WordCore.ext
    exact hu

private theorem suffix_int64_lt_not : lt_not := by
  intro x y
  by_cases hxy : x = y
  · subst y
    cases h : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed x) with
    | left hlt => exact (Int.lt_irrefl _ hlt).elim
    | right hge =>
        change zltSelect (signed x) (signed x) true false =
          (!zltSelect (signed x) (signed x) true false && !eq x x)
        simp only [zltSelect, sumboolSelect]
        rw [h]
        simp [eq, WordCore.eq]
  · have heq : eq x y = false := by
      have hxy' : x.intval ≠ y.intval := by
        intro hval
        apply hxy
        exact WordCore.ext hval
      simp [eq, WordCore.eq, hxy']
    cases h1 : CompCert4Lean.Lib.Coqlib.zlt (signed y) (signed x) with
    | left h1lt =>
        cases h2 : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed y) with
        | left h2lt => exact (Int.lt_asymm h1lt h2lt).elim
        | right h2ge =>
            change zltSelect (signed y) (signed x) true false =
              (!zltSelect (signed x) (signed y) true false && !eq x y)
            simp only [zltSelect, sumboolSelect]
            rw [h1, h2]
            simp [heq]
    | right h1ge =>
        cases h2 : CompCert4Lean.Lib.Coqlib.zlt (signed x) (signed y) with
        | left h2lt =>
            change zltSelect (signed y) (signed x) true false =
              (!zltSelect (signed x) (signed y) true false && !eq x y)
            simp only [zltSelect, sumboolSelect]
            rw [h1, h2]
            simp [heq]
        | right h2ge =>
            have hs : signed x = signed y := intOfZ_injective
              (Int.le_antisymm h1ge h2ge)
            exact (hxy (suffix_int64_signed_injective hs)).elim

theorem min_signed_neg_proof : min_signed_neg := by
  change (-((2 : Int) ^ 63)) < 0
  decide

theorem mul_zero_proof : mul_zero := by
  intro x
  change WordCore.mul x (WordCore.zero wordsize) = WordCore.zero wordsize
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [suffix_int64_wordcore_mul_val]
  rfl

theorem not_involutive_proof : not_involutive := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.not (WordCore.not x)).val = x.val
  rw [suffix_int64_not_val, suffix_int64_not_val, Nat.xor_eq, Nat.xor_eq, Nat.xor_assoc,
    Nat.xor_self, Nat.xor_zero]

theorem not_lt_proof : not_lt := by
  intro x y
  rw [suffix_int64_lt_not x y]
  cases hxy : lt x y <;> cases heq : eq x y <;> simp [hxy, heq]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_trans_proof : eqm_trans := by
  intro x y z hxy hyz
  exact CompCert4Lean.Lib.Zbits.eqmod_trans modulus x y z hxy hyz

theorem xor_zero_proof : xor_zero := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.xor x (WordCore.zero wordsize)).val = x.val
  unfold WordCore.xor
  rw [WordCore.val_repr_residue]
  have hzero : (WordCore.zero wordsize).val = 0 := by
    unfold WordCore.zero
    rw [WordCore.val_repr_residue]
    rfl
  change WordCore.residue wordsize
      (zOfNat (Nat.xor x.val (WordCore.zero wordsize).val)) = x.val
  rw [hzero]
  have hz : zOfNat (Nat.xor x.val 0) =
      zOfInt (Int.ofNat (Nat.xor x.val 0)) := by rfl
  rw [hz, WordCore.residue_zOfNat]
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (WordCore.val_lt x)
    (WordCore.val_lt (WordCore.zero wordsize)))).trans (Nat.xor_zero _)

theorem and_mone_proof : and_mone := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.and x (WordCore.mone wordsize)).val = x.val
  unfold WordCore.and
  rw [WordCore.val_repr_residue]
  change WordCore.residue wordsize
      (zOfNat (Nat.land x.val (WordCore.mone wordsize).val)) = x.val
  have hmone : (WordCore.mone wordsize).val = 2 ^ wordsize - 1 := by
    unfold WordCore.mone
    rw [WordCore.val_repr_residue]
    have hz : zOpp zOne = zOfInt (-1) := by rfl
    rw [hz, WordCore.residue_zOfInt]
    change ((-1 : Int) % Int.ofNat (2 ^ wordsize)).toNat =
      2 ^ wordsize - 1
    change ((-1 : Int) % Int.ofNat (2 ^ 64)).toNat = 2 ^ 64 - 1
    decide
  rw [hmone]
  have hz : zOfNat (Nat.land x.val (2 ^ wordsize - 1)) =
      zOfInt (Int.ofNat (Nat.land x.val (2 ^ wordsize - 1))) := by rfl
  rw [hz, WordCore.residue_zOfNat]
  have hmasklt : 2 ^ wordsize - 1 < 2 ^ wordsize := by
    exact Nat.sub_lt (Nat.two_pow_pos wordsize) (by omega)
  exact (Nat.mod_eq_of_lt (Nat.and_lt_two_pow x.val hmasklt)).trans
    (Nat.and_two_pow_sub_one_of_lt_two_pow (WordCore.val_lt x))

theorem eqm_unsigned_repr_r_proof : eqm_unsigned_repr_r := by
  intro a b hab
  exact eqm_trans_proof a b (unsigned (repr b)) hab
    (suffix_int64_eqm_unsigned_repr b)

end CompCert4Lean.Lib.Integers.Int64
namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private def asmgenproof1SumboolSelect {P Q : Prop} {A : Type}
    (d : CompCert4Lean.Foundation.Logic.Support.Sumbool P Q)
    (ifso ifnot : A) : A :=
  match d with
  | .left _ => ifso
  | .right _ => ifnot

private theorem word_signed_eq_select_aux {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.signed x =
      asmgenproof1SumboolSelect
        (CompCert4Lean.Lib.Coqlib.zlt
          (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
          (two_power_nat (bits - 1)))
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
        (ZArith.BinInt.Z.sub
          (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
          (two_power_nat bits)) := by
  rfl

private theorem int_signed_eq_select_aux
    (x : CompCert4Lean.Lib.Integers.Int.int) :
    CompCert4Lean.Lib.Integers.Int.signed x =
      asmgenproof1SumboolSelect
        (CompCert4Lean.Lib.Coqlib.zlt
          (CompCert4Lean.Lib.Integers.Int.unsigned x)
          CompCert4Lean.Lib.Integers.Int.half_modulus)
        (CompCert4Lean.Lib.Integers.Int.unsigned x)
        (ZArith.BinInt.Z.sub
          (CompCert4Lean.Lib.Integers.Int.unsigned x)
          CompCert4Lean.Lib.Integers.Int.modulus) := by
  exact word_signed_eq_select_aux x

private theorem int_sub_eq_repr_signed_aux
    (x y : CompCert4Lean.Lib.Integers.Int.int) :
    CompCert4Lean.Lib.Integers.Int.sub x y =
      CompCert4Lean.Lib.Integers.Int.repr
        (ZArith.BinInt.Z.sub
          (CompCert4Lean.Lib.Integers.Int.signed x)
          (CompCert4Lean.Lib.Integers.Int.signed y)) := by
  have hx : ∃ k : Z,
      CompCert4Lean.Lib.Integers.Int.unsigned x =
        ZArith.BinInt.Z.add
          (ZArith.BinInt.Z.mul k CompCert4Lean.Lib.Integers.Int.modulus)
          (CompCert4Lean.Lib.Integers.Int.signed x) := by
    have hs := int_signed_eq_select_aux x
    cases h : CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
        CompCert4Lean.Lib.Integers.Int.half_modulus with
    | left hp =>
        have h' : CompCert4Lean.Lib.Coqlib.zlt
            (CompCert4Lean.Lib.Integers.Int.unsigned x)
            CompCert4Lean.Lib.Integers.Int.half_modulus =
            CompCert4Lean.Foundation.Logic.Support.Sumbool.left hp := by
          exact h
        have hs' : CompCert4Lean.Lib.Integers.Int.signed x =
            CompCert4Lean.Lib.Integers.Int.unsigned x := by
          simpa only [asmgenproof1SumboolSelect, h'] using hs
        refine ⟨Z0, ?_⟩
        rw [hs']
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
        change intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned x) =
          0 * intOfZ CompCert4Lean.Lib.Integers.Int.modulus +
            intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned x)
        omega
    | right hn =>
        have h' : CompCert4Lean.Lib.Coqlib.zlt
            (CompCert4Lean.Lib.Integers.Int.unsigned x)
            CompCert4Lean.Lib.Integers.Int.half_modulus =
            CompCert4Lean.Foundation.Logic.Support.Sumbool.right hn := by
          exact h
        have hs' : CompCert4Lean.Lib.Integers.Int.signed x =
            ZArith.BinInt.Z.sub
              (CompCert4Lean.Lib.Integers.Int.unsigned x)
              CompCert4Lean.Lib.Integers.Int.modulus := by
          simpa only [asmgenproof1SumboolSelect, h'] using hs
        refine ⟨Zpos xH, ?_⟩
        rw [hs']
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
          ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned x) =
          1 * 4294967296 +
            (intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned x) - 4294967296)
        omega
  have hy : ∃ k : Z,
      CompCert4Lean.Lib.Integers.Int.unsigned y =
        ZArith.BinInt.Z.add
          (ZArith.BinInt.Z.mul k CompCert4Lean.Lib.Integers.Int.modulus)
          (CompCert4Lean.Lib.Integers.Int.signed y) := by
    have hs := int_signed_eq_select_aux y
    cases h : CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.WordCore.unsigned y)
        CompCert4Lean.Lib.Integers.Int.half_modulus with
    | left hp =>
        have h' : CompCert4Lean.Lib.Coqlib.zlt
            (CompCert4Lean.Lib.Integers.Int.unsigned y)
            CompCert4Lean.Lib.Integers.Int.half_modulus =
            CompCert4Lean.Foundation.Logic.Support.Sumbool.left hp := by
          exact h
        have hs' : CompCert4Lean.Lib.Integers.Int.signed y =
            CompCert4Lean.Lib.Integers.Int.unsigned y := by
          simpa only [asmgenproof1SumboolSelect, h'] using hs
        refine ⟨Z0, ?_⟩
        rw [hs']
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
        change intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned y) =
          0 * intOfZ CompCert4Lean.Lib.Integers.Int.modulus +
            intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned y)
        omega
    | right hn =>
        have h' : CompCert4Lean.Lib.Coqlib.zlt
            (CompCert4Lean.Lib.Integers.Int.unsigned y)
            CompCert4Lean.Lib.Integers.Int.half_modulus =
            CompCert4Lean.Foundation.Logic.Support.Sumbool.right hn := by
          exact h
        have hs' : CompCert4Lean.Lib.Integers.Int.signed y =
            ZArith.BinInt.Z.sub
              (CompCert4Lean.Lib.Integers.Int.unsigned y)
              CompCert4Lean.Lib.Integers.Int.modulus := by
          simpa only [asmgenproof1SumboolSelect, h'] using hs
        refine ⟨Zpos xH, ?_⟩
        rw [hs']
        apply intOfZ_injective
        simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
          ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned y) =
          1 * 4294967296 +
            (intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned y) - 4294967296)
        omega
  rcases hx with ⟨kx, hx⟩
  rcases hy with ⟨ky, hy⟩
  unfold CompCert4Lean.Lib.Integers.Int.sub
  unfold CompCert4Lean.Lib.Integers.WordCore.sub
  apply CompCert4Lean.Lib.Integers.Int.eqm_samerepr_proof
  unfold CompCert4Lean.Lib.Integers.Int.eqm
  unfold CompCert4Lean.Lib.Integers.WordCore.eqm
  unfold CompCert4Lean.Lib.Zbits.eqmod
  refine ⟨ZArith.BinInt.Z.sub kx ky, ?_⟩
  apply intOfZ_injective
  have hx' := congrArg intOfZ hx
  have hy' := congrArg intOfZ hy
  simp only [ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hx' hy' ⊢
  have hm : intOfZ CompCert4Lean.Lib.Integers.Int.modulus = 4294967296 := by
    rfl
  rw [hm] at hx' hy'
  change intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned x) -
      intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned y) =
    (intOfZ kx - intOfZ ky) * 4294967296 +
      (intOfZ (CompCert4Lean.Lib.Integers.Int.signed x) -
        intOfZ (CompCert4Lean.Lib.Integers.Int.signed y))
  omega

namespace CompCert4Lean.X86.Asmgenproof1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem word_unsigned_eq_zOfNat_val_aux {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.unsigned x =
      ZArith.BinInt.Z.of_nat x.val := by
  exact CompCert4Lean.Lib.Integers.WordCore.intval_eq_zOfNat_val x

private theorem word_unsigned_repr_int_aux {bits : Nat} (z : Z) :
    intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned
      (CompCert4Lean.Lib.Integers.WordCore.repr bits z)) =
      intOfZ z % (2 ^ bits : Nat) := by
  have hz : zOfInt (intOfZ z) = z := zOfInt_intOfZ z
  rw [← hz, word_unsigned_eq_zOfNat_val_aux,
    CompCert4Lean.Lib.Integers.WordCore.val_repr, intOfZ_zOfInt]
  simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt
    (Int.natCast_pos.mpr (Nat.two_pow_pos bits))))

private theorem word_lt_eq_decide_aux {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.lt x y =
      decide (intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) <
        intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y)) := by
  unfold CompCert4Lean.Lib.Integers.WordCore.lt
  change asmgenproof1SumboolSelect
      (CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.WordCore.signed x)
        (CompCert4Lean.Lib.Integers.WordCore.signed y)) true false = _
  cases h : CompCert4Lean.Lib.Coqlib.zlt
      (CompCert4Lean.Lib.Integers.WordCore.signed x)
      (CompCert4Lean.Lib.Integers.WordCore.signed y) with
  | left hp =>
      have h' : CompCert4Lean.Lib.Coqlib.zlt
          (CompCert4Lean.Lib.Integers.WordCore.signed x)
          (CompCert4Lean.Lib.Integers.WordCore.signed y) =
          CompCert4Lean.Foundation.Logic.Support.Sumbool.left hp := h
      simp only [asmgenproof1SumboolSelect, h']
      have hp' : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) <
          intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y) := hp
      exact (decide_eq_true hp').symm
  | right hn =>
      have h' : CompCert4Lean.Lib.Coqlib.zlt
          (CompCert4Lean.Lib.Integers.WordCore.signed x)
          (CompCert4Lean.Lib.Integers.WordCore.signed y) =
          CompCert4Lean.Foundation.Logic.Support.Sumbool.right hn := h
      simp only [asmgenproof1SumboolSelect, h']
      exact (decide_eq_false (Int.not_lt_of_ge hn)).symm

private theorem word_ltu_eq_decide_aux {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.ltu x y =
      decide (intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) <
        intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned y)) := by
  unfold CompCert4Lean.Lib.Integers.WordCore.ltu
  change asmgenproof1SumboolSelect
      (CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
        (CompCert4Lean.Lib.Integers.WordCore.unsigned y)) true false = _
  cases h : CompCert4Lean.Lib.Coqlib.zlt
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
      (CompCert4Lean.Lib.Integers.WordCore.unsigned y) with
  | left hp =>
      have h' : CompCert4Lean.Lib.Coqlib.zlt
          (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
          (CompCert4Lean.Lib.Integers.WordCore.unsigned y) =
          CompCert4Lean.Foundation.Logic.Support.Sumbool.left hp := h
      simp only [asmgenproof1SumboolSelect, h']
      have hp' : intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) <
          intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned y) := hp
      exact (decide_eq_true hp').symm
  | right hn =>
      have h' : CompCert4Lean.Lib.Coqlib.zlt
          (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
          (CompCert4Lean.Lib.Integers.WordCore.unsigned y) =
          CompCert4Lean.Foundation.Logic.Support.Sumbool.right hn := h
      simp only [asmgenproof1SumboolSelect, h']
      exact (decide_eq_false (Int.not_lt_of_ge hn)).symm

private theorem word_signed_repr_int_aux {bits : Nat} (z : Z) (M H : Int)
    (hM : ((2 ^ bits : Nat) : Int) = M)
    (hPow : intOfZ (two_power_nat bits) = M)
    (hHalf : intOfZ (two_power_nat (bits - 1)) = H)
    (hMtwo : M = 2 * H) (hMpos : 0 < M)
    (hzlo : -M < intOfZ z) (hzhi : intOfZ z < M) :
    intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
      (CompCert4Lean.Lib.Integers.WordCore.repr bits z)) =
      if intOfZ z < -H then intOfZ z + M
      else if H ≤ intOfZ z then intOfZ z - M else intOfZ z := by
  have hu0 := word_unsigned_repr_int_aux (bits := bits) z
  rw [hM] at hu0
  have hu : intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned
      (CompCert4Lean.Lib.Integers.WordCore.repr bits z)) =
      if intOfZ z < 0 then intOfZ z + M else intOfZ z := by
    by_cases hzneg : intOfZ z < 0
    · rw [if_pos hzneg]
      have hr0 : 0 ≤ intOfZ z + M := by omega
      have hrlt : intOfZ z + M < M := by omega
      have hmod : intOfZ z % M = intOfZ z + M := by
        calc
          intOfZ z % M = (intOfZ z + M) % M := (Int.add_emod_right _ _).symm
          _ = intOfZ z + M := Int.emod_eq_of_lt hr0 hrlt
      exact hu0.trans hmod
    · rw [if_neg hzneg]
      exact hu0.trans (Int.emod_eq_of_lt (Int.le_of_not_gt hzneg) hzhi)
  unfold CompCert4Lean.Lib.Integers.WordCore.signed
  change intOfZ (asmgenproof1SumboolSelect
      (CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.WordCore.unsigned
          (CompCert4Lean.Lib.Integers.WordCore.repr bits z))
        (two_power_nat (bits - 1)))
      (CompCert4Lean.Lib.Integers.WordCore.unsigned
        (CompCert4Lean.Lib.Integers.WordCore.repr bits z))
      (ZArith.BinInt.Z.sub
        (CompCert4Lean.Lib.Integers.WordCore.unsigned
          (CompCert4Lean.Lib.Integers.WordCore.repr bits z))
        (two_power_nat bits))) = _
  cases h : CompCert4Lean.Lib.Coqlib.zlt
      (CompCert4Lean.Lib.Integers.WordCore.unsigned
        (CompCert4Lean.Lib.Integers.WordCore.repr bits z))
      (two_power_nat (bits - 1)) with
  | left hp =>
      simp only [asmgenproof1SumboolSelect]
      have hp' : intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned
          (CompCert4Lean.Lib.Integers.WordCore.repr bits z)) < H := by
        change intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned
          (CompCert4Lean.Lib.Integers.WordCore.repr bits z)) <
            intOfZ (two_power_nat (bits - 1)) at hp
        rwa [hHalf] at hp
      by_cases hlo : intOfZ z < -H
      · simp only [if_pos hlo]
        by_cases hneg : intOfZ z < 0
        · simp only [if_pos hneg] at hu
          omega
        · simp only [if_neg hneg] at hu
          omega
      · simp only [if_neg hlo]
        by_cases hhi : H ≤ intOfZ z
        · simp only [if_pos hhi]
          by_cases hneg : intOfZ z < 0
          · simp only [if_pos hneg] at hu
            omega
          · simp only [if_neg hneg] at hu
            omega
        · simp only [if_neg hhi]
          by_cases hneg : intOfZ z < 0
          · simp only [if_pos hneg] at hu
            omega
          · simp only [if_neg hneg] at hu
            omega
  | right hn =>
      simp only [asmgenproof1SumboolSelect,
        ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      have hn' : H ≤ intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned
          (CompCert4Lean.Lib.Integers.WordCore.repr bits z)) := by
        change intOfZ (two_power_nat (bits - 1)) ≤
          intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned
            (CompCert4Lean.Lib.Integers.WordCore.repr bits z)) at hn
        rwa [hHalf] at hn
      rw [hPow]
      by_cases hlo : intOfZ z < -H
      · simp only [if_pos hlo]
        by_cases hneg : intOfZ z < 0
        · simp only [if_pos hneg] at hu
          omega
        · simp only [if_neg hneg] at hu
          omega
      · simp only [if_neg hlo]
        by_cases hhi : H ≤ intOfZ z
        · simp only [if_pos hhi]
          by_cases hneg : intOfZ z < 0
          · simp only [if_pos hneg] at hu
            omega
          · simp only [if_neg hneg] at hu
            omega
        · simp only [if_neg hhi]
          by_cases hneg : intOfZ z < 0
          · simp only [if_pos hneg] at hu
            omega
          · simp only [if_neg hneg] at hu
            omega

private theorem word_signed_bounds_int_aux {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) (M H : Int)
    (hPow : intOfZ (two_power_nat bits) = M)
    (hHalf : intOfZ (two_power_nat (bits - 1)) = H)
    (hMtwo : M = 2 * H) :
    -H ≤ intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) ∧
      intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) < H := by
  have hu0 : 0 ≤ intOfZ
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x) := by
    have h := x.intrange.1
    change (-1 : Int) < intOfZ
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x) at h
    omega
  have huM : intOfZ
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x) < M := by
    have h := x.intrange.2
    change intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) <
      intOfZ (two_power_nat bits) at h
    rwa [hPow] at h
  rw [word_signed_eq_select_aux]
  cases h : CompCert4Lean.Lib.Coqlib.zlt
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
      (two_power_nat (bits - 1)) with
  | left hp =>
      simp only [asmgenproof1SumboolSelect]
      change intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) <
        intOfZ (two_power_nat (bits - 1)) at hp
      rw [hHalf] at hp
      omega
  | right hn =>
      simp only [asmgenproof1SumboolSelect,
        ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      change intOfZ (two_power_nat (bits - 1)) ≤
        intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) at hn
      rw [hHalf] at hn
      rw [hPow]
      omega

private theorem word_repr_eq_of_int_eqmod_aux {bits : Nat} (a b : Z) (k : Int)
    (h : intOfZ a = k * ((2 ^ bits : Nat) : Int) + intOfZ b) :
    CompCert4Lean.Lib.Integers.WordCore.repr bits a =
      CompCert4Lean.Lib.Integers.WordCore.repr bits b := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [← zOfInt_intOfZ a, ← zOfInt_intOfZ b,
    CompCert4Lean.Lib.Integers.WordCore.val_repr, CompCert4Lean.Lib.Integers.WordCore.val_repr]
  apply congrArg Int.toNat
  rw [h, Int.add_comm]
  exact Int.add_mul_emod_self_right _ _ _

private theorem word_sub_eq_repr_signed_aux {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) (M : Int)
    (hM : ((2 ^ bits : Nat) : Int) = M)
    (hPow : intOfZ (two_power_nat bits) = M) :
    CompCert4Lean.Lib.Integers.WordCore.sub x y =
      CompCert4Lean.Lib.Integers.WordCore.repr bits
        (ZArith.BinInt.Z.sub
          (CompCert4Lean.Lib.Integers.WordCore.signed x)
          (CompCert4Lean.Lib.Integers.WordCore.signed y)) := by
  have hx : ∃ k : Int,
      intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) =
        k * M + intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) := by
    unfold CompCert4Lean.Lib.Integers.WordCore.signed
    change ∃ k : Int,
      intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) =
        k * M + intOfZ (asmgenproof1SumboolSelect
          (CompCert4Lean.Lib.Coqlib.zlt
            (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
            (two_power_nat (bits - 1)))
          (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
          (ZArith.BinInt.Z.sub
            (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
            (two_power_nat bits)))
    cases CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
        (two_power_nat (bits - 1)) with
    | left hp =>
        simp only [asmgenproof1SumboolSelect]
        exact ⟨0, by omega⟩
    | right hn =>
        simp only [asmgenproof1SumboolSelect,
          ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        refine ⟨1, ?_⟩
        rw [hPow]
        omega
  have hy : ∃ k : Int,
      intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned y) =
        k * M + intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y) := by
    unfold CompCert4Lean.Lib.Integers.WordCore.signed
    change ∃ k : Int,
      intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned y) =
        k * M + intOfZ (asmgenproof1SumboolSelect
          (CompCert4Lean.Lib.Coqlib.zlt
            (CompCert4Lean.Lib.Integers.WordCore.unsigned y)
            (two_power_nat (bits - 1)))
          (CompCert4Lean.Lib.Integers.WordCore.unsigned y)
          (ZArith.BinInt.Z.sub
            (CompCert4Lean.Lib.Integers.WordCore.unsigned y)
            (two_power_nat bits)))
    cases CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.WordCore.unsigned y)
        (two_power_nat (bits - 1)) with
    | left hp =>
        simp only [asmgenproof1SumboolSelect]
        exact ⟨0, by omega⟩
    | right hn =>
        simp only [asmgenproof1SumboolSelect,
          ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        refine ⟨1, ?_⟩
        rw [hPow]
        omega
  rcases hx with ⟨kx, hx⟩
  rcases hy with ⟨ky, hy⟩
  unfold CompCert4Lean.Lib.Integers.WordCore.sub
  apply word_repr_eq_of_int_eqmod_aux (k := kx - ky)
  simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  rw [hM]
  rw [Int.sub_mul]
  omega

private theorem word_zero_val_aux (bits : Nat) :
    (CompCert4Lean.Lib.Integers.WordCore.zero bits).val = 0 := by
  unfold CompCert4Lean.Lib.Integers.WordCore.zero
  change (CompCert4Lean.Lib.Integers.WordCore.repr bits (zOfInt (0 : Int))).val = 0
  simpa using CompCert4Lean.Lib.Integers.WordCore.val_repr bits 0

private theorem word_one_val_aux (bits : Nat) (hbits : 0 < bits) :
    (CompCert4Lean.Lib.Integers.WordCore.one bits).val = 1 := by
  unfold CompCert4Lean.Lib.Integers.WordCore.one
  change (CompCert4Lean.Lib.Integers.WordCore.repr bits (zOfInt (1 : Int))).val = 1
  rw [CompCert4Lean.Lib.Integers.WordCore.val_repr]
  have hlt : (1 : Int) < ((2 ^ bits : Nat) : Int) :=
    Int.ofNat_lt.mpr (Nat.one_lt_two_pow (Nat.ne_of_gt hbits))
  rw [Int.emod_eq_of_lt (by omega) hlt]
  rfl

private theorem word_xor_zero_zero_aux (bits : Nat) :
    CompCert4Lean.Lib.Integers.WordCore.xor
      (CompCert4Lean.Lib.Integers.WordCore.zero bits)
      (CompCert4Lean.Lib.Integers.WordCore.zero bits) =
        CompCert4Lean.Lib.Integers.WordCore.zero bits := by
  unfold CompCert4Lean.Lib.Integers.WordCore.xor
  change CompCert4Lean.Lib.Integers.WordCore.repr bits
    (ZArith.BinInt.Z.of_nat (Nat.xor
      (CompCert4Lean.Lib.Integers.WordCore.zero bits).val
      (CompCert4Lean.Lib.Integers.WordCore.zero bits).val)) = _
  rw [word_zero_val_aux]
  rfl

private theorem word_xor_zero_one_aux (bits : Nat) (hbits : 0 < bits) :
    CompCert4Lean.Lib.Integers.WordCore.xor
      (CompCert4Lean.Lib.Integers.WordCore.zero bits)
      (CompCert4Lean.Lib.Integers.WordCore.one bits) =
        CompCert4Lean.Lib.Integers.WordCore.one bits := by
  unfold CompCert4Lean.Lib.Integers.WordCore.xor
  change CompCert4Lean.Lib.Integers.WordCore.repr bits
    (ZArith.BinInt.Z.of_nat (Nat.xor
      (CompCert4Lean.Lib.Integers.WordCore.zero bits).val
      (CompCert4Lean.Lib.Integers.WordCore.one bits).val)) = _
  rw [word_zero_val_aux, word_one_val_aux bits hbits]
  rfl

private theorem word_xor_one_zero_aux (bits : Nat) (hbits : 0 < bits) :
    CompCert4Lean.Lib.Integers.WordCore.xor
      (CompCert4Lean.Lib.Integers.WordCore.one bits)
      (CompCert4Lean.Lib.Integers.WordCore.zero bits) =
        CompCert4Lean.Lib.Integers.WordCore.one bits := by
  unfold CompCert4Lean.Lib.Integers.WordCore.xor
  change CompCert4Lean.Lib.Integers.WordCore.repr bits
    (ZArith.BinInt.Z.of_nat (Nat.xor
      (CompCert4Lean.Lib.Integers.WordCore.one bits).val
      (CompCert4Lean.Lib.Integers.WordCore.zero bits).val)) = _
  rw [word_one_val_aux bits hbits, word_zero_val_aux]
  rfl

private theorem word_xor_one_one_aux (bits : Nat) (hbits : 0 < bits) :
    CompCert4Lean.Lib.Integers.WordCore.xor
      (CompCert4Lean.Lib.Integers.WordCore.one bits)
      (CompCert4Lean.Lib.Integers.WordCore.one bits) =
        CompCert4Lean.Lib.Integers.WordCore.zero bits := by
  unfold CompCert4Lean.Lib.Integers.WordCore.xor
  change CompCert4Lean.Lib.Integers.WordCore.repr bits
    (ZArith.BinInt.Z.of_nat (Nat.xor
      (CompCert4Lean.Lib.Integers.WordCore.one bits).val
      (CompCert4Lean.Lib.Integers.WordCore.one bits).val)) = _
  rw [word_one_val_aux bits hbits]
  rfl

private theorem word_sub_overflow_eq_select_aux {bits : Nat}
    (x y bin : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.sub_overflow x y bin =
      asmgenproof1SumboolSelect
        (CompCert4Lean.Lib.Coqlib.zlt
          (ZArith.BinInt.Z.sub
            (ZArith.BinInt.Z.sub
              (CompCert4Lean.Lib.Integers.WordCore.signed x)
              (CompCert4Lean.Lib.Integers.WordCore.signed y))
            (CompCert4Lean.Lib.Integers.WordCore.signed bin))
          (ZArith.BinInt.Z.opp (two_power_nat (bits - 1))))
        (CompCert4Lean.Lib.Integers.WordCore.one bits)
        (asmgenproof1SumboolSelect
          (CompCert4Lean.Lib.Coqlib.zlt
            (ZArith.BinInt.Z.sub (two_power_nat (bits - 1)) (Zpos xH))
            (ZArith.BinInt.Z.sub
              (ZArith.BinInt.Z.sub
                (CompCert4Lean.Lib.Integers.WordCore.signed x)
                (CompCert4Lean.Lib.Integers.WordCore.signed y))
              (CompCert4Lean.Lib.Integers.WordCore.signed bin)))
          (CompCert4Lean.Lib.Integers.WordCore.one bits)
          (CompCert4Lean.Lib.Integers.WordCore.zero bits)) := by
  rfl

private theorem word_lt_sub_overflow_aux {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) (M H : Int)
    (hbits : 0 < bits)
    (hM : ((2 ^ bits : Nat) : Int) = M)
    (hPow : intOfZ (two_power_nat bits) = M)
    (hHalf : intOfZ (two_power_nat (bits - 1)) = H)
    (hMtwo : M = 2 * H) (hMpos : 0 < M) :
    CompCert4Lean.Lib.Integers.WordCore.xor
      (CompCert4Lean.Lib.Integers.WordCore.sub_overflow x y
        (CompCert4Lean.Lib.Integers.WordCore.zero bits))
      (CompCert4Lean.Lib.Integers.WordCore.negative
        (CompCert4Lean.Lib.Integers.WordCore.sub x y)) =
      if CompCert4Lean.Lib.Integers.WordCore.lt x y then
        CompCert4Lean.Lib.Integers.WordCore.one bits
      else CompCert4Lean.Lib.Integers.WordCore.zero bits := by
  have hHpos : 0 < H := by omega
  have hxrange := word_signed_bounds_int_aux x M H hPow hHalf hMtwo
  have hyrange := word_signed_bounds_int_aux y M H hPow hHalf hMtwo
  let d : Z := ZArith.BinInt.Z.sub
    (CompCert4Lean.Lib.Integers.WordCore.signed x)
    (CompCert4Lean.Lib.Integers.WordCore.signed y)
  have hd : intOfZ d =
      intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) -
        intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y) := by
    dsimp [d]
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  have hdlo : -M < intOfZ d := by omega
  have hdhi : intOfZ d < M := by omega
  have hzeroInt : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
      (CompCert4Lean.Lib.Integers.WordCore.zero bits)) = 0 := by
    change intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
      (CompCert4Lean.Lib.Integers.WordCore.repr bits Z0)) = 0
    have h := word_signed_repr_int_aux (bits := bits) Z0 M H
      hM hPow hHalf hMtwo hMpos (by change -M < (0 : Int); omega)
        (by change (0 : Int) < M; omega)
    change intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
      (CompCert4Lean.Lib.Integers.WordCore.repr bits Z0)) =
        if (0 : Int) < -H then 0 + M else if H ≤ 0 then 0 - M else 0 at h
    have hnH : ¬H < 0 := by omega
    have hnle : ¬H ≤ 0 := by omega
    simpa [hnH, hnle] using h
  have hzero : CompCert4Lean.Lib.Integers.WordCore.signed
      (CompCert4Lean.Lib.Integers.WordCore.zero bits) = Z0 := by
    apply intOfZ_injective
    exact hzeroInt
  have hsub := word_sub_eq_repr_signed_aux x y M hM hPow
  have hwrapped : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
      (CompCert4Lean.Lib.Integers.WordCore.sub x y)) =
      if intOfZ d < -H then intOfZ d + M
      else if H ≤ intOfZ d then intOfZ d - M else intOfZ d := by
    rw [hsub]
    exact word_signed_repr_int_aux d M H hM hPow hHalf hMtwo hMpos hdlo hdhi
  rw [word_sub_overflow_eq_select_aux]
  unfold CompCert4Lean.Lib.Integers.WordCore.negative
  rw [word_lt_eq_decide_aux, word_lt_eq_decide_aux]
  rw [hzero]
  have hdzero : ZArith.BinInt.Z.sub d Z0 = d := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    rw [show intOfZ Z0 = 0 by rfl]
    omega
  rw [hdzero]
  have hzint : intOfZ Z0 = 0 := rfl
  rw [hzint]
  change CompCert4Lean.Lib.Integers.WordCore.xor
      (asmgenproof1SumboolSelect
        (CompCert4Lean.Lib.Coqlib.zlt d
          (ZArith.BinInt.Z.opp (two_power_nat (bits - 1))))
        (CompCert4Lean.Lib.Integers.WordCore.one bits)
        (asmgenproof1SumboolSelect
          (CompCert4Lean.Lib.Coqlib.zlt
            (ZArith.BinInt.Z.sub (two_power_nat (bits - 1)) (Zpos xH)) d)
          (CompCert4Lean.Lib.Integers.WordCore.one bits)
          (CompCert4Lean.Lib.Integers.WordCore.zero bits)))
      (if decide (intOfZ
          (CompCert4Lean.Lib.Integers.WordCore.signed
            (CompCert4Lean.Lib.Integers.WordCore.sub x y)) < 0) then
        CompCert4Lean.Lib.Integers.WordCore.one bits
       else CompCert4Lean.Lib.Integers.WordCore.zero bits) =
    (if decide (intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) <
        intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y)) then
      CompCert4Lean.Lib.Integers.WordCore.one bits
     else CompCert4Lean.Lib.Integers.WordCore.zero bits)
  cases hlo : CompCert4Lean.Lib.Coqlib.zlt d
      (ZArith.BinInt.Z.opp (two_power_nat (bits - 1))) with
  | left hlo' =>
      simp only [asmgenproof1SumboolSelect]
      have hloI : intOfZ d < -H := by
        change intOfZ d < intOfZ
          (ZArith.BinInt.Z.opp (two_power_nat (bits - 1))) at hlo'
        simp only [ZArith.BinInt.Z.opp, intOfZ_zOfInt] at hlo'
        rw [hHalf] at hlo'
        exact hlo'
      have hxy : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) <
          intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y) := by omega
      have hwrap0 : ¬intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
          (CompCert4Lean.Lib.Integers.WordCore.sub x y)) < 0 := by
        rw [if_pos hloI] at hwrapped
        omega
      simp [hwrap0, hxy, word_xor_one_zero_aux bits hbits]
  | right hlo' =>
      have hloI : -H ≤ intOfZ d := by
        change intOfZ (ZArith.BinInt.Z.opp (two_power_nat (bits - 1))) ≤
          intOfZ d at hlo'
        simp only [ZArith.BinInt.Z.opp, intOfZ_zOfInt] at hlo'
        rwa [hHalf] at hlo'
      cases hhi : CompCert4Lean.Lib.Coqlib.zlt
          (ZArith.BinInt.Z.sub (two_power_nat (bits - 1)) (Zpos xH)) d with
      | left hhi' =>
          simp only [asmgenproof1SumboolSelect]
          have hhiI : H ≤ intOfZ d := by
            change intOfZ
                (ZArith.BinInt.Z.sub (two_power_nat (bits - 1)) (Zpos xH)) <
              intOfZ d at hhi'
            simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hhi'
            rw [hHalf, show intOfZ (Zpos xH) = 1 by rfl] at hhi'
            omega
          have hxy : ¬intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) <
              intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y) := by omega
          have hwrap : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
              (CompCert4Lean.Lib.Integers.WordCore.sub x y)) < 0 := by
            rw [if_neg (by omega), if_pos hhiI] at hwrapped
            omega
          simp [hwrap, hxy, word_xor_one_one_aux bits hbits]
      | right hhi' =>
          simp only [asmgenproof1SumboolSelect]
          have hhiI : intOfZ d < H := by
            change intOfZ d ≤ intOfZ
              (ZArith.BinInt.Z.sub (two_power_nat (bits - 1)) (Zpos xH)) at hhi'
            simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hhi'
            rw [hHalf, show intOfZ (Zpos xH) = 1 by rfl] at hhi'
            omega
          rw [if_neg (by omega), if_neg (by omega)] at hwrapped
          by_cases hdneg : intOfZ d < 0
          · have hxy : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) <
                intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y) := by omega
            have hwrap : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
                (CompCert4Lean.Lib.Integers.WordCore.sub x y)) < 0 := by omega
            simp [hwrap, hxy, word_xor_zero_one_aux bits hbits]
          · have hxy : ¬intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) <
                intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y) := by omega
            have hwrap : ¬intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed
                (CompCert4Lean.Lib.Integers.WordCore.sub x y)) < 0 := by omega
            simp [hwrap, hxy, word_xor_zero_zero_aux bits]

private theorem word_repr_unsigned_aux {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Lib.Integers.WordCore.unsigned x) = x := by
  apply CompCert4Lean.Lib.Integers.WordCore.ext_of_val_eq
  rw [word_unsigned_eq_zOfNat_val_aux]
  change (CompCert4Lean.Lib.Integers.WordCore.repr bits
    (zOfInt (Int.ofNat x.val))).val = x.val
  rw [CompCert4Lean.Lib.Integers.WordCore.val_repr]
  have hlt : Int.ofNat x.val < ((2 ^ bits : Nat) : Int) :=
    Int.ofNat_lt.mpr (CompCert4Lean.Lib.Integers.WordCore.val_lt x)
  have hmod : Int.ofNat x.val % ((2 ^ bits : Nat) : Int) =
      Int.ofNat x.val := Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt
  rw [hmod]
  simp

private theorem word_repr_signed_aux {bits : Nat}
    (x : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.repr bits
      (CompCert4Lean.Lib.Integers.WordCore.signed x) = x := by
  have hx : ∃ k : Int,
      intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) =
        k * ((2 ^ bits : Nat) : Int) +
          intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) := by
    rw [word_signed_eq_select_aux]
    cases h : CompCert4Lean.Lib.Coqlib.zlt
        (CompCert4Lean.Lib.Integers.WordCore.unsigned x)
        (two_power_nat (bits - 1)) with
    | left hp =>
        simp only [asmgenproof1SumboolSelect]
        exact ⟨0, by omega⟩
    | right hn =>
        simp only [asmgenproof1SumboolSelect,
          ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        refine ⟨1, ?_⟩
        have hpow : intOfZ (two_power_nat bits) =
            ((2 ^ bits : Nat) : Int) := by
          have hp : two_power_nat bits = ZArith.BinInt.Z.of_nat (2 ^ bits) := by
            exact CompCert4Lean.Lib.Integers.WordCore.twoPowerNat_eq_zOfNat_twoPow bits
          have hi := congrArg intOfZ hp
          simpa only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
            Int.ofNat_eq_natCast] using hi
        rw [hpow]
        omega
  rcases hx with ⟨k, hk⟩
  have hs : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) =
      (-k) * ((2 ^ bits : Nat) : Int) +
        intOfZ (CompCert4Lean.Lib.Integers.WordCore.unsigned x) := by
    rw [Int.neg_mul]
    omega
  rw [word_repr_eq_of_int_eqmod_aux _ _ (-k) hs]
  exact word_repr_unsigned_aux x

private theorem word_eq_eq_decide_signed_aux {bits : Nat}
    (x y : CompCert4Lean.Lib.Integers.WordCore.Word bits) :
    CompCert4Lean.Lib.Integers.WordCore.eq x y =
      decide (intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) =
        intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y)) := by
  by_cases hs : intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed x) =
      intOfZ (CompCert4Lean.Lib.Integers.WordCore.signed y)
  · have hsz : CompCert4Lean.Lib.Integers.WordCore.signed x =
        CompCert4Lean.Lib.Integers.WordCore.signed y := intOfZ_injective hs
    have hxy : x = y := by
      rw [← word_repr_signed_aux x, ← word_repr_signed_aux y, hsz]
    subst y
    simp [CompCert4Lean.Lib.Integers.WordCore.eq]
  · have hxy : x.intval ≠ y.intval := by
      intro hval
      apply hs
      have hxy : x = y := CompCert4Lean.Lib.Integers.WordCore.ext hval
      subst y
      rfl
    simp [CompCert4Lean.Lib.Integers.WordCore.eq, hs, hxy]

private theorem int_lt_sub_overflow_aux
    (x y : CompCert4Lean.Lib.Integers.Int.int) :
    CompCert4Lean.Lib.Integers.Int.xor
      (CompCert4Lean.Lib.Integers.Int.sub_overflow
        x y CompCert4Lean.Lib.Integers.Int.zero)
      (CompCert4Lean.Lib.Integers.Int.negative
        (CompCert4Lean.Lib.Integers.Int.sub x y)) =
      if CompCert4Lean.Lib.Integers.Int.lt x y then
        CompCert4Lean.Lib.Integers.Int.one
      else CompCert4Lean.Lib.Integers.Int.zero := by
  exact word_lt_sub_overflow_aux x y 4294967296 2147483648
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem int64_lt_sub_overflow_aux
    (x y : CompCert4Lean.Lib.Integers.Int64.int) :
    CompCert4Lean.Lib.Integers.Int64.xor
      (CompCert4Lean.Lib.Integers.Int64.sub_overflow
        x y CompCert4Lean.Lib.Integers.Int64.zero)
      (CompCert4Lean.Lib.Integers.Int64.negative
        (CompCert4Lean.Lib.Integers.Int64.sub x y)) =
      if CompCert4Lean.Lib.Integers.Int64.lt x y then
        CompCert4Lean.Lib.Integers.Int64.one
      else CompCert4Lean.Lib.Integers.Int64.zero := by
  exact word_lt_sub_overflow_aux x y 18446744073709551616 9223372036854775808
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
end CompCert4Lean.X86.Asmgenproof1

end CompCert4Lean.X86.Asmgenproof1

namespace CompCert4Lean.Lib.Integers.Int64

theorem lt_sub_overflow_proof : lt_sub_overflow := by
  exact fun x y =>
    CompCert4Lean.X86.Asmgenproof1.CompCert4Lean.X86.Asmgenproof1.int64_lt_sub_overflow_aux x y

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem sub_add_l_proof : sub_add_l := by
  intro x y z
  change WordCore.sub (WordCore.add x y) z =
    WordCore.add (WordCore.sub x z) y
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int, WordCore.add_val_int,
    WordCore.sub_val_int]
  simp only [Int.emod_sub_emod, Int.sub_emod_emod, Int.emod_add_emod,
    Int.add_emod_emod]
  congr 1
  omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ltu_inv_proof : ltu_inv := by
  intro x y h
  change zltSelect (unsigned x) (unsigned y) true false = true at h
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt (unsigned x) (unsigned y) with
  | left hxy =>
      constructor
      · have hx := x.intrange.1
        change (-1 : Int) < intOfZ (unsigned x) at hx
        change 0 ≤ intOfZ (unsigned x)
        omega
      · exact hxy
  | right hxy =>
      simp [zltSelect, sumboolSelect, hlt] at h

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem xor_commut_proof : xor_commut := by
  intro x y
  change WordCore.repr wordsize (zOfNat (Nat.xor x.val y.val)) =
    WordCore.repr wordsize (zOfNat (Nat.xor y.val x.val))
  exact congrArg (fun n : Nat => WordCore.repr wordsize (zOfNat n))
    (Nat.xor_comm x.val y.val)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem or_zero_proof : or_zero := by
  intro x
  apply WordCore.ext_of_val_eq
  change (WordCore.or x (WordCore.zero wordsize)).val = x.val
  unfold WordCore.or
  rw [WordCore.val_repr_residue]
  have hzero : (WordCore.zero wordsize).val = 0 := by
    unfold WordCore.zero
    rw [WordCore.val_repr_residue]
    rfl
  change WordCore.residue wordsize
      (zOfNat (Nat.lor x.val (WordCore.zero wordsize).val)) = x.val
  rw [hzero]
  have hz : zOfNat (Nat.lor x.val 0) =
      zOfInt (Int.ofNat (Nat.lor x.val 0)) := by rfl
  rw [hz, WordCore.residue_zOfNat]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow (WordCore.val_lt x)
    (WordCore.val_lt (WordCore.zero wordsize)))).trans (Nat.or_zero _)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem add_zero_l_proof : add_zero_l := by
  intro x
  change WordCore.add (WordCore.zero wordsize) x = x
  apply WordCore.ext_of_val_eq
  rw [WordCore.add_val]
  change (0 + x.val) % (2 ^ wordsize) = x.val
  rw [Nat.zero_add, Nat.mod_eq_of_lt (WordCore.val_lt x)]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_int64_neg_val_int (x : int) :
    Int.ofNat (WordCore.neg x).val =
      (-Int.ofNat x.val) % Int.ofNat (2 ^ wordsize) := by
  unfold WordCore.neg
  have hrepr : zOpp (WordCore.unsigned x) =
      zOfInt (-Int.ofNat x.val) := by
    change zOfInt (-intOfZ x.intval) = zOfInt (-Int.ofNat x.val)
    rw [WordCore.intval_eq_zOfNat_val x]
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  rw [hrepr, WordCore.val_repr]
  exact Int.toNat_of_nonneg
    (Int.emod_nonneg _ (Int.ne_of_gt
      (Int.natCast_pos.mpr (Nat.two_pow_pos wordsize))))

theorem sub_add_r_proof : sub_add_r := by
  intro x y z
  change WordCore.sub x (WordCore.add y z) =
    WordCore.add (WordCore.sub x z) (WordCore.neg y)
  apply WordCore.ext_of_val_eq
  apply Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int,
    WordCore.add_val_int, pg_int64_neg_val_int,
    WordCore.sub_val_int]
  simp only [Int.emod_sub_emod, Int.sub_emod_emod,
    Int.emod_add_emod, Int.add_emod_emod]
  congr 1
  omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem suffix_int64_xor_val (x y : int) :
    (xor x y).val = Nat.xor x.val y.val := by
  change (WordCore.xor x y).val = Nat.xor x.val y.val
  unfold WordCore.xor
  have hz : zOfNat (Nat.xor x.val y.val) =
      zOfInt (Int.ofNat (Nat.xor x.val y.val)) := by rfl
  rw [hz, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt
    (Nat.xor_lt_two_pow (WordCore.val_lt x) (WordCore.val_lt y))

private theorem suffix_int64_testbit_nat (x : int) (n : Nat) :
    testbit x (zOfNat n) = x.val.testBit n := by
  cases n with
  | zero => rfl
  | succ n =>
      have hp :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) = n + 1 :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat (Nat.succ_pos n)
      have hz : zOfNat (Nat.succ n) =
          .Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) := by
        rfl
      rw [hz]
      simp only [testbit, WordCore.testbit,
        WordCore.positiveToNat_eq_posToNat, hp]

private theorem suffix_int64_bits_xor_nat (x y : int) (n : Nat) :
    testbit (xor x y) (zOfNat n) =
      Bool.xor (testbit x (zOfNat n)) (testbit y (zOfNat n)) := by
  rw [suffix_int64_testbit_nat, suffix_int64_testbit_nat,
    suffix_int64_testbit_nat]
  rw [suffix_int64_xor_val, Nat.xor_eq, Nat.testBit_xor]

theorem bits_xor_proof : bits_xor := by
  intro x y i hi
  cases i with
  | Zneg _ => rfl
  | Z0 =>
      exact suffix_int64_bits_xor_nat x y 0
  | Zpos p =>
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      exact suffix_int64_bits_xor_nat x y
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p)

end CompCert4Lean.Lib.Integers.Int64


namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_suffix_same_bits_eq {x y : int}
    (h : ∀ i : Z, zLe zZero i ∧ zLt i zwordsize →
      testbit x i = testbit y i) : x = y := by
  apply WordCore.ext_of_val_eq
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < wordsize
  · have hi0 : zLe zZero (zOfNat i) := by
      change 0 ≤ intOfZ (zOfNat i)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact Int.natCast_nonneg _
    have hil : zLt (zOfNat i) zwordsize := by
      change intOfZ (zOfNat i) < intOfZ (zOfNat wordsize)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact Int.ofNat_lt.mpr (by simpa [wordsize] using hi)
    have hh := h (zOfNat i) ⟨hi0, hil⟩
    rw [suffix_int64_testbit_nat, suffix_int64_testbit_nat] at hh
    exact hh
  · have hle : wordsize ≤ i := Nat.le_of_not_gt hi
    have hpow : 2 ^ wordsize ≤ 2 ^ i :=
      Nat.pow_le_pow_right Nat.zero_lt_two hle
    have hxlt : x.val < 2 ^ i :=
      Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
    have hylt : y.val < 2 ^ i :=
      Nat.lt_of_lt_of_le (WordCore.val_lt y) hpow
    rw [Nat.testBit_lt_two_pow hxlt, Nat.testBit_lt_two_pow hylt]

private theorem pg_suffix_ror_val (x y : int) :
    (WordCore.ror x y).val =
      Nat.lor (x.val >>> (y.val % wordsize))
        (x.val <<< (wordsize - (y.val % wordsize))) % (2 ^ wordsize) := by
  unfold WordCore.ror
  dsimp
  rw [WordCore.val_repr_residue]
  exact WordCore.residue_zOfNat _ _

private theorem pg_suffix_ror_bit (x y : int) (i : Nat)
    (hi : i < wordsize) :
    ((WordCore.ror x y).val).testBit i =
      x.val.testBit ((i + y.val) % wordsize) := by
  rw [pg_suffix_ror_val]
  rw [Nat.lor_eq]
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, Bool.true_and]
  let a := y.val % wordsize
  have ha : a < wordsize := Nat.mod_lt _ (by omega)
  have htarget : (i + y.val) % wordsize = (i + a) % wordsize := by
    dsimp [a]
    exact (Nat.add_mod_mod i y.val wordsize).symm
  rw [htarget]
  simp only [decide_true, Bool.true_and]
  dsimp [a] at ⊢
  by_cases hsum : i + a < wordsize
  · have hright : (x.val >>> a).testBit i = x.val.testBit (i + a) := by
      simpa [Nat.add_comm] using
        (Nat.testBit_shiftRight x.val a i)
    have hleft : (x.val <<< (wordsize - a)).testBit i = false := by
      rw [Nat.testBit_shiftLeft]
      simp [show ¬ wordsize - a ≤ i by omega]
    dsimp [a] at hright hleft
    simp only [Nat.testBit_or, hright, hleft, Bool.or_false, decide_true,
      Bool.true_and]
    rw [Nat.mod_eq_of_lt hsum]
  · have hsum' : wordsize ≤ i + a := Nat.le_of_not_gt hsum
    have hright : (x.val >>> a).testBit i = false := by
      rw [Nat.testBit_shiftRight]
      apply Nat.testBit_lt_two_pow
      have hpow : 2 ^ wordsize ≤ 2 ^ (a + i) :=
        Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      exact Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
    have hleft : (x.val <<< (wordsize - a)).testBit i =
        x.val.testBit (i + a - wordsize) := by
      rw [Nat.testBit_shiftLeft]
      simp [show wordsize - a ≤ i by omega]
      congr 1 <;> omega
    dsimp [a] at hright hleft
    simp only [Nat.testBit_or, hright, Bool.false_or, hleft, decide_true,
      Bool.true_and]
    rw [Nat.mod_eq_sub_mod hsum']
    have hidx : i + a - wordsize < wordsize := by omega
    rw [Nat.mod_eq_of_lt hidx]

private theorem pg_suffix_ror_testbit_nat (x y : int) (n : Nat)
    (hn : n < wordsize) :
    testbit (ror x y) (zOfNat n) =
      testbit x (zOfNat ((n + y.val) % wordsize)) := by
  change testbit (WordCore.ror x y) (zOfNat n) =
    testbit x (zOfNat ((n + y.val) % wordsize))
  rw [suffix_int64_testbit_nat (WordCore.ror x y) n]
  change (WordCore.ror x y).val.testBit n =
    testbit x (zOfNat ((n + y.val) % wordsize))
  rw [pg_suffix_ror_bit x y n hn, suffix_int64_testbit_nat]

private theorem pg_suffix_zmod_add_nat (i : Nat) (y : int) :
    zMod (zAdd (zOfNat i) (unsigned y)) zwordsize =
      zOfNat ((i + y.val) % wordsize) := by
  have hy : unsigned y = zOfNat y.val := by
    change y.intval = zOfNat y.val
    exact WordCore.intval_eq_zOfNat_val y
  rw [hy]
  apply intOfZ_injective
  simp only [zMod, zAdd, zwordsize, zOfNat,
    ZArith.BinInt.Z.modulo, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change (if (Int.ofNat wordsize) = 0 then
      Int.ofNat i + Int.ofNat y.val
    else if 0 < Int.ofNat wordsize then
      (Int.ofNat i + Int.ofNat y.val) % Int.ofNat wordsize
    else _) = Int.ofNat ((i + y.val) % wordsize)
  simp [wordsize, Int.natCast_add, Int.natCast_emod]

private theorem pg_suffix_rol_val (x y : int) :
    (WordCore.rol x y).val =
      Nat.lor (x.val <<< (y.val % wordsize))
        (x.val >>> (wordsize - (y.val % wordsize))) % (2 ^ wordsize) := by
  unfold WordCore.rol
  dsimp
  rw [WordCore.val_repr_residue]
  exact WordCore.residue_zOfNat _ _

private theorem pg_suffix_rol_bit (x y : int) (i : Nat)
    (hi : i < wordsize) :
    ((WordCore.rol x y).val).testBit i =
      x.val.testBit ((i + wordsize - (y.val % wordsize)) % wordsize) := by
  rw [pg_suffix_rol_val]
  rw [Nat.lor_eq]
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, Bool.true_and]
  let a := y.val % wordsize
  have ha : a < wordsize := Nat.mod_lt _ (by omega)
  by_cases hia : a ≤ i
  · have hleft : (x.val <<< a).testBit i = x.val.testBit (i - a) := by
      rw [Nat.testBit_shiftLeft]
      simp [hia]
    have hright : (x.val >>> (wordsize - a)).testBit i = false := by
      rw [Nat.testBit_shiftRight]
      apply Nat.testBit_lt_two_pow
      have hpow : 2 ^ wordsize ≤ 2 ^ (wordsize - a + i) :=
        Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      exact Nat.lt_of_lt_of_le (WordCore.val_lt x) hpow
    dsimp [a] at hleft hright
    simp only [Nat.testBit_or, hleft, hright, Bool.false_or, decide_true,
      Bool.true_and]
    rw [Bool.or_false]
    change x.val.testBit (i - a) =
      x.val.testBit ((i + wordsize - a) % wordsize)
    rw [Nat.mod_eq_sub_mod (by omega : wordsize ≤ i + wordsize - a)]
    have hidx : i + wordsize - a - wordsize = i - a := by omega
    rw [hidx, Nat.mod_eq_of_lt (by omega : i - a < wordsize)]
  · have hia' : i < a := Nat.lt_of_not_ge hia
    have hleft : (x.val <<< a).testBit i = false := by
      rw [Nat.testBit_shiftLeft]
      simp [show ¬ a ≤ i by omega]
    have hright : (x.val >>> (wordsize - a)).testBit i =
        x.val.testBit (i + (wordsize - a)) := by
      rw [Nat.testBit_shiftRight]
      congr 1 <;> omega
    dsimp [a] at hleft hright
    simp only [Nat.testBit_or, hleft, Bool.false_or, hright, decide_true,
      Bool.true_and]
    change x.val.testBit (i + (wordsize - a)) =
      x.val.testBit ((i + wordsize - a) % wordsize)
    rw [Nat.mod_eq_of_lt (by omega : i + wordsize - a < wordsize)]
    congr 1 <;> omega

private theorem pg_suffix_neg_mod_wordsize (y : int) :
    (WordCore.neg y).val % wordsize =
      (wordsize - (y.val % wordsize)) % wordsize := by
  have hdvd : (Int.ofNat wordsize : Int) ∣ Int.ofNat (2 ^ wordsize) := by
    decide
  have hrem : y.val % wordsize ≤ wordsize := by
    exact Nat.le_of_lt (Nat.mod_lt _ (by decide))
  have hInt :
      (Int.ofNat ((WordCore.neg y).val % wordsize) : Int) =
        Int.ofNat ((wordsize - (y.val % wordsize)) % wordsize) := by
    calc
      (Int.ofNat ((WordCore.neg y).val % wordsize) : Int) =
          (Int.ofNat (WordCore.neg y).val : Int) % Int.ofNat wordsize := by
        exact (Int.natCast_emod _ _).symm
      _ = ((-Int.ofNat y.val) % Int.ofNat (2 ^ wordsize)) %
          Int.ofNat wordsize := by
        rw [pg_int64_neg_val_int]
      _ = (-Int.ofNat y.val) % Int.ofNat wordsize := by
        rw [Int.emod_emod_of_dvd _ hdvd]
      _ = (Int.ofNat wordsize -
          (Int.ofNat y.val % Int.ofNat wordsize)) % Int.ofNat wordsize := by
        rw [Int.neg_emod_eq_sub_emod]
        rw [Int.sub_emod, Int.emod_self, Int.zero_sub,
          Int.neg_emod_eq_sub_emod]
      _ = Int.ofNat ((wordsize - (y.val % wordsize)) % wordsize) := by
        simp only [Int.ofNat_eq_natCast, Int.natCast_emod]
        rw [← Int.natCast_emod y.val wordsize, ← Int.ofNat_sub hrem]
  exact Int.ofNat.inj hInt

private theorem pg_suffix_rol_testbit_nat (x y : int) (n : Nat)
    (hn : n < wordsize) :
    testbit (rol x y) (zOfNat n) =
      testbit x (zOfNat ((n + wordsize - (y.val % wordsize)) % wordsize)) := by
  change testbit (WordCore.rol x y) (zOfNat n) =
    testbit x (zOfNat ((n + wordsize - (y.val % wordsize)) % wordsize))
  rw [suffix_int64_testbit_nat (WordCore.rol x y) n]
  change (WordCore.rol x y).val.testBit n =
    testbit x (zOfNat ((n + wordsize - (y.val % wordsize)) % wordsize))
  rw [pg_suffix_rol_bit x y n hn, suffix_int64_testbit_nat]

private theorem pg_suffix_rol_neg_index (y : int) (n : Nat) :
    (n + wordsize - ((WordCore.neg y).val % wordsize)) % wordsize =
      (n + y.val) % wordsize := by
  rw [pg_suffix_neg_mod_wordsize]
  let r := y.val % wordsize
  have hr : r < wordsize := Nat.mod_lt _ (by decide)
  have hright : (n + wordsize - ((wordsize - r) % wordsize)) % wordsize =
      (n + r) % wordsize := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · have hsublt : wordsize - r < wordsize := by omega
      rw [Nat.mod_eq_of_lt hsublt]
      congr 1 <;> omega
  calc
    (n + wordsize - ((wordsize - (y.val % wordsize)) % wordsize)) % wordsize =
        (n + r) % wordsize := by simpa [r] using hright
    _ = (n + y.val) % wordsize := by
      simpa [r] using (Nat.add_mod_mod n y.val wordsize).symm

theorem ror_rol_neg_proof : ror_rol_neg := by
  intro x y _
  apply pg_suffix_same_bits_eq
  intro i hi
  cases i with
  | Zneg p =>
      have hi0 := hi.1
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hi0
      have hp : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p)
      omega
  | Z0 =>
      have hmod := pg_suffix_zmod_add_nat 0 y
      have hmod' := hmod
      change zMod (zAdd (.Z0 : Z) (unsigned y)) zwordsize =
        zOfNat ((0 + y.val) % wordsize) at hmod'
      have hidx := pg_suffix_rol_neg_index y 0
      calc
        testbit (ror x y) (.Z0 : Z) =
            testbit x (zOfNat ((0 + y.val) % wordsize)) :=
          pg_suffix_ror_testbit_nat x y 0 (by decide)
        _ = testbit x
            (zOfNat ((0 + wordsize - ((WordCore.neg y).val % wordsize)) %
              wordsize)) := by
          rw [hidx]
        _ = testbit (rol x (neg y)) (.Z0 : Z) := by
          exact (pg_suffix_rol_testbit_nat x (WordCore.neg y) 0 (by decide)).symm
  | Zpos p =>
      have hkZ := hi.2
      change (Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) : Int) <
        Int.ofNat wordsize at hkZ
      have hk :
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p < wordsize :=
        Int.ofNat_lt.mp hkZ
      have hz : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) = .Zpos p := by
        exact ZArith.Znat.positive_nat_Z p
      rw [← hz] at hi ⊢
      let n := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p
      have hmod := pg_suffix_zmod_add_nat n y
      have hidx := pg_suffix_rol_neg_index y n
      calc
        testbit (ror x y) (zOfNat n) =
            testbit x (zOfNat ((n + y.val) % wordsize)) :=
          pg_suffix_ror_testbit_nat x y n hk
        _ = testbit x
            (zOfNat ((n + wordsize - ((WordCore.neg y).val % wordsize)) %
              wordsize)) := by
          rw [hidx]
        _ = testbit (rol x (neg y)) (zOfNat n) := by
          exact (pg_suffix_rol_testbit_nat x (WordCore.neg y) n hk).symm

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem modulus_power_proof : modulus_power := by
  rfl

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_int64_testbit_unsigned (w : int) (i : Z)
    (hi : zLe zZero i) :
    testbit w i = zTestbit (unsigned w) i := by
  cases i with
  | Zneg p =>
      change (0 : Int) ≤ -Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) at hi
      have hp : 0 < CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive p
      have hpI : (0 : Int) < Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) :=
        Int.natCast_pos.mpr hp
      omega
  | Z0 =>
      simp only [testbit, WordCore.testbit]
      change Nat.testBit w.val 0 = zTestbit (unsigned w) zZero
      rw [show unsigned w = zOfNat w.val by
        unfold unsigned WordCore.unsigned
        exact WordCore.intval_eq_zOfNat_val w]
      rw [Nat.testBit_zero]
      simp only [zTestbit, ZArith.BinInt.Z.testbit,
        ZArith.BinInt.Z.odd, ZArith.BinInt.Z.even,
        ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      have habs : (_root_.Int.ofNat w.val).natAbs = w.val := by
        apply _root_.Int.ofNat.inj
        exact _root_.Int.natAbs_of_nonneg (_root_.Int.natCast_nonneg _)
      rw [habs]
      rcases Nat.mod_two_eq_zero_or_one w.val with h | h <;> simp [h]
  | Zpos p =>
      simp only [testbit, WordCore.testbit,
        WordCore.positiveToNat_eq_posToNat]
      change Nat.testBit w.val (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat p) =
        zTestbit (unsigned w) (.Zpos p)
      rw [show unsigned w = zOfNat w.val by
        unfold unsigned WordCore.unsigned
        exact WordCore.intval_eq_zOfNat_val w]
      cases hw : w.val with
      | zero =>
          rw [show zOfNat 0 = (.Z0 : Z) by rfl]
          simp [zTestbit, ZArith.BinInt.Z.testbit]
      | succ n =>
          have hz : zOfNat (Nat.succ n) =
              .Zpos (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) := by
            rfl
          rw [hz]
          have hp :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posOfNat (n + 1)) = n + 1 :=
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
              (Nat.succ_pos n)
          simp only [zTestbit, ZArith.BinInt.Z.testbit, hp]

end CompCert4Lean.Lib.Integers.Int64


namespace CompCert4Lean.Lib.Integers.Int64

private theorem pg_int64_repr_unsigned (x : int) :
    repr (unsigned x) = x := by
  apply WordCore.ext_of_val_eq
  change (WordCore.repr wordsize (unsigned x)).val = x.val
  rw [WordCore.val_repr_residue]
  rw [show unsigned x = zOfNat x.val by
    unfold unsigned WordCore.unsigned
    exact WordCore.intval_eq_zOfNat_val x]
  have hz : zOfNat x.val = CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt (Int.ofNat x.val) := by rfl
  rw [hz, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt (WordCore.val_lt x)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

private theorem pg_int64_eqm_signed_unsigned (x : int) :
    eqm (signed x) (unsigned x) := by
  unfold eqm WordCore.eqm
  unfold signed WordCore.signed
  cases h : CompCert4Lean.Lib.Coqlib.zlt (WordCore.unsigned x)
      (zTwoPowerNat (wordsize - 1)) with
  | left hlt =>
      simp only [zltSelect, sumboolSelect, h]
      exact CompCert4Lean.Lib.Zbits.eqmod_refl modulus (unsigned x)
  | right hge =>
      simp only [zltSelect, sumboolSelect, h]
      unfold CompCert4Lean.Lib.Zbits.eqmod
      refine ⟨zOpp zOne, ?_⟩
      unfold unsigned
      change zSub (WordCore.unsigned x) modulus =
        zAdd (zMul (zOpp zOne) modulus) (WordCore.unsigned x)
      apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
      simp only [zSub, zMul, zAdd, zOpp, zOne,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.opp,
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
      have hz : CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ zOne = 1 := by rfl
      rw [hz]
      omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

private theorem pg_int64_repr_signed (x : int) :
    repr (signed x) = x := by
  exact (eqm_samerepr_proof (signed x) (unsigned x)
    (pg_int64_eqm_signed_unsigned x)).trans (pg_int64_repr_unsigned x)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

private theorem pg_int64_testbit_repr (x i : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hi : zLe zZero i ∧ zLt i zwordsize) :
    testbit (repr x) i = zTestbit x i := by
  rw [pg_int64_testbit_unsigned (repr x) i hi.1]
  rw [suffix_int64_unsigned_repr_eq_exact]
  have heq : CompCert4Lean.Lib.Zbits.eqmod
      (zTwoPowerNat wordsize) x (zMod x modulus) := by
    unfold CompCert4Lean.Lib.Zbits.eqmod
    refine ⟨CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div x modulus, ?_⟩
    have hd := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.Zdiv.Z_div_mod_eq_full x modulus
    apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
    have hd' := congrArg CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ hd
    simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.mul,
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hd' ⊢
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x = CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div x modulus) *
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ modulus + CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zMod x modulus)
    change CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x = CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ modulus *
      CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.div x modulus) + CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ (zMod x modulus) at hd'
    rw [Int.mul_comm]
    exact hd'
  exact (CompCert4Lean.Lib.Zbits.same_bits_eqmod
    wordsize x (zMod x modulus) i heq hi).symm

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_int64_signed_range :
    ∀ x : int, zLe min_signed (signed x) ∧ zLe (signed x) max_signed := by
  intro x
  unfold signed WordCore.signed
  cases hlt : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned x) (zTwoPowerNat (wordsize - 1)) with
  | left h =>
      simp only [zltSelect, sumboolSelect, hlt]
      constructor
      · have hx0 : 0 ≤ intOfZ (unsigned x) := by
          have hx := x.intrange.1
          change (-1 : Int) < intOfZ (unsigned x) at hx
          omega
        change (-9223372036854775808 : Int) ≤ intOfZ (unsigned x)
        omega
      · change intOfZ (unsigned x) ≤ 9223372036854775807
        change intOfZ (unsigned x) < 9223372036854775808 at h
        omega
  | right h =>
      simp only [zltSelect, sumboolSelect, hlt]
      have hxlt := x.intrange.2
      change intOfZ (unsigned x) < intOfZ modulus at hxlt
      change intOfZ (unsigned x) < 18446744073709551616 at hxlt
      change 9223372036854775808 ≤ intOfZ (unsigned x) at h
      constructor
      · change (-9223372036854775808 : Int) ≤
          intOfZ (zSub (unsigned x) modulus)
        simp only [zSub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change (-9223372036854775808 : Int) ≤
          intOfZ (unsigned x) - 18446744073709551616
        omega
      · change intOfZ (zSub (unsigned x) modulus) ≤
          9223372036854775807
        simp only [zSub, CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.sub,
          CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
        change intOfZ (unsigned x) - 18446744073709551616 ≤
          9223372036854775807
        omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem pg_int64_bits_signed_stable
    (z i : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z)
    (hz : (-9223372036854775808 : _root_.Int) ≤ intOfZ z ∧
      intOfZ z ≤ 9223372036854775807)
    (hi : (64 : _root_.Int) ≤ intOfZ i) :
    zTestbit z i = zTestbit z (zSub zwordsize zOne) := by
  cases i with
  | Z0 =>
      change (64 : _root_.Int) ≤ 0 at hi
      omega
  | Zneg p =>
      change (64 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat p) at hi
      have hp := posToNat_positive p
      simp only [_root_.Int.ofNat_eq_natCast] at hi
      omega
  | Zpos p =>
      have hip : 63 ≤ posToNat p := by
        change (64 : _root_.Int) ≤ _root_.Int.ofNat (posToNat p) at hi
        simp only [_root_.Int.ofNat_eq_natCast] at hi
        omega
      have hpow : (2 : Nat) ^ 63 ≤ 2 ^ posToNat p :=
        Nat.pow_le_pow_right (by decide) hip
      cases z with
      | Z0 => rfl
      | Zpos q =>
          have hq : posToNat q < 2 ^ 63 := by
            change (-9223372036854775808 : _root_.Int) ≤
                _root_.Int.ofNat (posToNat q) ∧
              _root_.Int.ofNat (posToNat q) ≤ 9223372036854775807 at hz
            change posToNat q < 9223372036854775808
            simp only [_root_.Int.ofNat_eq_natCast] at hz
            omega
          change Nat.testBit (posToNat q) (posToNat p) =
            Nat.testBit (posToNat q) 63
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hq hpow),
            Nat.testBit_lt_two_pow hq]
      | Zneg q =>
          have hq : posToNat q - 1 < 2 ^ 63 := by
            change (-9223372036854775808 : _root_.Int) ≤
                -_root_.Int.ofNat (posToNat q) ∧
              -_root_.Int.ofNat (posToNat q) ≤ 9223372036854775807 at hz
            change posToNat q - 1 < 9223372036854775808
            simp only [_root_.Int.ofNat_eq_natCast] at hz
            omega
          change (!Nat.testBit (posToNat q - 1) (posToNat p)) =
            (!Nat.testBit (posToNat q - 1) 63)
          rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hq hpow),
            Nat.testBit_lt_two_pow hq]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_signed_proof : bits_signed := by
  intro x i hi
  cases hcmp : CompCert4Lean.Lib.Coqlib.zlt i zwordsize with
  | left hlt =>
      simp only [zltSelect, sumboolSelect, hcmp]
      rw [pg_int64_testbit_unsigned x i hi]
      exact CompCert4Lean.Lib.Zbits.same_bits_eqmod wordsize
        (signed x) (unsigned x) i (pg_int64_eqm_signed_unsigned x) ⟨hi, hlt⟩
  | right hge =>
      simp only [zltSelect, sumboolSelect, hcmp]
      have hstable := pg_int64_bits_signed_stable (signed x) i (by
        have hs := pg_int64_signed_range x
        exact hs) hge
      rw [hstable]
      have htop := pg_int64_testbit_repr (signed x)
        (zSub zwordsize zOne)
        (by change (0 : _root_.Int) ≤ 63 ∧ (63 : _root_.Int) < 64; omega)
      rw [pg_int64_repr_signed] at htop
      exact htop.symm

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem repr_unsigned_proof : repr_unsigned := pg_int64_repr_unsigned

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem repr_signed_proof : repr_signed := pg_int64_repr_signed

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem testbit_repr_proof : testbit_repr := pg_int64_testbit_repr

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem signed_range_proof : signed_range := pg_int64_signed_range

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem eqm_signed_unsigned_proof : eqm_signed_unsigned := pg_int64_eqm_signed_unsigned

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

theorem unsigned_repr_eq_proof : unsigned_repr_eq := suffix_int64_unsigned_repr_eq_exact

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_commut_proof : add_commut := Ptrofs.add_commut_proof_api

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_assoc_proof : add_assoc := Ptrofs.add_assoc_proof_api

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_zero_proof : add_zero := by
  intro value
  rw [add_commut_proof, add_zero_l_proof]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem modulus_pos_proof : modulus_pos := by
  change (0 : _root_.Int) < 18446744073709551616
  decide

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem half_modulus_pos_proof : half_modulus_pos := by
  change (0 : _root_.Int) < 9223372036854775808
  decide

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eq_true_proof : eq_true := by
  intro value
  simp [eq, WordCore.eq]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eq_sym_proof : eq_sym := by
  intro left right
  simp [eq, WordCore.eq, eq_comm]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eq_spec_proof : eq_spec := by
  intro left right
  by_cases equal : left.intval = right.intval
  · have same : left = right := WordCore.ext equal
    simp [eq, WordCore.eq, equal, same]
  · have different : left ≠ right := by
      intro same
      exact equal (congrArg (fun value => value.intval) same)
    simp [eq, WordCore.eq, equal, different]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem signed_zero_proof : signed_zero := by
  rfl

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem one_not_zero_proof : one_not_zero := by
  intro same
  have values := congrArg WordCore.Word.val same
  change (1 : Nat) = 0 at values
  omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_refl2_proof : eqm_refl2 := by
  intro left right same
  subst right
  exact eqm_refl_proof left

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem unsigned_range_proof : unsigned_range := by
  intro value
  constructor
  · have lower := value.intrange.1
    change (-1 : _root_.Int) < intOfZ (unsigned value) at lower
    change 0 ≤ intOfZ (unsigned value)
    omega
  · exact value.intrange.2

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem lt_not_proof : lt_not := suffix_int64_lt_not

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_add_proof : eqm_add := CompCert4Lean.Lib.Zbits.eqmod_add modulus

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_mult_proof : eqm_mult := CompCert4Lean.Lib.Zbits.eqmod_mult modulus

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem mul_one_proof : mul_one := by
  intro value
  change WordCore.mul value (WordCore.one wordsize) = value
  unfold WordCore.mul
  rw [show WordCore.unsigned (WordCore.one wordsize) = Zpos xH by rfl]
  change WordCore.repr wordsize
      (ZArith.BinInt.Z.mul (WordCore.unsigned value) (Zpos xH)) = value
  rw [ZArith.BinInt.Zmult_1_r_proof]
  exact repr_unsigned_proof value

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem repr_unsigned_proof : repr_unsigned := Int64.repr_unsigned_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem unsigned_range_proof : unsigned_range := Int64.unsigned_range_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem unsigned_repr_eq_proof : unsigned_repr_eq := Int64.unsigned_repr_eq_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_unsigned_repr_proof : eqm_unsigned_repr := Int64.eqm_unsigned_repr_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem modulus_pos_proof : modulus_pos := Int64.modulus_pos_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem min_signed_neg_proof : min_signed_neg := Int64.min_signed_neg_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eq_true_proof : eq_true := Int64.eq_true_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eq_spec_proof : eq_spec := Int64.eq_spec_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eq_false_proof : eq_false := by
  intro left right different
  have fields : left.intval ≠ right.intval := fun same => different (WordCore.ext same)
  simp [eq, WordCore.eq, fields]

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_zero_proof : add_zero := Int64.add_zero_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_zero_l_proof : add_zero_l := Int64.add_zero_l_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem sub_add_r_proof : sub_add_r := Int64.sub_add_r_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem unsigned_zero_proof : unsigned_zero := by
  rfl

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem unsigned_one_proof : unsigned_one := by
  rfl

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_unsigned_proof : add_unsigned := by
  intro left right
  rfl

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem swap_cmpu_proof : swap_cmpu := Int64.swap_cmpu_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_repr_eq_proof : eqm_repr_eq := by
  intro number value equivalent
  exact (Int64.eqm_samerepr_proof number (unsigned value) equivalent).trans
    (repr_unsigned_proof value)

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem modulus_eq64_proof : modulus_eq64 := by
  intro architecture
  rfl

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem modulus_eq32_proof : modulus_eq32 := by
  intro incompatible
  cases incompatible

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm32_proof : eqm32 := by
  intro incompatible
  cases incompatible

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem agree32_repr_proof : agree32_repr := by
  intro incompatible
  cases incompatible

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem agree32_of_int_proof : agree32_of_int := by
  intro incompatible
  cases incompatible

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem of_int_to_int_proof : of_int_to_int := by
  intro incompatible
  cases incompatible

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm64_proof : eqm64 := by
  intro architecture left right
  rfl

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem agree64_repr_proof : agree64_repr := by
  intro architecture number
  rfl

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem of_int64_to_int64_proof : of_int64_to_int64 := by
  intro architecture value
  change Int64.repr (Int64.unsigned (Int64.repr (Int64.unsigned value))) = value
  exact (Int64.repr_unsigned_proof (Int64.repr (Int64.unsigned value))).trans
    (Int64.repr_unsigned_proof value)

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem unsigned_range_2_proof : unsigned_range_2 := by
  intro value
  have bounds := unsigned_range_proof value
  refine ⟨bounds.1, ?_⟩
  have upper := bounds.2
  change intOfZ (unsigned value) < 18446744073709551616 at upper
  change intOfZ (unsigned value) ≤ 18446744073709551615
  omega

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem unsigned_repr_proof : unsigned_repr := by
  intro number bounds
  apply Eq.symm
  apply CompCert4Lean.Lib.Zbits.eqmod_small_eq modulus number (unsigned (repr number))
  · exact eqm_unsigned_repr_proof number
  · refine ⟨bounds.1, ?_⟩
    have upper := bounds.2
    change intOfZ number ≤ 18446744073709551615 at upper
    change intOfZ number < 18446744073709551616
    omega
  · exact unsigned_range_proof (repr number)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem negate_cmpu_proof : negate_cmpu := by
  intro comparison left right
  cases comparison <;> simp [cmpu, WordCore.cmpu, negate_comparison]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem swap_cmp_proof : swap_cmp := by
  intro comparison left right
  cases comparison <;> simp [cmp, WordCore.cmp, swap_comparison, WordCore.eq, eq_comm]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem unsigned_repr_proof : unsigned_repr := Int64.unsigned_repr_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem negate_cmpu_proof : negate_cmpu := Int64.negate_cmpu_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_sym_proof : eqm_sym := by
  intro left right equivalent
  unfold eqm WordCore.eqm CompCert4Lean.Lib.Zbits.eqmod at equivalent ⊢
  obtain ⟨quotient, equality⟩ := equivalent
  refine ⟨zOpp quotient, ?_⟩
  apply intOfZ_injective
  have converted := congrArg intOfZ equality
  simp only [zAdd, zMul, zOpp, ZArith.BinInt.Z.add,
    ZArith.BinInt.Z.mul, ZArith.BinInt.Z.opp, intOfZ_zOfInt] at converted ⊢
  change intOfZ right = -intOfZ quotient * intOfZ modulus + intOfZ left
  change intOfZ left = intOfZ quotient * intOfZ modulus + intOfZ right at converted
  rw [converted]
  simp only [_root_.Int.neg_mul]
  omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_unsigned_repr_l_proof : eqm_unsigned_repr_l := by
  intro left right equivalent
  exact eqm_trans_proof (unsigned (repr left)) left right
    (eqm_sym_proof left (unsigned (repr left)) (eqm_unsigned_repr_proof left)) equivalent

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem add_signed_proof : add_signed := by
  intro left right
  change repr (zAdd (unsigned left) (unsigned right)) =
    repr (zAdd (signed left) (signed right))
  apply eqm_samerepr_proof
  apply eqm_add_proof
  · exact eqm_sym_proof _ _ (eqm_signed_unsigned_proof left)
  · exact eqm_sym_proof _ _ (eqm_signed_unsigned_proof right)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem mul_commut_proof : mul_commut := by
  intro left right
  change WordCore.mul left right = WordCore.mul right left
  apply WordCore.ext_of_val_eq
  apply _root_.Int.ofNat.inj
  rw [suffix_int64_wordcore_mul_val, suffix_int64_wordcore_mul_val,
    _root_.Int.mul_comm]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem sub_zero_l_proof : sub_zero_l := by
  intro value
  change WordCore.sub value (WordCore.zero wordsize) = value
  apply WordCore.ext_of_val_eq
  apply _root_.Int.ofNat.inj
  rw [WordCore.sub_val_int]
  change (_root_.Int.ofNat value.val - 0) % _root_.Int.ofNat (2 ^ wordsize) =
    _root_.Int.ofNat value.val
  rw [_root_.Int.sub_zero]
  exact _root_.Int.emod_eq_of_lt (_root_.Int.natCast_nonneg _)
    (_root_.Int.ofNat_lt.mpr (WordCore.val_lt value))

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem sub_add_opp_proof : sub_add_opp := by
  intro left right
  change WordCore.sub left right = WordCore.add left (WordCore.neg right)
  apply WordCore.ext_of_val_eq
  apply _root_.Int.ofNat.inj
  rw [WordCore.sub_val_int, WordCore.add_val_int, pg_int64_neg_val_int,
    _root_.Int.add_emod_emod]
  rw [_root_.Int.sub_eq_add_neg]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem sub_add_opp_proof : sub_add_opp := Int64.sub_add_opp_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem neg_involutive_proof : neg_involutive := by
  intro value
  change WordCore.neg (WordCore.neg value) = value
  apply WordCore.ext_of_val_eq
  apply _root_.Int.ofNat.inj
  rw [pg_int64_neg_val_int, pg_int64_neg_val_int]
  calc
    (-((-_root_.Int.ofNat value.val) % _root_.Int.ofNat (2 ^ wordsize))) %
        _root_.Int.ofNat (2 ^ wordsize) =
        _root_.Int.ofNat value.val % _root_.Int.ofNat (2 ^ wordsize) := by
      simpa only [_root_.Int.zero_sub, _root_.Int.neg_neg] using
        (_root_.Int.sub_emod_emod 0 (-_root_.Int.ofNat value.val)
          (_root_.Int.ofNat (2 ^ wordsize)))
    _ = _ := _root_.Int.emod_eq_of_lt (_root_.Int.natCast_nonneg _)
      (_root_.Int.ofNat_lt.mpr (WordCore.val_lt value))

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem mul_add_distr_l_proof : mul_add_distr_l := by
  intro left middle right
  change WordCore.mul (WordCore.add left middle) right =
    WordCore.add (WordCore.mul left right) (WordCore.mul middle right)
  apply WordCore.ext_of_val_eq
  apply _root_.Int.ofNat.inj
  simp only [suffix_int64_wordcore_mul_val, WordCore.add_val_int,
    _root_.Int.emod_add_emod, _root_.Int.add_emod_emod]
  rw [_root_.Int.mul_emod, _root_.Int.emod_emod, ← _root_.Int.mul_emod,
    _root_.Int.add_mul]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem mul_add_distr_r_proof : mul_add_distr_r := by
  intro left middle right
  rw [mul_commut_proof left (add middle right), mul_add_distr_l_proof,
    mul_commut_proof middle left, mul_commut_proof right left]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shru_zero_proof : shru_zero := by
  intro value
  change repr (ZArith.BinInt.Z.shiftr (unsigned value) Z0) = value
  rw [ZArith.BinInt.Z.shiftr_0_r]
  exact repr_unsigned_proof value

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shr_zero_proof : shr_zero := by
  intro value
  change repr (ZArith.BinInt.Z.shiftr (signed value) Z0) = value
  rw [ZArith.BinInt.Z.shiftr_0_r]
  exact repr_signed_proof value

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shl_zero_proof : shl_zero := by
  intro value
  change repr (ZArith.BinInt.Z.shiftl (unsigned value) Z0) = value
  rw [ZArith.BinInt.Z.shiftl_0_r]
  exact repr_unsigned_proof value

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem signed_repr_proof : signed_repr := by
  intro number bounds
  have shifted_range (candidate : Z)
      (candidate_bounds : zLe min_signed candidate ∧ zLe candidate max_signed) :
      zLe zZero (zAdd candidate half_modulus) ∧
        zLt (zAdd candidate half_modulus) modulus := by
    change (-9223372036854775808 : _root_.Int) ≤ intOfZ candidate ∧
      intOfZ candidate ≤ 9223372036854775807 at candidate_bounds
    change 0 ≤ intOfZ (zAdd candidate half_modulus) ∧
      intOfZ (zAdd candidate half_modulus) < 18446744073709551616
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change 0 ≤ intOfZ candidate + 9223372036854775808 ∧
      intOfZ candidate + 9223372036854775808 < 18446744073709551616
    omega
  have equivalent : eqm (signed (repr number)) number :=
    eqm_trans_proof (signed (repr number)) (unsigned (repr number)) number
      (eqm_signed_unsigned_proof (repr number))
      (eqm_sym_proof number (unsigned (repr number)) (eqm_unsigned_repr_proof number))
  have translated := CompCert4Lean.Lib.Zbits.eqmod_small_eq modulus
    (zAdd (signed (repr number)) half_modulus) (zAdd number half_modulus)
    (eqm_add_proof _ _ _ _ equivalent (eqm_refl_proof half_modulus))
    (shifted_range _ (signed_range_proof (repr number))) (shifted_range number bounds)
  apply intOfZ_injective
  have converted := congrArg intOfZ translated
  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at converted
  omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem signed_repr_proof : signed_repr := Int64.signed_repr_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ltu_not_proof : ltu_not := by
  intro left right
  change zltSelect (unsigned right) (unsigned left) true false =
    (!zltSelect (unsigned left) (unsigned right) true false &&
      !decide (left.intval = right.intval))
  cases forward : CompCert4Lean.Lib.Coqlib.zlt (unsigned right) (unsigned left) with
  | left less =>
      cases reverse : CompCert4Lean.Lib.Coqlib.zlt (unsigned left) (unsigned right) with
      | left opposite => exact (_root_.Int.lt_asymm less opposite).elim
      | right atLeast =>
          have different : left.intval ≠ right.intval := by
            intro fields
            have bound : intOfZ right.intval < intOfZ left.intval := less
            rw [fields] at bound
            omega
          simp [zltSelect, sumboolSelect, forward, reverse, different]
  | right atLeast =>
      cases reverse : CompCert4Lean.Lib.Coqlib.zlt (unsigned left) (unsigned right) with
      | left less => simp [zltSelect, sumboolSelect, forward, reverse]
      | right opposite =>
          have equal : left.intval = right.intval :=
            intOfZ_injective (_root_.Int.le_antisymm atLeast opposite)
          simp [zltSelect, sumboolSelect, forward, reverse, equal]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem not_ltu_proof : not_ltu := by
  intro left right
  rw [ltu_not_proof left right]
  cases less : ltu left right <;> cases same : eq left right <;> simp [less, same]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ltu_not_proof : ltu_not := Int64.ltu_not_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem not_ltu_proof : not_ltu := Int64.not_ltu_proof

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem xor_assoc_proof : xor_assoc := by
  intro left middle right
  apply WordCore.ext_of_val_eq
  simp only [suffix_int64_xor_val, Nat.xor_eq, Nat.xor_assoc]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem xor_idem_proof : xor_idem := by
  intro value
  apply WordCore.ext_of_val_eq
  rw [suffix_int64_xor_val]
  change Nat.xor value.val value.val = 0
  exact Nat.xor_self value.val

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem xor_zero_equal_proof : xor_zero_equal := by
  intro left right equal
  calc
    left = xor left zero := (xor_zero_proof left).symm
    _ = xor left (xor left right) := by rw [equal]
    _ = xor (xor left left) right := (xor_assoc_proof left left right).symm
    _ = right := by
      rw [xor_idem_proof, xor_commut_proof zero right, xor_zero_proof]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_zero_proof : bits_zero := by
  intro index
  cases index with
  | Z0 => rfl
  | Zneg position => rfl
  | Zpos position =>
      change Nat.testBit 0 (WordCore.positiveToNat position) = false
      simp

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem and_commut_proof : and_commut := by
  intro left right
  change repr (zOfNat (Nat.land left.val right.val)) =
    repr (zOfNat (Nat.land right.val left.val))
  rw [Nat.land_eq, Nat.land_eq, Nat.and_comm]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem or_commut_proof : or_commut := by
  intro left right
  change repr (zOfNat (Nat.lor left.val right.val)) =
    repr (zOfNat (Nat.lor right.val left.val))
  rw [Nat.lor_eq, Nat.lor_eq, Nat.or_comm]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem and_zero_proof : and_zero := by
  intro value
  change repr (zOfNat (Nat.land value.val 0)) = zero
  rw [Nat.land_eq, Nat.and_zero]
  rfl

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem and_idem_proof : and_idem := by
  intro value
  change repr (zOfNat (Nat.land value.val value.val)) = value
  rw [Nat.land_eq, Nat.and_self, ← WordCore.intval_eq_zOfNat_val value]
  exact repr_unsigned_proof value

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_above_proof : bits_above := by
  intro value index above
  cases index with
  | Z0 =>
      change (64 : _root_.Int) ≤ 0 at above
      omega
  | Zneg position =>
      change (64 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat position) at above
      simp only [_root_.Int.ofNat_eq_natCast] at above
      omega
  | Zpos position =>
      have exponent : wordsize ≤ posToNat position := by
        change (64 : _root_.Int) ≤ _root_.Int.ofNat (posToNat position) at above
        simp only [_root_.Int.ofNat_eq_natCast] at above
        change 64 ≤ posToNat position
        omega
      change Nat.testBit value.val (WordCore.positiveToNat position) = false
      rw [WordCore.positiveToNat_eq_posToNat]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (WordCore.val_lt value)
        (Nat.pow_le_pow_right Nat.zero_lt_two exponent))

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem same_bits_eq_proof : same_bits_eq := by
  intro left right matching
  apply WordCore.ext_of_val_eq
  apply Nat.eq_of_testBit_eq
  intro index
  by_cases inRange : index < wordsize
  · have lower : zLe zZero (zOfNat index) := by
      change 0 ≤ intOfZ (zOfNat index)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact _root_.Int.natCast_nonneg _
    have upper : zLt (zOfNat index) zwordsize := by
      change intOfZ (zOfNat index) < intOfZ (zOfNat wordsize)
      simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
      exact _root_.Int.ofNat_lt.mpr inRange
    have bits := matching (zOfNat index) ⟨lower, upper⟩
    rw [suffix_int64_testbit_nat, suffix_int64_testbit_nat] at bits
    exact bits
  · have power : 2 ^ wordsize ≤ 2 ^ index :=
      Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt inRange)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (WordCore.val_lt left) power),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (WordCore.val_lt right) power)]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_mone_proof : bits_mone := by
  intro index bounds
  change testbit (repr (zOpp zOne)) index = true
  rw [testbit_repr_proof _ _ bounds]
  cases index with
  | Z0 => rfl
  | Zneg position =>
      have positive := posToNat_positive position
      have lower := bounds.1
      change (0 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat position) at lower
      simp only [_root_.Int.ofNat_eq_natCast] at lower
      omega
  | Zpos position =>
      change (!Nat.testBit 0 (posToNat position)) = true
      simp

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_and_val (left right : int) :
    (and left right).val = Nat.land left.val right.val := by
  change (WordCore.and left right).val = Nat.land left.val right.val
  unfold WordCore.and
  have encoded : zOfNat (Nat.land left.val right.val) =
      zOfInt (_root_.Int.ofNat (Nat.land left.val right.val)) := by rfl
  rw [encoded, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (WordCore.val_lt right))

theorem and_assoc_proof : and_assoc := by
  intro left middle right
  apply WordCore.ext_of_val_eq
  simp only [manual_int64_and_val, Nat.land_eq, Nat.and_assoc]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_and_proof : bits_and := by
  intro left right index bounds
  have natural (offset : Nat) :
      testbit (and left right) (zOfNat offset) =
        (testbit left (zOfNat offset) && testbit right (zOfNat offset)) := by
    rw [suffix_int64_testbit_nat, suffix_int64_testbit_nat, suffix_int64_testbit_nat]
    rw [manual_int64_and_val, Nat.land_eq, Nat.testBit_and]
  cases index with
  | Zneg position => rfl
  | Z0 => exact natural 0
  | Zpos position =>
      have encoded : zOfNat (posToNat position) = .Zpos position :=
        ZArith.Znat.positive_nat_Z position
      rw [← encoded]
      exact natural (posToNat position)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_or_val (left right : int) :
    (or left right).val = Nat.lor left.val right.val := by
  change (WordCore.or left right).val = Nat.lor left.val right.val
  unfold WordCore.or
  have encoded : zOfNat (Nat.lor left.val right.val) =
      zOfInt (_root_.Int.ofNat (Nat.lor left.val right.val)) := by rfl
  rw [encoded, WordCore.val_repr_residue, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (WordCore.val_lt left) (WordCore.val_lt right))

theorem or_assoc_proof : or_assoc := by
  intro left middle right
  apply WordCore.ext_of_val_eq
  simp only [manual_int64_or_val, Nat.lor_eq, Nat.or_assoc]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_or_proof : bits_or := by
  intro left right index bounds
  have natural (offset : Nat) :
      testbit (or left right) (zOfNat offset) =
        (testbit left (zOfNat offset) || testbit right (zOfNat offset)) := by
    rw [suffix_int64_testbit_nat, suffix_int64_testbit_nat, suffix_int64_testbit_nat]
    rw [manual_int64_or_val, Nat.lor_eq, Nat.testBit_or]
  cases index with
  | Zneg position => rfl
  | Z0 => exact natural 0
  | Zpos position =>
      have encoded : zOfNat (posToNat position) = .Zpos position :=
        ZArith.Znat.positive_nat_Z position
      rw [← encoded]
      exact natural (posToNat position)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem or_mone_proof : or_mone := by
  intro value
  apply same_bits_eq_proof
  intro index bounds
  simp only [bits_or_proof value mone index bounds, bits_mone_proof index bounds,
    Bool.or_true]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem not_or_and_not_proof : not_or_and_not := by
  have complement (value : int) (index : Z)
      (bounds : zLe zZero index ∧ zLt index zwordsize) :
      testbit (not value) index = !(testbit value index) := by
    have encoding : not value = xor value mone := by
      apply WordCore.ext_of_val_eq
      change (WordCore.not value).val = (xor value mone).val
      rw [suffix_int64_not_val, suffix_int64_xor_val]
      congr 1
    rw [encoding, bits_xor_proof value mone index bounds, bits_mone_proof index bounds]
    cases testbit value index <;> rfl
  intro left right
  apply same_bits_eq_proof
  intro index bounds
  rw [complement (or left right) index bounds, bits_or_proof left right index bounds,
    bits_and_proof (not left) (not right) index bounds,
    complement left index bounds, complement right index bounds]
  cases testbit left index <;> cases testbit right index <;> rfl

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Ptrofs

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem translate_cmpu_proof : translate_cmpu := by
  intro comparison left right offset left_bounds right_bounds
  have left_sum : unsigned (add left offset) = zAdd (unsigned left) (unsigned offset) :=
    unsigned_repr_proof _ left_bounds
  have right_sum : unsigned (add right offset) = zAdd (unsigned right) (unsigned offset) :=
    unsigned_repr_proof _ right_bounds
  have equality : eq (add left offset) (add right offset) = eq left right := by
    change decide (unsigned (add left offset) = unsigned (add right offset)) =
      decide (unsigned left = unsigned right)
    rw [left_sum, right_sum]
    simp only [decide_eq_decide]
    constructor
    · intro sums
      apply intOfZ_injective
      have converted := congrArg intOfZ sums
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at converted
      omega
    · intro same
      rw [same]
  have ordered (first second : int)
      (first_sum : unsigned (add first offset) = zAdd (unsigned first) (unsigned offset))
      (second_sum : unsigned (add second offset) = zAdd (unsigned second) (unsigned offset)) :
      ltu (add first offset) (add second offset) = ltu first second := by
    change zltSelect (unsigned (add first offset)) (unsigned (add second offset)) true false =
      zltSelect (unsigned first) (unsigned second) true false
    rw [first_sum, second_sum]
    cases shifted : CompCert4Lean.Lib.Coqlib.zlt
        (zAdd (unsigned first) (unsigned offset)) (zAdd (unsigned second) (unsigned offset)) with
    | left shifted_less =>
        cases original : CompCert4Lean.Lib.Coqlib.zlt (unsigned first) (unsigned second) with
        | left base_less => simp [zltSelect, sumboolSelect, shifted, original]
        | right base_ge =>
            change intOfZ (zAdd (unsigned first) (unsigned offset)) <
              intOfZ (zAdd (unsigned second) (unsigned offset)) at shifted_less
            simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at shifted_less
            change intOfZ (unsigned second) ≤ intOfZ (unsigned first) at base_ge
            omega
    | right shifted_ge =>
        cases original : CompCert4Lean.Lib.Coqlib.zlt (unsigned first) (unsigned second) with
        | left base_less =>
            change intOfZ (zAdd (unsigned second) (unsigned offset)) ≤
              intOfZ (zAdd (unsigned first) (unsigned offset)) at shifted_ge
            simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at shifted_ge
            change intOfZ (unsigned first) < intOfZ (unsigned second) at base_less
            omega
        | right base_ge => simp [zltSelect, sumboolSelect, shifted, original]
  cases comparison <;> simp only [cmpu, equality,
    ordered left right left_sum right_sum, ordered right left right_sum left_sum]

end CompCert4Lean.Lib.Integers.Ptrofs

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_divs_one (value : int) : divs value one = value := by
  change repr (zQuot (signed value) (signed one)) = value
  rw [show signed one = zOne by rfl]
  have quotient : zQuot (signed value) zOne = signed value := by
    apply intOfZ_injective
    simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
    change (intOfZ (signed value)).tdiv 1 = intOfZ (signed value)
    exact _root_.Int.tdiv_one _
  rw [quotient]
  exact repr_signed_proof value

theorem shrx_zero_proof : shrx_zero := by
  intro value wordsize_large
  change divs value (shl one zero) = value
  rw [shl_zero_proof, manual_int64_divs_one]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shrx'_zero_proof : shrx'_zero := by
  intro value
  change divs value (shl' one Int.zero) = value
  rw [show shl' one Int.zero = one by rfl]
  exact manual_int64_divs_one value

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem eqm_mul_2p32_proof : eqm_mul_2p32 := by
  intro left right equivalent
  unfold Int.eqm WordCore.eqm CompCert4Lean.Lib.Zbits.eqmod at equivalent
  obtain ⟨quotient, equality⟩ := equivalent
  unfold eqm WordCore.eqm CompCert4Lean.Lib.Zbits.eqmod
  refine ⟨quotient, ?_⟩
  apply intOfZ_injective
  have converted := congrArg intOfZ equality
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    intOfZ_zOfInt] at converted ⊢
  change intOfZ left = intOfZ quotient * 4294967296 + intOfZ right at converted
  change intOfZ left * 4294967296 =
    intOfZ quotient * 18446744073709551616 + intOfZ right * 4294967296
  rw [converted, _root_.Int.add_mul, _root_.Int.mul_assoc]
  rfl

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shl'_mul_two_p_proof : shl'_mul_two_p := by
  intro value amount
  change repr (zShiftl (unsigned value) (Int.unsigned amount)) =
    repr (zMul (unsigned value) (unsigned (repr (zTwoP (Int.unsigned amount)))))
  have shift : zShiftl (unsigned value) (Int.unsigned amount) =
      zMul (unsigned value) (zTwoP (Int.unsigned amount)) :=
    CompCert4Lean.Lib.Zbits.Zshiftl_mul_two_p (unsigned value) (Int.unsigned amount)
      (Int.unsigned_range_proof amount).1
  rw [shift]
  apply eqm_samerepr_proof
  exact eqm_mult_proof _ _ _ _ (eqm_refl_proof (unsigned value))
    (eqm_unsigned_repr_proof (zTwoP (Int.unsigned amount)))

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shl'_one_two_p_proof : shl'_one_two_p := by
  intro amount
  rw [shl'_mul_two_p_proof, mul_commut_proof, mul_one_proof]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shl'_mul_proof : shl'_mul := by
  intro value amount
  rw [shl'_one_two_p_proof]
  exact shl'_mul_two_p_proof value amount

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_loword_proof : bits_loword := by
  intro value index bounds
  exact (Int.testbit_repr_proof (unsigned value) index bounds).trans
    (pg_int64_testbit_unsigned value index bounds.1).symm

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_unsigned_as_nat (value : int) :
    unsigned value = zOfNat value.val := WordCore.intval_eq_zOfNat_val value

theorem size_range_proof : size_range := by
  intro value
  change zLe zZero (CompCert4Lean.Lib.Zbits.Zsize (unsigned value)) ∧
    zLe (CompCert4Lean.Lib.Zbits.Zsize (unsigned value)) zwordsize
  rw [manual_int64_unsigned_as_nat value]
  cases value_eq : value.val with
  | zero =>
      change (0 : _root_.Int) ≤ 0 ∧ (0 : _root_.Int) ≤ _root_.Int.ofNat wordsize
      exact ⟨by omega, _root_.Int.natCast_nonneg _⟩
  | succ natural =>
      have size_eq : posToNat (PArith.BinPos.Pos.size (posOfNat (natural + 1))) =
          Nat.log2 (natural + 1) + 1 := by
        unfold PArith.BinPos.Pos.size
        rw [posToNat_posOfNat (by omega : 0 < natural + 1)]
        exact posToNat_posOfNat (by omega)
      have upper : natural + 1 < 2 ^ wordsize := by
        have bound := WordCore.val_lt value
        omega
      have logarithm : Nat.log2 (natural + 1) < wordsize :=
        (Nat.log2_lt (Nat.ne_of_gt (by omega : 0 < natural + 1))).mpr upper
      constructor
      · change (0 : _root_.Int) ≤
          _root_.Int.ofNat (posToNat (PArith.BinPos.Pos.size (posOfNat (natural + 1))))
        exact _root_.Int.natCast_nonneg _
      · change _root_.Int.ofNat (posToNat (PArith.BinPos.Pos.size (posOfNat (natural + 1)))) ≤
          _root_.Int.ofNat wordsize
        rw [size_eq]
        exact _root_.Int.ofNat_le.mpr (by omega)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_eqm_sub (first second third fourth : Z)
    (first_equiv : eqm first second) (second_equiv : eqm third fourth) :
    eqm (zSub first third) (zSub second fourth) := by
  have subtraction (left right : Z) : zSub left right = zAdd left (zOpp right) := by
    apply intOfZ_injective
    simp only [zSub, zAdd, zOpp, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add,
      ZArith.BinInt.Z.opp, intOfZ_zOfInt, _root_.Int.sub_eq_add_neg]
  rw [subtraction, subtraction]
  exact eqm_add_proof _ _ _ _ first_equiv
    (CompCert4Lean.Lib.Zbits.eqmod_neg modulus third fourth second_equiv)

theorem mods_divs_proof : mods_divs := by
  intro left right
  change repr (zSub (signed left) (zMul (zQuot (signed left) (signed right)) (signed right))) =
    repr (zSub (unsigned left) (unsigned (mul (divs left right) right)))
  apply eqm_samerepr_proof
  apply manual_int64_eqm_sub
  · exact eqm_signed_unsigned_proof left
  · exact eqm_trans_proof _ _ _
      (eqm_mult_proof _ _ _ _
        (eqm_unsigned_repr_proof (zQuot (signed left) (signed right)))
        (eqm_signed_unsigned_proof right))
      (eqm_unsigned_repr_proof (zMul (unsigned (divs left right)) (unsigned right)))

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem modu_divu_proof : modu_divu := by
  intro left right divisor_nonzero
  have positive : (0 : _root_.Int) < intOfZ (unsigned right) := by
    have lower : (0 : _root_.Int) ≤ intOfZ (unsigned right) :=
      (unsigned_range_proof right).1
    have nonzero : intOfZ (unsigned right) ≠ 0 := by
      intro zero_value
      apply divisor_nonzero
      apply WordCore.ext
      apply intOfZ_injective
      change intOfZ (unsigned right) = 0
      exact zero_value
    omega
  have remainder : zMod (unsigned left) (unsigned right) =
      zSub (unsigned left) (zMul (zDiv (unsigned left) (unsigned right)) (unsigned right)) := by
    apply intOfZ_injective
    have identity := congrArg intOfZ
      (CompCert4Lean.Lib.Coqlib.Z_div_mod_eq (unsigned left) (unsigned right) positive)
    simp only [zSub, zMul, zAdd, zDiv, zMod, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.mul,
      ZArith.BinInt.Z.add, intOfZ_zOfInt, _root_.Int.mul_comm] at identity ⊢
    omega
  change repr (zMod (unsigned left) (unsigned right)) =
    repr (zSub (unsigned left) (unsigned (mul (divu left right) right)))
  rw [remainder]
  apply eqm_samerepr_proof
  apply manual_int64_eqm_sub
  · exact eqm_refl_proof (unsigned left)
  · exact eqm_trans_proof _ _ _
      (eqm_mult_proof _ _ _ _
        (eqm_unsigned_repr_proof (zDiv (unsigned left) (unsigned right)))
        (eqm_refl_proof (unsigned right)))
      (eqm_unsigned_repr_proof (zMul (unsigned (divu left right)) (unsigned right)))

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_ltu_wordsize (value : int)
    (less : ltu value iwordsize = true) : value.val < wordsize := by
  have bound := (ltu_inv_proof value iwordsize less).2
  change ZArith.BinInt.Z.lt value.intval iwordsize.intval at bound
  rw [WordCore.intval_eq_zOfNat_val value,
    WordCore.intval_eq_zOfNat_val iwordsize] at bound
  have size_value : iwordsize.val = wordsize := rfl
  rw [size_value] at bound
  change intOfZ (zOfNat value.val) < intOfZ (zOfNat wordsize) at bound
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at bound
  exact _root_.Int.ofNat_lt.mp bound

private theorem manual_int64_shru_val (value amount : int) :
    (shru value amount).val = value.val / 2 ^ amount.val := by
  unfold shru WordCore.shru
  change (WordCore.repr wordsize
    (ZArith.BinInt.Z.shiftr value.intval amount.intval)).val = _
  rw [WordCore.intval_eq_zOfNat_val value, WordCore.intval_eq_zOfNat_val amount]
  have shifted : ZArith.BinInt.Z.shiftr (zOfNat value.val) (zOfNat amount.val) =
      zOfNat (value.val / 2 ^ amount.val) := by
    unfold ZArith.BinInt.Z.shiftr
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      _root_.Int.ofNat_eq_natCast, _root_.Int.natCast_nonneg, ↓reduceIte,
      _root_.Int.toNat_natCast, _root_.Int.natCast_pow]
    exact congrArg zOfInt _root_.Int.ofNat_ediv_ofNat
  rw [shifted, WordCore.val_repr_residue]
  have encoded : zOfNat (value.val / 2 ^ amount.val) =
      zOfInt (_root_.Int.ofNat (value.val / 2 ^ amount.val)) := by rfl
  rw [encoded, WordCore.residue_zOfNat]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self value.val _) (WordCore.val_lt value))

theorem shru_shru_proof : shru_shru := by
  intro value first second first_lt second_lt sum_lt
  have first_bound := manual_int64_ltu_wordsize first first_lt
  have second_bound := manual_int64_ltu_wordsize second second_lt
  have sum_bound : first.val + second.val < 2 ^ wordsize := by
    change first.val < 64 at first_bound
    change second.val < 64 at second_bound
    change first.val + second.val < 18446744073709551616
    omega
  apply WordCore.ext_of_val_eq
  rw [manual_int64_shru_val, manual_int64_shru_val, manual_int64_shru_val]
  change value.val / 2 ^ first.val / 2 ^ second.val =
    value.val / 2 ^ (WordCore.add first second).val
  rw [WordCore.add_val, Nat.mod_eq_of_lt sum_bound,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_shl_val (value amount : int) :
    (shl value amount).val = (value.val * 2 ^ amount.val) % (2 ^ wordsize) := by
  change (WordCore.repr wordsize
    (zShiftl (unsigned value) (unsigned amount))).val = _
  rw [manual_int64_unsigned_as_nat value, manual_int64_unsigned_as_nat amount]
  have shifted : zShiftl (zOfNat value.val) (zOfNat amount.val) =
      zOfNat (value.val * 2 ^ amount.val) := by
    unfold zShiftl ZArith.BinInt.Z.shiftl
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      _root_.Int.ofNat_eq_natCast, _root_.Int.natCast_nonneg, ↓reduceIte]
    rw [_root_.Int.natCast_mul, _root_.Int.natCast_pow]
    rfl
  rw [shifted, WordCore.val_repr_residue]
  have encoded : zOfNat (value.val * 2 ^ amount.val) =
      zOfInt (_root_.Int.ofNat (value.val * 2 ^ amount.val)) := by rfl
  rw [encoded, WordCore.residue_zOfNat]

theorem shl_shl_proof : shl_shl := by
  intro value first second first_lt second_lt sum_lt
  have first_bound := manual_int64_ltu_wordsize first first_lt
  have second_bound := manual_int64_ltu_wordsize second second_lt
  have sum_bound : first.val + second.val < 2 ^ wordsize := by
    change first.val < 64 at first_bound
    change second.val < 64 at second_bound
    change first.val + second.val < 18446744073709551616
    omega
  apply WordCore.ext_of_val_eq
  rw [manual_int64_shl_val, manual_int64_shl_val, manual_int64_shl_val]
  change ((value.val * 2 ^ first.val) % (2 ^ wordsize) * 2 ^ second.val) %
      (2 ^ wordsize) =
    (value.val * 2 ^ (WordCore.add first second).val) % (2 ^ wordsize)
  rw [WordCore.add_val, Nat.mod_eq_of_lt sum_bound, Nat.pow_add, ← Nat.mul_assoc]
  exact Nat.mod_mul_mod _ _ _

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_bits_shl_nat (value amount : int) (index : Nat)
    (inRange : index < wordsize) :
    testbit (shl value amount) (zOfNat index) =
      zltSelect (zOfNat index) (unsigned amount) false
        (testbit value (zSub (zOfNat index) (unsigned amount))) := by
  have amount_nat : unsigned amount = zOfNat amount.val :=
    manual_int64_unsigned_as_nat amount
  rw [suffix_int64_testbit_nat, manual_int64_shl_val, Nat.testBit_mod_two_pow]
  simp only [inRange, decide_true]
  rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt (zOfNat index) (unsigned amount) with
  | left less =>
      have bound : index < amount.val := by
        rw [amount_nat] at less
        change intOfZ (zOfNat index) < intOfZ (zOfNat amount.val) at less
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at less
        exact _root_.Int.ofNat_lt.mp less
      have not_le : ¬amount.val ≤ index := Nat.not_le.mpr bound
      simp [zltSelect, sumboolSelect, comparison, not_le]
  | right greater =>
      have bound : amount.val ≤ index := by
        rw [amount_nat] at greater
        change intOfZ (zOfNat amount.val) ≤ intOfZ (zOfNat index) at greater
        simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at greater
        exact _root_.Int.ofNat_le.mp greater
      have difference : zSub (zOfNat index) (unsigned amount) =
          zOfNat (index - amount.val) := by
        rw [amount_nat]
        apply intOfZ_injective
        simp only [zSub, zOfNat, ZArith.BinInt.Z.sub, ZArith.BinInt.Z.of_nat,
          intOfZ_zOfInt]
        exact (_root_.Int.ofNat_sub bound).symm
      rw [difference]
      simp [bound]
      have selected : zltSelect (zOfNat index) (unsigned amount) false
          (testbit value (zOfNat (index - amount.val))) =
          testbit value (zOfNat (index - amount.val)) := by
        unfold zltSelect
        rw [comparison]
        rfl
      rw [selected, suffix_int64_testbit_nat]

theorem bits_shl_proof : bits_shl := by
  intro value amount index bounds
  cases index with
  | Zneg position =>
      have lower := bounds.1
      change (0 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat position) at lower
      have positive : (0 : _root_.Int) < _root_.Int.ofNat (posToNat position) :=
        _root_.Int.natCast_pos.mpr (posToNat_positive position)
      omega
  | Z0 =>
      exact manual_int64_bits_shl_nat value amount 0 (by decide)
  | Zpos position =>
      have encoded : zOfNat (posToNat position) = .Zpos position :=
        ZArith.Znat.positive_nat_Z position
      rw [← encoded] at bounds ⊢
      have upper : posToNat position < wordsize := by
        have bound := bounds.2
        change intOfZ (zOfNat (posToNat position)) < intOfZ zwordsize at bound
        simp only [zOfNat, zwordsize, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at bound
        exact _root_.Int.ofNat_lt.mp bound
      exact manual_int64_bits_shl_nat value amount (posToNat position) upper

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_bits_shru_nat (value amount : int) (index : Nat) :
    testbit (shru value amount) (zOfNat index) =
      zltSelect (zAdd (zOfNat index) (unsigned amount)) zwordsize
        (testbit value (zAdd (zOfNat index) (unsigned amount))) false := by
  have sum : zAdd (zOfNat index) (unsigned amount) = zOfNat (index + amount.val) := by
    rw [manual_int64_unsigned_as_nat amount]
    apply intOfZ_injective
    simp only [zAdd, ZArith.BinInt.Z.add, zOfNat, ZArith.BinInt.Z.of_nat,
      intOfZ_zOfInt, _root_.Int.ofNat_eq_natCast, _root_.Int.natCast_add]
  rw [sum, suffix_int64_testbit_nat, manual_int64_shru_val]
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight, Nat.add_comm amount.val index]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt (zOfNat (index + amount.val)) zwordsize with
  | left less =>
      simp only [zltSelect, sumboolSelect, comparison]
      exact (suffix_int64_testbit_nat value (index + amount.val)).symm
  | right greater =>
      simp only [zltSelect, sumboolSelect, comparison]
      apply Nat.testBit_lt_two_pow
      have bound : wordsize ≤ index + amount.val := by
        change intOfZ zwordsize ≤ intOfZ (zOfNat (index + amount.val)) at greater
        simp only [zwordsize, zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at greater
        exact _root_.Int.ofNat_le.mp greater
      exact Nat.lt_of_lt_of_le (WordCore.val_lt value)
        (Nat.pow_le_pow_right Nat.zero_lt_two bound)

theorem bits_shru_proof : bits_shru := by
  intro value amount index bounds
  cases index with
  | Zneg position =>
      have lower := bounds.1
      change (0 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat position) at lower
      have positive : (0 : _root_.Int) < _root_.Int.ofNat (posToNat position) :=
        _root_.Int.natCast_pos.mpr (posToNat_positive position)
      omega
  | Z0 =>
      exact manual_int64_bits_shru_nat value amount 0
  | Zpos position =>
      have encoded : zOfNat (posToNat position) = .Zpos position :=
        ZArith.Znat.positive_nat_Z position
      rw [← encoded] at bounds ⊢
      have upper : posToNat position < wordsize := by
        have bound := bounds.2
        change intOfZ (zOfNat (posToNat position)) < intOfZ zwordsize at bound
        simp only [zOfNat, zwordsize, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at bound
        exact _root_.Int.ofNat_lt.mp bound
      exact manual_int64_bits_shru_nat value amount (posToNat position)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_widen_unsigned (value : Int.int) :
    unsigned (repr (Int.unsigned value)) = Int.unsigned value := by
  apply unsigned_repr_proof
  have bounds := Int.unsigned_range_proof value
  refine ⟨bounds.1, ?_⟩
  have upper := bounds.2
  change intOfZ (Int.unsigned value) < 4294967296 at upper
  change intOfZ (Int.unsigned value) ≤ 18446744073709551615
  omega

theorem bits_shl'_proof : bits_shl' := by
  intro value amount index bounds
  have original := bits_shl_proof value (repr (Int.unsigned amount)) index bounds
  change testbit (repr (zShiftl (unsigned value) (unsigned (repr (Int.unsigned amount))))) index = _ at original
  rw [manual_int64_widen_unsigned] at original
  exact original

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_shru'_proof : bits_shru' := by
  intro value amount index bounds
  have original := bits_shru_proof value (repr (Int.unsigned amount)) index bounds
  change testbit (repr (zShiftr (unsigned value) (unsigned (repr (Int.unsigned amount))))) index = _ at original
  rw [manual_int64_widen_unsigned] at original
  exact original

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_shr'_proof : bits_shr' := by
  intro value amount index bounds
  change testbit (repr (zShiftr (signed value) (Int.unsigned amount))) index = _
  rw [testbit_repr_proof _ _ bounds]
  change ZArith.BinInt.Z.testbit
    (ZArith.BinInt.Z.shiftr (signed value) (Int.unsigned amount)) index = _
  rw [ZArith.BinInt.Z.shiftr_spec (signed value) (Int.unsigned amount) index bounds.1]
  apply bits_signed_proof
  have index_nonnegative : 0 ≤ intOfZ index := bounds.1
  have amount_nonnegative : 0 ≤ intOfZ (Int.unsigned amount) :=
    (Int.unsigned_range_proof amount).1
  change 0 ≤ intOfZ (zAdd index (Int.unsigned amount))
  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_ror_proof : bits_ror := by
  intro value amount index bounds
  have natural (offset : Nat) (inRange : offset < wordsize) :
      testbit (ror value amount) (zOfNat offset) =
        testbit value (zMod (zAdd (zOfNat offset) (unsigned amount)) zwordsize) := by
    rw [pg_suffix_zmod_add_nat]
    exact pg_suffix_ror_testbit_nat value amount offset inRange
  cases index with
  | Zneg position =>
      have lower := bounds.1
      have positive := posToNat_positive position
      change (0 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat position) at lower
      simp only [_root_.Int.ofNat_eq_natCast] at lower
      omega
  | Z0 => exact natural 0 (by decide)
  | Zpos position =>
      have encoded : zOfNat (posToNat position) = .Zpos position :=
        ZArith.Znat.positive_nat_Z position
      rw [← encoded] at bounds ⊢
      have upper := bounds.2
      change intOfZ (zOfNat (posToNat position)) < intOfZ zwordsize at upper
      simp only [zOfNat, zwordsize, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at upper
      exact natural (posToNat position) (_root_.Int.ofNat_lt.mp upper)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_zmod_sub_nat (index : Nat) (amount : int) :
    zMod (zSub (zOfNat index) (unsigned amount)) zwordsize =
      zOfNat ((index + wordsize - (amount.val % wordsize)) % wordsize) := by
  rw [manual_int64_unsigned_as_nat amount]
  apply intOfZ_injective
  simp only [zMod, zSub, zwordsize, zOfNat, ZArith.BinInt.Z.modulo,
    ZArith.BinInt.Z.sub, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change (if (_root_.Int.ofNat wordsize) = 0 then
      _root_.Int.ofNat index - _root_.Int.ofNat amount.val
    else if 0 < _root_.Int.ofNat wordsize then
      (_root_.Int.ofNat index - _root_.Int.ofNat amount.val) % _root_.Int.ofNat wordsize
    else _) = _root_.Int.ofNat ((index + wordsize - (amount.val % wordsize)) % wordsize)
  have remainder_bound : amount.val % wordsize ≤ index + wordsize := by
    have upper : amount.val % wordsize < wordsize := Nat.mod_lt _ (by decide)
    omega
  simp only [show (_root_.Int.ofNat wordsize) ≠ 0 by decide,
    show 0 < _root_.Int.ofNat wordsize by decide, if_false, if_true]
  simp only [_root_.Int.ofNat_eq_natCast, _root_.Int.natCast_emod,
    _root_.Int.natCast_sub remainder_bound, _root_.Int.natCast_add]
  have rearrange : _root_.Int.ofNat index + _root_.Int.ofNat wordsize -
      (_root_.Int.ofNat amount.val % _root_.Int.ofNat wordsize) =
      (_root_.Int.ofNat index - (_root_.Int.ofNat amount.val % _root_.Int.ofNat wordsize)) +
        _root_.Int.ofNat wordsize := by omega
  simp only [_root_.Int.ofNat_eq_natCast] at rearrange
  rw [rearrange, _root_.Int.add_emod_right, _root_.Int.sub_emod_emod]

theorem bits_rol_proof : bits_rol := by
  intro value amount index bounds
  have natural (offset : Nat) (inRange : offset < wordsize) :
      testbit (rol value amount) (zOfNat offset) =
        testbit value (zMod (zSub (zOfNat offset) (unsigned amount)) zwordsize) := by
    rw [manual_int64_zmod_sub_nat]
    exact pg_suffix_rol_testbit_nat value amount offset inRange
  cases index with
  | Zneg position =>
      have lower := bounds.1
      have positive := posToNat_positive position
      change (0 : _root_.Int) ≤ -_root_.Int.ofNat (posToNat position) at lower
      simp only [_root_.Int.ofNat_eq_natCast] at lower
      omega
  | Z0 => exact natural 0 (by decide)
  | Zpos position =>
      have encoded : zOfNat (posToNat position) = .Zpos position :=
        ZArith.Znat.positive_nat_Z position
      rw [← encoded] at bounds ⊢
      have upper := bounds.2
      change intOfZ (zOfNat (posToNat position)) < intOfZ zwordsize at upper
      simp only [zOfNat, zwordsize, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at upper
      exact natural (posToNat position) (_root_.Int.ofNat_lt.mp upper)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_size_2_proof : bits_size_2 := by
  intro value index above
  have natural (offset : Nat) (bound : zLe (size value) (zOfNat offset)) :
      testbit value (zOfNat offset) = false := by
    rw [suffix_int64_testbit_nat]
    cases value_eq : value.val with
    | zero => simp
    | succ number =>
        have logarithm : Nat.log2 (number + 1) + 1 ≤ offset := by
          change intOfZ (CompCert4Lean.Lib.Zbits.Zsize (unsigned value)) ≤
            intOfZ (zOfNat offset) at bound
          rw [manual_int64_unsigned_as_nat value, value_eq] at bound
          simp only [CompCert4Lean.Lib.Zbits.Zsize, ZArith.BinInt.Z.of_nat,
            intOfZ_zOfInt] at bound
          change _root_.Int.ofNat (posToNat (PArith.BinPos.Pos.size (posOfNat (number + 1)))) ≤
            _root_.Int.ofNat offset at bound
          have size_eq : posToNat (PArith.BinPos.Pos.size (posOfNat (number + 1))) =
              Nat.log2 (number + 1) + 1 := by
            unfold PArith.BinPos.Pos.size
            rw [posToNat_posOfNat (by omega : 0 < number + 1)]
            exact posToNat_posOfNat (by omega)
          rw [size_eq] at bound
          exact _root_.Int.ofNat_le.mp bound
        apply Nat.testBit_lt_two_pow
        apply (Nat.log2_lt (Nat.ne_of_gt (by omega : 0 < number + 1))).mp
        omega
  cases index with
  | Zneg position => rfl
  | Z0 => exact natural 0 above
  | Zpos position =>
      have encoded : zOfNat (posToNat position) = .Zpos position :=
        ZArith.Znat.positive_nat_Z position
      rw [← encoded] at above ⊢
      exact natural (posToNat position) above

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_zero_ext_proof : bits_zero_ext := by
  intro width value index nonnegative
  by_cases within : zLt index zwordsize
  · change testbit (repr (CompCert4Lean.Lib.Zbits.Zzero_ext width (unsigned value))) index = _
    rw [testbit_repr_proof _ _ ⟨nonnegative, within⟩]
    have specification :
        zTestbit (CompCert4Lean.Lib.Zbits.Zzero_ext width (unsigned value)) index =
          zltSelect index width (zTestbit (unsigned value) index) false :=
      CompCert4Lean.Lib.Zbits.Zzero_ext_spec width (unsigned value) index nonnegative
    rw [specification, ← pg_int64_testbit_unsigned value index nonnegative]
  · have above : zLe zwordsize index := _root_.Int.le_of_not_gt within
    rw [bits_above_proof _ _ above, bits_above_proof _ _ above]
    cases comparison : CompCert4Lean.Lib.Coqlib.zlt index width <;>
      simp [zltSelect, sumboolSelect, comparison]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem bits_hiword_proof : bits_hiword := by
  intro value index bounds
  change Int.testbit (Int.repr (unsigned (shru value (repr Int.zwordsize)))) index = _
  rw [Int.testbit_repr_proof _ _ bounds,
    ← pg_int64_testbit_unsigned (shru value (repr Int.zwordsize)) index bounds.1]
  have within : zLt index zwordsize := by
    have upper := bounds.2
    change intOfZ index < 32 at upper
    change intOfZ index < 64
    omega
  rw [bits_shru_proof _ _ index ⟨bounds.1, within⟩]
  have shift_amount : unsigned (repr Int.zwordsize) = Int.zwordsize := by rfl
  rw [shift_amount]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt (zAdd index Int.zwordsize) zwordsize with
  | left less => simp only [zltSelect, sumboolSelect, comparison]
  | right greater =>
      have upper := bounds.2
      change intOfZ index < 32 at upper
      change 64 ≤ intOfZ (zAdd index Int.zwordsize) at greater
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at greater
      change 64 ≤ intOfZ index + 32 at greater
      omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_widen_bits (value : Int.int) (index : Z)
    (nonnegative : zLe zZero index) :
    testbit (repr (Int.unsigned value)) index = Int.testbit value index := by
  rw [pg_int64_testbit_unsigned _ _ nonnegative, manual_int64_widen_unsigned,
    ← Int.suffix_testbit_unsigned value index nonnegative]

theorem bits_ofwords_proof : bits_ofwords := by
  intro high low index bounds
  unfold ofwords
  rw [bits_or_proof _ _ index bounds, bits_shl_proof _ _ index bounds]
  have shift_amount : unsigned (repr Int.zwordsize) = Int.zwordsize := by rfl
  rw [shift_amount, manual_int64_widen_bits low index bounds.1]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt index Int.zwordsize with
  | left less => simp only [zltSelect, sumboolSelect, comparison, Bool.false_or]
  | right greater =>
      have difference_nonnegative : zLe zZero (zSub index Int.zwordsize) := by
        change intOfZ Int.zwordsize ≤ intOfZ index at greater
        change 0 ≤ intOfZ (zSub index Int.zwordsize)
        simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        omega
      simp only [zltSelect, sumboolSelect, comparison]
      rw [manual_int64_widen_bits high _ difference_nonnegative,
        Int.bits_above_proof low index greater, Bool.or_false]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem decompose_bitwise_binop_proof : decompose_bitwise_binop := by
  intro operation wide narrow high_left low_left high_right low_right wide_bits narrow_bits
  apply same_bits_eq_proof
  intro index bounds
  rw [wide_bits _ _ index bounds, bits_ofwords_proof _ _ index bounds,
    bits_ofwords_proof _ _ index bounds, bits_ofwords_proof _ _ index bounds]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt index Int.zwordsize with
  | left less =>
      simp only [zltSelect, sumboolSelect, comparison]
      exact (narrow_bits low_left low_right index ⟨bounds.1, less⟩).symm
  | right greater =>
      simp only [zltSelect, sumboolSelect, comparison]
      apply Eq.symm
      apply narrow_bits
      have upper := bounds.2
      change intOfZ index < 64 at upper
      change 32 ≤ intOfZ index at greater
      change 0 ≤ intOfZ (zSub index Int.zwordsize) ∧
        intOfZ (zSub index Int.zwordsize) < 32
      simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      change 0 ≤ intOfZ index - 32 ∧ intOfZ index - 32 < 32
      omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem decompose_and_proof : decompose_and := by
  intro high_left low_left high_right low_right
  exact decompose_bitwise_binop_proof Bool.and and Int.and
    high_left low_left high_right low_right bits_and_proof Int.bits_and_proof

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem decompose_or_proof : decompose_or := by
  intro high_left low_left high_right low_right
  exact decompose_bitwise_binop_proof Bool.or or Int.or
    high_left low_left high_right low_right bits_or_proof Int.bits_or_proof

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem decompose_xor_proof : decompose_xor := by
  intro high_left low_left high_right low_right
  exact decompose_bitwise_binop_proof Bool.xor xor Int.xor
    high_left low_left high_right low_right bits_xor_proof Int.bits_xor_proof

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem lo_ofwords_proof : lo_ofwords := by
  intro high low
  apply Int.same_bits_eq_proof
  intro index bounds
  rw [bits_loword_proof _ _ bounds]
  have wider : zLe zZero index ∧ zLt index zwordsize := by
    refine ⟨bounds.1, ?_⟩
    have upper := bounds.2
    change intOfZ index < 32 at upper
    change intOfZ index < 64
    omega
  rw [bits_ofwords_proof high low index wider]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt index Int.zwordsize with
  | left less => simp only [zltSelect, sumboolSelect, comparison]
  | right greater => exact (_root_.Int.not_lt_of_ge greater bounds.2).elim

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem hi_ofwords_proof : hi_ofwords := by
  intro high low
  apply Int.same_bits_eq_proof
  intro index bounds
  rw [bits_hiword_proof _ _ bounds]
  have offset_bounds : zLe zZero (zAdd index Int.zwordsize) ∧
      zLt (zAdd index Int.zwordsize) zwordsize := by
    change 0 ≤ intOfZ index ∧ intOfZ index < 32 at bounds
    change 0 ≤ intOfZ (zAdd index Int.zwordsize) ∧
      intOfZ (zAdd index Int.zwordsize) < 64
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change 0 ≤ intOfZ index + 32 ∧ intOfZ index + 32 < 64
    omega
  rw [bits_ofwords_proof high low _ offset_bounds]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt (zAdd index Int.zwordsize) Int.zwordsize with
  | left less =>
      have lower : 0 ≤ intOfZ index := bounds.1
      change intOfZ (zAdd index Int.zwordsize) < 32 at less
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at less
      change intOfZ index + 32 < 32 at less
      omega
  | right greater =>
      simp only [zltSelect, sumboolSelect, comparison]
      congr 1
      apply intOfZ_injective
      simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ofwords_recompose_proof : ofwords_recompose := by
  intro value
  apply same_bits_eq_proof
  intro index bounds
  rw [bits_ofwords_proof _ _ index bounds]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt index Int.zwordsize with
  | left less =>
      simp only [zltSelect, sumboolSelect, comparison]
      exact bits_loword_proof value index ⟨bounds.1, less⟩
  | right greater =>
      simp only [zltSelect, sumboolSelect, comparison]
      have difference_bounds : zLe zZero (zSub index Int.zwordsize) ∧
          zLt (zSub index Int.zwordsize) Int.zwordsize := by
        have upper := bounds.2
        change intOfZ index < 64 at upper
        change 32 ≤ intOfZ index at greater
        change 0 ≤ intOfZ (zSub index Int.zwordsize) ∧
          intOfZ (zSub index Int.zwordsize) < 32
        simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
        change 0 ≤ intOfZ index - 32 ∧ intOfZ index - 32 < 32
        omega
      rw [bits_hiword_proof value _ difference_bounds]
      congr 1
      apply intOfZ_injective
      simp only [zAdd, zSub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_small_int_unsigned (number : Z)
    (bounds : zLe zZero number ∧ zLt number zwordsize) :
    Int.unsigned (Int.repr number) = number := by
  apply Int.unsigned_repr_proof_api
  refine ⟨bounds.1, ?_⟩
  have upper := bounds.2
  change intOfZ number < 64 at upper
  change intOfZ number ≤ 4294967295
  omega

private theorem manual_int64_small_int_ltu (value : Int.int)
    (bounds : zLe zZero (Int.unsigned value) ∧ zLt (Int.unsigned value) zwordsize) :
    Int.ltu value iwordsize' = true := by
  change zltSelect (Int.unsigned value) (Int.unsigned iwordsize') true false = true
  have size_unsigned : Int.unsigned iwordsize' = zwordsize := by rfl
  rw [size_unsigned]
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt (Int.unsigned value) zwordsize with
  | left less => simp only [zltSelect, sumboolSelect, comparison]
  | right greater => exact (_root_.Int.not_lt_of_ge greater bounds.2).elim

theorem one_bits'_range_proof : one_bits'_range := by
  intro value index member
  unfold one_bits' at member
  obtain ⟨exponent, exponent_member, rfl⟩ := List.mem_map.mp member
  have bounds := CompCert4Lean.Lib.Zbits.Z_one_bits_range wordsize (unsigned value) exponent exponent_member
  apply manual_int64_small_int_ltu
  rw [manual_int64_small_int_unsigned exponent bounds]
  exact bounds

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_power2_singleton (value : int) (logarithm : Int.int)
    (found : is_power2' value = some logarithm) :
    ∃ exponent : Z,
      CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned value) zZero = [exponent] ∧
      logarithm = Int.repr exponent ∧
      zLe zZero exponent ∧ zLt exponent zwordsize := by
  cases bits_eq : CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned value) zZero with
  | nil => simp [is_power2', bits_eq] at found
  | cons exponent rest =>
      cases rest with
      | nil =>
          simp only [is_power2', bits_eq, Option.some.injEq] at found
          refine ⟨exponent, rfl, found.symm, ?_⟩
          exact CompCert4Lean.Lib.Zbits.Z_one_bits_range wordsize (unsigned value) exponent
            (by rw [bits_eq]; simp)
      | cons next remaining => simp [is_power2', bits_eq] at found

theorem is_power2'_rng_proof : is_power2'_rng := by
  intro value logarithm found
  obtain ⟨exponent, singleton, encoding, bounds⟩ := manual_int64_power2_singleton value logarithm found
  rw [encoding, manual_int64_small_int_unsigned exponent bounds]
  exact bounds

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem is_power2'_range_proof : is_power2'_range := by
  intro value logarithm found
  exact manual_int64_small_int_ltu logarithm (is_power2'_rng_proof value logarithm found)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem is_power2'_correct_proof : is_power2'_correct := by
  intro value logarithm found
  obtain ⟨exponent, singleton, encoding, bounds⟩ := manual_int64_power2_singleton value logarithm found
  have expansion := CompCert4Lean.Lib.Zbits.Z_one_bits_powerserie wordsize (unsigned value)
    (unsigned_range_proof value)
  rw [singleton] at expansion
  rw [encoding, manual_int64_small_int_unsigned exponent bounds]
  have single_value : CompCert4Lean.Lib.Zbits.powerserie [exponent] = zTwoP exponent := by
    change zAdd (zTwoP exponent) zZero = zTwoP exponent
    exact ZArith.BinInt.Z.add_0_r _
  exact expansion.trans single_value

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem mul_pow2'_proof : mul_pow2' := by
  intro value power logarithm found
  change repr (zMul (unsigned value) (unsigned power)) = _
  rw [is_power2'_correct_proof power logarithm found]
  have shifted : zShiftl (unsigned value) (Int.unsigned logarithm) =
      zMul (unsigned value) (zTwoP (Int.unsigned logarithm)) :=
    CompCert4Lean.Lib.Zbits.Zshiftl_mul_two_p (unsigned value) (Int.unsigned logarithm)
      (Int.unsigned_range_proof logarithm).1
  exact congrArg repr shifted.symm

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem divu_pow2'_proof : divu_pow2' := by
  intro value power logarithm found
  change repr (zDiv (unsigned value) (unsigned power)) = _
  rw [is_power2'_correct_proof power logarithm found]
  have shifted : zShiftr (unsigned value) (Int.unsigned logarithm) =
      zDiv (unsigned value) (zTwoP (Int.unsigned logarithm)) :=
    CompCert4Lean.Lib.Zbits.Zshiftr_div_two_p (unsigned value) (Int.unsigned logarithm)
      (Int.unsigned_range_proof logarithm).1
  exact congrArg repr shifted.symm

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem one_bits'_decomp_proof : one_bits'_decomp := by
  intro value
  have fold : ∀ (positions : List Z),
      (∀ exponent ∈ positions, zLe zZero exponent ∧ zLt exponent zwordsize) →
      repr (CompCert4Lean.Lib.Zbits.powerserie positions) =
        int_of_one_bits' (positions.map Int.repr) := by
    intro positions all_bounds
    induction positions with
    | nil => rfl
    | cons exponent remaining induction =>
        have bounds := all_bounds exponent (by simp)
        have remaining_bounds : ∀ next ∈ remaining, zLe zZero next ∧ zLt next zwordsize := by
          intro next member
          exact all_bounds next (by simp [member])
        have rest := induction remaining_bounds
        simp only [CompCert4Lean.Lib.Zbits.powerserie, List.map_cons, int_of_one_bits']
        rw [shl'_one_two_p_proof, manual_int64_small_int_unsigned exponent bounds, ← rest]
        change repr (zAdd (zTwoP exponent) (CompCert4Lean.Lib.Zbits.powerserie remaining)) =
          repr (zAdd (unsigned (repr (zTwoP exponent)))
            (unsigned (repr (CompCert4Lean.Lib.Zbits.powerserie remaining))))
        apply eqm_samerepr_proof
        exact eqm_add_proof _ _ _ _ (eqm_unsigned_repr_proof _) (eqm_unsigned_repr_proof _)
  have expansion := CompCert4Lean.Lib.Zbits.Z_one_bits_powerserie wordsize (unsigned value)
    (unsigned_range_proof value)
  change value = int_of_one_bits'
    ((CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned value) zZero).map Int.repr)
  calc
    value = repr (unsigned value) := (repr_unsigned_proof value).symm
    _ = repr (CompCert4Lean.Lib.Zbits.powerserie
        (CompCert4Lean.Lib.Zbits.Z_one_bits wordsize (unsigned value) zZero)) := congrArg repr expansion
    _ = _ := fold _ (fun exponent member =>
      CompCert4Lean.Lib.Zbits.Z_one_bits_range wordsize (unsigned value) exponent member)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_widen_val (value : Int.int) :
    (repr (Int.unsigned value)).val = value.val := by
  exact congrArg zToNat (manual_int64_widen_unsigned value)

private theorem manual_int64_ofwords_val (high low : Int.int) :
    (ofwords high low).val = high.val * 4294967296 + low.val := by
  unfold ofwords
  rw [manual_int64_or_val, manual_int64_shl_val,
    manual_int64_widen_val, manual_int64_widen_val]
  have shift_value : (repr Int.zwordsize).val = 32 := by rfl
  rw [shift_value]
  have high_bound := WordCore.val_lt high
  have low_bound := WordCore.val_lt low
  change high.val < 4294967296 at high_bound
  change low.val < 4294967296 at low_bound
  have shift_bound : high.val * 2 ^ 32 < 2 ^ wordsize := by
    change high.val * 4294967296 < 18446744073709551616
    omega
  rw [Nat.mod_eq_of_lt shift_bound, Nat.lor_eq]
  have disjoint := Nat.two_pow_add_eq_or_of_lt (i := 32) low_bound high.val
  simpa [Nat.mul_comm] using disjoint.symm

private theorem manual_int64_ofwords_encoding (high low : Int.int) :
    zAdd (zMul (Int.unsigned high) (zTwoP (zOfNat 32))) (Int.unsigned low) =
      zOfNat (high.val * 4294967296 + low.val) := by
  apply intOfZ_injective
  rw [show Int.unsigned high = zOfNat high.val from WordCore.intval_eq_zOfNat_val high,
    show Int.unsigned low = zOfNat low.val from WordCore.intval_eq_zOfNat_val low]
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
    zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  change _root_.Int.ofNat high.val * 4294967296 + _root_.Int.ofNat low.val =
    _root_.Int.ofNat (high.val * 4294967296 + low.val)
  simp only [_root_.Int.ofNat_eq_natCast, _root_.Int.natCast_add, _root_.Int.natCast_mul]
  rfl

theorem ofwords_add'_proof : ofwords_add' := by
  intro low high
  rw [manual_int64_unsigned_as_nat, manual_int64_ofwords_val,
    manual_int64_ofwords_encoding]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ofwords_add_proof : ofwords_add := by
  intro low high
  rw [← ofwords_add'_proof low high, repr_unsigned_proof]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem ofwords_add''_proof : ofwords_add'' := by
  intro low high
  have bounds : zLe min_signed
        (zAdd (zMul (Int.signed high) (zTwoP (zOfNat 32))) (Int.unsigned low)) ∧
      zLe (zAdd (zMul (Int.signed high) (zTwoP (zOfNat 32))) (Int.unsigned low)) max_signed := by
    have signed_bounds := Int.signed_range_proof high
    have low_bounds := Int.unsigned_range_proof low
    change (-2147483648 : _root_.Int) ≤ intOfZ (Int.signed high) ∧
      intOfZ (Int.signed high) ≤ 2147483647 at signed_bounds
    change 0 ≤ intOfZ (Int.unsigned low) ∧ intOfZ (Int.unsigned low) < 4294967296 at low_bounds
    change (-9223372036854775808 : _root_.Int) ≤
        intOfZ (zAdd (zMul (Int.signed high) (zTwoP (zOfNat 32))) (Int.unsigned low)) ∧
      intOfZ (zAdd (zMul (Int.signed high) (zTwoP (zOfNat 32))) (Int.unsigned low)) ≤
        9223372036854775807
    simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    change (-9223372036854775808 : _root_.Int) ≤
        intOfZ (Int.signed high) * 4294967296 + intOfZ (Int.unsigned low) ∧
      intOfZ (Int.signed high) * 4294967296 + intOfZ (Int.unsigned low) ≤ 9223372036854775807
    omega
  have equivalent := eqm_add_proof _ _ _ _
    (eqm_mul_2p32_proof (Int.signed high) (Int.unsigned high) (Int.eqm_signed_unsigned_proof high))
    (eqm_refl_proof (Int.unsigned low))
  rw [ofwords_add_proof low high, ← eqm_samerepr_proof _ _ equivalent]
  exact signed_repr_proof _ bounds

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem lt_sub_overflow_proof : lt_sub_overflow := CompCert4Lean.X86.Asmgenproof1.CompCert4Lean.X86.Asmgenproof1.int_lt_sub_overflow_aux

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_zlt_bool (left right : Z) :
    zltSelect left right true false = decide (intOfZ left < intOfZ right) := by
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt left right with
  | left less =>
      have bound : intOfZ left < intOfZ right := less
      simp [zltSelect, sumboolSelect, comparison, bound]
  | right greater =>
      have bound : ¬intOfZ left < intOfZ right := _root_.Int.not_lt_of_ge greater
      simp [zltSelect, sumboolSelect, comparison, bound]

private theorem manual_int64_eq_unsigned (left right : Int.int) :
    Int.eq left right =
      decide (intOfZ (Int.unsigned left) = intOfZ (Int.unsigned right)) := by
  change decide (left.intval = right.intval) =
    decide (intOfZ left.intval = intOfZ right.intval)
  apply decide_eq_decide.mpr
  exact ⟨congrArg intOfZ, fun equality => intOfZ_injective equality⟩

private theorem manual_int64_compare_halves
    (high_left high_right low_left low_right : _root_.Int)
    (left_bounds : 0 ≤ low_left ∧ low_left < 4294967296)
    (right_bounds : 0 ≤ low_right ∧ low_right < 4294967296) :
    decide (high_left * 4294967296 + low_left < high_right * 4294967296 + low_right) =
      if decide (high_left = high_right) then decide (low_left < low_right)
      else decide (high_left < high_right) := by
  by_cases equal : high_left = high_right
  · simp only [equal, decide_true, ↓reduceIte]
    apply decide_eq_decide.mpr
    omega
  · simp only [equal, decide_false, Bool.false_eq_true, ↓reduceIte]
    apply decide_eq_decide.mpr
    omega

theorem decompose_ltu_proof : decompose_ltu := by
  intro high_left low_left high_right low_right
  change zltSelect (unsigned (ofwords high_left low_left))
      (unsigned (ofwords high_right low_right)) true false =
    if Int.eq high_left high_right then
      zltSelect (Int.unsigned low_left) (Int.unsigned low_right) true false
    else zltSelect (Int.unsigned high_left) (Int.unsigned high_right) true false
  rw [ofwords_add'_proof low_left high_left, ofwords_add'_proof low_right high_right]
  rw [manual_int64_zlt_bool, manual_int64_zlt_bool, manual_int64_zlt_bool,
    manual_int64_eq_unsigned]
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  change decide (intOfZ (Int.unsigned high_left) * 4294967296 + intOfZ (Int.unsigned low_left) <
      intOfZ (Int.unsigned high_right) * 4294967296 + intOfZ (Int.unsigned low_right)) = _
  exact manual_int64_compare_halves _ _ _ _
    (Int.unsigned_range_proof low_left) (Int.unsigned_range_proof low_right)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_eq_signed (left right : Int.int) :
    Int.eq left right =
      decide (intOfZ (Int.signed left) = intOfZ (Int.signed right)) := by
  change decide (left.intval = right.intval) = _
  apply decide_eq_decide.mpr
  constructor
  · intro equality
    have same : left = right := WordCore.ext equality
    rw [same]
  · intro equality
    have same : left = right := by
      calc
        left = Int.repr (Int.signed left) := (Int.repr_signed_proof left).symm
        _ = Int.repr (Int.signed right) := congrArg Int.repr (intOfZ_injective equality)
        _ = right := Int.repr_signed_proof right
    exact congrArg (fun value : Int.int => value.intval) same

theorem decompose_lt_proof : decompose_lt := by
  intro high_left low_left high_right low_right
  change zltSelect (signed (ofwords high_left low_left))
      (signed (ofwords high_right low_right)) true false =
    if Int.eq high_left high_right then
      zltSelect (Int.unsigned low_left) (Int.unsigned low_right) true false
    else zltSelect (Int.signed high_left) (Int.signed high_right) true false
  rw [ofwords_add''_proof low_left high_left, ofwords_add''_proof low_right high_right]
  rw [manual_int64_zlt_bool, manual_int64_zlt_bool, manual_int64_zlt_bool,
    manual_int64_eq_signed]
  simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  change decide (intOfZ (Int.signed high_left) * 4294967296 + intOfZ (Int.unsigned low_left) <
      intOfZ (Int.signed high_right) * 4294967296 + intOfZ (Int.unsigned low_right)) = _
  exact manual_int64_compare_halves _ _ _ _
    (Int.unsigned_range_proof low_left) (Int.unsigned_range_proof low_right)

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem decompose_leu_proof : decompose_leu := by
  intro high_left low_left high_right low_right
  rw [decompose_ltu_proof]
  have swap : Int.eq high_right high_left = Int.eq high_left high_right := by
    simp [Int.eq, WordCore.eq, eq_comm]
  rw [swap]
  by_cases same : Int.eq high_left high_right = true
  · simp [same]
  · simp only [same, Bool.false_eq_true, ↓reduceIte]
    have law := Int.not_ltu_proof high_left high_right
    cases left_result : Int.ltu high_left high_right <;>
      cases right_result : Int.ltu high_right high_left <;> simp_all

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem decompose_le_proof : decompose_le := by
  intro high_left low_left high_right low_right
  rw [decompose_lt_proof]
  have swap : Int.eq high_right high_left = Int.eq high_left high_right := by
    simp [Int.eq, WordCore.eq, eq_comm]
  rw [swap]
  by_cases same : Int.eq high_left high_right = true
  · simp [same]
  · simp only [same, Bool.false_eq_true, ↓reduceIte]
    have law := Int.not_lt_proof high_left high_right
    cases left_result : Int.lt high_left high_right <;>
      cases right_result : Int.lt high_right high_left <;> simp_all

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_small_add_unsigned (left right : Int.int)
    (left_lt : Int.ltu left iwordsize' = true)
    (right_lt : Int.ltu right iwordsize' = true) :
    Int.unsigned (Int.add left right) = zAdd (Int.unsigned left) (Int.unsigned right) := by
  have left_bounds := Int.ltu_inv_proof left iwordsize' left_lt
  have right_bounds := Int.ltu_inv_proof right iwordsize' right_lt
  have left_lower : 0 ≤ intOfZ (Int.unsigned left) := left_bounds.1
  have right_lower : 0 ≤ intOfZ (Int.unsigned right) := right_bounds.1
  have left_upper : intOfZ (Int.unsigned left) < 64 := left_bounds.2
  have right_upper : intOfZ (Int.unsigned right) < 64 := right_bounds.2
  apply Int.unsigned_repr_proof_api
  change 0 ≤ intOfZ (zAdd (Int.unsigned left) (Int.unsigned right)) ∧
    intOfZ (zAdd (Int.unsigned left) (Int.unsigned right)) ≤ 4294967295
  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  omega

private theorem manual_int64_widen_ltu (value : Int.int)
    (less : Int.ltu value iwordsize' = true) :
    ltu (repr (Int.unsigned value)) iwordsize = true := by
  change zltSelect (unsigned (repr (Int.unsigned value))) zwordsize true false = true
  rw [manual_int64_widen_unsigned]
  exact less

private theorem manual_int64_widen_add (left right : Int.int)
    (left_lt : Int.ltu left iwordsize' = true)
    (right_lt : Int.ltu right iwordsize' = true) :
    add (repr (Int.unsigned left)) (repr (Int.unsigned right)) =
      repr (Int.unsigned (Int.add left right)) := by
  change repr (zAdd (unsigned (repr (Int.unsigned left)))
    (unsigned (repr (Int.unsigned right)))) = _
  rw [manual_int64_widen_unsigned, manual_int64_widen_unsigned,
    manual_int64_small_add_unsigned left right left_lt right_lt]

theorem int_ltu_2_inv_proof : int_ltu_2_inv := by
  intro left right left_lt right_lt sum_bound
  dsimp only
  have addition := manual_int64_widen_add left right left_lt right_lt
  refine ⟨(manual_int64_widen_unsigned left).symm,
    (manual_int64_widen_unsigned right).symm,
    manual_int64_widen_ltu left left_lt, manual_int64_widen_ltu right right_lt, ?_,
    addition⟩
  rw [addition, manual_int64_widen_unsigned]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_shl_prime (value : int) (amount : Int.int) :
    shl' value amount = shl value (repr (Int.unsigned amount)) := by
  change repr (zShiftl (unsigned value) (Int.unsigned amount)) =
    repr (zShiftl (unsigned value) (unsigned (repr (Int.unsigned amount))))
  rw [manual_int64_widen_unsigned]

private theorem manual_int64_shru_prime (value : int) (amount : Int.int) :
    shru' value amount = shru value (repr (Int.unsigned amount)) := by
  change repr (zShiftr (unsigned value) (Int.unsigned amount)) =
    repr (zShiftr (unsigned value) (unsigned (repr (Int.unsigned amount))))
  rw [manual_int64_widen_unsigned]

private theorem manual_int64_shr_prime (value : int) (amount : Int.int) :
    shr' value amount = shr value (repr (Int.unsigned amount)) := by
  change repr (zShiftr (signed value) (Int.unsigned amount)) =
    repr (zShiftr (signed value) (unsigned (repr (Int.unsigned amount))))
  rw [manual_int64_widen_unsigned]

theorem shl'_shl'_proof : shl'_shl' := by
  intro value first second first_lt second_lt sum_lt
  rw [manual_int64_shl_prime, manual_int64_shl_prime, manual_int64_shl_prime]
  have addition := manual_int64_widen_add first second first_lt second_lt
  rw [← addition]
  apply shl_shl_proof
  · exact manual_int64_widen_ltu first first_lt
  · exact manual_int64_widen_ltu second second_lt
  · rw [addition]
    exact manual_int64_widen_ltu (Int.add first second) sum_lt

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shru'_shru'_proof : shru'_shru' := by
  intro value first second first_lt second_lt sum_lt
  rw [manual_int64_shru_prime, manual_int64_shru_prime, manual_int64_shru_prime]
  have addition := manual_int64_widen_add first second first_lt second_lt
  rw [← addition]
  apply shru_shru_proof
  · exact manual_int64_widen_ltu first first_lt
  · exact manual_int64_widen_ltu second second_lt
  · rw [addition]
    exact manual_int64_widen_ltu (Int.add first second) sum_lt

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_clamped_index (index : Z) :
    zltSelect index zwordsize index (zSub zwordsize zOne) =
      zOfInt (min (intOfZ index) 63) := by
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt index zwordsize with
  | left less =>
      have bound : intOfZ index ≤ 63 := by
        change intOfZ index < 64 at less
        omega
      simp only [zltSelect, sumboolSelect, comparison, _root_.Int.min_eq_left bound]
      exact (zOfInt_intOfZ index).symm
  | right greater =>
      have bound : 63 ≤ intOfZ index := by
        change 64 ≤ intOfZ index at greater
        omega
      simp only [zltSelect, sumboolSelect, comparison, _root_.Int.min_eq_right bound]
      rfl

private theorem manual_int64_bits_shr (value amount : int) (index : Z)
    (bounds : zLe zZero index ∧ zLt index zwordsize) :
    testbit (shr value amount) index =
      testbit value (zOfInt (min (intOfZ index + intOfZ (unsigned amount)) 63)) := by
  change testbit (repr (zShiftr (signed value) (unsigned amount))) index = _
  rw [testbit_repr_proof _ _ bounds]
  change ZArith.BinInt.Z.testbit
    (ZArith.BinInt.Z.shiftr (signed value) (unsigned amount)) index = _
  rw [ZArith.BinInt.Z.shiftr_spec (signed value) (unsigned amount) index bounds.1]
  have lower : zLe zZero (zAdd index (unsigned amount)) := by
    have index_lower : 0 ≤ intOfZ index := bounds.1
    have amount_lower : 0 ≤ intOfZ (unsigned amount) := (unsigned_range_proof amount).1
    change 0 ≤ intOfZ (zAdd index (unsigned amount))
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    omega
  have signed_bits := bits_signed_proof value _ lower
  change ZArith.BinInt.Z.testbit (signed value) (ZArith.BinInt.Z.add index (unsigned amount)) =
    testbit value (zltSelect (zAdd index (unsigned amount)) zwordsize
      (zAdd index (unsigned amount)) (zSub zwordsize zOne)) at signed_bits
  rw [signed_bits, manual_int64_clamped_index]
  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]

theorem shr_shr_proof : shr_shr := by
  intro value first second first_lt second_lt sum_lt
  have first_bounds := ltu_inv_proof first iwordsize first_lt
  have second_bounds := ltu_inv_proof second iwordsize second_lt
  have first_lower : 0 ≤ intOfZ (unsigned first) := first_bounds.1
  have second_lower : 0 ≤ intOfZ (unsigned second) := second_bounds.1
  have first_upper : intOfZ (unsigned first) < 64 := first_bounds.2
  have second_upper : intOfZ (unsigned second) < 64 := second_bounds.2
  have addition : unsigned (add first second) = zAdd (unsigned first) (unsigned second) := by
    apply unsigned_repr_proof
    change 0 ≤ intOfZ (zAdd (unsigned first) (unsigned second)) ∧
      intOfZ (zAdd (unsigned first) (unsigned second)) ≤ 18446744073709551615
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    omega
  apply same_bits_eq_proof
  intro index bounds
  have index_lower : 0 ≤ intOfZ index := bounds.1
  have intermediate_bounds :
      zLe zZero (zOfInt (min (intOfZ index + intOfZ (unsigned second)) 63)) ∧
      zLt (zOfInt (min (intOfZ index + intOfZ (unsigned second)) 63)) zwordsize := by
    change 0 ≤ intOfZ (zOfInt _) ∧ intOfZ (zOfInt _) < 64
    simp only [intOfZ_zOfInt]
    omega
  rw [manual_int64_bits_shr (shr value first) second index bounds,
    manual_int64_bits_shr value (add first second) index bounds,
    manual_int64_bits_shr value first _ intermediate_bounds, addition]
  simp only [intOfZ_zOfInt, zAdd, ZArith.BinInt.Z.add]
  congr 2
  omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shr'_shr'_proof : shr'_shr' := by
  intro value first second first_lt second_lt sum_lt
  rw [manual_int64_shr_prime, manual_int64_shr_prime, manual_int64_shr_prime]
  have addition := manual_int64_widen_add first second first_lt second_lt
  rw [← addition]
  apply shr_shr_proof
  · exact manual_int64_widen_ltu first first_lt
  · exact manual_int64_widen_ltu second second_lt
  · rw [addition]
    exact manual_int64_widen_ltu (Int.add first second) sum_lt

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_negative_index (value : int) (index : Z)
    (negative : intOfZ index < 0) : testbit value index = false := by
  cases index with
  | Zneg position => rfl
  | Z0 =>
      change (0 : _root_.Int) < 0 at negative
      omega
  | Zpos position =>
      change _root_.Int.ofNat (posToNat position) < 0 at negative
      simp only [_root_.Int.ofNat_eq_natCast] at negative
      omega

theorem bits_size_4_proof : bits_size_4 := by
  intro value length hn hbit hhigh
  cases length with
  | Zneg position =>
      change (0 : Int) ≤ -_root_.Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position) at hn
      have hp : (0 : Int) < _root_.Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position) :=
        _root_.Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive position)
      omega
  | Z0 =>
      have hidx : intOfZ (zSub zZero zOne) < 0 := by
        change (0 : Int) - 1 < 0
        omega
      have hf := manual_int64_negative_index value (zSub zZero zOne) hidx
      rw [hf] at hbit
      cases hbit
  | Zpos position =>
      let width := CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position
      have hkpos : 0 < width :=
        CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive position
      have hz : zOfNat width = .Zpos position := by
        exact ZArith.Znat.positive_nat_Z position
      have hsub : zSub (.Zpos position) zOne = zOfNat (width - 1) := by
        rw [← hz]
        exact Int.suffix_zsub_nat width 1 (by omega)
      rw [hsub] at hbit
      have hbitnat : value.val.testBit (width - 1) = true := by
        rw [suffix_int64_testbit_nat] at hbit
        exact hbit
      have hhighNat : ∀ index : Nat, width ≤ index → value.val.testBit index = false := by
        intro index hik
        by_cases hi32 : index < wordsize
        · have hki : zLe (.Zpos position) (zOfNat index) := by
            change intOfZ (.Zpos position) ≤ intOfZ (zOfNat index)
            rw [← hz]
            simp only [zOfNat, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt]
            exact _root_.Int.ofNat_le.mpr hik
          have hil : zLt (zOfNat index) zwordsize := by
            change intOfZ (zOfNat index) < intOfZ zwordsize
            simp only [zOfNat, zwordsize, ZArith.BinInt.Z.of_nat,
              intOfZ_zOfInt]
            exact _root_.Int.ofNat_lt.mpr hi32
          have hh := hhigh (zOfNat index) ⟨hki, hil⟩
          rw [suffix_int64_testbit_nat] at hh
          exact hh
        · have hxlt : value.val < 2 ^ wordsize := WordCore.val_lt value
          have hpow : 2 ^ wordsize ≤ 2 ^ index :=
            Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi32)
          exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hxlt hpow)
      have hxne : value.val ≠ 0 := by
        intro hx
        rw [hx] at hbitnat
        simp at hbitnat
      have hlo : 2 ^ (width - 1) ≤ value.val :=
        Nat.ge_two_pow_of_testBit hbitnat
      have hkstep : width - 1 + 1 = width := by omega
      have hupp : value.val < 2 ^ ((width - 1) + 1) := by
        rw [hkstep]
        exact Nat.lt_pow_two_of_testBit value.val (by
          intro index hik
          exact hhighNat index hik)
      have hlog : Nat.log2 value.val = width - 1 :=
        (Nat.log2_eq_iff hxne).2 ⟨hlo, hupp⟩
      cases hval : value.val with
      | zero => exact (hxne hval).elim
      | succ number =>
          have hsz0 :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat
                  (PArith.BinPos.Pos.size (posOfNat (number + 1))) = width := by
            unfold PArith.BinPos.Pos.size
            rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
              (by omega : 0 < number + 1)]
            have hlog' : Nat.log2 (number + 1) = width - 1 := by
              simpa [hval] using hlog
            rw [hlog']
            rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat
              (by omega : 0 < width - 1 + 1)]
            omega
          change CompCert4Lean.Lib.Zbits.Zsize (unsigned value) = .Zpos position
          rw [← hz]
          rw [manual_int64_unsigned_as_nat value, hval]
          simp only [CompCert4Lean.Lib.Zbits.Zsize]
          change .Zpos (PArith.BinPos.Pos.size (posOfNat (number + 1))) = zOfNat width
          have hzk : zOfNat width = .Zpos (posOfNat width) := by
            cases hk : width with
            | zero => omega
            | succ remaining => rfl
          rw [hzk]
          have hpos : PArith.BinPos.Pos.size (posOfNat (number + 1)) =
              posOfNat width :=
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_injective
              (by
                rw [CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_posOfNat hkpos]
                exact hsz0)
          exact congrArg
            (fun remaining => CompCert4Lean.Foundation.Numbers.Rocq.Coq.Zpos remaining) hpos

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

set_option maxRecDepth 4096 in
theorem divmodu2_divu_modu_proof : divmodu2_divu_modu := by
  intro numerator denominator hd
  unfold divmodu2 divu modu
  by_cases hdz : denominator = zero
  · exact (hd hdz).elim
  · have hsum :
        zAdd (zMul (unsigned zero) modulus) (unsigned numerator) = unsigned numerator := by
      apply intOfZ_injective
      simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
        intOfZ_zOfInt]
      have hz : intOfZ (unsigned zero) = (0 : Int) := by rfl
      rw [hz]
      omega
    rw [hsum]
    simp [eq_dec, hdz]
    have hn0 : (0 : Int) ≤ intOfZ (unsigned numerator) := by
      have hn := numerator.intrange.1
      change (-1 : Int) < intOfZ numerator.intval at hn
      change 0 ≤ intOfZ numerator.intval
      omega
    have hnmax : intOfZ (unsigned numerator) ≤ intOfZ max_unsigned := by
      have hn := numerator.intrange.2
      change intOfZ numerator.intval < intOfZ modulus at hn
      change intOfZ numerator.intval ≤ intOfZ modulus - 1
      omega
    have hd0 : (0 : Int) ≤ intOfZ (unsigned denominator) := by
      have hd' := denominator.intrange.1
      change (-1 : Int) < intOfZ denominator.intval at hd'
      change 0 ≤ intOfZ denominator.intval
      omega
    have hdpos : (0 : Int) < intOfZ (unsigned denominator) := by
      have hdne : intOfZ (unsigned denominator) ≠ 0 := by
        intro hzero
        apply hd
        apply WordCore.ext
        apply intOfZ_injective
        change intOfZ denominator.intval = 0 at hzero
        have hz0 : intOfZ zero.intval = 0 := by rfl
        exact hzero.trans hz0.symm
      omega
    have hqbound : zLe (ZArith.BinInt.Z.div_eucl
        (unsigned numerator) (unsigned denominator)).1 max_unsigned := by
      have hb := CompCert4Lean.Lib.Coqlib.Zdiv_interval_1
        zZero (zAdd max_unsigned zOne) (unsigned numerator) (unsigned denominator)
        (by
          change (0 : Int) ≤ 0
          omega) (by
          change (0 : Int) < intOfZ (zAdd max_unsigned zOne)
          simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
          change (0 : Int) < (2 ^ wordsize : Int)
          exact _root_.Int.pow_pos (by omega))
        (by exact hdpos)
        (by
          constructor
          · change intOfZ (zMul zZero (unsigned denominator)) ≤ intOfZ (unsigned numerator)
            simp only [zMul, ZArith.BinInt.Z.mul]
            simp only [intOfZ_zOfInt]
            have hz0 : intOfZ zZero = (0 : Int) := by rfl
            rw [hz0, _root_.Int.zero_mul]
            exact hn0
          · change intOfZ (unsigned numerator) < intOfZ
              (zMul (zAdd max_unsigned zOne) (unsigned denominator))
            have hmax : intOfZ max_unsigned = (2 ^ wordsize : Int) - 1 := by
              rfl
            have hone : intOfZ zOne = (1 : Int) := by rfl
            have hmul : intOfZ (unsigned numerator) ≤
                ((2 ^ wordsize : Int) - 1) * intOfZ (unsigned denominator) := by
              have hnd := _root_.Int.mul_le_mul_of_nonneg_left
                (show (1 : Int) ≤ intOfZ (unsigned denominator) by omega) hn0
              have hmaxd := _root_.Int.mul_le_mul_of_nonneg_right hnmax hd0
              exact _root_.Int.le_trans (by simpa using hnd) (by simpa [hmax] using hmaxd)
            have hstrict : ((2 ^ wordsize : Int) - 1) * intOfZ (unsigned denominator) <
                (((2 ^ wordsize : Int) - 1) + 1) * intOfZ (unsigned denominator) := by
              apply _root_.Int.mul_lt_mul_of_pos_right _ hdpos
              omega
            have hlt : intOfZ (unsigned numerator) <
                (((2 ^ wordsize : Int) - 1) + 1) * intOfZ (unsigned denominator) :=
              _root_.Int.lt_of_le_of_lt hmul hstrict
            simpa [zMul, zAdd, ZArith.BinInt.Z.mul,
              ZArith.BinInt.Z.add, intOfZ_zOfInt, hmax, hone] using hlt)
      have hqhi := hb.2
      change intOfZ (ZArith.BinInt.Z.div_eucl
          (unsigned numerator) (unsigned denominator)).1 <
        intOfZ (zAdd max_unsigned zOne) at hqhi
      change intOfZ (ZArith.BinInt.Z.div_eucl
          (unsigned numerator) (unsigned denominator)).1 ≤ intOfZ max_unsigned
      simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] at hqhi ⊢
      have hmax : intOfZ max_unsigned = (2 ^ wordsize : Int) - 1 := by
        rfl
      have hone : intOfZ zOne = (1 : Int) := by rfl
      rw [hmax] at hqhi ⊢
      rw [hone] at hqhi
      omega
    cases hle : CompCert4Lean.Lib.Coqlib.zle
        (ZArith.BinInt.Z.div_eucl (unsigned numerator) (unsigned denominator)).1 max_unsigned with
    | left hle' =>
        simp [hle, ZArith.BinInt.Z.div_eucl]
        constructor <;> rfl
    | right hle' =>
        exfalso
        exact (_root_.Int.not_lt_of_ge hqbound hle').elim

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shr_lt_zero_proof : shr_lt_zero := by
  intro value
  have bounds := signed_range_proof value
  change (-9223372036854775808 : _root_.Int) ≤ intOfZ (signed value) ∧
    intOfZ (signed value) ≤ 9223372036854775807 at bounds
  change repr (zOfInt ((intOfZ (signed value)).ediv 9223372036854775808)) =
    if zltSelect (signed value) zZero true false then mone else zero
  rw [manual_int64_zlt_bool]
  change repr (zOfInt ((intOfZ (signed value)).ediv 9223372036854775808)) =
    if decide (intOfZ (signed value) < 0) then mone else zero
  by_cases negative : intOfZ (signed value) < 0
  · simp only [negative, decide_true, ↓reduceIte]
    have quotient : (intOfZ (signed value)).ediv 9223372036854775808 = -1 := by
      apply (_root_.Int.ediv_eq_iff_of_pos (by decide)).2
      constructor <;> omega
    rw [quotient]
    rfl
  · simp only [negative, decide_false, Bool.false_eq_true, ↓reduceIte]
    have quotient : (intOfZ (signed value)).ediv 9223372036854775808 = 0 := by
      apply (_root_.Int.ediv_eq_iff_of_pos (by decide)).2
      constructor <;> omega
    rw [quotient]
    rfl

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_signed_int (value : int) :
    intOfZ (signed value) =
      if intOfZ (unsigned value) < 9223372036854775808 then intOfZ (unsigned value)
      else intOfZ (unsigned value) - 18446744073709551616 := by
  unfold signed WordCore.signed
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt
      (WordCore.unsigned value) (zTwoPowerNat (wordsize - 1)) with
  | left less =>
      have bound : intOfZ (unsigned value) < 9223372036854775808 := less
      simp only [zltSelect, sumboolSelect, comparison, if_pos bound]
      rfl
  | right greater =>
      have bound : ¬intOfZ (unsigned value) < 9223372036854775808 :=
        _root_.Int.not_lt_of_ge greater
      simp only [zltSelect, sumboolSelect, comparison, if_neg bound,
        zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      rfl

private theorem manual_int64_negative_unsigned (value : int) :
    lt value zero = decide (9223372036854775808 ≤ intOfZ (unsigned value)) := by
  change zltSelect (signed value) zZero true false = _
  rw [manual_int64_zlt_bool]
  change decide (intOfZ (signed value) < 0) = _
  apply decide_eq_decide.mpr
  rw [manual_int64_signed_int]
  have bounds := unsigned_range_proof value
  change 0 ≤ intOfZ (unsigned value) ∧ intOfZ (unsigned value) < 18446744073709551616 at bounds
  split <;> omega

theorem shru_lt_zero_proof : shru_lt_zero := by
  intro value
  have bounds := unsigned_range_proof value
  change 0 ≤ intOfZ (unsigned value) ∧ intOfZ (unsigned value) < 18446744073709551616 at bounds
  change repr (zOfInt ((intOfZ (unsigned value)).ediv 9223372036854775808)) =
    if lt value zero then one else zero
  rw [manual_int64_negative_unsigned]
  by_cases upper : 9223372036854775808 ≤ intOfZ (unsigned value)
  · simp only [upper, decide_true, ↓reduceIte]
    have quotient : (intOfZ (unsigned value)).ediv 9223372036854775808 = 1 := by
      apply (_root_.Int.ediv_eq_iff_of_pos (by decide)).2
      constructor <;> omega
    rw [quotient]
    rfl
  · simp only [upper, decide_false, Bool.false_eq_true, ↓reduceIte]
    have quotient : (intOfZ (unsigned value)).ediv 9223372036854775808 = 0 := by
      apply (_root_.Int.ediv_eq_iff_of_pos (by decide)).2
      constructor <;> omega
    rw [quotient]
    rfl

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_bits_or_nat (left right : int) (index : Nat) :
    testbit (or left right) (zOfNat index) =
      (testbit left (zOfNat index) || testbit right (zOfNat index)) := by
  rw [suffix_int64_testbit_nat, suffix_int64_testbit_nat, suffix_int64_testbit_nat,
    manual_int64_or_val, Nat.lor_eq, Nat.testBit_or]

theorem or_ror_proof : or_ror := by
  intro value first second hy hz hsum
  have hyv : first.val < wordsize := manual_int64_ltu_wordsize first hy
  have hzv : second.val < wordsize := manual_int64_ltu_wordsize second hz
  have hsum_nat : first.val + second.val = wordsize := by
    change first.val < 64 at hyv
    change second.val < 64 at hzv
    have hval := congrArg (fun word : int => word.val) hsum
    change (WordCore.add first second).val = iwordsize.val at hval
    rw [WordCore.add_val] at hval
    change (first.val + second.val) % (2 ^ wordsize) = iwordsize.val at hval
    have hiword : iwordsize.val = wordsize := rfl
    rw [hiword] at hval
    have hlt : first.val + second.val < 2 ^ wordsize := by
      change first.val + second.val < 2 ^ 64
      omega
    rw [Nat.mod_eq_of_lt hlt] at hval
    exact hval
  have hyu : unsigned first = zOfNat first.val := by
    change first.intval = zOfNat first.val
    exact WordCore.intval_eq_zOfNat_val first
  have hzu : unsigned second = zOfNat second.val := by
    change second.intval = zOfNat second.val
    exact WordCore.intval_eq_zOfNat_val second
  have hbits : ∀ offset : Nat, offset < wordsize →
      testbit (ror value second) (zOfNat offset) =
        testbit (or (shl value first) (shru value second)) (zOfNat offset) := by
    intro offset hn
    calc
      testbit (ror value second) (zOfNat offset) =
          (WordCore.ror value second).val.testBit offset := suffix_int64_testbit_nat _ _
      _ = value.val.testBit ((offset + second.val) % wordsize) := pg_suffix_ror_bit value second offset hn
      _ = (testbit (shl value first) (zOfNat offset) ||
        testbit (shru value second) (zOfNat offset)) := by
        rw [manual_int64_bits_shl_nat value first offset hn, manual_int64_bits_shru_nat value second offset]
        by_cases hny : offset < first.val
        · have hnz : offset + second.val < wordsize := by omega
          have hYlt : zLt (zOfNat offset) (unsigned first) := by
            rw [hyu]
            change intOfZ (zOfNat offset) < intOfZ (zOfNat first.val)
            simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact _root_.Int.ofNat_lt.mpr hny
          have hWlt : zLt (zAdd (zOfNat offset) (unsigned second)) zwordsize := by
            rw [hzu]
            change intOfZ (zAdd (zOfNat offset) (zOfNat second.val)) < intOfZ zwordsize
            simp only [zAdd, zwordsize, ZArith.BinInt.Z.add,
              ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact _root_.Int.ofNat_lt.mpr hnz
          have haddz : zAdd (zOfNat offset) (unsigned second) =
              zOfNat (offset + second.val) := by
            rw [hzu]
            apply intOfZ_injective
            simp only [zAdd, ZArith.BinInt.Z.add, zOfNat,
              ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, _root_.Int.natCast_add]
            exact (_root_.Int.ofNat_add_ofNat offset second.val).symm
          have hidx : testbit value (zAdd (zOfNat offset) (unsigned second)) =
              value.val.testBit ((offset + second.val) % wordsize) := by
            rw [haddz, suffix_int64_testbit_nat]
            rw [Nat.mod_eq_of_lt hnz]
          cases hYc : CompCert4Lean.Lib.Coqlib.zlt
              (zOfNat offset) (unsigned first) with
          | left hYp =>
              cases hWc : CompCert4Lean.Lib.Coqlib.zlt
                  (zAdd (zOfNat offset) (unsigned second)) zwordsize with
              | left hWp =>
                  simp [zltSelect, sumboolSelect, hYc, hWc, hidx,
                    Nat.mod_eq_of_lt hnz]
              | right hWp => exfalso; exact (_root_.Int.not_lt_of_ge hWp) hWlt
          | right hYp => exfalso; exact (_root_.Int.not_lt_of_ge hYp) hYlt
        · have hyn : first.val ≤ offset := Nat.le_of_not_gt hny
          have hnz : wordsize ≤ offset + second.val := by omega
          have hYge : zLe (unsigned first) (zOfNat offset) := by
            rw [hyu]
            change intOfZ (zOfNat first.val) ≤ intOfZ (zOfNat offset)
            simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact _root_.Int.ofNat_le.mpr hyn
          have hWge : zLe zwordsize (zAdd (zOfNat offset) (unsigned second)) := by
            rw [hzu]
            change intOfZ zwordsize ≤ intOfZ (zAdd (zOfNat offset) (zOfNat second.val))
            simp only [zAdd, zwordsize, ZArith.BinInt.Z.add,
              ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact _root_.Int.ofNat_le.mpr hnz
          have hsuby : zSub (zOfNat offset) (unsigned first) =
              zOfNat (offset - first.val) := by
            rw [hyu]
            apply intOfZ_injective
            simp only [zSub, ZArith.BinInt.Z.sub, zOfNat,
              ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
            exact (_root_.Int.ofNat_sub hyn).symm
          have hidxNat : offset - first.val = (offset + second.val) % wordsize := by
            rw [Nat.mod_eq_sub_mod hnz, Nat.mod_eq_of_lt (by omega)]
            omega
          have hidx : testbit value (zSub (zOfNat offset) (unsigned first)) =
              value.val.testBit ((offset + second.val) % wordsize) := by
            rw [hsuby, suffix_int64_testbit_nat, hidxNat]
          cases hYc : CompCert4Lean.Lib.Coqlib.zlt
              (zOfNat offset) (unsigned first) with
          | left hYp => exfalso; exact (_root_.Int.not_lt_of_ge hYge) hYp
          | right hYp =>
              cases hWc : CompCert4Lean.Lib.Coqlib.zlt
                  (zAdd (zOfNat offset) (unsigned second)) zwordsize with
              | left hWp => exfalso; exact (_root_.Int.not_lt_of_ge hWge) hWp
              | right hWp =>
                  simp [zltSelect, sumboolSelect, hYc, hWc, hidx,
                    Nat.mod_eq_sub_mod hnz]
      _ = testbit (or (shl value first) (shru value second)) (zOfNat offset) :=
        (manual_int64_bits_or_nat (shl value first) (shru value second) offset).symm
  apply same_bits_eq_proof
  intro index hi
  cases index with
  | Zneg position =>
      have hi0 := hi.1
      change (0 : Int) ≤ -_root_.Int.ofNat
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position) at hi0
      have hp : (0 : Int) < _root_.Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position) :=
        _root_.Int.natCast_pos.mpr
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat_positive position)
      omega
  | Z0 => exact hbits 0 (by decide)
  | Zpos position =>
      have hnZ := hi.2
      change (_root_.Int.ofNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position) : Int) <
        _root_.Int.ofNat wordsize at hnZ
      have hn : CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position < wordsize :=
        _root_.Int.ofNat_lt.mp hnZ
      have hzpos : zOfNat
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position) = .Zpos position := by
        exact ZArith.Znat.positive_nat_Z position
      rw [← hzpos] at hi ⊢
      exact hbits _ hn

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem or_ror'_proof : or_ror' := by
  intro value first second first_lt second_lt sum_eq
  rw [manual_int64_shl_prime, manual_int64_shru_prime]
  apply or_ror_proof value (repr (Int.unsigned first)) (repr (Int.unsigned second))
    (manual_int64_widen_ltu first first_lt) (manual_int64_widen_ltu second second_lt)
  rw [manual_int64_widen_add first second first_lt second_lt, sum_eq]
  rfl

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_power_nat
    (power logn : int) (hpow : is_power2 power = some logn) :
    ∃ exponent : Nat, power.val = 2 ^ exponent := by
  unfold is_power2 at hpow
  cases hu : unsigned power with
  | Z0 =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zneg position =>
      simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu] at hpow
      cases hpow
  | Zpos position =>
      cases hp : CompCert4Lean.Lib.Zbits.P_is_power2 position with
      | false =>
          simp only [CompCert4Lean.Lib.Zbits.Z_is_power2, hu, hp,
            Bool.false_eq_true, ↓reduceIte] at hpow
          cases hpow
      | true =>
          rcases Int.suffix_positive_is_power2 position hp with ⟨exponent, hk⟩
          refine ⟨exponent, ?_⟩
          have hz : zOfNat power.val = .Zpos position := by
            exact (WordCore.intval_eq_zOfNat_val power).symm.trans hu
          have hi : _root_.Int.ofNat power.val = _root_.Int.ofNat
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position) := by
            calc
              _root_.Int.ofNat power.val = intOfZ (zOfNat power.val) := by
                exact (intOfZ_zOfInt (_root_.Int.ofNat power.val)).symm
              _ = intOfZ (.Zpos position) := congrArg intOfZ hz
              _ = _root_.Int.ofNat
                  (CompCert4Lean.Foundation.Numbers.Rocq.Coq.posToNat position) := by
                rfl
          exact (_root_.Int.ofNat.inj hi).trans hk

private theorem manual_int64_sub_one_val
    (power : int) (hnpos : 0 < power.val) :
    (sub power one).val = power.val - 1 := by
  change (WordCore.sub power (WordCore.one wordsize)).val = power.val - 1
  rw [WordCore.sub_val]
  change (2 ^ wordsize - 1 + power.val) % (2 ^ wordsize) = power.val - 1
  have hnlt : power.val < 2 ^ wordsize := WordCore.val_lt power
  have hadd : 2 ^ wordsize - 1 + power.val =
      (power.val - 1) + 2 ^ wordsize := by omega
  rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem manual_int64_modu_val
    (value power : int) (hnpos : 0 < power.val) :
    (modu value power).val = value.val % power.val := by
  unfold modu WordCore.modu
  change (WordCore.repr wordsize
    (ZArith.BinInt.Z.modulo (unsigned value) (unsigned power))).val = value.val % power.val
  have hx : unsigned value = zOfNat value.val :=
    WordCore.intval_eq_zOfNat_val value
  have hn : unsigned power = zOfNat power.val :=
    WordCore.intval_eq_zOfNat_val power
  rw [hx, hn, Int.suffix_modulo_nat _ _ hnpos]
  rw [show zOfNat (value.val % power.val) =
      zOfInt (_root_.Int.ofNat (value.val % power.val)) by rfl]
  rw [WordCore.val_repr]
  have hrem : value.val % power.val < 2 ^ wordsize :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hnpos)
      (Nat.le_of_lt (WordCore.val_lt power))
  have hmod : _root_.Int.ofNat (value.val % power.val) %
      ((2 ^ wordsize : Nat) : Int) = _root_.Int.ofNat (value.val % power.val) :=
    _root_.Int.emod_eq_of_lt (_root_.Int.natCast_nonneg _)
      (by
        change _root_.Int.ofNat (value.val % power.val) < _root_.Int.ofNat (2 ^ wordsize)
        exact _root_.Int.ofNat_lt.mpr hrem)
  rw [hmod]
  exact _root_.Int.toNat_natCast _


theorem modu_and_proof : modu_and := by
  intro value power logarithm found
  obtain ⟨exponent, encoding⟩ := manual_int64_power_nat power logarithm found
  have positive : 0 < power.val := by
    rw [encoding]
    exact Nat.two_pow_pos exponent
  apply WordCore.ext_of_val_eq
  rw [manual_int64_modu_val value power positive, manual_int64_and_val,
    manual_int64_sub_one_val power positive, encoding]
  exact (Nat.and_two_pow_sub_one_eq_mod value.val exponent).symm

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem manual_int64_zlt_select {Result : Type} (left right : Z)
    (yes no : Result) :
    zltSelect left right yes no =
      if intOfZ left < intOfZ right then yes else no := by
  cases comparison : CompCert4Lean.Lib.Coqlib.zlt left right with
  | left less =>
      have bound : intOfZ left < intOfZ right := less
      simp only [zltSelect, sumboolSelect, comparison, if_pos bound]
  | right greater =>
      simp only [zltSelect, sumboolSelect, comparison,
        if_neg (_root_.Int.not_lt_of_ge greater)]

private theorem manual_int64_sub32_unsigned (left right : Int.int)
    (bounds : 0 ≤ intOfZ (Int.unsigned left) - intOfZ (Int.unsigned right) ∧
      intOfZ (Int.unsigned left) - intOfZ (Int.unsigned right) ≤ 4294967295) :
    Int.unsigned (Int.sub left right) = zSub (Int.unsigned left) (Int.unsigned right) := by
  apply Int.unsigned_repr_proof_api
  change 0 ≤ intOfZ (zSub (Int.unsigned left) (Int.unsigned right)) ∧
    intOfZ (zSub (Int.unsigned left) (Int.unsigned right)) ≤ 4294967295
  simpa only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt] using bounds

private theorem manual_int64_ofwords_bits (high low : Int.int) (index : _root_.Int)
    (bounds : 0 ≤ index ∧ index < 64) :
    testbit (ofwords high low) (zOfInt index) =
      if index < 32 then Int.testbit low (zOfInt index)
      else Int.testbit high (zOfInt (index - 32)) := by
  have encoded_bounds : zLe zZero (zOfInt index) ∧ zLt (zOfInt index) zwordsize := by
    change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 64
    simpa only [intOfZ_zOfInt] using bounds
  rw [bits_ofwords_proof high low _ encoded_bounds, manual_int64_zlt_select]
  simp only [intOfZ_zOfInt, zSub, ZArith.BinInt.Z.sub]
  rfl

private theorem manual_int32_shl_bits (value amount : Int.int) (index : _root_.Int)
    (bounds : 0 ≤ index ∧ index < 32) :
    Int.testbit (Int.shl value amount) (zOfInt index) =
      if index < intOfZ (Int.unsigned amount) then false
      else Int.testbit value (zOfInt (index - intOfZ (Int.unsigned amount))) := by
  have encoded_bounds : zLe zZero (zOfInt index) ∧ zLt (zOfInt index) Int.zwordsize := by
    change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 32
    simpa only [intOfZ_zOfInt] using bounds
  have law := Int.bits_shl_proof value amount _ encoded_bounds
  change Int.testbit (Int.shl value amount) (zOfInt index) =
    zltSelect (zOfInt index) (Int.unsigned amount) false
      (Int.testbit value (zSub (zOfInt index) (Int.unsigned amount))) at law
  rw [law, manual_int64_zlt_select]
  simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]

private theorem manual_int64_shl_prime_bits (value : int) (amount : Int.int)
    (index : _root_.Int) (bounds : 0 ≤ index ∧ index < 64) :
    testbit (shl' value amount) (zOfInt index) =
      if index < intOfZ (Int.unsigned amount) then false
      else testbit value (zOfInt (index - intOfZ (Int.unsigned amount))) := by
  have encoded_bounds : zLe zZero (zOfInt index) ∧ zLt (zOfInt index) zwordsize := by
    change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 64
    simpa only [intOfZ_zOfInt] using bounds
  rw [bits_shl'_proof value amount _ encoded_bounds, manual_int64_zlt_select]
  simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]

theorem decompose_shl_2_proof : decompose_shl_2 := by
  intro high low amount amount_bounds
  have amount_lower : 32 ≤ intOfZ (Int.unsigned amount) := amount_bounds.1
  have amount_upper : intOfZ (Int.unsigned amount) < 64 := amount_bounds.2
  have difference := manual_int64_sub32_unsigned amount Int.iwordsize (by
    change 0 ≤ intOfZ (Int.unsigned amount) - 32 ∧
      intOfZ (Int.unsigned amount) - 32 ≤ 4294967295
    omega)
  have difference_value : intOfZ (Int.unsigned (Int.sub amount Int.iwordsize)) =
      intOfZ (Int.unsigned amount) - 32 := by
    rw [difference]
    simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    rfl
  apply same_bits_eq_proof
  intro encoded index_bounds
  let index := intOfZ encoded
  have index_bounds' : 0 ≤ index ∧ index < 64 := index_bounds
  have encoding : encoded = zOfInt index := (zOfInt_intOfZ encoded).symm
  rw [encoding, manual_int64_shl_prime_bits _ _ _ index_bounds',
    manual_int64_ofwords_bits _ _ _ index_bounds']
  by_cases lower : index < 32
  · have before_shift : index < intOfZ (Int.unsigned amount) := by omega
    simp only [lower, before_shift, ↓reduceIte]
    exact (Int.bits_zero_proof _).symm
  · simp only [lower, ↓reduceIte]
    rw [manual_int32_shl_bits _ _ _ (by omega), difference_value]
    by_cases before_shift : index < intOfZ (Int.unsigned amount)
    · have before_shift' : index - 32 < intOfZ (Int.unsigned amount) - 32 := by omega
      simp only [before_shift, before_shift', ↓reduceIte]
    · have after_shift' : ¬index - 32 < intOfZ (Int.unsigned amount) - 32 := by omega
      simp only [before_shift, after_shift', ↓reduceIte]
      rw [manual_int64_ofwords_bits _ _ _ (by omega)]
      have low_index : index - intOfZ (Int.unsigned amount) < 32 := by omega
      simp only [low_index, ↓reduceIte]
      congr 2
      omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem remaining_int32_shru_bits (value amount : Int.int) (index : _root_.Int)
    (bounds : 0 ≤ index ∧ index < 32) :
    Int.testbit (Int.shru value amount) (zOfInt index) =
      if index + intOfZ (Int.unsigned amount) < 32 then
        Int.testbit value (zOfInt (index + intOfZ (Int.unsigned amount)))
      else false := by
  have encoded_bounds : zLe zZero (zOfInt index) ∧ zLt (zOfInt index) Int.zwordsize := by
    change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 32
    simpa only [intOfZ_zOfInt] using bounds
  have law := Int.bits_shru_proof value amount _ encoded_bounds
  change Int.testbit (Int.shru value amount) (zOfInt index) =
    zltSelect (zAdd (zOfInt index) (Int.unsigned amount)) Int.zwordsize
      (Int.testbit value (zAdd (zOfInt index) (Int.unsigned amount))) false at law
  rw [law, manual_int64_zlt_select]
  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  rfl

private theorem remaining_int64_shru_prime_bits (value : int) (amount : Int.int)
    (index : _root_.Int) (bounds : 0 ≤ index ∧ index < 64) :
    testbit (shru' value amount) (zOfInt index) =
      if index + intOfZ (Int.unsigned amount) < 64 then
        testbit value (zOfInt (index + intOfZ (Int.unsigned amount)))
      else false := by
  have encoded_bounds : zLe zZero (zOfInt index) ∧ zLt (zOfInt index) zwordsize := by
    change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 64
    simpa only [intOfZ_zOfInt] using bounds
  rw [bits_shru'_proof value amount _ encoded_bounds, manual_int64_zlt_select]
  simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  rfl

theorem decompose_shru_2_proof : decompose_shru_2 := by
  intro high low amount amount_bounds
  have amount_lower : 32 ≤ intOfZ (Int.unsigned amount) := amount_bounds.1
  have amount_upper : intOfZ (Int.unsigned amount) < 64 := amount_bounds.2
  have difference := manual_int64_sub32_unsigned amount Int.iwordsize (by
    change 0 ≤ intOfZ (Int.unsigned amount) - 32 ∧
      intOfZ (Int.unsigned amount) - 32 ≤ 4294967295
    omega)
  have difference_value : intOfZ (Int.unsigned (Int.sub amount Int.iwordsize)) =
      intOfZ (Int.unsigned amount) - 32 := by
    rw [difference]
    simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    rfl
  apply same_bits_eq_proof
  intro encoded index_bounds
  let index := intOfZ encoded
  have index_bounds' : 0 ≤ index ∧ index < 64 := index_bounds
  have encoding : encoded = zOfInt index := (zOfInt_intOfZ encoded).symm
  rw [encoding, remaining_int64_shru_prime_bits _ _ _ index_bounds',
    manual_int64_ofwords_bits _ _ _ index_bounds']
  by_cases lower : index < 32
  · simp only [lower, ↓reduceIte]
    rw [remaining_int32_shru_bits _ _ _ (by omega), difference_value]
    by_cases inside : index + intOfZ (Int.unsigned amount) < 64
    · have inside' : index + (intOfZ (Int.unsigned amount) - 32) < 32 := by omega
      simp only [inside, inside', ↓reduceIte]
      rw [manual_int64_ofwords_bits _ _ _ (by omega)]
      have upper_word : ¬index + intOfZ (Int.unsigned amount) < 32 := by omega
      simp only [upper_word, ↓reduceIte]
      congr 2
      omega
    · have outside : ¬index + (intOfZ (Int.unsigned amount) - 32) < 32 := by omega
      simp only [inside, outside, ↓reduceIte]
  · have outside : ¬index + intOfZ (Int.unsigned amount) < 64 := by omega
    simp only [lower, outside, ↓reduceIte]
    exact (Int.bits_zero_proof _).symm

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem remaining_int32_shr_bits (value amount : Int.int) (index : _root_.Int)
    (bounds : 0 ≤ index ∧ index < 32) :
    Int.testbit (Int.shr value amount) (zOfInt index) =
      Int.testbit value (zOfInt (min (index + intOfZ (Int.unsigned amount)) 31)) := by
  have encoded_bounds : zLe zZero (zOfInt index) ∧ zLt (zOfInt index) Int.zwordsize := by
    change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 32
    simpa only [intOfZ_zOfInt] using bounds
  have law := Int.bits_shr_proof value amount _ encoded_bounds
  change Int.testbit (Int.shr value amount) (zOfInt index) =
    Int.testbit value (zltSelect (zAdd (zOfInt index) (Int.unsigned amount)) Int.zwordsize
      (zAdd (zOfInt index) (Int.unsigned amount)) (zSub Int.zwordsize zOne)) at law
  rw [law, manual_int64_zlt_select]
  simp only [zAdd, ZArith.BinInt.Z.add, zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  change Int.testbit value
    (if index + intOfZ (Int.unsigned amount) < 32 then
      zOfInt (index + intOfZ (Int.unsigned amount)) else zOfInt 31) = _
  apply congrArg (Int.testbit value)
  split <;> apply congrArg zOfInt <;> omega

private theorem remaining_int64_shr_prime_bits (value : int) (amount : Int.int)
    (index : _root_.Int) (bounds : 0 ≤ index ∧ index < 64) :
    testbit (shr' value amount) (zOfInt index) =
      testbit value (zOfInt (min (index + intOfZ (Int.unsigned amount)) 63)) := by
  have encoded_bounds : zLe zZero (zOfInt index) ∧ zLt (zOfInt index) zwordsize := by
    change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 64
    simpa only [intOfZ_zOfInt] using bounds
  rw [bits_shr'_proof value amount _ encoded_bounds, manual_int64_zlt_select]
  simp only [zAdd, ZArith.BinInt.Z.add, zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  change testbit value
    (if index + intOfZ (Int.unsigned amount) < 64 then
      zOfInt (index + intOfZ (Int.unsigned amount)) else zOfInt 63) = _
  apply congrArg (testbit value)
  split <;> apply congrArg zOfInt <;> omega

theorem decompose_shr_2_proof : decompose_shr_2 := by
  intro high low amount amount_bounds
  have amount_lower : 32 ≤ intOfZ (Int.unsigned amount) := amount_bounds.1
  have amount_upper : intOfZ (Int.unsigned amount) < 64 := amount_bounds.2
  have difference := manual_int64_sub32_unsigned amount Int.iwordsize (by
    change 0 ≤ intOfZ (Int.unsigned amount) - 32 ∧
      intOfZ (Int.unsigned amount) - 32 ≤ 4294967295
    omega)
  have difference_value : intOfZ (Int.unsigned (Int.sub amount Int.iwordsize)) =
      intOfZ (Int.unsigned amount) - 32 := by
    rw [difference]
    simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
    rfl
  have sign_shift : intOfZ (Int.unsigned (Int.sub Int.iwordsize Int.one)) = 31 := by
    decide
  apply same_bits_eq_proof
  intro encoded index_bounds
  let index := intOfZ encoded
  have index_bounds' : 0 ≤ index ∧ index < 64 := index_bounds
  have encoding : encoded = zOfInt index := (zOfInt_intOfZ encoded).symm
  rw [encoding, remaining_int64_shr_prime_bits _ _ _ index_bounds',
    manual_int64_ofwords_bits _ _ _ (by omega),
    manual_int64_ofwords_bits _ _ _ index_bounds']
  have upper_word : ¬min (index + intOfZ (Int.unsigned amount)) 63 < 32 := by omega
  simp only [upper_word, ↓reduceIte]
  by_cases lower : index < 32
  · simp only [lower, ↓reduceIte]
    rw [remaining_int32_shr_bits _ _ _ (by omega), difference_value]
    congr 2
    omega
  · simp only [lower, ↓reduceIte]
    rw [remaining_int32_shr_bits _ _ _ (by omega), sign_shift]
    congr 2
    omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem remaining_int32_or_bits (left right : Int.int) (index : _root_.Int)
    (bounds : 0 ≤ index ∧ index < 32) :
    Int.testbit (Int.or left right) (zOfInt index) =
      (Int.testbit left (zOfInt index) || Int.testbit right (zOfInt index)) := by
  apply Int.bits_or_proof
  change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 32
  simpa only [intOfZ_zOfInt] using bounds

private theorem remaining_int32_complement (amount : Int.int)
    (bounds : 0 ≤ intOfZ (Int.unsigned amount) ∧ intOfZ (Int.unsigned amount) ≤ 32) :
    intOfZ (Int.unsigned (Int.sub Int.iwordsize amount)) =
      32 - intOfZ (Int.unsigned amount) := by
  have difference := manual_int64_sub32_unsigned Int.iwordsize amount (by
    change 0 ≤ 32 - intOfZ (Int.unsigned amount) ∧
      32 - intOfZ (Int.unsigned amount) ≤ 4294967295
    omega)
  rw [difference]
  simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  rfl

theorem decompose_shru_1_proof : decompose_shru_1 := by
  intro high low amount amount_bounds
  have amount_lower : 0 ≤ intOfZ (Int.unsigned amount) := amount_bounds.1
  have amount_upper : intOfZ (Int.unsigned amount) < 32 := amount_bounds.2
  have complement := remaining_int32_complement amount (by omega)
  apply same_bits_eq_proof
  intro encoded index_bounds
  let index := intOfZ encoded
  have index_bounds' : 0 ≤ index ∧ index < 64 := index_bounds
  have encoding : encoded = zOfInt index := (zOfInt_intOfZ encoded).symm
  rw [encoding, remaining_int64_shru_prime_bits _ _ _ index_bounds',
    manual_int64_ofwords_bits _ _ _ index_bounds']
  by_cases lower : index < 32
  · have inside : index + intOfZ (Int.unsigned amount) < 64 := by omega
    simp only [lower, inside, ↓reduceIte]
    rw [manual_int64_ofwords_bits _ _ _ (by omega),
      remaining_int32_or_bits _ _ _ (by omega),
      remaining_int32_shru_bits _ _ _ (by omega),
      manual_int32_shl_bits _ _ _ (by omega), complement]
    by_cases low_source : index + intOfZ (Int.unsigned amount) < 32
    · have before_shift : index < 32 - intOfZ (Int.unsigned amount) := by omega
      simp only [low_source, before_shift, ↓reduceIte, Bool.or_false]
    · have after_shift : ¬index < 32 - intOfZ (Int.unsigned amount) := by omega
      simp only [low_source, after_shift, ↓reduceIte, Bool.false_or]
      congr 2
      omega
  · simp only [lower, ↓reduceIte]
    rw [remaining_int32_shru_bits _ _ _ (by omega)]
    by_cases inside : index + intOfZ (Int.unsigned amount) < 64
    · have inside' : index - 32 + intOfZ (Int.unsigned amount) < 32 := by omega
      simp only [inside, inside', ↓reduceIte]
      rw [manual_int64_ofwords_bits _ _ _ (by omega)]
      have high_source : ¬index + intOfZ (Int.unsigned amount) < 32 := by omega
      simp only [high_source, ↓reduceIte]
      congr 2
      omega
    · have outside : ¬index - 32 + intOfZ (Int.unsigned amount) < 32 := by omega
      simp only [inside, outside, ↓reduceIte]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem decompose_shl_1_proof : decompose_shl_1 := by
  intro high low amount amount_bounds
  have amount_lower : 0 ≤ intOfZ (Int.unsigned amount) := amount_bounds.1
  have amount_upper : intOfZ (Int.unsigned amount) < 32 := amount_bounds.2
  have complement := remaining_int32_complement amount (by omega)
  apply same_bits_eq_proof
  intro encoded index_bounds
  let index := intOfZ encoded
  have index_bounds' : 0 ≤ index ∧ index < 64 := index_bounds
  have encoding : encoded = zOfInt index := (zOfInt_intOfZ encoded).symm
  rw [encoding, manual_int64_shl_prime_bits _ _ _ index_bounds',
    manual_int64_ofwords_bits _ _ _ index_bounds']
  by_cases lower : index < 32
  · simp only [lower, ↓reduceIte]
    rw [manual_int32_shl_bits _ _ _ (by omega)]
    by_cases before_shift : index < intOfZ (Int.unsigned amount)
    · simp only [before_shift, ↓reduceIte]
    · simp only [before_shift, ↓reduceIte]
      rw [manual_int64_ofwords_bits _ _ _ (by omega)]
      have low_source : index - intOfZ (Int.unsigned amount) < 32 := by omega
      simp only [low_source, ↓reduceIte]
  · have after_shift : ¬index < intOfZ (Int.unsigned amount) := by omega
    simp only [lower, after_shift, ↓reduceIte]
    rw [manual_int64_ofwords_bits _ _ _ (by omega),
      remaining_int32_or_bits _ _ _ (by omega),
      manual_int32_shl_bits _ _ _ (by omega),
      remaining_int32_shru_bits _ _ _ (by omega), complement]
    by_cases low_source : index - intOfZ (Int.unsigned amount) < 32
    · have before_high_shift : index - 32 < intOfZ (Int.unsigned amount) := by omega
      have inside_low : index - 32 + (32 - intOfZ (Int.unsigned amount)) < 32 := by omega
      simp only [low_source, before_high_shift, inside_low, ↓reduceIte, Bool.false_or]
      congr 2
      omega
    · have after_high_shift : ¬index - 32 < intOfZ (Int.unsigned amount) := by omega
      have outside_low : ¬index - 32 + (32 - intOfZ (Int.unsigned amount)) < 32 := by omega
      simp only [low_source, after_high_shift, outside_low, ↓reduceIte, Bool.or_false]
      congr 2
      omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem decompose_shr_1_proof : decompose_shr_1 := by
  intro high low amount amount_bounds
  have amount_lower : 0 ≤ intOfZ (Int.unsigned amount) := amount_bounds.1
  have amount_upper : intOfZ (Int.unsigned amount) < 32 := amount_bounds.2
  have complement := remaining_int32_complement amount (by omega)
  apply same_bits_eq_proof
  intro encoded index_bounds
  let index := intOfZ encoded
  have index_bounds' : 0 ≤ index ∧ index < 64 := index_bounds
  have encoding : encoded = zOfInt index := (zOfInt_intOfZ encoded).symm
  rw [encoding, remaining_int64_shr_prime_bits _ _ _ index_bounds',
    manual_int64_ofwords_bits _ _ _ (by omega),
    manual_int64_ofwords_bits _ _ _ index_bounds']
  by_cases lower : index < 32
  · have unclamped : min (index + intOfZ (Int.unsigned amount)) 63 =
        index + intOfZ (Int.unsigned amount) := by omega
    rw [unclamped]
    simp only [lower, ↓reduceIte]
    rw [remaining_int32_or_bits _ _ _ (by omega),
      remaining_int32_shru_bits _ _ _ (by omega),
      manual_int32_shl_bits _ _ _ (by omega), complement]
    by_cases low_source : index + intOfZ (Int.unsigned amount) < 32
    · have before_shift : index < 32 - intOfZ (Int.unsigned amount) := by omega
      simp only [low_source, before_shift, ↓reduceIte, Bool.or_false]
    · have after_shift : ¬index < 32 - intOfZ (Int.unsigned amount) := by omega
      simp only [low_source, after_shift, ↓reduceIte, Bool.false_or]
      congr 2
      omega
  · have high_source : ¬min (index + intOfZ (Int.unsigned amount)) 63 < 32 := by omega
    simp only [lower, high_source, ↓reduceIte]
    rw [remaining_int32_shr_bits _ _ _ (by omega)]
    congr 2
    omega

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem remaining_sign_ext_bits (width : Z) (value : int) (index : _root_.Int)
    (bounds : 0 ≤ index ∧ index < 32) :
    testbit (sign_ext width value) (zOfInt index) =
      testbit value (zOfInt (min index (intOfZ width - 1))) := by
  have encoded_bounds : zLe zZero (zOfInt index) ∧ zLt (zOfInt index) zwordsize := by
    change 0 ≤ intOfZ (zOfInt index) ∧ intOfZ (zOfInt index) < 32
    simpa only [intOfZ_zOfInt] using bounds
  rw [bits_sign_ext_proof width value _ encoded_bounds, Int64.manual_int64_zlt_select]
  simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
  change testbit value
    (if index < intOfZ width then zOfInt index else zOfInt (intOfZ width - 1)) = _
  apply congrArg (testbit value)
  split <;> apply congrArg zOfInt <;> omega

theorem signed_bitfield_extract_by_shifts_proof : signed_bitfield_extract_by_shifts := by
  intro position width value position_nonnegative width_positive total_bound
  have position_bound : 0 ≤ intOfZ position := position_nonnegative
  have width_bound : 0 < intOfZ width := width_positive
  have total : intOfZ position + intOfZ width ≤ 32 := by
    change intOfZ (zAdd position width) ≤ 32 at total_bound
    simpa only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt] using total_bound
  have position_repr : unsigned (repr position) = position :=
    unsigned_repr_proof_api position (by
      change 0 ≤ intOfZ position ∧ intOfZ position ≤ 4294967295
      omega)
  have left_repr : intOfZ (unsigned (repr (zSub (zSub zwordsize position) width))) =
      32 - intOfZ position - intOfZ width := by
    rw [unsigned_repr_proof_api]
    · simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      rfl
    · change 0 ≤ intOfZ (zSub (zSub zwordsize position) width) ∧
        intOfZ (zSub (zSub zwordsize position) width) ≤ 4294967295
      simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      change 0 ≤ 32 - intOfZ position - intOfZ width ∧
        32 - intOfZ position - intOfZ width ≤ 4294967295
      omega
  have right_repr : intOfZ (unsigned (repr (zSub zwordsize width))) =
      32 - intOfZ width := by
    rw [unsigned_repr_proof_api]
    · simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      rfl
    · change 0 ≤ intOfZ (zSub zwordsize width) ∧
        intOfZ (zSub zwordsize width) ≤ 4294967295
      simp only [zSub, ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      change 0 ≤ 32 - intOfZ width ∧ 32 - intOfZ width ≤ 4294967295
      omega
  apply same_bits_eq_proof
  intro encoded index_bounds
  let index := intOfZ encoded
  have bounds : 0 ≤ index ∧ index < 32 := index_bounds
  have encoding : encoded = zOfInt index := (zOfInt_intOfZ encoded).symm
  change testbit (sign_ext width (shru value (repr position))) encoded = _
  rw [encoding, remaining_sign_ext_bits _ _ _ bounds,
    Int64.remaining_int32_shru_bits _ _ _ (by omega), position_repr,
    Int64.remaining_int32_shr_bits _ _ _ bounds, right_repr,
    Int64.manual_int32_shl_bits _ _ _ (by omega), left_repr]
  have source_inside : min index (intOfZ width - 1) + intOfZ position < 32 := by omega
  have shifted_inside : ¬min (index + (32 - intOfZ width)) 31 <
      32 - intOfZ position - intOfZ width := by omega
  simp only [source_inside, shifted_inside, ↓reduceIte]
  congr 2
  omega

end CompCert4Lean.Lib.Integers.Int

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem remaining_int64_repr_nat (value : Nat) :
    (repr (zOfNat value)).val = value % (2 ^ wordsize) := by
  change (WordCore.repr wordsize (zOfInt (_root_.Int.ofNat value))).val = _
  rw [WordCore.val_repr_residue, WordCore.residue_zOfNat]

theorem shifted_or_is_add_proof : shifted_or_is_add := by
  intro value low amount amount_bounds low_small
  have amount_unsigned : unsigned (repr amount) = amount := by
    apply unsigned_repr_proof
    refine ⟨amount_bounds.1, ?_⟩
    have upper : intOfZ amount < 64 := amount_bounds.2
    change intOfZ amount ≤ 18446744073709551615
    omega
  have amount_value : (repr amount).val = zToNat amount := congrArg zToNat amount_unsigned
  have power := Int.suffix_two_p_nonneg amount amount_bounds.1
  have low_bound : low.val < 2 ^ zToNat amount := by
    have numeric : intOfZ (unsigned low) < intOfZ (zTwoP amount) := low_small
    rw [manual_int64_unsigned_as_nat, power] at numeric
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at numeric
    exact _root_.Int.ofNat_lt.mp numeric
  have arithmetic_encoding :
      zAdd (zMul (unsigned value) (zTwoP amount)) (unsigned low) =
        zOfNat (value.val * 2 ^ zToNat amount + low.val) := by
    apply intOfZ_injective
    rw [manual_int64_unsigned_as_nat, manual_int64_unsigned_as_nat, power]
    simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul,
      zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      _root_.Int.ofNat_eq_natCast, _root_.Int.natCast_add, _root_.Int.natCast_mul]
  apply WordCore.ext_of_val_eq
  rw [manual_int64_or_val, manual_int64_shl_val, amount_value,
    arithmetic_encoding, remaining_int64_repr_nat, Nat.lor_eq]
  have disjoint : value.val * 2 ^ zToNat amount + low.val =
      value.val * 2 ^ zToNat amount ||| low.val := by
    simpa only [Nat.mul_comm] using Nat.two_pow_add_eq_or_of_lt low_bound value.val
  rw [disjoint, Nat.or_mod_two_pow, Nat.mod_eq_of_lt (WordCore.val_lt low)]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem remaining_int64_signed_mone : signed mone = zOpp zOne := by
  apply signed_repr_proof
  change (-9223372036854775808 : _root_.Int) ≤ -1 ∧ (-1 : _root_.Int) ≤ 9223372036854775807
  decide

private theorem remaining_int64_sign_extend_value (value : int) :
    zAdd (zMul (signed (if lt value zero then mone else zero)) modulus)
      (unsigned value) = signed value := by
  rw [manual_int64_negative_unsigned]
  apply intOfZ_injective
  by_cases negative : 9223372036854775808 ≤ intOfZ (unsigned value)
  · simp only [negative, decide_true, ↓reduceIte]
    simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    rw [remaining_int64_signed_mone, manual_int64_signed_int value, if_neg (by omega)]
    change -1 * 18446744073709551616 + intOfZ (unsigned value) =
      intOfZ (unsigned value) - 18446744073709551616
    omega
  · simp only [negative, decide_false, Bool.false_eq_true, ↓reduceIte]
    simp only [zAdd, zMul, ZArith.BinInt.Z.add, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    rw [signed_zero_proof, manual_int64_signed_int value, if_pos (by omega)]
    change 0 * 18446744073709551616 + intOfZ (unsigned value) = intOfZ (unsigned value)
    omega

private theorem remaining_int64_quotient_bounds (numerator denominator : int)
    (nonzero : denominator ≠ zero)
    (safe : numerator ≠ repr min_signed ∨ denominator ≠ mone) :
    zLe min_signed (zQuot (signed numerator) (signed denominator)) ∧
      zLe (zQuot (signed numerator) (signed denominator)) max_signed := by
  let dividend := intOfZ (signed numerator)
  let divisor := intOfZ (signed denominator)
  have bounds : -9223372036854775808 ≤ dividend ∧ dividend ≤ 9223372036854775807 :=
    signed_range_proof numerator
  have divisor_nonzero : divisor ≠ 0 := by
    intro contradiction
    apply nonzero
    rw [← repr_signed_proof denominator]
    have signed_zero : signed denominator = zZero := intOfZ_injective contradiction
    rw [signed_zero]
    rfl
  have overflow_excluded : dividend ≠ -9223372036854775808 ∨ divisor ≠ -1 := by
    rcases safe with numerator_safe | denominator_safe
    · left
      intro contradiction
      apply numerator_safe
      rw [← repr_signed_proof numerator]
      exact congrArg repr (intOfZ_injective contradiction)
    · right
      intro contradiction
      apply denominator_safe
      rw [← repr_signed_proof denominator]
      have signed_mone : signed denominator = signed mone := by
        rw [remaining_int64_signed_mone]
        exact intOfZ_injective contradiction
      rw [signed_mone, repr_signed_proof]
  change -9223372036854775808 ≤ intOfZ (zQuot (signed numerator) (signed denominator)) ∧
    intOfZ (zQuot (signed numerator) (signed denominator)) ≤ 9223372036854775807
  simp only [zQuot, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
  change -9223372036854775808 ≤ dividend.tdiv divisor ∧
    dividend.tdiv divisor ≤ 9223372036854775807
  by_cases positive_one : divisor = 1
  · simp only [positive_one, _root_.Int.tdiv_one]
    exact bounds
  by_cases negative_one : divisor = -1
  · have numerator_safe : dividend ≠ -9223372036854775808 := by omega
    simp only [negative_one, _root_.Int.tdiv_neg, _root_.Int.tdiv_one]
    omega
  have divisor_abs : 2 ≤ divisor.natAbs := by omega
  have dividend_abs : dividend.natAbs ≤ 9223372036854775808 := by omega
  have quotient_abs : (dividend.tdiv divisor).natAbs ≤ 4611686018427387904 := by
    rw [_root_.Int.natAbs_tdiv]
    calc
      dividend.natAbs / divisor.natAbs ≤ dividend.natAbs / 2 :=
        Nat.div_le_div_left divisor_abs (by decide)
      _ ≤ 9223372036854775808 / 2 := Nat.div_le_div_right dividend_abs
  omega

theorem divmods2_divs_mods_proof : divmods2_divs_mods := by
  intro numerator denominator nonzero safe
  unfold divmods2 divs mods
  simp only [eq_dec, dif_neg nonzero]
  rw [remaining_int64_sign_extend_value]
  have bounds := remaining_int64_quotient_bounds numerator denominator nonzero safe
  cases lower : CompCert4Lean.Lib.Coqlib.zle
      min_signed (zQuot (signed numerator) (signed denominator)) with
  | left lower_bound =>
      cases upper : CompCert4Lean.Lib.Coqlib.zle
          (zQuot (signed numerator) (signed denominator)) max_signed with
      | left upper_bound => rfl
      | right contradiction =>
          have upper_bound : intOfZ (zQuot (signed numerator) (signed denominator)) ≤
              intOfZ max_signed := bounds.2
          exact (_root_.Int.not_lt_of_ge upper_bound contradiction).elim
  | right contradiction =>
      have lower_bound : intOfZ min_signed ≤
          intOfZ (zQuot (signed numerator) (signed denominator)) := bounds.1
      exact (_root_.Int.not_lt_of_ge lower_bound contradiction).elim

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem remaining_int64_mul_val (left right : int) :
    (mul left right).val = (left.val * right.val) % (2 ^ wordsize) := by
  change (WordCore.mul left right).val = (left.val * right.val) % (2 ^ wordsize)
  apply _root_.Int.ofNat.inj
  rw [suffix_int64_wordcore_mul_val]
  simp only [_root_.Int.ofNat_eq_natCast, _root_.Int.natCast_mul, _root_.Int.natCast_emod]

private theorem remaining_int32_repr_nat (value : Nat) :
    (Int.repr (zOfNat value)).val = value % 4294967296 := by
  change (WordCore.repr Int.wordsize (zOfInt (_root_.Int.ofNat value))).val = _
  rw [WordCore.val_repr_residue, WordCore.residue_zOfNat]
  rfl

private theorem remaining_int64_loword_val (value : int) :
    (loword value).val = value.val % 4294967296 := by
  unfold loword
  rw [manual_int64_unsigned_as_nat, remaining_int32_repr_nat]

private theorem remaining_int64_hiword_val (value : int) :
    (hiword value).val = value.val / 4294967296 := by
  unfold hiword
  rw [manual_int64_unsigned_as_nat, remaining_int32_repr_nat, manual_int64_shru_val]
  change (value.val / 4294967296) % 4294967296 = value.val / 4294967296
  have bounds := WordCore.val_lt value
  change value.val < 18446744073709551616 at bounds
  apply Nat.mod_eq_of_lt
  omega

private theorem remaining_int64_mul_prime_val (left right : Int.int) :
    (mul' left right).val = left.val * right.val := by
  have encoding : zMul (Int.unsigned left) (Int.unsigned right) =
      zOfNat (left.val * right.val) := by
    apply intOfZ_injective
    rw [show Int.unsigned left = zOfNat left.val from WordCore.intval_eq_zOfNat_val left,
      show Int.unsigned right = zOfNat right.val from WordCore.intval_eq_zOfNat_val right]
    simp only [zMul, ZArith.BinInt.Z.mul, zOfNat, ZArith.BinInt.Z.of_nat,
      intOfZ_zOfInt, _root_.Int.ofNat_eq_natCast, _root_.Int.natCast_mul]
  unfold mul'
  rw [encoding, remaining_int64_repr_nat]
  apply Nat.mod_eq_of_lt
  have left_bound := WordCore.val_lt left
  have right_bound := WordCore.val_lt right
  change left.val < 4294967296 at left_bound
  change right.val < 4294967296 at right_bound
  exact Nat.lt_of_le_of_lt
    (Nat.mul_le_mul (by omega : left.val ≤ 4294967295)
      (by omega : right.val ≤ 4294967295)) (by decide)

private theorem remaining_int64_product_digits
    (high_left low_left high_right low_right : Nat) :
    ((high_left * 4294967296 + low_left) *
      (high_right * 4294967296 + low_right)) % 18446744073709551616 =
      ((low_left * low_right / 4294967296 + low_left * high_right +
        high_left * low_right) % 4294967296) * 4294967296 +
        (low_left * low_right) % 4294967296 := by
  have expansion :
      (high_left * 4294967296 + low_left) * (high_right * 4294967296 + low_right) =
        low_left * low_right + 4294967296 *
          (high_left * high_right * 4294967296 + low_left * high_right +
            high_left * low_right) := by
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    ac_rfl
  rw [expansion, Nat.mod_mul (a := 4294967296) (b := 4294967296),
    Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by decide)]
  have regroup :
      low_left * low_right / 4294967296 +
          (high_left * high_right * 4294967296 + low_left * high_right + high_left * low_right) =
        (low_left * low_right / 4294967296 + low_left * high_right + high_left * low_right) +
          (high_left * high_right) * 4294967296 := by omega
  rw [regroup, Nat.add_mul_mod_self_right]
  omega

theorem decompose_mul_proof : decompose_mul := by
  intro high_left low_left high_right low_right
  apply WordCore.ext_of_val_eq
  rw [remaining_int64_mul_val, manual_int64_ofwords_val,
    manual_int64_ofwords_val, manual_int64_ofwords_val]
  simp only [Int.add, Int.mul, WordCore.add_val, Int.suffix_wordcore_mul_val_nat,
    remaining_int64_hiword_val, remaining_int64_loword_val, remaining_int64_mul_prime_val]
  change ((high_left.val * 4294967296 + low_left.val) *
      (high_right.val * 4294967296 + low_right.val)) % 18446744073709551616 =
    (((low_left.val * low_right.val / 4294967296 +
      (low_left.val * high_right.val) % 4294967296) % 4294967296 +
      (high_left.val * low_right.val) % 4294967296) % 4294967296) * 4294967296 +
      (low_left.val * low_right.val) % 4294967296
  simp only [Nat.add_mod_mod, Nat.mod_add_mod]
  exact remaining_int64_product_digits _ _ _ _

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

private theorem remaining_int64_shr_as_int (value amount : int) :
    shr value amount = repr (zOfInt
      (intOfZ (signed value) / _root_.Int.ofNat (2 ^ amount.val))) := by
  change repr (zShiftr (signed value) (unsigned amount)) = _
  rw [manual_int64_unsigned_as_nat]
  simp only [zShiftr, ZArith.BinInt.Z.shiftr, zOfNat, ZArith.BinInt.Z.of_nat,
    intOfZ_zOfInt, _root_.Int.ofNat_eq_natCast, _root_.Int.natCast_nonneg,
    ↓reduceIte, _root_.Int.toNat_natCast, _root_.Int.natCast_pow]
  rfl

private theorem remaining_int64_sign_shift (value : int) :
    shr value (repr (zSub zwordsize zOne)) =
      if intOfZ (signed value) < 0 then mone else zero := by
  rw [remaining_int64_shr_as_int]
  have shift_value : (repr (zSub zwordsize zOne)).val = 63 := by rfl
  rw [shift_value]
  have bounds : -9223372036854775808 ≤ intOfZ (signed value) ∧
      intOfZ (signed value) ≤ 9223372036854775807 := signed_range_proof value
  by_cases negative : intOfZ (signed value) < 0
  · rw [if_pos negative]
    have quotient : intOfZ (signed value) / _root_.Int.ofNat (2 ^ 63) = -1 := by
      change intOfZ (signed value) / 9223372036854775808 = -1
      omega
    rw [quotient]
    rfl
  · rw [if_neg negative]
    have quotient : intOfZ (signed value) / _root_.Int.ofNat (2 ^ 63) = 0 := by
      change intOfZ (signed value) / 9223372036854775808 = 0
      omega
    rw [quotient]
    rfl

private theorem remaining_int64_complement_val (amount : int) (small : amount.val < 63) :
    (sub iwordsize amount).val = 64 - amount.val := by
  change (WordCore.sub iwordsize amount).val = _
  rw [WordCore.sub_val]
  change (18446744073709551616 - amount.val + 64) % 18446744073709551616 = 64 - amount.val
  have regroup : 18446744073709551616 - amount.val + 64 =
      18446744073709551616 + (64 - amount.val) := by omega
  rw [regroup, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

private theorem remaining_int64_mask_division (amount : Nat) (small : amount ≤ 64) :
    (2 ^ 64 - 1) / 2 ^ (64 - amount) = 2 ^ amount - 1 := by
  apply Nat.eq_of_testBit_eq
  intro index
  rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  apply decide_eq_decide.mpr
  omega

private theorem remaining_int64_signed_add_bias (value : int) (bias : Nat)
    (small : bias ≤ 9223372036854775807) (negative : intOfZ (signed value) < 0) :
    signed (add value (repr (zOfNat bias))) = zAdd (signed value) (zOfNat bias) := by
  have bias_signed : signed (repr (zOfNat bias)) = zOfNat bias := by
    apply signed_repr_proof
    change -9223372036854775808 ≤ intOfZ (zOfNat bias) ∧
      intOfZ (zOfNat bias) ≤ 9223372036854775807
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, _root_.Int.ofNat_eq_natCast]
    omega
  rw [add_signed_proof, bias_signed]
  apply signed_repr_proof
  have bounds : -9223372036854775808 ≤ intOfZ (signed value) ∧
      intOfZ (signed value) ≤ 9223372036854775807 := signed_range_proof value
  change -9223372036854775808 ≤ intOfZ (zAdd (signed value) (zOfNat bias)) ∧
    intOfZ (zAdd (signed value) (zOfNat bias)) ≤ 9223372036854775807
  simp only [zAdd, ZArith.BinInt.Z.add, zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
    _root_.Int.ofNat_eq_natCast]
  omega

theorem shrx_shr_2_proof : shrx_shr_2 := by
  intro value amount amount_small
  have upper := (ltu_inv_proof amount (repr (zSub zwordsize zOne)) amount_small).2
  change intOfZ (unsigned amount) < 63 at upper
  rw [manual_int64_unsigned_as_nat] at upper
  simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt] at upper
  have count_upper : amount.val < 63 := _root_.Int.ofNat_lt.mp upper
  have power_bound : 2 ^ amount.val ≤ 4611686018427387904 := by
    exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega : amount.val ≤ 62)
  have power_positive := Nat.two_pow_pos amount.val
  have shift_one : shl one amount = repr (zOfNat (2 ^ amount.val)) := by
    apply WordCore.ext_of_val_eq
    rw [manual_int64_shl_val, remaining_int64_repr_nat]
    simp only [show one.val = 1 from rfl, Nat.one_mul]
  have power_signed : signed (shl one amount) = zOfNat (2 ^ amount.val) := by
    rw [shift_one]
    apply signed_repr_proof
    change -9223372036854775808 ≤ intOfZ (zOfNat (2 ^ amount.val)) ∧
      intOfZ (zOfNat (2 ^ amount.val)) ≤ 9223372036854775807
    simp only [zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, _root_.Int.ofNat_eq_natCast]
    omega
  have correction :
      shru (shr value (repr (zSub zwordsize zOne))) (sub iwordsize amount) =
        if intOfZ (signed value) < 0 then repr (zOfNat (2 ^ amount.val - 1)) else zero := by
    rw [remaining_int64_sign_shift]
    split
    · apply WordCore.ext_of_val_eq
      rw [manual_int64_shru_val, remaining_int64_complement_val amount count_upper,
        remaining_int64_repr_nat]
      have mone_value : mone.val = 2 ^ 64 - 1 := by rfl
      rw [mone_value, remaining_int64_mask_division _ (by omega)]
      symm
      apply Nat.mod_eq_of_lt
      change 2 ^ amount.val - 1 < 18446744073709551616
      omega
    · apply WordCore.ext_of_val_eq
      rw [manual_int64_shru_val]
      change 0 / 2 ^ (sub iwordsize amount).val = 0
      exact Nat.zero_div _
  change repr (zQuot (signed value) (signed (shl one amount))) = _
  rw [power_signed, correction]
  have quotient_encoding : zQuot (signed value) (zOfNat (2 ^ amount.val)) =
      zOfInt ((intOfZ (signed value)).tdiv (_root_.Int.ofNat (2 ^ amount.val))) := by
    simp only [zQuot, ZArith.BinInt.Z.quot, zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
  rw [quotient_encoding]
  have power_positive_int : 0 < _root_.Int.ofNat (2 ^ amount.val) :=
    _root_.Int.ofNat_lt.mpr power_positive
  by_cases negative : intOfZ (signed value) < 0
  · simp only [negative, ↓reduceIte]
    rw [remaining_int64_shr_as_int,
      remaining_int64_signed_add_bias value (2 ^ amount.val - 1) (by omega) negative]
    simp only [zAdd, ZArith.BinInt.Z.add, zOfNat, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt]
    rw [Int.suffix_tdiv_adjust _ _ power_positive_int, if_pos negative]
    have bias_cast : _root_.Int.ofNat (2 ^ amount.val - 1) =
        _root_.Int.ofNat (2 ^ amount.val) - 1 :=
      _root_.Int.ofNat_sub (by omega)
    rw [bias_cast]
    congr 3
    omega
  · simp only [negative, ↓reduceIte]
    rw [add_zero_proof, remaining_int64_shr_as_int,
      Int.suffix_tdiv_adjust _ _ power_positive_int, if_neg negative]

end CompCert4Lean.Lib.Integers.Int64

namespace CompCert4Lean.Lib.Integers.Int64

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem shrx'_shr_2_proof : shrx'_shr_2 := by
  intro value amount amount_small
  have amount_bounds := Int.ltu_inv_proof amount (Int.repr (zOfNat 63)) amount_small
  have amount_lower : 0 ≤ intOfZ (Int.unsigned amount) := amount_bounds.1
  have amount_upper : intOfZ (Int.unsigned amount) < 63 := amount_bounds.2
  have widened_small :
      ltu (repr (Int.unsigned amount)) (repr (zSub zwordsize zOne)) = true := by
    change zltSelect (unsigned (repr (Int.unsigned amount)))
      (unsigned (repr (zSub zwordsize zOne))) true false = true
    rw [manual_int64_widen_unsigned, manual_int64_zlt_bool]
    apply decide_eq_true
    exact amount_upper
  have complement_unsigned := manual_int64_sub32_unsigned (Int.repr (zOfNat 64)) amount (by
    change 0 ≤ 64 - intOfZ (Int.unsigned amount) ∧
      64 - intOfZ (Int.unsigned amount) ≤ 4294967295
    omega)
  have complement : sub iwordsize (repr (Int.unsigned amount)) =
      repr (Int.unsigned (Int.sub (Int.repr (zOfNat 64)) amount)) := by
    rw [complement_unsigned]
    change repr (zSub (unsigned iwordsize) (unsigned (repr (Int.unsigned amount)))) =
      repr (zSub (Int.unsigned (Int.repr (zOfNat 64))) (Int.unsigned amount))
    rw [manual_int64_widen_unsigned]
    rfl
  have last_unsigned : Int.unsigned (Int.repr (zOfNat 63)) = zSub zwordsize zOne := by rfl
  change divs value (shl' one amount) = _
  rw [manual_int64_shl_prime]
  change shrx value (repr (Int.unsigned amount)) = _
  rw [shrx_shr_2_proof _ _ widened_small]
  simp only [manual_int64_shr_prime, manual_int64_shru_prime]
  rw [last_unsigned, ← complement]

end CompCert4Lean.Lib.Integers.Int64
