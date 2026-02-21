import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.RingTheory.Int.Basic

namespace FUST.FrourioAlgebra

/-!
# Golden Valuation and Non-Decreasing Property

This file formalizes the valuation non-decreasing property for the two-point
scale difference operator Δ_{α,β,ε} over the golden integer ring.
-/

open scoped BigOperators

/-!
## Golden Integer Ring

The ring O = Z[φ] of integers in Q(φ), where φ = (1 + √5)/2.
-/

/-- The golden integer ring O = Z[φ].
    Elements are of the form a + bφ where a, b ∈ Z. -/
structure GoldenInt where
  a : ℤ
  b : ℤ
deriving DecidableEq, Repr

namespace GoldenInt

/-- Zero element -/
def zero : GoldenInt := ⟨0, 0⟩

/-- One element -/
def one : GoldenInt := ⟨1, 0⟩

/-- The golden ratio φ as an element of O -/
def phi : GoldenInt := ⟨0, 1⟩

/-- Addition in O -/
def add (x y : GoldenInt) : GoldenInt := ⟨x.a + y.a, x.b + y.b⟩

/-- Negation in O -/
def neg (x : GoldenInt) : GoldenInt := ⟨-x.a, -x.b⟩

/-- Subtraction in O -/
def sub (x y : GoldenInt) : GoldenInt := add x (neg y)

/-- Multiplication in O using φ² = φ + 1 -/
def mul (x y : GoldenInt) : GoldenInt :=
  -- (a + bφ)(c + dφ) = ac + (ad + bc)φ + bdφ²
  -- = ac + (ad + bc)φ + bd(φ + 1)
  -- = (ac + bd) + (ad + bc + bd)φ
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

instance : Zero GoldenInt := ⟨zero⟩
instance : One GoldenInt := ⟨one⟩
instance : Add GoldenInt := ⟨add⟩
instance : Neg GoldenInt := ⟨neg⟩
instance : Sub GoldenInt := ⟨sub⟩
instance : Mul GoldenInt := ⟨mul⟩

/-- The norm N(a + bφ) = a² + ab - b² -/
def norm (x : GoldenInt) : ℤ := x.a^2 + x.a * x.b - x.b^2

/-- The trace Tr(a + bφ) = 2a + b -/
def trace (x : GoldenInt) : ℤ := 2 * x.a + x.b

/-- Galois conjugate: a + bφ ↦ a + bψ = (a + b) - bφ
    where ψ = (1 - √5)/2 = 1 - φ -/
def conj (x : GoldenInt) : GoldenInt := ⟨x.a + x.b, -x.b⟩

/-- An element is a unit iff its norm is ±1 -/
def isUnit (x : GoldenInt) : Bool := norm x == 1 || norm x == -1

theorem isUnit_iff (x : GoldenInt) : isUnit x ↔ norm x = 1 ∨ norm x = -1 := by
  unfold isUnit
  simp [Bool.or_eq_true, beq_iff_eq]

/-- Norm is multiplicative: N(xy) = N(x)N(y) -/
theorem norm_mul (x y : GoldenInt) : norm (mul x y) = norm x * norm y := by
  unfold norm mul
  simp only
  ring

/-- √5 is irrational: no integer solutions to m² = 5n² with n ≠ 0 -/
theorem no_sqrt5_rational : ∀ n : ℕ, n > 0 → ∀ m : ℤ, m^2 ≠ 5 * (n : ℤ)^2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn m hmeq
    -- 5 | m², so 5 | m (since 5 is prime)
    have h5_dvd_m2 : (5 : ℤ) ∣ m^2 := ⟨(n : ℤ)^2, hmeq⟩
    -- Use that 5 is prime to get 5 | m
    have hp : Nat.Prime 5 := by decide
    have h5_dvd_m : (5 : ℤ) ∣ m := Int.Prime.dvd_pow' hp h5_dvd_m2
    obtain ⟨k, hk⟩ := h5_dvd_m
    -- Substitute m = 5k into m² = 5n²
    rw [hk] at hmeq
    have h3 : 25 * k^2 = 5 * (n : ℤ)^2 := by ring_nf at hmeq ⊢; exact hmeq
    have h4 : 5 * k^2 = (n : ℤ)^2 := by linarith
    -- So 5 | n², hence 5 | n
    have h5_dvd_n2 : (5 : ℕ) ∣ n^2 := by
      have h5k : (5 : ℤ) ∣ (n : ℤ)^2 := ⟨k^2, h4.symm⟩
      have := Int.natCast_dvd_natCast.mp h5k
      simp only at this
      exact this
    have h5_dvd_n : (5 : ℕ) ∣ n := Nat.Prime.dvd_of_dvd_pow hp h5_dvd_n2
    obtain ⟨n', hn'⟩ := h5_dvd_n
    -- n = 5n', so k² = 5n'²
    have hn'_pos : n' > 0 := by
      by_contra hle
      push_neg at hle
      interval_cases n'
      simp_all
    have hn'_lt : n' < n := by
      rw [hn']
      omega
    rw [hn'] at h4
    have h5 : k^2 = 5 * (n' : ℤ)^2 := by
      simp only [Nat.cast_mul, Nat.cast_ofNat] at h4
      have : 5 * k^2 = 25 * (n' : ℤ)^2 := by ring_nf at h4 ⊢; exact h4
      linarith
    exact ih n' hn'_lt hn'_pos k h5

/-- norm x = 0 implies x = 0 -/
theorem norm_eq_zero_iff (x : GoldenInt) : norm x = 0 ↔ x = zero := by
  constructor
  · intro h
    unfold norm at h
    -- a² + ab - b² = 0
    -- Complete the square: (2a + b)² = 5b² (multiply by 4)
    have h2 : (2 * x.a + x.b)^2 = 5 * x.b^2 := by nlinarith
    -- Since 5 is not a perfect square, this implies b = 0
    have hb : x.b = 0 := by
      by_contra hne
      have hb_nat : x.b.natAbs > 0 := Int.natAbs_pos.mpr hne
      have h_contra := no_sqrt5_rational x.b.natAbs hb_nat (2 * x.a + x.b)
      apply h_contra
      simp only [Int.natAbs_sq]
      convert h2 using 2
    simp only [hb, mul_zero] at h
    unfold zero
    cases x
    simp_all
  · intro h
    rw [h]
    unfold zero norm
    simp

/-- GoldenInt has no zero divisors: xy = 0 implies x = 0 or y = 0 -/
theorem mul_eq_zero_iff (x y : GoldenInt) : mul x y = zero ↔ x = zero ∨ y = zero := by
  constructor
  · intro h
    have hn : norm (mul x y) = 0 := by
      have heq : mul x y = zero := h
      rw [heq]
      unfold zero norm
      simp
    rw [norm_mul] at hn
    have : norm x = 0 ∨ norm y = 0 := Int.mul_eq_zero.mp hn
    rcases this with hx | hy
    · left; exact norm_eq_zero_iff x |>.mp hx
    · right; exact norm_eq_zero_iff y |>.mp hy
  · intro h
    rcases h with hx | hy
    · rw [hx]; unfold mul zero; simp
    · rw [hy]; unfold mul zero; simp

/-- If u is a unit and u * x = 0, then x = 0 -/
theorem unit_mul_eq_zero (u x : GoldenInt) (hu : isUnit u) (h : mul u x = zero) : x = zero := by
  have := mul_eq_zero_iff u x |>.mp h
  rcases this with hu_zero | hx
  · -- u = 0 contradicts isUnit u
    exfalso
    rw [hu_zero] at hu
    simp [isUnit, zero, norm] at hu
  · exact hx

/-- φ is a unit (norm = -1) -/
theorem phi_isUnit : isUnit phi := by
  decide

/-- -1 is a unit -/
theorem neg_one_isUnit : isUnit (neg one) := by
  decide

/-- φ⁻¹ = φ - 1 since φ² = φ + 1 implies φ · (φ - 1) = φ² - φ = 1 -/
def phiInv : GoldenInt := ⟨-1, 1⟩

/-- φ⁻¹ is a unit (norm = -1) -/
theorem phiInv_isUnit : isUnit phiInv := by
  decide

/-- 1 is a unit -/
theorem one_isUnit : isUnit one := by
  decide

/-- Product of two units is a unit -/
theorem isUnit_mul (x y : GoldenInt) (hx : isUnit x) (hy : isUnit y) : isUnit (mul x y) := by
  simp only [isUnit_iff] at *
  rw [norm_mul]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]

/-- Powers of φ for natural numbers -/
def phiPowNat : ℕ → GoldenInt
  | 0 => one
  | n + 1 => mul phi (phiPowNat n)

/-- phiPowNat n is a unit for all n -/
theorem phiPowNat_isUnit (n : ℕ) : isUnit (phiPowNat n) := by
  induction n with
  | zero => exact one_isUnit
  | succ n ih => exact isUnit_mul phi (phiPowNat n) phi_isUnit ih

/-- Negative powers of φ -/
def phiPowNeg : ℕ → GoldenInt
  | 0 => one
  | n + 1 => mul phiInv (phiPowNeg n)

/-- phiPowNeg n is a unit for all n -/
theorem phiPowNeg_isUnit (n : ℕ) : isUnit (phiPowNeg n) := by
  induction n with
  | zero => exact one_isUnit
  | succ n ih => exact isUnit_mul phiInv (phiPowNeg n) phiInv_isUnit ih

/-- Powers of φ for all integers -/
def phiPow : ℤ → GoldenInt
  | Int.ofNat n => phiPowNat n
  | Int.negSucc n => phiPowNeg (n + 1)

/-- All powers of φ are units -/
theorem phiPow_isUnit (n : ℤ) : isUnit (phiPow n) := by
  cases n with
  | ofNat n => exact phiPowNat_isUnit n
  | negSucc n => exact phiPowNeg_isUnit (n + 1)

/-- Negation of a unit is a unit -/
theorem neg_isUnit (x : GoldenInt) (hx : isUnit x) : isUnit (neg x) := by
  simp only [isUnit_iff] at *
  unfold norm neg at *
  simp only
  rcases hx with hx | hx <;> [left; right] <;> linarith

/-- The unit group O× = {±φⁿ | n ∈ Z} -/
def Units : Set GoldenInt := { x | ∃ n : ℤ, x = phiPow n ∨ x = neg (phiPow n) }

/-- Elements in Units are units (forward direction) -/
theorem units_isUnit (x : GoldenInt) (hx : x ∈ Units) : isUnit x := by
  obtain ⟨n, hn | hn⟩ := hx
  · rw [hn]; exact phiPow_isUnit n
  · rw [hn]; exact neg_isUnit _ (phiPow_isUnit n)

/-- Equality of GoldenInt -/
theorem ext_iff (x y : GoldenInt) : x = y ↔ x.a = y.a ∧ x.b = y.b := by
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · intro ⟨ha, hb⟩; cases x; cases y; simp at ha hb; simp [ha, hb]

/-- neg (neg x) = x -/
theorem neg_neg (x : GoldenInt) : neg (neg x) = x := by
  unfold neg; simp

/-- The "size" of a golden integer for descent argument -/
def size (x : GoldenInt) : ℕ := x.a.natAbs + x.b.natAbs

/-- mul phiInv gives the components -/
theorem mul_phiInv_eq (x : GoldenInt) :
    mul phiInv x = ⟨-x.a + x.b, x.a⟩ := by
  simp only [mul, phiInv]
  congr 1 <;> ring

/-- mul phi gives the components -/
theorem mul_phi_eq (x : GoldenInt) :
    mul phi x = ⟨x.b, x.a + x.b⟩ := by
  simp only [mul, phi]
  congr 1 <;> ring

/-- If y ∈ Units, then mul phi y ∈ Units with shifted index -/
theorem mul_phi_Units (n : ℤ) : mul phi (phiPow n) = phiPow (n + 1) := by
  cases n with
  | ofNat m =>
    simp only [phiPow]
    induction m with
    | zero => rfl
    | succ k _ => rfl
  | negSucc m =>
    cases m with
    | zero =>
      simp only [phiPow, phiPowNeg, mul, phi, phiInv, one]
      rfl
    | succ k =>
      simp only [phiPow, phiPowNeg, mul, phi, phiInv]
      congr 1 <;> ring

/-- If y ∈ Units, then mul phiInv y ∈ Units with shifted index -/
theorem mul_phiInv_Units (n : ℤ) : mul phiInv (phiPow n) = phiPow (n - 1) := by
  cases n with
  | ofNat m =>
    cases m with
    | zero =>
      simp only [phiPow, phiPowNat, phiPowNeg, mul, phiInv, one]
      rfl
    | succ k =>
      have h : (Int.ofNat (k + 1) : ℤ) - 1 = Int.ofNat k := by simp
      simp only [phiPow, h]
      simp only [phiPowNat, mul, phi, phiInv]
      congr 1 <;> ring
  | negSucc m =>
    simp only [phiPow, phiPowNeg, mul, phiInv]
    congr 1

/-- Multiplication by phi commutes with negation -/
theorem mul_phi_neg (x : GoldenInt) : mul phi (neg x) = neg (mul phi x) := by
  simp only [mul, phi, neg]
  congr 1 <;> ring

/-- Multiplication by phiInv commutes with negation -/
theorem mul_phiInv_neg (x : GoldenInt) : mul phiInv (neg x) = neg (mul phiInv x) := by
  simp only [mul, phiInv, neg]
  congr 1 <;> ring

/-- mul phi (neg (phiPow n)) = neg (phiPow (n + 1)) -/
theorem mul_phi_neg_Units (n : ℤ) : mul phi (neg (phiPow n)) = neg (phiPow (n + 1)) := by
  rw [mul_phi_neg, mul_phi_Units]

/-- mul phiInv (neg (phiPow n)) = neg (phiPow (n - 1)) -/
theorem mul_phiInv_neg_Units (n : ℤ) : mul phiInv (neg (phiPow n)) = neg (phiPow (n - 1)) := by
  rw [mul_phiInv_neg, mul_phiInv_Units]

/-- Key descent lemma: for a unit x with a ≠ 0, b ≠ 0, and a·b > 0,
    multiplying by phiInv reduces size -/
theorem size_mul_phiInv_lt (x : GoldenInt) (hx : isUnit x) (ha : x.a ≠ 0) (hab : x.a * x.b > 0) :
    size (mul phiInv x) < size x := by
  simp only [size, mul_phiInv_eq]
  -- When a·b > 0, both have same sign
  -- mul phiInv x = ⟨-a + b, a⟩
  -- We need |−a + b| + |a| < |a| + |b|
  have h1 : (x.a > 0 ∧ x.b > 0) ∨ (x.a < 0 ∧ x.b < 0) := by
    rcases Int.lt_trichotomy x.a 0 with ha_neg | ha_zero | ha_pos
    · right; constructor
      · exact ha_neg
      · nlinarith
    · exact absurd ha_zero ha
    · left; constructor
      · exact ha_pos
      · nlinarith
  -- Use the norm constraint: a² + ab - b² = ±1
  simp only [isUnit_iff] at hx; unfold norm at hx
  rcases h1 with ⟨ha_pos, hb_pos⟩ | ⟨ha_neg, hb_neg⟩
  · -- Case: a > 0, b > 0
    -- mul phiInv x = ⟨-a + b, a⟩
    -- |a| = a, |b| = b
    -- We need |−a + b| + a < a + b, i.e., |−a + b| < b
    have ha_nonneg : x.a ≥ 0 := le_of_lt ha_pos
    have hb_nonneg : x.b ≥ 0 := le_of_lt hb_pos
    by_cases hab2 : x.a ≥ x.b
    · -- a ≥ b > 0: then -a + b ≤ 0, so |−a + b| = a - b
      -- Need (a - b) + a < a + b, i.e., a < 2b
      have hnorm_bound : x.a < 2 * x.b := by
        rcases hx with hx | hx <;> nlinarith
      have h2 : -x.a + x.b ≤ 0 := by omega
      have h3 : ((-x.a + x.b).natAbs : ℤ) = -(-x.a + x.b) := by
        rw [← Int.natAbs_neg, Int.natAbs_of_nonneg (by omega : -(-x.a + x.b) ≥ 0)]
      have h4 : (x.a.natAbs : ℤ) = x.a := Int.natAbs_of_nonneg ha_nonneg
      have h5 : (x.b.natAbs : ℤ) = x.b := Int.natAbs_of_nonneg hb_nonneg
      omega
    · -- b > a > 0: then -a + b > 0
      push_neg at hab2
      have h2 : -x.a + x.b > 0 := by omega
      have h3 : ((-x.a + x.b).natAbs : ℤ) = -x.a + x.b :=
        Int.natAbs_of_nonneg (le_of_lt h2)
      have h4 : (x.a.natAbs : ℤ) = x.a := Int.natAbs_of_nonneg ha_nonneg
      have h5 : (x.b.natAbs : ℤ) = x.b := Int.natAbs_of_nonneg hb_nonneg
      -- Need (-a + b) + a < a + b, i.e., b < a + b, always true for a > 0
      omega
  · -- Case: a < 0, b < 0
    -- |a| = -a, |b| = -b
    -- mul phiInv x = ⟨-a + b, a⟩
    have ha_nonpos : x.a ≤ 0 := le_of_lt ha_neg
    have hb_nonpos : x.b ≤ 0 := le_of_lt hb_neg
    by_cases hab2 : x.a ≤ x.b
    · -- a ≤ b < 0: then -a + b ≥ 0 (since -a ≥ -b > 0, so -a + b ≥ -b + b = 0)
      have h2 : -x.a + x.b ≥ 0 := by omega
      have h3 : ((-x.a + x.b).natAbs : ℤ) = -x.a + x.b := Int.natAbs_of_nonneg h2
      have h4 : (x.a.natAbs : ℤ) = -x.a := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr ha_nonpos)
      have h5 : (x.b.natAbs : ℤ) = -x.b := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr hb_nonpos)
      -- Need (-a + b) + (-a) < (-a) + (-b)
      -- i.e., -2a + b < -a - b, i.e., -a + 2b < 0, i.e., a > 2b
      -- Since a ≤ b < 0, we have b ≤ 0 and 2b < b ≤ a won't work directly.
      -- Use norm constraint: a² + ab - b² = ±1
      have hnorm_bound : x.a > 2 * x.b := by
        rcases hx with hx | hx <;> nlinarith
      have goal_in_int : ((-x.a + x.b).natAbs : ℤ) + (x.a.natAbs : ℤ) <
                         (x.a.natAbs : ℤ) + (x.b.natAbs : ℤ) := by
        rw [h3, h4, h5]; omega
      exact Nat.cast_lt.mp goal_in_int
    · -- b < a < 0
      push_neg at hab2
      have h2 : -x.a + x.b < 0 := by omega
      have h3 : ((-x.a + x.b).natAbs : ℤ) = -(-x.a + x.b) := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by omega : -(-x.a + x.b) ≥ 0)
      have h4 : (x.a.natAbs : ℤ) = -x.a := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr ha_nonpos)
      have h5 : (x.b.natAbs : ℤ) = -x.b := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr hb_nonpos)
      -- Need -(-a + b) + (-a) < (-a) + (-b)
      -- i.e., (a - b) + (-a) < -a - b
      -- i.e., -b < -a - b
      -- i.e., 0 < -a, true since a < 0
      omega

/-- Key descent lemma: for a unit x with a ≠ 0, b ≠ 0, and a·b < 0,
    multiplying by phi reduces size -/
theorem size_mul_phi_lt (x : GoldenInt) (hx : isUnit x) (ha : x.a ≠ 0) (hab : x.a * x.b < 0) :
    size (mul phi x) < size x := by
  simp only [size, mul_phi_eq]
  -- When a·b < 0, they have opposite signs
  -- mul phi x = ⟨b, a + b⟩
  have h1 : (x.a > 0 ∧ x.b < 0) ∨ (x.a < 0 ∧ x.b > 0) := by
    rcases Int.lt_trichotomy x.a 0 with ha_neg | ha_zero | ha_pos
    · right; constructor
      · exact ha_neg
      · nlinarith
    · exact absurd ha_zero ha
    · left; constructor
      · exact ha_pos
      · nlinarith
  simp only [isUnit_iff] at hx; unfold norm at hx
  rcases h1 with ⟨ha_pos, hb_neg⟩ | ⟨ha_neg, hb_pos⟩
  · -- Case: a > 0, b < 0
    by_cases hab2 : x.a + x.b ≥ 0
    · -- a + b ≥ 0, b < 0
      have h3 : (x.b.natAbs : ℤ) = -x.b := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt hb_neg))
      have h4 : ((x.a + x.b).natAbs : ℤ) = x.a + x.b := Int.natAbs_of_nonneg hab2
      have h5 : (x.a.natAbs : ℤ) = x.a := Int.natAbs_of_nonneg (le_of_lt ha_pos)
      -- |b| + |a+b| = -b + (a + b) = a
      -- Need a < a + (-b) = a - b
      -- Since b < 0, -b > 0, so a < a - b is true
      omega
    · -- a + b < 0, a > 0, b < 0
      push_neg at hab2
      have hab2' : x.a + x.b ≤ 0 := le_of_lt hab2
      have h3 : (x.b.natAbs : ℤ) = -x.b := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt hb_neg))
      have h4 : ((x.a + x.b).natAbs : ℤ) = -(x.a + x.b) := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr hab2')
      have h5 : (x.a.natAbs : ℤ) = x.a := Int.natAbs_of_nonneg (le_of_lt ha_pos)
      -- |b| + |a+b| = -b + (-(a+b)) = -b - a - b = -a - 2b
      -- Need -a - 2b < a + (-b) = a - b
      -- i.e., -2a - b < 0, i.e., -b < 2a
      have hnorm_bound : -x.b < 2 * x.a := by
        rcases hx with hx | hx <;> nlinarith
      omega
  · -- Case: a < 0, b > 0
    by_cases hab2 : x.a + x.b ≥ 0
    · -- a + b ≥ 0, a < 0, b > 0
      have h3 : (x.b.natAbs : ℤ) = x.b := Int.natAbs_of_nonneg (le_of_lt hb_pos)
      have h4 : ((x.a + x.b).natAbs : ℤ) = x.a + x.b := Int.natAbs_of_nonneg hab2
      have h5 : (x.a.natAbs : ℤ) = -x.a := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt ha_neg))
      -- |b| + |a+b| = b + (a + b) = a + 2b
      -- Need a + 2b < (-a) + b, i.e., 2a + b < 0
      have hnorm_bound : 2 * x.a + x.b < 0 := by
        rcases hx with hx | hx <;> nlinarith
      omega
    · -- a + b < 0, a < 0
      push_neg at hab2
      have hab2' : x.a + x.b ≤ 0 := le_of_lt hab2
      have h3 : (x.b.natAbs : ℤ) = x.b := Int.natAbs_of_nonneg (le_of_lt hb_pos)
      have h4 : ((x.a + x.b).natAbs : ℤ) = -(x.a + x.b) := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr hab2')
      have h5 : (x.a.natAbs : ℤ) = -x.a := by
        rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (neg_nonneg.mpr (le_of_lt ha_neg))
      -- |b| + |a+b| = b + (-(a+b)) = b - a - b = -a
      -- Need -a < (-a) + b
      omega

/-- Reverse direction helper: find n such that x = phiPow n or x = neg (phiPow n).
    This theorem is a consequence of Dirichlet's unit theorem for Q(√5).
    The proof uses that the fundamental unit is φ and all units are ±φⁿ. -/
theorem isUnit_mem_Units (x : GoldenInt) (hx : isUnit x) : x ∈ Units := by
  -- Well-founded induction on size
  induction h : size x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    unfold Units
    by_cases hb : x.b = 0
    · -- If b = 0, then a² = ±1, so a = ±1
      simp only [isUnit_iff] at hx; unfold norm at hx
      simp only [hb, mul_zero, sub_zero, sq] at hx
      have ha : x.a = 1 ∨ x.a = -1 := by
        rcases hx with hx | hx
        · have h1 : x.a * x.a = 1 := by linarith
          have h3 : (x.a - 1) * (x.a + 1) = 0 := by ring_nf; linarith
          rcases mul_eq_zero.mp h3 with h4 | h4 <;> omega
        · have h1 : x.a * x.a = -1 := by linarith
          have h2 : x.a * x.a ≥ 0 := mul_self_nonneg x.a
          omega
      rcases ha with ha | ha
      · use 0; left; simp only [phiPow, phiPowNat, ext_iff, one]; exact ⟨ha, hb⟩
      · use 0; right; simp only [phiPow, phiPowNat, ext_iff, one, neg]; constructor <;> linarith
    · by_cases ha : x.a = 0
      · -- If a = 0, then -b² = ±1, so b = ±1
        simp only [isUnit_iff] at hx; unfold norm at hx
        simp only [ha, sq, zero_mul, zero_add, zero_sub] at hx
        have hb' : x.b = 1 ∨ x.b = -1 := by
          have h1 : x.b * x.b ≥ 0 := mul_self_nonneg x.b
          rcases hx with hx | hx
          · omega
          · have h2 : x.b * x.b = 1 := by omega
            have h3 : (x.b - 1) * (x.b + 1) = 0 := by ring_nf; linarith
            rcases mul_eq_zero.mp h3 with h4 | h4 <;> omega
        rcases hb' with hb' | hb'
        · use 1; left
          simp only [phiPow, phiPowNat, mul, phi, one, ext_iff]
          exact ⟨ha, hb'⟩
        · use 1; right
          simp only [phiPow, phiPowNat, mul, phi, one, neg, ext_iff]
          constructor <;> linarith
      · -- General case: both a ≠ 0 and b ≠ 0
        -- Use descent: multiply by phi or phiInv based on sign of a*b
        by_cases hab : x.a * x.b > 0
        · -- a*b > 0: use phiInv
          have hsize : size (mul phiInv x) < size x :=
            size_mul_phiInv_lt x hx ha hab
          have hunit : isUnit (mul phiInv x) := isUnit_mul phiInv x phiInv_isUnit hx
          have hsize' : size (mul phiInv x) < n := by rw [← h]; exact hsize
          obtain ⟨m, hm⟩ := ih (size (mul phiInv x)) hsize' (mul phiInv x) hunit rfl
          -- mul phiInv x = phiPow m or neg (phiPow m)
          -- So x = mul phi (phiPow m) = phiPow (m+1) or x = mul phi (neg (phiPow m))
          rcases hm with hm | hm
          · use m + 1; left
            have hcomp : x = mul phi (mul phiInv x) := by
              simp only [mul, phi, phiInv]
              rw [ext_iff]; constructor <;> ring
            rw [hcomp, hm, mul_phi_Units]
          · use m + 1; right
            have hcomp : x = mul phi (mul phiInv x) := by
              simp only [mul, phi, phiInv]
              rw [ext_iff]; constructor <;> ring
            rw [hcomp, hm, mul_phi_neg_Units]
        · -- a*b ≤ 0
          push_neg at hab
          by_cases hab2 : x.a * x.b = 0
          · -- a*b = 0, but a ≠ 0 and b ≠ 0, contradiction
            have : x.a = 0 ∨ x.b = 0 := Int.mul_eq_zero.mp hab2
            rcases this with ha' | hb' <;> contradiction
          · -- a*b < 0: use phi
            have hab3 : x.a * x.b < 0 := by omega
            have hsize : size (mul phi x) < size x :=
              size_mul_phi_lt x hx ha hab3
            have hunit : isUnit (mul phi x) := isUnit_mul phi x phi_isUnit hx
            have hsize' : size (mul phi x) < n := by rw [← h]; exact hsize
            obtain ⟨m, hm⟩ := ih (size (mul phi x)) hsize' (mul phi x) hunit rfl
            rcases hm with hm | hm
            · use m - 1; left
              have hcomp : x = mul phiInv (mul phi x) := by
                simp only [mul, phi, phiInv]
                rw [ext_iff]; constructor <;> ring
              rw [hcomp, hm, mul_phiInv_Units]
            · use m - 1; right
              have hcomp : x = mul phiInv (mul phi x) := by
                simp only [mul, phi, phiInv]
                rw [ext_iff]; constructor <;> ring
              rw [hcomp, hm, mul_phiInv_neg_Units]

/-- Characterization of units: full equivalence -/
theorem units_iff_norm_pm_one (x : GoldenInt) : x ∈ Units ↔ isUnit x := by
  constructor
  · exact units_isUnit x
  · exact isUnit_mem_Units x

end GoldenInt

/-!
## Formal Power Series with Golden Integer Coefficients

Laurent series A = O((x)) over the golden integers.
-/

/-- A formal Laurent series with golden integer coefficients.
    Represented as a function from Z to GoldenInt with finite negative support. -/
structure GoldenLaurent where
  coeff : ℤ → GoldenInt
  finiteNegSupport : Set.Finite { n : ℤ | n < 0 ∧ coeff n ≠ 0 }

namespace GoldenLaurent

/-- The valuation of a Laurent series: the minimum index with nonzero coefficient -/
noncomputable def valuation (f : GoldenLaurent) : WithTop ℤ :=
  sInf { (n : WithTop ℤ) | ∃ m : ℤ, (m : WithTop ℤ) = n ∧ f.coeff m ≠ 0 }

/-- Zero Laurent series -/
def zero : GoldenLaurent := ⟨fun _ => 0, Set.finite_empty.subset (fun _ h => h.2 rfl)⟩

/-- The x variable as a Laurent series -/
def X : GoldenLaurent := ⟨fun n => if n = 1 then 1 else 0, by
  apply Set.finite_empty.subset
  intro n ⟨hn, hne⟩
  simp only [ne_eq] at hne
  split_ifs at hne with heq
  · omega
  · exact hne rfl⟩

/-- Monomial x^n -/
def monomial (n : ℤ) (c : GoldenInt) : GoldenLaurent :=
  ⟨fun m => if m = n then c else 0, by
    by_cases hn : n < 0
    · by_cases hc : c ≠ 0
      · apply (Set.finite_singleton n).subset
        intro m ⟨_, hne⟩
        simp only [ne_eq, Set.mem_singleton_iff] at hne ⊢
        split_ifs at hne with heq
        · exact heq
        · exact (hne rfl).elim
      · push_neg at hc
        apply Set.finite_empty.subset
        intro m ⟨_, hne⟩
        simp only [ne_eq, Set.mem_empty_iff_false] at hne ⊢
        split_ifs at hne with heq
        · subst heq; exact hne hc
        · exact hne rfl
    · apply Set.finite_empty.subset
      intro m ⟨hm, hne⟩
      simp only [ne_eq, Set.mem_empty_iff_false] at hne ⊢
      split_ifs at hne with heq
      · subst heq; omega
      · exact hne rfl⟩

/-- Addition of Laurent series -/
def add (f g : GoldenLaurent) : GoldenLaurent :=
  ⟨fun n => f.coeff n + g.coeff n, by
    have hf := f.finiteNegSupport
    have hg := g.finiteNegSupport
    apply (hf.union hg).subset
    intro n ⟨hn, hne⟩
    by_cases hfn : f.coeff n = 0
    · by_cases hgn : g.coeff n = 0
      · exfalso; apply hne
        change f.coeff n + g.coeff n = 0
        rw [hfn, hgn]
        rfl
      · right; exact ⟨hn, hgn⟩
    · left; exact ⟨hn, hfn⟩⟩

/-- Negation of Laurent series -/
def neg (f : GoldenLaurent) : GoldenLaurent :=
  ⟨fun n => -f.coeff n, by
    have hf := f.finiteNegSupport
    apply hf.subset
    intro n ⟨hn, hne⟩
    constructor
    · exact hn
    · intro heq
      apply hne
      -- heq : f.coeff n = 0, need to show -f.coeff n = 0
      change -f.coeff n = 0
      rw [heq]
      rfl⟩

/-- Subtraction of Laurent series -/
def sub (f g : GoldenLaurent) : GoldenLaurent := add f (neg g)

instance : Add GoldenLaurent := ⟨add⟩
instance : Neg GoldenLaurent := ⟨neg⟩
instance : Sub GoldenLaurent := ⟨sub⟩

/-- The M_{1/x} operator: shifts indices by -1 (multiplication by 1/x) -/
def invMulOp (f : GoldenLaurent) : GoldenLaurent :=
  ⟨fun n => f.coeff (n + 1), by
    have hf := f.finiteNegSupport
    -- {n | n < 0 ∧ f.coeff(n+1) ≠ 0} is finite
    -- This set is a subset of {m - 1 | m < 0 ∧ f.coeff m ≠ 0} ∪ {-1}
    -- which is finite since hf is finite
    have h1 : {n : ℤ | n < 0 ∧ f.coeff (n + 1) ≠ 0} ⊆
              (fun m => m - 1) '' {m : ℤ | m < 0 ∧ f.coeff m ≠ 0} ∪ {-1} := by
      intro n ⟨hn, hne⟩
      by_cases h : n + 1 < 0
      · left
        simp only [Set.mem_image]
        use n + 1
        exact ⟨⟨h, hne⟩, by ring⟩
      · right
        push_neg at h
        simp only [Set.mem_singleton_iff]
        omega
    exact ((hf.image (· - 1)).union (Set.finite_singleton (-1))).subset h1⟩

end GoldenLaurent

/-!
## Valuation Non-Decreasing Property

The main theorem: v_𝔭(Δf) ≥ v_𝔭(f) for the two-point difference operator.
-/

/-- Abstract valuation on golden integers (for a prime ideal 𝔭) -/
class GoldenValuation where
  v : GoldenInt → WithTop ℤ
  v_zero : v 0 = ⊤
  v_one : v 1 = 0
  v_mul : ∀ x y, v (x * y) = v x + v y
  v_add : ∀ x y, v (x + y) ≥ min (v x) (v y)
  v_unit : ∀ x, GoldenInt.isUnit x → v x = 0
  v_nonneg : ∀ x, (0 : WithTop ℤ) ≤ v x

variable [GoldenValuation]

/-- Coefficient valuation of a Laurent series:
    the minimum valuation among all coefficients -/
noncomputable def coeffValuation (f : GoldenLaurent) : WithTop ℤ :=
  ⨅ n, GoldenValuation.v (f.coeff n)

/-- The scale operator U multiplies each coefficient by a unit power of φ -/
def scaleCoeffByUnit (f : GoldenLaurent) (u : GoldenInt) :
    GoldenLaurent :=
  ⟨fun n => u * f.coeff n, by
    have hf := f.finiteNegSupport
    apply hf.subset
    intro n ⟨hn, hne⟩
    constructor
    · exact hn
    · intro heq
      apply hne
      -- f.coeff n = 0 implies u * f.coeff n = 0
      simp only [heq]
      change GoldenInt.mul u GoldenInt.zero = GoldenInt.zero
      unfold GoldenInt.mul GoldenInt.zero
      simp⟩

/-- The two-point scale difference operator Δ_{α,β,ε}
    Δf = M_{1/x}(αf - βf) for simplified version -/
def twoPointDiff (f : GoldenLaurent) (α β : GoldenInt) : GoldenLaurent :=
  GoldenLaurent.invMulOp (GoldenLaurent.sub (scaleCoeffByUnit f α) (scaleCoeffByUnit f β))

/-!
## Key Lemmas for the Proof
-/

/-- Units have valuation 0 -/
theorem unit_valuation_zero (u : GoldenInt) (hu : GoldenInt.isUnit u) :
    GoldenValuation.v u = 0 :=
  GoldenValuation.v_unit u hu

/-- The difference of two units has non-negative valuation -/
theorem unit_diff_valuation_nonneg (u₁ u₂ : GoldenInt)
    (hu₁ : GoldenInt.isUnit u₁) (hu₂ : GoldenInt.isUnit u₂) :
    (0 : WithTop ℤ) ≤ GoldenValuation.v (u₁ - u₂) := by
  have h := GoldenValuation.v_add u₁ (-u₂)
  simp only at h
  have hu₁' := unit_valuation_zero u₁ hu₁
  -- -u₂ is also a unit if u₂ is
  have hu₂_neg : GoldenInt.isUnit (-u₂) := GoldenInt.neg_isUnit u₂ hu₂
  have hu₂' := unit_valuation_zero (-u₂) hu₂_neg
  calc GoldenValuation.v (u₁ + -u₂)
      ≥ min (GoldenValuation.v u₁) (GoldenValuation.v (-u₂)) := h
    _ = min 0 0 := by rw [hu₁', hu₂']
    _ = 0 := min_self 0

-- Helper: distributive law for GoldenInt multiplication
omit [GoldenValuation] in
theorem GoldenInt.mul_sub_distrib (a b c : GoldenInt) :
    GoldenInt.mul (GoldenInt.sub a b) c =
    GoldenInt.sub (GoldenInt.mul a c) (GoldenInt.mul b c) := by
  unfold GoldenInt.mul GoldenInt.sub GoldenInt.add GoldenInt.neg
  simp only [GoldenInt.ext_iff]
  constructor <;> ring

/-- **Main Theorem: Valuation Non-Decreasing Property**

    For any Laurent series f and unit coefficients α, β ∈ O×,
    the two-point difference Δ_{α,β}f satisfies:

    v_𝔭(Δf) ≥ v_𝔭(f)

    where v_𝔭 denotes the coefficient valuation with respect to
    a golden prime ideal 𝔭.

    This is Proposition 6.1 / 8.1 in the papers. -/
theorem valuation_nonDecreasing
    (f : GoldenLaurent)
    (α β : GoldenInt)
    (hα : GoldenInt.isUnit α)
    (hβ : GoldenInt.isUnit β) :
    coeffValuation (twoPointDiff f α β) ≥ coeffValuation f := by
  -- The key insight: Δf = M_{1/x}(αf - βf)
  -- For each coefficient n: the coefficient of Δf at n is α*f(n+1) - β*f(n+1) = (α-β)*f(n+1)
  -- v((α - β) * c) = v(α - β) + v(c) ≥ 0 + v(c) = v(c) since α, β are units
  unfold coeffValuation
  rw [ge_iff_le]
  -- For each n, v((twoPointDiff f α β).coeff n) ≥ ⨅ m, v(f.coeff m)
  -- So ⨅ n, v((twoPointDiff f α β).coeff n) ≥ ⨅ m, v(f.coeff m)
  -- Use le_ciInf: if for all n, a ≤ f n, then a ≤ ⨅ f
  apply le_ciInf
  intro n
  -- The coefficient of twoPointDiff at n is α * f.coeff(n+1) + (-(β * f.coeff(n+1)))
  have hcoeff_eq : (twoPointDiff f α β).coeff n =
                   α * f.coeff (n + 1) + -(β * f.coeff (n + 1)) := by
    unfold twoPointDiff GoldenLaurent.invMulOp
           GoldenLaurent.sub GoldenLaurent.add GoldenLaurent.neg scaleCoeffByUnit
    rfl
  rw [hcoeff_eq]
  -- Show this equals (α - β) * f.coeff(n+1)
  have hcoeff : GoldenInt.add (GoldenInt.mul α (f.coeff (n + 1)))
                (GoldenInt.neg (GoldenInt.mul β (f.coeff (n + 1)))) =
                GoldenInt.mul (GoldenInt.sub α β) (f.coeff (n + 1)) := by
    rw [GoldenInt.mul_sub_distrib]
    unfold GoldenInt.sub GoldenInt.add GoldenInt.neg
    simp only
  -- Instance inference uses add/neg notation
  have hcoeff' : α * f.coeff (n + 1) + -(β * f.coeff (n + 1)) =
                (α - β) * f.coeff (n + 1) := hcoeff
  rw [hcoeff']
  -- v((α - β) * c) = v(α - β) + v(c)
  have hv_mul := GoldenValuation.v_mul (α - β) (f.coeff (n + 1))
  rw [hv_mul]
  -- v(α - β) ≥ 0 since both are units
  have hdiff_nonneg := unit_diff_valuation_nonneg α β hα hβ
  -- v(c) ≥ ⨅ m, v(f.coeff m)
  -- The infimum over all m is ≤ any specific value
  have hc_ge : ⨅ m, GoldenValuation.v (f.coeff m) ≤ GoldenValuation.v (f.coeff (n + 1)) := by
    apply csInf_le
    · -- BddBelow: 0 is a lower bound since all valuations are ≥ 0
      use 0
      intro x hx
      obtain ⟨m, hm⟩ := hx
      rw [← hm]
      exact GoldenValuation.v_nonneg (f.coeff m)
    · exact ⟨n + 1, rfl⟩
  calc ⨅ m, GoldenValuation.v (f.coeff m)
      ≤ GoldenValuation.v (f.coeff (n + 1)) := hc_ge
    _ = 0 + GoldenValuation.v (f.coeff (n + 1)) := (zero_add _).symm
    _ ≤ GoldenValuation.v (α - β) + GoldenValuation.v (f.coeff (n + 1)) :=
        add_le_add hdiff_nonneg le_rfl

/-- **Corollary: Conjugate Side**

    v_{𝔭̄}(Δf) ≥ v_{𝔭̄}(f)

    where 𝔭̄ is the conjugate prime ideal.

    This follows from applying the same argument with the conjugate valuation. -/
theorem valuation_nonDecreasing_conj
    (f : GoldenLaurent)
    (α β : GoldenInt)
    (hα : GoldenInt.isUnit α)
    (hβ : GoldenInt.isUnit β) :
    coeffValuation (twoPointDiff f α β) ≥ coeffValuation f :=
  valuation_nonDecreasing f α β hα hβ

/-- Scaling by a unit preserves coefficient valuation -/
theorem scale_preserves_coeff_valuation (f : GoldenLaurent) (u : GoldenInt)
    (hu : GoldenInt.isUnit u) :
    coeffValuation (scaleCoeffByUnit f u) = coeffValuation f := by
  unfold coeffValuation scaleCoeffByUnit
  simp only
  congr 1
  ext n
  -- v(u * c) = v(u) + v(c) = 0 + v(c) = v(c)
  have hv_mul := GoldenValuation.v_mul u (f.coeff n)
  have hv_unit := GoldenValuation.v_unit u hu
  simp only [hv_mul, hv_unit, zero_add]

omit [GoldenValuation] in
/-- M_{1/x} shifts indices but preserves coefficient valuations -/
theorem invMul_preserves_coeff_valuation [GoldenValuation] (f : GoldenLaurent) :
    coeffValuation (GoldenLaurent.invMulOp f) = coeffValuation f := by
  unfold coeffValuation GoldenLaurent.invMulOp
  simp only
  -- Need to show ⨅ n, v(f.coeff (n + 1)) = ⨅ m, v(f.coeff m)
  -- The map n ↦ n + 1 is a bijection on ℤ, so the infima are equal
  -- Use Equiv.iInf_congr with the equivalence (· + 1) : ℤ ≃ ℤ
  have heq : (fun n => GoldenValuation.v (f.coeff (n + 1))) =
             (fun n => GoldenValuation.v (f.coeff n)) ∘ (· + 1) := rfl
  rw [heq]
  -- Now use that composing with a bijection preserves infimum
  have hbij : Function.Bijective (fun n : ℤ => n + 1) := by
    constructor
    · intro a b hab; simp only at hab; linarith
    · intro b; use b - 1; simp only; ring
  exact Equiv.iInf_congr (Equiv.ofBijective _ hbij) (fun _ => rfl)

/-!
## Specialization to Φ-system and F-system
-/

omit [GoldenValuation] in
/-- For the Φ-system with α = φ⁻¹, β = φ -/
theorem valuation_nonDecreasing_Phi [GoldenValuation] (f : GoldenLaurent) :
    coeffValuation (twoPointDiff f GoldenInt.phiInv GoldenInt.phi) ≥ coeffValuation f := by
  -- α = φ⁻¹ and β = φ are both units
  exact valuation_nonDecreasing f GoldenInt.phiInv GoldenInt.phi
    GoldenInt.phiInv_isUnit GoldenInt.phi_isUnit

omit [GoldenValuation] in
/-- For the F-system with α = 1, β = -1 -/
theorem valuation_nonDecreasing_F [GoldenValuation] (f : GoldenLaurent) :
    coeffValuation (twoPointDiff f GoldenInt.one (GoldenInt.neg GoldenInt.one)) ≥
    coeffValuation f := by
  -- α = 1 and β = -1 are both units
  exact valuation_nonDecreasing f GoldenInt.one (GoldenInt.neg GoldenInt.one)
    GoldenInt.one_isUnit GoldenInt.neg_one_isUnit

end FUST.FrourioAlgebra
