import FUST.Basic
import FUST.FrourioAlgebra.GoldenValuation
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# Golden Integer Ring ℤ[φ]

This file establishes the commutative ring structure on the golden integer ring
ℤ[φ] = {a + bφ | a, b ∈ ℤ}, where φ = (1 + √5)/2 is the golden ratio.

## Main Results

* `GoldenInt.commRing` : ℤ[φ] is a commutative ring
* `GoldenInt.toReal` : Embedding ℤ[φ] → ℝ
* `GoldenInt.toReal_injective` : The embedding is injective
* `GoldenInt.phiPow_eq_toReal` : φ^n in ℤ[φ] corresponds to φ^n in ℝ

## Mathematical Background

The golden integer ring ℤ[φ] is the ring of integers in the quadratic field ℚ(√5).
Key properties:
- φ² = φ + 1 (golden ratio equation)
- Units: ℤ[φ]× = {±φⁿ | n ∈ ℤ}
- Norm: N(a + bφ) = a² + ab - b² = (-1)^n for units ±φⁿ
-/

namespace FUST.FrourioAlgebra

open GoldenInt

/-!
## Ring Axioms for GoldenInt
-/

/-- Addition is commutative -/
theorem add_comm' (x y : GoldenInt) : add x y = add y x := by
  unfold add
  congr 1 <;> ring

/-- Addition is associative -/
theorem add_assoc' (x y z : GoldenInt) : add (add x y) z = add x (add y z) := by
  unfold add
  congr 1 <;> ring

/-- Zero is left identity for addition -/
theorem zero_add' (x : GoldenInt) : add zero x = x := by
  unfold add zero
  simp

/-- Zero is right identity for addition -/
theorem add_zero' (x : GoldenInt) : add x zero = x := by
  unfold add zero
  simp

/-- Left inverse for addition -/
theorem add_left_neg' (x : GoldenInt) : add (neg x) x = zero := by
  unfold add neg zero
  simp

/-- Right inverse for addition (neg_add_cancel) -/
theorem neg_add_cancel' (x : GoldenInt) : neg x + x = (0 : GoldenInt) := by
  change add (neg x) x = zero
  unfold add neg zero
  simp

/-- Multiplication is commutative -/
theorem mul_comm' (x y : GoldenInt) : mul x y = mul y x := by
  unfold mul
  congr 1 <;> ring

/-- Multiplication is associative -/
theorem mul_assoc' (x y z : GoldenInt) : mul (mul x y) z = mul x (mul y z) := by
  unfold mul
  -- (a + bφ)(c + dφ) = (ac + bd) + (ad + bc + bd)φ
  -- Then multiply by (e + fφ)
  -- This uses φ² = φ + 1, φ³ = 2φ + 1, etc.
  congr 1 <;> ring

/-- One is left identity for multiplication -/
theorem one_mul' (x : GoldenInt) : mul one x = x := by
  unfold mul one
  simp

/-- One is right identity for multiplication -/
theorem mul_one' (x : GoldenInt) : mul x one = x := by
  unfold mul one
  simp

/-- Left distributivity -/
theorem left_distrib' (x y z : GoldenInt) : mul x (add y z) = add (mul x y) (mul x z) := by
  unfold mul add
  congr 1 <;> ring

/-- Right distributivity -/
theorem right_distrib' (x y z : GoldenInt) : mul (add x y) z = add (mul x z) (mul y z) := by
  unfold mul add
  congr 1 <;> ring

/-- Subtraction definition -/
theorem sub_eq_add_neg' (x y : GoldenInt) : sub x y = add x (neg y) := rfl

/-- Zero times anything is zero -/
theorem zero_mul' (x : GoldenInt) : mul zero x = zero := by
  unfold mul zero
  simp

/-- Anything times zero is zero -/
theorem mul_zero' (x : GoldenInt) : mul x zero = zero := by
  unfold mul zero
  simp

/-- Negation distributes over addition -/
theorem neg_add' (x y : GoldenInt) : neg (add x y) = add (neg x) (neg y) := by
  unfold neg add
  congr 1 <;> ring

/-- Double negation -/
theorem neg_neg' (x : GoldenInt) : neg (neg x) = x := by
  unfold neg
  simp

/-- Negation of zero is zero -/
theorem neg_zero' : neg zero = zero := by
  unfold neg zero
  simp

/-- Multiplication by -1 -/
theorem neg_one_mul' (x : GoldenInt) : mul (neg one) x = neg x := by
  unfold mul neg one
  congr 1 <;> ring

/-- Natural number scalar multiplication -/
def nsmul : ℕ → GoldenInt → GoldenInt
  | 0, _ => zero
  | n + 1, x => add (nsmul n x) x

/-- Integer scalar multiplication -/
def zsmul : ℤ → GoldenInt → GoldenInt
  | Int.ofNat n, x => nsmul n x
  | Int.negSucc n, x => neg (nsmul (n + 1) x)

/-- nsmul 0 is zero -/
theorem nsmul_zero' (x : GoldenInt) : nsmul 0 x = zero := rfl

/-- nsmul (n+1) is add -/
theorem nsmul_succ' (n : ℕ) (x : GoldenInt) : nsmul (n + 1) x = add (nsmul n x) x := rfl

/-- zsmul 0 is zero -/
theorem zsmul_zero' (x : GoldenInt) : zsmul 0 x = zero := rfl

/-- zsmul for positive integers -/
theorem zsmul_ofNat' (n : ℕ) (x : GoldenInt) : zsmul (Int.ofNat n) x = nsmul n x := rfl

/-- zsmul for negative integers -/
theorem zsmul_negSucc' (n : ℕ) (x : GoldenInt) :
    zsmul (Int.negSucc n) x = neg (nsmul (n + 1) x) := rfl

/-- Natural number power -/
def npow : ℕ → GoldenInt → GoldenInt
  | 0, _ => one
  | n + 1, x => mul (npow n x) x

/-- npow 0 is one -/
theorem npow_zero' (x : GoldenInt) : npow 0 x = one := rfl

/-- npow (n+1) is mul -/
theorem npow_succ' (n : ℕ) (x : GoldenInt) : npow (n + 1) x = mul (npow n x) x := rfl

/-- Integer cast into GoldenInt -/
def intCast : ℤ → GoldenInt
  | Int.ofNat n => ⟨n, 0⟩
  | Int.negSucc n => ⟨-(n + 1 : ℤ), 0⟩

/-- Natural number cast into GoldenInt -/
def natCast : ℕ → GoldenInt := fun n => ⟨n, 0⟩

instance : NatCast GoldenInt := ⟨natCast⟩
instance : IntCast GoldenInt := ⟨intCast⟩

/-- natCast 0 is zero -/
theorem natCast_zero' : (natCast 0 : GoldenInt) = zero := rfl

/-- natCast (n+1) is add one -/
theorem natCast_succ' (n : ℕ) : (natCast (n + 1) : GoldenInt) = add (natCast n) one := by
  simp only [natCast, add, one, ext_iff]
  constructor <;> simp

/-- intCast 0 is zero -/
theorem intCast_zero' : (intCast 0 : GoldenInt) = zero := rfl

/-- intCast 1 is one -/
theorem intCast_one' : (intCast 1 : GoldenInt) = one := rfl

/-!
## CommRing Instance
-/

instance : CommRing GoldenInt where
  add := add
  add_assoc := add_assoc'
  zero := zero
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmul
  nsmul_zero := nsmul_zero'
  nsmul_succ := nsmul_succ'
  neg := neg
  zsmul := zsmul
  zsmul_zero' := zsmul_zero'
  zsmul_succ' := fun n x => by
    change zsmul (Int.ofNat (n + 1)) x = zsmul (Int.ofNat n) x + x
    simp only [zsmul_ofNat', nsmul_succ']
    rfl
  zsmul_neg' := fun n x => by
    simp only [zsmul_negSucc', nsmul_succ']
    rfl
  neg_add_cancel := neg_add_cancel'
  add_comm := add_comm'
  mul := mul
  mul_assoc := mul_assoc'
  one := one
  one_mul := one_mul'
  mul_one := mul_one'
  npow := npow
  npow_zero := npow_zero'
  npow_succ := npow_succ'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  mul_comm := mul_comm'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  natCast := natCast
  natCast_zero := natCast_zero'
  natCast_succ := natCast_succ'
  intCast := intCast
  intCast_ofNat := fun n => rfl
  intCast_negSucc := fun n => by
    -- Need to show: intCast (Int.negSucc n) = -natCast (n + 1)
    -- intCast (Int.negSucc n) = ⟨-(n + 1 : ℤ), 0⟩
    -- -natCast (n + 1) = neg ⟨n + 1, 0⟩ = ⟨-(n + 1), 0⟩
    rfl

/-!
## Embedding into ℝ
-/

/-- Embed GoldenInt into ℝ via a + bφ -/
noncomputable def GoldenInt.toReal (x : GoldenInt) : ℝ := x.a + x.b * φ

/-- toReal of zero is 0 -/
theorem toReal_zero : GoldenInt.toReal zero = 0 := by
  unfold GoldenInt.toReal zero
  simp

/-- toReal of one is 1 -/
theorem toReal_one : GoldenInt.toReal one = 1 := by
  unfold GoldenInt.toReal one
  simp

/-- toReal of phi is φ -/
theorem toReal_phi : GoldenInt.toReal phi = φ := by
  unfold GoldenInt.toReal phi
  simp

/-- toReal preserves addition -/
theorem toReal_add (x y : GoldenInt) :
    GoldenInt.toReal (add x y) = GoldenInt.toReal x + GoldenInt.toReal y := by
  unfold GoldenInt.toReal add
  push_cast
  ring

/-- toReal preserves negation -/
theorem toReal_neg (x : GoldenInt) :
    GoldenInt.toReal (neg x) = -GoldenInt.toReal x := by
  unfold GoldenInt.toReal neg
  push_cast
  ring

/-- toReal preserves multiplication -/
theorem toReal_mul (x y : GoldenInt) :
    GoldenInt.toReal (mul x y) = GoldenInt.toReal x * GoldenInt.toReal y := by
  unfold GoldenInt.toReal mul
  -- Use φ² = φ + 1
  have hφ2' : φ * φ = φ + 1 := by simpa [pow_two] using golden_ratio_property
  push_cast
  -- (a + bφ)(c + dφ) = ac + (ad + bc)φ + bdφ²
  --                  = ac + (ad + bc)φ + bd(φ + 1)
  --                  = (ac + bd) + (ad + bc + bd)φ
  -- Expand RHS and use φ² = φ + 1
  calc (x.a : ℝ) * y.a + x.b * y.b + (x.a * y.b + x.b * y.a + x.b * y.b) * φ
      = x.a * y.a + x.b * y.b + x.a * y.b * φ + x.b * y.a * φ + x.b * y.b * φ := by ring
    _ = x.a * y.a + x.a * y.b * φ + x.b * y.a * φ + x.b * y.b * (φ + 1) := by ring
    _ = x.a * y.a + x.a * y.b * φ + x.b * y.a * φ + x.b * y.b * (φ * φ) := by rw [hφ2']
    _ = (x.a + x.b * φ) * (y.a + y.b * φ) := by ring

/-- toReal is a ring homomorphism -/
theorem toReal_ringHom : ∀ x y : GoldenInt,
    GoldenInt.toReal (x + y) = GoldenInt.toReal x + GoldenInt.toReal y ∧
    GoldenInt.toReal (x * y) = GoldenInt.toReal x * GoldenInt.toReal y :=
  fun x y => ⟨toReal_add x y, toReal_mul x y⟩

/-- φ is irrational -/
theorem phi_irrational : Irrational φ := by
  -- φ = (1 + √5)/2
  -- √5 is irrational (since 5 is prime)
  have h5_irrat : Irrational (Real.sqrt 5) := by
    have hp : Nat.Prime 5 := by decide
    exact hp.irrational_sqrt
  -- If φ were rational, then √5 = 2φ - 1 would be rational
  intro ⟨q, hq⟩
  apply h5_irrat
  -- √5 = 2φ - 1
  have h : Real.sqrt 5 = 2 * φ - 1 := by
    unfold φ
    ring
  use 2 * q - 1
  rw [h, ← hq]
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one]

/-- toReal is injective -/
theorem toReal_injective : Function.Injective GoldenInt.toReal := by
  intro x y h
  unfold GoldenInt.toReal at h
  -- x.a + x.b * φ = y.a + y.b * φ
  -- (x.a - y.a) = (y.b - x.b) * φ
  have h1 : (x.a - y.a : ℝ) = (y.b - x.b) * φ := by linarith
  -- If y.b ≠ x.b, then φ is rational, contradiction
  by_cases hb : x.b = y.b
  · -- x.b = y.b, so x.a = y.a
    have ha : x.a = y.a := by
      have : (x.a - y.a : ℝ) = 0 := by simp only [hb, sub_self, zero_mul] at h1; exact h1
      exact_mod_cast sub_eq_zero.mp this
    exact ext_iff x y |>.mpr ⟨ha, hb⟩
  · -- y.b ≠ x.b, derive contradiction
    exfalso
    have hdiff : (y.b - x.b : ℤ) ≠ 0 := by omega
    have hdiff_real : (y.b - x.b : ℝ) ≠ 0 := by exact_mod_cast hdiff
    have hφ_rat : φ = (x.a - y.a : ℝ) / (y.b - x.b : ℝ) := by
      field_simp at h1 ⊢
      linarith
    -- φ = (integer) / (integer) would make φ rational
    -- But φ is irrational
    have hφ_irrat : Irrational φ := phi_irrational
    apply hφ_irrat
    use (x.a - y.a) / (y.b - x.b)
    rw [hφ_rat]
    push_cast
    rfl

/-!
## Connection to φ powers
-/

/-- phiPowNat n corresponds to φ^n in ℝ -/
theorem phiPowNat_toReal (n : ℕ) : GoldenInt.toReal (phiPowNat n) = φ^n := by
  induction n with
  | zero =>
    simp only [phiPowNat, pow_zero]
    exact toReal_one
  | succ n ih =>
    simp only [phiPowNat, pow_succ]
    rw [toReal_mul, toReal_phi, ih]
    ring

/-- phiPowNeg n corresponds to φ^{-n} in ℝ -/
theorem phiPowNeg_toReal (n : ℕ) : GoldenInt.toReal (phiPowNeg n) = φ^(-(n : ℤ)) := by
  induction n with
  | zero =>
    simp only [phiPowNeg]
    exact toReal_one
  | succ n ih =>
    simp only [phiPowNeg]
    rw [toReal_mul]
    -- phiInv.toReal = φ^{-1}
    have h_phiInv : GoldenInt.toReal phiInv = φ^(-1 : ℤ) := by
      unfold GoldenInt.toReal phiInv
      simp only [Int.cast_neg, Int.cast_one]
      -- φ^{-1} = 1/φ = φ - 1 (since φ² = φ + 1 implies φ(φ-1) = 1)
      have hφ_pos : 0 < φ := phi_pos
      rw [zpow_neg_one, eq_comm]
      field_simp
      have hφ2 : φ * φ = φ + 1 := by simpa [pow_two] using golden_ratio_property
      linarith
    rw [h_phiInv, ih]
    have hn : (-(n + 1 : ℕ) : ℤ) = -1 + (-(n : ℕ) : ℤ) := by omega
    rw [hn, zpow_add₀ (ne_of_gt phi_pos)]

/-- phiPow n corresponds to φ^n in ℝ -/
theorem phiPow_toReal (n : ℤ) : GoldenInt.toReal (phiPow n) = φ^n := by
  cases n with
  | ofNat m =>
    simp only [phiPow]
    exact phiPowNat_toReal m
  | negSucc m =>
    simp only [phiPow]
    rw [phiPowNeg_toReal]
    simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one, neg_add_rev]

/-!
## Mass Parameters in ℤ[φ]

In FUFT, mass parameters have the form φⁿ × [1 + c₁φ^Δ₁ + c₂φ^Δ₂ + c₃φ^Δ₃]
where n, Δᵢ ∈ ℤ and cᵢ ∈ ℤ.

For integer exponents, φⁿ ∈ ℤ[φ] (proven above).
The correction factors 1 + c₁φ^Δ₁ + ... are sums of elements in ℤ[φ].
Therefore, all FUFT mass parameters naturally live in ℤ[φ].
-/

/-- A FUFT-style correction factor: 1 + c₁φ^Δ₁ + c₂φ^Δ₂ + c₃φ^Δ₃ -/
def fuftCorrectionFactor (c₁ c₂ c₃ : ℤ) (Δ₁ Δ₂ Δ₃ : ℤ) : GoldenInt :=
  one + intCast c₁ * phiPow Δ₁ + intCast c₂ * phiPow Δ₂ + intCast c₃ * phiPow Δ₃

/-- A FUFT mass parameter: φⁿ × correction_factor -/
def fuftMassParameter (n : ℤ) (c₁ c₂ c₃ : ℤ) (Δ₁ Δ₂ Δ₃ : ℤ) : GoldenInt :=
  phiPow n * fuftCorrectionFactor c₁ c₂ c₃ Δ₁ Δ₂ Δ₃

/-- intCast to real conversion -/
theorem intCast_toReal (c : ℤ) : GoldenInt.toReal (intCast c) = c := by
  cases c with
  | ofNat m => unfold GoldenInt.toReal intCast; simp
  | negSucc m => unfold GoldenInt.toReal intCast; simp

/-- The real value of a FUFT mass parameter -/
theorem fuftMassParameter_toReal (n : ℤ) (c₁ c₂ c₃ : ℤ) (Δ₁ Δ₂ Δ₃ : ℤ) :
    GoldenInt.toReal (fuftMassParameter n c₁ c₂ c₃ Δ₁ Δ₂ Δ₃) =
    φ^n * (1 + c₁ * φ^Δ₁ + c₂ * φ^Δ₂ + c₃ * φ^Δ₃) := by
  unfold fuftMassParameter fuftCorrectionFactor
  -- Use that * is mul in CommRing
  change GoldenInt.toReal (mul (phiPow n) _) = _
  rw [toReal_mul, phiPow_toReal]
  congr 1
  change GoldenInt.toReal (add (add (add one (mul (intCast c₁) (phiPow Δ₁)))
    (mul (intCast c₂) (phiPow Δ₂))) (mul (intCast c₃) (phiPow Δ₃))) = _
  simp only [toReal_add, toReal_mul, toReal_one, phiPow_toReal, intCast_toReal]

/-- All FUFT mass parameters are in ℤ[φ] (by construction) -/
theorem fuftMassParameter_in_goldenInt (n : ℤ) (c₁ c₂ c₃ : ℤ) (Δ₁ Δ₂ Δ₃ : ℤ) :
    ∃ x : GoldenInt, GoldenInt.toReal x =
      φ^n * (1 + c₁ * φ^Δ₁ + c₂ * φ^Δ₂ + c₃ * φ^Δ₃) :=
  ⟨fuftMassParameter n c₁ c₂ c₃ Δ₁ Δ₂ Δ₃, fuftMassParameter_toReal n c₁ c₂ c₃ Δ₁ Δ₂ Δ₃⟩

/-! ## Galois Conjugation σ: φ ↦ ψ

The unique non-trivial automorphism of ℤ[φ]. -/

theorem conj_add (x y : GoldenInt) :
    GoldenInt.conj (add x y) = add (GoldenInt.conj x) (GoldenInt.conj y) := by
  unfold GoldenInt.conj add; congr 1 <;> ring

theorem conj_mul (x y : GoldenInt) :
    GoldenInt.conj (mul x y) = mul (GoldenInt.conj x) (GoldenInt.conj y) := by
  unfold GoldenInt.conj mul; congr 1 <;> ring

theorem conj_one : GoldenInt.conj one = one := by
  unfold GoldenInt.conj one; simp

theorem conj_zero : GoldenInt.conj zero = zero := by
  unfold GoldenInt.conj zero; simp

theorem conj_neg (x : GoldenInt) :
    GoldenInt.conj (neg x) = neg (GoldenInt.conj x) := by
  unfold GoldenInt.conj neg; congr 1; ring

theorem conj_involution (x : GoldenInt) :
    GoldenInt.conj (GoldenInt.conj x) = x := by
  unfold GoldenInt.conj; simp

theorem conj_fixes_int (n : ℤ) : GoldenInt.conj (intCast n) = intCast n := by
  cases n with
  | ofNat m => unfold GoldenInt.conj intCast; simp
  | negSucc m => unfold GoldenInt.conj intCast; simp

theorem conj_phi : GoldenInt.conj phi = ⟨1, -1⟩ := by
  unfold GoldenInt.conj phi; simp

-- σ(φ).toReal = ψ
theorem conj_phi_toReal : (GoldenInt.conj phi).toReal = ψ := by
  rw [conj_phi]; unfold GoldenInt.toReal ψ φ; push_cast; ring

-- norm preserved: N(σ(x)) = N(x)
theorem conj_norm (x : GoldenInt) :
    GoldenInt.norm (GoldenInt.conj x) = GoldenInt.norm x := by
  unfold GoldenInt.conj GoldenInt.norm; ring

-- σ(x) · x has integer b-component = 0 (product with conjugate is in ℤ)
theorem conj_mul_self_in_Z (x : GoldenInt) :
    (mul x (GoldenInt.conj x)).b = 0 := by
  unfold mul GoldenInt.conj; simp; ring

-- Product x · σ(x) equals (norm x, 0) ... actually let's verify:
-- x = (a,b), conj(x) = (a+b,-b)
-- x * conj(x) = (a(a+b) + b(-b), a(-b) + b(a+b) + b(-b))
--             = (a² + ab - b², -ab + ab + b² - b²)
--             = (a² + ab - b², 0)
--             = (norm(x), 0)
theorem conj_mul_self_eq_norm (x : GoldenInt) :
    mul x (GoldenInt.conj x) = ⟨GoldenInt.norm x, 0⟩ := by
  unfold mul GoldenInt.conj GoldenInt.norm
  simp [GoldenInt.ext_iff]; constructor <;> ring

end FUST.FrourioAlgebra
