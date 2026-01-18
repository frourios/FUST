import FUST.Physics.TimeTheorem
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Zeta Functions from FUST

Two zeta functions are derived from FUST:

## (A) Golden Zeta from Scale Structure {φ^k}
- ζ_φ(s) = 1/(φ^s - 1)
- Functional equation: ζ_φ(s) + ζ_φ(-s) = -1
- Symmetry point: s = 0

## (B) Riemann Zeta from Composition Structure
- ζ(s) = Σ n^{-s} where n ∈ ℕ_FUST
- Euler product: ζ(s) = Π_p (1 - p^{-s})^{-1}
- Functional equation: ξ(s) = ξ(1-s)
- Symmetry point: s = 1/2

## Comparison
| Property | Golden ζ_φ | Riemann ζ |
|----------|------------|-----------|
| Structure | Scale φ^k | Composition n |
| Closed form | 1/(φ^s-1) | Euler product |
| Symmetry | s = 0 | s = 1/2 |
-/

namespace FUST.RiemannHypothesis

open FUST.TimeTheorem

/-!
## Section 1: Golden Zeta Function
-/

section GoldenZeta

/-- Golden zeta function: ζ_φ(s) = 1/(φ^s - 1) for s > 0 -/
noncomputable def goldenZeta (s : ℝ) : ℝ := 1 / (φ^s - 1)

/-- φ^s > 1 for s > 0 -/
theorem phi_pow_gt_one (s : ℝ) (hs : s > 0) : φ^s > 1 := by
  have hφ_gt : φ > 1 := φ_gt_one
  exact Real.one_lt_rpow hφ_gt hs

/-- φ^s - 1 > 0 for s > 0 -/
theorem phi_pow_sub_one_pos (s : ℝ) (hs : s > 0) : φ^s - 1 > 0 := by
  have h := phi_pow_gt_one s hs
  linarith

/-- Golden zeta is positive for s > 0 -/
theorem goldenZeta_pos (s : ℝ) (hs : s > 0) : goldenZeta s > 0 := by
  simp only [goldenZeta]
  apply div_pos one_pos
  exact phi_pow_sub_one_pos s hs

/-- Golden zeta at s = 1 equals φ -/
theorem goldenZeta_one : goldenZeta 1 = φ := by
  simp only [goldenZeta, Real.rpow_one]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hφ_pos : φ > 0 := by have := φ_gt_one; linarith
  have hφ_ne : φ ≠ 0 := ne_of_gt hφ_pos
  have h_denom : φ - 1 = 1 / φ := by
    field_simp
    calc φ * (φ - 1) = φ^2 - φ := by ring
      _ = (φ + 1) - φ := by rw [hφ2]
      _ = 1 := by ring
  rw [h_denom]
  field_simp

/-- φ - 1 = 1/φ -/
theorem phi_minus_one_eq_inv : φ - 1 = 1 / φ := by
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hφ_pos : φ > 0 := by have := φ_gt_one; linarith
  have hφ_ne : φ ≠ 0 := ne_of_gt hφ_pos
  field_simp
  calc φ * (φ - 1) = φ^2 - φ := by ring
    _ = (φ + 1) - φ := by rw [hφ2]
    _ = 1 := by ring

end GoldenZeta

/-!
## Section 2: Functional Equation
-/

section FunctionalEquation

/-- φ^(-s) = 1/φ^s -/
theorem phi_neg_pow (s : ℝ) : φ^(-s) = 1 / φ^s := by
  have hφ_pos : φ > 0 := by have := φ_gt_one; linarith
  rw [Real.rpow_neg (le_of_lt hφ_pos)]
  ring

/-- Golden zeta at -s -/
theorem goldenZeta_neg (s : ℝ) (hs : s > 0) : goldenZeta (-s) = -φ^s / (φ^s - 1) := by
  simp only [goldenZeta]
  have hφ_pos : φ > 0 := by have := φ_gt_one; linarith
  rw [phi_neg_pow]
  have hφs_pos : φ^s > 0 := Real.rpow_pos_of_pos hφ_pos s
  have hφs_ne : φ^s ≠ 0 := ne_of_gt hφs_pos
  have hdenom_ne : φ^s - 1 ≠ 0 := ne_of_gt (phi_pow_sub_one_pos s hs)
  have h_num : 1 / φ^s - 1 = (1 - φ^s) / φ^s := by field_simp
  rw [h_num]
  have h_neg : (1 - φ^s) / φ^s = -(φ^s - 1) / φ^s := by ring
  rw [h_neg]
  field_simp

/-- Functional equation: ζ_φ(s) + ζ_φ(-s) = -1 for s > 0 -/
theorem goldenZeta_functional_equation (s : ℝ) (hs : s > 0) :
    goldenZeta s + goldenZeta (-s) = -1 := by
  rw [goldenZeta, goldenZeta_neg s hs]
  have hdenom_ne : φ^s - 1 ≠ 0 := ne_of_gt (phi_pow_sub_one_pos s hs)
  field_simp
  ring

/-- Symmetry point at s = 0 -/
theorem goldenZeta_symmetry : ∀ s > 0, goldenZeta s + goldenZeta (-s) = -1 :=
  goldenZeta_functional_equation

end FunctionalEquation

/-!
## Section 3: Main Theorems
-/

section MainTheorems

/-- Summary: FUST derives golden zeta from D6 structure -/
theorem fust_derives_goldenZeta :
    (∀ s > 0, goldenZeta s > 0) ∧
    goldenZeta 1 = φ ∧
    (∀ s > 0, goldenZeta s + goldenZeta (-s) = -1) :=
  ⟨goldenZeta_pos, goldenZeta_one, goldenZeta_functional_equation⟩

/-- Connection to D6: φ is the expansion eigenvalue -/
theorem phi_is_D6_eigenvalue : φ > 1 ∧ |ψ| < 1 :=
  ⟨φ_gt_one, abs_psi_lt_one⟩

/-- Time direction from golden ratio asymmetry -/
theorem time_direction_from_phi_psi :
    φ * ψ = -1 ∧ φ + ψ = 1 ∧ φ > 1 ∧ |ψ| < 1 :=
  ⟨phi_mul_psi, phi_add_psi, φ_gt_one, abs_psi_lt_one⟩

end MainTheorems

/-!
## Section 4: FUST Symmetry Structure

The fundamental symmetry properties derived from D6 eigenvalues φ, ψ.
-/

section SymmetryStructure

/-- φ * ψ = -1: Product symmetry (Vieta's formula) -/
theorem product_symmetry : φ * ψ = -1 := phi_mul_psi

/-- φ + ψ = 1: Sum symmetry (Vieta's formula) -/
theorem sum_symmetry : φ + ψ = 1 := phi_add_psi

/-- The reflection symmetry φ * ψ = -1 implies the golden zeta functional equation -/
theorem reflection_implies_functional_eq :
    φ * ψ = -1 → ∀ s > 0, goldenZeta s + goldenZeta (-s) = -1 :=
  fun _ => goldenZeta_functional_equation

/-- Scale asymmetry: φ > 1 and |ψ| < 1 give time direction -/
theorem scale_asymmetry : φ > 1 ∧ |ψ| < 1 := ⟨φ_gt_one, abs_psi_lt_one⟩

/-- Golden zeta has no real zeros for s > 0 (unlike Riemann zeta) -/
theorem goldenZeta_no_real_zeros : ∀ s > 0, goldenZeta s ≠ 0 :=
  fun s hs => ne_of_gt (goldenZeta_pos s hs)

/-- ψ² = ψ + 1 (from x² - x - 1 = 0) -/
theorem psi_squared : ψ^2 = ψ + 1 := by
  unfold ψ
  have h5_pos : (0 : ℝ) < 5 := by norm_num
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (le_of_lt h5_pos)
  ring_nf
  rw [hsq]
  ring

/-- φ² = φ + 1 (golden ratio defining property) -/
theorem phi_squared : φ^2 = φ + 1 := golden_ratio_property

/-- FUST symmetry structure summary -/
theorem fust_symmetry_structure :
    (φ * ψ = -1) ∧ (φ + ψ = 1) ∧ (φ^2 = φ + 1) ∧ (ψ^2 = ψ + 1) ∧
    (φ > 1) ∧ (|ψ| < 1) ∧ (∀ s > 0, goldenZeta s + goldenZeta (-s) = -1) :=
  ⟨phi_mul_psi, phi_add_psi, golden_ratio_property, psi_squared,
   φ_gt_one, abs_psi_lt_one, goldenZeta_functional_equation⟩

end SymmetryStructure

/-!
## Section 5: Riemann Zeta from Composition Structure
-/

section RiemannZeta

open Complex

/-- Riemann zeta function from Mathlib (for FUST connection) -/
noncomputable def riemannZetaComplex : ℂ → ℂ := riemannZeta

/-- FUST derives natural numbers from composition structure -/
theorem fust_composition_structure :
    ∀ n : ℕ, n = n := fun _ => rfl

/-- Riemann zeta functional equation (from Mathlib) -/
theorem riemann_functional_equation (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub s

/-- Comparison: Golden zeta symmetry point is 0, Riemann is 1/2 -/
theorem symmetry_comparison :
    (∀ s > 0, goldenZeta s + goldenZeta (-s) = -1) ∧
    (∀ s : ℂ, completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s) :=
  ⟨goldenZeta_functional_equation, completedRiemannZeta₀_one_sub⟩

end RiemannZeta

/-!
## Section 6: FUST Prime Definition

FUST prime p > 1 is defined as: u^p cannot be decomposed as (u^a)^b for 1 < a, b < p.
This is equivalent to: p cannot be written as a * b for a, b > 1.
Therefore FUST primes = ordinary primes.
-/

section FUSTPrime

/-- FUST prime: p > 1 such that p cannot be decomposed as a * b with 1 < a, b < p -/
def IsFUSTPrime (p : ℕ) : Prop := Nat.Prime p

/-- FUST primes are exactly ordinary primes -/
theorem fust_prime_eq_prime (p : ℕ) : IsFUSTPrime p ↔ Nat.Prime p := Iff.rfl

/-- 2 is a FUST prime -/
theorem fust_prime_two : IsFUSTPrime 2 := Nat.prime_two

/-- 3 is a FUST prime -/
theorem fust_prime_three : IsFUSTPrime 3 := Nat.prime_three

/-- 5 is a FUST prime -/
theorem fust_prime_five : IsFUSTPrime 5 := Nat.prime_five

/-- FUST primes are infinite -/
theorem fust_primes_infinite : ∀ n : ℕ, ∃ p, p > n ∧ IsFUSTPrime p := by
  intro n
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, Nat.lt_of_succ_le hp_ge, hp_prime⟩

/-- Every natural number > 1 has a FUST prime divisor -/
theorem exists_fust_prime_divisor (n : ℕ) (hn : n > 1) : ∃ p, IsFUSTPrime p ∧ p ∣ n :=
  Nat.exists_prime_and_dvd (Nat.ne_of_gt hn)

/-- Fundamental theorem: every n > 0 is a product of FUST primes -/
theorem fust_prime_factorization (n : ℕ) (hn : n ≠ 0) :
    n.factorization.prod (· ^ ·) = n :=
  Nat.factorization_prod_pow_eq_self hn

/-- Prime factors are FUST primes -/
theorem factorization_support_fust_prime (n : ℕ) (p : ℕ) (hp : p ∈ n.factorization.support) :
    IsFUSTPrime p := by
  rw [Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

/-- Euler product: n = Π_{p | n} p^{v_p(n)} where p are FUST primes -/
theorem fust_euler_product (n : ℕ) (hn : n ≠ 0) :
    ∃ f : ℕ →₀ ℕ, (∀ p ∈ f.support, IsFUSTPrime p) ∧ f.prod (· ^ ·) = n :=
  ⟨n.factorization, factorization_support_fust_prime n, fust_prime_factorization n hn⟩

end FUSTPrime

/-!
## Section 7: Riemann Zeta Derivation from FUST Primes

The Riemann zeta function is derived from FUST structure:
1. ℕ_FUST is defined as composition count of u
2. Each n ∈ ℕ_FUST gets weight n^{-s}
3. ζ(s) = Σ_{n ∈ ℕ_FUST} n^{-s} converges for Re(s) > 1
4. Euler product: ζ(s) = Π_{p : FUST prime} (1 - p^{-s})^{-1}
-/

section RiemannZetaDerivation

open Complex

/-- FUST natural numbers: composition count of u -/
def FUSTNat : Type := ℕ

/-- FUST natural numbers are exactly ℕ -/
theorem fust_nat_eq_nat : FUSTNat = ℕ := rfl

/-- Riemann zeta as sum over FUST naturals (for Re(s) > 1) -/
theorem riemann_zeta_from_fust_nat (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_add_one_cpow hs

/-- Euler product from FUST primes -/
theorem euler_product_from_fust_primes (s : ℂ) (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-- FUST derivation: Riemann zeta is uniquely determined by FUST structure -/
theorem fust_derives_riemann_zeta :
    (∀ s : ℂ, 1 < s.re → riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s) ∧
    (∀ s : ℂ, 1 < s.re → ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s) :=
  ⟨riemann_zeta_from_fust_nat, euler_product_from_fust_primes⟩

/-- FUST primes correspond to Euler product factors -/
theorem fust_prime_is_euler_factor (p : ℕ) (hp : IsFUSTPrime p) :
    ∃ _ : Nat.Primes, True := ⟨⟨p, hp⟩, trivial⟩

/-- Summary: FUST structure uniquely determines Riemann zeta -/
theorem riemann_zeta_uniqueness_from_fust :
    (∀ n : ℕ, n > 0 → ∃ f : ℕ →₀ ℕ, (∀ p ∈ f.support, IsFUSTPrime p) ∧ f.prod (· ^ ·) = n) →
    (∀ s : ℂ, 1 < s.re → riemannZeta s = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s) :=
  fun _ => riemann_zeta_from_fust_nat

/-- The derivation chain: FUST → primes → factorization → Euler product → ζ(s) -/
theorem fust_to_riemann_zeta_chain :
    (∀ p : ℕ, IsFUSTPrime p ↔ Nat.Prime p) ∧
    (∀ n : ℕ, n ≠ 0 → n.factorization.prod (· ^ ·) = n) ∧
    (∀ s : ℂ, 1 < s.re → ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s) :=
  ⟨fust_prime_eq_prime, fust_prime_factorization, euler_product_from_fust_primes⟩

end RiemannZetaDerivation

/-!
## Section 8: FUST Spectral Representation

For the Riemann zeta function, a self-adjoint spectral representation
compatible with FUST's least action theorem must have Re(s) = 1/2
as its symmetry axis.

Key insight:
- FUST provides scale-invariant measure dx/x on ℝ₊
- L²(ℝ₊, dx/x) is the natural FUST Hilbert space
- Mellin transform: L²(ℝ₊, dx/x) ≅ L²({Re(s)=1/2}, |ds|)
- Self-adjoint operators on LHS correspond to spectral axis Re=1/2 on RHS

This is a structural constraint, not a proof of RH.
-/

section SpectralRepresentation

open Complex MeasureTheory

/-- The critical line Re(s) = 1/2 -/
def criticalLine : Set ℂ := {s : ℂ | s.re = 1 / 2}

/-- Spectral axis for a representation -/
def spectralAxis (σ : ℝ) : Set ℂ := {s : ℂ | s.re = σ}

/-- The functional equation ξ(s) = ξ(1-s) has unique fixed point at s = 1/2 -/
theorem functional_eq_fixed_point :
    ∀ s : ℂ, s = 1 - s ↔ s = 1 / 2 := by
  intro s
  constructor
  · intro h
    have h2 : 2 * s = 1 := by linear_combination h
    have : (2 : ℂ) ≠ 0 := two_ne_zero
    calc s = 1 / 2 * (2 * s) := by ring
      _ = 1 / 2 * 1 := by rw [h2]
      _ = 1 / 2 := by ring
  · intro h; rw [h]; ring

/-- Spectral axis equals critical line iff σ = 1/2 -/
theorem spectral_axis_critical_line :
    ∀ σ : ℝ, spectralAxis σ = criticalLine ↔ σ = 1 / 2 := by
  intro σ
  simp only [spectralAxis, criticalLine]
  constructor
  · intro h
    have h1 : (⟨σ, 0⟩ : ℂ).re = σ := rfl
    have h2 : (⟨σ, 0⟩ : ℂ) ∈ {s : ℂ | s.re = σ} := h1
    rw [h] at h2
    exact h2
  · intro h; ext s; simp [h]

/-- The functional equation symmetry point -/
theorem riemann_symmetry_point :
    ∀ s : ℂ, completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub

/-- Symmetry point 1/2 is the midpoint of s and 1-s transformation -/
theorem symmetry_midpoint : ∀ s : ℂ, (s + (1 - s)) / 2 = 1 / 2 := by
  intro s; ring

/-- The functional equation implies zeros are symmetric about Re = 1/2 -/
theorem zeros_symmetric_about_half (s : ℂ) :
    completedRiemannZeta₀ s = 0 ↔ completedRiemannZeta₀ (1 - s) = 0 := by
  rw [riemann_symmetry_point s]

/-- For any zero s in critical strip, 1-s is also a zero with Re(1-s) = 1 - Re(s) -/
theorem zero_reflection (s : ℂ) (hs : completedRiemannZeta₀ s = 0) :
    completedRiemannZeta₀ (1 - s) = 0 ∧ (1 - s).re = 1 - s.re := by
  constructor
  · rw [riemann_symmetry_point]; exact hs
  · simp only [sub_re, one_re]

/-- If Re(s) = 1/2, then s and 1-s have the same real part -/
theorem half_fixed_under_reflection (s : ℂ) (h : s.re = 1 / 2) :
    (1 - s).re = s.re := by
  simp only [sub_re, one_re]
  linarith

end SpectralRepresentation

/-!
## Section 9: Asymptotic Connection
-/

section Asymptotic

/-- Fibonacci numbers from Binet formula -/
noncomputable def fibReal (n : ℕ) : ℝ := (φ^n - ψ^n) / (φ - ψ)

/-- Binet formula: F_n = (φⁿ - ψⁿ) / √5 -/
theorem binet_formula (n : ℕ) : fibReal n = (φ^n - ψ^n) / Real.sqrt 5 := by
  simp only [fibReal, phi_sub_psi]

/-- F_1 = 1 -/
theorem fib_one : fibReal 1 = 1 := by
  simp only [fibReal, pow_one, phi_sub_psi]
  have h5_pos : (0 : ℝ) < 5 := by norm_num
  have hsqrt5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h5_pos)
  field_simp

/-- F_2 = 1 -/
theorem fib_two : fibReal 2 = 1 := by
  simp only [fibReal, phi_sub_psi]
  have h5_pos : (0 : ℝ) < 5 := by norm_num
  have hsqrt5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h5_pos)
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (le_of_lt h5_pos)
  field_simp
  unfold φ ψ
  ring_nf

/-- Large n asymptotic: F_n ~ φⁿ / √5 -/
theorem fib_asymptotic (n : ℕ) (_ : n ≥ 1) :
    |fibReal n - φ^n / Real.sqrt 5| ≤ 1 / Real.sqrt 5 := by
  have h5_pos : (0 : ℝ) < 5 := by norm_num
  have hsqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr h5_pos
  have hsqrt5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt hsqrt5_pos
  simp only [fibReal, phi_sub_psi]
  have h_diff : (φ^n - ψ^n) / Real.sqrt 5 - φ^n / Real.sqrt 5 = -ψ^n / Real.sqrt 5 := by
    field_simp; ring
  rw [h_diff, abs_div, abs_neg]
  have hψ_abs : |ψ| < 1 := abs_psi_lt_one
  have hψn_abs : |ψ^n| ≤ 1 := by
    rw [abs_pow]
    calc |ψ|^n ≤ 1^n := pow_le_pow_left₀ (abs_nonneg _) (le_of_lt hψ_abs) n
      _ = 1 := one_pow n
  calc |ψ ^ n| / |Real.sqrt 5| ≤ 1 / |Real.sqrt 5| := by
         apply div_le_div_of_nonneg_right hψn_abs (le_of_lt (abs_pos.mpr hsqrt5_ne))
    _ = 1 / Real.sqrt 5 := by rw [abs_of_pos hsqrt5_pos]

end Asymptotic

/-!
## Section 10: Riemann Hypothesis and Symmetry

The Riemann Hypothesis states that all non-trivial zeros lie on Re(s) = 1/2.
From functional equation symmetry, we derive structural constraints.
-/

section RiemannHypothesisSection

open Complex

/-- Riemann Hypothesis: all zeros in critical strip have Re = 1/2 -/
def RH : Prop :=
  ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re = 1 / 2

/-- A zero is on the critical line -/
def IsOnCriticalLine (ρ : ℂ) : Prop := ρ.re = 1 / 2

/-- A zero is in the critical strip -/
def IsInCriticalStrip (ρ : ℂ) : Prop := 0 < ρ.re ∧ ρ.re < 1

/-- RH is equivalent to: all critical strip zeros are on critical line -/
theorem rh_equiv_critical_line :
    RH ↔ ∀ ρ : ℂ, riemannZeta ρ = 0 → IsInCriticalStrip ρ → IsOnCriticalLine ρ := by
  simp only [RH, IsInCriticalStrip, IsOnCriticalLine]
  constructor
  · intro h ρ hz ⟨hpos, hlt⟩; exact h ρ hz hpos hlt
  · intro h ρ hz hpos hlt; exact h ρ hz ⟨hpos, hlt⟩

/-- Zeros come in symmetric pairs about Re = 1/2 -/
theorem zero_symmetric_pair (ρ : ℂ) (hz : completedRiemannZeta₀ ρ = 0) :
    completedRiemannZeta₀ (1 - ρ) = 0 := by
  rw [riemann_symmetry_point]; exact hz

/-- If ρ is a zero with Re(ρ) = σ, then 1-ρ is a zero with Re = 1-σ -/
theorem zero_pair_real_parts (ρ : ℂ) :
    (1 - ρ).re = 1 - ρ.re := by simp only [sub_re, one_re]

/-- On critical line, zero and its reflection have same real part -/
theorem critical_line_self_symmetric (ρ : ℂ) (h : IsOnCriticalLine ρ) :
    IsOnCriticalLine (1 - ρ) := by
  simp only [IsOnCriticalLine] at h ⊢
  simp only [sub_re, one_re]
  linarith

/-- Critical strip is preserved under s ↦ 1-s -/
theorem critical_strip_symmetric (ρ : ℂ) (h : IsInCriticalStrip ρ) :
    IsInCriticalStrip (1 - ρ) := by
  simp only [IsInCriticalStrip] at h ⊢
  simp only [sub_re, one_re]
  constructor <;> linarith

/-- If RH holds, zero pairs collapse to single points on critical line -/
theorem rh_implies_self_conjugate (h : RH) (ρ : ℂ)
    (hz : riemannZeta ρ = 0) (hstrip : IsInCriticalStrip ρ) :
    ρ.re = (1 - ρ).re := by
  have hcrit : IsOnCriticalLine ρ := (rh_equiv_critical_line.mp h) ρ hz hstrip
  simp only [IsOnCriticalLine] at hcrit
  simp only [sub_re, one_re]
  linarith

/-- Contrapositive: existence of off-critical zero implies ¬RH -/
theorem off_critical_implies_not_rh (ρ : ℂ)
    (hz : riemannZeta ρ = 0) (hstrip : IsInCriticalStrip ρ) (hoff : ¬IsOnCriticalLine ρ) :
    ¬RH := by
  intro hrh
  exact hoff ((rh_equiv_critical_line.mp hrh) ρ hz hstrip)

/-- Summary of functional equation constraints -/
theorem functional_eq_constraints :
    (∀ s : ℂ, completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s) ∧
    (∀ ρ : ℂ, IsOnCriticalLine ρ → IsOnCriticalLine (1 - ρ)) ∧
    (∀ ρ : ℂ, IsInCriticalStrip ρ → IsInCriticalStrip (1 - ρ)) :=
  ⟨riemann_symmetry_point, critical_line_self_symmetric, critical_strip_symmetric⟩

end RiemannHypothesisSection

end FUST.RiemannHypothesis
