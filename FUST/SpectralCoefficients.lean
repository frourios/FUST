/-
FUST D₆ Spectral Coefficients

D₆(xⁿ) = Cₙ · x^{n-1} / (√5)⁵ where Cₙ = √5 · (F_{3n} - 3F_{2n} + Fₙ).
The polynomial kernel {1, x, x²} (dim 3) and Laurent kernel {x⁻², 1, x, x²} (dim 4)
are fundamental properties of the golden-ratio 6-point difference operator.
-/

import FUST.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio

namespace FUST.SpectralCoefficients

open FUST Real

/-! ## Section 1: D₆ Spectral Coefficients (ℕ → ℝ)

D₆(xⁿ) = Cₙ · x^{n-1} / (√5)⁵ for n ≥ 3

The coefficient Cₙ encodes the spectral structure of D₆.
-/

section SpectralCoefficients

/-- Coefficient C_n for D₆(x^n) = C_n · x^{n-1} / (√5)⁵ -/
noncomputable def D6Coeff (n : ℕ) : ℝ :=
  φ^(3*n) - 3*φ^(2*n) + φ^n - ψ^n + 3*ψ^(2*n) - ψ^(3*n)

/-- C_0 = 0 (constant annihilation) -/
theorem D6Coeff_zero : D6Coeff 0 = 0 := by
  simp only [D6Coeff, Nat.mul_zero, pow_zero]
  ring

/-- C_1 = 0 (linear annihilation) -/
theorem D6Coeff_one : D6Coeff 1 = 0 := by
  simp only [D6Coeff, Nat.mul_one]
  have hφ3 : φ^3 = 2*φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2*ψ + 1 := by
    have hψ2 : ψ^2 = ψ + 1 := psi_sq
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [hψ2]
      _ = 2*ψ + 1 := by ring
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  have h : φ^(3*1) - 3*φ^(2*1) + φ^1 - ψ^1 + 3*ψ^(2*1) - ψ^(3*1)
    = φ^3 - 3*φ^2 + φ - ψ + 3*ψ^2 - ψ^3 := by ring
  rw [h, hφ3, hφ2, hψ2, hψ3]
  linarith

/-- C_2 = 0 (quadratic annihilation) -/
theorem D6Coeff_two : D6Coeff 2 = 0 := by
  simp only [D6Coeff]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ4 : φ^4 = 3*φ + 2 := by
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ+1) * (φ+1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ+1) + 2*φ + 1 := by rw [hφ2]
      _ = 3*φ + 2 := by ring
  have hψ4 : ψ^4 = 3*ψ + 2 := by
    calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ+1) * (ψ+1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ+1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3*ψ + 2 := by ring
  have hφ6 : φ^6 = 8*φ + 5 := by
    calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ+2) * (φ+1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ+1) + 5*φ + 2 := by rw [hφ2]
      _ = 8*φ + 5 := by ring
  have hψ6 : ψ^6 = 8*ψ + 5 := by
    calc ψ^6 = ψ^4 * ψ^2 := by ring
      _ = (3*ψ+2) * (ψ+1) := by rw [hψ4, hψ2]
      _ = 3*ψ^2 + 5*ψ + 2 := by ring
      _ = 3*(ψ+1) + 5*ψ + 2 := by rw [hψ2]
      _ = 8*ψ + 5 := by ring
  have hsum : φ + ψ = 1 := phi_add_psi
  calc φ^6 - 3*φ^4 + φ^2 - ψ^2 + 3*ψ^4 - ψ^6
    = (8*φ+5) - 3*(3*φ+2) + (φ+1) - (ψ+1) + 3*(3*ψ+2) - (8*ψ+5) := by
        rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]
    _ = 0 := by linarith

/-- C_3 = 12√5 (first non-kernel coefficient) -/
theorem D6Coeff_three : D6Coeff 3 = 12 * Real.sqrt 5 := by
  simp only [D6Coeff]
  have hφ3 : φ^3 = 2*φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2*ψ + 1 := by
    have hψ2 : ψ^2 = ψ + 1 := psi_sq
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ+1) * ψ := by rw [hψ2]
      _ = ψ^2 + ψ := by ring
      _ = (ψ+1) + ψ := by rw [hψ2]
      _ = 2*ψ + 1 := by ring
  have hφ6 : φ^6 = 8*φ + 5 := by
    have hφ2 : φ^2 = φ + 1 := golden_ratio_property
    have hφ4 : φ^4 = 3*φ + 2 := by
      calc φ^4 = φ^2 * φ^2 := by ring
        _ = (φ+1) * (φ+1) := by rw [hφ2]
        _ = φ^2 + 2*φ + 1 := by ring
        _ = (φ+1) + 2*φ + 1 := by rw [hφ2]
        _ = 3*φ + 2 := by ring
    calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ+2) * (φ+1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ+1) + 5*φ + 2 := by rw [hφ2]
      _ = 8*φ + 5 := by ring
  have hψ6 : ψ^6 = 8*ψ + 5 := by
    have hψ2 : ψ^2 = ψ + 1 := psi_sq
    have hψ4 : ψ^4 = 3*ψ + 2 := by
      calc ψ^4 = ψ^2 * ψ^2 := by ring
        _ = (ψ+1) * (ψ+1) := by rw [hψ2]
        _ = ψ^2 + 2*ψ + 1 := by ring
        _ = (ψ+1) + 2*ψ + 1 := by rw [hψ2]
        _ = 3*ψ + 2 := by ring
    calc ψ^6 = ψ^4 * ψ^2 := by ring
      _ = (3*ψ+2) * (ψ+1) := by rw [hψ4, hψ2]
      _ = 3*ψ^2 + 5*ψ + 2 := by ring
      _ = 3*(ψ+1) + 5*ψ + 2 := by rw [hψ2]
      _ = 8*ψ + 5 := by ring
  have hφ9 : φ^9 = 34*φ + 21 := by
    calc φ^9 = φ^6 * φ^3 := by ring
      _ = (8*φ+5) * (2*φ+1) := by rw [hφ6, hφ3]
      _ = 16*φ^2 + 18*φ + 5 := by ring
      _ = 16*(φ+1) + 18*φ + 5 := by rw [golden_ratio_property]
      _ = 34*φ + 21 := by ring
  have hψ9 : ψ^9 = 34*ψ + 21 := by
    calc ψ^9 = ψ^6 * ψ^3 := by ring
      _ = (8*ψ+5) * (2*ψ+1) := by rw [hψ6, hψ3]
      _ = 16*ψ^2 + 18*ψ + 5 := by ring
      _ = 16*(ψ+1) + 18*ψ + 5 := by rw [psi_sq]
      _ = 34*ψ + 21 := by ring
  have hsum : φ + ψ = 1 := phi_add_psi
  have hdiff : φ - ψ = Real.sqrt 5 := phi_sub_psi
  calc φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9
    = (34*φ+21) - 3*(8*φ+5) + (2*φ+1) - (2*ψ+1) + 3*(8*ψ+5) - (34*ψ+21) := by
        rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]
    _ = 12*φ - 12*ψ := by ring
    _ = 12*(φ - ψ) := by ring
    _ = 12 * Real.sqrt 5 := by rw [hdiff]

/-- D6Coeff expressed via Fibonacci: C_n = √5 · (F_{3n} - 3F_{2n} + F_n) -/
theorem D6Coeff_fibonacci (n : ℕ) :
    D6Coeff n = Real.sqrt 5 * (Nat.fib (3*n) - 3 * Nat.fib (2*n) + Nat.fib n) := by
  simp only [D6Coeff]
  have h1 : (Nat.fib (3*n) : ℝ) = (φ^(3*n) - ψ^(3*n)) / Real.sqrt 5 := coe_fib_eq (3*n)
  have h2 : (Nat.fib (2*n) : ℝ) = (φ^(2*n) - ψ^(2*n)) / Real.sqrt 5 := coe_fib_eq (2*n)
  have h3 : (Nat.fib n : ℝ) = (φ^n - ψ^n) / Real.sqrt 5 := coe_fib_eq n
  have hsqrt5_ne : Real.sqrt 5 ≠ 0 := by positivity
  rw [h1, h2, h3]
  field_simp
  ring

/-- C_3 = 12√5 ≠ 0 -/
theorem D6Coeff_three_ne_zero : D6Coeff 3 ≠ 0 := by
  rw [D6Coeff_three]
  have : (0 : ℝ) < 12 * Real.sqrt 5 := by positivity
  linarith

/-- Helper: √5 > 2.2 -/
theorem sqrt5_gt_22 : Real.sqrt 5 > 2.2 := by
  have h1 : (0 : ℝ) ≤ 2.2 := by norm_num
  have h2 : (2.2 : ℝ)^2 < 5 := by norm_num
  exact (Real.lt_sqrt h1).mpr h2

/-- Helper: φ > 1.6 -/
theorem phi_gt_16 : φ > 1.6 := by
  have h := sqrt5_gt_22
  calc φ = (1 + Real.sqrt 5) / 2 := rfl
    _ > (1 + 2.2) / 2 := by linarith
    _ = 1.6 := by norm_num

/-- Helper: φ^3 > 4 -/
theorem phi_cubed_gt_4 : φ^3 > 4 := by
  have h1 : φ^3 = 2*φ + 1 := phi_cubed
  linarith [phi_gt_16]

/-- Helper: φ^n ≥ φ^m for n ≥ m -/
theorem phi_pow_mono {n m : ℕ} (h : m ≤ n) : φ^m ≤ φ^n :=
  pow_right_mono₀ (le_of_lt φ_gt_one) h

/-- Helper: φ^n > 3 for n ≥ 3 -/
theorem phi_pow_gt_3 (n : ℕ) (hn : n ≥ 3) : φ^n > 3 := by
  have h := phi_pow_mono hn
  linarith [phi_cubed_gt_4]

/-- Helper: φ^6 > 17 -/
theorem phi_pow_6_gt_17 : φ^6 > 17 := by
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hφ4 : φ^4 = 3*φ + 2 := by
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ+1) * (φ+1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ+1) + 2*φ + 1 := by rw [hφ2]
      _ = 3*φ + 2 := by ring
  have hφ6 : φ^6 = 8*φ + 5 := by
    calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ+2) * (φ+1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ+1) + 5*φ + 2 := by rw [hφ2]
      _ = 8*φ + 5 := by ring
  linarith [phi_gt_16]

/-- F_{3n} + F_n > 3·F_{2n} for n ≥ 3 -/
theorem fib_combination_pos (n : ℕ) (hn : n ≥ 3) :
    Nat.fib (3*n) + Nat.fib n > 3 * Nat.fib (2*n) := by
  have hφ_pos : 0 < φ := phi_pos
  have hψ_abs_lt_1 : |ψ| < 1 := abs_psi_lt_one
  have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have hφn_gt_4 : φ^n > 4 := by
    have h := phi_pow_mono hn
    linarith [phi_cubed_gt_4]
  have h2n_ge_6 : 6 ≤ 2*n := by omega
  have hφ2n_gt_17 : φ^(2*n) > 17 := lt_of_lt_of_le phi_pow_6_gt_17 (phi_pow_mono h2n_ge_6)
  have h3n_eq : φ^(3*n) = φ^n * φ^(2*n) := by rw [← pow_add]; congr 1; omega
  -- |ψ^k| ≤ 1
  have hψn : |ψ^n| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (le_of_lt hψ_abs_lt_1)
  have hψ2n : |ψ^(2*n)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (le_of_lt hψ_abs_lt_1)
  have hψ3n : |ψ^(3*n)| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (le_of_lt hψ_abs_lt_1)
  have hψn_bd := abs_le.mp hψn
  have hψ2n_bd := abs_le.mp hψ2n
  have hψ3n_bd := abs_le.mp hψ3n
  -- φ^{3n} + φ^n - 3φ^{2n} > 5
  have h_φ_diff : φ^(3*n) + φ^n - 3 * φ^(2*n) > 5 := by
    -- φ^n * φ^{2n} + φ^n - 3 * φ^{2n} = φ^{2n} * (φ^n - 3) + φ^n
    have h1 : φ^n - 3 > 1 := by linarith
    have h2 : φ^(2*n) * (φ^n - 3) > 17 := by nlinarith [h1, hφ2n_gt_17]
    have h3 : φ^n * φ^(2*n) + φ^n - 3 * φ^(2*n) = φ^(2*n) * (φ^n - 3) + φ^n := by ring
    linarith [h3n_eq]
  -- ψ^{3n} + ψ^n - 3ψ^{2n} ≥ -5
  have h_ψ_bound : ψ^(3*n) + ψ^n - 3 * ψ^(2*n) ≥ -5 := by linarith [hψ3n_bd.1, hψn_bd.1, hψ2n_bd.2]
  -- Combined inequality
  have h_key : φ^(3*n) + φ^n - ψ^(3*n) - ψ^n > 3 * (φ^(2*n) - ψ^(2*n)) := by linarith
  -- Convert ℕ inequality to ℝ
  have h_real : (Nat.fib (3*n) : ℝ) + Nat.fib n > 3 * Nat.fib (2*n) := by
    rw [coe_fib_eq (3*n), coe_fib_eq (2*n), coe_fib_eq n]
    have hsqrt5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt hsqrt5_pos
    -- FUST.φ = Real.goldenRatio and FUST.ψ = Real.goldenConj by definition
    have hφ_eq : φ = Real.goldenRatio := rfl
    have hψ_eq : ψ = Real.goldenConj := rfl
    -- Rewrite h_key using goldenRatio/goldenConj
    rw [hφ_eq, hψ_eq] at h_key
    have lhs_eq : (Real.goldenRatio^(3*n) - Real.goldenConj^(3*n)) / Real.sqrt 5
        + (Real.goldenRatio^n - Real.goldenConj^n) / Real.sqrt 5
        = (Real.goldenRatio^(3*n) + Real.goldenRatio^n - Real.goldenConj^(3*n)
        - Real.goldenConj^n) / Real.sqrt 5 := by
      field_simp; ring
    have rhs_eq : 3 * ((Real.goldenRatio^(2*n) - Real.goldenConj^(2*n)) / Real.sqrt 5)
        = 3 * (Real.goldenRatio^(2*n) - Real.goldenConj^(2*n)) / Real.sqrt 5 := by field_simp
    rw [lhs_eq, rhs_eq]
    rw [gt_iff_lt, div_lt_div_iff₀ hsqrt5_pos hsqrt5_pos]
    nlinarith [h_key, hsqrt5_pos]
  exact_mod_cast h_real

/-- C_n ≠ 0 for n ≥ 3 (spectrum is non-trivial) -/
theorem D6Coeff_ne_zero_of_ge_three (n : ℕ) (hn : n ≥ 3) : D6Coeff n ≠ 0 := by
  rw [D6Coeff_fibonacci]
  have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have h_fib_pos : Nat.fib (3*n) + Nat.fib n > 3 * Nat.fib (2*n) := fib_combination_pos n hn
  have h : (0 : ℝ) < Nat.fib (3*n) - 3 * Nat.fib (2*n) + Nat.fib n := by
    have : (Nat.fib (3*n) : ℝ) + Nat.fib n > 3 * Nat.fib (2*n) := by exact_mod_cast h_fib_pos
    linarith
  exact ne_of_gt (mul_pos hsqrt5_pos h)

/-- Kernel characterization: C_n = 0 iff n ≤ 2 -/
theorem D6Coeff_eq_zero_iff (n : ℕ) : D6Coeff n = 0 ↔ n ≤ 2 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    exact D6Coeff_ne_zero_of_ge_three n hne h
  · intro h
    interval_cases n <;> simp [D6Coeff_zero, D6Coeff_one, D6Coeff_two]

end SpectralCoefficients

/-! ## Section 2: Factorization and Asymptotics -/

section ExplicitComputation

/-- D6Coeff factorization: C_n = (φ^n - ψ^n) * (φ^{2n} + ψ^{2n} + (-1)^n + 1 - 3(φ^n + ψ^n)) -/
theorem D6Coeff_factored (n : ℕ) :
    D6Coeff n = (φ^n - ψ^n) * (φ^(2*n) + ψ^(2*n) + (-1:ℝ)^n + 1 - 3*(φ^n + ψ^n)) := by
  simp only [D6Coeff]
  have h_phi_psi : φ * ψ = -1 := phi_mul_psi
  have h_prod : (φ*ψ)^n = (-1:ℝ)^n := by rw [h_phi_psi]
  have h2n_φ : φ^(2*n) = (φ^n)^2 := by rw [← pow_mul]; ring_nf
  have h2n_ψ : ψ^(2*n) = (ψ^n)^2 := by rw [← pow_mul]; ring_nf
  have h3n_φ : φ^(3*n) = (φ^n)^3 := by rw [← pow_mul]; ring_nf
  have h3n_ψ : ψ^(3*n) = (ψ^n)^3 := by rw [← pow_mul]; ring_nf
  rw [h2n_φ, h2n_ψ, h3n_φ, h3n_ψ]
  have key : (φ^n)^3 - 3*(φ^n)^2 + φ^n - ψ^n + 3*(ψ^n)^2 - (ψ^n)^3
      = (φ^n - ψ^n) * ((φ^n)^2 + (ψ^n)^2 + (φ*ψ)^n + 1 - 3*(φ^n + ψ^n)) := by
    rw [mul_pow]
    ring
  rw [key, h_prod]

/-- For large n, C_n ~ φ^{3n} (dominant term) -/
theorem D6Coeff_asymptotic (n : ℕ) (hn : n ≥ 3) :
    ∃ C > 0, |D6Coeff n - φ^(3*n)| ≤ C * φ^(2*n) := by
  use 5
  constructor
  · norm_num
  -- D6Coeff - φ^{3n} = -3φ^{2n} + φ^n - ψ^n + 3ψ^{2n} - ψ^{3n}
  have h_diff : D6Coeff n - φ^(3*n) = -3*φ^(2*n) + φ^n - ψ^n + 3*ψ^(2*n) - ψ^(3*n) := by
    simp only [D6Coeff]; ring
  rw [h_diff]
  have hφ_pos : 0 < φ := phi_pos
  have hψ_abs : |ψ| < 1 := abs_psi_lt_one
  have hψn : |ψ^n| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (le_of_lt hψ_abs)
  have hψ2n : |ψ^(2*n)| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (le_of_lt hψ_abs)
  have hψ3n : |ψ^(3*n)| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (le_of_lt hψ_abs)
  have hψn_bd := abs_le.mp hψn
  have hψ2n_bd := abs_le.mp hψ2n
  have hψ3n_bd := abs_le.mp hψ3n
  have hφn_pos : 0 < φ^n := pow_pos hφ_pos n
  have hφ2n_pos : 0 < φ^(2*n) := pow_pos hφ_pos (2*n)
  have hφn_le : φ^n ≤ φ^(2*n) := phi_pow_mono (by omega : n ≤ 2*n)
  have h6 : φ^(2*n) ≥ φ^6 := phi_pow_mono (by omega : 6 ≤ 2*n)
  have hφ6 : φ^6 > 17 := phi_pow_6_gt_17
  -- Lower and upper bounds for the expression
  have h_lower : -3*φ^(2*n) + φ^n - ψ^n + 3*ψ^(2*n) - ψ^(3*n) ≥ -(5*φ^(2*n)) := by
    have : -3*φ^(2*n) + φ^n - ψ^n + 3*ψ^(2*n) - ψ^(3*n)
        ≥ -3*φ^(2*n) + 0 - 1 + 3*(-1) - 1 := by linarith [hφn_pos, hψn_bd.1, hψ2n_bd.1, hψ3n_bd.2]
    linarith
  have h_upper : -3*φ^(2*n) + φ^n - ψ^n + 3*ψ^(2*n) - ψ^(3*n) ≤ 5*φ^(2*n) := by
    have : -3*φ^(2*n) + φ^n - ψ^n + 3*ψ^(2*n) - ψ^(3*n)
        ≤ -3*φ^(2*n) + φ^(2*n) + 1 + 3 + 1 := by linarith [hφn_le, hψn_bd.2, hψ2n_bd.2, hψ3n_bd.1]
    linarith
  rw [abs_le]
  constructor <;> linarith

end ExplicitComputation

/-! ## Section 3: Extended D₆ Kernel (ℤ → ℝ) -/

section ExtendedKernel

noncomputable def D6CoeffZ (n : ℤ) : ℝ :=
  φ ^ (3 * n) - 3 * φ ^ (2 * n) + φ ^ n - ψ ^ n + 3 * ψ ^ (2 * n) - ψ ^ (3 * n)

theorem D6CoeffZ_natCast (n : ℕ) : D6CoeffZ (n : ℤ) = D6Coeff n := by
  simp only [D6CoeffZ, D6Coeff, zpow_natCast]
  norm_cast

theorem D6CoeffZ_zero : D6CoeffZ 0 = 0 := by simp [D6CoeffZ]

theorem D6CoeffZ_one : D6CoeffZ 1 = 0 := by
  rw [show (1 : ℤ) = (1 : ℕ) from rfl, D6CoeffZ_natCast, D6Coeff_one]

theorem D6CoeffZ_two : D6CoeffZ 2 = 0 := by
  rw [show (2 : ℤ) = (2 : ℕ) from rfl, D6CoeffZ_natCast, D6Coeff_two]

private theorem phi_neg_zpow (k : ℤ) : φ ^ (-k) = (-ψ) ^ k := by
  rw [zpow_neg, ← inv_zpow]
  congr 1
  exact Real.inv_goldenRatio

private theorem psi_neg_zpow (k : ℤ) : ψ ^ (-k) = (-φ) ^ k := by
  rw [zpow_neg, ← inv_zpow]
  congr 1
  rw [inv_eq_of_mul_eq_one_left]
  linarith [phi_mul_psi]

theorem D6CoeffZ_neg_even (n : ℤ) (hn : Even n) : D6CoeffZ (-n) = -D6CoeffZ n := by
  simp only [D6CoeffZ]
  have h3n : Even (3 * n) := hn.mul_left 3
  have h2n : Even (2 * n) := hn.mul_left 2
  rw [show 3 * -n = -(3 * n) from by ring, show 2 * -n = -(2 * n) from by ring]
  rw [phi_neg_zpow, phi_neg_zpow, phi_neg_zpow,
      psi_neg_zpow, psi_neg_zpow, psi_neg_zpow]
  rw [h3n.neg_zpow, h2n.neg_zpow, hn.neg_zpow,
      h3n.neg_zpow, h2n.neg_zpow, hn.neg_zpow]
  ring

theorem D6CoeffZ_neg_two : D6CoeffZ (-2) = 0 := by
  have h := D6CoeffZ_neg_even 2 ⟨1, by ring⟩
  rw [D6CoeffZ_two, neg_zero] at h
  exact h

theorem D6_extended_kernel_dim :
    D6CoeffZ (-2) = 0 ∧ D6CoeffZ 0 = 0 ∧ D6CoeffZ 1 = 0 ∧ D6CoeffZ 2 = 0 :=
  ⟨D6CoeffZ_neg_two, D6CoeffZ_zero, D6CoeffZ_one, D6CoeffZ_two⟩

theorem D6CoeffZ_neg_one_ne_zero : D6CoeffZ (-1) ≠ 0 := by
  simp only [D6CoeffZ]
  rw [show (3 : ℤ) * (-1) = -3 from by ring, show (2 : ℤ) * (-1) = -2 from by ring]
  rw [phi_neg_zpow, phi_neg_zpow, phi_neg_zpow,
      psi_neg_zpow, psi_neg_zpow, psi_neg_zpow]
  rw [show (-ψ) ^ (3 : ℤ) = -(ψ ^ (3 : ℤ)) from
        (Odd.neg_zpow (⟨1, by ring⟩ : Odd (3 : ℤ)) ψ),
      show (-ψ) ^ (2 : ℤ) = ψ ^ (2 : ℤ) from
        (Even.neg_zpow (⟨1, by ring⟩ : Even (2 : ℤ)) ψ),
      show (-ψ) ^ (1 : ℤ) = -ψ ^ (1 : ℤ) from
        (Odd.neg_zpow (⟨0, by ring⟩ : Odd (1 : ℤ)) ψ),
      show (-φ) ^ (3 : ℤ) = -(φ ^ (3 : ℤ)) from
        (Odd.neg_zpow (⟨1, by ring⟩ : Odd (3 : ℤ)) φ),
      show (-φ) ^ (2 : ℤ) = φ ^ (2 : ℤ) from
        (Even.neg_zpow (⟨1, by ring⟩ : Even (2 : ℤ)) φ),
      show (-φ) ^ (1 : ℤ) = -φ ^ (1 : ℤ) from
        (Odd.neg_zpow (⟨0, by ring⟩ : Odd (1 : ℤ)) φ)]
  rw [show ψ ^ (3 : ℤ) = ψ ^ 3 from by norm_cast,
      show ψ ^ (2 : ℤ) = ψ ^ 2 from by norm_cast,
      show ψ ^ (1 : ℤ) = ψ from zpow_one ψ,
      show φ ^ (3 : ℤ) = φ ^ 3 from by norm_cast,
      show φ ^ (2 : ℤ) = φ ^ 2 from by norm_cast,
      show φ ^ (1 : ℤ) = φ from zpow_one φ]
  rw [phi_cubed, golden_ratio_property, psi_sq]
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [psi_sq]
  rw [hψ3]
  intro h
  have h6 : 6 * (φ - ψ) = 0 := by linarith [phi_add_psi]
  have hne : φ - ψ ≠ 0 := by
    rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num : (5:ℝ) > 0)
  exact absurd h6 (mul_ne_zero (by norm_num : (6:ℝ) ≠ 0) hne)

theorem D6CoeffZ_three_ne_zero : D6CoeffZ 3 ≠ 0 := by
  rw [show (3 : ℤ) = (3 : ℕ) from rfl, D6CoeffZ_natCast]
  exact D6Coeff_three_ne_zero

private theorem phi_pow6 : φ ^ 6 = 8 * φ + 5 := by
  have : φ ^ 6 = (φ ^ 3) ^ 2 := by ring
  rw [this, phi_cubed]; nlinarith [golden_ratio_property]

private theorem phi_pow9 : φ ^ 9 = 34 * φ + 21 := by
  have : φ ^ 9 = φ ^ 3 * φ ^ 6 := by ring
  rw [this, phi_cubed, phi_pow6]; nlinarith [golden_ratio_property]

private theorem psi_cubed : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [psi_sq]

private theorem psi_pow6 : ψ ^ 6 = 8 * ψ + 5 := by
  have : ψ ^ 6 = (ψ ^ 3) ^ 2 := by ring
  rw [this, psi_cubed]; nlinarith [psi_sq]

private theorem psi_pow9 : ψ ^ 9 = 34 * ψ + 21 := by
  have : ψ ^ 9 = ψ ^ 3 * ψ ^ 6 := by ring
  rw [this, psi_cubed, psi_pow6]; nlinarith [psi_sq]

theorem D6CoeffZ_neg_three_ne_zero : D6CoeffZ (-3) ≠ 0 := by
  -- C(-3) = 60(φ-ψ) = 60√5 ≠ 0
  simp only [D6CoeffZ]
  rw [show (3 : ℤ) * (-3) = -9 from by ring, show (2 : ℤ) * (-3) = -6 from by ring]
  rw [phi_neg_zpow, phi_neg_zpow, phi_neg_zpow,
      psi_neg_zpow, psi_neg_zpow, psi_neg_zpow]
  rw [(Odd.neg_zpow (⟨4, by ring⟩ : Odd (9 : ℤ)) ψ),
      (Even.neg_zpow (⟨3, by ring⟩ : Even (6 : ℤ)) ψ),
      (Odd.neg_zpow (⟨1, by ring⟩ : Odd (3 : ℤ)) ψ),
      (Odd.neg_zpow (⟨4, by ring⟩ : Odd (9 : ℤ)) φ),
      (Even.neg_zpow (⟨3, by ring⟩ : Even (6 : ℤ)) φ),
      (Odd.neg_zpow (⟨1, by ring⟩ : Odd (3 : ℤ)) φ)]
  rw [show ψ ^ (9 : ℤ) = ψ ^ 9 from by norm_cast,
      show ψ ^ (6 : ℤ) = ψ ^ 6 from by norm_cast,
      show ψ ^ (3 : ℤ) = ψ ^ 3 from by norm_cast,
      show φ ^ (9 : ℤ) = φ ^ 9 from by norm_cast,
      show φ ^ (6 : ℤ) = φ ^ 6 from by norm_cast,
      show φ ^ (3 : ℤ) = φ ^ 3 from by norm_cast]
  rw [phi_pow9, phi_pow6, phi_cubed, psi_pow9, psi_pow6, psi_cubed]
  intro h
  have : 60 * (φ - ψ) = 0 := by linarith
  rw [phi_sub_psi] at this
  linarith [Real.sqrt_pos_of_pos (show (5:ℝ) > 0 from by norm_num)]

theorem D6_kernel_gap_structure :
    D6CoeffZ (-3) ≠ 0 ∧ D6CoeffZ (-2) = 0 ∧ D6CoeffZ (-1) ≠ 0 ∧
    D6CoeffZ 0 = 0 ∧ D6CoeffZ 1 = 0 ∧ D6CoeffZ 2 = 0 ∧ D6CoeffZ 3 ≠ 0 :=
  ⟨D6CoeffZ_neg_three_ne_zero, D6CoeffZ_neg_two, D6CoeffZ_neg_one_ne_zero,
   D6CoeffZ_zero, D6CoeffZ_one, D6CoeffZ_two, D6CoeffZ_three_ne_zero⟩

end ExtendedKernel

end FUST.SpectralCoefficients
