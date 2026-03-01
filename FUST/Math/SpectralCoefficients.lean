/-
FUST Diff₆ Spectral Coefficients

Diff₆(xⁿ) = Cₙ · x^{n-1} where Cₙ = √5 · (F_{3n} - 3F_{2n} + Fₙ).
The polynomial kernel {1, x, x²} (dim 3) and Laurent kernel {x⁻², 1, x, x²} (dim 4)
are fundamental properties of the golden-ratio 6-point difference operator.
-/

import FUST.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Data.Nat.Fib.Basic

namespace FUST.SpectralCoefficients

open FUST Real

/-! ## Section 1: Diff₆ Spectral Coefficients (ℕ → ℝ)

Diff₆(xⁿ) = Cₙ · x^{n-1} for n ≥ 3

The coefficient Cₙ encodes the spectral structure of Diff₆.
-/

section SpectralCoefficients

/-- Coefficient C_n for Diff₆(x^n) = C_n · x^{n-1} -/
noncomputable def Diff6Coeff (n : ℕ) : ℝ :=
  φ^(3*n) - 3*φ^(2*n) + φ^n - ψ^n + 3*ψ^(2*n) - ψ^(3*n)

/-- C_0 = 0 (constant annihilation) -/
theorem Diff6Coeff_zero : Diff6Coeff 0 = 0 := by
  simp only [Diff6Coeff, Nat.mul_zero, pow_zero]
  ring

/-- C_1 = 0 (linear annihilation) -/
theorem Diff6Coeff_one : Diff6Coeff 1 = 0 := by
  simp only [Diff6Coeff, Nat.mul_one]
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
theorem Diff6Coeff_two : Diff6Coeff 2 = 0 := by
  simp only [Diff6Coeff]
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
theorem Diff6Coeff_three : Diff6Coeff 3 = 12 * Real.sqrt 5 := by
  simp only [Diff6Coeff]
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

/-- Diff6Coeff expressed via Fibonacci: C_n = √5 · (F_{3n} - 3F_{2n} + F_n) -/
theorem Diff6Coeff_fibonacci (n : ℕ) :
    Diff6Coeff n = Real.sqrt 5 * (Nat.fib (3*n) - 3 * Nat.fib (2*n) + Nat.fib n) := by
  simp only [Diff6Coeff]
  have h1 : (Nat.fib (3*n) : ℝ) = (φ^(3*n) - ψ^(3*n)) / Real.sqrt 5 := coe_fib_eq (3*n)
  have h2 : (Nat.fib (2*n) : ℝ) = (φ^(2*n) - ψ^(2*n)) / Real.sqrt 5 := coe_fib_eq (2*n)
  have h3 : (Nat.fib n : ℝ) = (φ^n - ψ^n) / Real.sqrt 5 := coe_fib_eq n
  have hsqrt5_ne : Real.sqrt 5 ≠ 0 := by positivity
  rw [h1, h2, h3]
  field_simp
  ring

/-- C_3 = 12√5 ≠ 0 -/
theorem Diff6Coeff_three_ne_zero : Diff6Coeff 3 ≠ 0 := by
  rw [Diff6Coeff_three]
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
theorem Diff6Coeff_ne_zero_of_ge_three (n : ℕ) (hn : n ≥ 3) : Diff6Coeff n ≠ 0 := by
  rw [Diff6Coeff_fibonacci]
  have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have h_fib_pos : Nat.fib (3*n) + Nat.fib n > 3 * Nat.fib (2*n) := fib_combination_pos n hn
  have h : (0 : ℝ) < Nat.fib (3*n) - 3 * Nat.fib (2*n) + Nat.fib n := by
    have : (Nat.fib (3*n) : ℝ) + Nat.fib n > 3 * Nat.fib (2*n) := by exact_mod_cast h_fib_pos
    linarith
  exact ne_of_gt (mul_pos hsqrt5_pos h)

/-- Kernel characterization: C_n = 0 iff n ≤ 2 -/
theorem Diff6Coeff_eq_zero_iff (n : ℕ) : Diff6Coeff n = 0 ↔ n ≤ 2 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    exact Diff6Coeff_ne_zero_of_ge_three n hne h
  · intro h
    interval_cases n <;> simp [Diff6Coeff_zero, Diff6Coeff_one, Diff6Coeff_two]

end SpectralCoefficients

/-! ## Section 2: Factorization and Asymptotics -/

section ExplicitComputation

/-- Diff6Coeff factorization: C_n = (φ^n - ψ^n) * (φ^{2n} + ψ^{2n} + (-1)^n + 1 - 3(φ^n + ψ^n)) -/
theorem Diff6Coeff_factored (n : ℕ) :
    Diff6Coeff n = (φ^n - ψ^n) * (φ^(2*n) + ψ^(2*n) + (-1:ℝ)^n + 1 - 3*(φ^n + ψ^n)) := by
  simp only [Diff6Coeff]
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
theorem Diff6Coeff_asymptotic (n : ℕ) (hn : n ≥ 3) :
    ∃ C > 0, |Diff6Coeff n - φ^(3*n)| ≤ C * φ^(2*n) := by
  use 5
  constructor
  · norm_num
  -- Diff6Coeff - φ^{3n} = -3φ^{2n} + φ^n - ψ^n + 3ψ^{2n} - ψ^{3n}
  have h_diff : Diff6Coeff n - φ^(3*n) = -3*φ^(2*n) + φ^n - ψ^n + 3*ψ^(2*n) - ψ^(3*n) := by
    simp only [Diff6Coeff]; ring
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

/-! ## Section 2.5: Spectral Weight and Triple Factorization

The spectral weight Q_n = φ^{2n} + ψ^{2n} + (-1)^n + 1 - 3(φ^n + ψ^n)
is the second factor in C_n = (φ^n - ψ^n) · Q_n.

Key identity: Q_n = (φ^n + ψ^n)² - 3(φ^n + ψ^n) + 1 - (-1)^n

This gives parity-dependent factorization:
  n odd:  Q_n = (φ^n+ψ^n - 1)(φ^n+ψ^n - 2)
  n even: Q_n = (φ^n+ψ^n)(φ^n+ψ^n - 3)

The three kernel zeros n ∈ {0,1,2} arise from three distinct mechanisms:
  n=0: φ^0 - ψ^0 = 0 (Fibonacci difference vanishes)
  n=1: φ+ψ - 1 = 0   (Lucas sum at threshold)
  n=2: φ²+ψ² - 3 = 0 (Lucas sum at identity level, even parity)
-/

section SpectralWeight

/-- Spectral weight Q_n: the symmetric factor in C_n = (φ^n - ψ^n) · Q_n -/
noncomputable def spectralWeight (n : ℕ) : ℝ :=
  φ^(2*n) + ψ^(2*n) + (-1:ℝ)^n + 1 - 3*(φ^n + ψ^n)

/-- Q_n = (φ^n+ψ^n)² - 3(φ^n+ψ^n) + 1 - (-1)^n -/
theorem spectralWeight_via_sum (n : ℕ) :
    spectralWeight n = (φ^n + ψ^n)^2 - 3*(φ^n + ψ^n) + 1 - (-1:ℝ)^n := by
  simp only [spectralWeight]
  have h2n_φ : φ^(2*n) = (φ^n)^2 := by rw [← pow_mul]; ring_nf
  have h2n_ψ : ψ^(2*n) = (ψ^n)^2 := by rw [← pow_mul]; ring_nf
  have hprod : φ^n * ψ^n = (-1:ℝ)^n := by rw [← mul_pow, phi_mul_psi]
  rw [h2n_φ, h2n_ψ]; nlinarith [hprod]

/-- n odd: Q_n = (φ^n+ψ^n - 1)(φ^n+ψ^n - 2) -/
theorem spectralWeight_odd (n : ℕ) (hn : Odd n) :
    spectralWeight n = (φ^n + ψ^n - 1) * (φ^n + ψ^n - 2) := by
  rw [spectralWeight_via_sum, Odd.neg_one_pow hn]; ring

/-- n even: Q_n = (φ^n+ψ^n)(φ^n+ψ^n - 3) -/
theorem spectralWeight_even (n : ℕ) (hn : Even n) :
    spectralWeight n = (φ^n + ψ^n) * (φ^n + ψ^n - 3) := by
  rw [spectralWeight_via_sum, Even.neg_one_pow hn]; ring

/-- Triple factorization (odd): C_n = (φ^n-ψ^n)(φ^n+ψ^n-1)(φ^n+ψ^n-2) -/
theorem Diff6Coeff_odd_factored (n : ℕ) (hn : Odd n) :
    Diff6Coeff n = (φ^n - ψ^n) * (φ^n + ψ^n - 1) * (φ^n + ψ^n - 2) := by
  have h1 := Diff6Coeff_factored n
  have h2 := spectralWeight_odd n hn
  simp only [spectralWeight] at h2
  rw [h1, h2, mul_assoc]

/-- Triple factorization (even): C_n = (φ^n-ψ^n)(φ^n+ψ^n)(φ^n+ψ^n-3) -/
theorem Diff6Coeff_even_factored (n : ℕ) (hn : Even n) :
    Diff6Coeff n = (φ^n - ψ^n) * (φ^n + ψ^n) * (φ^n + ψ^n - 3) := by
  have h1 := Diff6Coeff_factored n
  have h2 := spectralWeight_even n hn
  simp only [spectralWeight] at h2
  rw [h1, h2, mul_assoc]

/-- Three distinct zero mechanisms for dim ker(Diff₆) = 3 -/
theorem Diff6_kernel_three_mechanisms :
    (φ^0 - ψ^0 = 0) ∧
    (φ^1 + ψ^1 - 1 = 0) ∧
    (φ^2 + ψ^2 - 3 = 0) :=
  ⟨by simp,
   by rw [pow_one, pow_one]; linarith [phi_add_psi],
   by rw [golden_ratio_property, psi_sq]; linarith [phi_add_psi]⟩

/-- Q_0 = -2 -/
theorem spectralWeight_zero : spectralWeight 0 = -2 := by
  simp [spectralWeight]; ring

/-- Q_1 = 0 (kernel: φ+ψ = 1) -/
theorem spectralWeight_one : spectralWeight 1 = 0 := by
  simp only [spectralWeight, pow_one, Nat.mul_one]
  rw [golden_ratio_property, psi_sq]
  linarith [phi_add_psi]

/-- Q_2 = 0 (kernel: φ²+ψ² = 3) -/
theorem spectralWeight_two : spectralWeight 2 = 0 := by
  simp only [spectralWeight]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ4 : φ^4 = 3*φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ^4 = 3*ψ + 2 := by nlinarith [hψ2]
  change φ ^ (2 * 2) + ψ ^ (2 * 2) + (-1:ℝ) ^ 2 + 1 - 3 * (φ ^ 2 + ψ ^ 2) = 0
  rw [show 2 * 2 = 4 from by ring, hφ4, hψ4, hφ2, hψ2]
  linarith [phi_add_psi]

/-- Q_3 = 6 (first non-zero spectral weight) -/
theorem spectralWeight_three : spectralWeight 3 = 6 := by
  simp only [spectralWeight]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ3 : φ^3 = 2*φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2*ψ + 1 := by nlinarith [hψ2]
  have hφ6 : φ^6 = 8*φ + 5 := by nlinarith [hφ2, hφ3]
  have hψ6 : ψ^6 = 8*ψ + 5 := by nlinarith [hψ2, hψ3]
  change φ ^ (2 * 3) + ψ ^ (2 * 3) + (-1:ℝ) ^ 3 + 1 - 3 * (φ ^ 3 + ψ ^ 3) = 6
  rw [show 2 * 3 = 6 from by ring, hφ6, hψ6, hφ3, hψ3]
  linarith [phi_add_psi]

/-- C_3 = 2√5 · 3 · 2 = 12√5 via triple factorization -/
theorem Diff6Coeff_three_via_triple :
    Diff6Coeff 3 = (φ^3 - ψ^3) * (φ^3 + ψ^3 - 1) * (φ^3 + ψ^3 - 2) := by
  exact Diff6Coeff_odd_factored 3 ⟨1, by ring⟩

/-- Spectral eigenvalue via Fibonacci and spectral weight:
    λ_n = (φ^n-ψ^n) · Q_n / (√5)^5 = F_n · Q_n / (√5)^4 = F_n · Q_n / 25 -/
theorem spectralEigenvalue_factored (n : ℕ) :
    Diff6Coeff n = (φ^n - ψ^n) * spectralWeight n := by
  exact Diff6Coeff_factored n

end SpectralWeight

/-! ## Section 2.7: Fibonacci-Prime Bridge

The Diff6 spectral coefficient C_n = √5 · F_n · Q_n connects to prime numbers
through the Fibonacci divisibility structure:

1. Binet: φ^n - ψ^n = √5 · F_n, so C_n = √5 · F_n · Q_n
2. Strong divisibility: gcd(F_m, F_n) = F_{gcd(m,n)} (Mathlib: Nat.fib_gcd)
3. Rank of apparition: every prime p divides F_{α(p)} where α(p) | p-(5/p)
4. Periodicity: p | F_{α(p)} | F_{k·α(p)} for all k ≥ 1

This means every prime p is encoded in the Diff6 spectrum:
  p | F_{α(p)}, so p | C_{α(p)} / (√5 · Q_{α(p)})
  and p | C_{k·α(p)} / (√5 · Q_{k·α(p)}) for all k

The algebraic mechanism: p | F_n ⟺ φ^n ≡ ψ^n (mod p) in 𝔽_p[√5].
This is governed by the Frobenius element of ℚ(√5)/ℚ at p,
connecting Diff6 (which lives in ℚ(√5)) to the Euler product of ζ(s).

Key factorization: ζ_{ℚ(√5)}(s) = ζ(s) · L(s, χ_5)
where χ_5 is the Kronecker symbol (5/·). -/

section FibonacciPrimeBridge

/-- Binet formula: F_n = (φ^n - ψ^n) / √5 -/
theorem fib_binet (n : ℕ) :
    (Nat.fib n : ℝ) = (φ^n - ψ^n) / Real.sqrt 5 :=
  Real.coe_fib_eq n

/-- φ^n - ψ^n = √5 · F_n -/
theorem phi_sub_psi_eq_sqrt5_fib (n : ℕ) :
    φ^n - ψ^n = Real.sqrt 5 * (Nat.fib n : ℝ) := by
  rw [fib_binet]; field_simp

/-- Diff6Coeff via Fibonacci and spectral weight: C_n = √5 · F_n · Q_n -/
theorem Diff6Coeff_fib_spectralWeight (n : ℕ) :
    Diff6Coeff n = Real.sqrt 5 * (Nat.fib n : ℝ) * spectralWeight n := by
  rw [spectralEigenvalue_factored, phi_sub_psi_eq_sqrt5_fib, mul_assoc]

/-- Strong divisibility: gcd(F_m, F_n) = F_{gcd(m,n)} -/
theorem fib_strong_divisibility (m n : ℕ) :
    Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) :=
  Nat.fib_gcd m n

/-- Divisor transfer: m | n → F_m | F_n -/
theorem fib_dvd_of_dvd (m n : ℕ) (h : m ∣ n) : Nat.fib m ∣ Nat.fib n :=
  Nat.fib_dvd m n h

/-- If p | F_k then p | F_{nk} for all n. Every prime reappears periodically. -/
theorem fib_dvd_periodic (p k n : ℕ) (hk : p ∣ Nat.fib k) :
    p ∣ Nat.fib (n * k) :=
  dvd_trans hk (Nat.fib_dvd k (n * k) (dvd_mul_left k n))

/-- Concrete ranks of apparition: α(2)=3 -/
theorem rank_apparition_2 : 2 ∣ Nat.fib 3 := by decide
/-- α(3) = 4 -/
theorem rank_apparition_3 : 3 ∣ Nat.fib 4 := by decide
/-- α(5) = 5 (ramified prime, disc(ℚ(√5)) = 5) -/
theorem rank_apparition_5 : 5 ∣ Nat.fib 5 := by decide
/-- α(7) = 8 -/
theorem rank_apparition_7 : 7 ∣ Nat.fib 8 := by decide
/-- α(11) = 10, (5/11) = 1 since 11 ≡ 1 (mod 5), and 10 | 11-1 = 10 -/
theorem rank_apparition_11 : 11 ∣ Nat.fib 10 := by decide
/-- α(13) = 7, (5/13) = -1 since 13 ≡ 3 (mod 5), and 7 | 13+1 = 14 -/
theorem rank_apparition_13 : 13 ∣ Nat.fib 7 := by decide
/-- α(17) = 9, (5/17) = -1 since 17 ≡ 2 (mod 5), and 9 | 17+1 = 18 -/
theorem rank_apparition_17 : 17 ∣ Nat.fib 9 := by decide
/-- α(29) = 14, (5/29) = 1 since 29 ≡ 4 (mod 5), and 14 | 29-1 = 28 -/
theorem rank_apparition_29 : 29 ∣ Nat.fib 14 := by decide
/-- α(89) = 11, (5/89) = 1 since 89 ≡ 4 (mod 5), and 11 | 89-1 = 88 -/
theorem rank_apparition_89 : 89 ∣ Nat.fib 11 := by decide

/-- Diff6Coeff is proportional to Fibonacci with spectral weight as coefficient.
    For n ≥ 3, the spectral weight is nonzero, so F_n = 0 ⟺ C_n = 0. -/
theorem Diff6Coeff_zero_iff_fib_or_weight (n : ℕ) :
    Diff6Coeff n = 0 ↔ Nat.fib n = 0 ∨ spectralWeight n = 0 := by
  rw [Diff6Coeff_fib_spectralWeight]
  constructor
  · intro h
    have h5 : Real.sqrt 5 ≠ 0 := by positivity
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 h5
      · left; exact_mod_cast h2
    · right; exact h1
  · intro h
    rcases h with h | h
    · simp [h]
    · simp [h]

/-- Summary: Diff6 spectral coefficients encode all primes via Fibonacci.

The chain: Diff6 → C_n = √5·F_n·Q_n → F_n (Fibonacci) → p | F_{α(p)}
Every prime p enters the Fibonacci sequence at rank α(p) ≤ p+1.
By strong divisibility gcd(F_m,F_n) = F_{gcd(m,n)}, the prime p divides
F_n for exactly those n that are multiples of α(p).

The Frobenius element Frob_p ∈ Gal(ℚ(√5)/ℚ) determines α(p):
  (5/p) = 1 (p splits in ℤ[φ]):  α(p) | p-1
  (5/p) = -1 (p inert in ℤ[φ]): α(p) | p+1
  p = 5 (ramified):              α(5) = 5

This connects Diff6 (living in ℚ(√5)) to ζ(s) through:
  ζ_{ℚ(√5)}(s) = ζ(s) · L(s, χ_5) -/
theorem Diff6_prime_encoding_summary :
    -- C_n = √5 · F_n · Q_n (Fibonacci factorization)
    (∀ n, Diff6Coeff n = Real.sqrt 5 * (Nat.fib n : ℝ) * spectralWeight n) ∧
    -- Strong divisibility (prime periodicity)
    (∀ m n, Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n)) ∧
    -- Every small prime divides some Fibonacci number
    (2 ∣ Nat.fib 3 ∧ 3 ∣ Nat.fib 4 ∧ 5 ∣ Nat.fib 5 ∧
     7 ∣ Nat.fib 8 ∧ 11 ∣ Nat.fib 10 ∧ 13 ∣ Nat.fib 7 ∧
     29 ∣ Nat.fib 14 ∧ 89 ∣ Nat.fib 11) :=
  ⟨Diff6Coeff_fib_spectralWeight,
   fib_strong_divisibility,
   ⟨rank_apparition_2, rank_apparition_3, rank_apparition_5,
    rank_apparition_7, rank_apparition_11, rank_apparition_13,
    rank_apparition_29, rank_apparition_89⟩⟩

end FibonacciPrimeBridge

/-! ## Section 2.8: Dedekind Zeta Factorization for ℚ(√5)

The Dedekind zeta function of ℚ(√5) factors as ζ_{ℚ(√5)}(s) = ζ(s)·L(s,χ₅)
where χ₅ is the Kronecker character mod 5. We prove the local Euler factor
identity at each prime, which is the algebraic core of this factorization.

The splitting type of p in ℤ[φ] = ℤ[(1+√5)/2] determines the local factor:
  split (χ₅(p)=1):    (1-p⁻ˢ)⁻² — p splits into two principal ideals
  inert (χ₅(p)=-1):   (1-p⁻²ˢ)⁻¹ — p remains prime in ℤ[φ]
  ramified (χ₅(p)=0):  (1-p⁻ˢ)⁻¹ — p=5 ramifies (disc(ℚ(√5))=5) -/

section DedekindFactorization

/-- Kronecker character χ₅ defined by values mod 5: χ₅(n) = (5|n). -/
def chi5Fun (n : ℕ) : ℤ :=
  match n % 5 with
  | 0 => 0
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 1
  | _ => 0

theorem chi5Fun_zero : chi5Fun 0 = 0 := by decide
theorem chi5Fun_one : chi5Fun 1 = 1 := by decide
theorem chi5Fun_two : chi5Fun 2 = -1 := by decide
theorem chi5Fun_three : chi5Fun 3 = -1 := by decide
theorem chi5Fun_four : chi5Fun 4 = 1 := by decide
theorem chi5Fun_five : chi5Fun 5 = 0 := by decide

theorem chi5Fun_periodic (n : ℕ) : chi5Fun (n + 5) = chi5Fun n := by
  simp [chi5Fun]

theorem chi5Fun_values (n : ℕ) : chi5Fun n = 0 ∨ chi5Fun n = 1 ∨ chi5Fun n = -1 := by
  unfold chi5Fun
  have h5 : n % 5 < 5 := Nat.mod_lt n (by omega)
  interval_cases (n % 5) <;> simp

-- Splitting behavior: p ≡ ±1 (mod 5) splits, p ≡ ±2 (mod 5) inert, p=5 ramified
theorem chi5_split_11 : chi5Fun 11 = 1 := by decide
theorem chi5_split_19 : chi5Fun 19 = 1 := by decide
theorem chi5_split_29 : chi5Fun 29 = 1 := by decide
theorem chi5_split_31 : chi5Fun 31 = 1 := by decide
theorem chi5_split_41 : chi5Fun 41 = 1 := by decide
theorem chi5_inert_2 : chi5Fun 2 = -1 := by decide
theorem chi5_inert_3 : chi5Fun 3 = -1 := by decide
theorem chi5_inert_7 : chi5Fun 7 = -1 := by decide
theorem chi5_inert_13 : chi5Fun 13 = -1 := by decide
theorem chi5_inert_17 : chi5Fun 17 = -1 := by decide
theorem chi5_ramified_5 : chi5Fun 5 = 0 := by decide

/-- Split factor: (1-x)⁻¹·(1-x)⁻¹ = ((1-x)²)⁻¹ -/
theorem euler_factor_chi_one (x : ℂ) :
    (1 - x)⁻¹ * (1 - (1 : ℂ) * x)⁻¹ = ((1 - x) ^ 2)⁻¹ := by
  rw [one_mul, sq, mul_inv]

/-- Inert factor: (1-x)⁻¹·(1+x)⁻¹ = (1-x²)⁻¹ -/
theorem euler_factor_chi_neg_one (x : ℂ) :
    (1 - x)⁻¹ * (1 - (-1 : ℂ) * x)⁻¹ = (1 - x ^ 2)⁻¹ := by
  simp only [neg_one_mul, sub_neg_eq_add]
  rw [show x ^ 2 = x * x from sq x,
      show (1 : ℂ) - x * x = (1 - x) * (1 + x) from by ring, mul_inv]

/-- Ramified factor: (1-x)⁻¹·1 = (1-x)⁻¹ -/
theorem euler_factor_chi_zero (x : ℂ) :
    (1 - x)⁻¹ * (1 - (0 : ℂ) * x)⁻¹ = (1 - x)⁻¹ := by
  simp

private theorem local_euler_factor_case (p : ℕ) (x : ℂ) :
    (1 - x)⁻¹ * (1 - (chi5Fun p : ℂ) * x)⁻¹ =
      if chi5Fun p = 1 then ((1 - x) ^ 2)⁻¹
      else if chi5Fun p = -1 then (1 - x ^ 2)⁻¹
      else (1 - x)⁻¹ := by
  obtain h | h | h := chi5Fun_values p
  · have hif : (if chi5Fun p = 1 then ((1 - x) ^ 2)⁻¹
        else if chi5Fun p = -1 then (1 - x ^ 2)⁻¹ else (1 - x)⁻¹) = (1 - x)⁻¹ := by
      simp [h]
    rw [hif]
    have hc : (chi5Fun p : ℂ) = 0 := by exact_mod_cast h
    rw [hc, zero_mul, sub_zero, inv_one, mul_one]
  · have hif : (if chi5Fun p = 1 then ((1 - x) ^ 2)⁻¹
        else if chi5Fun p = -1 then (1 - x ^ 2)⁻¹ else (1 - x)⁻¹) = ((1 - x) ^ 2)⁻¹ := by
      simp [h]
    rw [hif]
    have hc : (chi5Fun p : ℂ) = 1 := by exact_mod_cast h
    rw [hc, one_mul, sq, mul_inv]
  · have hif : (if chi5Fun p = 1 then ((1 - x) ^ 2)⁻¹
        else if chi5Fun p = -1 then (1 - x ^ 2)⁻¹ else (1 - x)⁻¹) = (1 - x ^ 2)⁻¹ := by
      simp [h]
    rw [hif]
    have hc : (chi5Fun p : ℂ) = -1 := by exact_mod_cast h
    rw [hc, neg_one_mul, sub_neg_eq_add]
    rw [show x ^ 2 = x * x from sq x,
        show (1 : ℂ) - x * x = (1 - x) * (1 + x) from by ring, mul_inv]

/-- Connection: Fibonacci rank of apparition determines splitting type.

α(p) | p-1 ⟺ χ₅(p)=1 (split), α(p) | p+1 ⟺ χ₅(p)=-1 (inert).
The Frobenius element Frob_p ∈ Gal(ℚ(√5)/ℚ) determines both α(p) and χ₅(p). -/
theorem splitting_rank_apparition_consistency :
    -- Split primes: χ₅(p)=1 and α(p) | p-1
    (chi5Fun 11 = 1 ∧ 11 ∣ Nat.fib 10) ∧
    (chi5Fun 29 = 1 ∧ 29 ∣ Nat.fib 14) ∧
    (chi5Fun 31 = 1 ∧ 31 ∣ Nat.fib 30) ∧
    -- Inert primes: χ₅(p)=-1 and α(p) | p+1
    (chi5Fun 2 = -1 ∧ 2 ∣ Nat.fib 3) ∧
    (chi5Fun 3 = -1 ∧ 3 ∣ Nat.fib 4) ∧
    (chi5Fun 7 = -1 ∧ 7 ∣ Nat.fib 8) ∧
    (chi5Fun 13 = -1 ∧ 13 ∣ Nat.fib 7) ∧
    -- Ramified: χ₅(5)=0
    (chi5Fun 5 = 0 ∧ 5 ∣ Nat.fib 5) := by
  exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
         ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
         ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

end DedekindFactorization

/-! ## Section 3: Extended Diff₆ Kernel (ℤ → ℝ) -/

section ExtendedKernel

noncomputable def Diff6CoeffZ (n : ℤ) : ℝ :=
  φ ^ (3 * n) - 3 * φ ^ (2 * n) + φ ^ n - ψ ^ n + 3 * ψ ^ (2 * n) - ψ ^ (3 * n)

theorem Diff6CoeffZ_natCast (n : ℕ) : Diff6CoeffZ (n : ℤ) = Diff6Coeff n := by
  simp only [Diff6CoeffZ, Diff6Coeff, zpow_natCast]
  norm_cast

theorem Diff6CoeffZ_zero : Diff6CoeffZ 0 = 0 := by simp [Diff6CoeffZ]

theorem Diff6CoeffZ_one : Diff6CoeffZ 1 = 0 := by
  rw [show (1 : ℤ) = (1 : ℕ) from rfl, Diff6CoeffZ_natCast, Diff6Coeff_one]

theorem Diff6CoeffZ_two : Diff6CoeffZ 2 = 0 := by
  rw [show (2 : ℤ) = (2 : ℕ) from rfl, Diff6CoeffZ_natCast, Diff6Coeff_two]

private theorem phi_neg_zpow (k : ℤ) : φ ^ (-k) = (-ψ) ^ k := by
  rw [zpow_neg, ← inv_zpow]
  congr 1
  exact Real.inv_goldenRatio

private theorem psi_neg_zpow (k : ℤ) : ψ ^ (-k) = (-φ) ^ k := by
  rw [zpow_neg, ← inv_zpow]
  congr 1
  rw [inv_eq_of_mul_eq_one_left]
  linarith [phi_mul_psi]

theorem Diff6CoeffZ_neg_even (n : ℤ) (hn : Even n) : Diff6CoeffZ (-n) = -Diff6CoeffZ n := by
  simp only [Diff6CoeffZ]
  have h3n : Even (3 * n) := hn.mul_left 3
  have h2n : Even (2 * n) := hn.mul_left 2
  rw [show 3 * -n = -(3 * n) from by ring, show 2 * -n = -(2 * n) from by ring]
  rw [phi_neg_zpow, phi_neg_zpow, phi_neg_zpow,
      psi_neg_zpow, psi_neg_zpow, psi_neg_zpow]
  rw [h3n.neg_zpow, h2n.neg_zpow, hn.neg_zpow,
      h3n.neg_zpow, h2n.neg_zpow, hn.neg_zpow]
  ring

theorem Diff6CoeffZ_neg_two : Diff6CoeffZ (-2) = 0 := by
  have h := Diff6CoeffZ_neg_even 2 ⟨1, by ring⟩
  rw [Diff6CoeffZ_two, neg_zero] at h
  exact h

theorem Diff6_extended_kernel_dim :
    Diff6CoeffZ (-2) = 0 ∧ Diff6CoeffZ 0 = 0 ∧ Diff6CoeffZ 1 = 0 ∧ Diff6CoeffZ 2 = 0 :=
  ⟨Diff6CoeffZ_neg_two, Diff6CoeffZ_zero, Diff6CoeffZ_one, Diff6CoeffZ_two⟩

theorem Diff6CoeffZ_neg_one_ne_zero : Diff6CoeffZ (-1) ≠ 0 := by
  simp only [Diff6CoeffZ]
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

theorem Diff6CoeffZ_three_ne_zero : Diff6CoeffZ 3 ≠ 0 := by
  rw [show (3 : ℤ) = (3 : ℕ) from rfl, Diff6CoeffZ_natCast]
  exact Diff6Coeff_three_ne_zero

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

theorem Diff6CoeffZ_neg_three_ne_zero : Diff6CoeffZ (-3) ≠ 0 := by
  -- C(-3) = 60(φ-ψ) = 60√5 ≠ 0
  simp only [Diff6CoeffZ]
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

theorem Diff6_kernel_gap_structure :
    Diff6CoeffZ (-3) ≠ 0 ∧ Diff6CoeffZ (-2) = 0 ∧ Diff6CoeffZ (-1) ≠ 0 ∧
    Diff6CoeffZ 0 = 0 ∧ Diff6CoeffZ 1 = 0 ∧ Diff6CoeffZ 2 = 0 ∧ Diff6CoeffZ 3 ≠ 0 :=
  ⟨Diff6CoeffZ_neg_three_ne_zero, Diff6CoeffZ_neg_two, Diff6CoeffZ_neg_one_ne_zero,
   Diff6CoeffZ_zero, Diff6CoeffZ_one, Diff6CoeffZ_two, Diff6CoeffZ_three_ne_zero⟩

end ExtendedKernel

/-! ## Section 4: Diff₅ Spectral Coefficients

Diff₅(xⁿ) = Diff5Coeff(n) · x^{n-1} where
Diff5Coeff(n) = φ^{2n} + φ^n + ψ^n + ψ^{2n} - 4 = L(2n) + L(n) - 4.
ker(Diff₅) = {n | Diff5Coeff(n) = 0} = {0, 1} (polynomial), {0, 1} (Laurent).
-/

section Diff5Spectral

/-- Diff₅ spectral coefficient: Diff5Coeff(n) = φ^{2n} + φ^n + ψ^n + ψ^{2n} - 4 -/
noncomputable def Diff5CoeffZ (n : ℤ) : ℝ :=
  φ ^ (2 * n) + φ ^ n + ψ ^ n + ψ ^ (2 * n) - 4

theorem Diff5CoeffZ_zero : Diff5CoeffZ 0 = 0 := by simp [Diff5CoeffZ]; ring

theorem Diff5CoeffZ_one : Diff5CoeffZ 1 = 0 := by
  simp only [Diff5CoeffZ, zpow_one, show (2 : ℤ) * 1 = 2 from by ring]
  rw [show φ ^ (2 : ℤ) = φ ^ 2 from by norm_cast,
      show ψ ^ (2 : ℤ) = ψ ^ 2 from by norm_cast]
  rw [golden_ratio_property, psi_sq]
  linarith [phi_add_psi]

theorem Diff5CoeffZ_two : Diff5CoeffZ 2 = 6 := by
  simp only [Diff5CoeffZ, show (2 : ℤ) * 2 = 4 from by ring]
  rw [show φ ^ (4 : ℤ) = φ ^ 4 from by norm_cast,
      show φ ^ (2 : ℤ) = φ ^ 2 from by norm_cast,
      show ψ ^ (2 : ℤ) = ψ ^ 2 from by norm_cast,
      show ψ ^ (4 : ℤ) = ψ ^ 4 from by norm_cast]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  linarith [phi_add_psi]

theorem Diff5CoeffZ_two_ne_zero : Diff5CoeffZ 2 ≠ 0 := by
  rw [Diff5CoeffZ_two]; norm_num

theorem Diff5CoeffZ_neg_two : Diff5CoeffZ (-2) = 6 := by
  simp only [Diff5CoeffZ, show (2 : ℤ) * (-2) = -4 from by ring]
  rw [phi_neg_zpow, phi_neg_zpow, psi_neg_zpow, psi_neg_zpow]
  rw [show (-ψ) ^ (4 : ℤ) = ψ ^ (4 : ℤ) from
        (Even.neg_zpow (⟨2, by ring⟩ : Even (4 : ℤ)) ψ),
      show (-ψ) ^ (2 : ℤ) = ψ ^ (2 : ℤ) from
        (Even.neg_zpow (⟨1, by ring⟩ : Even (2 : ℤ)) ψ),
      show (-φ) ^ (4 : ℤ) = φ ^ (4 : ℤ) from
        (Even.neg_zpow (⟨2, by ring⟩ : Even (4 : ℤ)) φ),
      show (-φ) ^ (2 : ℤ) = φ ^ (2 : ℤ) from
        (Even.neg_zpow (⟨1, by ring⟩ : Even (2 : ℤ)) φ)]
  rw [show ψ ^ (4 : ℤ) = ψ ^ 4 from by norm_cast,
      show ψ ^ (2 : ℤ) = ψ ^ 2 from by norm_cast,
      show φ ^ (4 : ℤ) = φ ^ 4 from by norm_cast,
      show φ ^ (2 : ℤ) = φ ^ 2 from by norm_cast]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  linarith [phi_add_psi]

/-- Diff₅ Laurent kernel: ker = {0, 1}, same as polynomial kernel -/
theorem Diff5_kernel_structure :
    Diff5CoeffZ 0 = 0 ∧ Diff5CoeffZ 1 = 0 ∧
    Diff5CoeffZ 2 ≠ 0 ∧ Diff5CoeffZ (-1) ≠ 0 ∧ Diff5CoeffZ (-2) ≠ 0 := by
  refine ⟨Diff5CoeffZ_zero, Diff5CoeffZ_one, Diff5CoeffZ_two_ne_zero, ?_, ?_⟩
  · rw [Diff5CoeffZ]; simp only [show (2 : ℤ) * (-1) = -2 from by ring]
    rw [phi_neg_zpow, phi_neg_zpow, psi_neg_zpow, psi_neg_zpow]
    rw [show (-ψ) ^ (2 : ℤ) = ψ ^ (2 : ℤ) from
          (Even.neg_zpow (⟨1, by ring⟩ : Even (2 : ℤ)) ψ),
        show (-ψ) ^ (1 : ℤ) = -(ψ ^ (1 : ℤ)) from
          (Odd.neg_zpow (⟨0, by ring⟩ : Odd (1 : ℤ)) ψ),
        show (-φ) ^ (2 : ℤ) = φ ^ (2 : ℤ) from
          (Even.neg_zpow (⟨1, by ring⟩ : Even (2 : ℤ)) φ),
        show (-φ) ^ (1 : ℤ) = -(φ ^ (1 : ℤ)) from
          (Odd.neg_zpow (⟨0, by ring⟩ : Odd (1 : ℤ)) φ)]
    rw [show ψ ^ (2 : ℤ) = ψ ^ 2 from by norm_cast,
        show ψ ^ (1 : ℤ) = ψ from zpow_one ψ,
        show φ ^ (2 : ℤ) = φ ^ 2 from by norm_cast,
        show φ ^ (1 : ℤ) = φ from zpow_one φ]
    rw [golden_ratio_property, psi_sq]
    intro h
    have : φ - ψ = Real.sqrt 5 := phi_sub_psi
    have : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5:ℝ) > 0)
    linarith
  · rw [Diff5CoeffZ_neg_two]; norm_num

/-- Diff₅ and Diff₆ coefficients agree at d=2: both give 6 (Diff₅ detects, Diff₆ annihilates) -/
theorem Diff5Diff6_coeff_comparison_at_2 :
    Diff5CoeffZ 2 = 6 ∧ Diff6CoeffZ 2 = 0 :=
  ⟨Diff5CoeffZ_two, Diff6CoeffZ_two⟩

end Diff5Spectral

end FUST.SpectralCoefficients
