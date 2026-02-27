import FUST.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Finset.Basic

namespace FUST

open Complex

noncomputable def N2 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) * z) - f ((↑ψ : ℂ) * z)

noncomputable def N3 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) * z) - 2 * f z + f ((↑ψ : ℂ) * z)

noncomputable def N4 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^2 * z) - (↑φ : ℂ)^2 * f ((↑φ : ℂ) * z)
    + (↑ψ : ℂ)^2 * f ((↑ψ : ℂ) * z) - f ((↑ψ : ℂ)^2 * z)

noncomputable def N5 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) ^ 2 * z) + f ((↑φ : ℂ) * z) - 4 * f z +
  f ((↑ψ : ℂ) * z) + f ((↑ψ : ℂ) ^ 2 * z)

noncomputable def N6 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^3 * z) - 3 * f ((↑φ : ℂ)^2 * z) + f ((↑φ : ℂ) * z) -
  f ((↑ψ : ℂ) * z) + 3 * f ((↑ψ : ℂ)^2 * z) - f ((↑ψ : ℂ)^3 * z)

/-!
## Numerator Coefficient Uniqueness

N5 general numerator: f(φ²z) - a·f(φz) + b·f(z) - a·f(ψz) + f(ψ²z)
N6 general numerator: f(φ³z) - A·f(φ²z) + B·f(φz) - B·f(ψz) + A·f(ψ²z) - f(ψ³z)

The coefficients are uniquely determined by the kernel conditions.
-/

section CoefficientUniqueness

/-- N5 general numerator with parameters (a, b) -/
noncomputable def N5_general (a b : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^2 * z) - a * f ((↑φ : ℂ) * z)
    + b * f z - a * f ((↑ψ : ℂ) * z) + f ((↑ψ : ℂ)^2 * z)

/-- N6 general numerator with parameters (A, B) -/
noncomputable def N6_general (A B : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^3 * z) - A * f ((↑φ : ℂ)^2 * z) + B * f ((↑φ : ℂ) * z) -
   B * f ((↑ψ : ℂ) * z) + A * f ((↑ψ : ℂ)^2 * z) - f ((↑ψ : ℂ)^3 * z)

/-- Condition C0: N5[1] = 0 iff 2 - 2a + b = 0 -/
theorem N5_C0_condition (a b : ℂ) :
    (∀ z : ℂ, N5_general a b (fun _ => 1) z = 0) ↔ b = 2 * a - 2 := by
  constructor
  · intro h
    have h1 := h 1
    simp only [N5_general, mul_one] at h1
    linear_combination h1
  · intro hb z
    simp only [N5_general]
    rw [hb]; ring

/-- Condition C1: N5[id] = 0 iff (φ² + ψ²) - a(φ + ψ) + b = 0 -/
theorem N5_C1_condition (a b : ℂ) :
    (∀ z : ℂ, N5_general a b id z = 0) ↔ b = a - 3 := by
  have h1 : (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 = 3 := by
    linear_combination golden_ratio_property_complex + psi_sq_complex + phi_add_psi_complex
  have h2 := phi_add_psi_complex
  constructor
  · intro h
    have hz := h 1
    simp only [N5_general, id_eq, mul_one] at hz
    have hcoef : (↑φ : ℂ)^2 - a * ↑φ + b - a * ↑ψ + (↑ψ : ℂ)^2 =
        ((↑φ : ℂ)^2 + (↑ψ : ℂ)^2) - a * ((↑φ : ℂ) + ↑ψ) + b := by ring
    rw [hcoef, h1, h2] at hz
    linear_combination hz
  · intro hb z
    simp only [N5_general, id_eq]
    have hcoef : (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - a * ((↑φ : ℂ) + ↑ψ) + b = 0 := by
      rw [h1, h2, hb]; ring
    have hnum : (↑φ : ℂ)^2 * z - a * ((↑φ : ℂ) * z) + b * z - a * ((↑ψ : ℂ) * z) + (↑ψ : ℂ)^2 * z =
        ((↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - a * ((↑φ : ℂ) + ↑ψ) + b) * z := by ring
    rw [hnum, hcoef, zero_mul]

/-- N5 coefficient uniqueness: N5[1] = 0 and N5[id] = 0 determine a = -1, b = -4 -/
theorem N5_coefficients_unique :
    ∀ a b : ℂ,
    (∀ z : ℂ, N5_general a b (fun _ => 1) z = 0) →
    (∀ z : ℂ, N5_general a b id z = 0) →
    a = -1 ∧ b = -4 := by
  intro a b h0 h1
  have eq1 : b = 2 * a - 2 := N5_C0_condition a b |>.mp h0
  have eq2 : b = a - 3 := N5_C1_condition a b |>.mp h1
  have ha : a = -1 := by linear_combination eq2 - eq1
  have hb : b = -4 := by rw [eq2, ha]; ring
  exact ⟨ha, hb⟩

/-- N5_general with determined coefficients equals N5 -/
theorem N5_general_eq_N5 (f : ℂ → ℂ) (z : ℂ) :
    N5_general (-1) (-4) f z = N5 f z := by
  simp only [N5_general, N5]; ring

/-- Condition D1: N6[id] = 0 iff F₃ - A·F₂ + B·F₁ = 0, i.e., 2 - A + B = 0 -/
theorem N6_D1_condition (A B : ℂ) :
    (∀ z : ℂ, N6_general A B id z = 0) ↔ B = A - 2 := by
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  constructor
  · intro h
    have hz := h 1
    simp only [N6_general, id_eq, mul_one] at hz
    have hfact : (2 - A + B) * ((↑φ : ℂ) - ↑ψ) = 0 := by
      linear_combination hz + A * hφ2 - A * hψ2 - hφ3 + hψ3
    have := (mul_eq_zero.mp hfact).resolve_right phi_sub_psi_complex_ne
    linear_combination this
  · intro hB z
    simp only [N6_general, id_eq]
    have hnum : (↑φ : ℂ)^3 * z - A * ((↑φ : ℂ)^2 * z) + B * ((↑φ : ℂ) * z) - B * ((↑ψ : ℂ) * z) +
        A * ((↑ψ : ℂ)^2 * z) - (↑ψ : ℂ)^3 * z = (((↑φ : ℂ)^3 - (↑ψ : ℂ)^3) - A * ((↑φ : ℂ)^2
        - (↑ψ : ℂ)^2) + B * ((↑φ : ℂ) - ↑ψ)) * z := by ring
    have hcoef :
        ((↑φ : ℂ)^3 - (↑ψ : ℂ)^3) - A * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) + B * ((↑φ : ℂ) - ↑ψ) = 0 := by
      have : (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 = 2 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ3 - hψ3
      have : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by linear_combination hφ2 - hψ2
      rw [‹_ ^ 3 - _ ^ 3 = _›, ‹_ ^ 2 - _ ^ 2 = _›, hB]; ring
    rw [hnum, hcoef, zero_mul]

/-- Condition D2: N6[x²] = 0 iff F₆ - A·F₄ + B·F₂ = 0, i.e., 8 - 3A + B = 0 -/
theorem N6_D2_condition (A B : ℂ) :
    (∀ z : ℂ, N6_general A B (fun t => t^2) z = 0) ↔ B = 3 * A - 8 := by
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ6 := phi_pow6_complex
  have hψ6 := psi_pow6_complex
  constructor
  · intro h
    have hz := h 1
    simp only [N6_general, mul_one] at hz
    have hfact : (8 - 3 * A + B) * ((↑φ : ℂ) - ↑ψ) = 0 := by
      linear_combination hz + A * hφ4 - A * hψ4 - B * hφ2 + B * hψ2 - hφ6 + hψ6
    have := (mul_eq_zero.mp hfact).resolve_right phi_sub_psi_complex_ne
    linear_combination this
  · intro hB z
    simp only [N6_general]
    have hcoef : (↑φ : ℂ)^6 - (↑ψ : ℂ)^6 - A * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) +
        B * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) = 0 := by
      have h1 : (↑φ : ℂ)^6 - (↑ψ : ℂ)^6 = 8 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ6 - hψ6
      have h2 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ4 - hψ4
      have h3 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by linear_combination hφ2 - hψ2
      rw [h1, h2, h3, hB]; ring
    have hnum : ((↑φ : ℂ)^3 * z)^2 - A * ((↑φ : ℂ)^2 * z)^2 + B * ((↑φ : ℂ) * z)^2 -
        B * ((↑ψ : ℂ) * z)^2 + A * ((↑ψ : ℂ)^2 * z)^2 - ((↑ψ : ℂ)^3 * z)^2 =
        ((↑φ : ℂ)^6 - (↑ψ : ℂ)^6 - A * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) +
        B * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2)) * z^2 := by ring
    rw [hnum, hcoef, zero_mul]

/-- N6 coefficient uniqueness: N6[id] = 0 and N6[x²] = 0 determine A = 3, B = 1 -/
theorem N6_coefficients_unique :
    ∀ A B : ℂ,
    (∀ z : ℂ, N6_general A B id z = 0) →
    (∀ z : ℂ, N6_general A B (fun t => t^2) z = 0) →
    A = 3 ∧ B = 1 := by
  intro A B h1 h2
  have eq1 : B = A - 2 := N6_D1_condition A B |>.mp h1
  have eq2 : B = 3 * A - 8 := N6_D2_condition A B |>.mp h2
  have hA : A = 3 := by linear_combination (eq1 - eq2) / 2
  have hB : B = 1 := by rw [eq1, hA]; ring
  exact ⟨hA, hB⟩

/-- N6_general with determined coefficients equals N6 -/
theorem N6_general_eq_N6 (f : ℂ → ℂ) (z : ℂ) :
    N6_general 3 1 f z = N6 f z := by
  simp only [N6_general, N6]; ring

/-- Complete coefficient uniqueness for N5 and N6 -/
theorem FUST_coefficient_uniqueness :
    (∀ a b : ℂ,
      (∀ z, N5_general a b (fun _ => 1) z = 0) →
      (∀ z, N5_general a b id z = 0) →
      a = -1 ∧ b = -4) ∧
    (∀ A B : ℂ,
      (∀ z, N6_general A B id z = 0) →
      (∀ z, N6_general A B (fun t => t^2) z = 0) →
      A = 3 ∧ B = 1) :=
  ⟨N5_coefficients_unique, N6_coefficients_unique⟩

end CoefficientUniqueness

section AlgebraicConstants

/-- Half-order mixing parameter: λ = 2/(φ + 2) = 2/(φ² + 1) ≈ 0.5528 -/
noncomputable def halfOrderParam : ℂ := 2 / ((↑φ : ℂ) + 2)

/-- Alternative form: λ = 2/(φ² + 1) -/
theorem halfOrderParam_alt : halfOrderParam = 2 / ((↑φ : ℂ)^2 + 1) := by
  simp only [halfOrderParam]
  congr 1; linear_combination -golden_ratio_property_complex

/-- Uniqueness condition: halfOrderParam satisfies μ·(φ² + 1) = 2 -/
theorem halfOrderParam_uniqueness : halfOrderParam * ((↑φ : ℂ)^2 + 1) = 2 := by
  rw [halfOrderParam_alt]
  have h : (↑φ : ℂ)^2 + 1 ≠ 0 := by
    intro heq
    have : (↑φ : ℂ) + 2 = 0 := by linear_combination -golden_ratio_property_complex + heq
    have : (↑φ : ℂ) = -2 := by linear_combination this
    have : (φ : ℝ) = -2 := by exact_mod_cast this
    linarith [phi_pos]
  field_simp

/-- If μ·(φ² + 1) = 2, then μ = halfOrderParam -/
theorem halfOrderParam_unique_from_condition (μ : ℂ) (h : μ * ((↑φ : ℂ) ^ 2 + 1) = 2) :
    μ = halfOrderParam := by
  rw [halfOrderParam_alt]
  have hne : (↑φ : ℂ) ^ 2 + 1 ≠ 0 := by
    intro heq
    have : (↑φ : ℂ) + 2 = 0 := by linear_combination -golden_ratio_property_complex + heq
    have : (↑φ : ℂ) = -2 := by linear_combination this
    have : (φ : ℝ) = -2 := by exact_mod_cast this
    linarith [phi_pos]
  field_simp at h ⊢; linear_combination h

end AlgebraicConstants

/-!
## N7 Algebraic Reduction to N6

N7 antisymmetric numerator form: [1, -a, b, -c, +c, -b, +a, -1]
N7(a,b,c)[f](z) = f(φ⁴z) - a·f(φ³z) + b·f(φ²z) - c·f(φz)
                   + c·f(ψz) - b·f(ψ²z) + a·f(ψ³z) - f(ψ⁴z)

Key result: ker(N7) = ker(N6) implies N7 provides no new structure.
-/

section N7Reduction

/-- N7 general antisymmetric numerator with parameters (a, b, c) -/
noncomputable def N7_general (a b c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^4 * z) - a * f ((↑φ : ℂ)^3 * z) + b * f ((↑φ : ℂ)^2 * z)
    - c * f ((↑φ : ℂ) * z) + c * f ((↑ψ : ℂ) * z) - b * f ((↑ψ : ℂ)^2 * z)
    + a * f ((↑ψ : ℂ)^3 * z) - f ((↑ψ : ℂ)^4 * z)

/-- Condition E0: N7[1] = 0 holds for antisymmetric form (coefficient sum = 0) -/
theorem N7_E0_condition (a b c : ℂ) :
    ∀ z : ℂ, N7_general a b c (fun _ => 1) z = 0 := by
  intro z
  simp only [N7_general]; ring

/-- Condition E1: N7[id] = 0 iff 3 - 2a + b - c = 0
    (using Fibonacci: F₄ = 3, F₃ = 2, F₂ = 1, F₁ = 1) -/
theorem N7_E1_condition (a b c : ℂ) :
    (∀ z : ℂ, N7_general a b c id z = 0) ↔ 3 - 2 * a + b - c = 0 := by
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  constructor
  · intro h
    have hz := h 1
    simp only [N7_general, id_eq, mul_one] at hz
    have hcoef : (↑φ : ℂ)^4 - a * (↑φ : ℂ)^3 + b * (↑φ : ℂ)^2 - c * ↑φ + c * ↑ψ
      - b * (↑ψ : ℂ)^2 + a * (↑ψ : ℂ)^3 - (↑ψ : ℂ)^4
      = ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) - a * ((↑φ : ℂ)^3 - (↑ψ : ℂ)^3)
      + b * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) - c * ((↑φ : ℂ) - ↑ψ) := by ring
    rw [hcoef] at hz
    have hF4 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by
      linear_combination hφ4 - hψ4
    have hF3 : (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 = 2 * ((↑φ : ℂ) - ↑ψ) := by
      linear_combination hφ3 - hψ3
    have hF2 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by
      linear_combination hφ2 - hψ2
    rw [hF4, hF3, hF2] at hz
    have hfact : (3 - 2*a + b - c) * ((↑φ : ℂ) - ↑ψ) = 0 := by linear_combination hz
    have := (mul_eq_zero.mp hfact).resolve_right phi_sub_psi_complex_ne
    linear_combination this
  · intro hcond z
    simp only [N7_general, id_eq]
    have hF4 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ4 - hψ4
    have hF3 : (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 = 2 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ3 - hψ3
    have hF2 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by linear_combination hφ2 - hψ2
    have hcoef : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 - a * ((↑φ : ℂ)^3
        - (↑ψ : ℂ)^3) + b * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) - c * ((↑φ : ℂ) - ↑ψ) = 0 := by
      rw [hF4, hF3, hF2]; linear_combination hcond * ((↑φ : ℂ) - ↑ψ)
    have hnum : (↑φ : ℂ)^4 * z - a * ((↑φ : ℂ)^3 * z) + b * ((↑φ : ℂ)^2 * z) - c * ((↑φ : ℂ) * z)
        + c * ((↑ψ : ℂ) * z) - b * ((↑ψ : ℂ)^2 * z) + a * ((↑ψ : ℂ)^3 * z) - (↑ψ : ℂ)^4 * z
        = ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4 - a * ((↑φ : ℂ)^3 - (↑ψ : ℂ)^3)
        + b * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) - c * ((↑φ : ℂ) - ↑ψ)) * z := by ring
    rw [hnum, hcoef, zero_mul]

/-- Condition E2: N7[x²] = 0 iff F₈ - a·F₆ + b·F₄ - c·F₂ = 21 - 8a + 3b - c = 0 -/
theorem N7_E2_condition (a b c : ℂ) :
    (∀ z : ℂ, N7_general a b c (fun t => t^2) z = 0) ↔ 21 - 8 * a + 3 * b - c = 0 := by
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ6 := phi_pow6_complex
  have hψ6 := psi_pow6_complex
  have hφ8 := phi_pow8_complex
  have hψ8 := psi_pow8_complex
  constructor
  · intro h
    have hz := h 1
    simp only [N7_general, mul_one] at hz
    have hcoef : ((↑φ : ℂ)^4)^2 - a * ((↑φ : ℂ)^3)^2 + b * ((↑φ : ℂ)^2)^2 - c * (↑φ : ℂ)^2
        + c * (↑ψ : ℂ)^2 - b * ((↑ψ : ℂ)^2)^2 + a * ((↑ψ : ℂ)^3)^2 - ((↑ψ : ℂ)^4)^2
        = (↑φ : ℂ)^8 - (↑ψ : ℂ)^8 - a * ((↑φ : ℂ)^6 - (↑ψ : ℂ)^6)
        + b * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) - c * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) := by ring
    rw [hcoef] at hz
    have hF8 : (↑φ : ℂ)^8 - (↑ψ : ℂ)^8 = 21 * ((↑φ : ℂ) - ↑ψ) := by
      linear_combination hφ8 - hψ8
    have hF6 : (↑φ : ℂ)^6 - (↑ψ : ℂ)^6 = 8 * ((↑φ : ℂ) - ↑ψ) := by
      linear_combination hφ6 - hψ6
    have hF4 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by
      linear_combination hφ4 - hψ4
    have hF2 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by
      linear_combination hφ2 - hψ2
    rw [hF8, hF6, hF4, hF2] at hz
    have hfact : (21 - 8*a + 3*b - c) * ((↑φ : ℂ) - ↑ψ) = 0 := by linear_combination hz
    have := (mul_eq_zero.mp hfact).resolve_right phi_sub_psi_complex_ne
    linear_combination this
  · intro hcond z
    simp only [N7_general]
    have hF8 : (↑φ : ℂ)^8 - (↑ψ : ℂ)^8 = 21 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ8 - hψ8
    have hF6 : (↑φ : ℂ)^6 - (↑ψ : ℂ)^6 = 8 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ6 - hψ6
    have hF4 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ4 - hψ4
    have hF2 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by
        linear_combination hφ2 - hψ2
    have hcoef : (↑φ : ℂ)^8 - (↑ψ : ℂ)^8 - a * ((↑φ : ℂ)^6 - (↑ψ : ℂ)^6)
        + b * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) - c * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) = 0 := by
      rw [hF8, hF6, hF4, hF2]; linear_combination hcond * ((↑φ : ℂ) - ↑ψ)
    have hnum : ((↑φ : ℂ)^4 * z)^2 - a * ((↑φ : ℂ)^3 * z)^2
        + b * ((↑φ : ℂ)^2 * z)^2 - c * ((↑φ : ℂ) * z)^2 + c * ((↑ψ : ℂ) * z)^2
        - b * ((↑ψ : ℂ)^2 * z)^2 + a * ((↑ψ : ℂ)^3 * z)^2 - ((↑ψ : ℂ)^4 * z)^2
        = ((↑φ : ℂ)^8 - (↑ψ : ℂ)^8 - a * ((↑φ : ℂ)^6 - (↑ψ : ℂ)^6)
        + b * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) - c * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2)) * z^2 := by ring
    rw [hnum, hcoef, zero_mul]

/-- N7 coefficient constraint: E1 and E2 imply c = a - 6, b = 3a - 9 (1 free parameter) -/
theorem N7_coefficients_constrained (a b c : ℂ) :
    (∀ z : ℂ, N7_general a b c id z = 0) →
    (∀ z : ℂ, N7_general a b c (fun t => t^2) z = 0) →
    c = a - 6 ∧ b = 3 * a - 9 := by
  intro h1 h2
  have eq1 : 3 - 2 * a + b - c = 0 := N7_E1_condition a b c |>.mp h1
  have eq2 : 21 - 8 * a + 3 * b - c = 0 := N7_E2_condition a b c |>.mp h2
  constructor
  · linear_combination (eq2 - 3 * eq1) / 2
  · linear_combination (eq2 - eq1) / 2

/-- N7 with constrained coefficients: a arbitrary, b = 3a - 9, c = a - 6 -/
noncomputable def N7_constrained (a : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  N7_general a (3 * a - 9) (a - 6) f z

/-- N7_constrained annihilates constants -/
theorem N7_constrained_const (a : ℂ) (k : ℂ) (z : ℂ) :
    N7_constrained a (fun _ => k) z = 0 := by
  simp only [N7_constrained, N7_general]; ring

/-- N7_constrained annihilates linear functions -/
theorem N7_constrained_linear (a : ℂ) :
    ∀ z : ℂ, N7_constrained a id z = 0 := by
  intro z; simp only [N7_constrained]
  have h : 3 - 2 * a + (3 * a - 9) - (a - 6) = 0 := by ring
  exact N7_E1_condition a (3*a - 9) (a - 6) |>.mpr h z

/-- N7_constrained annihilates quadratic functions -/
theorem N7_constrained_quadratic (a : ℂ) :
    ∀ z : ℂ, N7_constrained a (fun t => t^2) z = 0 := by
  intro z; simp only [N7_constrained]
  have h : 21 - 8 * a + 3 * (3 * a - 9) - (a - 6) = 0 := by ring
  exact N7_E2_condition a (3*a - 9) (a - 6) |>.mpr h z

/-- ker(N7) = ker(N6): N7 annihilates {1, z, z²} (same as N6 kernel) -/
theorem N7_kernel_equals_N6_kernel (a : ℂ) :
    (∀ c z, N7_constrained a (fun _ => c) z = 0) ∧
    (∀ z, N7_constrained a id z = 0) ∧
    (∀ z, N7_constrained a (fun t => t^2) z = 0) :=
  ⟨fun c z => N7_constrained_const a c z,
   N7_constrained_linear a,
   N7_constrained_quadratic a⟩

end N7Reduction

end FUST
