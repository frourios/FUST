import FUST.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Complex

attribute [local ext] Complex.ext

namespace FUST.DζOperator

noncomputable def Diff2 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) * z) - f ((↑ψ : ℂ) * z)

noncomputable def Diff3 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) * z) - 2 * f z + f ((↑ψ : ℂ) * z)

noncomputable def Diff4 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^2 * z) - (↑φ : ℂ)^2 * f ((↑φ : ℂ) * z)
    + (↑ψ : ℂ)^2 * f ((↑ψ : ℂ) * z) - f ((↑ψ : ℂ)^2 * z)

noncomputable def Diff5 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) ^ 2 * z) + f ((↑φ : ℂ) * z) - 4 * f z +
  f ((↑ψ : ℂ) * z) + f ((↑ψ : ℂ) ^ 2 * z)

noncomputable def Diff6 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^3 * z) - 3 * f ((↑φ : ℂ)^2 * z) + f ((↑φ : ℂ) * z) -
  f ((↑ψ : ℂ) * z) + 3 * f ((↑ψ : ℂ)^2 * z) - f ((↑ψ : ℂ)^3 * z)

/-!
## Numerator Coefficient Uniqueness

Diff5 general numerator: f(φ²z) - a·f(φz) + b·f(z) - a·f(ψz) + f(ψ²z)
Diff6 general numerator: f(φ³z) - A·f(φ²z) + B·f(φz) - B·f(ψz) + A·f(ψ²z) - f(ψ³z)

The coefficients are uniquely determined by the kernel conditions.
-/

section CoefficientUniqueness

/-- Diff5 general numerator with parameters (a, b) -/
noncomputable def Diff5_general (a b : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^2 * z) - a * f ((↑φ : ℂ) * z)
    + b * f z - a * f ((↑ψ : ℂ) * z) + f ((↑ψ : ℂ)^2 * z)

/-- Diff6 general numerator with parameters (A, B) -/
noncomputable def Diff6_general (A B : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^3 * z) - A * f ((↑φ : ℂ)^2 * z) + B * f ((↑φ : ℂ) * z) -
   B * f ((↑ψ : ℂ) * z) + A * f ((↑ψ : ℂ)^2 * z) - f ((↑ψ : ℂ)^3 * z)

/-- Condition C0: Diff5[1] = 0 iff 2 - 2a + b = 0 -/
theorem Diff5_C0_condition (a b : ℂ) :
    (∀ z : ℂ, Diff5_general a b (fun _ => 1) z = 0) ↔ b = 2 * a - 2 := by
  constructor
  · intro h
    have h1 := h 1
    simp only [Diff5_general, mul_one] at h1
    linear_combination h1
  · intro hb z
    simp only [Diff5_general]
    rw [hb]; ring

/-- Condition C1: Diff5[id] = 0 iff (φ² + ψ²) - a(φ + ψ) + b = 0 -/
theorem Diff5_C1_condition (a b : ℂ) :
    (∀ z : ℂ, Diff5_general a b id z = 0) ↔ b = a - 3 := by
  have h1 : (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 = 3 := by
    linear_combination golden_ratio_property_complex + psi_sq_complex + phi_add_psi_complex
  have h2 := phi_add_psi_complex
  constructor
  · intro h
    have hz := h 1
    simp only [Diff5_general, id_eq, mul_one] at hz
    have hcoef : (↑φ : ℂ)^2 - a * ↑φ + b - a * ↑ψ + (↑ψ : ℂ)^2 =
        ((↑φ : ℂ)^2 + (↑ψ : ℂ)^2) - a * ((↑φ : ℂ) + ↑ψ) + b := by ring
    rw [hcoef, h1, h2] at hz
    linear_combination hz
  · intro hb z
    simp only [Diff5_general, id_eq]
    have hcoef : (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - a * ((↑φ : ℂ) + ↑ψ) + b = 0 := by
      rw [h1, h2, hb]; ring
    have hnum : (↑φ : ℂ)^2 * z - a * ((↑φ : ℂ) * z) + b * z - a * ((↑ψ : ℂ) * z) + (↑ψ : ℂ)^2 * z =
        ((↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - a * ((↑φ : ℂ) + ↑ψ) + b) * z := by ring
    rw [hnum, hcoef, zero_mul]

/-- Diff5 coefficient uniqueness: Diff5[1] = 0 and Diff5[id] = 0 determine a = -1, b = -4 -/
theorem Diff5_coefficients_unique :
    ∀ a b : ℂ,
    (∀ z : ℂ, Diff5_general a b (fun _ => 1) z = 0) →
    (∀ z : ℂ, Diff5_general a b id z = 0) →
    a = -1 ∧ b = -4 := by
  intro a b h0 h1
  have eq1 : b = 2 * a - 2 := Diff5_C0_condition a b |>.mp h0
  have eq2 : b = a - 3 := Diff5_C1_condition a b |>.mp h1
  have ha : a = -1 := by linear_combination eq2 - eq1
  have hb : b = -4 := by rw [eq2, ha]; ring
  exact ⟨ha, hb⟩

/-- Diff5_general with determined coefficients equals Diff5 -/
theorem Diff5_general_eq_Diff5 (f : ℂ → ℂ) (z : ℂ) :
    Diff5_general (-1) (-4) f z = Diff5 f z := by
  simp only [Diff5_general, Diff5]; ring

/-- Condition D1: Diff6[id] = 0 iff F₃ - A·F₂ + B·F₁ = 0, i.e., 2 - A + B = 0 -/
theorem Diff6_D1_condition (A B : ℂ) :
    (∀ z : ℂ, Diff6_general A B id z = 0) ↔ B = A - 2 := by
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  constructor
  · intro h
    have hz := h 1
    simp only [Diff6_general, id_eq, mul_one] at hz
    have hfact : (2 - A + B) * ((↑φ : ℂ) - ↑ψ) = 0 := by
      linear_combination hz + A * hφ2 - A * hψ2 - hφ3 + hψ3
    have := (mul_eq_zero.mp hfact).resolve_right phi_sub_psi_complex_ne
    linear_combination this
  · intro hB z
    simp only [Diff6_general, id_eq]
    have hnum : (↑φ : ℂ)^3 * z - A * ((↑φ : ℂ)^2 * z) + B * ((↑φ : ℂ) * z) - B * ((↑ψ : ℂ) * z) +
        A * ((↑ψ : ℂ)^2 * z) - (↑ψ : ℂ)^3 * z = (((↑φ : ℂ)^3 - (↑ψ : ℂ)^3) - A * ((↑φ : ℂ)^2
        - (↑ψ : ℂ)^2) + B * ((↑φ : ℂ) - ↑ψ)) * z := by ring
    have hcoef :
        ((↑φ : ℂ)^3 - (↑ψ : ℂ)^3) - A * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) + B * ((↑φ : ℂ) - ↑ψ) = 0 := by
      have : (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 = 2 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ3 - hψ3
      have : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by linear_combination hφ2 - hψ2
      rw [‹_ ^ 3 - _ ^ 3 = _›, ‹_ ^ 2 - _ ^ 2 = _›, hB]; ring
    rw [hnum, hcoef, zero_mul]

/-- Condition D2: Diff6[x²] = 0 iff F₆ - A·F₄ + B·F₂ = 0, i.e., 8 - 3A + B = 0 -/
theorem Diff6_D2_condition (A B : ℂ) :
    (∀ z : ℂ, Diff6_general A B (fun t => t^2) z = 0) ↔ B = 3 * A - 8 := by
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ6 := phi_pow6_complex
  have hψ6 := psi_pow6_complex
  constructor
  · intro h
    have hz := h 1
    simp only [Diff6_general, mul_one] at hz
    have hfact : (8 - 3 * A + B) * ((↑φ : ℂ) - ↑ψ) = 0 := by
      linear_combination hz + A * hφ4 - A * hψ4 - B * hφ2 + B * hψ2 - hφ6 + hψ6
    have := (mul_eq_zero.mp hfact).resolve_right phi_sub_psi_complex_ne
    linear_combination this
  · intro hB z
    simp only [Diff6_general]
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

/-- Diff6 coefficient uniqueness: Diff6[id] = 0 and Diff6[x²] = 0 determine A = 3, B = 1 -/
theorem Diff6_coefficients_unique :
    ∀ A B : ℂ,
    (∀ z : ℂ, Diff6_general A B id z = 0) →
    (∀ z : ℂ, Diff6_general A B (fun t => t^2) z = 0) →
    A = 3 ∧ B = 1 := by
  intro A B h1 h2
  have eq1 : B = A - 2 := Diff6_D1_condition A B |>.mp h1
  have eq2 : B = 3 * A - 8 := Diff6_D2_condition A B |>.mp h2
  have hA : A = 3 := by linear_combination (eq1 - eq2) / 2
  have hB : B = 1 := by rw [eq1, hA]; ring
  exact ⟨hA, hB⟩

/-- Diff6_general with determined coefficients equals Diff6 -/
theorem Diff6_general_eq_Diff6 (f : ℂ → ℂ) (z : ℂ) :
    Diff6_general 3 1 f z = Diff6 f z := by
  simp only [Diff6_general, Diff6]; ring

/-- Complete coefficient uniqueness for Diff5 and Diff6 -/
theorem FUST_coefficient_uniqueness :
    (∀ a b : ℂ,
      (∀ z, Diff5_general a b (fun _ => 1) z = 0) →
      (∀ z, Diff5_general a b id z = 0) →
      a = -1 ∧ b = -4) ∧
    (∀ A B : ℂ,
      (∀ z, Diff6_general A B id z = 0) →
      (∀ z, Diff6_general A B (fun t => t^2) z = 0) →
      A = 3 ∧ B = 1) :=
  ⟨Diff5_coefficients_unique, Diff6_coefficients_unique⟩

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
## Diff7 Algebraic Reduction to Diff6

Diff7 antisymmetric numerator form: [1, -a, b, -c, +c, -b, +a, -1]
Diff7(a,b,c)[f](z) = f(φ⁴z) - a·f(φ³z) + b·f(φ²z) - c·f(φz)
                      + c·f(ψz) - b·f(ψ²z) + a·f(ψ³z) - f(ψ⁴z)

Key result: ker(Diff7) = ker(Diff6) implies Diff7 provides no new structure.
-/

section Diff7Reduction

/-- Diff7 general antisymmetric numerator with parameters (a, b, c) -/
noncomputable def Diff7_general (a b c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^4 * z) - a * f ((↑φ : ℂ)^3 * z) + b * f ((↑φ : ℂ)^2 * z)
    - c * f ((↑φ : ℂ) * z) + c * f ((↑ψ : ℂ) * z) - b * f ((↑ψ : ℂ)^2 * z)
    + a * f ((↑ψ : ℂ)^3 * z) - f ((↑ψ : ℂ)^4 * z)

/-- Condition E0: Diff7[1] = 0 holds for antisymmetric form (coefficient sum = 0) -/
theorem Diff7_E0_condition (a b c : ℂ) :
    ∀ z : ℂ, Diff7_general a b c (fun _ => 1) z = 0 := by
  intro z
  simp only [Diff7_general]; ring

/-- Condition E1: Diff7[id] = 0 iff 3 - 2a + b - c = 0
    (using Fibonacci: F₄ = 3, F₃ = 2, F₂ = 1, F₁ = 1) -/
theorem Diff7_E1_condition (a b c : ℂ) :
    (∀ z : ℂ, Diff7_general a b c id z = 0) ↔ 3 - 2 * a + b - c = 0 := by
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  constructor
  · intro h
    have hz := h 1
    simp only [Diff7_general, id_eq, mul_one] at hz
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
    simp only [Diff7_general, id_eq]
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

/-- Condition E2: Diff7[x²] = 0 iff F₈ - a·F₆ + b·F₄ - c·F₂ = 21 - 8a + 3b - c = 0 -/
theorem Diff7_E2_condition (a b c : ℂ) :
    (∀ z : ℂ, Diff7_general a b c (fun t => t^2) z = 0) ↔ 21 - 8 * a + 3 * b - c = 0 := by
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
    simp only [Diff7_general, mul_one] at hz
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
    simp only [Diff7_general]
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

/-- Diff7 coefficient constraint: E1 and E2 imply c = a - 6, b = 3a - 9 (1 free parameter) -/
theorem Diff7_coefficients_constrained (a b c : ℂ) :
    (∀ z : ℂ, Diff7_general a b c id z = 0) →
    (∀ z : ℂ, Diff7_general a b c (fun t => t^2) z = 0) →
    c = a - 6 ∧ b = 3 * a - 9 := by
  intro h1 h2
  have eq1 : 3 - 2 * a + b - c = 0 := Diff7_E1_condition a b c |>.mp h1
  have eq2 : 21 - 8 * a + 3 * b - c = 0 := Diff7_E2_condition a b c |>.mp h2
  constructor
  · linear_combination (eq2 - 3 * eq1) / 2
  · linear_combination (eq2 - eq1) / 2

/-- Diff7 with constrained coefficients: a arbitrary, b = 3a - 9, c = a - 6 -/
noncomputable def Diff7_constrained (a : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Diff7_general a (3 * a - 9) (a - 6) f z

/-- Diff7_constrained annihilates constants -/
theorem Diff7_constrained_const (a : ℂ) (k : ℂ) (z : ℂ) :
    Diff7_constrained a (fun _ => k) z = 0 := by
  simp only [Diff7_constrained, Diff7_general]; ring

/-- Diff7_constrained annihilates linear functions -/
theorem Diff7_constrained_linear (a : ℂ) :
    ∀ z : ℂ, Diff7_constrained a id z = 0 := by
  intro z; simp only [Diff7_constrained]
  have h : 3 - 2 * a + (3 * a - 9) - (a - 6) = 0 := by ring
  exact Diff7_E1_condition a (3*a - 9) (a - 6) |>.mpr h z

/-- Diff7_constrained annihilates quadratic functions -/
theorem Diff7_constrained_quadratic (a : ℂ) :
    ∀ z : ℂ, Diff7_constrained a (fun t => t^2) z = 0 := by
  intro z; simp only [Diff7_constrained]
  have h : 21 - 8 * a + 3 * (3 * a - 9) - (a - 6) = 0 := by ring
  exact Diff7_E2_condition a (3*a - 9) (a - 6) |>.mpr h z

/-- ker(Diff7) = ker(Diff6): Diff7 annihilates {1, z, z²} (same as Diff6 kernel) -/
theorem Diff7_kernel_equals_Diff6_kernel (a : ℂ) :
    (∀ c z, Diff7_constrained a (fun _ => c) z = 0) ∧
    (∀ z, Diff7_constrained a id z = 0) ∧
    (∀ z, Diff7_constrained a (fun t => t^2) z = 0) :=
  ⟨fun c z => Diff7_constrained_const a c z,
   Diff7_constrained_linear a,
   Diff7_constrained_quadratic a⟩

end Diff7Reduction

/-! ## ζ₆ convolution filters: AFNum and SymNum

Anti-Fibonacci sequence: C_n = C_{n-1} - C_{n-2}, C_0=0, C_1=1.
Period 6: [0, 1, 1, 0, -1, -1]. Recurrence mirrors ζ₆²=ζ₆-1.

AFNum: antisymmetric filter with coefficients C_k = [0,1,1,0,-1,-1]
SymNum: symmetric filter with coefficients 2Re(ζ₆^k) = [2,1,-1,-2,-1,1]

For s ≡ 1 mod 6: AFNum selects AF_coeff = 2i√3, SymNum selects 6.
For s ≡ 5 mod 6: AFNum selects -AF_coeff, SymNum selects 6.
For s ≡ 0,2,3,4 mod 6: both filters annihilate. -/

/-- Anti-Fibonacci numerator: Σ C_k · g(ζ₆^k · z) for C_k = [0,1,1,0,-1,-1] -/
noncomputable def AFNum (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  g (ζ₆ * z) + g (ζ₆ ^ 2 * z) - g (ζ₆ ^ 4 * z) - g (ζ₆ ^ 5 * z)

/-- Symmetric 6-point: Σ 2Re(ζ₆^k) · g(ζ₆^k · z), coefficients [2,1,-1,-2,-1,1] -/
noncomputable def SymNum (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  2 * g z + g (ζ₆ * z) - g (ζ₆ ^ 2 * z) - 2 * g (ζ₆ ^ 3 * z) -
  g (ζ₆ ^ 4 * z) + g (ζ₆ ^ 5 * z)

private lemma zeta6k_mul_ne (k : ℕ) (z : ℂ) (hz : z ≠ 0) : ζ₆ ^ k * z ≠ 0 := by
  apply mul_ne_zero _ hz
  exact pow_ne_zero k zeta6_ne_zero

private lemma zeta6_mul_ne (z : ℂ) (hz : z ≠ 0) : ζ₆ * z ≠ 0 :=
  mul_ne_zero zeta6_ne_zero hz

/-- AFNum annihilates constant functions -/
theorem AFNum_const (c : ℂ) (z : ℂ) : AFNum (fun _ => c) z = 0 := by
  unfold AFNum; ring

/-- SymNum annihilates constant functions -/
theorem SymNum_const (c : ℂ) (z : ℂ) : SymNum (fun _ => c) z = 0 := by
  unfold SymNum; ring

/-- AFNum is additive: AFNum(f+g) = AFNum(f) + AFNum(g) -/
theorem AFNum_add (f g : ℂ → ℂ) (z : ℂ) :
    AFNum (fun w => f w + g w) z = AFNum f z + AFNum g z := by
  unfold AFNum; ring

/-- SymNum is additive: SymNum(f+g) = SymNum(f) + SymNum(g) -/
theorem SymNum_add (f g : ℂ → ℂ) (z : ℂ) :
    SymNum (fun w => f w + g w) z = SymNum f z + SymNum g z := by
  unfold SymNum; ring

/-! ## Dζ operator

Rank-2 operator on ⟨φ,ζ₆⟩ ≅ ℤ × ℤ/6ℤ.
C(a,k) = AF_k·Φ_A(a) + SY_k·Φ_S(a) where:
  Φ_A = Diff6 + Diff2 - Diff4: antisymmetric channel
  Φ_S = 2·Diff5 + Diff3 + μ·Diff2: symmetric channel, μ = 2/(φ+2)
Half-period: C(a, k+3) = -C(a, k) from AF/SY anti-periodicity. -/

/-- Φ_A: φ-numerator = Diff6 + Diff2 - Diff4, all 6 ops AF channel -/
noncomputable def Φ_A (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) ^ 3 * z) - 4 * f ((↑φ : ℂ) ^ 2 * z) +
  (3 + (↑φ : ℂ)) * f (↑φ * z) - (3 + (↑ψ : ℂ)) * f (↑ψ * z) +
  4 * f ((↑ψ : ℂ) ^ 2 * z) - f ((↑ψ : ℂ) ^ 3 * z)

/-- Φ_S: φ-numerator = 2·Diff5 + Diff3 + μ·Diff2, all 6 ops SY channel -/
noncomputable def Φ_S (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let μ : ℂ := 2 / ((↑φ : ℂ) + 2)
  2 * Diff5 f z + Diff3 f z + μ * Diff2 f z

/-- Dζ: rank-2 on lattice ⟨φ,ζ₆⟩, encoding all 6 operators -/
noncomputable def Dζ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (AFNum (Φ_A f) z + SymNum (Φ_S f) z) / z

lemma phi_plus_two_ne : (↑φ : ℂ) + 2 ≠ 0 := by
  rw [ne_eq, ← ofReal_ofNat, ← ofReal_add, ofReal_eq_zero]
  linarith [phi_pos]

/-- Φ_A on constants: Σ = 1-4+(3+φ)-(3+ψ)+4-1 = φ-ψ (not zero, but AFNum kills it) -/
theorem Φ_A_const (c : ℂ) (z : ℂ) :
    Φ_A (fun _ => c) z = ((↑φ : ℂ) - ↑ψ) * c := by
  unfold Φ_A; ring

/-- Φ_S annihilates constants: 2+(3+μ)-10+(3-μ)+2 = 0 -/
theorem Φ_S_const (c : ℂ) (z : ℂ) : Φ_S (fun _ => c) z = 0 := by
  simp only [Φ_S, Diff5, Diff3, Diff2]
  have hφ2 : (↑φ : ℂ) + 2 ≠ 0 := phi_plus_two_ne
  field_simp; ring

/-- Dζ annihilates constants (Φ_A gives const, AFNum kills it) -/
theorem Dζ_const (z : ℂ) : Dζ (fun _ => 1) z = 0 := by
  simp only [Dζ]
  have hA : ∀ w, Φ_A (fun _ => (1 : ℂ)) w = ((↑φ : ℂ) - ↑ψ) * 1 :=
    fun w => Φ_A_const 1 w
  have hS : ∀ w, Φ_S (fun _ => (1 : ℂ)) w = 0 := fun w => Φ_S_const 1 w
  simp only [AFNum, hA, SymNum, hS, mul_one]
  simp [sub_self]

/-- Decomposition: Φ_A = Diff6 + Diff2 - Diff4 -/
theorem Φ_A_decompose (f : ℂ → ℂ) (z : ℂ) :
    Φ_A f z = Diff6 f z + Diff2 f z - Diff4 f z := by
  unfold Φ_A Diff6 Diff2 Diff4
  have hφ2 : (↑φ : ℂ) ^ 2 = ↑φ + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ) ^ 2 = ↑ψ + 1 := psi_sq_complex
  rw [hφ2, hψ2]; ring

/-! ## Fourier coefficients: AF = 2i√3, SY = 6

For f = w^s with s coprime to 6, the ζ₆ Fourier coefficients are:
  AFNum factor = ζ₆^s + ζ₆^{2s} - ζ₆^{4s} - ζ₆^{5s}
  SymNum factor = 2 + ζ₆^s - ζ₆^{2s} - 2ζ₆^{3s} - ζ₆^{4s} + ζ₆^{5s}
For s ≡ 1 mod 6: AF = 2i√3, SY = 6.  For s ≡ 5 mod 6: AF = -2i√3, SY = 6. -/

/-- AF_coeff = ζ₆+ζ₆²-ζ₆⁴-ζ₆⁵ = (ζ₆-ζ₆⁵)+(ζ₆²-ζ₆⁴) -/
noncomputable def AF_coeff : ℂ := ζ₆ + ζ₆ ^ 2 - ζ₆ ^ 4 - ζ₆ ^ 5

/-- AF_coeff = 2i√3 -/
theorem AF_coeff_eq : AF_coeff = ⟨0, 2 * Real.sqrt 3⟩ := by
  unfold AF_coeff; rw [zeta6_sq, zeta6_pow_four, zeta6_pow_five]
  ext <;> simp [ζ₆] <;> ring

/-- 2+ζ₆-ζ₆²-2ζ₆³-ζ₆⁴+ζ₆⁵ = 6 -/
theorem SY_coeff_val :
    (2 : ℂ) + ζ₆ - ζ₆ ^ 2 - 2 * ζ₆ ^ 3 - ζ₆ ^ 4 + ζ₆ ^ 5 = 6 := by
  rw [zeta6_sq, zeta6_cubed, zeta6_pow_four, zeta6_pow_five]
  ext <;> simp [ζ₆]; ring

/-! ## Monomial mode selection: (ζ₆^j)^{6k+r} = ζ₆^{jr} -/

private theorem zeta6_pow_pow_6k1 (j k : ℕ) : (ζ₆ ^ j) ^ (6 * k + 1) = ζ₆ ^ j := by
  rw [← pow_mul, show j * (6 * k + 1) = 6 * (j * k) + j from by ring,
      pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

private theorem zeta6_pow_6k1 (k : ℕ) : ζ₆ ^ (6 * k + 1) = ζ₆ := by
  rw [pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul, pow_one]

private theorem zeta6_pow_pow_6k5 (j k : ℕ) : (ζ₆ ^ j) ^ (6 * k + 5) = ζ₆ ^ (5 * j) := by
  rw [← pow_mul, show j * (6 * k + 5) = 6 * (j * k) + 5 * j from by ring,
      pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

private theorem zeta6_pow_6k5 (k : ℕ) : ζ₆ ^ (6 * k + 5) = ζ₆ ^ 5 := by
  rw [pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

/-- AFNum on w^{6k+1} = AF_coeff · z^{6k+1} -/
theorem AFNum_pow_mod6_1 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 1)) z = z ^ (6 * k + 1) * AF_coeff := by
  simp only [AFNum, AF_coeff, mul_pow, zeta6_pow_6k1,
    zeta6_pow_pow_6k1 2, zeta6_pow_pow_6k1 4, zeta6_pow_pow_6k1 5]
  ring

/-- SymNum on w^{6k+1} = 6 · z^{6k+1} -/
theorem SymNum_pow_mod6_1 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 1)) z = 6 * z ^ (6 * k + 1) := by
  simp only [SymNum, mul_pow, zeta6_pow_6k1,
    zeta6_pow_pow_6k1 2, zeta6_pow_pow_6k1 3, zeta6_pow_pow_6k1 4, zeta6_pow_pow_6k1 5]
  have key : (2 : ℂ) * z ^ (6 * k + 1) + ζ₆ * z ^ (6 * k + 1) - ζ₆ ^ 2 * z ^ (6 * k + 1) -
    2 * (ζ₆ ^ 3 * z ^ (6 * k + 1)) - ζ₆ ^ 4 * z ^ (6 * k + 1) +
    ζ₆ ^ 5 * z ^ (6 * k + 1) =
    (2 + ζ₆ - ζ₆ ^ 2 - 2 * ζ₆ ^ 3 - ζ₆ ^ 4 + ζ₆ ^ 5) * z ^ (6 * k + 1) := by ring
  rw [key, SY_coeff_val]

private theorem AF_coeff_mod5 :
    ζ₆ ^ 5 + ζ₆ ^ 10 - ζ₆ ^ 20 - ζ₆ ^ 25 = -AF_coeff := by
  unfold AF_coeff
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_mul]
  have h20 : ζ₆ ^ 20 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 20 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_pow, one_mul]
  have h25 : ζ₆ ^ 25 = ζ₆ := by
    calc ζ₆ ^ 25 = (ζ₆ ^ 6) ^ 4 * ζ₆ := by ring
    _ = ζ₆ := by rw [zeta6_pow_six, one_pow, one_mul]
  rw [h10, h20, h25]; ring

/-- AFNum on w^{6k+5} = -AF_coeff · z^{6k+5} -/
theorem AFNum_pow_mod6_5 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 5)) z = -(z ^ (6 * k + 5) * AF_coeff) := by
  simp only [AFNum, mul_pow, zeta6_pow_6k5,
    zeta6_pow_pow_6k5 2, zeta6_pow_pow_6k5 4, zeta6_pow_pow_6k5 5]
  simp only [show 5 * 2 = 10 from by ring,
             show 5 * 4 = 20 from by ring, show 5 * 5 = 25 from by ring]
  have key : ζ₆ ^ 5 * z ^ (6 * k + 5) + ζ₆ ^ 10 * z ^ (6 * k + 5) -
    ζ₆ ^ 20 * z ^ (6 * k + 5) - ζ₆ ^ 25 * z ^ (6 * k + 5) =
    (ζ₆ ^ 5 + ζ₆ ^ 10 - ζ₆ ^ 20 - ζ₆ ^ 25) * z ^ (6 * k + 5) := by ring
  rw [key, AF_coeff_mod5]; ring

private theorem SY_coeff_mod5 :
    (2 : ℂ) + ζ₆ ^ 5 - ζ₆ ^ 10 - 2 * ζ₆ ^ 15 - ζ₆ ^ 20 + ζ₆ ^ 25 = 6 := by
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_mul]
  have h15 : ζ₆ ^ 15 = -1 := by
    calc ζ₆ ^ 15 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 3 := by ring
    _ = ζ₆ ^ 3 := by rw [zeta6_pow_six, one_pow, one_mul]
    _ = -1 := zeta6_cubed
  have h20 : ζ₆ ^ 20 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 20 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_pow, one_mul]
  have h25 : ζ₆ ^ 25 = ζ₆ := by
    calc ζ₆ ^ 25 = (ζ₆ ^ 6) ^ 4 * ζ₆ := by ring
    _ = ζ₆ := by rw [zeta6_pow_six, one_pow, one_mul]
  rw [h10, h15, h20, h25, zeta6_pow_four, zeta6_pow_five, zeta6_sq]
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  ext
  · simp [ζ₆]; nlinarith
  · simp [ζ₆]

/-- SymNum on w^{6k+5} = 6 · z^{6k+5} -/
theorem SymNum_pow_mod6_5 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 5)) z = 6 * z ^ (6 * k + 5) := by
  simp only [SymNum, mul_pow, zeta6_pow_6k5,
    zeta6_pow_pow_6k5 2, zeta6_pow_pow_6k5 3, zeta6_pow_pow_6k5 4, zeta6_pow_pow_6k5 5]
  simp only [show 5 * 2 = 10 from by ring, show 5 * 3 = 15 from by ring,
             show 5 * 4 = 20 from by ring, show 5 * 5 = 25 from by ring]
  have key : (2 : ℂ) * z ^ (6 * k + 5) + ζ₆ ^ 5 * z ^ (6 * k + 5) -
    ζ₆ ^ 10 * z ^ (6 * k + 5) - 2 * (ζ₆ ^ 15 * z ^ (6 * k + 5)) -
    ζ₆ ^ 20 * z ^ (6 * k + 5) + ζ₆ ^ 25 * z ^ (6 * k + 5) =
    (2 + ζ₆ ^ 5 - ζ₆ ^ 10 - 2 * ζ₆ ^ 15 - ζ₆ ^ 20 + ζ₆ ^ 25) * z ^ (6 * k + 5) := by ring
  rw [key, SY_coeff_mod5]

/-! ## Mod 6 vanishing: AFNum and SymNum kill w^n for gcd(n,6) > 1

For n ≡ 0,2,3,4 mod 6, the ζ₆-multiplexing sums vanish:
  AF_n := ζ₆ⁿ + ζ₆²ⁿ - ζ₆⁴ⁿ - ζ₆⁵ⁿ = 0
  SY_n := 2 + ζ₆ⁿ - ζ₆²ⁿ - 2ζ₆³ⁿ - ζ₆⁴ⁿ + ζ₆⁵ⁿ = 0 -/

private theorem zeta6_pow_6kr (k r : ℕ) : ζ₆ ^ (6 * k + r) = ζ₆ ^ r := by
  rw [pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

private theorem zeta6_pow_pow_6k (j k r : ℕ) :
    (ζ₆ ^ j) ^ (6 * k + r) = ζ₆ ^ (j * r) := by
  rw [← pow_mul, show j * (6 * k + r) = 6 * (j * k) + j * r from by ring,
      pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

/-- AFNum on w^{6k} = 0 -/
theorem AFNum_pow_mod6_0 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k)) z = 0 := by
  simp only [AFNum, mul_pow]
  have h1 : ζ₆ ^ (6 * k) = 1 := by rw [pow_mul, zeta6_pow_six, one_pow]
  have h2 : (ζ₆ ^ 2) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 2*(6*k) = 6*(2*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h4 : (ζ₆ ^ 4) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 4*(6*k) = 6*(4*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h5 : (ζ₆ ^ 5) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 5*(6*k) = 6*(5*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  rw [h1, h2, h4, h5]; ring

/-- SymNum on w^{6k} = 0 -/
theorem SymNum_pow_mod6_0 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k)) z = 0 := by
  simp only [SymNum, mul_pow]
  have h1 : ζ₆ ^ (6 * k) = 1 := by rw [pow_mul, zeta6_pow_six, one_pow]
  have h2 : (ζ₆ ^ 2) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 2*(6*k) = 6*(2*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h3 : (ζ₆ ^ 3) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 3*(6*k) = 6*(3*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h4 : (ζ₆ ^ 4) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 4*(6*k) = 6*(4*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h5 : (ζ₆ ^ 5) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 5*(6*k) = 6*(5*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  rw [h1, h2, h3, h4, h5]; ring

private theorem zeta6_pow_red (n r : ℕ) (h : n = 6 * (n / 6) + r) : ζ₆ ^ n = ζ₆ ^ r := by
  rw [h, zeta6_pow_6kr]

/-- AFNum on w^{6k+2} = 0 (ζ₆²+ζ₆⁴-ζ₆⁸-ζ₆¹⁰ = 0) -/
theorem AFNum_pow_mod6_2 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 2)) z = 0 := by
  simp only [AFNum, mul_pow]
  rw [zeta6_pow_6kr k 2,
      zeta6_pow_pow_6k 2 k 2, show 2 * 2 = 4 from by ring,
      zeta6_pow_pow_6k 4 k 2, show 4 * 2 = 8 from by ring,
      zeta6_pow_pow_6k 5 k 2, show 5 * 2 = 10 from by ring]
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_mul]
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_mul]
  rw [h8, h10]; ring

/-- SymNum on w^{6k+2} = 0 -/
theorem SymNum_pow_mod6_2 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 2)) z = 0 := by
  simp only [SymNum, mul_pow]
  rw [zeta6_pow_6kr k 2,
      zeta6_pow_pow_6k 2 k 2, show 2 * 2 = 4 from by ring,
      zeta6_pow_pow_6k 3 k 2, show 3 * 2 = 6 from by ring,
      zeta6_pow_pow_6k 4 k 2, show 4 * 2 = 8 from by ring,
      zeta6_pow_pow_6k 5 k 2, show 5 * 2 = 10 from by ring]
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_mul]
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_mul]
  rw [zeta6_pow_six, h8, h10]; ring

/-- AFNum on w^{6k+3} = 0 (ζ₆³=-1 cancellation) -/
theorem AFNum_pow_mod6_3 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 3)) z = 0 := by
  simp only [AFNum, mul_pow]
  rw [zeta6_pow_6kr k 3,
      zeta6_pow_pow_6k 2 k 3, show 2 * 3 = 6 from by ring,
      zeta6_pow_pow_6k 4 k 3, show 4 * 3 = 12 from by ring,
      zeta6_pow_pow_6k 5 k 3, show 5 * 3 = 15 from by ring]
  have h12 : ζ₆ ^ 12 = 1 := by
    calc ζ₆ ^ 12 = (ζ₆ ^ 6) ^ 2 := by ring
    _ = 1 := by rw [zeta6_pow_six, one_pow]
  have h15 : ζ₆ ^ 15 = -1 := by
    calc ζ₆ ^ 15 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 3 := by ring
    _ = ζ₆ ^ 3 := by rw [zeta6_pow_six, one_pow, one_mul]
    _ = -1 := zeta6_cubed
  rw [zeta6_cubed, zeta6_pow_six, h12, h15]; ring

/-- SymNum on w^{6k+3} = 0 -/
theorem SymNum_pow_mod6_3 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 3)) z = 0 := by
  simp only [SymNum, mul_pow]
  rw [zeta6_pow_6kr k 3,
      zeta6_pow_pow_6k 2 k 3, show 2 * 3 = 6 from by ring,
      zeta6_pow_pow_6k 3 k 3, show 3 * 3 = 9 from by ring,
      zeta6_pow_pow_6k 4 k 3, show 4 * 3 = 12 from by ring,
      zeta6_pow_pow_6k 5 k 3, show 5 * 3 = 15 from by ring]
  have h9 : ζ₆ ^ 9 = -1 := by
    calc ζ₆ ^ 9 = ζ₆ ^ 6 * ζ₆ ^ 3 := by ring
    _ = ζ₆ ^ 3 := by rw [zeta6_pow_six, one_mul]
    _ = -1 := zeta6_cubed
  have h12 : ζ₆ ^ 12 = 1 := by
    calc ζ₆ ^ 12 = (ζ₆ ^ 6) ^ 2 := by ring
    _ = 1 := by rw [zeta6_pow_six, one_pow]
  have h15 : ζ₆ ^ 15 = -1 := by
    calc ζ₆ ^ 15 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 3 := by ring
    _ = ζ₆ ^ 3 := by rw [zeta6_pow_six, one_pow, one_mul]
    _ = -1 := zeta6_cubed
  rw [zeta6_cubed, zeta6_pow_six, h9, h12, h15]; ring

/-- AFNum on w^{6k+4} = 0 (ζ₆⁴=-ζ₆ cancellation) -/
theorem AFNum_pow_mod6_4 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 4)) z = 0 := by
  simp only [AFNum, mul_pow]
  rw [zeta6_pow_6kr k 4,
      zeta6_pow_pow_6k 2 k 4, show 2 * 4 = 8 from by ring,
      zeta6_pow_pow_6k 4 k 4, show 4 * 4 = 16 from by ring,
      zeta6_pow_pow_6k 5 k 4, show 5 * 4 = 20 from by ring]
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_mul]
  have h16 : ζ₆ ^ 16 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 16 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_pow, one_mul]
  have h20 : ζ₆ ^ 20 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 20 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_pow, one_mul]
  rw [h8, h16, h20]; ring

/-- SymNum on w^{6k+4} = 0 -/
theorem SymNum_pow_mod6_4 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 4)) z = 0 := by
  simp only [SymNum, mul_pow]
  rw [zeta6_pow_6kr k 4,
      zeta6_pow_pow_6k 2 k 4, show 2 * 4 = 8 from by ring,
      zeta6_pow_pow_6k 3 k 4, show 3 * 4 = 12 from by ring,
      zeta6_pow_pow_6k 4 k 4, show 4 * 4 = 16 from by ring,
      zeta6_pow_pow_6k 5 k 4, show 5 * 4 = 20 from by ring]
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_mul]
  have h12 : ζ₆ ^ 12 = 1 := by
    calc ζ₆ ^ 12 = (ζ₆ ^ 6) ^ 2 := by ring
    _ = 1 := by rw [zeta6_pow_six, one_pow]
  have h16 : ζ₆ ^ 16 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 16 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_pow, one_mul]
  have h20 : ζ₆ ^ 20 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 20 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_pow, one_mul]
  rw [h8, h12, h16, h20]
  simp only [zeta6_pow_four]; ring

/-! ## Norm squared decomposition: |6a + 2i√3·b|² = 12(3a² + b²)

The unified Dζ output for monomial z^s decomposes as:
  Re(Dζ) = 6·Φ_S (symmetric/rotation channel, weight 3)
  Im(Dζ) = ±2√3·Φ_A (antisymmetric/boost channel, weight 1)
The 3:1 weight ratio in |Dζ|² encodes I4 = Fin 3 ⊕ Fin 1. -/

/-- |6a + AF_coeff·b|² = 12(3a² + b²) for real a, b -/
theorem Dζ_normSq_decomposition (a b : ℝ) :
    Complex.normSq (6 * (a : ℂ) + AF_coeff * b) = 12 * (3 * a ^ 2 + b ^ 2) := by
  rw [AF_coeff_eq]
  have heq : 6 * (a : ℂ) + (⟨0, 2 * Real.sqrt 3⟩ : ℂ) * (b : ℂ) =
    ⟨6 * a, 2 * Real.sqrt 3 * b⟩ := by ext <;> simp
  rw [heq, normSq_mk]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  nlinarith

/-- |AF_coeff|² = 12 -/
theorem AF_coeff_normSq : Complex.normSq AF_coeff = 12 := by
  have h := Dζ_normSq_decomposition 0 1
  simp only [ofReal_zero, mul_zero, zero_add, ofReal_one, mul_one] at h
  linarith

/-! ## Φ_S 3-component decomposition: Diff5 + Diff3 + μ·Diff2

Φ_S decomposes into 3 independent sub-operators (Dn numerators Diff2/Diff3/Diff5).
For monomials z^s, the coefficients σ_Diff_n(s) = Diff_n(z^s)/z^s form
rank-3 vectors across s=1,5,7, proving Φ_S carries Fin 3 of information. -/

/-- Φ_S = 2·Diff5 + Diff3 + μ·Diff2 -/
theorem Φ_S_decompose (f : ℂ → ℂ) (z : ℂ) :
    Φ_S f z = 2 * Diff5 f z + Diff3 f z +
    (2 / ((↑φ : ℂ) + 2)) * Diff2 f z := by
  unfold Φ_S Diff5 Diff3 Diff2; ring

/-- Diff_n on w^s: monomial coefficients -/
theorem Diff2_pow (s : ℕ) (z : ℂ) :
    Diff2 (fun w => w ^ s) z = ((↑φ : ℂ) ^ s - (↑ψ : ℂ) ^ s) * z ^ s := by
  unfold Diff2; simp only [mul_pow]; ring

theorem Diff3_pow (s : ℕ) (z : ℂ) :
    Diff3 (fun w => w ^ s) z = ((↑φ : ℂ) ^ s - 2 + (↑ψ : ℂ) ^ s) * z ^ s := by
  unfold Diff3; simp only [mul_pow]; ring

theorem Diff5_pow (s : ℕ) (z : ℂ) :
    Diff5 (fun w => w ^ s) z =
    ((↑φ : ℂ) ^ (2 * s) + (↑φ : ℂ) ^ s - 4 + (↑ψ : ℂ) ^ s + (↑ψ : ℂ) ^ (2 * s)) * z ^ s := by
  unfold Diff5; simp only [mul_pow, ← pow_mul]; ring

/-- Φ_S on w^s via sub-operator coefficients -/
theorem Φ_S_pow_via_sub (s : ℕ) (z : ℂ) :
    Φ_S (fun w => w ^ s) z =
    (2 * ((↑φ : ℂ) ^ (2 * s) + (↑φ : ℂ) ^ s - 4 + (↑ψ : ℂ) ^ s + (↑ψ : ℂ) ^ (2 * s)) +
     ((↑φ : ℂ) ^ s - 2 + (↑ψ : ℂ) ^ s) +
     (2 / ((↑φ : ℂ) + 2)) * ((↑φ : ℂ) ^ s - (↑ψ : ℂ) ^ s)) * z ^ s := by
  unfold Φ_S Diff5 Diff3 Diff2; simp only [mul_pow, ← pow_mul]; ring

/-! ### Golden ratio powers as F_n·φ + F_{n-1} -/

private lemma psi_eq_c : (↑ψ : ℂ) = 1 - ↑φ := by
  have h : φ + ψ = 1 := phi_add_psi
  have : (↑ψ : ℂ) = ↑(1 - φ) := by rw [show 1 - φ = ψ from by linarith]
  rw [this, ofReal_sub, ofReal_one]

private lemma phi_sq_c : (↑φ : ℂ) ^ 2 = ↑φ + 1 := by
  have h := golden_ratio_property
  have : (↑(φ ^ 2) : ℂ) = ↑(φ + 1) := congrArg _ h
  simp only [ofReal_pow, ofReal_add, ofReal_one] at this; exact this

private lemma phi_pow3_c : (↑φ : ℂ) ^ 3 = 2 * ↑φ + 1 := by
  calc (↑φ : ℂ) ^ 3 = (↑φ : ℂ) ^ 2 * ↑φ := by ring
    _ = ((↑φ : ℂ) + 1) * ↑φ := by rw [phi_sq_c]
    _ = (↑φ : ℂ) ^ 2 + ↑φ := by ring
    _ = (↑φ : ℂ) + 1 + ↑φ := by rw [phi_sq_c]
    _ = 2 * ↑φ + 1 := by ring

private lemma phi_pow4_c : (↑φ : ℂ) ^ 4 = 3 * ↑φ + 2 := by
  calc (↑φ : ℂ) ^ 4 = (↑φ : ℂ) ^ 3 * ↑φ := by ring
    _ = (2 * ↑φ + 1) * ↑φ := by rw [phi_pow3_c]
    _ = 2 * (↑φ : ℂ) ^ 2 + ↑φ := by ring
    _ = 2 * ((↑φ : ℂ) + 1) + ↑φ := by rw [phi_sq_c]
    _ = 3 * ↑φ + 2 := by ring

private lemma phi_pow5_c : (↑φ : ℂ) ^ 5 = 5 * ↑φ + 3 := by
  calc (↑φ : ℂ) ^ 5 = (↑φ : ℂ) ^ 3 * (↑φ : ℂ) ^ 2 := by ring
    _ = (2 * ↑φ + 1) * ((↑φ : ℂ) + 1) := by rw [phi_pow3_c, phi_sq_c]
    _ = 2 * (↑φ : ℂ) ^ 2 + 3 * ↑φ + 1 := by ring
    _ = 2 * ((↑φ : ℂ) + 1) + 3 * ↑φ + 1 := by rw [phi_sq_c]
    _ = 5 * ↑φ + 3 := by ring

private lemma phi_pow7_c : (↑φ : ℂ) ^ 7 = 13 * ↑φ + 8 := by
  calc (↑φ : ℂ) ^ 7 = (↑φ : ℂ) ^ 5 * (↑φ : ℂ) ^ 2 := by ring
    _ = (5 * ↑φ + 3) * ((↑φ : ℂ) + 1) := by rw [phi_pow5_c, phi_sq_c]
    _ = 5 * (↑φ : ℂ) ^ 2 + 8 * ↑φ + 3 := by ring
    _ = 5 * ((↑φ : ℂ) + 1) + 8 * ↑φ + 3 := by rw [phi_sq_c]
    _ = 13 * ↑φ + 8 := by ring

private lemma phi_pow10_c : (↑φ : ℂ) ^ 10 = 55 * ↑φ + 34 := by
  calc (↑φ : ℂ) ^ 10 = ((↑φ : ℂ) ^ 5) ^ 2 := by ring
    _ = (5 * ↑φ + 3) ^ 2 := by rw [phi_pow5_c]
    _ = 25 * (↑φ : ℂ) ^ 2 + 30 * ↑φ + 9 := by ring
    _ = 25 * ((↑φ : ℂ) + 1) + 30 * ↑φ + 9 := by rw [phi_sq_c]
    _ = 55 * ↑φ + 34 := by ring

private lemma phi_pow14_c : (↑φ : ℂ) ^ 14 = 377 * ↑φ + 233 := by
  calc (↑φ : ℂ) ^ 14 = ((↑φ : ℂ) ^ 7) ^ 2 := by ring
    _ = (13 * ↑φ + 8) ^ 2 := by rw [phi_pow7_c]
    _ = 169 * (↑φ : ℂ) ^ 2 + 208 * ↑φ + 64 := by ring
    _ = 169 * ((↑φ : ℂ) + 1) + 208 * ↑φ + 64 := by rw [phi_sq_c]
    _ = 377 * ↑φ + 233 := by ring

private lemma one_sub_phi_pow5 : (1 - (↑φ : ℂ)) ^ 5 = -(5 * ↑φ) + 8 := by
  have : (1 - (↑φ : ℂ)) ^ 5 =
    1 - 5 * ↑φ + 10 * (↑φ : ℂ) ^ 2 - 10 * (↑φ : ℂ) ^ 3 +
    5 * (↑φ : ℂ) ^ 4 - (↑φ : ℂ) ^ 5 := by ring
  rw [this, phi_sq_c, phi_pow3_c, phi_pow4_c, phi_pow5_c]; ring

private lemma one_sub_phi_pow7 : (1 - (↑φ : ℂ)) ^ 7 = -(13 * ↑φ) + 21 := by
  have h2 : (1 - (↑φ : ℂ)) ^ 2 = 2 - ↑φ := by
    have : (1 - (↑φ : ℂ)) ^ 2 = (↑φ : ℂ) ^ 2 - 2 * ↑φ + 1 := by ring
    rw [this, phi_sq_c]; ring
  calc (1 - (↑φ : ℂ)) ^ 7 = (1 - (↑φ : ℂ)) ^ 5 * (1 - (↑φ : ℂ)) ^ 2 := by ring
    _ = (-(5 * ↑φ) + 8) * (2 - ↑φ) := by rw [one_sub_phi_pow5, h2]
    _ = 5 * (↑φ : ℂ) ^ 2 - 18 * ↑φ + 16 := by ring
    _ = 5 * ((↑φ : ℂ) + 1) - 18 * ↑φ + 16 := by rw [phi_sq_c]
    _ = -(13 * ↑φ) + 21 := by ring

private lemma one_sub_phi_pow10 : (1 - (↑φ : ℂ)) ^ 10 = -(55 * ↑φ) + 89 := by
  calc (1 - (↑φ : ℂ)) ^ 10 = ((1 - (↑φ : ℂ)) ^ 5) ^ 2 := by ring
    _ = (-(5 * ↑φ) + 8) ^ 2 := by rw [one_sub_phi_pow5]
    _ = 25 * (↑φ : ℂ) ^ 2 - 80 * ↑φ + 64 := by ring
    _ = 25 * ((↑φ : ℂ) + 1) - 80 * ↑φ + 64 := by rw [phi_sq_c]
    _ = -(55 * ↑φ) + 89 := by ring

private lemma one_sub_phi_pow14 : (1 - (↑φ : ℂ)) ^ 14 = -(377 * ↑φ) + 610 := by
  calc (1 - (↑φ : ℂ)) ^ 14 = ((1 - (↑φ : ℂ)) ^ 7) ^ 2 := by ring
    _ = (-(13 * ↑φ) + 21) ^ 2 := by rw [one_sub_phi_pow7]
    _ = 169 * (↑φ : ℂ) ^ 2 - 546 * ↑φ + 441 := by ring
    _ = 169 * ((↑φ : ℂ) + 1) - 546 * ↑φ + 441 := by rw [phi_sq_c]
    _ = -(377 * ↑φ) + 610 := by ring

/-! ### Sub-operator coefficient values -/

/-- σ_Diff5(s) = L_{2s} + L_s - 4, σ_Diff3(s) = L_s - 2, σ_Diff2(s) = √5·F_s -/
noncomputable def σ_Diff5 (s : ℕ) : ℂ :=
  (↑φ : ℂ) ^ (2 * s) + (↑φ : ℂ) ^ s - 4 + (↑ψ : ℂ) ^ s + (↑ψ : ℂ) ^ (2 * s)

noncomputable def σ_Diff3 (s : ℕ) : ℂ := (↑φ : ℂ) ^ s - 2 + (↑ψ : ℂ) ^ s

noncomputable def σ_Diff2 (s : ℕ) : ℂ := (↑φ : ℂ) ^ s - (↑ψ : ℂ) ^ s

-- s = 1
theorem σ_Diff5_one : σ_Diff5 1 = 0 := by
  simp only [σ_Diff5, Nat.mul_one, pow_one, phi_sq_c, psi_eq_c]
  have : (1 - (↑φ : ℂ)) ^ 2 = (↑φ : ℂ) ^ 2 - 2 * ↑φ + 1 := by ring
  rw [this, phi_sq_c]; ring

theorem σ_Diff3_one : σ_Diff3 1 = -1 := by
  simp only [σ_Diff3, pow_one, psi_eq_c]; ring

theorem σ_Diff2_one : σ_Diff2 1 = (↑φ : ℂ) - ↑ψ := by
  simp only [σ_Diff2, pow_one]

-- s = 5
theorem σ_Diff5_five : σ_Diff5 5 = 130 := by
  simp only [σ_Diff5, show 2 * 5 = 10 from by ring, psi_eq_c]
  rw [phi_pow10_c, phi_pow5_c, one_sub_phi_pow5, one_sub_phi_pow10]; ring

theorem σ_Diff3_five : σ_Diff3 5 = 9 := by
  simp only [σ_Diff3, psi_eq_c]; rw [phi_pow5_c, one_sub_phi_pow5]; ring

theorem σ_Diff2_five : σ_Diff2 5 = 5 * ((↑φ : ℂ) - ↑ψ) := by
  simp only [σ_Diff2, psi_eq_c]; rw [phi_pow5_c, one_sub_phi_pow5]; ring

-- s = 7
theorem σ_Diff5_seven : σ_Diff5 7 = 868 := by
  simp only [σ_Diff5, show 2 * 7 = 14 from by ring, psi_eq_c]
  rw [phi_pow14_c, phi_pow7_c, one_sub_phi_pow7, one_sub_phi_pow14]; ring

theorem σ_Diff3_seven : σ_Diff3 7 = 27 := by
  simp only [σ_Diff3, psi_eq_c]; rw [phi_pow7_c, one_sub_phi_pow7]; ring

theorem σ_Diff2_seven : σ_Diff2 7 = 13 * ((↑φ : ℂ) - ↑ψ) := by
  simp only [σ_Diff2, psi_eq_c]; rw [phi_pow7_c, one_sub_phi_pow7]; ring

private lemma phi_sub_psi_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := by
  rw [← ofReal_sub, ne_eq, ofReal_eq_zero, sub_eq_zero]
  intro h; linarith [phi_pos, psi_neg]

/-- The 3×3 det of [σ_Diff5, σ_Diff3, σ_Diff2] at s=1,5,7 is -6952(φ-ψ) ≠ 0: rank 3.
    This proves Φ_S carries Fin 3 worth of independent information. -/
theorem Φ_S_rank_three :
    σ_Diff5 1 * (σ_Diff3 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff3 7) -
    σ_Diff3 1 * (σ_Diff5 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff5 7) +
    σ_Diff2 1 * (σ_Diff5 5 * σ_Diff3 7 - σ_Diff3 5 * σ_Diff5 7) ≠ 0 := by
  rw [σ_Diff5_one, σ_Diff3_one, σ_Diff2_one,
      σ_Diff5_five, σ_Diff3_five, σ_Diff2_five,
      σ_Diff5_seven, σ_Diff3_seven, σ_Diff2_seven]
  have hne := phi_sub_psi_ne
  intro h; apply hne
  have : (0 : ℂ) * (9 * (13 * ((↑φ : ℂ) - ↑ψ)) - 5 * ((↑φ : ℂ) - ↑ψ) * 27) -
    (-1 : ℂ) * ((130 : ℂ) * (13 * ((↑φ : ℂ) - ↑ψ)) - 5 * ((↑φ : ℂ) - ↑ψ) * 868) +
    ((↑φ : ℂ) - ↑ψ) * ((130 : ℂ) * 27 - 9 * 868) = -6952 * ((↑φ : ℂ) - ↑ψ) := by ring
  rw [this] at h
  by_contra hc
  exact absurd (mul_ne_zero (by norm_num : (-6952 : ℂ) ≠ 0) hc) (not_not.mpr h)

/-! ## Dζ Gauge Covariance

Dζ(f(c·))(z) = c · Dζ(f)(c·z) for any c ≠ 0.
"Continuity without limits": every observer at scale φⁿ sees identical
algebraic structure. A continuous-parameter limit (D_t → θ) would only
parametrize the φ-direction and cannot extend to full Dζ, because
the ζ₆-direction is compact-discrete (ℤ/6ℤ, period 6). -/

section GaugeCovariance

private lemma mul_comm_assoc' (c a z : ℂ) : c * (a * z) = a * (c * z) := by ring

/-- Φ_A is translation-equivariant: Φ_A(f(c·))(z) = Φ_A(f)(cz) -/
theorem Φ_A_translate (f : ℂ → ℂ) (c z : ℂ) :
    Φ_A (fun t => f (c * t)) z = Φ_A f (c * z) := by
  simp only [Φ_A, mul_comm_assoc']

/-- Φ_S is translation-equivariant: Φ_S(f(c·))(z) = Φ_S(f)(cz) -/
theorem Φ_S_translate (f : ℂ → ℂ) (c z : ℂ) :
    Φ_S (fun t => f (c * t)) z = Φ_S f (c * z) := by
  simp only [Φ_S, Diff5, Diff3, Diff2, mul_comm_assoc']

/-- AFNum is translation-equivariant: AFNum(g(c·))(z) = AFNum(g)(cz) -/
theorem AFNum_translate (g : ℂ → ℂ) (c z : ℂ) :
    AFNum (fun w => g (c * w)) z = AFNum g (c * z) := by
  simp only [AFNum, mul_comm_assoc']

/-- SymNum is translation-equivariant: SymNum(g(c·))(z) = SymNum(g)(cz) -/
theorem SymNum_translate (g : ℂ → ℂ) (c z : ℂ) :
    SymNum (fun w => g (c * w)) z = SymNum g (c * z) := by
  simp only [SymNum, mul_comm_assoc']

private lemma Φ_A_translate_fun (f : ℂ → ℂ) (c : ℂ) :
    Φ_A (fun t => f (c * t)) = fun w => Φ_A f (c * w) := by
  funext z; exact Φ_A_translate f c z

private lemma Φ_S_translate_fun (f : ℂ → ℂ) (c : ℂ) :
    Φ_S (fun t => f (c * t)) = fun w => Φ_S f (c * w) := by
  funext z; exact Φ_S_translate f c z

/-- Dζ gauge covariance: Dζ(f(c·))(z) = c · Dζ(f)(cz) -/
theorem Dζ_gauge_covariance (f : ℂ → ℂ) (c z : ℂ) (hc : c ≠ 0) (hz : z ≠ 0) :
    Dζ (fun t => f (c * t)) z = c * Dζ f (c * z) := by
  have hcz : c * z ≠ 0 := mul_ne_zero hc hz
  simp only [Dζ]
  rw [Φ_A_translate_fun f c, Φ_S_translate_fun f c]
  rw [show AFNum (fun w => Φ_A f (c * w)) z = AFNum (Φ_A f) (c * z)
      from AFNum_translate (Φ_A f) c z]
  rw [show SymNum (fun w => Φ_S f (c * w)) z = SymNum (Φ_S f) (c * z)
      from SymNum_translate (Φ_S f) c z]
  field_simp

/-- φ-gauge covariance: Dζ(f(φ·))(z) = φ · Dζ(f)(φz) -/
theorem Dζ_phi_covariance (f : ℂ → ℂ) (z : ℂ) (hz : z ≠ 0) :
    Dζ (fun t => f ((↑φ : ℂ) * t)) z =
    (↑φ : ℂ) * Dζ f ((↑φ : ℂ) * z) :=
  Dζ_gauge_covariance f _ z (ofReal_ne_zero.mpr (ne_of_gt phi_pos)) hz

/-- Iterated φ-scaling: Dζ(f(φⁿ·))(z) = φⁿ · Dζ(f)(φⁿz) -/
theorem Dζ_self_similar (f : ℂ → ℂ) (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    Dζ (fun t => f ((↑φ : ℂ) ^ n * t)) z =
    (↑φ : ℂ) ^ n * Dζ f ((↑φ : ℂ) ^ n * z) :=
  Dζ_gauge_covariance f _ z
    (pow_ne_zero n (ofReal_ne_zero.mpr (ne_of_gt phi_pos))) hz

/-- Observer scale independence: no internal measurement distinguishes absolute scale -/
theorem observer_scale_independence (f : ℂ → ℂ) (n : ℤ)
    (z : ℂ) (hz : z ≠ 0) :
    Dζ (fun t => f ((↑φ : ℂ) ^ n * t)) z =
    (↑φ : ℂ) ^ n * Dζ f ((↑φ : ℂ) ^ n * z) :=
  Dζ_gauge_covariance f _ z
    (zpow_ne_zero n (ofReal_ne_zero.mpr (ne_of_gt phi_pos))) hz

end GaugeCovariance

/-! ## Channel Decomposition Theorem

Dζ decomposes into AF (antisymmetric) and SY (symmetric) channels:
  Dζ = (AFNum(Φ_A) + SymNum(Φ_S)) / z
where Φ_A = Diff6 + Diff2 - Diff4 and Φ_S = 2Diff5 + Diff3 + μDiff2 with μ = 2/(φ+2).

The AF channel carries Diff6, Diff4, Diff2 (odd-rank)
and the SY channel carries Diff5, Diff3 (even-rank). -/

section ChannelDecomposition

/-- AF channel linearity: AFNum distributes over Φ_A = Diff6 + Diff2 - Diff4 -/
theorem AFNum_Φ_A_decompose (f : ℂ → ℂ) (z : ℂ) :
    AFNum (Φ_A f) z = AFNum (Diff6 f) z + AFNum (Diff2 f) z - AFNum (Diff4 f) z := by
  conv_lhs => rw [show Φ_A f = fun w =>
    Diff6 f w + Diff2 f w - Diff4 f w from funext (Φ_A_decompose f)]
  simp only [AFNum]; ring

/-- SY channel linearity: SymNum distributes over Φ_S = 2Diff5 + Diff3 + μDiff2 -/
theorem SymNum_Φ_S_decompose (f : ℂ → ℂ) (z : ℂ) :
    SymNum (Φ_S f) z =
    2 * SymNum (Diff5 f) z + SymNum (Diff3 f) z +
    (2 / ((↑φ : ℂ) + 2)) * SymNum (Diff2 f) z := by
  conv_lhs =>
    rw [show Φ_S f = fun w => 2 * Diff5 f w + Diff3 f w + (2 / ((↑φ : ℂ) + 2)) * Diff2 f w
        from funext (fun w => by simp only [Φ_S])]
  simp only [SymNum]; ring

/-- Dζ channel decomposition: Dζ splits into Diff_n components via Φ_A and Φ_S -/
theorem Dζ_channel_decompose (f : ℂ → ℂ) (z : ℂ) :
    Dζ f z =
    (AFNum (fun w => Diff6 f w + Diff2 f w - Diff4 f w) z +
     SymNum (fun w => 2 * Diff5 f w + Diff3 f w + (2 / ((↑φ : ℂ) + 2)) * Diff2 f w) z) / z := by
  simp only [Dζ, show Φ_A f = fun w => Diff6 f w + Diff2 f w - Diff4 f w
    from funext (Φ_A_decompose f), show Φ_S f = fun w => 2 * Diff5 f w + Diff3 f w +
    (2 / ((↑φ : ℂ) + 2)) * Diff2 f w from funext (fun w => by simp only [Φ_S])]

/-- AF channel of Dζ: carries Diff6, Diff2, Diff4 (odd-rank operators) -/
theorem Dζ_AF_channel (f : ℂ → ℂ) (z : ℂ) :
    AFNum (Φ_A f) z / z =
    (AFNum (Diff6 f) z + AFNum (Diff2 f) z - AFNum (Diff4 f) z) / z := by
  rw [AFNum_Φ_A_decompose]

/-- SY channel of Dζ: carries Diff5, Diff3, Diff2 (even-rank operators) -/
theorem Dζ_SY_channel (f : ℂ → ℂ) (z : ℂ) :
    SymNum (Φ_S f) z / z =
    (2 * SymNum (Diff5 f) z + SymNum (Diff3 f) z +
     (2 / ((↑φ : ℂ) + 2)) * SymNum (Diff2 f) z) / z := by
  rw [SymNum_Φ_S_decompose]

end ChannelDecomposition

end FUST.DζOperator
