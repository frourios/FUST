import FUST.Physics.LeastAction

/-!
# FUST Wave Equation

Derives the wave equation from FUST Least Action Theorem via Euler-Lagrange.

## Logical Chain

1. **Lagrangian**: L[f](x) = ‖D6 f(x)‖² (from LeastAction.lean)
2. **Action**: A[f] = ∫ ‖D6 f‖² dx/x
3. **Variation**: δA = 0 ⟹ ∫ D6 f · D6 η dx/x = 0 for all η
-/

namespace FUST.WaveEquation

open FUST.LeastAction Complex

/-! ## Part 1: D6 Linearity -/

/-- D6 coefficient pattern sum is zero -/
theorem D6_coeff_sum_zero : (1 : ℝ) + (-3) + 1 + (-1) + 3 + (-1) = 0 := by norm_num

/-- D6 is linear -/
theorem D6_linear_combination (f g : ℂ → ℂ) (a b : ℂ) (x : ℂ) :
    D6 (fun t => a * f t + b * g t) x = a * D6 f x + b * D6 g x := by
  simp only [D6, N6]
  ring

/-- D6 is homogeneous -/
theorem D6_homogeneous (f : ℂ → ℂ) (c x : ℂ) :
    D6 (fun t => c * f t) x = c * D6 f x := by
  have h := D6_linear_combination f (fun _ => 0) c 0 x
  simp only [mul_zero, add_zero, zero_mul] at h
  exact h

/-! ## Part 2: First Variation of Action -/

/-- First variation structure -/
theorem action_variation_structure (f η : ℂ → ℂ) (x : ℂ) :
    D6 (fun t => f t + η t) x = D6 f x + D6 η x := by
  have h := D6_linear_combination f η 1 1 x
  simp only [one_mul] at h
  exact h

/-- Lagrangian expansion for perturbation (normSq version) -/
theorem lagrangian_perturbation (f η : ℂ → ℂ) (ε : ℂ) (x : ℂ) :
    D6Lagrangian (fun t => f t + ε * η t) x =
    normSq (D6 f x) + 2 * (ε * D6 η x * starRingEnd ℂ (D6 f x)).re +
    normSq ε * normSq (D6 η x) := by
  simp only [D6Lagrangian]
  have hlin : D6 (fun t => f t + ε * η t) x = D6 f x + ε * D6 η x := by
    have h := D6_linear_combination f η 1 ε x
    simp only [one_mul] at h
    convert h using 2
  rw [hlin]
  simp only [normSq_add, normSq_mul]
  have : (D6 f x * (starRingEnd ℂ) (ε * D6 η x)).re =
      (ε * D6 η x * (starRingEnd ℂ) (D6 f x)).re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  linarith

/-- Critical point condition -/
theorem critical_point_condition (f : ℂ → ℂ) (x : ℂ) (hx : x ≠ 0) :
    (∀ η : ℂ → ℂ, D6 f x * D6 η x = 0) → D6 f x = 0 := by
  intro h
  have h_cubic := h (fun t => t^3)
  have hD6_cubic_ne : D6 (fun t => t^3) x ≠ 0 := D6_detects_cubic x hx
  exact (mul_eq_zero.mp h_cubic).resolve_right hD6_cubic_ne

end FUST.WaveEquation
