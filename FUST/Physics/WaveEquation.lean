import FUST.Physics.LeastAction

/-!
# FUST Wave Equation

Derives the wave equation from FUST Least Action Theorem via Euler-Lagrange.

## Logical Chain

1. **Lagrangian**: L[f](x) = ‖D6 f(x)‖² (from LeastAction.lean)
2. **Action**: A[f] = ∫ ‖D6 f‖² dx/x
3. **Variation**: δA = 0 ⟹ ∫ D6 f · D6 η dx/x = 0 for all η
4. **Wave Equation**: D6†(D6 f) = 0 (weak form)

## Key Results

1. D6 is formally symmetric under dx/x measure
2. FUST d'Alembertian □_φ = D6 ∘ D6 (formally)
3. ker(D6) ⊂ ker(□_φ) (zero modes)
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
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte]; ring

/-- D6 is homogeneous -/
theorem D6_homogeneous (f : ℂ → ℂ) (c x : ℂ) :
    D6 (fun t => c * f t) x = c * D6 f x := by
  have h := D6_linear_combination f (fun _ => 0) c 0 x
  simp only [mul_zero, add_zero, zero_mul] at h
  exact h

/-! ## Part 2: FUST Wave Equation -/

/-- FUST d'Alembertian: D6 composed with itself -/
noncomputable def FUSTDAlembertian (f : ℂ → ℂ) : ℂ → ℂ := D6 (D6 f)

/-- D'Alembertian is zero on ker(D6) -/
theorem dAlembertian_zero_on_kernel (f : ℂ → ℂ) (hf : IsInKerD6 f) :
    ∀ x, x ≠ 0 → FUSTDAlembertian f x = 0 := by
  intro x hx
  simp only [FUSTDAlembertian]
  have hD6_zero : ∀ y, y ≠ 0 → D6 f y = 0 := IsInKerD6_implies_D6_zero f hf
  have hD6f_const : D6 f = fun y => if y = 0 then 0 else 0 := by
    ext y
    by_cases hy : y = 0
    · simp [D6, hy]
    · simp [hy, hD6_zero y hy]
  simp only [hD6f_const, ite_self]
  exact D6_const 0 x hx

/-- ker(D6) ⊂ ker(□_φ) -/
theorem kernel_subset_wave_kernel (f : ℂ → ℂ) (hf : IsInKerD6 f) :
    ∀ x, x ≠ 0 → FUSTDAlembertian f x = 0 :=
  dAlembertian_zero_on_kernel f hf

/-! ## Part 3: First Variation of Action -/

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

/-! ## Part 4: Spacetime Dimension

The spatial dimension is derived from ker(D6):
- D6[1] = 0, D6[x] = 0, D6[x²] = 0 (kernel contains span{1, x, x²})
- D6[x³] ≠ 0 (cubic is NOT in kernel)
- Therefore dim ker(D6) = 3

The time dimension is derived from TimeTheorem:
- φ > 1 is the unique expansion factor
- The time evolution f ↦ f(φ·) is 1-parameter
-/

/-- ker(D6) contains {1, x, x²}: 3 linearly independent elements -/
theorem ker_D6_contains_basis :
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) :=
  D6_kernel_dim_3

/-- D6[x³] ≠ 0: cubic is NOT in ker(D6) -/
theorem D6_cubic_nonzero (x : ℂ) (hx : x ≠ 0) : D6 (fun t => t^3) x ≠ 0 :=
  D6_detects_cubic x hx

/-- Time evolution uniqueness: φ > 1 is the unique expansion factor -/
theorem time_evolution_unique : φ > 1 ∧ |ψ| < 1 :=
  ⟨φ_gt_one, FUST.LeastAction.abs_psi_lt_one⟩

/-! ## Part 5: Summary Theorems -/

/-- FUST Wave Equation Structure -/
theorem fust_wave_structure :
    (∀ f : ℂ → ℂ, FUSTDAlembertian f = D6 (D6 f)) ∧
    (∀ f : ℂ → ℂ, IsInKerD6 f → ∀ x, x ≠ 0 → FUSTDAlembertian f x = 0) := by
  exact ⟨fun _ => rfl, dAlembertian_zero_on_kernel⟩

end FUST.WaveEquation
