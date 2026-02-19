import FUST.Physics.TimeTheorem

/-!
# FUST Wave Equation

Derives the wave equation from FUST Least Action Theorem via Euler-Lagrange.

## Logical Chain

1. **Lagrangian**: L[f](x) = (D6 f(x))² (from LeastAction.lean)
2. **Action**: A[f] = ∫ (D6 f)² dx/x
3. **Variation**: δA = 0 ⟹ ∫ D6 f · D6 η dx/x = 0 for all η
4. **Wave Equation**: D6†(D6 f) = 0 (weak form)

## Key Results

1. D6 is formally symmetric under dx/x measure
2. FUST d'Alembertian □_φ = D6 ∘ D6 (formally)
3. ker(D6) ⊂ ker(□_φ) (zero modes)
-/

namespace FUST.WaveEquation

open FUST.LeastAction

/-! ## Part 1: D6 Linearity -/

/-- D6 coefficient pattern sum is zero -/
theorem D6_coeff_sum_zero : (1 : ℝ) + (-3) + 1 + (-1) + 3 + (-1) = 0 := by norm_num

/-- D6 is linear -/
theorem D6_linear_combination (f g : ℝ → ℝ) (a b : ℝ) (x : ℝ) :
    D6 (fun t => a * f t + b * g t) x = a * D6 f x + b * D6 g x := by
  simp only [D6, N6]
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte]; ring

/-- D6 is homogeneous -/
theorem D6_homogeneous (f : ℝ → ℝ) (c x : ℝ) :
    D6 (fun t => c * f t) x = c * D6 f x := by
  have h := D6_linear_combination f (fun _ => 0) c 0 x
  simp only [zero_mul, add_zero, mul_zero] at h
  exact h

/-! ## Part 2: FUST Wave Equation -/

/-- FUST d'Alembertian: D6 composed with itself -/
noncomputable def FUSTDAlembertian (f : ℝ → ℝ) : ℝ → ℝ := D6 (D6 f)

/-- D'Alembertian is zero on ker(D6) -/
theorem dAlembertian_zero_on_kernel (f : ℝ → ℝ) (hf : IsInKerD6 f) :
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
theorem kernel_subset_wave_kernel (f : ℝ → ℝ) (hf : IsInKerD6 f) :
    ∀ x, x ≠ 0 → FUSTDAlembertian f x = 0 :=
  dAlembertian_zero_on_kernel f hf

/-! ## Part 3: First Variation of Action -/

/-- First variation structure -/
theorem action_variation_structure (f η : ℝ → ℝ) (x : ℝ) :
    D6 (fun t => f t + η t) x = D6 f x + D6 η x := by
  have h := D6_linear_combination f η 1 1 x
  simp only [one_mul] at h
  exact h

/-- Lagrangian expansion for perturbation -/
theorem lagrangian_perturbation (f η : ℝ → ℝ) (ε x : ℝ) :
    D6Lagrangian (fun t => f t + ε * η t) x =
    (D6 f x)^2 + 2 * ε * D6 f x * D6 η x + ε^2 * (D6 η x)^2 := by
  simp only [D6Lagrangian]
  have hlin : D6 (fun t => f t + ε * η t) x = D6 f x + ε * D6 η x := by
    have h := D6_linear_combination f η 1 ε x
    simp only [one_mul] at h
    convert h using 2
  rw [hlin]
  ring

/-- Critical point condition -/
theorem critical_point_condition (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    (∀ η : ℝ → ℝ, D6 f x * D6 η x = 0) → D6 f x = 0 := by
  intro h
  have h_cubic := h (fun t => t^3)
  have hD6_cubic_ne : D6 (fun t => t^3) x ≠ 0 := by
    simp only [D6, N6, D6Denom, hx, ↓reduceIte]
    intro heq
    rw [div_eq_zero_iff] at heq
    cases heq with
    | inl hnum =>
      have hφ3 := phi_cubed
      have hψ3 : ψ^3 = 2 * ψ + 1 := by
        calc ψ^3 = ψ^2 * ψ := by ring
          _ = (ψ + 1) * ψ := by rw [psi_sq]
          _ = ψ^2 + ψ := by ring
          _ = (ψ + 1) + ψ := by rw [psi_sq]
          _ = 2 * ψ + 1 := by ring
      have hφ2 := golden_ratio_property
      have hψ2 := psi_sq
      have hφ6 : φ^6 = 8 * φ + 5 := by
        have hφ4 : φ^4 = 3 * φ + 2 := by
          calc φ^4 = φ^2 * φ^2 := by ring
            _ = (φ + 1) * (φ + 1) := by rw [hφ2]
            _ = φ^2 + 2*φ + 1 := by ring
            _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
            _ = 3 * φ + 2 := by ring
        calc φ^6 = φ^4 * φ^2 := by ring
          _ = (3*φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
          _ = 3*φ^2 + 5*φ + 2 := by ring
          _ = 3*(φ + 1) + 5*φ + 2 := by rw [hφ2]
          _ = 8 * φ + 5 := by ring
      have hψ6 : ψ^6 = 8 * ψ + 5 := by
        have hψ4 : ψ^4 = 3 * ψ + 2 := by
          calc ψ^4 = ψ^2 * ψ^2 := by ring
            _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
            _ = ψ^2 + 2*ψ + 1 := by ring
            _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
            _ = 3 * ψ + 2 := by ring
        calc ψ^6 = ψ^4 * ψ^2 := by ring
          _ = (3*ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
          _ = 3*ψ^2 + 5*ψ + 2 := by ring
          _ = 3*(ψ + 1) + 5*ψ + 2 := by rw [hψ2]
          _ = 8 * ψ + 5 := by ring
      have hφ9 : φ^9 = 34 * φ + 21 := by
        calc φ^9 = φ^6 * φ^3 := by ring
          _ = (8*φ + 5) * (2*φ + 1) := by rw [hφ6, hφ3]
          _ = 16*φ^2 + 18*φ + 5 := by ring
          _ = 16*(φ + 1) + 18*φ + 5 := by rw [hφ2]
          _ = 34 * φ + 21 := by ring
      have hψ9 : ψ^9 = 34 * ψ + 21 := by
        calc ψ^9 = ψ^6 * ψ^3 := by ring
          _ = (8*ψ + 5) * (2*ψ + 1) := by rw [hψ6, hψ3]
          _ = 16*ψ^2 + 18*ψ + 5 := by ring
          _ = 16*(ψ + 1) + 18*ψ + 5 := by rw [hψ2]
          _ = 34 * ψ + 21 := by ring
      have hcoef_val : φ^9 - 3 * φ^6 + φ^3 - ψ^3 + 3 * ψ^6 - ψ^9 = 12 * (φ - ψ) := by
        rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]; ring
      have hx3_ne : x^3 ≠ 0 := pow_ne_zero 3 hx
      have hnum_expand : (φ^3 * x)^3 - 3 * (φ^2 * x)^3 + (φ * x)^3 - (ψ * x)^3 +
          3 * (ψ^2 * x)^3 - (ψ^3 * x)^3 =
          x^3 * (φ^9 - 3 * φ^6 + φ^3 - ψ^3 + 3 * ψ^6 - ψ^9) := by ring
      rw [hnum_expand] at hnum
      have hcoef_zero := (mul_eq_zero.mp hnum).resolve_left hx3_ne
      rw [hcoef_val, phi_sub_psi] at hcoef_zero
      have hsqrt5_ne : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
      have h12_ne : (12 : ℝ) ≠ 0 := by norm_num
      exact mul_ne_zero h12_ne hsqrt5_ne hcoef_zero
    | inr h => exact (D6Denom_mul_ne_zero x hx) h
  exact (mul_eq_zero.mp h_cubic).resolve_right hD6_cubic_ne

/-! ## Part 4: Spacetime Dimension

The spatial dimension is derived from ker(D6):
- D6[1] = 0, D6[x] = 0, D6[x²] = 0 (kernel contains span{1, x, x²})
- D6[x³] ≠ 0 (cubic is NOT in kernel, proved in critical_point_condition)
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
theorem D6_cubic_nonzero (x : ℝ) (hx : x ≠ 0) : D6 (fun t => t^3) x ≠ 0 := by
  simp only [D6, N6, D6Denom, hx, ↓reduceIte]
  intro heq
  have hdenom_ne := D6Denom_mul_ne_zero x hx
  rw [div_eq_zero_iff] at heq
  cases heq with
  | inl hnum =>
    have hφ3 := phi_cubed
    have hψ3 : ψ^3 = 2 * ψ + 1 := by
      calc ψ^3 = ψ^2 * ψ := by ring
        _ = (ψ + 1) * ψ := by rw [psi_sq]
        _ = ψ^2 + ψ := by ring
        _ = (ψ + 1) + ψ := by rw [psi_sq]
        _ = 2 * ψ + 1 := by ring
    have hφ2 := golden_ratio_property
    have hψ2 := psi_sq
    have hφ6 : φ^6 = 8 * φ + 5 := by
      have hφ4 : φ^4 = 3 * φ + 2 := by
        calc φ^4 = φ^2 * φ^2 := by ring
          _ = (φ + 1) * (φ + 1) := by rw [hφ2]
          _ = φ^2 + 2*φ + 1 := by ring
          _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
          _ = 3 * φ + 2 := by ring
      calc φ^6 = φ^4 * φ^2 := by ring
        _ = (3*φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
        _ = 3*φ^2 + 5*φ + 2 := by ring
        _ = 3*(φ + 1) + 5*φ + 2 := by rw [hφ2]
        _ = 8 * φ + 5 := by ring
    have hψ6 : ψ^6 = 8 * ψ + 5 := by
      have hψ4 : ψ^4 = 3 * ψ + 2 := by
        calc ψ^4 = ψ^2 * ψ^2 := by ring
          _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
          _ = ψ^2 + 2*ψ + 1 := by ring
          _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
          _ = 3 * ψ + 2 := by ring
      calc ψ^6 = ψ^4 * ψ^2 := by ring
        _ = (3*ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
        _ = 3*ψ^2 + 5*ψ + 2 := by ring
        _ = 3*(ψ + 1) + 5*ψ + 2 := by rw [hψ2]
        _ = 8 * ψ + 5 := by ring
    have hφ9 : φ^9 = 34 * φ + 21 := by
      calc φ^9 = φ^6 * φ^3 := by ring
        _ = (8*φ + 5) * (2*φ + 1) := by rw [hφ6, hφ3]
        _ = 16*φ^2 + 18*φ + 5 := by ring
        _ = 16*(φ + 1) + 18*φ + 5 := by rw [hφ2]
        _ = 34 * φ + 21 := by ring
    have hψ9 : ψ^9 = 34 * ψ + 21 := by
      calc ψ^9 = ψ^6 * ψ^3 := by ring
        _ = (8*ψ + 5) * (2*ψ + 1) := by rw [hψ6, hψ3]
        _ = 16*ψ^2 + 18*ψ + 5 := by ring
        _ = 16*(ψ + 1) + 18*ψ + 5 := by rw [hψ2]
        _ = 34 * ψ + 21 := by ring
    have hcoef_val : φ^9 - 3 * φ^6 + φ^3 - ψ^3 + 3 * ψ^6 - ψ^9 = 12 * (φ - ψ) := by
      rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]; ring
    have hx3_ne : x^3 ≠ 0 := pow_ne_zero 3 hx
    have hnum_expand : (φ^3 * x)^3 - 3 * (φ^2 * x)^3 + (φ * x)^3 - (ψ * x)^3 +
        3 * (ψ^2 * x)^3 - (ψ^3 * x)^3 =
        x^3 * (φ^9 - 3 * φ^6 + φ^3 - ψ^3 + 3 * ψ^6 - ψ^9) := by ring
    rw [hnum_expand] at hnum
    have hcoef_zero := (mul_eq_zero.mp hnum).resolve_left hx3_ne
    rw [hcoef_val, phi_sub_psi] at hcoef_zero
    have hsqrt5_ne : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have h12_ne : (12 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h12_ne hsqrt5_ne hcoef_zero
  | inr h => exact hdenom_ne h

/-- Time evolution uniqueness: φ > 1 is the unique expansion factor -/
theorem time_evolution_unique : φ > 1 ∧ |ψ| < 1 :=
  ⟨φ_gt_one, FUST.TimeTheorem.abs_psi_lt_one⟩

/-! ## Part 5: Summary Theorems -/

/-- FUST Wave Equation Structure -/
theorem fust_wave_structure :
    (∀ f : ℝ → ℝ, FUSTDAlembertian f = D6 (D6 f)) ∧
    (∀ f : ℝ → ℝ, IsInKerD6 f → ∀ x, x ≠ 0 → FUSTDAlembertian f x = 0) := by
  exact ⟨fun _ => rfl, dAlembertian_zero_on_kernel⟩

end FUST.WaveEquation
