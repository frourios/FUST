import FUST.DifferenceOperators
import FUST.DimensionalAnalysis
import FUST.Zeta6
import Mathlib.Tactic

/-!
# Least Action from Dζ Unified Operator

Dζ determines 4D spacetime (I4 = Fin 3 ⊕ Fin 1) via |Dζ|² = 12(3a² + b²).
D6 is the Dζ AF-channel projection at r=1.
The action |D6 f|² = 0 iff f ∈ ker(D6) = span{1,z,z²}: least action is a theorem.
Time evolution f(t) ↦ f(φt) is the Poincaré boost, with φ > 1 giving the arrow of time.
-/

namespace FUST.LeastAction

/-! ## D6 Kernel Structure -/

/-- D6 kernel is 3-dimensional: span{1, x, x²} -/
theorem D6_kernel_dim_3 :
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) :=
  ⟨fun x _hx => D6_const 1 x, fun x _hx => D6_linear x, fun x _hx => D6_quadratic x⟩

/-! ## Kernel Membership -/

/-- f ∈ ker(D6) iff f equals some degree-2 polynomial -/
def IsInKerD6 (f : ℂ → ℂ) : Prop :=
  ∃ a₀ a₁ a₂ : ℂ, ∀ t, f t = a₀ + a₁ * t + a₂ * t^2

/-- D6 applied to degree-2 polynomial is zero -/
theorem D6_polynomial_deg2 (a₀ a₁ a₂ : ℂ) (x : ℂ) :
    D6 (fun t => a₀ + a₁ * t + a₂ * t^2) x = 0 := by
  simp only [D6, N6, D6Denom]
  have hφ3 : (↑φ : ℂ)^3 = 2 * ↑φ + 1 := phi_cubed_complex
  have hψ3 : (↑ψ : ℂ)^3 = 2 * ↑ψ + 1 := psi_cubed_complex
  have hφ2 : (↑φ : ℂ)^2 = ↑φ + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ)^2 = ↑ψ + 1 := psi_sq_complex
  have hlin_coef : (↑φ : ℂ)^3 - 3*(↑φ)^2 + ↑φ - ↑ψ + 3*(↑ψ)^2 - (↑ψ)^3 = 0 := by
    rw [hφ3, hφ2, hψ2, hψ3]; ring
  have hquad_coef :
      ((↑φ : ℂ)^3)^2 - 3*((↑φ)^2)^2 + (↑φ)^2
        - (↑ψ)^2 + 3*((↑ψ)^2)^2 - ((↑ψ)^3)^2
        = 0 := by
    have hφ4 : (↑φ : ℂ)^4 = 3 * ↑φ + 2 := by calc (↑φ : ℂ)^4 = (↑φ)^2 * (↑φ)^2 := by ring
      _ = (↑φ + 1) * (↑φ + 1) := by rw [hφ2]
      _ = (↑φ)^2 + 2*(↑φ) + 1 := by ring
      _ = (↑φ + 1) + 2*(↑φ) + 1 := by rw [hφ2]
      _ = 3 * ↑φ + 2 := by ring
    have hψ4 : (↑ψ : ℂ)^4 = 3 * ↑ψ + 2 := by calc (↑ψ : ℂ)^4 = (↑ψ)^2 * (↑ψ)^2 := by ring
      _ = (↑ψ + 1) * (↑ψ + 1) := by rw [hψ2]
      _ = (↑ψ)^2 + 2*(↑ψ) + 1 := by ring
      _ = (↑ψ + 1) + 2*(↑ψ) + 1 := by rw [hψ2]
      _ = 3 * ↑ψ + 2 := by ring
    have hφ6 : (↑φ : ℂ)^6 = 8 * ↑φ + 5 := by calc (↑φ : ℂ)^6 = (↑φ)^4 * (↑φ)^2 := by ring
      _ = (3*(↑φ) + 2) * (↑φ + 1) := by rw [hφ4, hφ2]
      _ = 3*(↑φ)^2 + 5*(↑φ) + 2 := by ring
      _ = 3*(↑φ + 1) + 5*(↑φ) + 2 := by rw [hφ2]
      _ = 8 * ↑φ + 5 := by ring
    have hψ6 : (↑ψ : ℂ)^6 = 8 * ↑ψ + 5 := by calc (↑ψ : ℂ)^6 = (↑ψ)^4 * (↑ψ)^2 := by ring
      _ = (3*(↑ψ) + 2) * (↑ψ + 1) := by rw [hψ4, hψ2]
      _ = 3*(↑ψ)^2 + 5*(↑ψ) + 2 := by ring
      _ = 3*(↑ψ + 1) + 5*(↑ψ) + 2 := by rw [hψ2]
      _ = 8 * ↑ψ + 5 := by ring
    calc ((↑φ : ℂ)^3)^2 - 3*((↑φ)^2)^2 + (↑φ)^2 - (↑ψ)^2 + 3*((↑ψ)^2)^2 - ((↑ψ)^3)^2
      = (↑φ)^6 - 3*(↑φ)^4 + (↑φ)^2 - (↑ψ)^2 + 3*(↑ψ)^4 - (↑ψ)^6 := by ring
      _ = (8*(↑φ)+5) - 3*(3*(↑φ)+2) + (↑φ+1) - (↑ψ+1) + 3*(3*(↑ψ)+2) - (8*(↑ψ)+5) := by
          rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]
      _ = 0 := by ring
  rw [div_eq_zero_iff]
  left
  calc (a₀ + a₁ * ((↑φ)^3 * x) + a₂ * ((↑φ)^3 * x)^2) -
      3 * (a₀ + a₁ * ((↑φ)^2 * x) + a₂ * ((↑φ)^2 * x)^2) +
      (a₀ + a₁ * ((↑φ) * x) + a₂ * ((↑φ) * x)^2) -
      (a₀ + a₁ * ((↑ψ) * x) + a₂ * ((↑ψ) * x)^2) +
      3 * (a₀ + a₁ * ((↑ψ)^2 * x) + a₂ * ((↑ψ)^2 * x)^2) -
      (a₀ + a₁ * ((↑ψ)^3 * x) + a₂ * ((↑ψ)^3 * x)^2)
    = a₀ * (1 - 3 + 1 - 1 + 3 - 1) +
      a₁ * x * ((↑φ)^3 - 3*(↑φ)^2 + ↑φ
        - ↑ψ + 3*(↑ψ)^2 - (↑ψ)^3) +
      a₂ * x^2 * (((↑φ)^3)^2 - 3*((↑φ)^2)^2
        + (↑φ)^2 - (↑ψ)^2 + 3*((↑ψ)^2)^2
        - ((↑ψ)^3)^2) := by ring
    _ = a₀ * 0 + a₁ * x * 0 + a₂ * x^2 * 0 := by rw [hlin_coef, hquad_coef]; ring
    _ = 0 := by ring

/-- If f ∈ ker(D6), then D6 f = 0 for all x ≠ 0 -/
theorem IsInKerD6_implies_D6_zero (f : ℂ → ℂ) (hf : IsInKerD6 f) :
    ∀ x, x ≠ 0 → D6 f x = 0 := by
  intro x hx
  obtain ⟨a₀, a₁, a₂, hf_eq⟩ := hf
  have hf' : f = fun t => a₀ + a₁ * t + a₂ * t^2 := funext hf_eq
  rw [hf']
  exact D6_polynomial_deg2 a₀ a₁ a₂ x

/-! ## Kernel Projection -/

section KernelProjection

/-- D6 kernel projection using interpolation at {0, 1, -1} -/
noncomputable def kernelProjectionD6 (f : ℂ → ℂ) : ℂ → ℂ :=
  let a₀ := f 0
  let a₁ := (f 1 - f (-1)) / 2
  let a₂ := (f 1 + f (-1) - 2 * f 0) / 2
  fun t => a₀ + a₁ * t + a₂ * t^2

/-- D6 uniqueness theorem for degree-2 interpolation -/
theorem kernel_interpolation_unique_D6 (p q : ℂ → ℂ) (hp : IsInKerD6 p) (hq : IsInKerD6 q)
    (t₀ t₁ t₂ : ℂ) (h01 : t₀ ≠ t₁) (h02 : t₀ ≠ t₂) (h12 : t₁ ≠ t₂)
    (hp0 : p t₀ = q t₀) (hp1 : p t₁ = q t₁) (hp2 : p t₂ = q t₂) :
    ∀ t, p t = q t := by
  obtain ⟨a₀, a₁, a₂, hp_eq⟩ := hp
  obtain ⟨b₀, b₁, b₂, hq_eq⟩ := hq
  intro t
  have h0 : a₀ + a₁ * t₀ + a₂ * t₀^2 = b₀ + b₁ * t₀ + b₂ * t₀^2 := by
    rw [← hp_eq t₀, ← hq_eq t₀]; exact hp0
  have h1 : a₀ + a₁ * t₁ + a₂ * t₁^2 = b₀ + b₁ * t₁ + b₂ * t₁^2 := by
    rw [← hp_eq t₁, ← hq_eq t₁]; exact hp1
  have h2 : a₀ + a₁ * t₂ + a₂ * t₂^2 = b₀ + b₁ * t₂ + b₂ * t₂^2 := by
    rw [← hp_eq t₂, ← hq_eq t₂]; exact hp2
  let c₀ := a₀ - b₀
  let c₁ := a₁ - b₁
  let c₂ := a₂ - b₂
  have hc0 : c₀ + c₁ * t₀ + c₂ * t₀^2 = 0 := by
    simp only [c₀, c₁, c₂]; calc (a₀ - b₀) + (a₁ - b₁) * t₀ + (a₂ - b₂) * t₀^2
      = (a₀ + a₁ * t₀ + a₂ * t₀^2) - (b₀ + b₁ * t₀ + b₂ * t₀^2) := by ring
      _ = 0 := by rw [h0]; ring
  have hc1 : c₀ + c₁ * t₁ + c₂ * t₁^2 = 0 := by
    simp only [c₀, c₁, c₂]; calc (a₀ - b₀) + (a₁ - b₁) * t₁ + (a₂ - b₂) * t₁^2
      = (a₀ + a₁ * t₁ + a₂ * t₁^2) - (b₀ + b₁ * t₁ + b₂ * t₁^2) := by ring
      _ = 0 := by rw [h1]; ring
  have hc2 : c₀ + c₁ * t₂ + c₂ * t₂^2 = 0 := by
    simp only [c₀, c₁, c₂]; calc (a₀ - b₀) + (a₁ - b₁) * t₂ + (a₂ - b₂) * t₂^2
      = (a₀ + a₁ * t₂ + a₂ * t₂^2) - (b₀ + b₁ * t₂ + b₂ * t₂^2) := by ring
      _ = 0 := by rw [h2]; ring
  have hc2_zero : c₂ = 0 := by
    by_contra hne
    have hdiff1 : c₁ * (t₁ - t₀) + c₂ * (t₁^2 - t₀^2) = 0 := by
      linear_combination hc1 - hc0
    have hdiff2 : c₁ * (t₂ - t₀) + c₂ * (t₂^2 - t₀^2) = 0 := by
      linear_combination hc2 - hc0
    have hfac1 : (t₁ - t₀) * (c₁ + c₂ * (t₁ + t₀)) = 0 := by
      calc (t₁ - t₀) * (c₁ + c₂ * (t₁ + t₀))
        = c₁ * (t₁ - t₀) + c₂ * (t₁ + t₀) * (t₁ - t₀) := by ring
        _ = c₁ * (t₁ - t₀) + c₂ * (t₁^2 - t₀^2) := by ring
        _ = 0 := hdiff1
    have hfac2 : (t₂ - t₀) * (c₁ + c₂ * (t₂ + t₀)) = 0 := by
      calc (t₂ - t₀) * (c₁ + c₂ * (t₂ + t₀))
        = c₁ * (t₂ - t₀) + c₂ * (t₂ + t₀) * (t₂ - t₀) := by ring
        _ = c₁ * (t₂ - t₀) + c₂ * (t₂^2 - t₀^2) := by ring
        _ = 0 := hdiff2
    have ht01 : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
    have ht02 : t₂ - t₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h02)
    have heq1 : c₁ + c₂ * (t₁ + t₀) = 0 := by
      have := mul_eq_zero.mp hfac1
      cases this with
      | inl h => exact absurd h ht01
      | inr h => exact h
    have heq2 : c₁ + c₂ * (t₂ + t₀) = 0 := by
      have := mul_eq_zero.mp hfac2
      cases this with
      | inl h => exact absurd h ht02
      | inr h => exact h
    have hdiff3 : c₂ * (t₁ - t₂) = 0 := by
      calc c₂ * (t₁ - t₂) = (c₁ + c₂ * (t₁ + t₀)) - (c₁ + c₂ * (t₂ + t₀)) := by ring
        _ = 0 - 0 := by rw [heq1, heq2]
        _ = 0 := by ring
    have ht12 : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h12
    have hc2' : c₂ = 0 := by
      have := mul_eq_zero.mp hdiff3
      cases this with
      | inl h => exact h
      | inr h => exact absurd h ht12
    exact hne hc2'
  have hc1_zero : c₁ = 0 := by
    have hdiff : c₁ * (t₁ - t₀) = 0 := by
      have h := hc2_zero
      linear_combination hc1 - hc0 - (t₁ + t₀) * (t₁ - t₀) * h
    have ht01' : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
    have := mul_eq_zero.mp hdiff
    cases this with
    | inl h => exact h
    | inr h => exact absurd h ht01'
  have hc0_zero : c₀ = 0 := by
    calc c₀ = c₀ + c₁ * t₀ + c₂ * t₀^2 := by rw [hc1_zero, hc2_zero]; ring
      _ = 0 := hc0
  rw [hp_eq, hq_eq]
  have ha0 : a₀ = b₀ := by simp only [c₀] at hc0_zero; exact sub_eq_zero.mp hc0_zero
  have ha1 : a₁ = b₁ := by simp only [c₁] at hc1_zero; exact sub_eq_zero.mp hc1_zero
  have ha2 : a₂ = b₂ := by simp only [c₂] at hc2_zero; exact sub_eq_zero.mp hc2_zero
  rw [ha0, ha1, ha2]

theorem kernelProjectionD6_annihilated (f : ℂ → ℂ) (x : ℂ) :
    D6 (kernelProjectionD6 f) x = 0 := by
  simp only [kernelProjectionD6]
  exact D6_polynomial_deg2 _ _ _ x

theorem kernelProjectionD6_is_in_ker (f : ℂ → ℂ) : IsInKerD6 (kernelProjectionD6 f) := by
  use f 0, (f 1 - f (-1)) / 2, (f 1 + f (-1) - 2 * f 0) / 2
  intro t
  simp only [kernelProjectionD6]

theorem kernelProjectionD6_interpolates (f : ℂ → ℂ) :
    kernelProjectionD6 f 0 = f 0 ∧
    kernelProjectionD6 f 1 = f 1 ∧
    kernelProjectionD6 f (-1) = f (-1) := by
  simp only [kernelProjectionD6]
  constructor
  · ring
  constructor
  · ring
  · ring

end KernelProjection

/-! ## Perpendicular Projection -/

/-- D6 perpendicular projection: deviation from ker(D6) -/
noncomputable def perpProjectionD6 (f : ℂ → ℂ) : ℂ → ℂ :=
  fun t => f t - kernelProjectionD6 f t

theorem perpProjectionD6_D6_eq (f : ℂ → ℂ) (x : ℂ) (hx : x ≠ 0) :
    D6 (perpProjectionD6 f) x = D6 f x := by
  have hker := kernelProjectionD6_annihilated f x
  rw [D6_eq_N6_div _ x, D6_eq_N6_div f x]
  congr 1
  rw [D6_eq_N6_div _ x] at hker
  have hdenom_ne : D6Denom * x ≠ 0 := D6Denom_mul_ne_zero x hx
  have hnum_zero : N6 (kernelProjectionD6 f) x = 0 := by
    exact (div_eq_zero_iff.mp hker).resolve_right hdenom_ne
  have : N6 (perpProjectionD6 f) x =
    N6 f x - N6 (kernelProjectionD6 f) x := by
    simp only [N6, perpProjectionD6]; ring
  rw [this, hnum_zero, sub_zero]

/-- If f ∈ ker(D6), then perpProjectionD6 is zero everywhere -/
theorem kerD6_implies_perp_zero (f : ℂ → ℂ) (hf : IsInKerD6 f) :
    ∀ t, perpProjectionD6 f t = 0 := by
  obtain ⟨a₀, a₁, a₂, hf_eq⟩ := hf
  intro t
  simp only [perpProjectionD6, kernelProjectionD6, hf_eq]
  ring

theorem perpD6_zero_implies_ker (f : ℂ → ℂ) (h : ∀ t, perpProjectionD6 f t = 0) :
    IsInKerD6 f := by
  use f 0, (f 1 - f (-1)) / 2, (f 1 + f (-1) - 2 * f 0) / 2
  intro t
  have ht := h t
  simp only [perpProjectionD6, kernelProjectionD6] at ht
  exact sub_eq_zero.mp ht

/-! ## Arrow of Time from φ/ψ Asymmetry

φ > 1 causes scale expansion (future), |ψ| < 1 causes decay (past).
This asymmetry is intrinsic to the golden ratio within Dζ. -/

/-- |ψ| < 1 -/
theorem abs_psi_lt_one : |ψ| < 1 := by
  have h : ψ = (1 - Real.sqrt 5) / 2 := rfl
  have hsqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have hsqrt5_gt_1 : Real.sqrt 5 > 1 := by
    have h1 : (1 : ℝ) < 5 := by norm_num
    calc Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) h1
      _ = 1 := Real.sqrt_one
  have hpsi_neg : ψ < 0 := by
    simp only [h]
    have : 1 - Real.sqrt 5 < 0 := by linarith
    linarith
  have hpsi_gt_neg1 : ψ > -1 := by
    simp only [h]
    have hsqrt5_lt_3 : Real.sqrt 5 < 3 := by
      have h9 : (5 : ℝ) < 9 := by norm_num
      have h3 : Real.sqrt 9 = 3 := by norm_num
      calc Real.sqrt 5 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) h9
        _ = 3 := h3
    linarith
  rw [abs_of_neg hpsi_neg]
  linarith

/-- φ · |ψ| = 1 -/
theorem phi_mul_abs_psi : φ * |ψ| = 1 := by
  have hpsi_neg : ψ < 0 := by
    have h : ψ = (1 - Real.sqrt 5) / 2 := rfl
    have hsqrt5_gt_1 : Real.sqrt 5 > 1 := by
      calc Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5)
        _ = 1 := Real.sqrt_one
    simp only [h]
    linarith
  rw [abs_of_neg hpsi_neg]
  have h : φ * (-ψ) = -(φ * ψ) := by ring
  rw [h, phi_mul_psi]
  ring

/-- φⁿ > 1 for n ≥ 1 -/
theorem phi_pow_gt_one (n : ℕ) (hn : n ≥ 1) : φ^n > 1 := by
  exact one_lt_pow₀ φ_gt_one (Nat.one_le_iff_ne_zero.mp hn)

/-! ## Lagrangian -/

section Lagrangian

noncomputable def D6Lagrangian (f : ℂ → ℂ) (x : ℂ) : ℝ := Complex.normSq (D6 f x)

theorem D6_lagrangian_nonneg (f : ℂ → ℂ) (x : ℂ) : D6Lagrangian f x ≥ 0 := Complex.normSq_nonneg _

theorem D6_lagrangian_zero_iff (f : ℂ → ℂ) (x : ℂ) :
    D6Lagrangian f x = 0 ↔ D6 f x = 0 := Complex.normSq_eq_zero

theorem D6_lagrangian_ker_zero (f : ℂ → ℂ) (hf : IsInKerD6 f) (x : ℂ) (hx : x ≠ 0) :
    D6Lagrangian f x = 0 := by
  rw [D6_lagrangian_zero_iff]; exact IsInKerD6_implies_D6_zero f hf x hx

end Lagrangian

/-! ## Time Existence -/

/-- D6 f ≠ 0 at some gauge implies time exists -/
theorem D6_nonzero_implies_time (f : ℂ → ℂ) (x : ℂ) (hx : x ≠ 0) (hD6 : D6 f x ≠ 0) :
    ¬ IsInKerD6 f := by
  intro hker
  exact hD6 (IsInKerD6_implies_D6_zero f hker x hx)

theorem timeExists_iff_nonzero_perpD6 (f : ℂ → ℂ) :
    ¬ IsInKerD6 f ↔ ∃ t, perpProjectionD6 f t ≠ 0 := by
  constructor
  · intro hf
    by_contra h
    push_neg at h
    exact hf (perpD6_zero_implies_ker f h)
  · intro ⟨t, ht⟩ hker
    exact ht (kerD6_implies_perp_zero f hker t)

theorem timeExists_has_proper_timeD6 (f : ℂ → ℂ) (hf : ¬ IsInKerD6 f) :
    ∃ t, perpProjectionD6 f t ≠ 0 :=
  (timeExists_iff_nonzero_perpD6 f).mp hf

/-- For cubic polynomials, D6 = 0 everywhere implies a₃ = 0 -/
theorem D6_zero_implies_ker_poly (a₀ a₁ a₂ a₃ : ℂ)
    (h : ∀ x, x ≠ 0 → D6 (fun t => a₀ + a₁ * t + a₂ * t ^ 2 + a₃ * t ^ 3) x = 0) :
    a₃ = 0 := by
  have h1 := h 1 one_ne_zero
  simp only [D6, N6, mul_one] at h1
  have hdenom_ne : D6Denom ≠ 0 := D6Denom_ne_zero
  have hnum := (div_eq_zero_iff.mp h1).resolve_right hdenom_ne
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ3 : (↑φ : ℂ) ^ 3 = 2 * (↑φ : ℂ) + 1 := phi_cubed_complex
  have hψ3 : (↑ψ : ℂ) ^ 3 = 2 * (↑ψ : ℂ) + 1 := by
    calc (↑ψ : ℂ) ^ 3 = (↑ψ : ℂ) ^ 2 * (↑ψ : ℂ) := by ring
      _ = ((↑ψ : ℂ) + 1) * (↑ψ : ℂ) := by rw [hψ2]
      _ = (↑ψ : ℂ) ^ 2 + (↑ψ : ℂ) := by ring
      _ = ((↑ψ : ℂ) + 1) + (↑ψ : ℂ) := by rw [hψ2]
      _ = 2 * (↑ψ : ℂ) + 1 := by ring
  have hφ6 : (↑φ : ℂ) ^ 6 = 8 * (↑φ : ℂ) + 5 := by
    calc (↑φ : ℂ) ^ 6 = ((↑φ : ℂ) ^ 3) ^ 2 := by ring
      _ = (2 * (↑φ : ℂ) + 1) ^ 2 := by rw [hφ3]
      _ = 4 * (↑φ : ℂ) ^ 2 + 4 * (↑φ : ℂ) + 1 := by ring
      _ = 4 * ((↑φ : ℂ) + 1) + 4 * (↑φ : ℂ) + 1 := by rw [hφ2]
      _ = 8 * (↑φ : ℂ) + 5 := by ring
  have hψ6 : (↑ψ : ℂ) ^ 6 = 8 * (↑ψ : ℂ) + 5 := by
    calc (↑ψ : ℂ) ^ 6 = ((↑ψ : ℂ) ^ 3) ^ 2 := by ring
      _ = (2 * (↑ψ : ℂ) + 1) ^ 2 := by rw [hψ3]
      _ = 4 * (↑ψ : ℂ) ^ 2 + 4 * (↑ψ : ℂ) + 1 := by ring
      _ = 4 * ((↑ψ : ℂ) + 1) + 4 * (↑ψ : ℂ) + 1 := by rw [hψ2]
      _ = 8 * (↑ψ : ℂ) + 5 := by ring
  have hφ9 : (↑φ : ℂ) ^ 9 = 34 * (↑φ : ℂ) + 21 := by
    calc (↑φ : ℂ) ^ 9 = (↑φ : ℂ) ^ 6 * (↑φ : ℂ) ^ 3 := by ring
      _ = (8 * (↑φ : ℂ) + 5) * (2 * (↑φ : ℂ) + 1) := by rw [hφ6, hφ3]
      _ = 16 * (↑φ : ℂ) ^ 2 + 18 * (↑φ : ℂ) + 5 := by ring
      _ = 16 * ((↑φ : ℂ) + 1) + 18 * (↑φ : ℂ) + 5 := by rw [hφ2]
      _ = 34 * (↑φ : ℂ) + 21 := by ring
  have hψ9 : (↑ψ : ℂ) ^ 9 = 34 * (↑ψ : ℂ) + 21 := by
    calc (↑ψ : ℂ) ^ 9 = (↑ψ : ℂ) ^ 6 * (↑ψ : ℂ) ^ 3 := by ring
      _ = (8 * (↑ψ : ℂ) + 5) * (2 * (↑ψ : ℂ) + 1) := by rw [hψ6, hψ3]
      _ = 16 * (↑ψ : ℂ) ^ 2 + 18 * (↑ψ : ℂ) + 5 := by ring
      _ = 16 * ((↑ψ : ℂ) + 1) + 18 * (↑ψ : ℂ) + 5 := by rw [hψ2]
      _ = 34 * (↑ψ : ℂ) + 21 := by ring
  have hφ4 : (↑φ : ℂ) ^ 4 = 3 * (↑φ : ℂ) + 2 := by
    calc (↑φ : ℂ) ^ 4 = (↑φ : ℂ) ^ 2 * (↑φ : ℂ) ^ 2 := by ring
      _ = ((↑φ : ℂ) + 1) * ((↑φ : ℂ) + 1) := by rw [hφ2]
      _ = (↑φ : ℂ) ^ 2 + 2 * (↑φ : ℂ) + 1 := by ring
      _ = ((↑φ : ℂ) + 1) + 2 * (↑φ : ℂ) + 1 := by rw [hφ2]
      _ = 3 * (↑φ : ℂ) + 2 := by ring
  have hψ4 : (↑ψ : ℂ) ^ 4 = 3 * (↑ψ : ℂ) + 2 := by
    calc (↑ψ : ℂ) ^ 4 = (↑ψ : ℂ) ^ 2 * (↑ψ : ℂ) ^ 2 := by ring
      _ = ((↑ψ : ℂ) + 1) * ((↑ψ : ℂ) + 1) := by rw [hψ2]
      _ = (↑ψ : ℂ) ^ 2 + 2 * (↑ψ : ℂ) + 1 := by ring
      _ = ((↑ψ : ℂ) + 1) + 2 * (↑ψ : ℂ) + 1 := by rw [hψ2]
      _ = 3 * (↑ψ : ℂ) + 2 := by ring
  have hC0 : (1 : ℂ) - 3 + 1 - 1 + 3 - 1 = 0 := by ring
  have hC1 :
      (↑φ : ℂ) ^ 3 - 3 * (↑φ : ℂ) ^ 2 + (↑φ : ℂ)
        - (↑ψ : ℂ) + 3 * (↑ψ : ℂ) ^ 2
        - (↑ψ : ℂ) ^ 3 = 0 := by
    calc (↑φ : ℂ) ^ 3 - 3 * (↑φ : ℂ) ^ 2
          + (↑φ : ℂ) - (↑ψ : ℂ)
          + 3 * (↑ψ : ℂ) ^ 2 - (↑ψ : ℂ) ^ 3
        = (2 * (↑φ : ℂ) + 1)
          - 3 * ((↑φ : ℂ) + 1) + (↑φ : ℂ)
          - (↑ψ : ℂ) + 3 * ((↑ψ : ℂ) + 1)
          - (2 * (↑ψ : ℂ) + 1) := by
            rw [hφ3, hφ2, hψ2, hψ3]
      _ = 0 := by ring
  have hC2 :
      (↑φ : ℂ) ^ 6 - 3 * (↑φ : ℂ) ^ 4
        + (↑φ : ℂ) ^ 2 - (↑ψ : ℂ) ^ 2
        + 3 * (↑ψ : ℂ) ^ 4
        - (↑ψ : ℂ) ^ 6 = 0 := by
    calc (↑φ : ℂ) ^ 6 - 3 * (↑φ : ℂ) ^ 4
          + (↑φ : ℂ) ^ 2 - (↑ψ : ℂ) ^ 2
          + 3 * (↑ψ : ℂ) ^ 4 - (↑ψ : ℂ) ^ 6
        = (8 * (↑φ : ℂ) + 5)
          - 3 * (3 * (↑φ : ℂ) + 2)
          + ((↑φ : ℂ) + 1) - ((↑ψ : ℂ) + 1)
          + 3 * (3 * (↑ψ : ℂ) + 2)
          - (8 * (↑ψ : ℂ) + 5) := by
            rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]
      _ = 0 := by ring
  have hC3 :
      (↑φ : ℂ) ^ 9 - 3 * (↑φ : ℂ) ^ 6
        + (↑φ : ℂ) ^ 3 - (↑ψ : ℂ) ^ 3
        + 3 * (↑ψ : ℂ) ^ 6 - (↑ψ : ℂ) ^ 9
        = 12 * ((↑φ : ℂ) - ↑ψ) := by
    calc (↑φ : ℂ) ^ 9 - 3 * (↑φ : ℂ) ^ 6
          + (↑φ : ℂ) ^ 3 - (↑ψ : ℂ) ^ 3
          + 3 * (↑ψ : ℂ) ^ 6 - (↑ψ : ℂ) ^ 9
        = (34 * (↑φ : ℂ) + 21)
          - 3 * (8 * (↑φ : ℂ) + 5)
          + (2 * (↑φ : ℂ) + 1)
          - (2 * (↑ψ : ℂ) + 1)
          + 3 * (8 * (↑ψ : ℂ) + 5)
          - (34 * (↑ψ : ℂ) + 21) := by
            rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]
      _ = 12 * ((↑φ : ℂ) - ↑ψ) := by ring
  have hC3_ne :
      (↑φ : ℂ) ^ 9 - 3 * (↑φ : ℂ) ^ 6
        + (↑φ : ℂ) ^ 3 - (↑ψ : ℂ) ^ 3
        + 3 * (↑ψ : ℂ) ^ 6
        - (↑ψ : ℂ) ^ 9 ≠ 0 := by
    rw [hC3]
    apply mul_ne_zero (by norm_num : (12 : ℂ) ≠ 0) phi_sub_psi_complex_ne
  have hnum_eq : a₀ + a₁ * (↑φ : ℂ) ^ 3 + a₂ * ((↑φ : ℂ) ^ 3) ^ 2 + a₃ * ((↑φ : ℂ) ^ 3) ^ 3 -
      3 * (a₀ + a₁ * (↑φ : ℂ) ^ 2 + a₂ * ((↑φ : ℂ) ^ 2) ^ 2 + a₃ * ((↑φ : ℂ) ^ 2) ^ 3) +
      (a₀ + a₁ * (↑φ : ℂ) + a₂ * (↑φ : ℂ) ^ 2 + a₃ * (↑φ : ℂ) ^ 3) -
      (a₀ + a₁ * (↑ψ : ℂ) + a₂ * (↑ψ : ℂ) ^ 2 + a₃ * (↑ψ : ℂ) ^ 3) +
      3 * (a₀ + a₁ * (↑ψ : ℂ) ^ 2 + a₂ * ((↑ψ : ℂ) ^ 2) ^ 2 + a₃ * ((↑ψ : ℂ) ^ 2) ^ 3) -
      (a₀ + a₁ * (↑ψ : ℂ) ^ 3 + a₂ * ((↑ψ : ℂ) ^ 3) ^ 2 + a₃ * ((↑ψ : ℂ) ^ 3) ^ 3) =
      a₀ * ((1 : ℂ) - 3 + 1 - 1 + 3 - 1) +
      a₁ * ((↑φ : ℂ) ^ 3 - 3 * (↑φ : ℂ) ^ 2
        + (↑φ : ℂ) - (↑ψ : ℂ)
        + 3 * (↑ψ : ℂ) ^ 2 - (↑ψ : ℂ) ^ 3) +
      a₂ * ((↑φ : ℂ) ^ 6 - 3 * (↑φ : ℂ) ^ 4
        + (↑φ : ℂ) ^ 2 - (↑ψ : ℂ) ^ 2
        + 3 * (↑ψ : ℂ) ^ 4 - (↑ψ : ℂ) ^ 6) +
      a₃ * ((↑φ : ℂ) ^ 9 - 3 * (↑φ : ℂ) ^ 6
        + (↑φ : ℂ) ^ 3 - (↑ψ : ℂ) ^ 3
        + 3 * (↑ψ : ℂ) ^ 6
        - (↑ψ : ℂ) ^ 9) := by ring
  rw [hnum_eq, hC0, hC1, hC2] at hnum
  simp only [mul_zero, zero_add] at hnum
  exact (mul_eq_zero.mp hnum).resolve_right hC3_ne

/-! ## Gauge Scaling -/

section GaugeScaling

theorem D6_gauge_scaling (f : ℂ → ℂ) (c x : ℂ) (hc : c ≠ 0) (hx : x ≠ 0) :
    D6 (fun t => f (c * t)) x = c * D6 f (c * x) := by
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  simp only [D6, N6, D6Denom]
  field_simp [D6Denom_mul_ne_zero x hx, D6Denom_mul_ne_zero (c * x) hcx, hc]

end GaugeScaling

/-! ## Time Evolution from Dζ/Poincaré Structure

Time evolution f(t) ↦ f(φt) is the one-parameter subgroup of the Poincaré group
generated by the golden scaling. ker(D6) invariance = Lorentz invariance of vacuum. -/

section TimeEvolution

noncomputable def timeEvolution (f : ℂ → ℂ) : ℂ → ℂ := fun t => f ((↑φ : ℂ) * t)

private theorem phi_complex_ne_zero : (↑φ : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt phi_pos)

theorem ker_D6_invariant (f : ℂ → ℂ) (hf : IsInKerD6 f) :
    IsInKerD6 (timeEvolution f) := by
  obtain ⟨a₀, a₁, a₂, hf_eq⟩ := hf
  use a₀, a₁ * (↑φ : ℂ), a₂ * (↑φ : ℂ)^2
  intro t
  simp only [timeEvolution]
  rw [hf_eq ((↑φ : ℂ) * t)]
  ring

theorem D6_timeEvolution (f : ℂ → ℂ) (x : ℂ) (hx : x ≠ 0) :
    D6 (timeEvolution f) x = (↑φ : ℂ) * D6 f ((↑φ : ℂ) * x) :=
  D6_gauge_scaling f (↑φ) x phi_complex_ne_zero hx

theorem timeEvolution_preserves_D6 (f : ℂ → ℂ) :
    ¬ IsInKerD6 f ↔ ¬ IsInKerD6 (timeEvolution f) := by
  have hφ : (↑φ : ℂ) ≠ 0 := phi_complex_ne_zero
  constructor
  · intro hf hker
    apply hf
    obtain ⟨a₀, a₁, a₂, h_eq⟩ := hker
    use a₀, a₁ / (↑φ : ℂ), a₂ / (↑φ : ℂ)^2
    intro t
    have hφ2 : (↑φ : ℂ)^2 ≠ 0 := pow_ne_zero 2 hφ
    have key := h_eq (t / (↑φ : ℂ))
    simp only [timeEvolution] at key
    have hsimp : (↑φ : ℂ) * (t / (↑φ : ℂ)) = t := by field_simp
    rw [hsimp] at key
    calc f t = a₀ + a₁ * (t / (↑φ : ℂ)) + a₂ * (t / (↑φ : ℂ))^2 := key
      _ = a₀ + a₁ / (↑φ : ℂ) * t + a₂ / (↑φ : ℂ)^2 * t^2 := by field_simp [hφ, hφ2]
  · intro hf hker; exact hf (ker_D6_invariant f hker)

/-- For tⁿ, time evolution amplifies by φⁿ -/
theorem monomial_amplification (n : ℕ) (t : ℂ) :
    timeEvolution (fun s => s^n) t = (↑φ : ℂ)^n * t^n := by
  simp only [timeEvolution]; ring

/-- Adding kernel component doesn't change D6 -/
theorem kernel_component_D6_invariant (f g : ℂ → ℂ) (hg : IsInKerD6 g) :
    ∀ x, x ≠ 0 → D6 (fun t => f t + g t) x = D6 f x := by
  intro x hx
  obtain ⟨a₀, a₁, a₂, hg_eq⟩ := hg
  have hpoly : D6 g x = 0 := by
    have hg' : g = fun t => a₀ + a₁ * t + a₂ * t^2 := funext hg_eq
    rw [hg']
    exact D6_polynomial_deg2 a₀ a₁ a₂ x
  simp only [D6, N6] at hpoly ⊢
  have hpoly_num : g ((↑φ : ℂ) ^ 3 * x) - 3 * g ((↑φ : ℂ) ^ 2 * x) +
      g ((↑φ : ℂ) * x) - g ((↑ψ : ℂ) * x) +
      3 * g ((↑ψ : ℂ) ^ 2 * x) - g ((↑ψ : ℂ) ^ 3 * x) = 0 := by
    rw [div_eq_zero_iff] at hpoly
    cases hpoly with
    | inl h => exact h
    | inr h => exact absurd h (D6Denom_mul_ne_zero x hx)
  calc ((f ((↑φ : ℂ)^3*x) + g ((↑φ : ℂ)^3*x)) -
      3*(f ((↑φ : ℂ)^2*x) + g ((↑φ : ℂ)^2*x)) +
      (f ((↑φ : ℂ)*x) + g ((↑φ : ℂ)*x)) -
      (f ((↑ψ : ℂ)*x) + g ((↑ψ : ℂ)*x)) +
      3*(f ((↑ψ : ℂ)^2*x) + g ((↑ψ : ℂ)^2*x)) -
      (f ((↑ψ : ℂ)^3*x) + g ((↑ψ : ℂ)^3*x))) / (D6Denom * x)
    = ((f ((↑φ : ℂ)^3*x) - 3*f ((↑φ : ℂ)^2*x) + f ((↑φ : ℂ)*x) -
       f ((↑ψ : ℂ)*x) + 3*f ((↑ψ : ℂ)^2*x) - f ((↑ψ : ℂ)^3*x)) +
       (g ((↑φ : ℂ)^3*x) - 3*g ((↑φ : ℂ)^2*x) + g ((↑φ : ℂ)*x) -
       g ((↑ψ : ℂ)*x) + 3*g ((↑ψ : ℂ)^2*x) -
       g ((↑ψ : ℂ)^3*x))) / (D6Denom * x) := by ring_nf
    _ = ((f ((↑φ : ℂ)^3*x) - 3*f ((↑φ : ℂ)^2*x) + f ((↑φ : ℂ)*x) -
       f ((↑ψ : ℂ)*x) + 3*f ((↑ψ : ℂ)^2*x) - f ((↑ψ : ℂ)^3*x)) +
       0) / (D6Denom * x) := by rw [hpoly_num]
    _ = (f ((↑φ : ℂ)^3*x) - 3*f ((↑φ : ℂ)^2*x) + f ((↑φ : ℂ)*x) -
       f ((↑ψ : ℂ)*x) + 3*f ((↑ψ : ℂ)^2*x) - f ((↑ψ : ℂ)^3*x)) /
       (D6Denom * x) := by ring_nf

end TimeEvolution

/-! ## Higher Order Reduction

ker(D7) = ker(D6): the 6-point Dζ AF-channel operator is complete. -/

/-- Higher Order Reduction: ker(D7) = ker(D6) -/
theorem higher_order_reduction :
    ∀ a : ℂ, (∀ k z, z ≠ 0 → FUST.D7_constrained a (fun _ => k) z = 0) ∧
             (∀ z, z ≠ 0 → FUST.D7_constrained a id z = 0) ∧
             (∀ z, z ≠ 0 → FUST.D7_constrained a (fun t => t^2) z = 0) :=
  FUST.D7_kernel_equals_D6_kernel

/-! ## Entropy and Third Law

f ∉ ker(D6) ⟹ ∃t: entropy > 0 (Dζ third law). -/

section Entropy

noncomputable def entropyAtD6 (f : ℂ → ℂ) (t : ℂ) : ℝ := Complex.normSq (perpProjectionD6 f t)

theorem entropyAtD6_nonneg (f : ℂ → ℂ) (t : ℂ) : entropyAtD6 f t ≥ 0 := Complex.normSq_nonneg _

theorem entropyAtD6_zero_iff (f : ℂ → ℂ) (t : ℂ) :
    entropyAtD6 f t = 0 ↔ perpProjectionD6 f t = 0 := Complex.normSq_eq_zero

theorem entropy_zero_iff_kerD6 (f : ℂ → ℂ) :
    (∀ t, entropyAtD6 f t = 0) ↔ IsInKerD6 f := by
  constructor
  · intro h; exact perpD6_zero_implies_ker f (fun t => (entropyAtD6_zero_iff f t).mp (h t))
  · intro hf t; rw [entropyAtD6_zero_iff]; exact kerD6_implies_perp_zero f hf t

theorem third_law_D6 (f : ℂ → ℂ) (hf : ¬IsInKerD6 f) :
    ∃ t, entropyAtD6 f t > 0 := by
  by_contra h; push_neg at h
  exact hf ((entropy_zero_iff_kerD6 f).mp
    (fun t => le_antisymm (h t) (entropyAtD6_nonneg f t)))

theorem time_requires_deviation_D6 (f : ℂ → ℂ)
    (h : ∃ x, x ≠ 0 ∧ D6 f x ≠ 0) : ∃ t, perpProjectionD6 f t ≠ 0 := by
  by_contra hAll; push_neg at hAll
  have hker : IsInKerD6 f := perpD6_zero_implies_ker f hAll
  obtain ⟨x, hx, hD6⟩ := h
  exact hD6 (IsInKerD6_implies_D6_zero f hker x hx)

end Entropy

/-! ## Structural Minimum Time from Dζ

t_FUST = 25/12 = (√5)⁵ / |C₃|, where C₃ = 12√5 is the Dζ AF-channel
spectral coefficient at the minimum massive degree d=3. -/

section StructuralMinTime

/-- D6: t_min = (√5)^5 / |C_3| = (√5)^4 / 12, since |C_3| = 12√5 -/
noncomputable def structuralMinTimeD6 : ℝ := (Real.sqrt 5)^4 / 12

private theorem sqrt5_sq : (Real.sqrt 5)^2 = 5 :=
  Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)

private theorem sqrt5_pow4 : (Real.sqrt 5)^4 = 25 := by
  calc (Real.sqrt 5)^4 = ((Real.sqrt 5)^2)^2 := by ring
    _ = 5^2 := by rw [sqrt5_sq]
    _ = 25 := by norm_num

private theorem sqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)

private theorem sqrt5_ne_zero : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos

theorem structuralMinTimeD6_eq : structuralMinTimeD6 = 25 / 12 := by
  simp only [structuralMinTimeD6]; rw [sqrt5_pow4]

theorem structuralMinTimeD6_positive : structuralMinTimeD6 > 0 := by
  rw [structuralMinTimeD6_eq]; norm_num

/-- C_3 = 12√5 (D6 minimum nonzero spectral coefficient) -/
theorem C3_eq_12_sqrt5 : φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9 = 12 * Real.sqrt 5 := by
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ3 : φ^3 = 2*φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2*ψ + 1 := by
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [hψ2]
      _ = 2*ψ + 1 := by ring
  have hφ6 : φ^6 = 8*φ + 5 := by
    have hφ4 : φ^4 = 3*φ + 2 := by
      calc φ^4 = φ^2 * φ^2 := by ring
        _ = (φ + 1) * (φ + 1) := by rw [hφ2]
        _ = φ^2 + 2*φ + 1 := by ring
        _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
        _ = 3*φ + 2 := by ring
    calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ + 1) + 5*φ + 2 := by rw [hφ2]
      _ = 8*φ + 5 := by ring
  have hψ6 : ψ^6 = 8*ψ + 5 := by
    have hψ4 : ψ^4 = 3*ψ + 2 := by
      calc ψ^4 = ψ^2 * ψ^2 := by ring
        _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
        _ = ψ^2 + 2*ψ + 1 := by ring
        _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
        _ = 3*ψ + 2 := by ring
    calc ψ^6 = ψ^4 * ψ^2 := by ring
      _ = (3*ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3*ψ^2 + 5*ψ + 2 := by ring
      _ = 3*(ψ + 1) + 5*ψ + 2 := by rw [hψ2]
      _ = 8*ψ + 5 := by ring
  have hφ9 : φ^9 = 34*φ + 21 := by
    calc φ^9 = φ^6 * φ^3 := by ring
      _ = (8*φ + 5) * (2*φ + 1) := by rw [hφ6, hφ3]
      _ = 16*φ^2 + 18*φ + 5 := by ring
      _ = 16*(φ + 1) + 18*φ + 5 := by rw [hφ2]
      _ = 34*φ + 21 := by ring
  have hψ9 : ψ^9 = 34*ψ + 21 := by
    calc ψ^9 = ψ^6 * ψ^3 := by ring
      _ = (8*ψ + 5) * (2*ψ + 1) := by rw [hψ6, hψ3]
      _ = 16*ψ^2 + 18*ψ + 5 := by ring
      _ = 16*(ψ + 1) + 18*ψ + 5 := by rw [hψ2]
      _ = 34*ψ + 21 := by ring
  calc φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9
    = (34*φ + 21) - 3*(8*φ + 5) + (2*φ + 1) - (2*ψ + 1) + 3*(8*ψ + 5) - (34*ψ + 21) := by
        rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]
    _ = 12*φ - 12*ψ := by ring
    _ = 12 * (φ - ψ) := by ring
    _ = 12 * Real.sqrt 5 := by rw [phi_sub_psi]

/-- D6 minimum time expressed as (√5)^5 / (12√5) -/
theorem structuralMinTimeD6_from_D6 :
    structuralMinTimeD6 = (Real.sqrt 5)^5 / (12 * Real.sqrt 5) := by
  simp only [structuralMinTimeD6]
  have h12_ne : (12 : ℝ) ≠ 0 := by norm_num
  have h12sqrt5_ne : 12 * Real.sqrt 5 ≠ 0 := mul_ne_zero h12_ne sqrt5_ne_zero
  rw [div_eq_div_iff h12_ne h12sqrt5_ne]
  have h5 : (Real.sqrt 5)^5 = (Real.sqrt 5)^4 * Real.sqrt 5 := by ring
  rw [h5]; ring

end StructuralMinTime

end FUST.LeastAction

/-! ## Backward Compatibility: FUST.TimeTheorem namespace -/

namespace FUST.TimeTheorem

open FUST.LeastAction

theorem abs_psi_lt_one : |ψ| < 1 := FUST.LeastAction.abs_psi_lt_one
theorem phi_mul_abs_psi : φ * |ψ| = 1 := FUST.LeastAction.phi_mul_abs_psi
theorem phi_pow_gt_one (n : ℕ) (hn : n ≥ 1) : φ^n > 1 := FUST.LeastAction.phi_pow_gt_one n hn
theorem monomial_amplification (n : ℕ) (t : ℂ) :
    timeEvolution (fun s => s^n) t = (↑φ : ℂ)^n * t^n :=
  FUST.LeastAction.monomial_amplification n t
theorem kernel_component_D6_invariant (f g : ℂ → ℂ) (hg : IsInKerD6 g) :
    ∀ x, x ≠ 0 → D6 (fun t => f t + g t) x = D6 f x :=
  FUST.LeastAction.kernel_component_D6_invariant f g hg

noncomputable def structuralMinTimeD6 : ℝ := FUST.LeastAction.structuralMinTimeD6
theorem structuralMinTimeD6_eq : structuralMinTimeD6 = 25 / 12 :=
  FUST.LeastAction.structuralMinTimeD6_eq
theorem structuralMinTimeD6_positive : structuralMinTimeD6 > 0 :=
  FUST.LeastAction.structuralMinTimeD6_positive
theorem C3_eq_12_sqrt5 : φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9 = 12 * Real.sqrt 5 :=
  FUST.LeastAction.C3_eq_12_sqrt5
theorem structuralMinTimeD6_from_D6 :
    structuralMinTimeD6 = (Real.sqrt 5)^5 / (12 * Real.sqrt 5) :=
  FUST.LeastAction.structuralMinTimeD6_from_D6

end FUST.TimeTheorem

/-! ## Dimensional Analysis -/

namespace FUST.Dim

/-- Structural minimum time with derived dimension -/
noncomputable def structuralMinTime_dim : ScaleQ dimTime :=
  ⟨FUST.LeastAction.structuralMinTimeD6⟩

theorem structuralMinTime_dim_val : structuralMinTime_dim.val = 25 / 12 :=
  FUST.LeastAction.structuralMinTimeD6_eq

/-- Time is positive -/
theorem structuralMinTime_positive : structuralMinTime_dim.val > 0 :=
  FUST.LeastAction.structuralMinTimeD6_positive

end FUST.Dim
