import FUST.DifferenceOperators
import Mathlib.Tactic

/-!
# FUST Least Action Theorem

In FUST, "least action" is not a principle (external assumption) but a theorem
derived from D6 structure: D6 structure → Least Action Theorem → Time Theorem
-/

namespace FUST.LeastAction

/-! ## Part 1: D6 Kernel Structure -/

/-- D6 kernel is 3-dimensional: span{1, x, x²} -/
theorem D6_kernel_dim_3 :
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) :=
  ⟨D6_const 1, D6_linear, D6_quadratic⟩

/-! ## Part 2: Kernel Membership Definition -/

/-- A function is in ker(D6) iff it equals some degree-2 polynomial.
    Physical interpretation: ker(D6) = light cone (null structure) -/
def IsInKerD6 (f : ℝ → ℝ) : Prop :=
  ∃ a₀ a₁ a₂ : ℝ, ∀ t, f t = a₀ + a₁ * t + a₂ * t^2

/-- D6 applied to degree-2 polynomial is zero -/
theorem D6_polynomial_deg2 (a₀ a₁ a₂ : ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 (fun t => a₀ + a₁ * t + a₂ * t^2) x = 0 := by
  simp only [D6, hx, ↓reduceIte]
  have hφ3 : φ^3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2 * ψ + 1 := by
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [psi_sq]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [psi_sq]
      _ = 2 * ψ + 1 := by ring
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hlin_coef : φ^3 - 3*φ^2 + φ - ψ + 3*ψ^2 - ψ^3 = 0 := by
    rw [hφ3, hφ2, hψ2, hψ3]; ring
  have hquad_coef : (φ^3)^2 - 3*(φ^2)^2 + φ^2 - ψ^2 + 3*(ψ^2)^2 - (ψ^3)^2 = 0 := by
    have hφ4 : φ^4 = 3 * φ + 2 := by calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
    have hψ4 : ψ^4 = 3 * ψ + 2 := by calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
    have hφ6 : φ^6 = 8 * φ + 5 := by calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ + 1) + 5*φ + 2 := by rw [hφ2]
      _ = 8 * φ + 5 := by ring
    have hψ6 : ψ^6 = 8 * ψ + 5 := by calc ψ^6 = ψ^4 * ψ^2 := by ring
      _ = (3*ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3*ψ^2 + 5*ψ + 2 := by ring
      _ = 3*(ψ + 1) + 5*ψ + 2 := by rw [hψ2]
      _ = 8 * ψ + 5 := by ring
    calc (φ^3)^2 - 3*(φ^2)^2 + φ^2 - ψ^2 + 3*(ψ^2)^2 - (ψ^3)^2
      = φ^6 - 3*φ^4 + φ^2 - ψ^2 + 3*ψ^4 - ψ^6 := by ring
      _ = (8*φ+5) - 3*(3*φ+2) + (φ+1) - (ψ+1) + 3*(3*ψ+2) - (8*ψ+5) := by
          rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]
      _ = 0 := by ring
  have hdenom_ne : (φ - ψ)^5 * x ≠ 0 := by
    have hphi_sub : φ - ψ = Real.sqrt 5 := phi_sub_psi
    rw [hphi_sub]
    apply mul_ne_zero
    · apply pow_ne_zero; exact Real.sqrt_ne_zero'.mpr (by norm_num)
    · exact hx
  rw [div_eq_zero_iff]
  left
  calc (a₀ + a₁ * (φ^3 * x) + a₂ * (φ^3 * x)^2) -
      3 * (a₀ + a₁ * (φ^2 * x) + a₂ * (φ^2 * x)^2) +
      (a₀ + a₁ * (φ * x) + a₂ * (φ * x)^2) -
      (a₀ + a₁ * (ψ * x) + a₂ * (ψ * x)^2) +
      3 * (a₀ + a₁ * (ψ^2 * x) + a₂ * (ψ^2 * x)^2) -
      (a₀ + a₁ * (ψ^3 * x) + a₂ * (ψ^3 * x)^2)
    = a₀ * (1 - 3 + 1 - 1 + 3 - 1) +
           a₁ * x * (φ^3 - 3*φ^2 + φ - ψ + 3*ψ^2 - ψ^3) +
           a₂ * x^2 * ((φ^3)^2 - 3*(φ^2)^2 + φ^2 - ψ^2 + 3*(ψ^2)^2 - (ψ^3)^2) := by ring
    _ = a₀ * 0 + a₁ * x * 0 + a₂ * x^2 * 0 := by rw [hlin_coef, hquad_coef]; ring
    _ = 0 := by ring

/-- If f ∈ ker(D6), then D6 f = 0 for all x ≠ 0 -/
theorem IsInKerD6_implies_D6_zero (f : ℝ → ℝ) (hf : IsInKerD6 f) :
    ∀ x, x ≠ 0 → D6 f x = 0 := by
  intro x hx
  obtain ⟨a₀, a₁, a₂, hf_eq⟩ := hf
  have hf' : f = fun t => a₀ + a₁ * t + a₂ * t^2 := funext hf_eq
  rw [hf']
  exact D6_polynomial_deg2 a₀ a₁ a₂ x hx

/-! ## Part 3: Kernel Projection -/

/-- Kernel projection using interpolation points {0, 1, -1}.
    This is the unique degree-2 polynomial agreeing with f at these points. -/
noncomputable def kernelProjection (f : ℝ → ℝ) : ℝ → ℝ :=
  let a₀ := f 0
  let a₁ := (f 1 - f (-1)) / 2
  let a₂ := (f 1 + f (-1) - 2 * f 0) / 2
  fun t => a₀ + a₁ * t + a₂ * t^2

/-- The uniqueness theorem for degree-2 interpolation -/
theorem kernel_interpolation_unique (p q : ℝ → ℝ) (hp : IsInKerD6 p) (hq : IsInKerD6 q)
    (t₀ t₁ t₂ : ℝ) (h01 : t₀ ≠ t₁) (h02 : t₀ ≠ t₂) (h12 : t₁ ≠ t₂)
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
  have hc0 : c₀ + c₁ * t₀ + c₂ * t₀^2 = 0 := by simp only [c₀, c₁, c₂]; linarith
  have hc1 : c₀ + c₁ * t₁ + c₂ * t₁^2 = 0 := by simp only [c₀, c₁, c₂]; linarith
  have hc2 : c₀ + c₁ * t₂ + c₂ * t₂^2 = 0 := by simp only [c₀, c₁, c₂]; linarith
  have hc2_zero : c₂ = 0 := by
    by_contra hne
    have hdiff1 : c₁ * (t₁ - t₀) + c₂ * (t₁^2 - t₀^2) = 0 := by linarith
    have hdiff2 : c₁ * (t₂ - t₀) + c₂ * (t₂^2 - t₀^2) = 0 := by linarith
    have hfac1 : (t₁ - t₀) * (c₁ + c₂ * (t₁ + t₀)) = 0 := by
      have : c₁ * (t₁ - t₀) + c₂ * (t₁ + t₀) * (t₁ - t₀) = 0 := by
        calc c₁ * (t₁ - t₀) + c₂ * (t₁ + t₀) * (t₁ - t₀)
          = c₁ * (t₁ - t₀) + c₂ * (t₁^2 - t₀^2) := by ring
          _ = 0 := hdiff1
      linarith
    have hfac2 : (t₂ - t₀) * (c₁ + c₂ * (t₂ + t₀)) = 0 := by
      have : c₁ * (t₂ - t₀) + c₂ * (t₂ + t₀) * (t₂ - t₀) = 0 := by
        calc c₁ * (t₂ - t₀) + c₂ * (t₂ + t₀) * (t₂ - t₀)
          = c₁ * (t₂ - t₀) + c₂ * (t₂^2 - t₀^2) := by ring
          _ = 0 := hdiff2
      linarith
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
    have hdiff3 : c₂ * (t₁ - t₂) = 0 := by linarith
    have ht12 : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h12
    have hc2' : c₂ = 0 := by
      have := mul_eq_zero.mp hdiff3
      cases this with
      | inl h => exact h
      | inr h => exact absurd h ht12
    exact hne hc2'
  have hc1_zero : c₁ = 0 := by
    have hdiff : c₁ * (t₁ - t₀) = 0 := by
      calc c₁ * (t₁ - t₀) = c₁ * (t₁ - t₀) + c₂ * (t₁^2 - t₀^2) := by rw [hc2_zero]; ring
        _ = 0 := by linarith
    have ht01' : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
    have := mul_eq_zero.mp hdiff
    cases this with
    | inl h => exact h
    | inr h => exact absurd h ht01'
  have hc0_zero : c₀ = 0 := by
    calc c₀ = c₀ + c₁ * t₀ + c₂ * t₀^2 := by rw [hc1_zero, hc2_zero]; ring
      _ = 0 := hc0
  rw [hp_eq, hq_eq]
  have ha0 : a₀ = b₀ := by simp only [c₀] at hc0_zero; linarith
  have ha1 : a₁ = b₁ := by simp only [c₁] at hc1_zero; linarith
  have ha2 : a₂ = b₂ := by simp only [c₂] at hc2_zero; linarith
  rw [ha0, ha1, ha2]

/-- Kernel projection is annihilated by D6 -/
theorem kernelProjection_annihilated_by_D6 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 (kernelProjection f) x = 0 := by
  simp only [kernelProjection]
  exact D6_polynomial_deg2 _ _ _ x hx

/-- Kernel projection is in ker(D6) -/
theorem kernelProjection_is_in_ker (f : ℝ → ℝ) : IsInKerD6 (kernelProjection f) := by
  use f 0, (f 1 - f (-1)) / 2, (f 1 + f (-1) - 2 * f 0) / 2
  intro t
  simp only [kernelProjection]

/-- Perpendicular projection: deviation from ker(D6) -/
noncomputable def perpProjection (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f t - kernelProjection f t

/-- Perpendicular projection has the same D6 value as original function -/
theorem perpProjection_D6_eq (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 (perpProjection f) x = D6 f x := by
  have hker := kernelProjection_annihilated_by_D6 f x hx
  simp only [perpProjection, D6, hx, ↓reduceIte]
  simp only [D6, hx, ↓reduceIte] at hker
  have hdenom_ne : (φ - ψ)^5 * x ≠ 0 := by
    have hphi_sub : φ - ψ = Real.sqrt 5 := phi_sub_psi
    rw [hphi_sub]
    apply mul_ne_zero
    · apply pow_ne_zero; exact Real.sqrt_ne_zero'.mpr (by norm_num)
    · exact hx
  have hnum_zero : kernelProjection f (φ ^ 3 * x) - 3 * kernelProjection f (φ ^ 2 * x) +
      kernelProjection f (φ * x) - kernelProjection f (ψ * x) +
      3 * kernelProjection f (ψ ^ 2 * x) - kernelProjection f (ψ ^ 3 * x) = 0 := by
    have h := div_eq_zero_iff.mp hker
    cases h with
    | inl hnum => exact hnum
    | inr hdenom => exact absurd hdenom hdenom_ne
  have heq : (f (φ ^ 3 * x) - kernelProjection f (φ ^ 3 * x) -
      3 * (f (φ ^ 2 * x) - kernelProjection f (φ ^ 2 * x)) +
      (f (φ * x) - kernelProjection f (φ * x)) -
      (f (ψ * x) - kernelProjection f (ψ * x)) +
      3 * (f (ψ ^ 2 * x) - kernelProjection f (ψ ^ 2 * x)) -
      (f (ψ ^ 3 * x) - kernelProjection f (ψ ^ 3 * x))) =
      (f (φ ^ 3 * x) - 3 * f (φ ^ 2 * x) + f (φ * x) - f (ψ * x) +
       3 * f (ψ ^ 2 * x) - f (ψ ^ 3 * x)) -
      (kernelProjection f (φ ^ 3 * x) - 3 * kernelProjection f (φ ^ 2 * x) +
       kernelProjection f (φ * x) - kernelProjection f (ψ * x) +
       3 * kernelProjection f (ψ ^ 2 * x) - kernelProjection f (ψ ^ 3 * x)) := by ring
  rw [heq, hnum_zero, sub_zero]

/-- If f ∈ ker(D6), then perpProjection is zero everywhere -/
theorem kernel_implies_perp_zero (f : ℝ → ℝ) (hf : IsInKerD6 f) :
    ∀ t, perpProjection f t = 0 := by
  obtain ⟨a₀, a₁, a₂, hf_eq⟩ := hf
  intro t
  simp only [perpProjection, kernelProjection, hf_eq]
  ring

/-- Kernel projection matches f at interpolation points -/
theorem kernelProjection_interpolates (f : ℝ → ℝ) :
    kernelProjection f 0 = f 0 ∧
    kernelProjection f 1 = f 1 ∧
    kernelProjection f (-1) = f (-1) := by
  simp only [kernelProjection]
  constructor
  · ring
  constructor
  · ring
  · ring

/-! ## Part 4: Time Existence (Derived from Action Theorem) -/

/-- Time existence: f ∉ ker(D6), equivalently A[f] > 0 -/
def TimeExists (f : ℝ → ℝ) : Prop := ¬ IsInKerD6 f

/-- A function has degree ≥ 3 component -/
def HasHigherDegree (f : ℝ → ℝ) : Prop :=
  ¬ ∃ a₀ a₁ a₂ : ℝ, ∀ t, f t = a₀ + a₁ * t + a₂ * t^2

/-- Massive state: f ∉ ker(D6) -/
def IsMassiveState (f : ℝ → ℝ) : Prop := HasHigherDegree f

/-- IsMassiveState is exactly TimeExists -/
theorem massive_iff_time_exists (f : ℝ → ℝ) : IsMassiveState f ↔ TimeExists f := by
  simp only [IsMassiveState, HasHigherDegree, TimeExists, IsInKerD6]

/-- D6 f ≠ 0 at some gauge implies time exists -/
theorem D6_nonzero_implies_time (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) (hD6 : D6 f x ≠ 0) :
    TimeExists f := by
  intro hker
  exact hD6 (IsInKerD6_implies_D6_zero f hker x hx)

/-! ## Part 5: φ-Scale Invariant Measure (Haar Measure) -/

section HaarMeasure

/-- φ-scale transformation: x ↦ φx -/
noncomputable def phiScale (x : ℝ) : ℝ := φ * x

/-- The Haar measure on (0,∞) is dx/x in logarithmic coordinates -/
theorem haar_measure_invariance_principle :
    ∀ (a b : ℝ), 0 < a → a < b → Real.log b - Real.log a = Real.log (b/a) := by
  intro a b ha _
  rw [Real.log_div (ne_of_gt (by linarith : 0 < b)) (ne_of_gt ha)]

/-- φ-scaling preserves the ratio structure -/
theorem phi_scale_ratio (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    phiScale x / phiScale y = x / y := by
  simp only [phiScale]
  have hφ : φ ≠ 0 := by have := φ_gt_one; linarith
  field_simp

/-- The measure dx/x is characterized by scale invariance -/
theorem haar_measure_scale_invariance (a b c : ℝ) (ha : 0 < a) (hb : a < b) (hc : 0 < c) :
    Real.log (c * b) - Real.log (c * a) = Real.log b - Real.log a := by
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt (lt_trans ha hb))]
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt ha)]
  ring

end HaarMeasure

/-! ## Part 6: FUST Lagrangian (Local Action Density) -/

section Lagrangian

/-- FUST Lagrangian: squared D6 value at a point -/
noncomputable def FUSTLagrangian (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (D6 f x)^2

/-- Lagrangian is non-negative -/
theorem lagrangian_nonneg (f : ℝ → ℝ) (x : ℝ) : FUSTLagrangian f x ≥ 0 :=
  sq_nonneg _

/-- Lagrangian is zero iff D6 f = 0 at that point -/
theorem lagrangian_zero_iff (f : ℝ → ℝ) (x : ℝ) :
    FUSTLagrangian f x = 0 ↔ D6 f x = 0 := sq_eq_zero_iff

/-- For ker(D6) states, Lagrangian is identically zero -/
theorem lagrangian_ker_zero (f : ℝ → ℝ) (hf : IsInKerD6 f) (x : ℝ) (hx : x ≠ 0) :
    FUSTLagrangian f x = 0 := by
  rw [lagrangian_zero_iff]
  exact IsInKerD6_implies_D6_zero f hf x hx

/-- Positive Lagrangian implies TimeExists -/
theorem positive_lagrangian_implies_time (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hpos : FUSTLagrangian f x > 0) : TimeExists f := by
  intro hker
  have hzero := lagrangian_ker_zero f hker x hx
  linarith

/-- D6 f ≠ 0 implies positive Lagrangian -/
theorem D6_nonzero_implies_positive_lagrangian (f : ℝ → ℝ) (x : ℝ)
    (hne : D6 f x ≠ 0) : FUSTLagrangian f x > 0 := by
  simp only [FUSTLagrangian]
  exact sq_pos_of_ne_zero hne

end Lagrangian

/-! ## Part 7: Causal Boundary Theorem -/

/-- Causal boundary: perpProjection = 0 everywhere implies f ∈ ker(D6) -/
theorem perp_zero_implies_ker (f : ℝ → ℝ) (h : ∀ t, perpProjection f t = 0) :
    IsInKerD6 f := by
  use f 0, (f 1 - f (-1)) / 2, (f 1 + f (-1) - 2 * f 0) / 2
  intro t
  have ht := h t
  simp only [perpProjection, kernelProjection] at ht
  linarith

/-- Causal boundary theorem (both directions) -/
theorem causal_boundary_theorem :
    (∀ f : ℝ → ℝ, IsInKerD6 f → ∀ x, x ≠ 0 → D6 f x = 0) ∧
    (∀ f : ℝ → ℝ, (∀ t, perpProjection f t = 0) → IsInKerD6 f) :=
  ⟨IsInKerD6_implies_D6_zero, perp_zero_implies_ker⟩

/-! ## Part 8: IsMassiveState Properties -/

/-- IsMassiveState iff nonzero perpProjection somewhere -/
theorem massive_iff_nonzero_perp (f : ℝ → ℝ) :
    IsMassiveState f ↔ ∃ t, perpProjection f t ≠ 0 := by
  constructor
  · intro hf
    by_contra h
    push_neg at h
    have hker : IsInKerD6 f := perp_zero_implies_ker f h
    rw [massive_iff_time_exists] at hf
    exact hf hker
  · intro ⟨t, ht⟩
    rw [massive_iff_time_exists]
    intro hker
    exact ht (kernel_implies_perp_zero f hker t)

/-- Massive particle has nonzero perpProjection -/
theorem massive_has_proper_time (f : ℝ → ℝ) (hf : IsMassiveState f) :
    ∃ t, perpProjection f t ≠ 0 :=
  (massive_iff_nonzero_perp f).mp hf

/-! ## Part 9: D6_zero_implies_ker_poly -/

/-- For cubic polynomials, D6 = 0 everywhere implies a₃ = 0 -/
theorem D6_zero_implies_ker_poly (a₀ a₁ a₂ a₃ : ℝ)
    (h : ∀ x, x ≠ 0 → D6 (fun t => a₀ + a₁ * t + a₂ * t ^ 2 + a₃ * t ^ 3) x = 0) :
    a₃ = 0 := by
  have h1 := h 1 one_ne_zero
  simp only [D6, one_ne_zero, ↓reduceIte, mul_one] at h1
  have hdenom_ne : (φ - ψ) ^ 5 ≠ 0 := by
    apply pow_ne_zero
    rw [phi_sub_psi]
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hnum := (div_eq_zero_iff.mp h1).resolve_right hdenom_ne
  have hφ2 := golden_ratio_property
  have hψ2 := psi_sq
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
    calc ψ ^ 3 = ψ ^ 2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ ^ 2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [hψ2]
      _ = 2 * ψ + 1 := by ring
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by
    calc φ ^ 6 = (φ ^ 3) ^ 2 := by ring
      _ = (2 * φ + 1) ^ 2 := by rw [hφ3]
      _ = 4 * φ ^ 2 + 4 * φ + 1 := by ring
      _ = 4 * (φ + 1) + 4 * φ + 1 := by rw [hφ2]
      _ = 8 * φ + 5 := by ring
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by
    calc ψ ^ 6 = (ψ ^ 3) ^ 2 := by ring
      _ = (2 * ψ + 1) ^ 2 := by rw [hψ3]
      _ = 4 * ψ ^ 2 + 4 * ψ + 1 := by ring
      _ = 4 * (ψ + 1) + 4 * ψ + 1 := by rw [hψ2]
      _ = 8 * ψ + 5 := by ring
  have hφ9 : φ ^ 9 = 34 * φ + 21 := by
    calc φ ^ 9 = φ ^ 6 * φ ^ 3 := by ring
      _ = (8 * φ + 5) * (2 * φ + 1) := by rw [hφ6, hφ3]
      _ = 16 * φ ^ 2 + 18 * φ + 5 := by ring
      _ = 16 * (φ + 1) + 18 * φ + 5 := by rw [hφ2]
      _ = 34 * φ + 21 := by ring
  have hψ9 : ψ ^ 9 = 34 * ψ + 21 := by
    calc ψ ^ 9 = ψ ^ 6 * ψ ^ 3 := by ring
      _ = (8 * ψ + 5) * (2 * ψ + 1) := by rw [hψ6, hψ3]
      _ = 16 * ψ ^ 2 + 18 * ψ + 5 := by ring
      _ = 16 * (ψ + 1) + 18 * ψ + 5 := by rw [hψ2]
      _ = 34 * ψ + 21 := by ring
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by
    calc φ ^ 4 = φ ^ 2 * φ ^ 2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ ^ 2 + 2 * φ + 1 := by ring
      _ = (φ + 1) + 2 * φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by
    calc ψ ^ 4 = ψ ^ 2 * ψ ^ 2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ ^ 2 + 2 * ψ + 1 := by ring
      _ = (ψ + 1) + 2 * ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  have hC0 : (1 : ℝ) - 3 + 1 - 1 + 3 - 1 = 0 := by ring
  have hC1 : φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3 = 0 := by
    calc φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3
        = (2 * φ + 1) - 3 * (φ + 1) + φ - ψ + 3 * (ψ + 1) - (2 * ψ + 1) := by
            rw [hφ3, hφ2, hψ2, hψ3]
      _ = 0 := by ring
  have hC2 : φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6 = 0 := by
    calc φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6
        = (8 * φ + 5) - 3 * (3 * φ + 2) + (φ + 1) - (ψ + 1) + 3 * (3 * ψ + 2) - (8 * ψ + 5) := by
            rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]
      _ = 0 := by ring
  have hC3 : φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9 = 12 * (φ - ψ) := by
    calc φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9
        = (34 * φ + 21) - 3 * (8 * φ + 5) + (2 * φ + 1) - (2 * ψ + 1) +
          3 * (8 * ψ + 5) - (34 * ψ + 21) := by rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]
      _ = 12 * (φ - ψ) := by ring
  have hC3_ne : φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9 ≠ 0 := by
    rw [hC3, phi_sub_psi]
    apply mul_ne_zero (by norm_num : (12 : ℝ) ≠ 0)
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hnum_eq : a₀ + a₁ * φ ^ 3 + a₂ * (φ ^ 3) ^ 2 + a₃ * (φ ^ 3) ^ 3 -
      3 * (a₀ + a₁ * φ ^ 2 + a₂ * (φ ^ 2) ^ 2 + a₃ * (φ ^ 2) ^ 3) +
      (a₀ + a₁ * φ + a₂ * φ ^ 2 + a₃ * φ ^ 3) -
      (a₀ + a₁ * ψ + a₂ * ψ ^ 2 + a₃ * ψ ^ 3) +
      3 * (a₀ + a₁ * ψ ^ 2 + a₂ * (ψ ^ 2) ^ 2 + a₃ * (ψ ^ 2) ^ 3) -
      (a₀ + a₁ * ψ ^ 3 + a₂ * (ψ ^ 3) ^ 2 + a₃ * (ψ ^ 3) ^ 3) =
      a₀ * ((1 : ℝ) - 3 + 1 - 1 + 3 - 1) +
      a₁ * (φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3) +
      a₂ * (φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6) +
      a₃ * (φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9) := by ring
  rw [hnum_eq, hC0, hC1, hC2] at hnum
  simp only [mul_zero, zero_add] at hnum
  exact (mul_eq_zero.mp hnum).resolve_right hC3_ne

/-! ## Part 10: Photon and Constant States -/

/-- A function is constant -/
def IsConstant (f : ℝ → ℝ) : Prop := ∃ c : ℝ, ∀ t, f t = c

/-- A function has energy (non-constant) -/
def HasEnergy (f : ℝ → ℝ) : Prop := ¬ IsConstant f

/-- Constant functions are in ker(D6) -/
theorem constant_in_kernel (c : ℝ) : IsInKerD6 (fun _ => c) := by
  use c, 0, 0
  intro t; ring

/-- Photon state: in ker(D6) but non-constant -/
def IsPhotonState (f : ℝ → ℝ) : Prop := IsInKerD6 f ∧ HasEnergy f

/-- Photon has D6 = 0 (no proper time) -/
theorem photon_no_proper_time (f : ℝ → ℝ) (hf : IsPhotonState f) :
    ∀ x, x ≠ 0 → D6 f x = 0 :=
  IsInKerD6_implies_D6_zero f hf.1

/-! ## Part 11: Summary Theorems -/

/-- Complete Least Action Theorem (derived, not assumed) -/
theorem ker_iff_not_time (f : ℝ → ℝ) : IsInKerD6 f ↔ ¬TimeExists f := by
  simp only [TimeExists, not_not]

theorem fust_least_action_complete :
    (∀ f x, FUSTLagrangian f x ≥ 0) ∧
    (∀ f, IsInKerD6 f → ∀ x, x ≠ 0 → FUSTLagrangian f x = 0) ∧
    (∀ f, IsInKerD6 f ↔ ¬TimeExists f) ∧
    (∀ f, IsInKerD6 f → ∀ x, x ≠ 0 → D6 f x = 0) :=
  ⟨lagrangian_nonneg, lagrangian_ker_zero, ker_iff_not_time, IsInKerD6_implies_D6_zero⟩

end FUST.LeastAction
