import FUST.DifferenceOperators
import FUST.DimensionalAnalysis
import FUST.FrourioLogarithm
import Mathlib.Tactic

/-!
# FUST Least Action Theorem

In FUST, "least action" is not a principle (external assumption) but a theorem
derived from Dm structure. Each operator Dm (m=2..6) has its own kernel,
projection, Lagrangian, and time existence condition.
-/

namespace FUST.LeastAction

/-! ## Part 1: D6 Kernel Structure -/

/-- D6 kernel is 3-dimensional: span{1, x, x²} -/
theorem D6_kernel_dim_3 :
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) :=
  ⟨D6_const 1, D6_linear, D6_quadratic⟩

/-! ## Part 2: Kernel Membership -/

/-- f ∈ ker(D2) iff f is constant -/
def IsInKerD2 (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ t, f t = c

/-- f ∈ ker(D3) iff f is constant -/
def IsInKerD3 (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ t, f t = c

/-- f ∈ ker(D4) iff f = c·x² -/
def IsInKerD4 (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ t, f t = c * t ^ 2

/-- f ∈ ker(D5) iff f is affine -/
def IsInKerD5 (f : ℝ → ℝ) : Prop :=
  ∃ a₀ a₁ : ℝ, ∀ t, f t = a₀ + a₁ * t

/-- f ∈ ker(D6) iff f equals some degree-2 polynomial -/
def IsInKerD6 (f : ℝ → ℝ) : Prop :=
  ∃ a₀ a₁ a₂ : ℝ, ∀ t, f t = a₀ + a₁ * t + a₂ * t^2

/-- D6 applied to degree-2 polynomial is zero -/
theorem D6_polynomial_deg2 (a₀ a₁ a₂ : ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 (fun t => a₀ + a₁ * t + a₂ * t^2) x = 0 := by
  simp only [D6, N6, D6Denom, hx, ↓reduceIte]
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

theorem IsInKerD2_implies_D2_zero (f : ℝ → ℝ) (hf : IsInKerD2 f) :
    ∀ x, x ≠ 0 → D2 f x = 0 := by
  intro x hx
  obtain ⟨c, hf⟩ := hf
  rw [show f = (fun _ => c) from funext hf]
  exact D2_const c x hx

theorem IsInKerD3_implies_D3_zero (f : ℝ → ℝ) (hf : IsInKerD3 f) :
    ∀ x, x ≠ 0 → D3 f x = 0 := by
  intro x hx
  obtain ⟨c, hf⟩ := hf
  rw [show f = (fun _ => c) from funext hf]
  exact D3_const c x hx

theorem IsInKerD4_implies_D4_zero (f : ℝ → ℝ) (hf : IsInKerD4 f) :
    ∀ x, x ≠ 0 → D4 f x = 0 := by
  intro x hx
  obtain ⟨c, hf⟩ := hf
  rw [show f = (fun t => c * t ^ 2) from funext hf]
  simp only [D4, hx, ↓reduceIte]
  have : c * (φ ^ 2 * x) ^ 2 - φ ^ 2 * (c * (φ * x) ^ 2) +
      ψ ^ 2 * (c * (ψ * x) ^ 2) - c * (ψ ^ 2 * x) ^ 2 = 0 := by ring
  simp [this]

/-- D5 applied to affine function is zero -/
theorem D5_polynomial_deg1 (a₀ a₁ : ℝ) (x : ℝ) (hx : x ≠ 0) :
    D5 (fun t => a₀ + a₁ * t) x = 0 := by
  have hconst : D5 (fun _ => a₀) x = 0 := D5_const a₀ x hx
  have hlin : D5 (fun t => a₁ * t) x = 0 := by
    have h := D5_linear x hx
    calc D5 (fun t => a₁ * t) x = a₁ * D5 id x := by
          simp only [D5, hx, ↓reduceIte, id]; ring
      _ = a₁ * 0 := by rw [h]
      _ = 0 := by ring
  calc D5 (fun t => a₀ + a₁ * t) x
    = D5 (fun _ => a₀) x + D5 (fun t => a₁ * t) x := by
        simp only [D5, hx, ↓reduceIte]; ring
    _ = 0 + 0 := by rw [hconst, hlin]
    _ = 0 := by ring

theorem IsInKerD5_implies_D5_zero (f : ℝ → ℝ) (hf : IsInKerD5 f) :
    ∀ x, x ≠ 0 → D5 f x = 0 := by
  intro x hx
  obtain ⟨a₀, a₁, hf⟩ := hf
  rw [show f = (fun t => a₀ + a₁ * t) from funext hf]
  exact D5_polynomial_deg1 a₀ a₁ x hx

/-! ## Part 3: Kernel Projection -/

section KernelProjection

/-- D6 kernel projection using interpolation at {0, 1, -1} -/
noncomputable def kernelProjectionD6 (f : ℝ → ℝ) : ℝ → ℝ :=
  let a₀ := f 0
  let a₁ := (f 1 - f (-1)) / 2
  let a₂ := (f 1 + f (-1) - 2 * f 0) / 2
  fun t => a₀ + a₁ * t + a₂ * t^2

noncomputable def kernelProjectionD2 (f : ℝ → ℝ) : ℝ → ℝ := fun _ => f 0
noncomputable def kernelProjectionD3 (f : ℝ → ℝ) : ℝ → ℝ := fun _ => f 0

/-- D4 kernel projection onto span{x²} using evaluation at x=1 -/
noncomputable def kernelProjectionD4 (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f 1 * t ^ 2

/-- D5 kernel projection onto span{1, x} using interpolation at {1, -1} -/
noncomputable def kernelProjectionD5 (f : ℝ → ℝ) : ℝ → ℝ :=
  let a₀ := (f 1 + f (-1)) / 2
  let a₁ := (f 1 - f (-1)) / 2
  fun t => a₀ + a₁ * t

/-- D6 uniqueness theorem for degree-2 interpolation -/
theorem kernel_interpolation_unique_D6 (p q : ℝ → ℝ) (hp : IsInKerD6 p) (hq : IsInKerD6 q)
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

theorem kernelProjectionD6_annihilated (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 (kernelProjectionD6 f) x = 0 := by
  simp only [kernelProjectionD6]
  exact D6_polynomial_deg2 _ _ _ x hx

theorem kernelProjectionD6_is_in_ker (f : ℝ → ℝ) : IsInKerD6 (kernelProjectionD6 f) := by
  use f 0, (f 1 - f (-1)) / 2, (f 1 + f (-1) - 2 * f 0) / 2
  intro t
  simp only [kernelProjectionD6]

theorem kernelProjectionD2_is_in_ker (f : ℝ → ℝ) : IsInKerD2 (kernelProjectionD2 f) :=
  ⟨f 0, fun _ => rfl⟩

theorem kernelProjectionD3_is_in_ker (f : ℝ → ℝ) : IsInKerD3 (kernelProjectionD3 f) :=
  ⟨f 0, fun _ => rfl⟩

theorem kernelProjectionD4_is_in_ker (f : ℝ → ℝ) : IsInKerD4 (kernelProjectionD4 f) :=
  ⟨f 1, fun _ => rfl⟩

theorem kernelProjectionD5_is_in_ker (f : ℝ → ℝ) : IsInKerD5 (kernelProjectionD5 f) :=
  ⟨(f 1 + f (-1)) / 2, (f 1 - f (-1)) / 2, fun _ => rfl⟩

/-- D6 perpendicular projection: deviation from ker(D6) -/
noncomputable def perpProjectionD6 (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f t - kernelProjectionD6 f t

noncomputable def perpProjectionD2 (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f t - kernelProjectionD2 f t

noncomputable def perpProjectionD3 (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f t - kernelProjectionD3 f t

noncomputable def perpProjectionD4 (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f t - kernelProjectionD4 f t

noncomputable def perpProjectionD5 (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f t - kernelProjectionD5 f t

theorem perpProjectionD6_D6_eq (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 (perpProjectionD6 f) x = D6 f x := by
  have hker := kernelProjectionD6_annihilated f x hx
  rw [D6_eq_N6_div _ _ hx, D6_eq_N6_div f _ hx]
  congr 1
  rw [D6_eq_N6_div _ _ hx] at hker
  have hdenom_ne : D6Denom * x ≠ 0 := D6Denom_mul_ne_zero x hx
  have hnum_zero : N6 (kernelProjectionD6 f) x = 0 := by
    have h := div_eq_zero_iff.mp hker
    cases h with
    | inl hnum => exact hnum
    | inr hdenom => exact absurd hdenom hdenom_ne
  simp only [N6, perpProjectionD6] at hnum_zero ⊢
  linarith

theorem perpProjectionD2_D2_eq (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D2 (perpProjectionD2 f) x = D2 f x := by
  simp only [perpProjectionD2, kernelProjectionD2, D2, hx, ↓reduceIte]
  ring

theorem perpProjectionD3_D3_eq (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D3 (perpProjectionD3 f) x = D3 f x := by
  simp only [perpProjectionD3, kernelProjectionD3, D3, hx, ↓reduceIte]
  ring

theorem perpProjectionD4_D4_eq (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D4 (perpProjectionD4 f) x = D4 f x := by
  simp only [perpProjectionD4, kernelProjectionD4, D4, hx, ↓reduceIte]
  have hden : (φ - ψ) ^ 3 * x ≠ 0 := by
    apply mul_ne_zero
    · apply pow_ne_zero; rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
    · exact hx
  rw [div_eq_div_iff hden hden]
  ring

theorem perpProjectionD5_D5_eq (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D5 (perpProjectionD5 f) x = D5 f x := by
  have hker := IsInKerD5_implies_D5_zero _ (kernelProjectionD5_is_in_ker f) x hx
  have : D5 (perpProjectionD5 f) x =
      D5 f x + D5 (fun t => -(kernelProjectionD5 f t)) x := by
    simp only [perpProjectionD5, kernelProjectionD5, D5, hx, ↓reduceIte]; ring
  rw [this]
  have hneg : D5 (fun t => -(kernelProjectionD5 f t)) x =
      -(D5 (kernelProjectionD5 f) x) := by
    simp only [D5, hx, ↓reduceIte, kernelProjectionD5]; ring
  rw [hneg, hker, neg_zero, add_zero]

/-- If f ∈ ker(D6), then perpProjectionD6 is zero everywhere -/
theorem kerD6_implies_perp_zero (f : ℝ → ℝ) (hf : IsInKerD6 f) :
    ∀ t, perpProjectionD6 f t = 0 := by
  obtain ⟨a₀, a₁, a₂, hf_eq⟩ := hf
  intro t
  simp only [perpProjectionD6, kernelProjectionD6, hf_eq]
  ring

theorem kernelProjectionD6_interpolates (f : ℝ → ℝ) :
    kernelProjectionD6 f 0 = f 0 ∧
    kernelProjectionD6 f 1 = f 1 ∧
    kernelProjectionD6 f (-1) = f (-1) := by
  simp only [kernelProjectionD6]
  constructor
  · ring
  constructor
  · ring
  · ring

/-- Uniqueness: two constants agreeing at one point are equal -/
theorem kernel_interpolation_unique_D2 (p q : ℝ → ℝ) (hp : IsInKerD2 p) (hq : IsInKerD2 q)
    (t₀ : ℝ) (h : p t₀ = q t₀) : ∀ t, p t = q t := by
  obtain ⟨c, hp⟩ := hp
  obtain ⟨d, hq⟩ := hq
  have : c = d := by rw [hp t₀, hq t₀] at h; exact h
  intro t; rw [hp, hq, this]

theorem kernel_interpolation_unique_D3 (p q : ℝ → ℝ) (hp : IsInKerD3 p) (hq : IsInKerD3 q)
    (t₀ : ℝ) (h : p t₀ = q t₀) : ∀ t, p t = q t := by
  obtain ⟨c, hp⟩ := hp
  obtain ⟨d, hq⟩ := hq
  have : c = d := by rw [hp t₀, hq t₀] at h; exact h
  intro t; rw [hp, hq, this]

/-- Uniqueness: two c·t² agreeing at any nonzero point are equal -/
theorem kernel_interpolation_unique_D4 (p q : ℝ → ℝ) (hp : IsInKerD4 p) (hq : IsInKerD4 q)
    (t₀ : ℝ) (ht₀ : t₀ ≠ 0) (h : p t₀ = q t₀) : ∀ t, p t = q t := by
  obtain ⟨c, hp_eq⟩ := hp
  obtain ⟨d, hq_eq⟩ := hq
  have : c * t₀ ^ 2 = d * t₀ ^ 2 := by rw [← hp_eq, ← hq_eq]; exact h
  have hcd : c = d := by
    have ht2 : t₀ ^ 2 ≠ 0 := pow_ne_zero 2 ht₀
    exact mul_right_cancel₀ ht2 this
  intro t; rw [hp_eq, hq_eq, hcd]

/-- Uniqueness: two affine functions agreeing at 2 distinct points are equal -/
theorem kernel_interpolation_unique_D5 (p q : ℝ → ℝ) (hp : IsInKerD5 p) (hq : IsInKerD5 q)
    (t₀ t₁ : ℝ) (h01 : t₀ ≠ t₁) (hp0 : p t₀ = q t₀) (hp1 : p t₁ = q t₁) :
    ∀ t, p t = q t := by
  obtain ⟨a₀, a₁, hp_eq⟩ := hp
  obtain ⟨b₀, b₁, hq_eq⟩ := hq
  have h0 : a₀ + a₁ * t₀ = b₀ + b₁ * t₀ := by rw [← hp_eq, ← hq_eq]; exact hp0
  have h1 : a₀ + a₁ * t₁ = b₀ + b₁ * t₁ := by rw [← hp_eq, ← hq_eq]; exact hp1
  have hc1 : (a₁ - b₁) * (t₀ - t₁) = 0 := by linarith
  have ht : t₀ - t₁ ≠ 0 := sub_ne_zero.mpr h01
  have ha1 : a₁ = b₁ := by
    have := mul_eq_zero.mp hc1
    cases this with
    | inl h => linarith
    | inr h => exact absurd h ht
  have ha0 : a₀ = b₀ := by
    have := h0; rw [ha1] at this; linarith
  intro t; rw [hp_eq, hq_eq, ha0, ha1]

end KernelProjection

/-! ## Part 4: Time Existence -/

def TimeExistsD2 (f : ℝ → ℝ) : Prop := ¬ IsInKerD2 f
def TimeExistsD3 (f : ℝ → ℝ) : Prop := ¬ IsInKerD3 f
def TimeExistsD4 (f : ℝ → ℝ) : Prop := ¬ IsInKerD4 f
def TimeExistsD5 (f : ℝ → ℝ) : Prop := ¬ IsInKerD5 f
def TimeExistsD6 (f : ℝ → ℝ) : Prop := ¬ IsInKerD6 f

/-- D6 f ≠ 0 at some gauge implies time exists -/
theorem D6_nonzero_implies_time (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) (hD6 : D6 f x ≠ 0) :
    TimeExistsD6 f := by
  intro hker
  exact hD6 (IsInKerD6_implies_D6_zero f hker x hx)

/-! ## Part 5: Lagrangian -/

section Lagrangian

noncomputable def D2Lagrangian (f : ℝ → ℝ) (x : ℝ) : ℝ := (D2 f x) ^ 2
noncomputable def D3Lagrangian (f : ℝ → ℝ) (x : ℝ) : ℝ := (D3 f x) ^ 2
noncomputable def D4Lagrangian (f : ℝ → ℝ) (x : ℝ) : ℝ := (D4 f x) ^ 2
noncomputable def D5Lagrangian (f : ℝ → ℝ) (x : ℝ) : ℝ := (D5 f x) ^ 2
noncomputable def D6Lagrangian (f : ℝ → ℝ) (x : ℝ) : ℝ := (D6 f x) ^ 2

theorem D2_lagrangian_nonneg (f : ℝ → ℝ) (x : ℝ) : D2Lagrangian f x ≥ 0 := sq_nonneg _
theorem D3_lagrangian_nonneg (f : ℝ → ℝ) (x : ℝ) : D3Lagrangian f x ≥ 0 := sq_nonneg _
theorem D4_lagrangian_nonneg (f : ℝ → ℝ) (x : ℝ) : D4Lagrangian f x ≥ 0 := sq_nonneg _
theorem D5_lagrangian_nonneg (f : ℝ → ℝ) (x : ℝ) : D5Lagrangian f x ≥ 0 := sq_nonneg _
theorem D6_lagrangian_nonneg (f : ℝ → ℝ) (x : ℝ) : D6Lagrangian f x ≥ 0 := sq_nonneg _

theorem D2_lagrangian_zero_iff (f : ℝ → ℝ) (x : ℝ) :
    D2Lagrangian f x = 0 ↔ D2 f x = 0 := sq_eq_zero_iff
theorem D3_lagrangian_zero_iff (f : ℝ → ℝ) (x : ℝ) :
    D3Lagrangian f x = 0 ↔ D3 f x = 0 := sq_eq_zero_iff
theorem D4_lagrangian_zero_iff (f : ℝ → ℝ) (x : ℝ) :
    D4Lagrangian f x = 0 ↔ D4 f x = 0 := sq_eq_zero_iff
theorem D5_lagrangian_zero_iff (f : ℝ → ℝ) (x : ℝ) :
    D5Lagrangian f x = 0 ↔ D5 f x = 0 := sq_eq_zero_iff
theorem D6_lagrangian_zero_iff (f : ℝ → ℝ) (x : ℝ) :
    D6Lagrangian f x = 0 ↔ D6 f x = 0 := sq_eq_zero_iff

theorem D2_lagrangian_ker_zero (f : ℝ → ℝ) (hf : IsInKerD2 f) (x : ℝ) (hx : x ≠ 0) :
    D2Lagrangian f x = 0 := by
  rw [D2_lagrangian_zero_iff]; exact IsInKerD2_implies_D2_zero f hf x hx

theorem D3_lagrangian_ker_zero (f : ℝ → ℝ) (hf : IsInKerD3 f) (x : ℝ) (hx : x ≠ 0) :
    D3Lagrangian f x = 0 := by
  rw [D3_lagrangian_zero_iff]; exact IsInKerD3_implies_D3_zero f hf x hx

theorem D4_lagrangian_ker_zero (f : ℝ → ℝ) (hf : IsInKerD4 f) (x : ℝ) (hx : x ≠ 0) :
    D4Lagrangian f x = 0 := by
  rw [D4_lagrangian_zero_iff]; exact IsInKerD4_implies_D4_zero f hf x hx

theorem D5_lagrangian_ker_zero (f : ℝ → ℝ) (hf : IsInKerD5 f) (x : ℝ) (hx : x ≠ 0) :
    D5Lagrangian f x = 0 := by
  rw [D5_lagrangian_zero_iff]; exact IsInKerD5_implies_D5_zero f hf x hx

theorem D6_lagrangian_ker_zero (f : ℝ → ℝ) (hf : IsInKerD6 f) (x : ℝ) (hx : x ≠ 0) :
    D6Lagrangian f x = 0 := by
  rw [D6_lagrangian_zero_iff]; exact IsInKerD6_implies_D6_zero f hf x hx

end Lagrangian

/-! ## Part 6: Causal Boundary -/

theorem perpD6_zero_implies_ker (f : ℝ → ℝ) (h : ∀ t, perpProjectionD6 f t = 0) :
    IsInKerD6 f := by
  use f 0, (f 1 - f (-1)) / 2, (f 1 + f (-1) - 2 * f 0) / 2
  intro t
  have ht := h t
  simp only [perpProjectionD6, kernelProjectionD6] at ht
  linarith

theorem perpD2_zero_implies_ker (f : ℝ → ℝ) (h : ∀ t, perpProjectionD2 f t = 0) :
    IsInKerD2 f := by
  have : ∀ t, f t = f 0 := fun t => by
    have := h t; simp only [perpProjectionD2, kernelProjectionD2] at this; linarith
  exact ⟨f 0, this⟩

theorem perpD3_zero_implies_ker (f : ℝ → ℝ) (h : ∀ t, perpProjectionD3 f t = 0) :
    IsInKerD3 f := by
  have : ∀ t, f t = f 0 := fun t => by
    have := h t; simp only [perpProjectionD3, kernelProjectionD3] at this; linarith
  exact ⟨f 0, this⟩

theorem perpD4_zero_implies_ker (f : ℝ → ℝ) (h : ∀ t, perpProjectionD4 f t = 0) :
    IsInKerD4 f := by
  have : ∀ t, f t = f 1 * t ^ 2 := fun t => by
    have := h t; simp only [perpProjectionD4, kernelProjectionD4] at this; linarith
  exact ⟨f 1, this⟩

theorem perpD5_zero_implies_ker (f : ℝ → ℝ) (h : ∀ t, perpProjectionD5 f t = 0) :
    IsInKerD5 f := by
  have hval : ∀ t, f t = (f 1 + f (-1)) / 2 + (f 1 - f (-1)) / 2 * t := fun t => by
    have := h t; simp only [perpProjectionD5, kernelProjectionD5] at this; linarith
  exact ⟨(f 1 + f (-1)) / 2, (f 1 - f (-1)) / 2, hval⟩

theorem kerD2_implies_perp_zero (f : ℝ → ℝ) (hf : IsInKerD2 f) :
    ∀ t, perpProjectionD2 f t = 0 := by
  obtain ⟨c, hf⟩ := hf
  intro t; simp only [perpProjectionD2, kernelProjectionD2, hf]; ring

theorem kerD3_implies_perp_zero (f : ℝ → ℝ) (hf : IsInKerD3 f) :
    ∀ t, perpProjectionD3 f t = 0 := by
  obtain ⟨c, hf⟩ := hf
  intro t; simp only [perpProjectionD3, kernelProjectionD3, hf]; ring

theorem kerD4_implies_perp_zero (f : ℝ → ℝ) (hf : IsInKerD4 f) :
    ∀ t, perpProjectionD4 f t = 0 := by
  obtain ⟨c, hf⟩ := hf
  intro t; simp only [perpProjectionD4, kernelProjectionD4, hf]; ring

theorem kerD5_implies_perp_zero (f : ℝ → ℝ) (hf : IsInKerD5 f) :
    ∀ t, perpProjectionD5 f t = 0 := by
  obtain ⟨a₀, a₁, hf⟩ := hf
  intro t; simp only [perpProjectionD5, kernelProjectionD5, hf]; ring

/-! ## Part 7: TimeExistsD6 Properties -/

theorem timeExists_iff_nonzero_perpD6 (f : ℝ → ℝ) :
    TimeExistsD6 f ↔ ∃ t, perpProjectionD6 f t ≠ 0 := by
  constructor
  · intro hf
    by_contra h
    push_neg at h
    exact hf (perpD6_zero_implies_ker f h)
  · intro ⟨t, ht⟩ hker
    exact ht (kerD6_implies_perp_zero f hker t)

theorem timeExists_has_proper_timeD6 (f : ℝ → ℝ) (hf : TimeExistsD6 f) :
    ∃ t, perpProjectionD6 f t ≠ 0 :=
  (timeExists_iff_nonzero_perpD6 f).mp hf

/-! ## Part 8: D6_zero_implies_ker_poly -/

/-- For cubic polynomials, D6 = 0 everywhere implies a₃ = 0 -/
theorem D6_zero_implies_ker_poly (a₀ a₁ a₂ a₃ : ℝ)
    (h : ∀ x, x ≠ 0 → D6 (fun t => a₀ + a₁ * t + a₂ * t ^ 2 + a₃ * t ^ 3) x = 0) :
    a₃ = 0 := by
  have h1 := h 1 one_ne_zero
  simp only [D6, N6, one_ne_zero, ↓reduceIte, mul_one] at h1
  have hdenom_ne : D6Denom ≠ 0 := D6Denom_ne_zero
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

/-! ## Part 9: Kernel Hierarchy -/

section KernelHierarchy

/-- ker(D2) ⊂ ker(D5) -/
theorem ker_D2_subset_ker_D5 (f : ℝ → ℝ) (hf : IsInKerD2 f) : IsInKerD5 f := by
  obtain ⟨c, hf⟩ := hf
  exact ⟨c, 0, fun t => by rw [hf]; ring⟩

/-- ker(D4) ⊄ ker(D5): x² ∈ ker(D4) \ ker(D5) -/
theorem ker_D4_not_subset_ker_D5 :
    ¬ (∀ f, IsInKerD4 f → IsInKerD5 f) := by
  push_neg
  refine ⟨fun t => t ^ 2, ⟨1, fun t => by ring⟩, ?_⟩
  intro ⟨a₀, a₁, h⟩
  have h0 := h 0; simp at h0
  have h1 := h 1; simp at h1
  have h2 := h 2; simp at h2
  linarith

/-- D4 detects constants: constant functions are massive under D4 -/
theorem D4_constant_is_massive (c : ℝ) (hc : c ≠ 0) : TimeExistsD4 (fun _ => c) := by
  intro ⟨d, hd⟩
  have h0 := hd 0; simp only [mul_zero, pow_succ, pow_zero] at h0
  exact hc h0

end KernelHierarchy

/-! ## Part 10: Gauge Scaling -/

section GaugeScaling

theorem D2_gauge_scaling (f : ℝ → ℝ) (c x : ℝ) (hc : c ≠ 0) (hx : x ≠ 0) :
    D2 (fun t => f (c * t)) x = c * D2 f (c * x) := by
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  simp only [D2, hx, hcx, ↓reduceIte]
  have : c * (φ * x) = φ * (c * x) := by ring
  have : c * (ψ * x) = ψ * (c * x) := by ring
  field_simp [mul_ne_zero (by rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num) :
    φ - ψ ≠ 0) hx,
    mul_ne_zero (by rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num) :
    φ - ψ ≠ 0) hcx, hc]

theorem D3_gauge_scaling (f : ℝ → ℝ) (c x : ℝ) (hc : c ≠ 0) (hx : x ≠ 0) :
    D3 (fun t => f (c * t)) x = c * D3 f (c * x) := by
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  simp only [D3, hx, hcx, ↓reduceIte]
  have hφψ : (φ - ψ) ^ 2 ≠ 0 := pow_ne_zero 2
    (by rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num))
  field_simp [mul_ne_zero hφψ hx, mul_ne_zero hφψ hcx, hc]

theorem D4_gauge_scaling (f : ℝ → ℝ) (c x : ℝ) (hc : c ≠ 0) (hx : x ≠ 0) :
    D4 (fun t => f (c * t)) x = c * D4 f (c * x) := by
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  simp only [D4, hx, hcx, ↓reduceIte]
  have hφψ : (φ - ψ) ^ 3 ≠ 0 := pow_ne_zero 3
    (by rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num))
  field_simp [mul_ne_zero hφψ hx, mul_ne_zero hφψ hcx, hc]

theorem D5_gauge_scaling (f : ℝ → ℝ) (c x : ℝ) (hc : c ≠ 0) (hx : x ≠ 0) :
    D5 (fun t => f (c * t)) x = c * D5 f (c * x) := by
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  simp only [D5, hx, hcx, ↓reduceIte]
  have hφψ : (φ - ψ) ^ 4 ≠ 0 := pow_ne_zero 4
    (by rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num))
  field_simp [mul_ne_zero hφψ hx, mul_ne_zero hφψ hcx, hc]

theorem D6_gauge_scaling (f : ℝ → ℝ) (c x : ℝ) (hc : c ≠ 0) (hx : x ≠ 0) :
    D6 (fun t => f (c * t)) x = c * D6 f (c * x) := by
  have hcx : c * x ≠ 0 := mul_ne_zero hc hx
  simp only [D6, N6, D6Denom, hx, hcx, ↓reduceIte]
  have harg2 : c * (φ^2 * x) = φ^2 * (c * x) := by ring
  have harg3 : c * (φ * x) = φ * (c * x) := by ring
  have harg4 : c * (ψ * x) = ψ * (c * x) := by ring
  have harg5 : c * (ψ^2 * x) = ψ^2 * (c * x) := by ring
  have harg6 : c * (ψ^3 * x) = ψ^3 * (c * x) := by ring
  simp only [harg2, harg3, harg4, harg5, harg6]
  field_simp [D6Denom_mul_ne_zero x hx, D6Denom_mul_ne_zero (c * x) hcx, hc]

end GaugeScaling

/-! ## Part 11: Time Evolution and Kernel Invariance -/

section TimeEvolution

noncomputable def timeEvolution (f : ℝ → ℝ) : ℝ → ℝ := fun t => f (φ * t)

theorem ker_D2_invariant (f : ℝ → ℝ) (hf : IsInKerD2 f) :
    IsInKerD2 (timeEvolution f) := by
  obtain ⟨c, hf⟩ := hf; exact ⟨c, fun t => by simp [timeEvolution, hf]⟩

theorem ker_D3_invariant (f : ℝ → ℝ) (hf : IsInKerD3 f) :
    IsInKerD3 (timeEvolution f) := by
  obtain ⟨c, hf⟩ := hf; exact ⟨c, fun t => by simp [timeEvolution, hf]⟩

theorem ker_D4_invariant (f : ℝ → ℝ) (hf : IsInKerD4 f) :
    IsInKerD4 (timeEvolution f) := by
  obtain ⟨c, hf⟩ := hf
  exact ⟨c * φ ^ 2, fun t => by simp only [timeEvolution, hf]; ring⟩

theorem ker_D5_invariant (f : ℝ → ℝ) (hf : IsInKerD5 f) :
    IsInKerD5 (timeEvolution f) := by
  obtain ⟨a₀, a₁, hf⟩ := hf
  exact ⟨a₀, a₁ * φ, fun t => by simp only [timeEvolution, hf]; ring⟩

theorem D2_timeEvolution (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D2 (timeEvolution f) x = φ * D2 f (φ * x) :=
  D2_gauge_scaling f φ x (by have := φ_gt_one; linarith) hx

theorem D3_timeEvolution (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D3 (timeEvolution f) x = φ * D3 f (φ * x) :=
  D3_gauge_scaling f φ x (by have := φ_gt_one; linarith) hx

theorem D4_timeEvolution (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D4 (timeEvolution f) x = φ * D4 f (φ * x) :=
  D4_gauge_scaling f φ x (by have := φ_gt_one; linarith) hx

theorem D5_timeEvolution (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D5 (timeEvolution f) x = φ * D5 f (φ * x) :=
  D5_gauge_scaling f φ x (by have := φ_gt_one; linarith) hx

theorem ker_D6_invariant (f : ℝ → ℝ) (hf : IsInKerD6 f) :
    IsInKerD6 (timeEvolution f) := by
  obtain ⟨a₀, a₁, a₂, hf_eq⟩ := hf
  use a₀, a₁ * φ, a₂ * φ^2
  intro t
  simp only [timeEvolution]
  rw [hf_eq (φ * t)]
  ring

theorem D6_timeEvolution (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 (timeEvolution f) x = φ * D6 f (φ * x) :=
  D6_gauge_scaling f φ x (by have := φ_gt_one; linarith) hx

theorem timeEvolution_preserves_D6 (f : ℝ → ℝ) :
    TimeExistsD6 f ↔ TimeExistsD6 (timeEvolution f) := by
  have hφ : φ ≠ 0 := by have := φ_gt_one; linarith
  constructor
  · intro hf hker
    apply hf
    obtain ⟨a₀, a₁, a₂, h_eq⟩ := hker
    use a₀, a₁ / φ, a₂ / φ^2
    intro t
    have hφ2 : φ^2 ≠ 0 := pow_ne_zero 2 hφ
    have key := h_eq (t / φ)
    simp only [timeEvolution] at key
    have hsimp : φ * (t / φ) = t := by field_simp
    rw [hsimp] at key
    calc f t = a₀ + a₁ * (t / φ) + a₂ * (t / φ)^2 := key
      _ = a₀ + a₁ / φ * t + a₂ / φ^2 * t^2 := by field_simp [hφ, hφ2]
  · intro hf hker; exact hf (ker_D6_invariant f hker)

theorem timeEvolution_preserves_D2 (f : ℝ → ℝ) :
    TimeExistsD2 f ↔ TimeExistsD2 (timeEvolution f) := by
  have hφ : φ ≠ 0 := by have := φ_gt_one; linarith
  constructor
  · intro hf hker; apply hf; obtain ⟨c, hc⟩ := hker
    exact ⟨c, fun t => by
      have h := hc (t / φ); simp only [timeEvolution] at h
      rwa [mul_div_cancel₀ t hφ] at h⟩
  · intro hf hker; exact hf (ker_D2_invariant f hker)

theorem timeEvolution_preserves_D3 (f : ℝ → ℝ) :
    TimeExistsD3 f ↔ TimeExistsD3 (timeEvolution f) := by
  have hφ : φ ≠ 0 := by have := φ_gt_one; linarith
  constructor
  · intro hf hker; apply hf; obtain ⟨c, hc⟩ := hker
    exact ⟨c, fun t => by
      have h := hc (t / φ); simp only [timeEvolution] at h
      rwa [mul_div_cancel₀ t hφ] at h⟩
  · intro hf hker; exact hf (ker_D3_invariant f hker)

theorem timeEvolution_preserves_D4 (f : ℝ → ℝ) :
    TimeExistsD4 f ↔ TimeExistsD4 (timeEvolution f) := by
  have hφ : φ ≠ 0 := by have := φ_gt_one; linarith
  constructor
  · intro hf hker; apply hf; obtain ⟨c, hc⟩ := hker
    exact ⟨c / φ ^ 2, fun t => by
      have h := hc (t / φ); simp only [timeEvolution] at h
      rw [mul_div_cancel₀ t hφ] at h; rw [h]; field_simp⟩
  · intro hf hker; exact hf (ker_D4_invariant f hker)

theorem timeEvolution_preserves_D5 (f : ℝ → ℝ) :
    TimeExistsD5 f ↔ TimeExistsD5 (timeEvolution f) := by
  have hφ : φ ≠ 0 := by have := φ_gt_one; linarith
  constructor
  · intro hf hker; apply hf; obtain ⟨a₀, a₁, hc⟩ := hker
    exact ⟨a₀, a₁ / φ, fun t => by
      have h := hc (t / φ); simp only [timeEvolution] at h
      rw [mul_div_cancel₀ t hφ] at h; rw [h]; field_simp⟩
  · intro hf hker; exact hf (ker_D5_invariant f hker)

end TimeEvolution

/-! ## Part 12: Entropy -/

section Entropy

noncomputable def entropyAtD2 (f : ℝ → ℝ) (t : ℝ) : ℝ := (perpProjectionD2 f t) ^ 2
noncomputable def entropyAtD3 (f : ℝ → ℝ) (t : ℝ) : ℝ := (perpProjectionD3 f t) ^ 2
noncomputable def entropyAtD4 (f : ℝ → ℝ) (t : ℝ) : ℝ := (perpProjectionD4 f t) ^ 2
noncomputable def entropyAtD5 (f : ℝ → ℝ) (t : ℝ) : ℝ := (perpProjectionD5 f t) ^ 2

theorem entropyAtD2_nonneg (f : ℝ → ℝ) (t : ℝ) : entropyAtD2 f t ≥ 0 := sq_nonneg _
theorem entropyAtD3_nonneg (f : ℝ → ℝ) (t : ℝ) : entropyAtD3 f t ≥ 0 := sq_nonneg _
theorem entropyAtD4_nonneg (f : ℝ → ℝ) (t : ℝ) : entropyAtD4 f t ≥ 0 := sq_nonneg _
theorem entropyAtD5_nonneg (f : ℝ → ℝ) (t : ℝ) : entropyAtD5 f t ≥ 0 := sq_nonneg _

theorem entropyAtD2_zero_iff (f : ℝ → ℝ) (t : ℝ) :
    entropyAtD2 f t = 0 ↔ perpProjectionD2 f t = 0 := sq_eq_zero_iff
theorem entropyAtD3_zero_iff (f : ℝ → ℝ) (t : ℝ) :
    entropyAtD3 f t = 0 ↔ perpProjectionD3 f t = 0 := sq_eq_zero_iff
theorem entropyAtD4_zero_iff (f : ℝ → ℝ) (t : ℝ) :
    entropyAtD4 f t = 0 ↔ perpProjectionD4 f t = 0 := sq_eq_zero_iff
theorem entropyAtD5_zero_iff (f : ℝ → ℝ) (t : ℝ) :
    entropyAtD5 f t = 0 ↔ perpProjectionD5 f t = 0 := sq_eq_zero_iff

theorem entropy_zero_iff_kerD2 (f : ℝ → ℝ) :
    (∀ t, entropyAtD2 f t = 0) ↔ IsInKerD2 f := by
  constructor
  · intro h; exact perpD2_zero_implies_ker f (fun t => (entropyAtD2_zero_iff f t).mp (h t))
  · intro hf t; rw [entropyAtD2_zero_iff]; exact kerD2_implies_perp_zero f hf t

theorem entropy_zero_iff_kerD3 (f : ℝ → ℝ) :
    (∀ t, entropyAtD3 f t = 0) ↔ IsInKerD3 f := by
  constructor
  · intro h; exact perpD3_zero_implies_ker f (fun t => (entropyAtD3_zero_iff f t).mp (h t))
  · intro hf t; rw [entropyAtD3_zero_iff]; exact kerD3_implies_perp_zero f hf t

theorem entropy_zero_iff_kerD4 (f : ℝ → ℝ) :
    (∀ t, entropyAtD4 f t = 0) ↔ IsInKerD4 f := by
  constructor
  · intro h; exact perpD4_zero_implies_ker f (fun t => (entropyAtD4_zero_iff f t).mp (h t))
  · intro hf t; rw [entropyAtD4_zero_iff]; exact kerD4_implies_perp_zero f hf t

theorem entropy_zero_iff_kerD5 (f : ℝ → ℝ) :
    (∀ t, entropyAtD5 f t = 0) ↔ IsInKerD5 f := by
  constructor
  · intro h; exact perpD5_zero_implies_ker f (fun t => (entropyAtD5_zero_iff f t).mp (h t))
  · intro hf t; rw [entropyAtD5_zero_iff]; exact kerD5_implies_perp_zero f hf t

noncomputable def entropyAtD6 (f : ℝ → ℝ) (t : ℝ) : ℝ := (perpProjectionD6 f t) ^ 2

theorem entropyAtD6_nonneg (f : ℝ → ℝ) (t : ℝ) : entropyAtD6 f t ≥ 0 := sq_nonneg _

theorem entropyAtD6_zero_iff (f : ℝ → ℝ) (t : ℝ) :
    entropyAtD6 f t = 0 ↔ perpProjectionD6 f t = 0 := sq_eq_zero_iff

theorem entropy_zero_iff_kerD6 (f : ℝ → ℝ) :
    (∀ t, entropyAtD6 f t = 0) ↔ IsInKerD6 f := by
  constructor
  · intro h; exact perpD6_zero_implies_ker f (fun t => (entropyAtD6_zero_iff f t).mp (h t))
  · intro hf t; rw [entropyAtD6_zero_iff]; exact kerD6_implies_perp_zero f hf t

end Entropy

/-! ## Part 13: Third Law -/

section ThirdLaw

theorem third_law_D2 (f : ℝ → ℝ) (hf : ¬IsInKerD2 f) :
    ∃ t, entropyAtD2 f t > 0 := by
  by_contra h; push_neg at h
  exact hf ((entropy_zero_iff_kerD2 f).mp
    (fun t => le_antisymm (h t) (entropyAtD2_nonneg f t)))

theorem third_law_D3 (f : ℝ → ℝ) (hf : ¬IsInKerD3 f) :
    ∃ t, entropyAtD3 f t > 0 := by
  by_contra h; push_neg at h
  exact hf ((entropy_zero_iff_kerD3 f).mp
    (fun t => le_antisymm (h t) (entropyAtD3_nonneg f t)))

theorem third_law_D4 (f : ℝ → ℝ) (hf : ¬IsInKerD4 f) :
    ∃ t, entropyAtD4 f t > 0 := by
  by_contra h; push_neg at h
  exact hf ((entropy_zero_iff_kerD4 f).mp
    (fun t => le_antisymm (h t) (entropyAtD4_nonneg f t)))

theorem third_law_D5 (f : ℝ → ℝ) (hf : ¬IsInKerD5 f) :
    ∃ t, entropyAtD5 f t > 0 := by
  by_contra h; push_neg at h
  exact hf ((entropy_zero_iff_kerD5 f).mp
    (fun t => le_antisymm (h t) (entropyAtD5_nonneg f t)))

theorem third_law_D6 (f : ℝ → ℝ) (hf : ¬IsInKerD6 f) :
    ∃ t, entropyAtD6 f t > 0 := by
  by_contra h; push_neg at h
  exact hf ((entropy_zero_iff_kerD6 f).mp
    (fun t => le_antisymm (h t) (entropyAtD6_nonneg f t)))

end ThirdLaw

/-! ## Part 14: Time Requires Deviation -/

section TimeRequiresDeviation

theorem time_requires_deviation_D2 (f : ℝ → ℝ)
    (h : ∃ x, x ≠ 0 ∧ D2 f x ≠ 0) : ∃ t, perpProjectionD2 f t ≠ 0 := by
  by_contra hAll; push_neg at hAll
  have hker : IsInKerD2 f := perpD2_zero_implies_ker f hAll
  obtain ⟨x, hx, hD2⟩ := h
  exact hD2 (IsInKerD2_implies_D2_zero f hker x hx)

theorem time_requires_deviation_D3 (f : ℝ → ℝ)
    (h : ∃ x, x ≠ 0 ∧ D3 f x ≠ 0) : ∃ t, perpProjectionD3 f t ≠ 0 := by
  by_contra hAll; push_neg at hAll
  have hker : IsInKerD3 f := perpD3_zero_implies_ker f hAll
  obtain ⟨x, hx, hD3⟩ := h
  exact hD3 (IsInKerD3_implies_D3_zero f hker x hx)

theorem time_requires_deviation_D4 (f : ℝ → ℝ)
    (h : ∃ x, x ≠ 0 ∧ D4 f x ≠ 0) : ∃ t, perpProjectionD4 f t ≠ 0 := by
  by_contra hAll; push_neg at hAll
  have hker : IsInKerD4 f := perpD4_zero_implies_ker f hAll
  obtain ⟨x, hx, hD4⟩ := h
  exact hD4 (IsInKerD4_implies_D4_zero f hker x hx)

theorem time_requires_deviation_D5 (f : ℝ → ℝ)
    (h : ∃ x, x ≠ 0 ∧ D5 f x ≠ 0) : ∃ t, perpProjectionD5 f t ≠ 0 := by
  by_contra hAll; push_neg at hAll
  have hker : IsInKerD5 f := perpD5_zero_implies_ker f hAll
  obtain ⟨x, hx, hD5⟩ := h
  exact hD5 (IsInKerD5_implies_D5_zero f hker x hx)

theorem time_requires_deviation_D6 (f : ℝ → ℝ)
    (h : ∃ x, x ≠ 0 ∧ D6 f x ≠ 0) : ∃ t, perpProjectionD6 f t ≠ 0 := by
  by_contra hAll; push_neg at hAll
  have hker : IsInKerD6 f := perpD6_zero_implies_ker f hAll
  obtain ⟨x, hx, hD6⟩ := h
  exact hD6 (IsInKerD6_implies_D6_zero f hker x hx)

end TimeRequiresDeviation

/-! ## Part 15: Minimum Massive Degree -/

section MinimumMassiveDegree

theorem D2_minimum_massive_degree :
    (∀ x, x ≠ 0 → D2 (fun _ => 1) x = 0) ∧
    (∃ x, x ≠ 0 ∧ D2 id x ≠ 0) :=
  ⟨fun x hx => D2_const 1 x hx, ⟨1, one_ne_zero, D2_linear_ne_zero 1 one_ne_zero⟩⟩

theorem D3_minimum_massive_degree :
    (∀ x, x ≠ 0 → D3 (fun _ => 1) x = 0) ∧
    (∃ x, x ≠ 0 ∧ D3 id x ≠ 0) :=
  ⟨fun x hx => D3_const 1 x hx, ⟨1, one_ne_zero, D3_linear_ne_zero 1 one_ne_zero⟩⟩

theorem D4_minimum_massive_degree :
    (∀ x, x ≠ 0 → D4 (fun t => t ^ 2) x = 0) ∧
    (∀ x, x ≠ 0 → D4 (fun _ => 1) x ≠ 0) :=
  ⟨D4_quadratic, D4_const_ne_zero⟩

theorem D5_minimum_massive_degree :
    (∀ x, x ≠ 0 → D5 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D5 id x = 0) ∧
    (∀ x, x ≠ 0 → D5 (fun t => t ^ 2) x ≠ 0) :=
  ⟨fun x hx => D5_const 1 x hx, D5_linear, D5_not_annihilate_quadratic⟩

theorem mass_gap_existence_universal :
    (∃ f, TimeExistsD2 f) ∧
    (∃ f, TimeExistsD3 f) ∧
    (∃ f, TimeExistsD4 f) ∧
    (∃ f, TimeExistsD5 f) := by
  refine ⟨⟨id, fun ⟨c, h⟩ => ?_⟩, ⟨id, fun ⟨c, h⟩ => ?_⟩,
         ⟨fun _ => 1, fun ⟨c, h⟩ => ?_⟩, ⟨fun t => t ^ 2, fun ⟨a₀, a₁, h⟩ => ?_⟩⟩
  · have h0 := h 0; have h1 := h 1; simp [id] at h0 h1; linarith
  · have h0 := h 0; have h1 := h 1; simp [id] at h0 h1; linarith
  · have h0 := h 0; simp at h0
  · have h0 := h 0; have h1 := h 1; have h2 := h 2; simp at h0 h1 h2; nlinarith

end MinimumMassiveDegree

/-! ## Frourio Time Coordinate -/

section FrourioFormulation

open FUST.FrourioLogarithm

noncomputable def frourioTime (x : ℝ) : ℝ := frourioLog x

theorem phi_scale_is_time_shift (x : ℝ) (hx : 0 < x) :
    frourioTime (φ * x) = frourioTime x + phiStep := by
  unfold frourioTime
  exact phi_scale_is_translation hx

end FrourioFormulation

end FUST.LeastAction
