import FUST.FζOperator

/-!
# Time Structure from φ-Scaling

Time evolution f ↦ f(φ·) derived from Fζ translation symmetry.
- φ/ψ duality: φ·|ψ| = 1, φ > 1 > |ψ|
- Kernel: IsInKerFζ f ↔ ∀ z, Fζ f z = 0
- Action functional: |Fζ f|² with Lagrangian equivariance L[f(φ·)](z) = L[f](φz)
- Entropy: |Fζ f|² measures departure from ker(Fζ)
- Planck second: 1/(20√15) from eigenvalue norm 6000
-/

namespace FUST.TimeStructure

open FUST.FζOperator FUST.DζOperator Complex

/-! ## φ/ψ Duality

Algebraic properties of the golden ratio pair: φ·|ψ| = 1, φ > 1 > |ψ|. -/

theorem phi_mul_abs_psi : φ * |ψ| = 1 := by
  have hpsi_neg : ψ < 0 := by
    have h : ψ = (1 - Real.sqrt 5) / 2 := rfl
    have hsqrt5_gt_1 : Real.sqrt 5 > 1 := by
      calc Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5)
        _ = 1 := Real.sqrt_one
    simp only [h]; linarith
  rw [abs_of_neg hpsi_neg]
  have h : φ * (-ψ) = -(φ * ψ) := by ring
  rw [h, phi_mul_psi]; ring

theorem phi_pow_gt_one (n : ℕ) (hn : n ≥ 1) : φ^n > 1 :=
  one_lt_pow₀ φ_gt_one (Nat.one_le_iff_ne_zero.mp hn)

/-! ## Kernel Membership -/

/-- f ∈ ker(Fζ) iff Fζ f = 0 everywhere -/
def IsInKerFζ (f : ℂ → ℂ) : Prop := ∀ z, Fζ f z = 0

theorem IsInKerFζ_const : IsInKerFζ (fun _ => 1) := Fζ_kernel_const

theorem IsInKerFζ_quad : IsInKerFζ (fun w => w ^ 2) := Fζ_kernel_quad

theorem IsInKerFζ_cube : IsInKerFζ (fun w => w ^ 3) := Fζ_kernel_cube

theorem IsInKerFζ_fourth : IsInKerFζ (fun w => w ^ 4) := Fζ_kernel_fourth

theorem IsInKerFζ_vanish_mod6_0 (k : ℕ) : IsInKerFζ (fun w => w ^ (6 * k)) :=
  Fζ_vanish_mod6_0 k

theorem IsInKerFζ_vanish_mod6_2 (k : ℕ) : IsInKerFζ (fun w => w ^ (6 * k + 2)) :=
  Fζ_vanish_mod6_2 k

theorem IsInKerFζ_vanish_mod6_3 (k : ℕ) : IsInKerFζ (fun w => w ^ (6 * k + 3)) :=
  Fζ_vanish_mod6_3 k

theorem IsInKerFζ_vanish_mod6_4 (k : ℕ) : IsInKerFζ (fun w => w ^ (6 * k + 4)) :=
  Fζ_vanish_mod6_4 k

theorem IsInKerFζ_smul (c : ℂ) (f : ℂ → ℂ) (hf : IsInKerFζ f) :
    IsInKerFζ (fun w => c * f w) := by
  intro z; rw [Fζ_const_smul, hf z, mul_zero]

/-! ## Action Functional

|Fζ f|² is non-negative with minimum at ker(Fζ). -/

noncomputable def FζLagrangian (f : ℂ → ℂ) (z : ℂ) : ℝ := Complex.normSq (Fζ f z)

theorem Fζ_lagrangian_nonneg (f : ℂ → ℂ) (z : ℂ) : FζLagrangian f z ≥ 0 :=
  Complex.normSq_nonneg _

theorem Fζ_lagrangian_zero_iff (f : ℂ → ℂ) (z : ℂ) :
    FζLagrangian f z = 0 ↔ Fζ f z = 0 := Complex.normSq_eq_zero

theorem Fζ_lagrangian_ker_zero (f : ℂ → ℂ) (hf : IsInKerFζ f) (z : ℂ) :
    FζLagrangian f z = 0 := by
  rw [Fζ_lagrangian_zero_iff]; exact hf z

/-! ## Time Evolution

f ↦ f(φ·) from Fζ translation symmetry: Fζ[f(c·)](z) = Fζ[f](cz). -/

section TimeEvolution

noncomputable def timeEvolution (f : ℂ → ℂ) : ℂ → ℂ := fun t => f ((↑φ : ℂ) * t)

private theorem phi_complex_ne_zero : (↑φ : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt phi_pos)

theorem ker_Fζ_invariant (f : ℂ → ℂ) (hf : IsInKerFζ f) :
    IsInKerFζ (timeEvolution f) := by
  intro z; change Fζ (fun t => f ((↑φ : ℂ) * t)) z = 0
  rw [Fζ_translate]; exact hf _

private theorem timeEvolution_Fζ (f : ℂ → ℂ) (z : ℂ) :
    Fζ (timeEvolution f) z = Fζ f ((↑φ : ℂ) * z) := by
  change Fζ (fun t => f ((↑φ : ℂ) * t)) z = _; exact Fζ_translate f _ z

theorem timeEvolution_preserves_Fζ (f : ℂ → ℂ) :
    ¬ IsInKerFζ f ↔ ¬ IsInKerFζ (timeEvolution f) := by
  constructor
  · intro hf hker; apply hf; intro z
    have key := hker (z / (↑φ : ℂ))
    rw [timeEvolution_Fζ] at key
    have : (↑φ : ℂ) * (z / (↑φ : ℂ)) = z := mul_div_cancel₀ z phi_complex_ne_zero
    rwa [this] at key
  · intro hf hker; exact hf (ker_Fζ_invariant f hker)

theorem monomial_amplification (n : ℕ) (t : ℂ) :
    timeEvolution (fun s => s^n) t = (↑φ : ℂ)^n * t^n := by
  simp only [timeEvolution]; ring

theorem Fζ_gauge_scaling (f : ℂ → ℂ) (c z : ℂ) :
    Fζ (fun t => f (c * t)) z = Fζ f (c * z) := Fζ_translate f c z

/-- |Fζ f|² is a Lagrangian: equivariant under time evolution L[f(φ·)](z) = L[f](φz) -/
theorem lagrangian_phi_equivariant (f : ℂ → ℂ) (z : ℂ) :
    FζLagrangian (timeEvolution f) z = FζLagrangian f ((↑φ : ℂ) * z) := by
  simp only [FζLagrangian]; congr 1; exact timeEvolution_Fζ f z

end TimeEvolution

/-! ## Fζ Nonzero Implies Non-Kernel -/

theorem Fζ_nonzero_implies_time (f : ℂ → ℂ) (z : ℂ) (hFζ : Fζ f z ≠ 0) :
    ¬ IsInKerFζ f := by
  intro hker; exact hFζ (hker z)

/-! ## Entropy and Third Law

|Fζ f|² measures departure from ker(Fζ).
f ∉ ker(Fζ) ⟹ ∃z: entropy > 0. -/

section Entropy

noncomputable def entropyAtFζ (f : ℂ → ℂ) (z : ℂ) : ℝ := FζLagrangian f z

theorem entropyAtFζ_nonneg (f : ℂ → ℂ) (z : ℂ) : entropyAtFζ f z ≥ 0 :=
  Fζ_lagrangian_nonneg f z

theorem entropyAtFζ_zero_iff (f : ℂ → ℂ) (z : ℂ) :
    entropyAtFζ f z = 0 ↔ Fζ f z = 0 := Fζ_lagrangian_zero_iff f z

theorem entropy_zero_iff_kerFζ (f : ℂ → ℂ) :
    (∀ z, entropyAtFζ f z = 0) ↔ IsInKerFζ f := by
  constructor
  · intro h z; exact (entropyAtFζ_zero_iff f z).mp (h z)
  · intro hf z; exact (entropyAtFζ_zero_iff f z).mpr (hf z)

theorem third_law_Fζ (f : ℂ → ℂ) (hf : ¬IsInKerFζ f) :
    ∃ z, entropyAtFζ f z > 0 := by
  by_contra h; push_neg at h
  exact hf ((entropy_zero_iff_kerFζ f).mp
    (fun z => le_antisymm (h z) (entropyAtFζ_nonneg f z)))

end Entropy

/-! ## Planck Second

|temporal Fζ eigenvalue|² = 6000, Planck second = 1/(20√15). -/

section PlanckSecond

private theorem sqrt5_sq : (Real.sqrt 5)^2 = 5 :=
  Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)

private theorem sqrt15_sq : (Real.sqrt 15)^2 = 15 :=
  Real.sq_sqrt (by norm_num : (15 : ℝ) ≥ 0)

private theorem sqrt15_pos : Real.sqrt 15 > 0 :=
  Real.sqrt_pos.mpr (by norm_num : (15 : ℝ) > 0)

noncomputable def temporalEigenNormSq : ℝ := 6000

theorem temporalEigenNormSq_eq : temporalEigenNormSq = 6000 := rfl

theorem temporalEigenNormSq_from_channels :
    temporalEigenNormSq = (20 * Real.sqrt 15)^2 := by
  simp only [temporalEigenNormSq]
  rw [mul_pow, show (20 : ℝ)^2 = 400 from by norm_num, sqrt15_sq]
  norm_num

theorem temporalEigenNormSq_pos : temporalEigenNormSq > 0 := by
  simp only [temporalEigenNormSq]; norm_num

noncomputable def planckSecondSq : ℝ := 1 / temporalEigenNormSq

theorem planckSecondSq_eq : planckSecondSq = 1 / 6000 := rfl

theorem planckSecondSq_pos : planckSecondSq > 0 := by
  simp only [planckSecondSq, temporalEigenNormSq]; norm_num

noncomputable def planckSecond : ℝ := 1 / (20 * Real.sqrt 15)

theorem planckSecond_pos : planckSecond > 0 := by
  simp only [planckSecond]
  exact div_pos one_pos (mul_pos (by norm_num : (20 : ℝ) > 0) sqrt15_pos)

theorem planckSecond_sq : planckSecond ^ 2 = planckSecondSq := by
  simp only [planckSecond, planckSecondSq, temporalEigenNormSq]
  rw [div_pow, one_pow, mul_pow, show (20 : ℝ)^2 = 400 from by norm_num, sqrt15_sq]
  norm_num

end PlanckSecond

/-! ## Planck second algebraic decomposition -/

theorem planckSecondSq_from_sqrt5 :
    planckSecondSq = 1 / (5 * (2 * Real.sqrt 5)) ^ 2 / 12 := by
  simp only [planckSecondSq, temporalEigenNormSq]
  rw [mul_pow, show (5 : ℝ)^2 = 25 from by norm_num,
      show (2 * Real.sqrt 5)^2 = 4 * (Real.sqrt 5)^2 from by ring,
      Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
  norm_num

theorem temporalEigenNormSq_AF_decomposition :
    temporalEigenNormSq = Complex.normSq AF_coeff * (5 * (2 * Real.sqrt 5))^2 := by
  simp only [temporalEigenNormSq, AF_coeff_normSq]
  rw [mul_pow, show (5 : ℝ)^2 = 25 from by norm_num,
      show (2 * Real.sqrt 5)^2 = 4 * (Real.sqrt 5)^2 from by ring,
      Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
  norm_num

end FUST.TimeStructure
