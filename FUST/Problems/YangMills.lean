import FUST.Physics.Gravity
import FUST.Physics.MassGap
import FUST.Physics.LeastAction
import FUST.Physics.WaveEquation
import Mathlib.LinearAlgebra.Matrix.Trace

namespace FUST.YangMills

open LinearMap (BilinForm)
open LieAlgebra.Orthogonal Matrix FUST
open FUST.Physics.Lorentz FUST.Physics.Poincare FUST.Physics.Gravity

/-! ## Killing form on so(3,1) via matrix trace -/

noncomputable def killingTrace (A B : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) : ℝ :=
  Matrix.trace ((A : Matrix I4 I4 ℝ) * (B : Matrix I4 I4 ℝ))

theorem killingTrace_comm (A B : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) :
    killingTrace A B = killingTrace B A := by
  unfold killingTrace; exact Matrix.trace_mul_comm _ _

theorem killingTrace_add_left (A B C : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) :
    killingTrace (A + B) C = killingTrace A C + killingTrace B C := by
  unfold killingTrace
  simp only [Submodule.coe_add, Matrix.add_mul, Matrix.trace_add]

theorem killingTrace_add_right (A B C : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) :
    killingTrace A (B + C) = killingTrace A B + killingTrace A C := by
  unfold killingTrace
  simp only [Submodule.coe_add, Matrix.mul_add, Matrix.trace_add]

theorem killingTrace_lie_invariant (A B C : Matrix I4 I4 ℝ) :
    Matrix.trace ((A * B - B * A) * C) =
    Matrix.trace (A * (B * C - C * B)) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
  rw [show B * (A * C) = B * A * C from (Matrix.mul_assoc B A C).symm,
      show A * (C * B) = A * C * B from (Matrix.mul_assoc A C B).symm]
  linarith [Matrix.trace_mul_cycle A C B]

/-! ## Yang-Mills action -/

noncomputable def ymAction (ω : I4 → so' (Fin 3) (Fin 1) ℝ) : ℝ :=
  ∑ μ : I4, ∑ ν : I4,
    killingTrace
      ⟨(curvature ω μ ν).val, (curvature ω μ ν).prop⟩
      ⟨(curvature ω μ ν).val, (curvature ω μ ν).prop⟩

theorem ymAction_flat (ω : I4 → so' (Fin 3) (Fin 1) ℝ)
    (hflat : ∀ μ ν, curvature ω μ ν = 0) :
    ymAction ω = 0 := by
  unfold ymAction killingTrace
  simp only [hflat]; simp [Matrix.trace_zero]

theorem constant_connection_flat (A : so' (Fin 3) (Fin 1) ℝ) :
    ∀ μ ν : I4, curvature (fun _ => A) μ ν = 0 := by
  intro μ ν; unfold curvature; exact lie_self A

theorem ymAction_const_zero (A : so' (Fin 3) (Fin 1) ℝ) :
    ymAction (fun _ => A) = 0 :=
  ymAction_flat _ (constant_connection_flat A)

/-! ## Gauge invariance -/

theorem gauge_invariance_ym
    (F g ginv : Matrix I4 I4 ℝ) (hginv : ginv * g = 1) :
    Matrix.trace (g * F * ginv * (g * F * ginv)) =
    Matrix.trace (F * F) := by
  have key : g * F * ginv * (g * F * ginv) = g * (F * F) * ginv := by
    calc g * F * ginv * (g * F * ginv)
        = g * F * (ginv * g) * F * ginv := by
          simp only [Matrix.mul_assoc]
      _ = g * F * 1 * F * ginv := by rw [hginv]
      _ = g * (F * F) * ginv := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [key]
  calc Matrix.trace (g * (F * F) * ginv)
      = Matrix.trace (ginv * (g * (F * F))) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (ginv * g * (F * F)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (1 * (F * F)) := by rw [hginv]
    _ = Matrix.trace (F * F) := by rw [Matrix.one_mul]

/-! ## Hamiltonian -/

noncomputable def curvatureEnergy (A : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) : ℝ :=
  killingTrace A A

noncomputable def ymHamiltonian (ω : I4 → so' (Fin 3) (Fin 1) ℝ) : ℝ :=
  ∑ μ : I4, ∑ ν : I4,
    curvatureEnergy ⟨(curvature ω μ ν).val, (curvature ω μ ν).prop⟩

theorem ymHamiltonian_eq_action (ω : I4 → so' (Fin 3) (Fin 1) ℝ) :
    ymHamiltonian ω = ymAction ω := rfl

theorem ymHamiltonian_vacuum (ω : I4 → so' (Fin 3) (Fin 1) ℝ)
    (hflat : ∀ μ ν, curvature ω μ ν = 0) :
    ymHamiltonian ω = 0 :=
  ymAction_flat ω hflat

theorem curvatureEnergy_antisymm (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) :
    curvatureEnergy ⟨(curvature ω μ ν).val, (curvature ω μ ν).prop⟩ =
    curvatureEnergy ⟨(curvature ω ν μ).val, (curvature ω ν μ).prop⟩ := by
  unfold curvatureEnergy killingTrace
  have hval : (curvature ω μ ν).val = -(curvature ω ν μ).val := by
    rw [curvature_antisymm]; rfl
  simp only [hval, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-! ## Spectrum from finite-dimensional algebra -/

theorem spacetime_finite : Fintype.card I4 = 4 := by
  simp [I4, Fintype.card_sum, Fintype.card_fin]

theorem curvature_components :
    Nat.choose (Fintype.card I4) 2 = 6 := by
  rw [spacetime_finite]; decide

theorem bianchi_constraints :
    Nat.choose (Fintype.card I4) 3 = 4 := by
  rw [spacetime_finite]; decide

theorem curvature_total_dof :
    Nat.choose (Fintype.card I4) 2 *
    Module.finrank ℝ (so' (Fin 3) (Fin 1) ℝ).toSubmodule = 36 := by
  rw [curvature_components, finrank_so31]

theorem gauge_dof :
    Module.finrank ℝ (so' (Fin 3) (Fin 1) ℝ).toSubmodule = 6 := finrank_so31

theorem physical_dof :
    Module.finrank ℝ (I4 → (so' (Fin 3) (Fin 1) ℝ).toSubmodule) -
    Module.finrank ℝ (so' (Fin 3) (Fin 1) ℝ).toSubmodule = 18 := by
  rw [finrank_connection, finrank_so31]

theorem zero_is_vacuum :
    ymHamiltonian (fun _ => (0 : so' (Fin 3) (Fin 1) ℝ)) = 0 :=
  ymHamiltonian_vacuum _ (fun μ ν => by unfold curvature; simp [lie_self])

theorem curvature_diagonal_zero (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ : I4) :
    curvature ω μ μ = 0 := by
  unfold curvature; exact lie_self (ω μ)

theorem curvatureEnergy_diagonal_zero (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ : I4) :
    curvatureEnergy ⟨(curvature ω μ μ).val, (curvature ω μ μ).prop⟩ = 0 := by
  unfold curvatureEnergy killingTrace
  have h := curvature_diagonal_zero ω μ
  simp [h]

/-! ## Algebraic confinement via Fζ -/

section AlgebraicConfinement

open FUST FUST.FζOperator FUST.Zeta6 FUST.TimeStructure FUST.LeastAction FUST.WaveEquation

theorem kerFζ_add_closed (f g : ℂ → ℂ) (hf : IsInKerFζ f) (hg : IsInKerFζ g) :
    IsInKerFζ (fun t => f t + g t) := by
  intro z; rw [Fζ_additive]; rw [hf z, hg z, add_zero]

-- Golden ratio power lemmas (ℝ)
private theorem phi5_r : φ^5 = 5*φ + 3 := by nlinarith [golden_ratio_property, phi_cubed]
private theorem psi5_r : ψ^5 = 5*ψ + 3 := by nlinarith [psi_sq, psi_cubed_alt]
private theorem phi10_r : φ^10 = 55*φ + 34 := by nlinarith [phi5_r, golden_ratio_property]
private theorem psi10_r : ψ^10 = 55*ψ + 34 := by nlinarith [psi5_r, psi_sq]
private theorem phi15_r : φ^15 = 610*φ + 377 := by
  nlinarith [phi5_r, phi10_r, golden_ratio_property]
private theorem psi15_r : ψ^15 = 610*ψ + 377 := by nlinarith [psi5_r, psi10_r, psi_sq]

private theorem phiS5_real :
    10 * φ^10 + (21 - 2*φ) * φ^5 - 50 + (9 + 2*φ) * ψ^5 + 10 * ψ^10 =
    50 * φ + 1295 := by
  rw [phi5_r, psi5_r, phi10_r, psi10_r]
  have hψ : ψ = 1 - φ := by linarith [phi_add_psi]
  rw [hψ]; nlinarith [golden_ratio_property]

private theorem phiA5_real :
    φ^15 - 4 * φ^10 + (3 + φ) * φ^5 - (3 + ψ) * ψ^5 + 4 * ψ^10 - ψ^15 =
    413 * Real.sqrt 5 := by
  rw [phi5_r, psi5_r, phi10_r, psi10_r, phi15_r, psi15_r]
  have hψ : ψ = 1 - φ := by linarith [phi_add_psi]
  rw [hψ, show 413 * Real.sqrt 5 = 413 * (φ - ψ) from by rw [phi_sub_psi], hψ]
  nlinarith [golden_ratio_property]

private theorem phiS5_complex :
    (10 * (↑φ : ℂ) ^ 10 + (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ 5 - 50 +
     (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ 5 + 10 * (↑ψ : ℂ) ^ 10) =
    ↑(50 * φ + 1295) := by
  rw [show (50 * φ + 1295 : ℝ) =
    10 * φ^10 + (21 - 2*φ) * φ^5 - 50 + (9 + 2*φ) * ψ^5 + 10 * ψ^10 from phiS5_real.symm]
  push_cast; ring

private theorem phiA5_complex :
    ((↑φ : ℂ) ^ 15 - 4 * (↑φ : ℂ) ^ 10 +
     (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ 5 -
     (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ 5 +
     4 * (↑ψ : ℂ) ^ 10 - (↑ψ : ℂ) ^ 15) =
    ↑(413 * Real.sqrt 5) := by
  rw [show (413 * Real.sqrt 5 : ℝ) =
    φ^15 - 4 * φ^10 + (3 + φ) * φ^5 - (3 + ψ) * ψ^5 + 4 * ψ^10 - ψ^15 from phiA5_real.symm]
  push_cast; ring

private theorem eigenCoeff5_re_pos :
    (-5 * ((↑φ : ℂ) ^ 15 - 4 * (↑φ : ℂ) ^ 10 +
      (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ 5 -
      (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ 5 +
      4 * (↑ψ : ℂ) ^ 10 - (↑ψ : ℂ) ^ 15) * AF_coeff +
     6 * (10 * (↑φ : ℂ) ^ 10 +
      (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ 5 - 50 +
      (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ 5 +
      10 * (↑ψ : ℂ) ^ 10)).re > 0 := by
  rw [phiA5_complex, phiS5_complex, AF_coeff_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re]
  norm_num
  linarith [phi_pos]

private theorem eigenCoeff5_ne_zero :
    (-5 * ((↑φ : ℂ) ^ 15 - 4 * (↑φ : ℂ) ^ 10 +
      (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ 5 -
      (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ 5 +
      4 * (↑ψ : ℂ) ^ 10 - (↑ψ : ℂ) ^ 15) * AF_coeff +
     6 * (10 * (↑φ : ℂ) ^ 10 +
      (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ 5 - 50 +
      (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ 5 +
      10 * (↑ψ : ℂ) ^ 10)) ≠ 0 := by
  intro h; have := eigenCoeff5_re_pos; rw [h] at this; simp at this

theorem Fζ_detects_fifth (z : ℂ) (hz : z ≠ 0) :
    Fζ (fun t => t ^ 5) z ≠ 0 := by
  have h := Fζ_eigenvalue_mod6_5 0 z
  norm_num at h; rw [h]
  have hne : (-(5 * ((↑φ : ℂ) ^ (3 * 5) - 4 * (↑φ : ℂ) ^ (2 * 5) +
     (3 + ↑φ) * (↑φ : ℂ) ^ 5 - (3 + ↑ψ) * (↑ψ : ℂ) ^ 5 +
     4 * (↑ψ : ℂ) ^ (2 * 5) - (↑ψ : ℂ) ^ (3 * 5)) * AF_coeff) +
    6 * (10 * (↑φ : ℂ) ^ (2 * 5) + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 5 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 5 + 10 * (↑ψ : ℂ) ^ (2 * 5))) ≠ 0 := by
    convert eigenCoeff5_ne_zero using 1; norm_num
  exact mul_ne_zero hne (pow_ne_zero 5 hz)

theorem ker_Fζ_not_subalgebra :
    ∃ f g : ℂ → ℂ, IsInKerFζ f ∧ IsInKerFζ g ∧ ¬IsInKerFζ (fun t => f t * g t) := by
  refine ⟨fun t => t ^ 2, fun t => t ^ 3, IsInKerFζ_quad, IsInKerFζ_cube, ?_⟩
  intro h
  have h5 : ∀ z, Fζ (fun t => t ^ 5) z = 0 := by
    intro z; convert h z using 2; ext t; ring
  exact Fζ_detects_fifth 1 one_ne_zero (h5 1)

end AlgebraicConfinement

/-! ## D₆ cubic eigenvalue -/

section D6Cubic

open FUST

/-- D₆(x³)(z) = (12/25) · z² -/
theorem D6_cubic_value (z : ℂ) (hz : z ≠ 0) :
    D6 (fun t => t^3) z = (12 / 25 : ℂ) * z^2 := by
  simp only [D6, N6]
  have hφ9 := phi_pow9_complex; have hφ6 := phi_pow6_complex
  have hφ3 := phi_cubed_complex; have hψ3 := psi_cubed_complex
  have hψ6 := psi_pow6_complex; have hψ9 := psi_pow9_complex
  have hcoef : (↑φ : ℂ)^9 - 3*(↑φ : ℂ)^6 + (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 +
      3*(↑ψ : ℂ)^6 - (↑ψ : ℂ)^9 = 12 * ((↑φ : ℂ) - ↑ψ) := by
    linear_combination hφ9 - 3 * hφ6 + hφ3 - hψ3 + 3 * hψ6 - hψ9
  have hnum : ((↑φ : ℂ)^3 * z)^3 - 3 * ((↑φ : ℂ)^2 * z)^3 + ((↑φ : ℂ) * z)^3 -
      ((↑ψ : ℂ) * z)^3 + 3 * ((↑ψ : ℂ)^2 * z)^3 - ((↑ψ : ℂ)^3 * z)^3 =
      12 * ((↑φ : ℂ) - ↑ψ) * z^3 := by
    have : ((↑φ : ℂ)^3 * z)^3 - 3 * ((↑φ : ℂ)^2 * z)^3 + ((↑φ : ℂ) * z)^3 -
        ((↑ψ : ℂ) * z)^3 + 3 * ((↑ψ : ℂ)^2 * z)^3 - ((↑ψ : ℂ)^3 * z)^3 =
        ((↑φ : ℂ)^9 - 3*(↑φ : ℂ)^6 + (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 +
         3*(↑ψ : ℂ)^6 - (↑ψ : ℂ)^9) * z^3 := by ring
    rw [hcoef] at this; exact this
  rw [hnum]
  have h_sub_eq : (↑φ : ℂ) - ↑ψ = ↑(Real.sqrt 5) := by
    rw [← Complex.ofReal_sub]; congr 1; exact phi_sub_psi
  unfold D6Denom; rw [h_sub_eq]
  have hsqrt5_ne : (↑(Real.sqrt 5) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  have hsqrt5_sq : (↑(Real.sqrt 5) : ℂ)^2 = 5 := by
    rw [← Complex.ofReal_pow]
    simp [Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
  have hsqrt5_pow4 : (↑(Real.sqrt 5) : ℂ)^4 = 25 := by
    have : (↑(Real.sqrt 5) : ℂ)^4 = ((↑(Real.sqrt 5) : ℂ)^2)^2 := by ring
    rw [this, hsqrt5_sq]; norm_num
  have hsqrt5_pow5 : (↑(Real.sqrt 5) : ℂ)^5 = 25 * ↑(Real.sqrt 5) := by
    have : (↑(Real.sqrt 5) : ℂ)^5 = (↑(Real.sqrt 5) : ℂ)^4 * ↑(Real.sqrt 5) := by ring
    rw [this, hsqrt5_pow4]
  rw [hsqrt5_pow5]; field_simp [hsqrt5_ne, hz]

/-- D₆(x³)(x₀) = Δ · x₀² for x₀ ∈ ℝ -/
theorem D6_cubic_eq_massGap_mul_sq (x₀ : ℝ) (hx₀ : x₀ ≠ 0) :
    D6 (fun t => t^3) x₀ = FUST.D6MinEigenvalue * x₀^2 := by
  have hx₀' : (↑x₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx₀
  rw [show (x₀ : ℂ) = ↑x₀ from rfl, D6_cubic_value (↑x₀) hx₀']
  simp only [FUST.D6MinEigenvalue]; push_cast; ring

end D6Cubic

/-! ## Main theorem: Yang-Mills mass gap -/

section MainTheorem

open FUST FUST.TimeStructure

/-- SU(3) mass gap: Δ = 12/25 > 0 from D₆, confinement from ker(Fζ) -/
theorem yangMills_massGap_SU3 :
    (∀ x : ℂ, x ≠ 0 →
      D6 (fun _ => 1) x = 0 ∧ D6 id x = 0 ∧ D6 (fun t => t ^ 2) x = 0) ∧
    (0 < FUST.D6MinEigenvalue ∧ FUST.D6MinEigenvalue = 12 / 25) ∧
    (∀ x₀ : ℝ, x₀ ≠ 0 →
      D6 (fun t => t ^ 3) (x₀ : ℂ) = (FUST.D6MinEigenvalue : ℂ) * (x₀ : ℂ) ^ 2) ∧
    (∃ f g, IsInKerFζ f ∧ IsInKerFζ g ∧ ¬IsInKerFζ (fun t => f t * g t)) :=
  ⟨fun x _hx => ⟨D6_const 1 x, D6_linear x, D6_quadratic x⟩,
   ⟨FUST.D6MinEigenvalue_pos, rfl⟩,
   D6_cubic_eq_massGap_mul_sq,
   ker_Fζ_not_subalgebra⟩

/-- SU(2) mass gap: D₅(x²) ≠ 0 -/
theorem yangMills_massGap_SU2 :
    (∀ x : ℂ, x ≠ 0 → D5 (fun _ => 1) x = 0 ∧ D5 id x = 0) ∧
    (∀ x : ℂ, x ≠ 0 → D5 (fun t => t ^ 2) x ≠ 0) :=
  ⟨fun x _hx => ⟨D5_const 1 x, D5_linear x⟩,
   D5_not_annihilate_quadratic⟩

/-- Yang-Mills mass gap: SU(3) has Δ = 12/25 > 0, SU(2) has D₅(x²) ≠ 0 -/
theorem yangMills_massGap :
    (0 < FUST.D6MinEigenvalue ∧ FUST.D6MinEigenvalue = 12 / 25 ∧
     (∀ x : ℂ, x ≠ 0 →
       D6 (fun _ => 1) x = 0 ∧ D6 id x = 0 ∧ D6 (fun t => t ^ 2) x = 0) ∧
     (∀ x₀ : ℝ, x₀ ≠ 0 →
       D6 (fun t => t ^ 3) (x₀ : ℂ) = (FUST.D6MinEigenvalue : ℂ) * (x₀ : ℂ) ^ 2)) ∧
    ((∀ x : ℂ, x ≠ 0 → D5 (fun _ => 1) x = 0 ∧ D5 id x = 0) ∧
     (∀ x : ℂ, x ≠ 0 → D5 (fun t => t ^ 2) x ≠ 0)) ∧
    (∃ f g, IsInKerFζ f ∧ IsInKerFζ g ∧ ¬IsInKerFζ (fun t => f t * g t)) :=
  ⟨⟨FUST.D6MinEigenvalue_pos, rfl,
    fun x _hx => ⟨D6_const 1 x, D6_linear x, D6_quadratic x⟩,
    D6_cubic_eq_massGap_mul_sq⟩,
   ⟨fun x _hx => ⟨D5_const 1 x, D5_linear x⟩,
    D5_not_annihilate_quadratic⟩,
   ker_Fζ_not_subalgebra⟩

end MainTheorem

end FUST.YangMills
