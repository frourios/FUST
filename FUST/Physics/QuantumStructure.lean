import FUST.DifferenceOperators
import FUST.Physics.LeastAction
import FUST.Physics.Probability
import FUST.Physics.HilbertPolya
import FUST.Physics.Thermodynamics

namespace FUST.Dim

/-! ## Probability: observation as ScaleQ(dimLagrangian^(1/2)) -/

/-- Observation |D₆ f(φ^k x₀)| with D₆ output dimension -/
noncomputable def observation (f : ℝ → ℝ) (x₀ : ℝ) (k : ℤ) : ScaleQ (deriveFDim 6) :=
  ⟨FUST.Probability.observationAt f x₀ k⟩

theorem observation_nonneg (f : ℝ → ℝ) (x₀ : ℝ) (k : ℤ) :
    (observation f x₀ k).val ≥ 0 :=
  FUST.Probability.observationAt_nonneg f x₀ k

/-- Discrete action as ScaleQ(dimLagrangian) -/
noncomputable def discreteAction (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) :
    ScaleQ dimLagrangian :=
  ⟨FUST.Probability.discreteAction f x₀ N⟩

theorem discreteAction_nonneg (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) :
    (discreteAction f x₀ N).val ≥ 0 :=
  FUST.Probability.discreteAction_nonneg f x₀ N

theorem action_zero_for_ker (f : ℝ → ℝ) (hf : FUST.LeastAction.IsInKerD6 f)
    (x₀ : ℝ) (hx₀ : 0 < x₀) (N : ℕ) :
    (discreteAction f x₀ N).val = 0 :=
  FUST.Probability.action_zero_for_ker f hf x₀ hx₀ N

/-! ## Hamiltonian: (D₆ f x)² as ScaleQ(dimLagrangian) -/

noncomputable def fustHamiltonian (f : ℝ → ℝ) (x : ℝ) : ScaleQ dimLagrangian :=
  ⟨FUST.HilbertPolya.FUSTHamiltonian f x⟩

theorem fustHamiltonian_nonneg (f : ℝ → ℝ) (x : ℝ) :
    (fustHamiltonian f x).val ≥ 0 :=
  FUST.HilbertPolya.hamiltonian_nonneg f x

theorem fustHamiltonian_ker_zero (f : ℝ → ℝ) (hf : FUST.LeastAction.IsInKerD6 f)
    (x : ℝ) (hx : x ≠ 0) :
    (fustHamiltonian f x).val = 0 :=
  FUST.HilbertPolya.hamiltonian_ker_zero f hf x hx

theorem fustHamiltonian_eq_lagrangian (f : ℝ → ℝ) (x : ℝ) :
    (fustHamiltonian f x).val = (Dim.lagrangian_dim f x).val := rfl

/-! ## Spectral Eigenvalues as CountQ -/

def fustEigenvalue3 : CountQ := ⟨FUST.Hamiltonian.spectralGapValue⟩

theorem fustEigenvalue3_val : fustEigenvalue3.val = 6 := by
  simp only [fustEigenvalue3, FUST.Hamiltonian.spectralGapValue_eq]

/-! ## Thermodynamics: entropy as ScaleQ(dimLagrangian) -/

/-- Entropy at time t for function f -/
noncomputable def entropyAt (f : ℝ → ℝ) (t : ℝ) : ScaleQ dimLagrangian :=
  ⟨FUST.TimeTheorem.entropyAt f t⟩

theorem third_law (f : ℝ → ℝ) (hf : ¬FUST.LeastAction.IsInKerD6 f) :
    ∃ t, (entropyAt f t).val > 0 :=
  FUST.Thermodynamics.third_law_massive_positive_entropy f hf

theorem absolute_zero_implies_lightlike (f : ℝ → ℝ)
    (h : ∀ t, (entropyAt f t).val = 0) : FUST.LeastAction.IsInKerD6 f :=
  FUST.Thermodynamics.absolute_zero_implies_lightlike f h

theorem lightlike_zero_entropy (f : ℝ → ℝ) (hf : FUST.LeastAction.IsInKerD6 f) :
    ∀ t, (entropyAt f t).val = 0 :=
  FUST.Thermodynamics.lightlike_can_reach_zero f hf

/-! ## Dimensional Consistency -/

theorem hamiltonian_lagrangian_same_dim :
    dimLagrangian = deriveFDim 6 * deriveFDim 6 := rfl

theorem observation_is_D6_output :
    deriveFDim 6 = dimTime⁻¹ := by decide

end FUST.Dim
