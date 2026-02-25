import FUST.Physics.MassGap
import FUST.Physics.Poincare
import FUST.IntegralDzeta
import FUST.SpectralCoefficients
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace FUST.Hamiltonian

open FUST FUST.IntegralDzeta Complex

/-! ## Fζ Action Functional -/

section FζAction

noncomputable def actionFζ (f : ℂ → ℂ) (n : ℤ) : ℝ :=
  Complex.normSq (Fζ f (↑(φ ^ n)))

theorem actionFζ_nonneg (f : ℂ → ℂ) (n : ℤ) :
    actionFζ f n ≥ 0 := Complex.normSq_nonneg _

noncomputable def partialActionFζ (f : ℂ → ℂ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum (fun n => actionFζ f n)

theorem partialActionFζ_nonneg (f : ℂ → ℂ) (N : ℕ) :
    partialActionFζ f N ≥ 0 :=
  Finset.sum_nonneg fun n _ => actionFζ_nonneg f n

theorem actionFζ_ker_zero (f : ℂ → ℂ) (hf : IsInKerFζ f) (n : ℤ) :
    actionFζ f n = 0 := by
  simp only [actionFζ, hf (↑(φ ^ n)), map_zero]

theorem partialActionFζ_ker_zero (f : ℂ → ℂ) (hf : IsInKerFζ f) (N : ℕ) :
    partialActionFζ f N = 0 :=
  Finset.sum_eq_zero fun n _ => actionFζ_ker_zero f hf n

theorem actionFζ_zero_iff (f : ℂ → ℂ) (n : ℤ) :
    actionFζ f n = 0 ↔ Fζ f (↑(φ ^ n)) = 0 := by
  simp only [actionFζ, Complex.normSq_eq_zero]

end FζAction

/-! ## Poincaré Mass Connection

P^μP_μ via Minkowski bilinear form. Signature (3,1). -/

section PoincareMass

open FUST.Physics.Poincare FUST.Physics.Gravity Physics.Lorentz

noncomputable def poincareCasimir (p : I4 → ℝ) : ℝ := minkowskiBilin p p

def onMassShell (p : I4 → ℝ) (m : ℝ) : Prop := -poincareCasimir p = m ^ 2

theorem vacuum_massless : onMassShell (fun _ => 0) 0 := by
  simp only [onMassShell, poincareCasimir, sq, mul_zero, neg_eq_zero]
  unfold minkowskiBilin
  simp [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec]

end PoincareMass

/-! ## Resonance Stability

Real eigenvalues force real energy: E² = μ > 0 ⟹ E ∈ ℝ.
Real-energy time evolution has unit amplitude (stable). -/

section ResonanceStability

theorem sq_eq_pos_real_implies_real (c : ℝ) (hc : 0 < c)
    (E : ℂ) (h : E ^ 2 = (c : ℂ)) : E.im = 0 := by
  have him : (E ^ 2).im = (c : ℂ).im := congrArg Complex.im h
  simp only [sq, Complex.mul_im, Complex.ofReal_im] at him
  have h2 : 2 * E.re * E.im = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exfalso
      have hre : (E ^ 2).re = (c : ℂ).re := congrArg Complex.re h
      simp only [sq, Complex.mul_re, Complex.ofReal_re] at hre
      rw [h4] at hre
      simp at hre
      linarith [sq_nonneg E.im]
  · exact h3

theorem resonance_amplitude_stable (E t : ℝ) :
    ‖Complex.exp (-(I * E * t))‖ = 1 := by
  have h : -(I * (E : ℂ) * (t : ℂ)) = (-(E * t) : ℝ) * I := by
    push_cast; ring
  rw [h, norm_exp_ofReal_mul_I]

theorem resonance_amplitude_unstable (E : ℂ) (t : ℝ)
    (ht : t ≠ 0) (him : E.im ≠ 0) :
    ‖Complex.exp (-(I * E * (t : ℂ)))‖ ≠ 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf
  intro h
  have : Real.exp (E.im * t) = 1 := h
  rw [Real.exp_eq_one_iff] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact him h1
  · exact ht h1

end ResonanceStability

end FUST.Hamiltonian

/-! ## Dimensioned Wrappers -/

namespace FUST.Dim

noncomputable def actionFζ_dim (f : ℂ → ℂ) (n : ℤ) :
    ScaleQ dimLagrangian :=
  ⟨FUST.Hamiltonian.actionFζ f n⟩

theorem actionFζ_dim_nonneg (f : ℂ → ℂ) (n : ℤ) :
    (actionFζ_dim f n).val ≥ 0 :=
  FUST.Hamiltonian.actionFζ_nonneg f n

theorem actionFζ_ker_zero (f : ℂ → ℂ)
    (hf : FUST.IntegralDzeta.IsInKerFζ f) (n : ℤ) :
    (actionFζ_dim f n).val = 0 :=
  FUST.Hamiltonian.actionFζ_ker_zero f hf n

end FUST.Dim
