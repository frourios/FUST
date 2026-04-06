import FUST.Physics.TimeStructure
import FUST.Physics.Gravity

namespace FUST

open FUST.TimeStructure FUST.FζOperator FUST.Physics.Poincare  Physics.Lorentz
open FUST.Physics.Gravity LieAlgebra.Orthogonal

/-! ## Fζ Action on Scale Lattice

S[f](n) = |Fζ f(φⁿ)|², partial sum over [-N, N]. -/

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

/-! ## Mass Invariant from Dζ Eigenvalue

m²(s) = Dζ_im(s)² - Dζ_re(s)² = 12·Φ_A(s)² - 36·Φ_S(s)².
Temporal component (AF channel, imaginary) minus spatial (SY channel, real).
Minimum active mode s=1: m² = 144√5 - 84 = 12(12√5 - 7). -/

section DzetaMass

private lemma phi_sub_psi_sq : (φ - ψ) ^ 2 = 5 := by
  rw [phi_sub_psi, sq, Real.mul_self_sqrt (by norm_num : (5:ℝ) ≥ 0)]

/-- Mass² from Dζ eigenvalue: Im² - Re² = 12·Φ_A² - 36·Φ_S² -/
noncomputable def casimirMassSq (s : ℕ) : ℝ :=
  Dζ_im s ^ 2 - Dζ_re s ^ 2

theorem casimirMassSq_def (s : ℕ) :
    casimirMassSq s = 12 * Φ_A_coeff s ^ 2 - 36 * Φ_S_coeff s ^ 2 := by
  unfold casimirMassSq Dζ_im Dζ_re
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
  nlinarith [h3]

theorem casimirMassSq_one : casimirMassSq 1 = 144 * Real.sqrt 5 - 84 := by
  rw [casimirMassSq_def, Φ_A_coeff_one, Φ_S_coeff_one]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  have hφψ : φ - ψ = Real.sqrt 5 := phi_sub_psi
  nlinarith [h5, hφψ]

noncomputable def massGapSq : ℝ := casimirMassSq 1

theorem massGapSq_eq : massGapSq = 144 * Real.sqrt 5 - 84 := casimirMassSq_one

theorem massGapSq_pos : 0 < massGapSq := by
  rw [massGapSq_eq]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  nlinarith [Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num),
             Real.sqrt_nonneg 5, h5]

end DzetaMass

end FUST
