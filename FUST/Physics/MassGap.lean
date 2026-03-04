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

/-! ## Poincaré Mass Connection

P^μP_μ via Minkowski bilinear form. Signature (1,3). -/

section PoincareMass

noncomputable def poincareCasimir (p : I4 → ℝ) : ℝ := minkowskiBilin p p

def onMassShell (p : I4 → ℝ) (m : ℝ) : Prop := poincareCasimir p = m ^ 2

theorem vacuum_massless : onMassShell (fun _ => 0) 0 := by
  simp only [onMassShell, poincareCasimir, sq, mul_zero]
  unfold minkowskiBilin
  simp [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec]

end PoincareMass

/-! ## Mass Gap from Dζ Casimir Invariant

m²(s) = P^μP_μ where P^μ = Re(Dζ_components(s)).
Minimum active mode s=1: m² = 14. -/

section CasimirMassGap

private lemma phi_sub_psi_sq : (φ - ψ) ^ 2 = 5 := by
  rw [phi_sub_psi, sq, Real.mul_self_sqrt (by norm_num : (5:ℝ) ≥ 0)]

noncomputable def casimirMassSq (s : ℕ) : ℝ := poincareCasimir (Dζ_momentum s)

theorem casimirMassSq_one : casimirMassSq 1 = 14 := by
  unfold casimirMassSq poincareCasimir minkowskiBilin
  rw [Matrix.toBilin'_apply']
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Fin.sum_univ_three, Fin.sum_univ_one]
  simp only [Dζ_momentum_one_inl0, Dζ_momentum_one_inr0,
    Dζ_momentum_one_inr1, Dζ_momentum_one_inr2]
  simp (config := { decide := true }) only [indefiniteDiagonal, Matrix.diagonal_apply,
    Sum.elim_inl, Sum.elim_inr, ↓reduceIte]
  nlinarith [phi_sub_psi_sq]

noncomputable def massGapSq : ℝ := casimirMassSq 1

theorem massGapSq_eq : massGapSq = 14 := casimirMassSq_one

theorem massGapSq_pos : 0 < massGapSq := by rw [massGapSq_eq]; norm_num

theorem massGap_onMassShell : onMassShell (Dζ_momentum 1) (Real.sqrt 14) := by
  unfold onMassShell
  rw [sq, Real.mul_self_sqrt (by norm_num : (14:ℝ) ≥ 0)]
  exact casimirMassSq_one

end CasimirMassGap

end FUST
