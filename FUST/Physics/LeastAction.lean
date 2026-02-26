import FUST.Physics.TimeStructure

/-!
# Least Action Principle

Variational calculus on the Fζ Lagrangian |Fζ f|².
Time evolution equivariance (TimeStructure.lagrangian_phi_equivariant) ensures
|Fζ f|² is a true Lagrangian, and δL = 0 ⟹ f ∈ ker(Fζ).
-/

namespace FUST.LeastAction

open FUST.FζOperator FUST.TimeStructure FUST.Zeta6 Complex

/-! ## Variational Structure

Fζ is linear, so L[f] = |Fζ f|² admits standard first variation.
δL = 0 for all test η implies Fζ f = 0, i.e. f ∈ ker(Fζ). -/

theorem Fζ_linear_combination (f g : ℂ → ℂ) (a b : ℂ) (z : ℂ) :
    Fζ (fun t => a * f t + b * g t) z = a * Fζ f z + b * Fζ g z := by
  unfold Fζ AFNum SymNum Φ_A Φ_S_int; ring

theorem Fζ_additive (f g : ℂ → ℂ) (z : ℂ) :
    Fζ (fun t => f t + g t) z = Fζ f z + Fζ g z := by
  have h := Fζ_linear_combination f g 1 1 z; simp only [one_mul] at h; exact h

/-- First variation: L[f+εη] = L[f] + 2Re(ε·Fζη·conj(Fζf)) + O(ε²) -/
theorem lagrangian_perturbation (f η : ℂ → ℂ) (ε : ℂ) (z : ℂ) :
    FζLagrangian (fun t => f t + ε * η t) z =
    normSq (Fζ f z) + 2 * (ε * Fζ η z * starRingEnd ℂ (Fζ f z)).re +
    normSq ε * normSq (Fζ η z) := by
  simp only [FζLagrangian]
  have hlin : Fζ (fun t => f t + ε * η t) z = Fζ f z + ε * Fζ η z := by
    have h := Fζ_linear_combination f η 1 ε z
    simp only [one_mul] at h; exact h
  rw [hlin, normSq_add, normSq_mul]
  have : (Fζ f z * (starRingEnd ℂ) (ε * Fζ η z)).re =
      (ε * Fζ η z * (starRingEnd ℂ) (Fζ f z)).re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  linarith

/-- Critical point: if a nontrivial test variation exists, δL = 0 implies Fζ f = 0 -/
theorem critical_point_of_witness (f : ℂ → ℂ) (z : ℂ)
    (h_witness : ∃ η : ℂ → ℂ, Fζ η z ≠ 0) :
    (∀ η : ℂ → ℂ, Fζ f z * Fζ η z = 0) → Fζ f z = 0 := by
  intro h; obtain ⟨η, hη⟩ := h_witness
  exact (mul_eq_zero.mp (h η)).resolve_right hη

end FUST.LeastAction
