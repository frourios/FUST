import FUST.Physics.TimeStructure
import FUST.Physics.Gravity

/-!
# Mass Gap and Poincaré Mass Structure

1. Fζ kernel: n ≡ 0,2,3,4 mod 6 → Fζ(zⁿ) = 0
2. Active modes: n ≡ 1,5 mod 6 → Fζ(zⁿ) = λ(n)·zⁿ
3. massScale = |AF_coeff|²/5² = 12/25 (from Fζ = 5z·Dζ and AF_coeff = 2i√3)
4. Fζ action on scale lattice: S[f] = Σ ‖Fζ f(φⁿ)‖²
5. Casimir mass gap: m²(1) = -P^μP_μ = 14
-/

namespace FUST

open FUST.TimeStructure FUST.FζOperator

/-! ## Fζ kernel structure

4 of every 6 monomial modes are annihilated by Fζ. -/

section KernelStructure

theorem kernel_mod6 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k)) z = 0 ∧
    Fζ (fun w => w ^ (6 * k + 2)) z = 0 ∧
    Fζ (fun w => w ^ (6 * k + 3)) z = 0 ∧
    Fζ (fun w => w ^ (6 * k + 4)) z = 0 :=
  ⟨Fζ_vanish_mod6_0 k z, Fζ_vanish_mod6_2 k z,
   Fζ_vanish_mod6_3 k z, Fζ_vanish_mod6_4 k z⟩

end KernelStructure

/-! ## Mass Scale from Fζ Structure

massScale = |AF_coeff|²/5² = 12/25.
- 12 = |AF_coeff|² = |−2 + 4ζ₆|² (gauge channel norm, proved in Zeta6.AF_coeff_normSq)
- 25 = 5² from Fζ = 5z·Dζ (operator rescaling, proved in FζOperator.Fζ_eq) -/

section MassScaleSection

open FUST.Zeta6

/-- Mass scale Δ = |AF_coeff|²/5² derived from Fζ/Dζ structural constants -/
noncomputable def massScale : ℝ := Complex.normSq AF_coeff / 5 ^ 2

theorem massScale_eq : massScale = 12 / 25 := by
  simp only [massScale, AF_coeff_normSq]; norm_num

theorem massScale_pos : 0 < massScale := by rw [massScale_eq]; norm_num

theorem massScale_sq : massScale ^ 2 = 144 / 625 := by rw [massScale_eq]; norm_num

theorem massScale_sq_pos : 0 < massScale ^ 2 := by rw [massScale_eq]; norm_num

end MassScaleSection

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

/-! ## Mass Gap from Dζ Casimir Invariant

m²(s) = -P^μP_μ where P^μ = Re(Dζ_components(s)).
Minimum active mode s=1: m² = 14. -/

section CasimirMassGap

open FUST.Physics.Poincare FUST.Physics.Gravity Physics.Lorentz LieAlgebra.Orthogonal

private lemma phi_sub_psi_sq : (φ - ψ) ^ 2 = 5 := by
  rw [phi_sub_psi, sq, Real.mul_self_sqrt (by norm_num : (5:ℝ) ≥ 0)]

noncomputable def casimirMassSq (s : ℕ) : ℝ := -poincareCasimir (Dζ_momentum s)

theorem casimirMassSq_one : casimirMassSq 1 = 14 := by
  unfold casimirMassSq poincareCasimir minkowskiBilin
  rw [Matrix.toBilin'_apply']
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Fin.sum_univ_three, Fin.sum_univ_one]
  simp only [Dζ_momentum_one_inl0, Dζ_momentum_one_inl1,
    Dζ_momentum_one_inl2, Dζ_momentum_one_inr0]
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

namespace FUST.Dim

noncomputable def massScale : ScaleQ dimTime⁻¹ := ⟨FUST.massScale⟩

theorem massScale_val : massScale.val = 12 / 25 := by
  simp only [massScale, FUST.massScale_eq]

theorem massScale_pos : 0 < massScale.val := by rw [massScale_val]; norm_num

end FUST.Dim
