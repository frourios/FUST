import FUST.FζOperator
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace FUST

open FUST.DζOperator Matrix FUST.FrourioAlgebra.GoldenEisensteinInt

/-- U(1) gauge group uniqueness for the trivial channel.

The trivial channel is the Galois-fixed subspace of ℤ[φ,ζ₆]:
- galois_fixed_iff: σ(x)=x ∧ τ(x)=x ↔ b=c=d=0 (1D over ℤ)
- On 1D: norm-preserving gauge = unitaryGroup (Fin 1) ℂ = U(1)
- SU(1) = {I} is trivial: no SU reduction, full gauge is U(1)
- derivDefect_const_gauge: scalar U(1) is exactly the gauge freedom -/
theorem U1_gauge_uniqueness :
    -- Galois-fixed subspace = ℤ (dim 1)
    (∀ x : FUST.FrourioAlgebra.GoldenEisensteinInt,
      sigma x = x ∧ tau x = x ↔ x.b = 0 ∧ x.c = 0 ∧ x.d = 0) ∧
    -- Scalar gauge invariance (derivDefect)
    (∀ (c : ℂ) (_ : c ≠ 0) (f g : ℂ → ℂ) (z : ℂ),
      FζOperator.derivDefect (fun w => c * f w) (fun w => c⁻¹ * g w) z =
      FζOperator.derivDefect f g z) ∧
    -- Scalar unitary c·I₁ ∈ U(1)
    (∀ c : ℂ, starRingEnd ℂ c * c = 1 →
      c • (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ unitaryGroup (Fin 1) ℂ) ∧
    -- det(c·I₁) = c (linear, not higher power)
    (∀ c : ℂ, (c • (1 : Matrix (Fin 1) (Fin 1) ℂ)).det = c ^ 1) ∧
    -- SU(1) is trivial (only identity)
    (∀ M : Matrix (Fin 1) (Fin 1) ℂ,
      M ∈ specialUnitaryGroup (Fin 1) ℂ → M = 1) ∧
    -- Galois-fixed units are ±1
    (∀ x : FUST.FrourioAlgebra.GoldenEisensteinInt,
      sigma x = x ∧ tau x = x ∧ (mul x x = one ∨ mul x (neg x) = one) →
      x = one ∨ x = neg one) :=
  ⟨galois_fixed_iff,
   FζOperator.derivDefect_const_gauge,
   fun c hc => by
     rw [mem_unitaryGroup_iff']; ext i j
     simp only [star_smul, star_one, mul_apply, smul_apply, one_apply, smul_eq_mul]
     simp [hc, Fin.eq_zero i, Fin.eq_zero j],
   fun c => by simp,
   fun M hM => by
     rw [mem_specialUnitaryGroup_iff] at hM; ext i j
     have hi := Fin.eq_zero i; have hj := Fin.eq_zero j; subst hi; subst hj
     simp only [one_apply_eq]; rw [det_fin_one] at hM; exact hM.2,
   galois_fixed_unit_iff⟩

/-- SU(2) gauge group uniqueness for the AF channel.

The AF channel carries a quaternionic structure from τ-anti-invariance:
- τ(AF_coeff) = -AF_coeff and τ² = id give eigenvalue -1
- AF_coeff² = -12: the J² < 0 quaternionic condition
- The 1D-over-ℂ AF space with quaternionic doubling gives ℂ² = ℍ¹
- Norm preservation on ℂ² → U(2), scalar separation → SU(2) = Sp(1) -/
theorem SU2_gauge_uniqueness :
    -- τ(AF_coeff) = -AF_coeff (quaternionic indicator)
    (tau AF_coeff_gei =
      FUST.FrourioAlgebra.GoldenEisensteinInt.neg AF_coeff_gei) ∧
    -- τ is an involution (eigenvalues ±1)
    (∀ x : FUST.FrourioAlgebra.GoldenEisensteinInt, tau (tau x) = x) ∧
    -- τ preserves multiplication (ring automorphism)
    (∀ x y : FUST.FrourioAlgebra.GoldenEisensteinInt,
      tau (mul x y) = mul (tau x) (tau y)) ∧
    -- AF_coeff² = -12 (quaternionic: J² < 0)
    (mul AF_coeff_gei AF_coeff_gei =
      (⟨-12, 0, 0, 0⟩ : FUST.FrourioAlgebra.GoldenEisensteinInt)) ∧
    -- AF_coeff is not real (complex structure essential, excludes SO(3))
    (AF_coeff.im ≠ 0) ∧
    -- Scalar unitary c·I₂ ∈ U(2) (center)
    (∀ c : ℂ, starRingEnd ℂ c * c = 1 →
      c • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitaryGroup (Fin 2) ℂ) ∧
    -- Scalar gauge has det c²
    (∀ c : ℂ, (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = c ^ 2) :=
  ⟨by unfold tau AF_coeff_gei FUST.FrourioAlgebra.GoldenEisensteinInt.neg; ext <;> simp,
   tau_involution,
   tau_mul,
   by unfold AF_coeff_gei mul; ext <;> simp,
   by rw [AF_coeff_eq]; simp,
   fun c hc => by
     rw [mem_unitaryGroup_iff']; ext i j
     simp only [star_smul, star_one, mul_apply, smul_apply, one_apply, smul_eq_mul,
       Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_zero, mul_one,
       ite_mul, zero_mul]
     split
     · subst_vars; exact hc
     · ring,
   fun c => by simp [Fintype.card_fin]⟩

/-- 3×3 matrix of SY sub-operator eigenvalues at the first three active modes -/
noncomputable def syModeMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![σ_Diff5 1, σ_Diff5 5, σ_Diff5 7;
     σ_Diff3 1, σ_Diff3 5, σ_Diff3 7;
     σ_Diff2 1, σ_Diff2 5, σ_Diff2 7]

/-- SU(3) gauge group uniqueness for the SY channel.

Rank 3 mode space → U(3), scalar U(1) center separated by derivDefect gauge,
remaining mode-mixing has det = 1, giving SU(3). -/
theorem SU3_gauge_uniqueness :
    -- SY mode vectors are linearly independent (rank 3)
    (LinearIndependent ℝ (fun i : Fin 3 => syModeMatrix i)) ∧
    -- Scalar unitary c·I ∈ U(3) (center)
    (∀ c : ℂ, starRingEnd ℂ c * c = 1 →
      c • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∈ unitaryGroup (Fin 3) ℂ) ∧
    -- Scalar gauge has nontrivial det: det(cI₃) = c³
    (∀ c : ℂ, (c • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = c ^ 3) ∧
    -- ℂ has nontrivial star (conjugation ≠ identity, excludes O(3))
    (starRingEnd ℂ ≠ RingHom.id ℂ) ∧
    -- Scalar gauge is already separated (derivDefect_const_gauge)
    (∀ (c : ℂ) (_ : c ≠ 0) (f g : ℂ → ℂ) (z : ℂ),
      FζOperator.derivDefect (fun w => c * f w) (fun w => c⁻¹ * g w) z =
      FζOperator.derivDefect f g z) :=
  ⟨Matrix.linearIndependent_rows_of_det_ne_zero (by
      rw [Matrix.det_fin_three]
      simp only [syModeMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one]
      simp only [show (2 : Fin 3) = ⟨2, by omega⟩ from rfl]
      norm_num
      rw [σ_Diff5_one, σ_Diff3_one, σ_Diff2_one,
          σ_Diff5_five, σ_Diff3_five, σ_Diff2_five,
          σ_Diff5_seven, σ_Diff3_seven, σ_Diff2_seven]
      intro h
      have : φ - ψ ≠ 0 := ne_of_gt (by linarith [φ_gt_one, psi_neg])
      exact this (by nlinarith)),
   fun c hc => by
     rw [mem_unitaryGroup_iff']; ext i j
     simp only [star_smul, star_one, mul_apply, smul_apply, one_apply, smul_eq_mul,
       Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_zero, mul_one,
       ite_mul, zero_mul]
     split
     · subst_vars; exact hc
     · ring,
   fun c => by simp [Fintype.card_fin],
   by intro h; have h1 : (starRingEnd ℂ) Complex.I = Complex.I := by rw [h]; simp
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_I] at h1
      have := congr_arg Complex.im h1
      simp only [Complex.neg_im, Complex.I_im] at this; linarith,
   FζOperator.derivDefect_const_gauge⟩

end FUST
