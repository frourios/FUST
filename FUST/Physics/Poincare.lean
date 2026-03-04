/-
Poincaré algebra iso(3,1) = so(3,1) ⋉ ℝ⁴, dim = 6 + 4 = 10.
φ-dilation z → φz becomes translation t → t + log φ in log-coordinates.
4 independent translation vectors from φ-scaling on I4 = Fin 1 ⊕ Fin 3.
-/
import FUST.Physics.Lorentz
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace FUST.Physics.Poincare

open LinearMap (BilinForm)
open LieAlgebra.Orthogonal Matrix Physics.Lorentz DζOperator

/-! ## Module.Finite instance for so(3,1) -/

noncomputable instance : Module.Finite ℝ
    (so' (Fin 1) (Fin 3) ℝ).toSubmodule :=
  Module.Finite.equiv so31EquivR6.symm

/-! ## Translation space ℝ⁴ -/

/-- dim ℝ⁴ = dim(I4 → ℝ) = 4 -/
theorem finrank_translations :
    Module.finrank ℝ (I4 → ℝ) = 4 := by
  simp [I4, Fintype.card_sum, Fintype.card_fin]

/-! ## Poincaré algebra dimension -/

/-- dim iso(3,1) = dim so(3,1) + dim ℝ⁴ = 6 + 4 = 10 -/
theorem finrank_poincare :
    Module.finrank ℝ
      ((so' (Fin 1) (Fin 3) ℝ).toSubmodule × (I4 → ℝ)) = 10 := by
  rw [Module.finrank_prod, finrank_so31, finrank_translations]

/-! ## Casimir invariant: Minkowski bilinear form on I4 → ℝ

Signature (1,3): 1 positive from φψ = -1, 3 negative from ζ₆ compact structure. -/

/-- Minkowski bilinear form B(v,w) = v ⬝ᵥ (η *ᵥ w) -/
noncomputable def minkowskiBilin : BilinForm ℝ (I4 → ℝ) :=
  Matrix.toBilin' (indefiniteDiagonal (Fin 1) (Fin 3) ℝ)

/-- Aᵀη + ηA = 0 for A ∈ so(3,1) -/
theorem skewAdj_sum_zero
    (A : (so' (Fin 1) (Fin 3) ℝ).toSubmodule) :
    (A : Matrix I4 I4 ℝ)ᵀ * indefiniteDiagonal (Fin 1) (Fin 3) ℝ +
    indefiniteDiagonal (Fin 1) (Fin 3) ℝ * (A : Matrix I4 I4 ℝ) = 0 := by
  have hA := A.prop
  simp only [so', LieSubalgebra.mem_toSubmodule,
    mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule] at hA
  rw [hA, mul_neg, neg_add_cancel]

/-- Infinitesimal Lorentz invariance: B(Av, w) + B(v, Aw) = 0 -/
theorem lorentz_infinitesimal_invariance
    (A : (so' (Fin 1) (Fin 3) ℝ).toSubmodule) (v w : I4 → ℝ) :
    minkowskiBilin ((A : Matrix I4 I4 ℝ) *ᵥ v) w +
    minkowskiBilin v ((A : Matrix I4 I4 ℝ) *ᵥ w) = 0 := by
  simp only [minkowskiBilin]
  have h1 : Matrix.toBilin' (indefiniteDiagonal (Fin 1) (Fin 3) ℝ)
    ((A : Matrix I4 I4 ℝ) *ᵥ v) w =
    Matrix.toBilin' ((A : Matrix I4 I4 ℝ)ᵀ * indefiniteDiagonal (Fin 1) (Fin 3) ℝ) v w := by
    simp only [Matrix.toBilin'_apply']
    rw [← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]
  have h2 : Matrix.toBilin' (indefiniteDiagonal (Fin 1) (Fin 3) ℝ)
    v ((A : Matrix I4 I4 ℝ) *ᵥ w) =
    Matrix.toBilin' (indefiniteDiagonal (Fin 1) (Fin 3) ℝ * (A : Matrix I4 I4 ℝ)) v w := by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← mulVec_mulVec]
  rw [h1, h2, show
    Matrix.toBilin' ((A : Matrix I4 I4 ℝ)ᵀ * indefiniteDiagonal (Fin 1) (Fin 3) ℝ) v w +
    Matrix.toBilin' (indefiniteDiagonal (Fin 1) (Fin 3) ℝ * (A : Matrix I4 I4 ℝ)) v w =
    Matrix.toBilin' ((A : Matrix I4 I4 ℝ)ᵀ * indefiniteDiagonal (Fin 1) (Fin 3) ℝ +
      indefiniteDiagonal (Fin 1) (Fin 3) ℝ * (A : Matrix I4 I4 ℝ)) v w from by
    rw [map_add]; rfl]
  rw [skewAdj_sum_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

/-! ## φ-Dilation as Translation in Log-Coordinates

φ-scaling z → φz is multiplicative. In log-coordinates t = log z,
it becomes additive translation t → t + log φ. This establishes
the translation symmetry needed for the Poincaré group. -/

theorem log_phi_pos : 0 < Real.log φ :=
  Real.log_pos φ_gt_one

theorem log_phi_ne_zero : Real.log φ ≠ 0 :=
  ne_of_gt log_phi_pos

/-- exp conjugacy: φ-scaling = translation by log φ in log-coordinates -/
theorem exp_log_phi_translate (t : ℝ) :
    Real.exp (t + Real.log φ) = φ * Real.exp t := by
  rw [Real.exp_add, Real.exp_log phi_pos, mul_comm]

/-- Iterated φ-scaling = translation by n·log φ -/
theorem exp_log_phi_translate_nat (n : ℕ) (t : ℝ) :
    Real.exp (t + ↑n * Real.log φ) = φ ^ n * Real.exp t := by
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log phi_pos, mul_comm]

/-- Translation vector: log φ in the μ-th direction of I4 -/
noncomputable def phiTranslation (μ : I4) : I4 → ℝ :=
  fun i => if i = μ then Real.log φ else 0

theorem phiTranslation_apply_self (μ : I4) : phiTranslation μ μ = Real.log φ := by
  simp [phiTranslation]

theorem phiTranslation_apply_ne {μ ν : I4} (h : ν ≠ μ) : phiTranslation μ ν = 0 := by
  simp [phiTranslation, h]

/-- The 4 translation vectors span I4 → ℝ (linearly independent) -/
theorem phiTranslation_linearIndependent :
    LinearIndependent ℝ (fun μ : I4 => phiTranslation μ) := by
  rw [linearIndependent_iff']
  intro s g hg μ hμ
  have h := congr_fun hg μ
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
  have : ∀ ν ∈ s, g ν * phiTranslation ν μ = if ν = μ then g μ * Real.log φ else 0 := by
    intro ν _
    by_cases hνμ : ν = μ
    · simp [hνμ, phiTranslation_apply_self]
    · simp [phiTranslation_apply_ne (Ne.symm hνμ), hνμ]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq'] at h
  simp only [hμ, ite_true] at h
  exact mul_right_cancel₀ log_phi_ne_zero (by linarith)

/-- φ-dilation corresponds to translation in the Poincaré group -/
theorem phi_dilation_is_translation :
    (∀ t : ℝ, Real.exp (t + Real.log φ) = φ * Real.exp t) ∧
    (0 < Real.log φ) ∧
    (LinearIndependent ℝ (fun μ : I4 => phiTranslation μ)) ∧
    (Module.finrank ℝ (I4 → ℝ) = 4) :=
  ⟨exp_log_phi_translate, log_phi_pos, phiTranslation_linearIndependent, finrank_translations⟩

end FUST.Physics.Poincare
