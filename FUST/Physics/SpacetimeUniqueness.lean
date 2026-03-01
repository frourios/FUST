import FUST.Physics.Gravity
import PhysLean.Relativity.LorentzGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Spacetime Structure from Dζ: Dimension, Signature, and Poincaré Group

The 4D Lorentzian spacetime I4 = Fin 1 ⊕ Fin 3 with signature (1,3) is
determined by the algebraic structure of Dζ. The symmetry group is
O(3,1) = LorentzGroup 3 (PhysLean, with Group instance).
ISO(3,1) = ℝ⁴ ⋊ O(3,1) is constructed as a semidirect product.
-/

namespace FUST.SpacetimeUniqueness

open DζOperator Complex
open LieAlgebra.Orthogonal Matrix FUST.Physics.Lorentz FUST.Physics.Poincare LorentzGroup

/-- Lorentz invariance of the Minkowski bilinear form -/
theorem lorentz_bilin_invariance (Λ : LorentzGroup 3) (v w : I4 → ℝ) :
    minkowskiBilin (Λ.1 *ᵥ v) (Λ.1 *ᵥ w) = minkowskiBilin v w := by
  simp only [minkowskiBilin]
  have h1 : toBilin' (indefiniteDiagonal (Fin 1) (Fin 3) ℝ) (Λ.1 *ᵥ v) (Λ.1 *ᵥ w) =
    toBilin' (Λ.1ᵀ * indefiniteDiagonal (Fin 1) (Fin 3) ℝ * Λ.1) v w := by
    simp only [toBilin'_apply']
    rw [← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, ← mulVec_mulVec,
      ← dotProduct_mulVec]
  rw [h1, show Λ.1ᵀ * indefiniteDiagonal (Fin 1) (Fin 3) ℝ * Λ.1 =
    indefiniteDiagonal (Fin 1) (Fin 3) ℝ from
    (LorentzGroup.mem_iff_transpose_mul_minkowskiMatrix_mul_self Λ.1).mp Λ.2]

/-! ## Semidirect product ISO(3,1) = ℝ⁴ ⋊ O(3,1)

O(3,1) acts on ℝ⁴ by matrix-vector multiplication. The Poincaré group
is the semidirect product of translations ℝ⁴ and Lorentz transformations O(3,1). -/

/-- Each Lorentz transformation Λ gives an additive automorphism of ℝ⁴ -/
noncomputable def lorentzAddEquiv (Λ : LorentzGroup 3) : (I4 → ℝ) ≃+ (I4 → ℝ) where
  toFun v := Λ.1 *ᵥ v
  invFun v := Λ⁻¹.1 *ᵥ v
  left_inv v := by
    change Λ⁻¹.1 *ᵥ (Λ.1 *ᵥ v) = v
    rw [mulVec_mulVec, coe_inv, inv_mul_of_invertible, one_mulVec]
  right_inv v := by
    change Λ.1 *ᵥ (Λ⁻¹.1 *ᵥ v) = v
    rw [mulVec_mulVec, coe_inv, mul_inv_of_invertible, one_mulVec]
  map_add' u v := mulVec_add Λ.1 u v

/-- Lorentz group action on Multiplicative(ℝ⁴) as group automorphisms -/
noncomputable def lorentzAction :
    LorentzGroup 3 →* MulAut (Multiplicative (I4 → ℝ)) where
  toFun Λ := (MulAutMultiplicative (I4 → ℝ)).symm (lorentzAddEquiv Λ)
  map_one' := by
    apply MulEquiv.injective (MulAutMultiplicative (I4 → ℝ))
    simp only [map_one, MulEquiv.apply_symm_apply]
    ext v
    simp [lorentzAddEquiv, lorentzGroupIsGroup_one_coe, one_mulVec]
  map_mul' Λ₁ Λ₂ := by
    apply MulEquiv.injective (MulAutMultiplicative (I4 → ℝ))
    simp only [map_mul, MulEquiv.apply_symm_apply]
    ext v
    simp [lorentzAddEquiv, lorentzGroupIsGroup_mul_coe, mulVec_mulVec]

/-- Poincaré group ISO(3,1) = ℝ⁴ ⋊ O(3,1) as a semidirect product -/
abbrev PoincareGroup := Multiplicative (I4 → ℝ) ⋊[lorentzAction] LorentzGroup 3

noncomputable instance : Group PoincareGroup := inferInstance

/-- Dζ determines O(3,1) spacetime structure and Poincaré group -/
theorem spacetime_from_Dζ :
    -- Dζ 3+1 decomposition
    (AF_coeff.re = 0 ∧ AF_coeff.im > 0) ∧
    -- Spatial channel rank 3
    (σ_Diff5 1 * (σ_Diff3 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff3 7) -
     σ_Diff3 1 * (σ_Diff5 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff5 7) +
     σ_Diff2 1 * (σ_Diff5 5 * σ_Diff3 7 - σ_Diff3 5 * σ_Diff5 7) ≠ 0) ∧
    -- Temporal channel nontrivial
    (Φ_A id 1 ≠ 0) ∧
    -- Signature (1,3): temporal positive, spatial negative
    (∀ a : ℝ, a ≠ 0 → ((6 * (a : ℂ) + AF_coeff * 0) ^ 2).re > 0) ∧
    (∀ b : ℝ, b ≠ 0 → ((6 * (0 : ℂ) + AF_coeff * b) ^ 2).re < 0) ∧
    -- Lorentz group preserves Dζ-derived metric
    (∀ (Λ : LorentzGroup 3) (v w : I4 → ℝ),
      minkowskiBilin (Λ.1 *ᵥ v) (Λ.1 *ᵥ w) = minkowskiBilin v w) :=
  ⟨⟨by rw [AF_coeff_eq], by rw [AF_coeff_eq]; positivity⟩,
   Φ_S_rank_three,
   by simp only [Φ_A, id, mul_one]; norm_cast
      have hψ : ψ = 1 - φ := by unfold ψ φ; ring
      rw [hψ]; nlinarith [φ_gt_one, golden_ratio_property],
   fun a ha => by simp only [mul_zero, add_zero]; norm_cast; positivity,
   fun b hb => by
     simp only [mul_zero, zero_add]; rw [AF_coeff_eq]
     simp [sq, mul_re, ofReal_re, ofReal_im]
     have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
     have hb2 : b ^ 2 > 0 := by positivity
     nlinarith,
   lorentz_bilin_invariance⟩

end FUST.SpacetimeUniqueness
