/-
Poincaré algebra iso(3,1) = so(3,1) ⋉ ℝ⁴.
dim iso(3,1) = C(kerDim + posRootCount, 2) + (kerDim + posRootCount) = 6 + 4 = 10.
kerDim = 3 from ζ₆_N6 kernel, posRootCount = 1 from golden ratio root analysis.
-/
import FUST.Physics.Lorentz
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.BilinearForm

namespace FUST.Physics.Poincare

open LinearMap (BilinForm)
open LieAlgebra.Orthogonal Matrix FUST Physics.Lorentz DζOperator

/-! ## Module.Finite instance for so(3,1) -/

noncomputable instance : Module.Finite ℝ
    (so' (Fin 3) (Fin 1) ℝ).toSubmodule :=
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
      ((so' (Fin 3) (Fin 1) ℝ).toSubmodule × (I4 → ℝ)) = 10 := by
  rw [Module.finrank_prod, finrank_so31, finrank_translations]

/-! ## Casimir invariant: Minkowski bilinear form on I4 → ℝ

Signature (3,1): 3 positive from ζ₆ compact structure, 1 negative from φψ = -1. -/

/-- Minkowski bilinear form B(v,w) = v ⬝ᵥ (η *ᵥ w) -/
noncomputable def minkowskiBilin : BilinForm ℝ (I4 → ℝ) :=
  Matrix.toBilin' (indefiniteDiagonal (Fin 3) (Fin 1) ℝ)

/-- Aᵀη + ηA = 0 for A ∈ so(3,1) -/
theorem skewAdj_sum_zero
    (A : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) :
    (A : Matrix I4 I4 ℝ)ᵀ * indefiniteDiagonal (Fin 3) (Fin 1) ℝ +
    indefiniteDiagonal (Fin 3) (Fin 1) ℝ * (A : Matrix I4 I4 ℝ) = 0 := by
  have hA := A.prop
  simp only [so', LieSubalgebra.mem_toSubmodule,
    mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule] at hA
  rw [hA, mul_neg, neg_add_cancel]

/-- Infinitesimal Lorentz invariance: B(Av, w) + B(v, Aw) = 0 -/
theorem lorentz_infinitesimal_invariance
    (A : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) (v w : I4 → ℝ) :
    minkowskiBilin ((A : Matrix I4 I4 ℝ) *ᵥ v) w +
    minkowskiBilin v ((A : Matrix I4 I4 ℝ) *ᵥ w) = 0 := by
  simp only [minkowskiBilin]
  have h1 : Matrix.toBilin' (indefiniteDiagonal (Fin 3) (Fin 1) ℝ)
    ((A : Matrix I4 I4 ℝ) *ᵥ v) w =
    Matrix.toBilin' ((A : Matrix I4 I4 ℝ)ᵀ * indefiniteDiagonal (Fin 3) (Fin 1) ℝ) v w := by
    simp only [Matrix.toBilin'_apply']
    rw [← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]
  have h2 : Matrix.toBilin' (indefiniteDiagonal (Fin 3) (Fin 1) ℝ)
    v ((A : Matrix I4 I4 ℝ) *ᵥ w) =
    Matrix.toBilin' (indefiniteDiagonal (Fin 3) (Fin 1) ℝ * (A : Matrix I4 I4 ℝ)) v w := by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← mulVec_mulVec]
  rw [h1, h2, show
    Matrix.toBilin' ((A : Matrix I4 I4 ℝ)ᵀ * indefiniteDiagonal (Fin 3) (Fin 1) ℝ) v w +
    Matrix.toBilin' (indefiniteDiagonal (Fin 3) (Fin 1) ℝ * (A : Matrix I4 I4 ℝ)) v w =
    Matrix.toBilin' ((A : Matrix I4 I4 ℝ)ᵀ * indefiniteDiagonal (Fin 3) (Fin 1) ℝ +
      indefiniteDiagonal (Fin 3) (Fin 1) ℝ * (A : Matrix I4 I4 ℝ)) v w from by
    rw [map_add]; rfl]
  rw [skewAdj_sum_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

/-! ## Poincaré algebra Lie brackets via 5×5 matrix representation

iso(3,1) embeds into gl(5,ℝ). Rotation/boost generators and translation
generators P_μ are defined directly on Fin 5 × Fin 5 matrices.
Indices: 0,1,2 = spatial, 3 = time, 4 = affine extension. -/

/-- Translation generator P_μ: (P_μ)_{ij} = δ_{i,μ}·δ_{j,4} -/
def P5 (μ : Fin 4) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => if i.val = μ.val ∧ j = 4 then 1 else 0

/-- Rotation generator J₃(=e₀), -J₂(=e₁), J₁(=e₂) in 5×5 -/
def Rot5 (k : Fin 3) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j =>
    if k = 0 then (if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0)
    else if k = 1 then (if i = 0 ∧ j = 2 then 1 else if i = 2 ∧ j = 0 then -1 else 0)
    else (if i = 1 ∧ j = 2 then 1 else if i = 2 ∧ j = 1 then -1 else 0)

/-- Boost generator K₁(=e₃), K₂(=e₄), K₃(=e₅) in 5×5 -/
def Boost5 (k : Fin 3) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j =>
    -- k=0: K₁ = boost in 0: A₀₃=1, A₃₀=1
    -- k=1: K₂ = boost in 1: A₁₃=1, A₃₁=1
    -- k=2: K₃ = boost in 2: A₂₃=1, A₃₂=1
    if i.val = k.val ∧ j = 3 then 1
    else if i = 3 ∧ j.val = k.val then 1
    else 0

/-! ### Structural lemmas for P5 and Boost5 -/

private theorem P5_col (μ : Fin 4) (i : Fin 5) (j : Fin 5) (hj : j ≠ 4) :
    P5 μ i j = 0 := by
  simp only [P5]; split_ifs with h
  · exact absurd h.2 hj
  · rfl

private theorem P5_row (ν : Fin 4) (j : Fin 5) :
    P5 ν 4 j = 0 := by
  simp only [P5]; split_ifs with h
  · exact absurd h.1 (by omega)
  · rfl

private theorem Boost5_row4 (k : Fin 3) (j : Fin 5) :
    Boost5 k 4 j = 0 := by
  simp only [Boost5]; split_ifs with h1 h2
  · exact absurd h1.1 (by omega)
  · exact absurd h2.1 (by omega : (4 : Fin 5) ≠ 3)
  · rfl

private theorem P5_mul_zero (μ ν : Fin 4) : P5 μ * P5 ν = 0 := by
  ext a b; simp only [mul_apply, zero_apply]
  apply Finset.sum_eq_zero; intro k _
  by_cases hk : k = 4
  · rw [hk, P5_row ν b]; ring
  · rw [P5_col μ a k hk]; ring

private theorem P5_mul_Boost5_zero (μ : Fin 4) (k : Fin 3) :
    P5 μ * Boost5 k = 0 := by
  ext a b; simp only [mul_apply, zero_apply]
  apply Finset.sum_eq_zero; intro c _
  by_cases hc : c = 4
  · rw [hc, Boost5_row4]; ring
  · rw [P5_col μ a c hc]; ring

private theorem Boost5_col3 (k : Fin 3) (a : Fin 5) :
    Boost5 k a 3 = if a.val = k.val then 1 else 0 := by
  unfold Boost5
  by_cases h : a.val = k.val
  · simp [h]
  · simp only [h, false_and, ite_false]
    split_ifs with h2
    · exfalso; omega
    · rfl

private theorem Boost5_not3 (k : Fin 3) (a j : Fin 5) (hj : j ≠ 3) :
    Boost5 k a j = if a = 3 ∧ j.val = k.val then 1 else 0 := by
  unfold Boost5; simp [hj]

private theorem Boost5_mul_P5_apply (k : Fin 3) (μ : Fin 4) (a b : Fin 5) :
    (Boost5 k * P5 μ) a b =
    Boost5 k a ⟨μ.val, by omega⟩ * (if b = 4 then 1 else 0) := by
  simp only [mul_apply]
  by_cases hb : b = 4
  · subst hb; simp only [ite_true]; rw [Fin.sum_univ_five]
    simp only [P5]; fin_cases μ <;> simp
  · simp only [hb, ite_false, mul_zero]
    apply Finset.sum_eq_zero; intro c _; rw [P5_col μ c b hb, mul_zero]

private theorem ite_mul_ite (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : ℝ) else 0) * (if q then 1 else 0) =
    if p ∧ q then 1 else 0 := by
  split_ifs <;> simp_all

/-! ### Translations commute -/

theorem translations_commute (μ ν : Fin 4) :
    P5 μ * P5 ν - P5 ν * P5 μ = 0 := by
  rw [P5_mul_zero, P5_mul_zero, sub_self]

/-! ### [K_i, P₃] = P_i (boost-energy → momentum) -/

theorem boost_energy (i : Fin 3) :
    Boost5 i * P5 3 - P5 3 * Boost5 i = P5 ⟨i, by omega⟩ := by
  rw [P5_mul_Boost5_zero 3 i, sub_zero]
  ext a b; rw [Boost5_mul_P5_apply]
  change Boost5 i a 3 * (if b = 4 then 1 else 0) = P5 ⟨i, by omega⟩ a b
  rw [Boost5_col3]; simp only [P5]
  split_ifs <;> simp_all

/-! ### [K_i, P_j] = δ_{ij} P₃ (boost-momentum → energy) -/

theorem boost_momentum (i j : Fin 3) :
    Boost5 i * P5 ⟨j, by omega⟩ - P5 ⟨j, by omega⟩ * Boost5 i =
    if i = j then P5 3 else 0 := by
  rw [P5_mul_Boost5_zero ⟨j, by omega⟩ i, sub_zero]
  ext a b; rw [Boost5_mul_P5_apply]
  have hj3 : (⟨j.val, by omega⟩ : Fin 5) ≠ 3 := by simp [Fin.ext_iff]; omega
  rw [Boost5_not3 i a ⟨j.val, by omega⟩ hj3, ite_mul_ite]
  by_cases hij : i = j
  · subst hij; simp only [P5, and_true, ite_true]
    congr 1; simp [Fin.ext_iff]
  · simp only [hij, ite_false, zero_apply]
    rw [if_neg]; intro ⟨⟨_, hji⟩, _⟩; exact hij (Fin.ext (by omega))

/-! ### [J_i, P₃] = 0 (rotation commutes with energy) -/

theorem rotation_energy (i : Fin 3) :
    Rot5 i * P5 3 - P5 3 * Rot5 i = 0 := by
  fin_cases i <;> {
    ext a b; simp only [P5, Rot5, mul_apply, Fin.sum_univ_five, sub_apply, zero_apply]
    fin_cases a <;> fin_cases b <;> norm_num [Fin.ext_iff]
  }

/-! ### [J_i, P_j] (rotation acts on spatial momentum)

[Rot5(0), P5(0)] = -P5(1), [Rot5(0), P5(1)] = P5(0), [Rot5(0), P5(2)] = 0
[Rot5(1), P5(0)] = -P5(2), [Rot5(1), P5(2)] = P5(0), [Rot5(1), P5(1)] = 0
[Rot5(2), P5(1)] = -P5(2), [Rot5(2), P5(2)] = P5(1), [Rot5(2), P5(0)] = 0 -/

theorem rot0_P0 : Rot5 0 * P5 0 - P5 0 * Rot5 0 = -(P5 1) := by
  ext a b; simp only [P5, Rot5, mul_apply, Fin.sum_univ_five, sub_apply, neg_apply]
  fin_cases a <;> fin_cases b <;> norm_num [Fin.ext_iff]
theorem rot0_P1 : Rot5 0 * P5 1 - P5 1 * Rot5 0 = P5 0 := by
  ext a b; simp only [P5, Rot5, mul_apply, Fin.sum_univ_five, sub_apply]
  fin_cases a <;> fin_cases b <;> norm_num [Fin.ext_iff]
theorem rot1_P0 : Rot5 1 * P5 0 - P5 0 * Rot5 1 = -(P5 2) := by
  ext a b; simp only [P5, Rot5, mul_apply, Fin.sum_univ_five, sub_apply, neg_apply]
  fin_cases a <;> fin_cases b <;> norm_num [Fin.ext_iff]
theorem rot1_P2 : Rot5 1 * P5 2 - P5 2 * Rot5 1 = P5 0 := by
  ext a b; simp only [P5, Rot5, mul_apply, Fin.sum_univ_five, sub_apply]
  fin_cases a <;> fin_cases b <;> norm_num [Fin.ext_iff]
theorem rot2_P1 : Rot5 2 * P5 1 - P5 1 * Rot5 2 = -(P5 2) := by
  ext a b; simp only [P5, Rot5, mul_apply, Fin.sum_univ_five, sub_apply, neg_apply]
  fin_cases a <;> fin_cases b <;> norm_num [Fin.ext_iff]
theorem rot2_P2 : Rot5 2 * P5 2 - P5 2 * Rot5 2 = P5 1 := by
  ext a b; simp only [P5, Rot5, mul_apply, Fin.sum_univ_five, sub_apply]
  fin_cases a <;> fin_cases b <;> norm_num [Fin.ext_iff]

/-! ### Summary: semidirect product structure

iso(3,1) = so(3,1) ⋉ ℝ⁴ where:
  [so(3,1), so(3,1)] ⊆ so(3,1) (proved in Lorentz.lean: so31_brackets)
  [so(3,1), ℝ⁴] ⊆ ℝ⁴ (translations form an ideal: boost_energy, rotation_spatial)
  [ℝ⁴, ℝ⁴] = 0 (abelian ideal: translations_commute)
  [K_i, P₀] = P_i (boost-energy → momentum)
  [K_i, P_j] = δ_{ij} P₀ (boost-momentum → energy) -/

theorem poincare_algebra :
    Module.finrank ℝ ((so' (Fin 3) (Fin 1) ℝ).toSubmodule × (I4 → ℝ)) = 10 ∧
    (∀ μ ν : Fin 4, P5 μ * P5 ν - P5 ν * P5 μ = 0) ∧
    (∀ i : Fin 3, Rot5 i * P5 3 - P5 3 * Rot5 i = 0) ∧
    (∀ i : Fin 3, Boost5 i * P5 3 - P5 3 * Boost5 i = P5 ⟨i, by omega⟩) ∧
    (∀ i j : Fin 3, Boost5 i * P5 ⟨j, by omega⟩ - P5 ⟨j, by omega⟩ * Boost5 i =
      if i = j then P5 3 else 0) :=
  ⟨finrank_poincare, translations_commute, rotation_energy, boost_energy, boost_momentum⟩

end FUST.Physics.Poincare
