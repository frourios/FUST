/-
so(3,1) ≃ ℝ⁶: Lorentz algebra dimension from indefinite diagonal (1,3).
I4 = Fin 1 ⊕ Fin 3: spacetime index type.
-/
import FUST.DζOperator
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace FUST.Physics.Lorentz

open LieAlgebra.Orthogonal Matrix

/-! ## so(3,1) ≃ ℝ⁶: dimension via LinearEquiv -/

/-- Spacetime index type. Justified by Dζ channel decomposition:
1 AF channel (temporal, AF_coeff_eq) + 3 SY sub-operators (spatial, Φ_S_rank_three). -/
abbrev I4 := Fin 1 ⊕ Fin 3

private theorem entry_eq {A : Matrix I4 I4 ℝ}
    (hA : Aᵀ * (indefiniteDiagonal (Fin 1) (Fin 3) ℝ) =
          (indefiniteDiagonal (Fin 1) (Fin 3) ℝ) * (-A))
    (i j : I4) :
    (Aᵀ * (indefiniteDiagonal (Fin 1) (Fin 3) ℝ)) i j =
    ((indefiniteDiagonal (Fin 1) (Fin 3) ℝ) * (-A)) i j :=
  congr_fun (congr_fun hA i) j

syntax "so31_simp" ident : tactic
macro_rules
  | `(tactic| so31_simp $h) =>
    `(tactic| simp (config := { decide := true }) only [
      indefiniteDiagonal, transpose_apply,
      mul_apply, diagonal_apply, Sum.elim_inl, Sum.elim_inr,
      neg_apply, Fintype.sum_sum_type,
      Fin.sum_univ_three, Fin.sum_univ_one,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      ite_mul, one_mul, zero_mul, mul_neg, mul_ite,
      mul_one, mul_zero, neg_one_mul,
      Fin.isValue, ↓reduceIte, neg_neg, neg_zero,
      add_zero, zero_add,
      ite_false, ite_true] at $h:ident)

section EntryRelations

variable {A : Matrix I4 I4 ℝ}
    (hA : Aᵀ * (indefiniteDiagonal (Fin 1) (Fin 3) ℝ) =
          (indefiniteDiagonal (Fin 1) (Fin 3) ℝ) * (-A))

include hA

private theorem diag_00 :
    A (Sum.inl 0) (Sum.inl 0) = 0 := by
  have h := entry_eq hA (Sum.inl 0) (Sum.inl 0)
  so31_simp h; linarith
private theorem diag_11 :
    A (Sum.inr 0) (Sum.inr 0) = 0 := by
  have h := entry_eq hA (Sum.inr 0) (Sum.inr 0)
  so31_simp h; linarith
private theorem diag_22 :
    A (Sum.inr 1) (Sum.inr 1) = 0 := by
  have h := entry_eq hA (Sum.inr 1) (Sum.inr 1)
  so31_simp h; linarith
private theorem diag_33 :
    A (Sum.inr 2) (Sum.inr 2) = 0 := by
  have h := entry_eq hA (Sum.inr 2) (Sum.inr 2)
  so31_simp h; linarith

private theorem skew_01 :
    A (Sum.inr 0) (Sum.inr 1) =
      -(A (Sum.inr 1) (Sum.inr 0)) := by
  have h := entry_eq hA (Sum.inr 0) (Sum.inr 1)
  so31_simp h; linarith
private theorem skew_02 :
    A (Sum.inr 0) (Sum.inr 2) =
      -(A (Sum.inr 2) (Sum.inr 0)) := by
  have h := entry_eq hA (Sum.inr 0) (Sum.inr 2)
  so31_simp h; linarith
private theorem skew_12 :
    A (Sum.inr 1) (Sum.inr 2) =
      -(A (Sum.inr 2) (Sum.inr 1)) := by
  have h := entry_eq hA (Sum.inr 1) (Sum.inr 2)
  so31_simp h; linarith

private theorem boost_0 :
    A (Sum.inr 0) (Sum.inl 0) =
      A (Sum.inl 0) (Sum.inr 0) := by
  have h := entry_eq hA (Sum.inr 0) (Sum.inl 0)
  so31_simp h; linarith
private theorem boost_1 :
    A (Sum.inr 1) (Sum.inl 0) =
      A (Sum.inl 0) (Sum.inr 1) := by
  have h := entry_eq hA (Sum.inr 1) (Sum.inl 0)
  so31_simp h; linarith
private theorem boost_2 :
    A (Sum.inr 2) (Sum.inl 0) =
      A (Sum.inl 0) (Sum.inr 2) := by
  have h := entry_eq hA (Sum.inr 2) (Sum.inl 0)
  so31_simp h; linarith

end EntryRelations

/-! ## Build and extract maps -/

noncomputable def buildLorentz (v : Fin 6 → ℝ) :
    Matrix I4 I4 ℝ :=
  fun i j => match i, j with
  | Sum.inr a, Sum.inr b =>
    if a = 0 ∧ b = 1 then v 0
    else if a = 0 ∧ b = 2 then v 1
    else if a = 1 ∧ b = 2 then v 2
    else if a = 1 ∧ b = 0 then -(v 0)
    else if a = 2 ∧ b = 0 then -(v 1)
    else if a = 2 ∧ b = 1 then -(v 2)
    else 0
  | Sum.inl _, Sum.inr a =>
    if a = 0 then v 3
    else if a = 1 then v 4 else v 5
  | Sum.inr a, Sum.inl _ =>
    if a = 0 then v 3
    else if a = 1 then v 4 else v 5
  | Sum.inl _, Sum.inl _ => 0

private theorem buildLorentz_mem (v : Fin 6 → ℝ) :
    buildLorentz v ∈ so' (Fin 1) (Fin 3) ℝ := by
  simp only [so', mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule,
    Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  ext (i | i) (j | j) <;>
    simp only [buildLorentz, indefiniteDiagonal,
      transpose_apply, mul_apply, diagonal_apply,
      Sum.elim_inl, Sum.elim_inr, neg_apply,
      Fintype.sum_sum_type,
      Fin.sum_univ_three, Fin.sum_univ_one] <;>
    (try fin_cases i) <;> (try fin_cases j) <;> simp

noncomputable def extractSix :
    (so' (Fin 1) (Fin 3) ℝ).toSubmodule →ₗ[ℝ]
      (Fin 6 → ℝ) where
  toFun A := ![A.val (Sum.inr 0) (Sum.inr 1),
               A.val (Sum.inr 0) (Sum.inr 2),
               A.val (Sum.inr 1) (Sum.inr 2),
               A.val (Sum.inl 0) (Sum.inr 0),
               A.val (Sum.inl 0) (Sum.inr 1),
               A.val (Sum.inl 0) (Sum.inr 2)]
  map_add' x y := by
    ext k; fin_cases k <;>
      simp [cons_val_zero, cons_val_one]
  map_smul' r x := by
    ext k; fin_cases k <;>
      simp [cons_val_zero, cons_val_one]

noncomputable def buildLorentzSub (v : Fin 6 → ℝ) :
    (so' (Fin 1) (Fin 3) ℝ).toSubmodule :=
  ⟨buildLorentz v, buildLorentz_mem v⟩

private theorem extract_build_lorentz (v : Fin 6 → ℝ) :
    extractSix (buildLorentzSub v) = v := by
  ext k
  simp only [extractSix, buildLorentzSub, buildLorentz,
    LinearMap.coe_mk, AddHom.coe_mk]
  fin_cases k <;> simp [cons_val_zero, cons_val_one]

private theorem mem_to_eq
    (A : (so' (Fin 1) (Fin 3) ℝ).toSubmodule) :
    (A : Matrix I4 I4 ℝ)ᵀ *
      (indefiniteDiagonal (Fin 1) (Fin 3) ℝ) =
    (indefiniteDiagonal (Fin 1) (Fin 3) ℝ) *
      (-(A : Matrix I4 I4 ℝ)) := by
  have h := A.prop
  simp only [so', LieSubalgebra.mem_toSubmodule,
    mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule] at h
  exact h

private theorem build_extract_lorentz
    (A : (so' (Fin 1) (Fin 3) ℝ).toSubmodule) :
    buildLorentzSub (extractSix A) = A := by
  have hA := mem_to_eq A
  have h00 := entry_eq hA (Sum.inl 0) (Sum.inl 0)
  so31_simp h00
  have h11 := entry_eq hA (Sum.inr 0) (Sum.inr 0)
  so31_simp h11
  have h22 := entry_eq hA (Sum.inr 1) (Sum.inr 1)
  so31_simp h22
  have h33 := entry_eq hA (Sum.inr 2) (Sum.inr 2)
  so31_simp h33
  have h01 := entry_eq hA (Sum.inr 0) (Sum.inr 1)
  so31_simp h01
  have h02 := entry_eq hA (Sum.inr 0) (Sum.inr 2)
  so31_simp h02
  have h12 := entry_eq hA (Sum.inr 1) (Sum.inr 2)
  so31_simp h12
  have hb0 := entry_eq hA (Sum.inr 0) (Sum.inl 0)
  so31_simp hb0
  have hb1 := entry_eq hA (Sum.inr 1) (Sum.inl 0)
  so31_simp hb1
  have hb2 := entry_eq hA (Sum.inr 2) (Sum.inl 0)
  so31_simp hb2
  ext (i | i) (j | j)
  all_goals
    simp only [extractSix, buildLorentzSub, buildLorentz,
      LinearMap.coe_mk, AddHom.coe_mk,
      Subtype.coe_mk, Fin.isValue]
  all_goals fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- so(3,1) ≃ₗ[ℝ] ℝ⁶ -/
noncomputable def so31EquivR6 :
    (so' (Fin 1) (Fin 3) ℝ).toSubmodule ≃ₗ[ℝ]
      (Fin 6 → ℝ) where
  toFun := extractSix
  invFun := buildLorentzSub
  left_inv := build_extract_lorentz
  right_inv := extract_build_lorentz
  map_add' := extractSix.map_add
  map_smul' := extractSix.map_smul

/-- dim so(3,1) = 6 -/
theorem finrank_so31 :
    Module.finrank ℝ
      (so' (Fin 1) (Fin 3) ℝ).toSubmodule = 6 := by
  rw [so31EquivR6.finrank_eq]; simp

end FUST.Physics.Lorentz
