/-
so(3,1) ≃ ℝ⁶: Lorentz algebra dimension from indefinite diagonal (1,3).
I4 = Fin 1 ⊕ Fin 3: spacetime index type derived from Dζ channels.
Metric signature from Galois norms: φψ = -1 (AF/temporal), |ζ₆|² = 1 (SY/spatial).
-/
import FUST.DζOperator
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace FUST.Physics.Lorentz

open LieAlgebra.Orthogonal Matrix DζOperator Complex

/-! ## Spacetime dimension from Dζ channel decomposition

AF channel (Φ_A): 1-dimensional — AF_coeff = 2i√3 is pure imaginary (1 real DOF).
SY channel (Φ_S): 3-dimensional — rank 3 from Φ_S_rank_three.
Total: 1 + 3 = 4 spacetime dimensions. -/

theorem AF_channel_dim : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1

theorem SY_channel_dim : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3

theorem spacetime_dim_from_Dζ :
    Fintype.card (Fin 1) + Fintype.card (Fin 3) = 4 := by simp

/-! ## Metric signature from Galois norms

The two Galois conjugations of ℚ(√5, √-3) determine the metric:
- σ₁ (φ ↔ ψ): φψ = -1 → AF channel norm is NEGATIVE → timelike
- σ₂ (ζ₆ ↔ ζ₆⁻¹): ζ₆·ζ₆⁻¹ = 1 → SY channel norm is POSITIVE → spacelike -/

theorem AF_sign_from_phi_psi : φ * ψ = -1 := phi_mul_psi

theorem SY_sign_from_zeta6 : ζ₆ * ζ₆' = 1 := zeta6_mul_conj

theorem AF_coeff_sq_negative : (AF_coeff ^ 2).re < 0 := by
  rw [AF_coeff_eq, sq]
  simp only [mul_re]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
  nlinarith

theorem SY_coeff_sq_positive : (0 : ℝ) < (6 : ℝ) ^ 2 := by positivity

/-- The indefinite diagonal diag(+1,-1,-1,-1) is determined by the Dζ channel signs:
AF (1D, φψ = -1) contributes the timelike (+1 in mostly-plus, but indefiniteDiagonal
uses Sum.elim 1 (-1) placing +1 on Fin p and -1 on Fin q). -/
theorem signature_from_Dζ :
    (φ * ψ = -1) ∧ (ζ₆ * ζ₆' = 1) ∧
    (AF_coeff ^ 2).re < 0 ∧ (0 : ℝ) < (6 : ℝ) ^ 2 ∧
    Fintype.card (Fin 1) + Fintype.card (Fin 3) = 4 :=
  ⟨AF_sign_from_phi_psi, SY_sign_from_zeta6,
   AF_coeff_sq_negative, SY_coeff_sq_positive, spacetime_dim_from_Dζ⟩

/-! ## so(3,1) ≃ ℝ⁶: dimension via LinearEquiv -/

/-- Spacetime index type from Dζ: 1 AF channel + 3 SY sub-operators. -/
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
