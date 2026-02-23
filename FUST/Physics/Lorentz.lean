/-
SO(3,1) from ζ₆/φψ duality.
Compact part (ζ₆·ζ₆'=+1, |ζ₆|=1): rotations J₁,J₂,J₃ → so(3), dim=3.
Non-compact part (φψ=-1): boosts K₁,K₂,K₃, dim=3.
Combined: so(3,1), dim = 3+3 = 6.
Both share: trace=1 (φ+ψ=ζ₆+ζ₆'=1), ker dim=3, detect x³/z³.
-/
import FUST.Zeta6
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Card

namespace FUST.Physics.Lorentz

open LieAlgebra.Orthogonal Matrix FUST Zeta6

/-! ## so(3) ≃ ℝ³: rotation subalgebra -/

private theorem skew_diag {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = -A) (k : Fin 3) :
    A k k = 0 := by
  have := congr_fun (congr_fun hA k) k
  simp [transpose_apply, neg_apply] at this; linarith

private theorem skew_anti {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : Aᵀ = -A) (i j : Fin 3) :
    A j i = -(A i j) := by
  have := congr_fun (congr_fun hA j) i
  simp [transpose_apply, neg_apply] at this; linarith

private theorem buildSkew_mem (v : Fin 3 → ℝ) :
    (fun i j : Fin 3 =>
      if i = 0 ∧ j = 1 then v 0
      else if i = 0 ∧ j = 2 then v 1
      else if i = 1 ∧ j = 2 then v 2
      else if i = 1 ∧ j = 0 then -(v 0)
      else if i = 2 ∧ j = 0 then -(v 1)
      else if i = 2 ∧ j = 1 then -(v 2)
      else 0 : Matrix (Fin 3) (Fin 3) ℝ) ∈ so (Fin 3) ℝ := by
  rw [mem_so]
  ext i j
  simp only [transpose_apply, neg_apply]
  fin_cases i <;> fin_cases j <;> simp

noncomputable def extractTriple :
    (so (Fin 3) ℝ).toSubmodule →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun A := ![A.val 0 1, A.val 0 2, A.val 1 2]
  map_add' x y := by ext k; fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  map_smul' r x := by ext k; fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

noncomputable def buildSkew (v : Fin 3 → ℝ) : (so (Fin 3) ℝ).toSubmodule :=
  ⟨fun i j =>
    if i = 0 ∧ j = 1 then v 0
    else if i = 0 ∧ j = 2 then v 1
    else if i = 1 ∧ j = 2 then v 2
    else if i = 1 ∧ j = 0 then -(v 0)
    else if i = 2 ∧ j = 0 then -(v 1)
    else if i = 2 ∧ j = 1 then -(v 2)
    else 0, buildSkew_mem v⟩

private theorem extract_build (v : Fin 3 → ℝ) : extractTriple (buildSkew v) = v := by
  ext k; simp only [extractTriple, buildSkew, LinearMap.coe_mk, AddHom.coe_mk]
  fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem build_extract (A : (so (Fin 3) ℝ).toSubmodule) :
    buildSkew (extractTriple A) = A := by
  have hA : (A : Matrix (Fin 3) (Fin 3) ℝ)ᵀ = -(A : Matrix (Fin 3) (Fin 3) ℝ) :=
    (mem_so (n := Fin 3) (R := ℝ) _).mp A.prop
  ext i j
  simp only [extractTriple, buildSkew, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases i <;> fin_cases j <;> (
    first
    | rfl
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Fin.reduceEq,
        zero_ne_one, one_ne_zero, and_self, and_true, and_false, ↓reduceIte]
       first
       | exact (skew_diag hA _).symm
       | exact (skew_anti hA _ _).symm))

/-- so(3) ≃ₗ[ℝ] ℝ³ -/
noncomputable def so3EquivR3 :
    (so (Fin 3) ℝ).toSubmodule ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := extractTriple
  invFun := buildSkew
  left_inv := build_extract
  right_inv := extract_build
  map_add' := extractTriple.map_add
  map_smul' := extractTriple.map_smul

/-- dim so(3) = 3 -/
theorem finrank_so3 :
    Module.finrank ℝ (so (Fin 3) ℝ).toSubmodule = 3 := by
  rw [so3EquivR3.finrank_eq]; simp

/-! ## so(3,1) ≃ ℝ⁶: dimension via LinearEquiv -/

abbrev I4 := Fin 3 ⊕ Fin 1

private theorem entry_eq {A : Matrix I4 I4 ℝ}
    (hA : Aᵀ * (indefiniteDiagonal (Fin 3) (Fin 1) ℝ) =
          (indefiniteDiagonal (Fin 3) (Fin 1) ℝ) * (-A))
    (i j : I4) :
    (Aᵀ * (indefiniteDiagonal (Fin 3) (Fin 1) ℝ)) i j =
    ((indefiniteDiagonal (Fin 3) (Fin 1) ℝ) * (-A)) i j :=
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
      mul_one, mul_zero,
      Fin.isValue, ↓reduceIte, neg_neg, neg_zero,
      add_zero, zero_add,
      ite_false, ite_true] at $h:ident)

section EntryRelations

variable {A : Matrix I4 I4 ℝ}
    (hA : Aᵀ * (indefiniteDiagonal (Fin 3) (Fin 1) ℝ) =
          (indefiniteDiagonal (Fin 3) (Fin 1) ℝ) * (-A))

include hA

private theorem diag_00 :
    A (Sum.inl 0) (Sum.inl 0) = 0 := by
  have h := entry_eq hA (Sum.inl 0) (Sum.inl 0)
  so31_simp h; linarith
private theorem diag_11 :
    A (Sum.inl 1) (Sum.inl 1) = 0 := by
  have h := entry_eq hA (Sum.inl 1) (Sum.inl 1)
  so31_simp h; linarith
private theorem diag_22 :
    A (Sum.inl 2) (Sum.inl 2) = 0 := by
  have h := entry_eq hA (Sum.inl 2) (Sum.inl 2)
  so31_simp h; linarith
private theorem diag_33 :
    A (Sum.inr 0) (Sum.inr 0) = 0 := by
  have h := entry_eq hA (Sum.inr 0) (Sum.inr 0)
  so31_simp h; linarith

private theorem skew_01 :
    A (Sum.inl 0) (Sum.inl 1) =
      -(A (Sum.inl 1) (Sum.inl 0)) := by
  have h := entry_eq hA (Sum.inl 0) (Sum.inl 1)
  so31_simp h; linarith
private theorem skew_02 :
    A (Sum.inl 0) (Sum.inl 2) =
      -(A (Sum.inl 2) (Sum.inl 0)) := by
  have h := entry_eq hA (Sum.inl 0) (Sum.inl 2)
  so31_simp h; linarith
private theorem skew_12 :
    A (Sum.inl 1) (Sum.inl 2) =
      -(A (Sum.inl 2) (Sum.inl 1)) := by
  have h := entry_eq hA (Sum.inl 1) (Sum.inl 2)
  so31_simp h; linarith

private theorem boost_0 :
    A (Sum.inr 0) (Sum.inl 0) =
      A (Sum.inl 0) (Sum.inr 0) := by
  have h := entry_eq hA (Sum.inr 0) (Sum.inl 0)
  so31_simp h; linarith
private theorem boost_1 :
    A (Sum.inr 0) (Sum.inl 1) =
      A (Sum.inl 1) (Sum.inr 0) := by
  have h := entry_eq hA (Sum.inr 0) (Sum.inl 1)
  so31_simp h; linarith
private theorem boost_2 :
    A (Sum.inr 0) (Sum.inl 2) =
      A (Sum.inl 2) (Sum.inr 0) := by
  have h := entry_eq hA (Sum.inr 0) (Sum.inl 2)
  so31_simp h; linarith

end EntryRelations

/-! ## Build and extract maps -/

noncomputable def buildLorentz (v : Fin 6 → ℝ) :
    Matrix I4 I4 ℝ :=
  fun i j => match i, j with
  | Sum.inl a, Sum.inl b =>
    if a = 0 ∧ b = 1 then v 0
    else if a = 0 ∧ b = 2 then v 1
    else if a = 1 ∧ b = 2 then v 2
    else if a = 1 ∧ b = 0 then -(v 0)
    else if a = 2 ∧ b = 0 then -(v 1)
    else if a = 2 ∧ b = 1 then -(v 2)
    else 0
  | Sum.inl a, Sum.inr _ =>
    if a = 0 then v 3
    else if a = 1 then v 4 else v 5
  | Sum.inr _, Sum.inl a =>
    if a = 0 then v 3
    else if a = 1 then v 4 else v 5
  | Sum.inr _, Sum.inr _ => 0

private theorem buildLorentz_mem (v : Fin 6 → ℝ) :
    buildLorentz v ∈ so' (Fin 3) (Fin 1) ℝ := by
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
    (so' (Fin 3) (Fin 1) ℝ).toSubmodule →ₗ[ℝ]
      (Fin 6 → ℝ) where
  toFun A := ![A.val (Sum.inl 0) (Sum.inl 1),
               A.val (Sum.inl 0) (Sum.inl 2),
               A.val (Sum.inl 1) (Sum.inl 2),
               A.val (Sum.inl 0) (Sum.inr 0),
               A.val (Sum.inl 1) (Sum.inr 0),
               A.val (Sum.inl 2) (Sum.inr 0)]
  map_add' x y := by
    ext k; fin_cases k <;>
      simp [cons_val_zero, cons_val_one]
  map_smul' r x := by
    ext k; fin_cases k <;>
      simp [cons_val_zero, cons_val_one]

noncomputable def buildLorentzSub (v : Fin 6 → ℝ) :
    (so' (Fin 3) (Fin 1) ℝ).toSubmodule :=
  ⟨buildLorentz v, buildLorentz_mem v⟩

private theorem extract_build_lorentz (v : Fin 6 → ℝ) :
    extractSix (buildLorentzSub v) = v := by
  ext k
  simp only [extractSix, buildLorentzSub, buildLorentz,
    LinearMap.coe_mk, AddHom.coe_mk]
  fin_cases k <;> simp [cons_val_zero, cons_val_one]

private theorem mem_to_eq
    (A : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) :
    (A : Matrix I4 I4 ℝ)ᵀ *
      (indefiniteDiagonal (Fin 3) (Fin 1) ℝ) =
    (indefiniteDiagonal (Fin 3) (Fin 1) ℝ) *
      (-(A : Matrix I4 I4 ℝ)) := by
  have h := A.prop
  simp only [so', LieSubalgebra.mem_toSubmodule,
    mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule] at h
  exact h

private theorem build_extract_lorentz
    (A : (so' (Fin 3) (Fin 1) ℝ).toSubmodule) :
    buildLorentzSub (extractSix A) = A := by
  have hA := mem_to_eq A
  have h00 := entry_eq hA (Sum.inl 0) (Sum.inl 0)
  so31_simp h00
  have h11 := entry_eq hA (Sum.inl 1) (Sum.inl 1)
  so31_simp h11
  have h22 := entry_eq hA (Sum.inl 2) (Sum.inl 2)
  so31_simp h22
  have h33 := entry_eq hA (Sum.inr 0) (Sum.inr 0)
  so31_simp h33
  have h01 := entry_eq hA (Sum.inl 0) (Sum.inl 1)
  so31_simp h01
  have h02 := entry_eq hA (Sum.inl 0) (Sum.inl 2)
  so31_simp h02
  have h12 := entry_eq hA (Sum.inl 1) (Sum.inl 2)
  so31_simp h12
  have hb0 := entry_eq hA (Sum.inr 0) (Sum.inl 0)
  so31_simp hb0
  have hb1 := entry_eq hA (Sum.inr 0) (Sum.inl 1)
  so31_simp hb1
  have hb2 := entry_eq hA (Sum.inr 0) (Sum.inl 2)
  so31_simp hb2
  ext (i | i) (j | j)
  all_goals
    simp only [extractSix, buildLorentzSub, buildLorentz,
      LinearMap.coe_mk, AddHom.coe_mk,
      Subtype.coe_mk, Fin.isValue]
  · (try fin_cases i) <;> (try fin_cases j) <;>
      simp <;> linarith
  · (try fin_cases i) <;> (try fin_cases j) <;> simp
  · (try fin_cases i); (try fin_cases j) <;>
      simp <;> linarith
  · (try fin_cases i); (try fin_cases j)
    simp; linarith

/-- so(3,1) ≃ₗ[ℝ] ℝ⁶ -/
noncomputable def so31EquivR6 :
    (so' (Fin 3) (Fin 1) ℝ).toSubmodule ≃ₗ[ℝ]
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
      (so' (Fin 3) (Fin 1) ℝ).toSubmodule = 6 := by
  rw [so31EquivR6.finrank_eq]; simp

/-! ## Golden ratio root analysis → temporal dimension -/

attribute [local instance] Classical.propDecidable

/-- φ satisfies t²-t-1=0 -/
theorem phi_is_root : φ ^ 2 - φ - 1 = 0 := by linarith [golden_ratio_property]

/-- ψ satisfies t²-t-1=0 -/
theorem psi_is_root : ψ ^ 2 - ψ - 1 = 0 := by linarith [psi_sq]

/-- t²-t-1=0 has exactly two roots: φ and ψ -/
theorem golden_poly_roots (x : ℝ) (hx : x ^ 2 - x - 1 = 0) :
    x = φ ∨ x = ψ := by
  have : (x - φ) * (x - ψ) = 0 := by nlinarith [phi_add_psi, phi_mul_psi]
  rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith

/-- φ ≠ ψ -/
theorem phi_ne_psi : φ ≠ ψ := by
  intro h; have : φ - ψ = 0 := by linarith
  rw [phi_sub_psi] at this; linarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]

noncomputable def goldenRoots : Finset ℝ := {φ, ψ}

/-- Positive roots of t²-t-1: {φ} (one temporal dimension) -/
theorem positive_roots_eq :
    goldenRoots.filter (· > 0) = {φ} := by
  ext x; simp only [goldenRoots, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h_mem, h_pos⟩; rcases h_mem with rfl | rfl
    · rfl
    · linarith [psi_neg]
  · rintro rfl; exact ⟨Or.inl rfl, phi_pos⟩

/-- Temporal dimension = 1 -/
theorem temporal_dim_eq_one :
    (goldenRoots.filter (· > 0)).card = 1 := by
  rw [positive_roots_eq, Finset.card_singleton]

/-- Spacetime dim = ker dim + temporal dim = 3 + 1 = 4 -/
theorem spacetime_dim :
    ζ₆_kerDim + (goldenRoots.filter (· > 0)).card = 4 := by
  rw [temporal_dim_eq_one]; rfl

/-! ## Lie brackets of so(3,1)

Basis e_i := buildLorentz(δ_i) for i ∈ Fin 6:
  e₀,e₁,e₂ = rotations (spatial antisymmetric block)
  e₃,e₄,e₅ = boosts (space-time symmetric block)

Commutation relations [e_i, e_j] = A*B - B*A on I4×I4 matrices. -/

private noncomputable def e (i : Fin 6) : Fin 6 → ℝ :=
  fun j => if j = i then 1 else 0

private theorem lie_e0_e1 :
    buildLorentz (e 0) * buildLorentz (e 1) -
    buildLorentz (e 1) * buildLorentz (e 0) =
    -(buildLorentz (e 2)) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e0_e2 :
    buildLorentz (e 0) * buildLorentz (e 2) -
    buildLorentz (e 2) * buildLorentz (e 0) =
    buildLorentz (e 1) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e1_e2 :
    buildLorentz (e 1) * buildLorentz (e 2) -
    buildLorentz (e 2) * buildLorentz (e 1) =
    -(buildLorentz (e 0)) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e3_e4 :
    buildLorentz (e 3) * buildLorentz (e 4) -
    buildLorentz (e 4) * buildLorentz (e 3) =
    buildLorentz (e 0) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e3_e5 :
    buildLorentz (e 3) * buildLorentz (e 5) -
    buildLorentz (e 5) * buildLorentz (e 3) =
    buildLorentz (e 1) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e4_e5 :
    buildLorentz (e 4) * buildLorentz (e 5) -
    buildLorentz (e 5) * buildLorentz (e 4) =
    buildLorentz (e 2) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e0_e3 :
    buildLorentz (e 0) * buildLorentz (e 3) -
    buildLorentz (e 3) * buildLorentz (e 0) =
    -(buildLorentz (e 4)) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type]

private theorem lie_e0_e4 :
    buildLorentz (e 0) * buildLorentz (e 4) -
    buildLorentz (e 4) * buildLorentz (e 0) =
    buildLorentz (e 3) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e1_e3 :
    buildLorentz (e 1) * buildLorentz (e 3) -
    buildLorentz (e 3) * buildLorentz (e 1) =
    -(buildLorentz (e 5)) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e1_e5 :
    buildLorentz (e 1) * buildLorentz (e 5) -
    buildLorentz (e 5) * buildLorentz (e 1) =
    buildLorentz (e 3) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e2_e4 :
    buildLorentz (e 2) * buildLorentz (e 4) -
    buildLorentz (e 4) * buildLorentz (e 2) =
    -(buildLorentz (e 5)) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e2_e5 :
    buildLorentz (e 2) * buildLorentz (e 5) -
    buildLorentz (e 5) * buildLorentz (e 2) =
    buildLorentz (e 4) := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e0_e5 :
    buildLorentz (e 0) * buildLorentz (e 5) -
    buildLorentz (e 5) * buildLorentz (e 0) =
    0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e1_e4 :
    buildLorentz (e 1) * buildLorentz (e 4) -
    buildLorentz (e 4) * buildLorentz (e 1) =
    0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

private theorem lie_e2_e3 :
    buildLorentz (e 2) * buildLorentz (e 3) -
    buildLorentz (e 3) * buildLorentz (e 2) =
    0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> (try fin_cases j) <;>
    simp [buildLorentz, e, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three]

/-! ## so(3,1) Lie algebra structure constants

Rotation-Rotation: [e_i, e_j] = -ε_{ijk} e_k
Boost-Boost: [e_{i+3}, e_{j+3}] = +ε_{ijk} e_k (rotation!)
Rotation-Boost: [e_i, e_{j+3}] = -ε_{ijk} e_{k+3} -/

/-- All 15 brackets of so(3,1) basis -/
theorem so31_brackets :
    -- [rotation, rotation] → -rotation (so(3) subalgebra)
    buildLorentz (e 0) * buildLorentz (e 1) -
      buildLorentz (e 1) * buildLorentz (e 0) = -(buildLorentz (e 2)) ∧
    buildLorentz (e 1) * buildLorentz (e 2) -
      buildLorentz (e 2) * buildLorentz (e 1) = -(buildLorentz (e 0)) ∧
    buildLorentz (e 0) * buildLorentz (e 2) -
      buildLorentz (e 2) * buildLorentz (e 0) = buildLorentz (e 1) ∧
    -- [boost, boost] → +rotation (compact return)
    buildLorentz (e 3) * buildLorentz (e 4) -
      buildLorentz (e 4) * buildLorentz (e 3) = buildLorentz (e 0) ∧
    buildLorentz (e 4) * buildLorentz (e 5) -
      buildLorentz (e 5) * buildLorentz (e 4) = buildLorentz (e 2) ∧
    buildLorentz (e 3) * buildLorentz (e 5) -
      buildLorentz (e 5) * buildLorentz (e 3) = buildLorentz (e 1) ∧
    -- [rotation, boost] → boost
    buildLorentz (e 0) * buildLorentz (e 3) -
      buildLorentz (e 3) * buildLorentz (e 0) = -(buildLorentz (e 4)) ∧
    buildLorentz (e 0) * buildLorentz (e 4) -
      buildLorentz (e 4) * buildLorentz (e 0) = buildLorentz (e 3) ∧
    buildLorentz (e 1) * buildLorentz (e 3) -
      buildLorentz (e 3) * buildLorentz (e 1) = -(buildLorentz (e 5)) ∧
    buildLorentz (e 1) * buildLorentz (e 5) -
      buildLorentz (e 5) * buildLorentz (e 1) = buildLorentz (e 3) ∧
    buildLorentz (e 2) * buildLorentz (e 4) -
      buildLorentz (e 4) * buildLorentz (e 2) = -(buildLorentz (e 5)) ∧
    buildLorentz (e 2) * buildLorentz (e 5) -
      buildLorentz (e 5) * buildLorentz (e 2) = buildLorentz (e 4) ∧
    -- [rotation_i, boost_i] = 0 (same axis)
    buildLorentz (e 0) * buildLorentz (e 5) -
      buildLorentz (e 5) * buildLorentz (e 0) = 0 ∧
    buildLorentz (e 1) * buildLorentz (e 4) -
      buildLorentz (e 4) * buildLorentz (e 1) = 0 ∧
    buildLorentz (e 2) * buildLorentz (e 3) -
      buildLorentz (e 3) * buildLorentz (e 2) = 0 :=
  ⟨lie_e0_e1, lie_e1_e2, lie_e0_e2, lie_e3_e4, lie_e4_e5, lie_e3_e5,
   lie_e0_e3, lie_e0_e4, lie_e1_e3, lie_e1_e5, lie_e2_e4, lie_e2_e5,
   lie_e0_e5, lie_e1_e4, lie_e2_e3⟩

end FUST.Physics.Lorentz
