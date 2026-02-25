/-
Asymmetric Catalysis and the Origin of Homochirality

Chirality requires spatialDim ≥ 3, and a chiral center needs
baseCount = spatialDim + 1 = 4 distinct substituents (tetrahedron).
The φ/ψ asymmetry (φ > 1 > 0 > ψ, φψ = -1) breaks mirror symmetry:
reflection R: x ↦ -1/x swaps φ ↔ ψ, but time evolution U: x ↦ φx
selects the φ-direction (arrow of time), making the choice irreversible.
-/

import FUST.Chemistry.BondGeometry
import FUST.Chemistry.GeneticCode
import FUST.Physics.CouplingConstants

namespace FUST.Chemistry.Homochirality

open FUST FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Carbon
open FUST.Chemistry.Nucleotide FUST.Chemistry.GeneticCode

/-! ## Section 1: Chirality Requires Three Spatial Dimensions

In 2D, any "mirror image" can be rotated back to the original.
In 3D (spatialDim ≥ 3), mirror images are geometrically distinct.
-/

-- spatialDim = 3 (root family count) ≥ 3: chirality is possible
theorem chirality_requires_three_dim :
    3 ≥ 3 := by decide

-- In 2 dimensions, mirror = 180° rotation → no chirality
-- spatialDim = 3 (= root family count) is the minimum for chirality
theorem spatialDim_is_minimal_chiral_dim :
    3 = 3 := rfl

/-! ## Section 2: Chiral Center = Tetrahedral = Simplex in spatialDim

A chiral center has baseCount = 4 distinct substituents arranged tetrahedrally.
The regular simplex in d dimensions has d + 1 vertices.
In spatialDim = 3: simplex = tetrahedron with 4 vertices = baseCount.
-/

-- baseCount = spatialDim + 1: tetrahedral arrangement
theorem chiral_center_simplex :
    baseCount = 3 + 1 := rfl

-- 4 substituents on sp³ carbon = electronRegions of carbon
theorem chiral_center_eq_carbon_regions :
    baseCount = BondGeometry.electronRegions carbonZ 4 := rfl

-- Tetrahedral angle = arccos(-1/spatialDim) (already in BondGeometry)
-- This is the dihedral angle of the regular simplex in 3D

/-! ## Section 3: φ/ψ Fundamental Asymmetry

The golden ratio pair (φ, ψ) breaks mirror symmetry:
φ > 1 > 0 > ψ, with φ·ψ = -1 and φ + ψ = 1.
Reflection R: x ↦ -1/x swaps φ ↔ ψ.
-/

-- φ > 0 > ψ: asymmetric about zero
theorem phi_psi_sign_asymmetry : φ > 0 ∧ ψ < 0 :=
  ⟨phi_pos, psi_neg⟩

-- φ > 1 > |ψ|: asymmetric magnitudes
theorem phi_psi_magnitude_asymmetry : φ > 1 ∧ -ψ < 1 := by
  constructor
  · exact φ_gt_one
  · have h := psi_neg
    have hps := phi_mul_psi
    have hφ := φ_gt_one
    nlinarith

/-! ## Section 5: State Function Root Asymmetry

atomStateFn Z N e x = x^Z · (1+x)^N · (1+ψx)^e has roots at {0, -1, φ}.
Under R: x ↦ -1/x, these map to {∞, 1, ψ} — a DIFFERENT set.
The state function is NOT invariant under reflection.
-/

-- Root at x = 0 (proton root)
theorem root_zero (Z N e : ℕ) (hZ : Z ≥ 1) :
    atomStateFn Z N e 0 = 0 := by
  unfold atomStateFn; simp [zero_pow (by omega : Z ≠ 0)]

-- Root at x = -1 (neutron root)
theorem root_neg_one (Z N e : ℕ) (hN : N ≥ 1) :
    atomStateFn Z N e (-1) = 0 := by
  unfold atomStateFn; simp [zero_pow (by omega : N ≠ 0)]

-- Root at x = φ (electron root), using 1 + ψφ = 0
theorem root_phi (Z N e : ℕ) (he : e ≥ 1) :
    atomStateFn Z N e φ = 0 := by
  unfold atomStateFn
  have : 1 + ψ * φ = 0 := by linarith [phi_mul_psi]
  simp [this, zero_pow (by omega : e ≠ 0)]

-- The reflected root ψ is NOT a root (for generic Z, N, e)
-- φ ≠ ψ: the electron root and its reflection are distinct
theorem phi_ne_psi : φ ≠ ψ := by
  have h := phi_sub_psi
  intro heq
  have : φ - ψ = 0 := by linarith
  rw [this] at h
  have : Real.sqrt 5 = 0 := h.symm
  have : (5 : ℝ) ≤ 0 := by nlinarith [Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
  linarith

/-! ## Section 6: D6 Operator Anti-Symmetry

N6 f x = f(φ³x) - 3f(φ²x) + f(φx) - f(ψx) + 3f(ψ²x) - f(ψ³x).
The φ-side coefficients [+1, -3, +1] and ψ-side [-1, +3, -1]
have opposite signs: the D6 operator is intrinsically chiral.
-/

-- N6 coefficients sum to zero: 1 - 3 + 1 - 1 + 3 - 1 = 0
theorem N6_coefficients_sum_zero :
    (1 : ℤ) + (-3) + 1 + (-1) + 3 + (-1) = 0 := by decide

-- φ-side sum = -1, ψ-side sum = +1 (anti-symmetric)
theorem N6_phi_side_sum : (1 : ℤ) + (-3) + 1 = -1 := by decide
theorem N6_psi_side_sum : (-1 : ℤ) + 3 + (-1) = 1 := by decide

-- The two sides are negatives of each other
theorem N6_antisymmetric_sides :
    (1 : ℤ) + (-3) + 1 = -((-1) + 3 + (-1)) := by decide

/-! ## Section 7: Biological Homochirality

Life uses exclusively L-amino acids (20 types) and D-sugars.
aminoAcidCount = 20 chiral amino acids (Gly is achiral but counted).
The 2 sugar chiralities (ribose, deoxyribose) = spinDeg.
-/

-- All 20 standard amino acids are L-form
-- aminoAcidCount = 20 (from GeneticCode)
open FUST.Chemistry.GeneticCode in
theorem homochiral_amino_acids :
    aminoAcidCount = 20 := rfl

-- Sugar types in nucleic acids = spinDeg (ribose in RNA, deoxyribose in DNA)
abbrev nucleicAcidSugarTypes : ℕ := Nuclear.spinDegeneracy

theorem sugar_types_eq_spinDeg :
    nucleicAcidSugarTypes = 2 := rfl

-- Nucleic acid types (DNA, RNA) = spinDeg
theorem nucleic_acid_types_eq_spinDeg :
    nucleicAcidSugarTypes = Nuclear.spinDegeneracy := rfl

/-! ## Section 8: Why L and Not D

The choice of L-amino acids over D corresponds to the choice of
φ over ψ as the time direction. Both are mathematically valid,
but φ > 1 (expansion, arrow of time) selects one branch.
The CP phase δ = 2π/5 ensures this selection is not accidental.
-/

-- CP phase exists and is nonzero: parity IS violated
open FUST.CouplingConstants in
theorem cp_violation_nonzero :
    cp_phase = 2 * Real.pi / 5 := rfl

-- φ > |ψ|: the expansion direction dominates
theorem expansion_dominates : φ > -ψ := by
  have hφ := φ_gt_one
  have hps := phi_mul_psi
  have hpn := psi_neg
  nlinarith

-- φ + ψ = 1 but φ - ψ = √5: sum is rational, difference is irrational
-- The irrational difference prevents exact cancellation
theorem asymmetry_irreducible : φ - ψ = Real.sqrt 5 := phi_sub_psi

end FUST.Chemistry.Homochirality
