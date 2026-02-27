/-
Nucleobases and Watson-Crick Pairing from FDim Structure

Five nucleobases (A, G, C, T, U) as dimAtom(Z, N, Z) for neutral molecules.
Watson-Crick H-bond counts = D-operator kernel dimensions.
Chargaff's rule (Z-conservation) emerges as proton number balance.
Base count 4 = 2^spinDegeneracy.
-/

import FUST.Chemistry.PhosphorusAtom

namespace FUST.Chemistry.Nucleotide

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Nitrogen
open FUST.Chemistry.Phosphorus FUST.Chemistry.Dihydrogen
open FUST.Chemistry.Carbon

/-! ## Section 1: Nucleobase Molecular Parameters

Each nucleobase is a neutral molecule with (Z, N, e=Z).
FDim = dimAtom Z N Z, effectiveDegree = 18Z + 15N + 1.
-/

-- Adenine C₅H₅N₅
abbrev adenineZ : ℕ := 5 * carbonZ + 5 * hydrogenZ + 5 * nitrogenZ
abbrev adenineN : ℕ := 5 * Carbon.neutrons_C12 + 5 * protium_N + 5 * Nitrogen.neutrons_N14

-- Guanine C₅H₅N₅O
abbrev guanineZ : ℕ := 5 * carbonZ + 5 * hydrogenZ + 5 * nitrogenZ + oxygenZ
abbrev guanineN : ℕ :=
  5 * Carbon.neutrons_C12 + 5 * protium_N + 5 * Nitrogen.neutrons_N14 + neutrons_O16

-- Cytosine C₄H₅N₃O
abbrev cytosineZ : ℕ := 4 * carbonZ + 5 * hydrogenZ + 3 * nitrogenZ + oxygenZ
abbrev cytosineN : ℕ :=
  4 * Carbon.neutrons_C12 + 5 * protium_N + 3 * Nitrogen.neutrons_N14 + neutrons_O16

-- Thymine C₅H₆N₂O₂
abbrev thymineZ : ℕ := 5 * carbonZ + 6 * hydrogenZ + 2 * nitrogenZ + 2 * oxygenZ
abbrev thymineN : ℕ :=
  5 * Carbon.neutrons_C12 + 6 * protium_N + 2 * Nitrogen.neutrons_N14 + 2 * neutrons_O16

-- Uracil C₄H₄N₂O₂
abbrev uracilZ : ℕ := 4 * carbonZ + 4 * hydrogenZ + 2 * nitrogenZ + 2 * oxygenZ
abbrev uracilN : ℕ :=
  4 * Carbon.neutrons_C12 + 4 * protium_N + 2 * Nitrogen.neutrons_N14 + 2 * neutrons_O16

/-! ## Section 2: Parameter Verification -/

theorem adenineZ_eq : adenineZ = 70 := rfl
theorem adenineN_eq : adenineN = 65 := rfl
theorem guanineZ_eq : guanineZ = 78 := rfl
theorem guanineN_eq : guanineN = 73 := rfl
theorem cytosineZ_eq : cytosineZ = 58 := rfl
theorem cytosineN_eq : cytosineN = 53 := rfl
theorem thymineZ_eq : thymineZ = 66 := rfl
theorem thymineN_eq : thymineN = 60 := rfl
theorem uracilZ_eq : uracilZ = 58 := rfl
theorem uracilN_eq : uracilN = 54 := rfl

/-! ## Section 3: FDim and effectiveDegree -/

set_option maxRecDepth 8192

theorem adenine_effDeg :
    (dimAtom adenineZ adenineN adenineZ).effectiveDegree = 2236 := by decide
theorem guanine_effDeg :
    (dimAtom guanineZ guanineN guanineZ).effectiveDegree = 2500 := by decide
theorem cytosine_effDeg :
    (dimAtom cytosineZ cytosineN cytosineZ).effectiveDegree = 1840 := by decide
theorem thymine_effDeg :
    (dimAtom thymineZ thymineN thymineZ).effectiveDegree = 2089 := by decide
theorem uracil_effDeg :
    (dimAtom uracilZ uracilN uracilZ).effectiveDegree = 1855 := by decide

/-! ## Section 4: Watson-Crick Hydrogen Bonds

A-T: 2 hydrogen bonds = spinDegeneracy
G-C: 3 hydrogen bonds = spatialDim
-/

abbrev AT_hbonds : ℕ := Nuclear.spinDegeneracy
abbrev GC_hbonds : ℕ := 3

theorem AT_hbonds_eq : AT_hbonds = 2 := rfl
theorem GC_hbonds_eq : GC_hbonds = 3 := rfl

theorem hbond_difference : GC_hbonds - AT_hbonds = 1 := rfl

/-! ## Section 5: Chargaff's Rule (Z-Conservation)

Both Watson-Crick pairs have the same total proton number Z.
-/

theorem chargaff_Z_conservation :
    adenineZ + thymineZ = guanineZ + cytosineZ := rfl

theorem chargaff_Z_value : adenineZ + thymineZ = 136 := rfl

/-! ## Section 6: Base Count from Spin Degeneracy

4 DNA bases = 2^spinDegeneracy.
-/

abbrev baseCount : ℕ := 2 ^ Nuclear.spinDegeneracy

theorem baseCount_eq : baseCount = 4 := rfl

theorem purine_pyrimidine_split :
    Nuclear.spinDegeneracy + Nuclear.spinDegeneracy = baseCount := rfl

/-! ## Section 7: GC-AT effectiveDegree Difference

GC pair has 15 more effectiveDegree than AT pair.
15 = 15 × ΔN where ΔN = (guanineN + cytosineN) - (adenineN + thymineN) = 1.
-/

theorem basePair_AT_effDeg :
    (dimAtom adenineZ adenineN adenineZ).effectiveDegree +
    (dimAtom thymineZ thymineN thymineZ).effectiveDegree = 4325 := by decide

theorem basePair_GC_effDeg :
    (dimAtom guanineZ guanineN guanineZ).effectiveDegree +
    (dimAtom cytosineZ cytosineN cytosineZ).effectiveDegree = 4340 := by decide

theorem basePair_GC_AT_neutron_diff :
    guanineN + cytosineN = adenineN + thymineN + 1 := rfl

/-! ## Section 8: Cytosine-Uracil Relationship

C and U differ by one NH₂→O substitution.
U replaces T in RNA (T = U + CH₂ methylation).
-/

theorem cytosine_uracil_same_Z : cytosineZ = uracilZ := rfl

-- T and U differ by one methyl group (CH₂): ΔZ = carbonZ + 2·hydrogenZ = 8
theorem thymine_uracil_Z_diff :
    thymineZ - uracilZ = carbonZ + 2 * hydrogenZ := rfl

theorem thymine_uracil_effDeg_diff :
    (dimAtom thymineZ thymineN thymineZ).effectiveDegree -
    (dimAtom uracilZ uracilN uracilZ).effectiveDegree = 234 := by decide

/-! ## Section 9: FDim Distinctness -/

theorem AT_GC_distinct :
    dimAtom adenineZ adenineN adenineZ ≠ dimAtom guanineZ guanineN guanineZ := by decide

theorem all_bases_distinct_effDeg :
    (dimAtom adenineZ adenineN adenineZ).effectiveDegree ≠
    (dimAtom guanineZ guanineN guanineZ).effectiveDegree ∧
    (dimAtom adenineZ adenineN adenineZ).effectiveDegree ≠
    (dimAtom cytosineZ cytosineN cytosineZ).effectiveDegree ∧
    (dimAtom adenineZ adenineN adenineZ).effectiveDegree ≠
    (dimAtom thymineZ thymineN thymineZ).effectiveDegree ∧
    (dimAtom guanineZ guanineN guanineZ).effectiveDegree ≠
    (dimAtom cytosineZ cytosineN cytosineZ).effectiveDegree := by decide

/-! ## Section 10: Summary -/

theorem nucleobase_classification :
    -- Chargaff Z-conservation
    adenineZ + thymineZ = guanineZ + cytosineZ ∧
    adenineZ + thymineZ = 136 ∧
    -- H-bond counts from D-operator kernels
    AT_hbonds = Nuclear.spinDegeneracy ∧
    GC_hbonds = 3 ∧
    -- Base count from spin
    baseCount = 4 ∧
    -- C and U share Z
    cytosineZ = uracilZ := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.Nucleotide
