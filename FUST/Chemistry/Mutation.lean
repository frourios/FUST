/-
Point Mutation Classification from FDim Structure

Transitions have |ΔZ| = oxygenZ = 8.
G-C Z difference = aminoAcidCount = 20.
Complementary strand mutations preserve total Z (Chargaff conservation).
Transition/transversion ratio = 1/spinDegeneracy.
-/

import FUST.Chemistry.Translation

namespace FUST.Chemistry.Mutation

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Nucleotide
open FUST.Chemistry.GeneticCode
open FUST.Chemistry.AminoAcid FUST.Chemistry.Oxygen
open FUST.Chemistry.Carbon FUST.Chemistry.Dihydrogen

/-! ## Section 1: Base Z Differences

Purine-purine and pyrimidine-pyrimidine Z differences are both oxygenZ.
-/

-- A→G transition: ΔZ = oxygenZ = 8
theorem transition_AG_Z : guanineZ - adenineZ = oxygenZ := rfl

-- C→T transition: ΔZ = oxygenZ = 8
theorem transition_CT_Z : thymineZ - cytosineZ = oxygenZ := rfl

-- Both transitions have the same |ΔZ|
theorem transitions_same_Z_change :
    guanineZ - adenineZ = thymineZ - cytosineZ := rfl

-- G-C Z difference = aminoAcidCount = 20
theorem purine_pyrimidine_max_Z_diff :
    guanineZ - cytosineZ = aminoAcidCount := rfl

-- A-T Z difference = 4 = baseCount
theorem purine_pyrimidine_min_Z_diff :
    adenineZ - thymineZ = baseCount := rfl

/-! ## Section 2: Chargaff Conservation Under Mutation

When A→G on one strand, the complement T→C.
Net ΔZ across both strands = 0.
-/

theorem complementary_mutation_Z_conservation :
    guanineZ - adenineZ = thymineZ - cytosineZ := rfl

theorem chargaff_mutation_invariant :
    adenineZ + thymineZ = guanineZ + cytosineZ := rfl

/-! ## Section 3: Transition/Transversion Counting

4 transitions (A↔G, C↔T) vs 8 transversions.
Ratio = 4/8 = 1/spinDegeneracy.
-/

abbrev transitionCount : ℕ := 4
abbrev transversionCount : ℕ := 8

-- Total single-base substitution types = 12 = 4 × 3
theorem total_substitution_types :
    transitionCount + transversionCount = baseCount * 3 := rfl

theorem transition_transversion_ratio :
    transversionCount / transitionCount =
    Nuclear.spinDegeneracy := rfl

/-! ## Section 4: Mutation Space of Sense Codons

61 sense codons × 3 positions × 3 alternatives = 549 possible mutations.
-/

abbrev totalSingleBaseMutations : ℕ :=
  senseCodonCount * codonLength * 3

theorem total_mutations_eq :
    totalSingleBaseMutations = 549 := rfl

abbrev synonymousMutationCount : ℕ := 134
abbrev missenseMutationCount : ℕ := 392
abbrev nonsenseMutationCount : ℕ := 23

theorem mutation_partition :
    synonymousMutationCount + missenseMutationCount +
    nonsenseMutationCount = totalSingleBaseMutations := rfl

/-! ## Section 5: Sickle Cell Disease

GAG → GTG: A→T transversion at position 2.
Glu(Z=78) → Val(Z=64): ΔZ = -14.
-/

-- Base-level change: A→T (transversion)
theorem sickle_base_Z_change :
    adenineZ - thymineZ = baseCount := rfl

-- Protein-level change: Glu → Val
theorem sickle_protein_Z_change :
    gluZ - valZ = 14 := rfl

/-! ## Section 6: Cystic Fibrosis (ΔF508)

Deletion of Phe (F) at position 508 of CFTR protein.
Phe residue Z = pheZ - 10 = 78 = guanineZ.
-/

theorem cystic_fibrosis_residue_Z :
    pheZ - 10 = 78 := rfl

-- Phe residue Z = guanineZ
theorem phe_residue_Z_eq_guanine_Z :
    pheZ - 10 = guanineZ := rfl

/-! ## Section 7: Summary -/

theorem mutation_classification :
    guanineZ - adenineZ = oxygenZ ∧
    thymineZ - cytosineZ = oxygenZ ∧
    guanineZ - cytosineZ = aminoAcidCount ∧
    adenineZ + thymineZ = guanineZ + cytosineZ ∧
    synonymousMutationCount + missenseMutationCount +
      nonsenseMutationCount = 549 ∧
    transversionCount / transitionCount =
      Nuclear.spinDegeneracy ∧
    gluZ - valZ = 14 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.Mutation
