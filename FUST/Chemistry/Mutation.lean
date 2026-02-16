/-
Point Mutation Classification from State Function Model

Transitions have |ΔZ| = oxygenZ = 8.
G-C Z difference = aminoAcidCount = 20.
Complementary strand mutations preserve total Z (Chargaff conservation).
Transition/transversion ratio = 1/spinDegeneracy.
-/

import FUST.Chemistry.Translation

namespace FUST.Chemistry.Mutation

open FUST FUST.Chemistry.Nucleotide FUST.Chemistry.GeneticCode
open FUST.Chemistry.AminoAcid FUST.Chemistry.Oxygen
open FUST.Chemistry.Carbon FUST.Chemistry.Dihydrogen

/-! ## Section 1: Base Z Differences

Purine-purine and pyrimidine-pyrimidine Z differences are both oxygenZ.
-/

-- A→G transition: ΔZ = oxygenZ = 8
theorem transition_AG_Z : guanine.Z - adenine.Z = oxygenZ := rfl

-- C→T transition: ΔZ = oxygenZ = 8
theorem transition_CT_Z : thymine.Z - cytosine.Z = oxygenZ := rfl

-- Both transitions have the same |ΔZ|
theorem transitions_same_Z_change :
    guanine.Z - adenine.Z = thymine.Z - cytosine.Z := rfl

-- G-C Z difference = aminoAcidCount = 20
theorem purine_pyrimidine_max_Z_diff :
    guanine.Z - cytosine.Z = aminoAcidCount := rfl

-- A-T Z difference = 4 = baseCount
theorem purine_pyrimidine_min_Z_diff :
    adenine.Z - thymine.Z = baseCount := rfl

/-! ## Section 2: Transition Degree Changes -/

-- A→G: Δdeg = 24 = 3 × oxygenZ = spatialDim × oxygenZ
theorem transition_AG_deg :
    guanine.deg - adenine.deg = 24 := rfl

theorem transition_AG_deg_structure :
    guanine.deg - adenine.deg =
    WaveEquation.spatialDim * oxygenZ := rfl

-- C→T: Δdeg = 23
theorem transition_CT_deg :
    thymine.deg - cytosine.deg = 23 := rfl

-- Transition deg difference = 1 (= H-bond difference)
theorem transition_deg_asymmetry :
    (guanine.deg - adenine.deg) -
    (thymine.deg - cytosine.deg) = 1 := rfl

/-! ## Section 3: Chargaff Conservation Under Mutation

When A→G on one strand, the complement T→C.
Net ΔZ across both strands = 0.
-/

-- Complementary mutation: ΔZ cancels (G-A = T-C on ℕ)
theorem complementary_mutation_Z_conservation :
    guanine.Z - adenine.Z = thymine.Z - cytosine.Z := rfl

-- Both Chargaff pairs have the same total Z = 136
-- so any complementary mutation preserves double-strand Z
theorem chargaff_mutation_invariant :
    adenine.Z + thymine.Z = guanine.Z + cytosine.Z := rfl

/-! ## Section 4: Transition/Transversion Counting

4 transitions (A↔G, C↔T) vs 8 transversions.
Ratio = 4/8 = 1/spinDegeneracy.
-/

abbrev transitionCount : ℕ := 4
abbrev transversionCount : ℕ := 8

-- Total single-base substitution types = 12 = 4 bases × 3 alternatives
theorem total_substitution_types :
    transitionCount + transversionCount = baseCount * 3 := rfl

-- Transition/transversion ratio (integer division)
theorem transition_transversion_ratio :
    transversionCount / transitionCount =
    Nuclear.spinDegeneracy := rfl

/-! ## Section 5: Mutation Space of Sense Codons

61 sense codons × 3 positions × 3 alternatives = 549 possible mutations.
134 synonymous + 392 missense + 23 nonsense = 549.
-/

abbrev totalSingleBaseMutations : ℕ :=
  senseCodonCount * codonLength * 3

theorem total_mutations_eq :
    totalSingleBaseMutations = 549 := rfl

-- Synonymous (silent) mutations
abbrev synonymousMutationCount : ℕ := 134

-- Nonsynonymous (missense) mutations
abbrev missenseMutationCount : ℕ := 392

-- Nonsense (premature stop) mutations
abbrev nonsenseMutationCount : ℕ := 23

theorem mutation_partition :
    synonymousMutationCount + missenseMutationCount +
    nonsenseMutationCount = totalSingleBaseMutations := rfl

-- Nonsense mutations = 23 (prime number)
-- Synonymous fraction ≈ 134/549 ≈ 24.4%

/-! ## Section 6: Sickle Cell Disease (revisited)

GAG → GTG: A→T transversion at position 2.
Glu(Z=78) → Val(Z=64): ΔZ = -14.
This is among the largest single-point ΔZ changes in proteins.
-/

-- Base-level change: A→T (transversion)
theorem sickle_base_Z_change :
    adenine.Z - thymine.Z = baseCount := rfl

-- Protein-level change: Glu → Val
theorem sickle_protein_Z_change :
    glu.Z - val.Z = 14 := rfl

theorem sickle_protein_deg_change :
    glu.deg - val.deg = 44 := rfl

-- 44 = 4 × 11 = baseCount × 11
theorem sickle_deg_structure :
    glu.deg - val.deg = baseCount * 11 := rfl

/-! ## Section 7: Cystic Fibrosis (ΔF508)

Deletion of Phe (F) at position 508 of CFTR protein.
Residue loss: Z=78, deg=225.
-/

-- Phe residue Z (free Phe Z minus H₂O Z)
theorem cystic_fibrosis_residue_Z :
    phe.Z - 10 = 78 := rfl

-- Phe residue degree
theorem cystic_fibrosis_residue_deg :
    phe.deg - 28 = 225 := rfl

-- Phe residue Z = guanine.Z (remarkable coincidence)
theorem phe_residue_Z_eq_guanine_Z :
    phe.Z - 10 = guanine.Z := rfl

/-! ## Section 8: Summary -/

theorem mutation_classification :
    -- Transitions have ΔZ = oxygenZ
    guanine.Z - adenine.Z = oxygenZ ∧
    thymine.Z - cytosine.Z = oxygenZ ∧
    -- G-C Z difference = aminoAcidCount
    guanine.Z - cytosine.Z = aminoAcidCount ∧
    -- Chargaff conservation under complementary mutation
    adenine.Z + thymine.Z = guanine.Z + cytosine.Z ∧
    -- Mutation space partition
    synonymousMutationCount + missenseMutationCount +
      nonsenseMutationCount = 549 ∧
    -- Transition/transversion ratio
    transversionCount / transitionCount =
      Nuclear.spinDegeneracy ∧
    -- Sickle cell Glu→Val
    glu.deg - val.deg = 44 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.Mutation

namespace FUST.DiscreteTag
open FUST.Chemistry.Mutation FUST.Chemistry.AminoAcid FUST.Chemistry.Nucleotide

-- transition count = baseCount
theorem transition_count_is_baseCount :
    (⟨transitionCount⟩ : DTagged .count) = baseCount_t := rfl

-- transversion count = 2 × baseCount
theorem transversion_is_2baseCount :
    (⟨transversionCount⟩ : DTagged .count) = countMul ⟨2⟩ baseCount_t := rfl

-- transition:transversion ratio = spinDeg
theorem transition_transversion_ratio_tagged :
    (⟨transversionCount / transitionCount⟩ : DTagged .count) =
    kerToCount spinDeg_t := rfl

-- Transition A↔G Δdeg = 24 = Met oxidation
theorem transition_AG_deg_eq_metOx :
    (⟨guanine.deg - adenine.deg⟩ : DTagged .deltaDeg) = ⟨24⟩ := rfl

-- Sickle cell Δdeg = 44 = baseCount × 11
theorem sickle_cell_deltaDeg_tagged :
    (⟨glu.deg - val.deg⟩ : DTagged .deltaDeg) = ⟨44⟩ := rfl

-- Transition A→G ΔZ = C→T ΔZ
theorem transition_Z_symmetric_tagged :
    (⟨guanine.Z - adenine.Z⟩ : DTagged .protonNum) =
    (⟨thymine.Z - cytosine.Z⟩ : DTagged .protonNum) := rfl

-- Sickle cell Glu→Val ΔZ = 14 = carbonZ + oxygenZ
theorem sickle_cell_Z_tagged :
    (⟨glu.Z - val.Z⟩ : DTagged .protonNum) = carbonZ_t + oxygenZ_t := rfl

-- transition ΔZ = oxygenZ
theorem bridge_transition_Z :
    (⟨guanine.Z - adenine.Z⟩ : DTagged .protonNum).val = oxygenZ_t.val := rfl

-- sickle cell ΔZ = CO Z
theorem bridge_sickle_cell_Z :
    (⟨glu.Z - val.Z⟩ : DTagged .protonNum).val =
    (carbonZ_t + oxygenZ_t).val := rfl

end FUST.DiscreteTag
