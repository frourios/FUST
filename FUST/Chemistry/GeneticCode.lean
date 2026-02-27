/-
Genetic Code from Particle Root Structure

Codon length 3 = spatialDim.
Total codons 64 = 4³ = baseCount^spatialDim.
Standard amino acids 20 = nuclearMagic(2).
Stop codons 3 = spatialDim.
DNA→RNA transcription: T→U substitution with ΔeffDeg = 234.
-/

import FUST.Chemistry.Nucleotides

namespace FUST.Chemistry.GeneticCode

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen
open FUST.Chemistry.Nucleotide
open FUST.Chemistry.Carbon FUST.Chemistry.Dihydrogen

/-! ## Section 1: Codon Structure

Codons are triplets of nucleotide bases.
Codon length = spatialDim = 3 (three root families in particle structure).
-/

abbrev codonLength : ℕ := 3

theorem codonLength_eq : codonLength = 3 := rfl

abbrev codonCount : ℕ := baseCount ^ codonLength

theorem codonCount_eq : codonCount = 64 := rfl

-- 64 = 4³ = (2^spinDeg)^spatialDim = 2^(spinDeg × spatialDim) = 2^6
theorem codonCount_binary :
    codonCount = 2 ^ (Nuclear.spinDegeneracy * 3) := rfl

-- codonCount = 2^carbonZ (carbonZ = spinDeg × spatialDim = 6)
theorem codonCount_eq_two_pow_carbonZ :
    codonCount = 2 ^ carbonZ := rfl

/-! ## Section 2: Amino Acids and Stop Codons

20 standard amino acids = nuclearMagic(2) = hoMagic(2).
3 stop codons = spatialDim.
61 sense codons = 64 - 3.
-/

abbrev aminoAcidCount : ℕ := Nuclear.nuclearMagic 2

theorem aminoAcidCount_eq : aminoAcidCount = 20 := rfl

abbrev stopCodonCount : ℕ := 3

theorem stopCodonCount_eq : stopCodonCount = 3 := rfl

abbrev senseCodonCount : ℕ := codonCount - stopCodonCount

theorem senseCodonCount_eq : senseCodonCount = 61 := rfl

-- Degeneracy: average codons per amino acid
theorem codon_degeneracy_quotient :
    senseCodonCount / aminoAcidCount = 3 := rfl

theorem codon_degeneracy_remainder :
    senseCodonCount % aminoAcidCount = 1 := rfl

-- aminoAcidCount is a nuclear magic number
theorem aminoAcid_is_magic :
    ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = aminoAcidCount :=
  ⟨2, by omega, rfl⟩

-- stopCodonCount = spatialDim = GC_hbonds
theorem stop_codon_spatial : stopCodonCount = GC_hbonds := rfl

/-! ## Section 3: DNA vs RNA Transcription

DNA uses thymine (T), RNA uses uracil (U).
T = U + methyl group (CH₂): ΔZ = carbonZ + 2·hydrogenZ = 8.
-/

-- T→U substitution Z change
theorem transcription_Z_change :
    thymineZ - uracilZ = carbonZ + 2 * hydrogenZ := rfl

theorem transcription_Z_change_value : thymineZ - uracilZ = 8 := rfl

-- T→U substitution N change
theorem transcription_N_change : thymineN - uracilN = 6 := rfl

/-! ## Section 4: Central Dogma EffDeg Algebra

DNA → RNA → Protein (Central Dogma).
Each step has a well-defined effectiveDegree transformation.
-/

set_option maxRecDepth 8192

-- Start codon AUG effectiveDegree sum
theorem start_codon_effDeg :
    (dimAtom adenineZ adenineN adenineZ).effectiveDegree +
    (dimAtom uracilZ uracilN uracilZ).effectiveDegree +
    (dimAtom guanineZ guanineN guanineZ).effectiveDegree = 6591 := by
  decide

-- DNA version: ATG
theorem start_codon_DNA_effDeg :
    (dimAtom adenineZ adenineN adenineZ).effectiveDegree +
    (dimAtom thymineZ thymineN thymineZ).effectiveDegree +
    (dimAtom guanineZ guanineN guanineZ).effectiveDegree = 6825 := by
  decide

-- Transcription effDeg change for start codon (ATG → AUG)
theorem start_codon_transcription_change :
    (dimAtom thymineZ thymineN thymineZ).effectiveDegree -
    (dimAtom uracilZ uracilN uracilZ).effectiveDegree = 234 := by
  decide

/-! ## Section 5: Information Content

Information per base = log₂(baseCount) = log₂(4) = 2 bits = spinDegeneracy.
Information per codon = codonLength × 2 = 6 bits = carbonZ.
-/

theorem info_per_base : Nuclear.spinDegeneracy = 2 := rfl
theorem info_per_codon :
    codonLength * Nuclear.spinDegeneracy = carbonZ := rfl

theorem genetic_code_info_bits :
    codonLength * Nuclear.spinDegeneracy = 6 := rfl

/-! ## Section 6: Summary -/

theorem genetic_code_classification :
    codonLength = 3 ∧
    codonCount = 64 ∧
    aminoAcidCount = Nuclear.nuclearMagic 2 ∧
    aminoAcidCount = 20 ∧
    stopCodonCount = 3 ∧
    codonCount = 2 ^ carbonZ ∧
    thymineZ - uracilZ = 8 ∧
    codonLength * Nuclear.spinDegeneracy = carbonZ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.GeneticCode
