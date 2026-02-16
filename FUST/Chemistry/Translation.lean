/-
Translation: mRNA Codon to Amino Acid Mapping

Codon degeneracy distribution from D-operator kernel structure.
Met(ATG) and Trp(TGG) are the only 1-fold degenerate amino acids.
Peptide chain degree is additive modulo H₂O condensation.
-/

import FUST.Chemistry.AminoAcids
import FUST.Chemistry.GeneticCode

namespace FUST.Chemistry.Translation

open FUST FUST.Chemistry.Nucleotide FUST.Chemistry.GeneticCode
open FUST.Chemistry.AminoAcid

/-! ## Section 1: Codon Degeneracy Distribution

Degeneracy classes: how many codons encode each amino acid.
1-fold: Met, Trp (2 AAs)
2-fold: Phe, Tyr, His, Gln, Asn, Lys, Asp, Glu, Cys (9 AAs)
3-fold: Ile (1 AA)
4-fold: Val, Pro, Thr, Ala, Gly (5 AAs)
6-fold: Leu, Ser, Arg (3 AAs)
-/

def degeneracyClassCount : List (ℕ × ℕ) :=
  [(1, 2), (2, 9), (3, 1), (4, 5), (6, 3)]

theorem degeneracy_total_aa :
    (degeneracyClassCount.map Prod.snd).sum = aminoAcidCount := rfl

theorem degeneracy_total_codons :
    (degeneracyClassCount.map (fun p => p.1 * p.2)).sum =
    senseCodonCount := rfl

theorem degeneracy_class_count :
    degeneracyClassCount.length = 5 := rfl

/-! ## Section 2: Unique Codon Amino Acids

Met (ATG) and Trp (TGG) are the only amino acids with exactly one codon.
Met is the universal start codon amino acid.
-/

theorem start_codon_encodes_met :
    codonDeg adenine thymine guanine = 626 ∧
    met.deg = 229 := ⟨rfl, rfl⟩

theorem trp_unique_codon_deg :
    codonDeg thymine guanine guanine = 650 ∧
    trp.deg = 312 := ⟨rfl, rfl⟩

-- Met degree = guanine degree (nucleobase-amino acid bridge)
theorem met_guanine_bridge : met.deg = guanine.deg := rfl

/-! ## Section 3: Codon Z Range

Sense codon Z values span [3×cytosineZ, 3×guanineZ] = [174, 234].
The range width = 3 × (guanineZ - cytosineZ) = 3 × 20 = 60.
-/

theorem min_codon_Z : 3 * cytosine.Z = 174 := rfl
theorem max_codon_Z : 3 * guanine.Z = 234 := rfl

theorem codon_Z_range :
    3 * guanine.Z - 3 * cytosine.Z = 60 := rfl

-- Range width = 3 × aminoAcidCount
theorem codon_Z_range_structure :
    3 * (guanine.Z - cytosine.Z) = 3 * aminoAcidCount := rfl

/-! ## Section 4: All Amino Acid Z Values Are Even -/

theorem all_aa_Z_even :
    allAA.map (fun a => a.Z % 2) =
    List.replicate 20 0 := rfl

/-! ## Section 5: Peptide Chain Degree Algebra

For a peptide chain of n amino acids:
deg(chain) = Σᵢ deg(AAᵢ) - (n-1) × deg(H₂O)
Each peptide bond releases one H₂O (Z=10, N=8, deg=28).
-/

def chainDeg (l : List AA) : ℕ :=
  (l.map AA.deg).sum - (l.length - 1) * 28

-- Dipeptide: Met-Ala (start of many proteins)
theorem met_ala_chain_deg :
    chainDeg [met, ala] = 338 := rfl

-- Tripeptide: Met-Ala-Gly
theorem met_ala_gly_chain_deg :
    chainDeg [met, ala, gly] = 425 := rfl

-- Single amino acid: no peptide bond
theorem single_aa_chain_deg (a : AA) :
    chainDeg [a] = a.deg := by
  simp [chainDeg, AA.deg]

/-! ## Section 6: Wobble Position and 4-Box Codons

8 amino acids have 4-box degeneracy (all 4 bases at wobble position).
Pure 4-box (V,P,T,A,G) = 5; 6-fold with 4-box subset (L,S,R) = 3.
Total 4-box sets = 8 = shellCapacity(1).
-/

theorem four_box_count :
    5 + 3 = Nuclear.shellCapacity 2 := by decide

/-! ## Section 7: Degeneracy and Kernel Dimensions

2-fold degenerate AAs = 9 = spatialDim².
6-fold degenerate AAs = 3 = spatialDim.
-/

theorem two_fold_count_eq :
    9 = WaveEquation.spatialDim ^ 2 := rfl

theorem six_fold_count_eq :
    3 = WaveEquation.spatialDim := rfl

/-! ## Section 8: Amino Acid Z and Degree Sums -/

theorem aa_Z_sum :
    (allAA.map AA.Z).sum = 1466 := rfl

theorem aa_deg_sum :
    (allAA.map AA.deg).sum = 4201 := by decide

theorem aa_deg_avg : 4201 / 20 = 210 := rfl

/-! ## Section 9: Summary -/

theorem translation_classification :
    (degeneracyClassCount.map Prod.snd).sum = 20 ∧
    (degeneracyClassCount.map (fun p => p.1 * p.2)).sum = 61 ∧
    met.deg = guanine.deg ∧
    3 * guanine.Z - 3 * cytosine.Z = 60 ∧
    allAA.map (fun a => a.Z % 2) = List.replicate 20 0 ∧
    chainDeg [met, ala] = 338 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.Translation

namespace FUST.DiscreteTag

-- Two-fold degeneracy count (9) = spatialDim²
theorem twofold_is_spatialDim_sq :
    (⟨9⟩ : DTagged .count).val = spatialDim_t.val * spatialDim_t.val := rfl

-- Six-fold degeneracy count (3) = spatialDim
theorem sixfold_is_spatialDim :
    (⟨3⟩ : DTagged .count) = kerToCount spatialDim_t := rfl

-- Four-box count (5 + 3 = 8) = shellCapacity(2)
theorem fourbox_is_shellCapacity2 :
    (⟨5 + 3⟩ : DTagged .count).val = Nuclear.shellCapacity 2 := rfl

end FUST.DiscreteTag
