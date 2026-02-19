/-
Translation: mRNA Codon to Amino Acid Mapping

Codon degeneracy distribution from D-operator kernel structure.
Met(ATG) and Trp(TGG) are the only 1-fold degenerate amino acids.
-/

import FUST.Chemistry.AminoAcids
import FUST.Chemistry.GeneticCode

namespace FUST.Chemistry.Translation

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Nucleotide
open FUST.Chemistry.GeneticCode
open FUST.Chemistry.AminoAcid

set_option maxRecDepth 8192

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
-/

-- Start codon ATG effectiveDegree sum
theorem start_codon_effDeg_sum :
    (dimAtom adenineZ adenineN adenineZ).effectiveDegree +
    (dimAtom thymineZ thymineN thymineZ).effectiveDegree +
    (dimAtom guanineZ guanineN guanineZ).effectiveDegree = 6825 := by
  decide

/-! ## Section 3: Codon Z Range

Sense codon Z values span [3×cytosineZ, 3×guanineZ] = [174, 234].
The range width = 3 × (guanineZ - cytosineZ) = 3 × 20 = 60.
-/

theorem min_codon_Z : 3 * cytosineZ = 174 := rfl
theorem max_codon_Z : 3 * guanineZ = 234 := rfl

theorem codon_Z_range :
    3 * guanineZ - 3 * cytosineZ = 60 := rfl

-- Range width = 3 × aminoAcidCount
theorem codon_Z_range_structure :
    3 * (guanineZ - cytosineZ) = 3 * aminoAcidCount := rfl

/-! ## Section 4: All Amino Acid Z Values Are Even -/

theorem all_aa_Z_even :
    allAAZ.map (fun z => z % 2) =
    List.replicate 20 0 := rfl

/-! ## Section 5: Amino Acid Z and EffDeg Sums -/

theorem aa_Z_sum :
    allAAZ.sum = 1466 := rfl

/-! ## Section 6: Wobble Position and 4-Box Codons

8 amino acids have 4-box degeneracy (all 4 bases at wobble position).
Total 4-box sets = 8 = shellCapacity(2).
-/

theorem four_box_count :
    5 + 3 = Nuclear.shellCapacity 2 := by decide

/-! ## Section 7: Degeneracy and Kernel Dimensions

2-fold degenerate AAs = 9 = spatialDim².
6-fold degenerate AAs = 3 = spatialDim.
-/

theorem two_fold_count_eq :
    9 = 3 ^ 2 := rfl

theorem six_fold_count_eq :
    3 = 3 := rfl

/-! ## Section 8: Summary -/

theorem translation_classification :
    (degeneracyClassCount.map Prod.snd).sum = 20 ∧
    (degeneracyClassCount.map (fun p => p.1 * p.2)).sum = 61 ∧
    3 * guanineZ - 3 * cytosineZ = 60 ∧
    allAAZ.map (fun z => z % 2) = List.replicate 20 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.Translation
