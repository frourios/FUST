/-
Nucleobases and Watson-Crick Pairing from State Function Model

Five nucleobases (A, G, C, T, U) as molecular state functions.
Watson-Crick H-bond counts = D-operator kernel dimensions.
Chargaff's rule (Z-conservation) emerges as proton number balance.
Base count 4 = 2^spinDegeneracy, degree difference = H-bond difference.
-/

import FUST.Chemistry.PhosphorusAtom

namespace FUST.Chemistry.Nucleotide

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Nitrogen
open FUST.Chemistry.Phosphorus FUST.Chemistry.Dihydrogen
open FUST.Chemistry.Carbon

/-! ## Section 1: Nucleobase Parameters

Molecular (Z, N, e) from atomic composition. Neutral molecules: e = Z.
-/

structure NucleoBase where
  name : String
  Z : ℕ
  N : ℕ
  deriving Repr

def NucleoBase.e (b : NucleoBase) : ℕ := b.Z
def NucleoBase.deg (b : NucleoBase) : ℕ := b.Z + b.N + b.e

-- Adenine C₅H₅N₅
def adenine : NucleoBase := ⟨"adenine",
  5 * carbonZ + 5 * hydrogenZ + 5 * nitrogenZ,
  5 * Carbon.neutrons_C12 + 5 * protium_N + 5 * Nitrogen.neutrons_N14⟩

-- Guanine C₅H₅N₅O
def guanine : NucleoBase := ⟨"guanine",
  5 * carbonZ + 5 * hydrogenZ + 5 * nitrogenZ + oxygenZ,
  5 * Carbon.neutrons_C12 + 5 * protium_N + 5 * Nitrogen.neutrons_N14 + neutrons_O16⟩

-- Cytosine C₄H₅N₃O
def cytosine : NucleoBase := ⟨"cytosine",
  4 * carbonZ + 5 * hydrogenZ + 3 * nitrogenZ + oxygenZ,
  4 * Carbon.neutrons_C12 + 5 * protium_N + 3 * Nitrogen.neutrons_N14 + neutrons_O16⟩

-- Thymine C₅H₆N₂O₂
def thymine : NucleoBase := ⟨"thymine",
  5 * carbonZ + 6 * hydrogenZ + 2 * nitrogenZ + 2 * oxygenZ,
  5 * Carbon.neutrons_C12 + 6 * protium_N + 2 * Nitrogen.neutrons_N14 + 2 * neutrons_O16⟩

-- Uracil C₄H₄N₂O₂
def uracil : NucleoBase := ⟨"uracil",
  4 * carbonZ + 4 * hydrogenZ + 2 * nitrogenZ + 2 * oxygenZ,
  4 * Carbon.neutrons_C12 + 4 * protium_N + 2 * Nitrogen.neutrons_N14 + 2 * neutrons_O16⟩

/-! ## Section 2: Parameter Verification -/

theorem adenine_Z : adenine.Z = 70 := rfl
theorem adenine_N : adenine.N = 65 := rfl
theorem adenine_e : adenine.e = 70 := rfl
theorem adenine_deg : adenine.deg = 205 := rfl

theorem guanine_Z : guanine.Z = 78 := rfl
theorem guanine_N : guanine.N = 73 := rfl
theorem guanine_e : guanine.e = 78 := rfl
theorem guanine_deg : guanine.deg = 229 := rfl

theorem cytosine_Z : cytosine.Z = 58 := rfl
theorem cytosine_N : cytosine.N = 53 := rfl
theorem cytosine_e : cytosine.e = 58 := rfl
theorem cytosine_deg : cytosine.deg = 169 := rfl

theorem thymine_Z : thymine.Z = 66 := rfl
theorem thymine_N : thymine.N = 60 := rfl
theorem thymine_e : thymine.e = 66 := rfl
theorem thymine_deg : thymine.deg = 192 := rfl

theorem uracil_Z : uracil.Z = 58 := rfl
theorem uracil_N : uracil.N = 54 := rfl
theorem uracil_e : uracil.e = 58 := rfl
theorem uracil_deg : uracil.deg = 170 := rfl

/-! ## Section 3: Watson-Crick Hydrogen Bonds

A-T: 2 hydrogen bonds = spinDegeneracy = dim ker(D₅)
G-C: 3 hydrogen bonds = spatialDim = dim ker(D₆)
-/

abbrev AT_hbonds : ℕ := Nuclear.spinDegeneracy
abbrev GC_hbonds : ℕ := WaveEquation.spatialDim

theorem AT_hbonds_eq : AT_hbonds = 2 := rfl
theorem GC_hbonds_eq : GC_hbonds = 3 := rfl

theorem hbond_difference : GC_hbonds - AT_hbonds = 1 := rfl

/-! ## Section 4: Chargaff's Rule (Z-Conservation)

In double-stranded DNA, A pairs with T and G pairs with C.
Both pairs have the same total proton number Z.
-/

theorem chargaff_Z_conservation :
    adenine.Z + thymine.Z = guanine.Z + cytosine.Z := rfl

theorem chargaff_Z_value : adenine.Z + thymine.Z = 136 := rfl

-- Electron conservation follows from Z (neutral molecules have e = Z)
theorem chargaff_e_conservation :
    adenine.e + thymine.e = guanine.e + cytosine.e := rfl

/-! ## Section 5: Base Count from Spin Degeneracy

4 DNA bases = 2^spinDegeneracy. The binary nature of spin gives rise
to purine/pyrimidine classification (2 of each in DNA).
-/

abbrev baseCount : ℕ := 2 ^ Nuclear.spinDegeneracy

theorem baseCount_eq : baseCount = 4 := rfl

-- Purines (A, G) vs pyrimidines (C, T): 2 + 2 = 4
theorem purine_pyrimidine_split :
    Nuclear.spinDegeneracy + Nuclear.spinDegeneracy = baseCount := rfl

/-! ## Section 6: Degree Difference = H-Bond Difference

The total degree of a G-C pair exceeds that of an A-T pair by exactly 1,
which equals the H-bond count difference (3 - 2 = 1).
-/

def basePairDeg (b1 b2 : NucleoBase) : ℕ := b1.deg + b2.deg

theorem AT_pair_deg : basePairDeg adenine thymine = 397 := rfl
theorem GC_pair_deg : basePairDeg guanine cytosine = 398 := rfl

theorem degree_difference_eq_hbond_difference :
    basePairDeg guanine cytosine - basePairDeg adenine thymine =
    GC_hbonds - AT_hbonds := rfl

/-! ## Section 7: Cytosine-Uracil Relationship

C and U differ by one NH₂→O substitution.
U replaces T in RNA (T = U + CH₂ methylation).
-/

-- C and U have the same Z (both 58)
theorem cytosine_uracil_same_Z : cytosine.Z = uracil.Z := rfl

-- T and U differ by one methyl group (CH₂): Z difference = C.Z + 2·H.Z = 8
theorem thymine_uracil_Z_diff :
    thymine.Z - uracil.Z = carbonZ + 2 * hydrogenZ := rfl

-- T-U degree difference
theorem thymine_uracil_deg_diff : thymine.deg - uracil.deg = 22 := rfl

/-! ## Section 8: Summary -/

theorem nucleobase_classification :
    -- Chargaff Z-conservation
    adenine.Z + thymine.Z = guanine.Z + cytosine.Z ∧
    adenine.Z + thymine.Z = 136 ∧
    -- H-bond counts from D-operator kernels
    AT_hbonds = Nuclear.spinDegeneracy ∧
    GC_hbonds = WaveEquation.spatialDim ∧
    -- Base count from spin
    baseCount = 4 ∧
    -- Degree difference = H-bond difference
    basePairDeg guanine cytosine - basePairDeg adenine thymine = 1 ∧
    -- C and U share Z
    cytosine.Z = uracil.Z := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.Nucleotide

namespace FUST.DiscreteTag
open FUST.Chemistry.Nucleotide

def adenineZ_t : DTagged .protonNum := ⟨adenine.Z⟩
def guanineZ_t : DTagged .protonNum := ⟨guanine.Z⟩
def cytosineZ_t : DTagged .protonNum := ⟨cytosine.Z⟩
def thymineZ_t : DTagged .protonNum := ⟨thymine.Z⟩
def uracilZ_t : DTagged .protonNum := ⟨uracil.Z⟩

def adenineN_t : DTagged .neutronNum := ⟨adenine.N⟩
def guanineN_t : DTagged .neutronNum := ⟨guanine.N⟩
def cytosineN_t : DTagged .neutronNum := ⟨cytosine.N⟩
def thymineN_t : DTagged .neutronNum := ⟨thymine.N⟩
def uracilN_t : DTagged .neutronNum := ⟨uracil.N⟩

def adenineDeg_t : DTagged .degree := ⟨adenine.deg⟩
def guanineDeg_t : DTagged .degree := ⟨guanine.deg⟩
def cytosineDeg_t : DTagged .degree := ⟨cytosine.deg⟩
def thymineDeg_t : DTagged .degree := ⟨thymine.deg⟩
def uracilDeg_t : DTagged .degree := ⟨uracil.deg⟩

def transcriptionDeltaDeg_t : DTagged .deltaDeg := ⟨thymine.deg - uracil.deg⟩

theorem adenineZ_t_val : adenineZ_t.val = 70 := rfl
theorem guanineZ_t_val : guanineZ_t.val = 78 := rfl
theorem cytosineZ_t_val : cytosineZ_t.val = 58 := rfl
theorem thymineZ_t_val : thymineZ_t.val = 66 := rfl
theorem uracilZ_t_val : uracilZ_t.val = 58 := rfl

theorem adenineN_t_val : adenineN_t.val = 65 := rfl
theorem guanineN_t_val : guanineN_t.val = 73 := rfl
theorem cytosineN_t_val : cytosineN_t.val = 53 := rfl
theorem thymineN_t_val : thymineN_t.val = 60 := rfl
theorem uracilN_t_val : uracilN_t.val = 54 := rfl

theorem adenineDeg_t_val : adenineDeg_t.val = 205 := rfl
theorem guanineDeg_t_val : guanineDeg_t.val = 229 := rfl
theorem cytosineDeg_t_val : cytosineDeg_t.val = 169 := rfl
theorem thymineDeg_t_val : thymineDeg_t.val = 192 := rfl
theorem uracilDeg_t_val : uracilDeg_t.val = 170 := rfl

theorem transcriptionDeltaDeg_t_val : transcriptionDeltaDeg_t.val = 22 := rfl

-- Chargaff Z-conservation (A+T = G+C)
theorem chargaff_Z_tagged :
    adenineZ_t + thymineZ_t = guanineZ_t + cytosineZ_t := rfl

-- C and U same Z
theorem cytosine_uracil_Z_tagged : cytosineZ_t = uracilZ_t := rfl

-- T→U transcription = 22
theorem transcription_deltaDeg_tagged : transcriptionDeltaDeg_t = ⟨22⟩ := rfl

-- Degree construction consistency
theorem adenine_deg_consistency :
    mkDegree adenineZ_t adenineN_t adenineZ_t = adenineDeg_t := rfl
theorem guanine_deg_consistency :
    mkDegree guanineZ_t guanineN_t guanineZ_t = guanineDeg_t := rfl
theorem cytosine_deg_consistency :
    mkDegree cytosineZ_t cytosineN_t cytosineZ_t = cytosineDeg_t := rfl
theorem thymine_deg_consistency :
    mkDegree thymineZ_t thymineN_t thymineZ_t = thymineDeg_t := rfl
theorem uracil_deg_consistency :
    mkDegree uracilZ_t uracilN_t uracilZ_t = uracilDeg_t := rfl

-- G.Z - C.Z = 20 = aminoAcidCount
theorem bridge_purine_pyrimidine_max_diff :
    (⟨guanine.Z - cytosine.Z⟩ : DTagged .protonNum).val =
    aminoAcidCount_t.val := rfl

-- A.Z - T.Z = 4 = baseCount
theorem bridge_purine_pyrimidine_min_diff :
    (⟨adenine.Z - thymine.Z⟩ : DTagged .protonNum).val =
    baseCount_t.val := rfl

end FUST.DiscreteTag
