/-
Protein Folding from D-operator Kernel Structure

α-helix H-bond span = baseCount = 4.
3₁₀-helix span = spatialDim = 3.
Backbone dihedrals per residue = spinDegeneracy = 2.
Peptide plane atoms = carbonZ = 6.
Protein degree is a topological invariant of primary sequence.
-/

import FUST.Chemistry.Mutation

namespace FUST.Chemistry.ProteinFolding

open FUST FUST.Chemistry.Nucleotide FUST.Chemistry.GeneticCode
open FUST.Chemistry.AminoAcid FUST.Chemistry.Translation
open FUST.Chemistry.Oxygen FUST.Chemistry.Carbon
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Nitrogen

/-! ## Section 1: Backbone Structure

Peptide bond plane contains 6 = carbonZ atoms: Cα₁, C, O, N, H, Cα₂.
Each residue contributes 2 = spinDegeneracy backbone dihedral angles (φ, ψ).
-/

abbrev peptidePlaneAtoms : ℕ := carbonZ

theorem peptidePlaneAtoms_eq : peptidePlaneAtoms = 6 := rfl

abbrev backboneDihedrals : ℕ := Nuclear.spinDegeneracy

theorem backboneDihedrals_eq : backboneDihedrals = 2 := rfl

/-! ## Section 2: Secondary Structure

Helix types defined by H-bond span (residue i to residue i+n).
3₁₀-helix: span 3 = spatialDim.
α-helix: span 4 = baseCount (most common).
π-helix: span 5 = baseCount + 1.
β-sheet H-bond repeat every 2 = spinDegeneracy residues.
-/

abbrev helix310Span : ℕ := WaveEquation.spatialDim
abbrev alphaHelixSpan : ℕ := baseCount
abbrev piHelixSpan : ℕ := baseCount + 1
abbrev betaSheetRepeat : ℕ := Nuclear.spinDegeneracy

theorem helix310Span_eq : helix310Span = 3 := rfl
theorem alphaHelixSpan_eq : alphaHelixSpan = 4 := rfl
theorem piHelixSpan_eq : piHelixSpan = 5 := rfl
theorem betaSheetRepeat_eq : betaSheetRepeat = 2 := rfl

-- Helix spans form consecutive integers 3, 4, 5
theorem helix_span_consecutive :
    alphaHelixSpan = helix310Span + 1 ∧
    piHelixSpan = alphaHelixSpan + 1 := ⟨rfl, rfl⟩

-- α-helix is the most common: span = 2^spinDeg = baseCount
theorem alpha_helix_from_spin :
    alphaHelixSpan = 2 ^ Nuclear.spinDegeneracy := rfl

/-! ## Section 3: Hydrogen Bond in Folding

Peptide H-bond: N-H···O=C.
H-bond donor (N-H) Z = nitrogenZ + hydrogenZ = 8 = oxygenZ.
H-bond acceptor (C=O) Z = carbonZ + oxygenZ = 14.
-/

abbrev hbondDonorZ : ℕ := nitrogenZ + hydrogenZ
abbrev hbondAcceptorZ : ℕ := carbonZ + oxygenZ

theorem hbond_donor_eq_oxygenZ :
    hbondDonorZ = oxygenZ := rfl

theorem hbondAcceptorZ_eq : hbondAcceptorZ = 14 := rfl

-- H-bond pair total Z
theorem hbond_pair_Z :
    hbondDonorZ + hbondAcceptorZ = 22 := rfl

-- 22 = thymine.deg - uracil.deg (transcription degree change)
theorem hbond_pair_Z_eq_transcription :
    hbondDonorZ + hbondAcceptorZ =
    thymine.deg - uracil.deg := rfl

/-! ## Section 4: Amino Acid Chemical Classification

Aromatic: F, W, Y = 3 = spatialDim.
Charged: K, R (+), D, E (-) = 4 = baseCount.
Positive = Negative = 2 = spinDegeneracy (charge balance).
Sulfur-containing: M, C = 2 = spinDegeneracy.
-/

def aromaticAA : List AA := [phe, trp, tyr]
def chargedAA : List AA := [lys, arg, asp, glu]
def positiveAA : List AA := [lys, arg]
def negativeAA : List AA := [asp, glu]
def sulfurAA : List AA := [met, cys]

theorem aromatic_count :
    aromaticAA.length = WaveEquation.spatialDim := rfl

theorem charged_count :
    chargedAA.length = baseCount := rfl

theorem positive_count :
    positiveAA.length = Nuclear.spinDegeneracy := rfl

theorem negative_count :
    negativeAA.length = Nuclear.spinDegeneracy := rfl

-- Charge balance: equal number of positive and negative
theorem charge_balance :
    positiveAA.length = negativeAA.length := rfl

theorem sulfur_count :
    sulfurAA.length = Nuclear.spinDegeneracy := rfl

/-! ## Section 5: Side Chain Degree

Side chain = free AA minus backbone (Gly) plus one hydrogen.
sideChainZ(AA) = AA.Z - gly.Z + hydrogenZ.
Gly has the minimal side chain (just H, sideDeg = 2).
-/

def sideChainZ (a : AA) : ℕ := a.Z - gly.Z + hydrogenZ
def sideChainN (a : AA) : ℕ := a.N - gly.N
def sideChainDeg (a : AA) : ℕ :=
    2 * sideChainZ a + sideChainN a

-- Gly side chain = H
theorem gly_sideChainZ : sideChainZ gly = 1 := rfl
theorem gly_sideChainDeg : sideChainDeg gly = 2 := rfl

-- Trp has the largest side chain
theorem trp_sideChainZ : sideChainZ trp = 69 := rfl
theorem trp_sideChainDeg : sideChainDeg trp = 199 := rfl

-- Gly is the minimal-degree amino acid
theorem gly_minimal_deg :
    ∀ a ∈ allAA, gly.deg ≤ a.deg := by decide

-- Trp is the maximal-degree amino acid
theorem trp_maximal_deg :
    ∀ a ∈ allAA, a.deg ≤ trp.deg := by decide

/-! ## Section 6: Protein Degree Invariance

Protein degree depends only on primary sequence (amino acid order).
Folding involves non-covalent interactions which do not change deg.
deg(protein) = Σᵢ deg(AAᵢ) - (n-1) × deg(H₂O).
-/

-- Protein degree from primary sequence is well-defined
-- (chainDeg from Translation.lean)

-- Adding a disulfide bond (removing H₂) decreases deg by 4
def disulfideDegLoss : ℕ := 2 * (2 * hydrogenZ)

theorem disulfide_deg_loss_eq :
    disulfideDegLoss = 4 := rfl

-- Protein with k disulfide bonds
def proteinDeg (chain : List AA) (nDisulfide : ℕ) : ℕ :=
    chainDeg chain - nDisulfide * disulfideDegLoss

/-! ## Section 7: Salt Bridges

Electrostatic pairs between charged residues stabilize folds.
K-D, K-E, R-D, R-E are the 4 = baseCount possible salt bridges.
-/

def saltBridgePairs : List (AA × AA) :=
    [(lys, asp), (lys, glu), (arg, asp), (arg, glu)]

theorem salt_bridge_count :
    saltBridgePairs.length = baseCount := rfl

-- Salt bridge pair degrees
theorem salt_bridge_KD_deg :
    lys.deg + asp.deg = 429 := rfl

theorem salt_bridge_RE_deg :
    arg.deg + glu.deg = 493 := rfl

-- Largest salt bridge: R+E
-- Smallest salt bridge: K+D
-- Range = 493 - 429 = 64 = codonCount
theorem salt_bridge_deg_range :
    (arg.deg + glu.deg) - (lys.deg + asp.deg) =
    codonCount := rfl

/-! ## Section 8: Insulin as Verification

Insulin A chain: 21 residues, B chain: 30 residues.
3 disulfide bonds (A7-B7, A20-B19, A6-A11).
Total Cys = 6 = 2 × spatialDim = carbonZ.
-/

-- Insulin A chain sequence
def insulinA : List AA :=
    [gly,ile,val,glu,gln,cys,cys,thr,ser,ile,
     cys,ser,leu,tyr,gln,leu,glu,asn,tyr,cys,asn]

-- Insulin B chain sequence
def insulinB : List AA :=
    [phe,val,asn,gln,his,leu,cys,gly,ser,his,
     leu,val,glu,ala,leu,tyr,leu,val,cys,gly,
     glu,arg,gly,phe,phe,tyr,thr,pro,lys,thr]

theorem insulinA_length : insulinA.length = 21 := rfl
theorem insulinB_length : insulinB.length = 30 := rfl

-- Cysteine count
theorem insulinA_cys_count :
    (insulinA.filter (fun a => a.Z = cys.Z ∧ a.N = cys.N)).length = 4 := by
  decide

theorem insulinB_cys_count :
    (insulinB.filter (fun a => a.Z = cys.Z ∧ a.N = cys.N)).length = 2 := by
  decide

-- Total Cys = 6 = carbonZ = 2 × spatialDim
theorem insulin_total_cys :
    4 + 2 = carbonZ := rfl

theorem insulin_cys_eq_twice_disulfide :
    4 + 2 = 2 * WaveEquation.spatialDim := rfl

-- Insulin has 3 disulfide bonds = spatialDim
abbrev insulinDisulfideCount : ℕ := WaveEquation.spatialDim
theorem insulin_disulfide_eq : insulinDisulfideCount = 3 := rfl

-- Insulin A chain degree
theorem insulinA_deg :
    chainDeg insulinA = 3649 := by decide

-- Insulin B chain degree
theorem insulinB_deg :
    chainDeg insulinB = 5256 := by decide

/-! ## Section 9: Summary -/

theorem protein_folding_classification :
    -- Peptide plane = carbonZ atoms
    peptidePlaneAtoms = carbonZ ∧
    -- Backbone dihedrals = spinDegeneracy
    backboneDihedrals = Nuclear.spinDegeneracy ∧
    -- α-helix span = baseCount
    alphaHelixSpan = baseCount ∧
    -- 3₁₀-helix span = spatialDim
    helix310Span = WaveEquation.spatialDim ∧
    -- H-bond donor Z = oxygenZ
    hbondDonorZ = oxygenZ ∧
    -- Aromatic count = spatialDim
    aromaticAA.length = WaveEquation.spatialDim ∧
    -- Charged count = baseCount
    chargedAA.length = baseCount ∧
    -- Salt bridge range = codonCount
    (arg.deg + glu.deg) - (lys.deg + asp.deg) = codonCount ∧
    -- Insulin disulfide = spatialDim
    insulinDisulfideCount = WaveEquation.spatialDim :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.ProteinFolding

namespace FUST.DiscreteTag
open FUST.Chemistry.ProteinFolding

def disulfideDegLoss_t : DTagged .deltaDeg := ⟨disulfideDegLoss⟩

theorem disulfide_deltaDeg : disulfideDegLoss_t = ⟨4⟩ := rfl

-- α-helix span = baseCount
theorem alphaHelixSpan_is_baseCount :
    (⟨alphaHelixSpan⟩ : DTagged .count) = baseCount_t := rfl

-- 3₁₀-helix span = spatialDim
theorem helix310Span_is_spatialDim :
    (⟨helix310Span⟩ : DTagged .count) = stopCodonCount_t := rfl

-- peptide plane atoms = carbonZ
theorem peptidePlane_is_carbonZ :
    (⟨peptidePlaneAtoms⟩ : DTagged .count).val = carbonZ_t.val := rfl

-- backbone dihedrals = spinDeg
theorem backboneDihedrals_is_spinDeg :
    (⟨backboneDihedrals⟩ : DTagged .count).val = spinDeg_t.val := rfl

-- β-sheet repeat = spinDeg
theorem betaSheetRepeat_is_spinDeg :
    (⟨betaSheetRepeat⟩ : DTagged .count).val = spinDeg_t.val := rfl

-- aromatic AA count = spatialDim
theorem aromatic_count_is_spatialDim :
    (⟨aromaticAA.length⟩ : DTagged .count) = kerToCount spatialDim_t := rfl

-- charged AA count = baseCount
theorem charged_count_is_baseCount :
    (⟨chargedAA.length⟩ : DTagged .count) = baseCount_t := rfl

-- positive AA count = spinDeg
theorem positive_count_is_spinDeg :
    (⟨positiveAA.length⟩ : DTagged .count) = kerToCount spinDeg_t := rfl

-- negative AA count = spinDeg
theorem negative_count_is_spinDeg :
    (⟨negativeAA.length⟩ : DTagged .count) = kerToCount spinDeg_t := rfl

-- sulfur AA count = spinDeg
theorem sulfur_count_is_spinDeg :
    (⟨sulfurAA.length⟩ : DTagged .count) = kerToCount spinDeg_t := rfl

-- salt bridge pair count = baseCount
theorem saltBridge_count_is_baseCount :
    (⟨saltBridgePairs.length⟩ : DTagged .count) = baseCount_t := rfl

-- H-bond donor Z = oxygenZ (N + H = 7 + 1 = 8)
theorem hbond_donor_is_oxygenZ :
    (⟨hbondDonorZ⟩ : DTagged .protonNum) = oxygenZ_t := rfl

-- H-bond acceptor Z = C + O = 14
theorem hbond_acceptor_is_COZ :
    (⟨hbondAcceptorZ⟩ : DTagged .protonNum) = carbonZ_t + oxygenZ_t := rfl

-- H-bond pair Z = C + 2O = 22
theorem hbond_pair_is_CO2Z :
    (⟨hbondDonorZ + hbondAcceptorZ⟩ : DTagged .protonNum) =
    carbonZ_t + scaleZ 2 oxygenZ_t := rfl

-- insulin total Cys (4 + 2) = carbonZ
theorem insulin_cys_is_carbonZ :
    (⟨4 + 2⟩ : DTagged .count).val = carbonZ_t.val := rfl

-- insulin disulfide = spatialDim
theorem insulin_disulfide_is_spatialDim :
    (⟨insulinDisulfideCount⟩ : DTagged .count).val = spatialDim_t.val := rfl

open FUST.Chemistry.AminoAcid in
-- salt bridge degree range = codonCount
theorem bridge_salt_bridge_range :
    (⟨(arg.deg + glu.deg) - (lys.deg + asp.deg)⟩ : DTagged .deltaDeg).val =
    codonCount_t.val := rfl

open FUST.Chemistry.Nucleotide in
-- hbond pair Z = T-U transcription deg diff
theorem bridge_hbond_pair_eq_transcription :
    (⟨hbondDonorZ + hbondAcceptorZ⟩ : DTagged .protonNum).val =
    transcriptionDeltaDeg_t.val := rfl

end FUST.DiscreteTag
