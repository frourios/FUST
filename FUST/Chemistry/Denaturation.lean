/-
Protein Denaturation from FDim Structure

Type 1 (non-covalent): ΔeffDeg = 0, thermodynamically reversible.
Type 2 (disulfide change): ΔZ = ±2 per bond, conditionally reversible.
Type 3 (oxidation/carbonylation): ΔZ ≠ 0, requires enzymatic repair.
Met oxidation: ΔZ = oxygenZ = 8.
Carbonylation: ΔZ = carbonZ = 6.
-/

import FUST.Chemistry.ProteinFolding

namespace FUST.Chemistry.Denaturation

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Nucleotide
open FUST.Chemistry.GeneticCode
open FUST.Chemistry.AminoAcid FUST.Chemistry.Translation
open FUST.Chemistry.Oxygen FUST.Chemistry.Carbon
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Nitrogen
open FUST.Chemistry.ProteinFolding

set_option maxRecDepth 8192

/-! ## Section 1: Disulfide Bond Energetics

Each disulfide bond formation removes H₂ (2 hydrogen atoms).
ΔZ = -2, ΔN = 0.
-/

theorem disulfide_Z_loss : 2 * hydrogenZ = 2 := rfl

/-! ## Section 2: Met Oxidation

Met → Met-sulfoxide: gain one oxygen atom.
Met: C₅H₁₁NO₂S (Z=80, N=69).
Met-SO: C₅H₁₁NO₃S (Z=88, N=77).
ΔZ = oxygenZ = 8, ΔN = oxygenZ = 8.
-/

abbrev metSulfoxideZ : ℕ := metZ + oxygenZ
abbrev metSulfoxideN : ℕ := metN + Oxygen.neutrons_O16

theorem metSO_Z : metSulfoxideZ = 88 := rfl
theorem metSO_N : metSulfoxideN = 77 := rfl

-- Met oxidation ΔZ = oxygenZ = 8
theorem met_oxidation_deltaZ :
    metSulfoxideZ - metZ = oxygenZ := rfl

-- Met-sulfoxide effectiveDegree
theorem metSO_effDeg :
    (dimAtom metSulfoxideZ metSulfoxideN metSulfoxideZ
      ).effectiveDegree = 2740 := by decide

-- Met oxidation ΔeffDeg = 264
theorem met_oxidation_deltaEffDeg :
    (dimAtom metSulfoxideZ metSulfoxideN metSulfoxideZ
      ).effectiveDegree -
    (dimAtom metZ metN metZ).effectiveDegree = 264 := by
  decide

-- Met oxidation = same ΔZ as nucleobase transitions (A↔G, C↔T)
theorem met_oxidation_Z_eq_transition :
    metSulfoxideZ - metZ = guanineZ - adenineZ := rfl

/-! ## Section 3: Protein Carbonylation

Side chain oxidation: lose 2H, gain O.
ΔZ = oxygenZ - 2·hydrogenZ = carbonZ = 6.
ΔN = oxygenZ = 8.
-/

abbrev carbonylationDeltaZ : ℕ := oxygenZ - 2 * hydrogenZ

-- ΔZ = carbonZ = 6
theorem carbonylation_deltaZ :
    carbonylationDeltaZ = carbonZ := rfl

abbrev carbonylationDeltaN : ℕ := Oxygen.neutrons_O16

/-! ## Section 4: Deamidation

Asn → Asp: spontaneous aging modification.
ΔZ = 0 (both have Z=70), ΔN = 1.
-/

theorem deamidation_preserves_Z : asnZ = aspZ := rfl

theorem deamidation_deltaN :
    aspN - asnN = 1 := rfl

-- Same for Gln → Glu
theorem gln_glu_deamidation_Z : glnZ = gluZ := rfl

theorem gln_glu_deamidation_deltaN :
    gluN - glnN = 1 := rfl

/-! ## Section 5: Ovalbumin (Egg White)

385 residues, 6 Cys: 1 native disulfide + 4 free SH.
Cooking forms up to 2 additional disulfides.
-/

abbrev ovalbuminCysCount : ℕ := carbonZ   -- 6 Cys = carbonZ
abbrev ovalbuminNativeDisulfide : ℕ := 1
abbrev ovalbuminFreeSH : ℕ := 4
abbrev ovalbuminResidueCount : ℕ := 385

theorem ovalbumin_cys_partition :
    2 * ovalbuminNativeDisulfide + ovalbuminFreeSH =
    ovalbuminCysCount := rfl

abbrev ovalbuminMaxNewDisulfide : ℕ := ovalbuminFreeSH / 2

theorem ovalbumin_max_new_SS :
    ovalbuminMaxNewDisulfide = 2 := rfl

theorem ovalbumin_cooked_max_SS :
    ovalbuminNativeDisulfide + ovalbuminMaxNewDisulfide = 3 := rfl

/-! ## Section 6: Denaturation Classification Hierarchy

Type 1 → Type 2 → Type 3 in increasing severity.
Only Type 1 is spontaneously reversible.
-/

-- Type 1: ΔZ = 0 (non-covalent)
-- Type 2: ΔZ = ±2k (disulfide changes)
-- Type 3: ΔZ ≥ carbonZ = 6 (chemical modification)

theorem type2_Z_loss_unit : 2 * hydrogenZ = 2 := rfl

theorem type3_carbonylation_deltaZ :
    carbonylationDeltaZ = carbonZ := rfl

/-! ## Section 7: Summary -/

theorem denaturation_classification :
    metSulfoxideZ - metZ = oxygenZ ∧
    carbonylationDeltaZ = carbonZ ∧
    asnZ = aspZ ∧
    aspN - asnN = 1 ∧
    2 * hydrogenZ = 2 ∧
    ovalbuminCysCount = carbonZ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.Denaturation
