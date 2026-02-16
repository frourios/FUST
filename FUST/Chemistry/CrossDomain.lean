import FUST.Chemistry.CarbonMolecules
import FUST.Chemistry.Denaturation

namespace FUST.DiscreteTag

open FUST FUST.Dim
open FUST.Chemistry.Nucleotide FUST.Chemistry.ProteinFolding
open FUST.Chemistry.Denaturation FUST.Chemistry.Nitrogen

/-! ## Reduction to Three Axioms (Chemistry constants)

These reduce Chemistry-defined DTag constants to operatorKerDim / nuclearMagic / hydrogenZ. -/

theorem reduce_oxygenZ :
    oxygenZ_t.val = Nuclear.nuclearMagic 1 := rfl

theorem reduce_nitrogenZ :
    nitrogenZ_t.val = oxygenZ_t.val - hydrogenZ_t.val := rfl

theorem reduce_sulfurZ :
    sulfurZ_t.val = oxygenZ_t.val + Nuclear.shellCapacity 2 := rfl

theorem reduce_disulfideLoss :
    disulfideDegLoss_t.val = 2 * (2 * hydrogenZ_t.val) := rfl

theorem reduce_met_oxidation :
    metOxidationDeltaDeg_t.val =
    Dim.operatorKerDim 6 * Nuclear.nuclearMagic 1 := rfl

theorem reduce_carbonylation :
    carbonylationDeltaDeg_t.val = Nuclear.nuclearMagic 2 := rfl

theorem reduce_waterZ :
    waterZ_t.val = 2 * hydrogenZ_t.val + Nuclear.nuclearMagic 1 := rfl

theorem reduce_phosphorusZ :
    phosphorusZ_t.val =
    Nuclear.nuclearMagic 1 + Nuclear.shellCapacity 2 - hydrogenZ_t.val := rfl

/-! ## Cross-Domain Theorems

These require imports from multiple Chemistry branches
that individual files cannot access without circular deps. -/

-- transition A↔G deg diff = Met oxidation Δdeg
theorem bridge_transition_eq_met_oxidation :
    (⟨guanine.deg - adenine.deg⟩ : DTagged .deltaDeg).val =
    metOxidationDeltaDeg_t.val := rfl

-- dehydrogenation per step = disulfide loss
theorem bridge_dehydrogenation_eq_disulfide :
    dehydrogenationDeltaDeg_t.val = disulfideDegLoss_t.val := rfl

-- Isoelectronic: CH₄ = H₂O = NH₃ in Z
theorem isoelectronic_10 :
    waterZ_t = methaneZ_t ∧ waterZ_t = ammoniaZ_t := ⟨rfl, rfl⟩

end FUST.DiscreteTag
