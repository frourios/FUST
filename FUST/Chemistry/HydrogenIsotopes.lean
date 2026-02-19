/-
Hydrogen Isotopes: FDim Structure with Mass Defect

Each bound state has FDim = product of constituent dims / binding defect dim.
The binding defect dimTimeD2 per bond accounts for mass defect energy,
preventing zero-cost binding/unbinding.

  H⁺ = dimProton                              (bare proton, no binding)
  H  = dimProton × dimElectron / dimTimeD2     (EM binding, 1 bond)
  D⁺ = dimProton × dimNeutron / dimTimeD2      (nuclear binding, 1 bond)
  D  = D⁺ × dimElectron / dimTimeD2            (nuclear + EM, 2 bonds)
  T⁺ = D⁺ × dimNeutron / dimTimeD2             (nuclear, 2 bonds)
  T  = T⁺ × dimElectron / dimTimeD2            (nuclear + EM, 3 bonds)
  H⁻ = H × dimElectron / dimTimeD2             (EM, 2 bonds)
-/

import FUST.Physics.MassRatios

namespace FUST.Chemistry

open FUST.Dim

/-! ## Section 1: Binding Defect

Each bound state pays a dimensional cost dimTimeD2 per binding bond.
This prevents the paradox of zero-cost binding/unbinding:
without the defect, dimH = dimProton × dimElectron would mean
H ↔ p + e is dimensionally free. -/

abbrev dimBindingDefect : FDim := dimTimeD2

/-! ## Section 2: Hydrogen Species FDim

H⁺ = bare proton (no binding).
H = proton bound to electron (1 EM bond).
D⁺ = proton bound to neutron (1 nuclear bond).
Heavier isotopes accumulate one defect per bond. -/

def dimHydrogenIon : FDim := dimProton

def dimHydrogenAtom : FDim := dimProton * dimElectron * dimBindingDefect⁻¹

def dimHydrideAnion : FDim := dimHydrogenAtom * dimElectron * dimBindingDefect⁻¹

def dimDeuteronIon : FDim := dimProton * dimNeutron * dimBindingDefect⁻¹

def dimDeuteriumAtom : FDim := dimDeuteronIon * dimElectron * dimBindingDefect⁻¹

def dimTritonIon : FDim := dimDeuteronIon * dimNeutron * dimBindingDefect⁻¹

def dimTritiumAtom : FDim := dimTritonIon * dimElectron * dimBindingDefect⁻¹

/-! ## Section 3: Explicit FDim Values -/

theorem dimHydrogenIon_eq : dimHydrogenIon = ⟨9, -13⟩ := by decide
theorem dimHydrogenAtom_eq : dimHydrogenAtom = ⟨3, -11⟩ := by decide
theorem dimHydrideAnion_eq : dimHydrideAnion = ⟨-3, -9⟩ := by decide
theorem dimDeuteronIon_eq : dimDeuteronIon = ⟨16, -24⟩ := by decide
theorem dimDeuteriumAtom_eq : dimDeuteriumAtom = ⟨10, -22⟩ := by decide
theorem dimTritonIon_eq : dimTritonIon = ⟨23, -35⟩ := by decide
theorem dimTritiumAtom_eq : dimTritiumAtom = ⟨17, -33⟩ := by decide

/-! ## Section 4: Sector Decomposition

All species decompose as deriveFDim(6)^k × dimTimeD2^n. -/

theorem hydrogenIon_sector :
    dimHydrogenIon = deriveFDim 6 * dimTimeD2 ^ (14 : ℤ) := by decide
theorem hydrogenAtom_sector :
    dimHydrogenAtom = (deriveFDim 6) ^ (2 : ℤ) * dimTimeD2 ^ (13 : ℤ) := by decide
theorem hydrideAnion_sector :
    dimHydrideAnion = (deriveFDim 6) ^ (3 : ℤ) * dimTimeD2 ^ (12 : ℤ) := by decide
theorem deuteronIon_sector :
    dimDeuteronIon = (deriveFDim 6) ^ (2 : ℤ) * dimTimeD2 ^ (26 : ℤ) := by decide
theorem deuteriumAtom_sector :
    dimDeuteriumAtom = (deriveFDim 6) ^ (3 : ℤ) * dimTimeD2 ^ (25 : ℤ) := by decide
theorem tritonIon_sector :
    dimTritonIon = (deriveFDim 6) ^ (3 : ℤ) * dimTimeD2 ^ (38 : ℤ) := by decide
theorem tritiumAtom_sector :
    dimTritiumAtom = (deriveFDim 6) ^ (4 : ℤ) * dimTimeD2 ^ (37 : ℤ) := by decide

/-! ## Section 5: Effective Degree (Spectral Index) -/

theorem hydrogenIon_effectiveDegree :
    dimHydrogenIon.effectiveDegree = 17 := by decide
theorem hydrogenAtom_effectiveDegree :
    dimHydrogenAtom.effectiveDegree = 19 := by decide
theorem hydrideAnion_effectiveDegree :
    dimHydrideAnion.effectiveDegree = 21 := by decide
theorem deuteronIon_effectiveDegree :
    dimDeuteronIon.effectiveDegree = 32 := by decide
theorem deuteriumAtom_effectiveDegree :
    dimDeuteriumAtom.effectiveDegree = 34 := by decide
theorem tritonIon_effectiveDegree :
    dimTritonIon.effectiveDegree = 47 := by decide
theorem tritiumAtom_effectiveDegree :
    dimTritiumAtom.effectiveDegree = 49 := by decide

/-! ## Section 6: Distinctness

All hydrogen species have pairwise distinct FDim,
and none coincides with an elementary particle. -/

theorem hydrogenSpecies_all_distinct :
    dimHydrogenIon ≠ dimHydrogenAtom ∧
    dimHydrogenIon ≠ dimHydrideAnion ∧
    dimHydrogenIon ≠ dimDeuteronIon ∧
    dimHydrogenIon ≠ dimDeuteriumAtom ∧
    dimHydrogenIon ≠ dimTritonIon ∧
    dimHydrogenIon ≠ dimTritiumAtom ∧
    dimHydrogenAtom ≠ dimHydrideAnion ∧
    dimHydrogenAtom ≠ dimDeuteronIon ∧
    dimHydrogenAtom ≠ dimDeuteriumAtom ∧
    dimHydrogenAtom ≠ dimTritonIon ∧
    dimHydrogenAtom ≠ dimTritiumAtom ∧
    dimHydrideAnion ≠ dimDeuteronIon ∧
    dimHydrideAnion ≠ dimDeuteriumAtom ∧
    dimHydrideAnion ≠ dimTritonIon ∧
    dimHydrideAnion ≠ dimTritiumAtom ∧
    dimDeuteronIon ≠ dimDeuteriumAtom ∧
    dimDeuteronIon ≠ dimTritonIon ∧
    dimDeuteronIon ≠ dimTritiumAtom ∧
    dimDeuteriumAtom ≠ dimTritonIon ∧
    dimDeuteriumAtom ≠ dimTritiumAtom ∧
    dimTritonIon ≠ dimTritiumAtom := by decide

theorem hydrogenDims_ne_elementary :
    dimHydrogenAtom ≠ dimElectron ∧
    dimHydrogenAtom ≠ dimMuon ∧
    dimHydrogenAtom ≠ dimTau ∧
    dimHydrogenAtom ≠ dimProton ∧
    dimHydrogenAtom ≠ dimNeutron ∧
    dimHydrogenAtom ≠ dimWBoson ∧
    dimDeuteronIon ≠ dimElectron ∧
    dimDeuteronIon ≠ dimProton ∧
    dimDeuteronIon ≠ dimNeutron ∧
    dimDeuteriumAtom ≠ dimElectron ∧
    dimDeuteriumAtom ≠ dimProton ∧
    dimDeuteriumAtom ≠ dimNeutron := by decide

/-! ## Section 7: Mass Defect Monotonicity

Each binding lowers the effective degree by 1 relative to the free product.
Free product effectiveDegree = sum of constituent effectiveDegrees.
Bound state effectiveDegree = free product - (number of bonds). -/

theorem hydrogen_binding_lowers_degree :
    dimHydrogenAtom.effectiveDegree =
      dimProton.effectiveDegree + dimElectron.effectiveDegree - 1 := by decide

theorem deuteron_binding_lowers_degree :
    dimDeuteronIon.effectiveDegree =
      dimProton.effectiveDegree + dimNeutron.effectiveDegree - 1 := by decide

theorem deuterium_two_bonds :
    dimDeuteriumAtom.effectiveDegree =
      dimProton.effectiveDegree + dimNeutron.effectiveDegree +
      dimElectron.effectiveDegree - 2 := by decide

theorem tritium_three_bonds :
    dimTritiumAtom.effectiveDegree =
      dimProton.effectiveDegree + 2 * dimNeutron.effectiveDegree +
      dimElectron.effectiveDegree - 3 := by decide

end FUST.Chemistry
