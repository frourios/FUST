/-
Aluminum Z = 13 = closedShellElectronCount(2) + spatialDim = 10 + 3.
Configuration: [Ne] 3s² 3p¹ (p-block metal, no d-electrons).
Al-27 (Z=13, N=14): only stable isotope. N = 2 × nitrogenZ.
-/

import FUST.Chemistry.SulfurAtom

namespace FUST.Chemistry.Aluminum

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Nitrogen

/-! ## Section 1: Aluminum Parameters

aluminumZ = 13 = closedShellElectronCount(2) + spatialDim = 10 + 3.
Aufbau: [Ne] 3s² 3p¹. p-block metal with no d-electrons.
-/

abbrev aluminumZ : ℕ := 13

theorem aluminumZ_derivation :
    closedShellElectronCount 2 + 3 = aluminumZ := by decide

-- [Ne] 3s² 3p¹
theorem aluminumZ_shell_filling :
    closedShellElectronCount 2 +
    Nuclear.subshellCapacity 0 +  -- 3s: 2
    1 = aluminumZ                             -- 3p: 1 of 6
    := by decide

-- Valence = 3 (group IIIA)
theorem aluminum_valence :
    aluminumZ - closedShellElectronCount 2 = 3 := by decide

/-! ## Section 2: Aluminum Isotope -/

def neutrons (A : ℕ) : ℕ := A - aluminumZ
abbrev neutrons_Al27 : ℕ := neutrons 27

theorem neutrons_Al27_eq : neutrons_Al27 = 14 := rfl

-- Al-27 N = 2 × nitrogenZ
theorem Al27_N_eq_2nitrogenZ : neutrons_Al27 = 2 * nitrogenZ := rfl

/-! ## Section 3: State Functions -/

noncomputable def aluminum27Ion (x : ℝ) : ℝ := atomStateFn 13 14 0 x
noncomputable def aluminum27Atom (x : ℝ) : ℝ := atomStateFn 13 14 13 x

theorem aluminum27Atom_eq (x : ℝ) :
    aluminum27Atom x = x ^ 13 * (1 + x) ^ 14 * (1 + ψ * x) ^ 13 := rfl

/-! ## Section 4: FDim Structure -/

theorem effDeg_aluminum27Ion : (dimAtom 13 14 0).effectiveDegree = 419 := by decide
theorem effDeg_aluminum27Atom : (dimAtom 13 14 13).effectiveDegree = 445 := by decide

/-! ## Section 5: Mass Number -/

theorem Al27_mass_number : aluminumZ + neutrons_Al27 = 27 := rfl

/-! ## Section 6: Summary -/

theorem aluminum_classification :
    aluminumZ = 13 ∧
    closedShellElectronCount 2 + 3 = aluminumZ ∧
    neutrons_Al27 = 2 * nitrogenZ ∧
    (dimAtom 13 14 0).effectiveDegree > 2 ∧
    (dimAtom 13 14 13).effectiveDegree > 2 := by
  exact ⟨rfl, by decide, rfl, by decide, by decide⟩

end FUST.Chemistry.Aluminum
