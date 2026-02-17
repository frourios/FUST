/-
Niobium from D-operator Kernel Structure

Niobium Z = 41 = 2 × nuclearMagic(2) + hydrogenZ = 40 + 1.
Configuration: [Kr] 4d⁴ 5s¹ (anomalous — half-filled proximity).
Nb-93 (Z=41, N=52): only stable isotope.
Nb-93 N = 52 = nuclearMagic(4) + spinDegeneracy = 50 + 2.
NbH is a superconductor — hydrogen strengthening metal.
-/

import FUST.Chemistry.Metals.Zirconium

namespace FUST.Chemistry.Niobium

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Iron
open FUST.Chemistry.Zirconium

/-! ## Section 1: Niobium Parameters

niobiumZ = 41 = zirconiumZ + hydrogenZ = 40 + 1.
Aufbau anomaly: [Kr] 4d⁴ 5s¹ (not 4d³ 5s²).
-/

abbrev niobiumZ : ℕ := 41

theorem niobiumZ_from_zirconium :
    zirconiumZ + hydrogenZ = niobiumZ := rfl

-- [Kr] 4d⁴ 5s¹ (anomalous: 5s has only 1 electron)
abbrev niobium_4d_electrons : ℕ := 4

theorem niobiumZ_shell_filling :
    krCoreElectrons +
    niobium_4d_electrons +  -- 4d: 4 of 10
    1 = niobiumZ             -- 5s: 1
    := rfl

-- 4d vacancy = 10 - 4 = 6
theorem niobium_4d_vacancy :
    Nuclear.subshellCapacity 2 - niobium_4d_electrons = 6 := rfl

/-! ## Section 2: Niobium Isotopes -/

def neutrons (A : ℕ) : ℕ := A - niobiumZ
abbrev neutrons_Nb93 : ℕ := neutrons 93

theorem neutrons_Nb93_eq : neutrons_Nb93 = 52 := rfl

-- N = nuclearMagic(4) + spinDegeneracy = 50 + 2
theorem Nb93_N_from_magic :
    Nuclear.nuclearMagic 4 + Nuclear.spinDegeneracy = neutrons_Nb93 := rfl

/-! ## Section 3: State Functions -/

noncomputable def niobium93Ion (x : ℝ) : ℝ := atomStateFn 41 52 0 x
noncomputable def niobium93Atom (x : ℝ) : ℝ := atomStateFn 41 52 41 x

theorem niobium93Atom_eq (x : ℝ) :
    niobium93Atom x = x ^ 41 * (1 + x) ^ 52 * (1 + ψ * x) ^ 41 := rfl

/-! ## Section 4: FDim Structure -/

set_option maxRecDepth 4096 in
theorem effDeg_niobium93Ion : (dimAtom 41 52 0).effectiveDegree = 1437 := by decide
set_option maxRecDepth 4096 in
theorem effDeg_niobium93Atom : (dimAtom 41 52 41).effectiveDegree = 1519 := by decide

set_option maxRecDepth 4096 in
theorem niobium_effDeg_exceeds_kerD6 :
    (dimAtom 41 52 0).effectiveDegree > 2 ∧
    (dimAtom 41 52 41).effectiveDegree > 2 := by decide

/-! ## Section 5: Mass Number -/

theorem Nb93_mass_number : niobiumZ + neutrons_Nb93 = 93 := rfl

/-! ## Section 6: Summary -/

set_option maxRecDepth 4096 in
theorem niobium_classification :
    niobiumZ = 41 ∧
    zirconiumZ + hydrogenZ = niobiumZ ∧
    Nuclear.nuclearMagic 4 + Nuclear.spinDegeneracy = neutrons_Nb93 ∧
    (dimAtom 41 52 0).effectiveDegree > 2 ∧
    (dimAtom 41 52 41).effectiveDegree > 2 := by
  exact ⟨rfl, rfl, rfl, by decide, by decide⟩

end FUST.Chemistry.Niobium
