/-
Iron Z = 26 = nuclearMagic(3) - spinDegeneracy = 28 - 2.
Configuration: [Ar] 3d⁶ 4s² (period 4, Group VIII transition metal).
Fe-56 (Z=26, N=30): most abundant isotope.
Fe-56 neutral atom particle count Z+N+e = 82 = nuclearMagic(5).
-/

import FUST.Chemistry.SulfurAtom

namespace FUST.Chemistry.Iron

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen

/-! ## Section 1: Iron Parameters

ironZ = 26 = nuclearMagic(3) - spinDegeneracy = 28 - 2.
Aufbau: 1s² 2s² 2p⁶ 3s² 3p⁶ 4s² 3d⁶.
-/

abbrev ironZ : ℕ := 26

theorem ironZ_from_magic :
    Nuclear.nuclearMagic 3 - Nuclear.spinDegeneracy = ironZ := rfl

-- Ar core (1s² 2s² 2p⁶ 3s² 3p⁶) = 18
abbrev arCoreElectrons : ℕ := 18

theorem arCore_eq :
    Nuclear.subshellCapacity 0 +
    Nuclear.subshellCapacity 0 +
    Nuclear.subshellCapacity 1 +
    Nuclear.subshellCapacity 0 +
    Nuclear.subshellCapacity 1 = arCoreElectrons := rfl

-- [Ar] 3d⁶ 4s²
abbrev iron_3d_electrons : ℕ := 6

theorem ironZ_shell_filling :
    arCoreElectrons +
    Nuclear.subshellCapacity 0 +  -- 4s: 2
    iron_3d_electrons = ironZ                 -- 3d: 6 of 10
    := rfl

-- 3d vacancy = 10 - 6 = 4
theorem iron_3d_vacancy :
    Nuclear.subshellCapacity 2 - iron_3d_electrons = 4 := rfl

/-! ## Section 2: Iron Isotopes -/

def neutrons (A : ℕ) : ℕ := A - ironZ
abbrev neutrons_Fe54 : ℕ := neutrons 54
abbrev neutrons_Fe56 : ℕ := neutrons 56
abbrev neutrons_Fe57 : ℕ := neutrons 57
abbrev neutrons_Fe58 : ℕ := neutrons 58

theorem neutrons_Fe54_eq : neutrons_Fe54 = 28 := rfl
theorem neutrons_Fe56_eq : neutrons_Fe56 = 30 := rfl
theorem neutrons_Fe57_eq : neutrons_Fe57 = 31 := rfl
theorem neutrons_Fe58_eq : neutrons_Fe58 = 32 := rfl

-- Fe-54 has a magic neutron number N=28
theorem Fe54_neutron_magic :
    ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Fe54 := ⟨3, by omega, rfl⟩

/-! ## Section 3: State Functions -/

noncomputable def iron56Ion (x : ℝ) : ℝ := atomStateFn 26 30 0 x
noncomputable def iron56Atom (x : ℝ) : ℝ := atomStateFn 26 30 26 x

theorem iron56Atom_eq (x : ℝ) :
    iron56Atom x = x ^ 26 * (1 + x) ^ 30 * (1 + ψ * x) ^ 26 := rfl

/-! ## Section 4: FDim Structure -/

theorem effDeg_iron56Ion : (dimAtom 26 30 0).effectiveDegree = 867 := by decide
theorem effDeg_iron56Atom : (dimAtom 26 30 26).effectiveDegree = 919 := by decide

-- Fe-56 neutral atom particle count = nuclearMagic(5) = 82
theorem iron56_particleCount_is_magic : 26 + 30 + 26 = Nuclear.nuclearMagic 5 := rfl

/-! ## Section 5: Mass Numbers -/

theorem Fe54_mass_number : ironZ + neutrons_Fe54 = 54 := rfl
theorem Fe56_mass_number : ironZ + neutrons_Fe56 = 56 := rfl
theorem Fe57_mass_number : ironZ + neutrons_Fe57 = 57 := rfl
theorem Fe58_mass_number : ironZ + neutrons_Fe58 = 58 := rfl

/-! ## Section 6: Summary -/

theorem iron_classification :
    ironZ = 26 ∧
    Nuclear.nuclearMagic 3 - Nuclear.spinDegeneracy = ironZ ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Fe54) ∧
    26 + 30 + 26 = Nuclear.nuclearMagic 5 ∧
    (dimAtom 26 30 0).effectiveDegree > 2 ∧
    (dimAtom 26 30 26).effectiveDegree > 2 := by
  exact ⟨rfl, rfl, ⟨3, by omega, rfl⟩, rfl, by decide, by decide⟩

end FUST.Chemistry.Iron
