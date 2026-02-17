/-
Nickel from D-operator Kernel Structure

Nickel Z = 28 = nuclearMagic(3) — proton number itself is a magic number.
Configuration: [Ar] 3d⁸ 4s².
Ni-58 (Z=28, N=30): most abundant isotope. N=30 = Fe-56.N.
-/

import FUST.Chemistry.Metals.Iron

namespace FUST.Chemistry.Nickel

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Iron
open FUST.Chemistry.Helium FUST.Chemistry.Dihydrogen

/-! ## Section 1: Nickel Parameters

nickelZ = 28 = nuclearMagic(3). Aufbau: [Ar] 3d⁸ 4s².
-/

abbrev nickelZ : ℕ := 28

theorem nickelZ_is_magic :
    ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = nickelZ := ⟨3, by omega, rfl⟩

theorem nickelZ_eq_magic3 : Nuclear.nuclearMagic 3 = nickelZ := rfl

-- [Ar] 3d⁸ 4s²
abbrev nickel_3d_electrons : ℕ := 8

theorem nickelZ_shell_filling :
    arCoreElectrons +
    Nuclear.subshellCapacity 0 +  -- 4s: 2
    nickel_3d_electrons = nickelZ              -- 3d: 8 of 10
    := rfl

-- 3d vacancy = 10 - 8 = 2
theorem nickel_3d_vacancy :
    Nuclear.subshellCapacity 2 - nickel_3d_electrons = 2 := rfl

/-! ## Section 2: Nickel Isotopes -/

def neutrons (A : ℕ) : ℕ := A - nickelZ
abbrev neutrons_Ni58 : ℕ := neutrons 58
abbrev neutrons_Ni60 : ℕ := neutrons 60

theorem neutrons_Ni58_eq : neutrons_Ni58 = 30 := rfl
theorem neutrons_Ni60_eq : neutrons_Ni60 = 32 := rfl

-- Fe-56 and Ni-58 share the same neutron count N=30
theorem iron_nickel_same_N : neutrons_Fe56 = neutrons_Ni58 := rfl

/-! ## Section 3: State Functions -/

noncomputable def nickel58Ion (x : ℝ) : ℝ := atomStateFn 28 30 0 x
noncomputable def nickel58Atom (x : ℝ) : ℝ := atomStateFn 28 30 28 x

theorem nickel58Atom_eq (x : ℝ) :
    nickel58Atom x = x ^ 28 * (1 + x) ^ 30 * (1 + ψ * x) ^ 28 := rfl

/-! ## Section 4: FDim Structure -/

theorem effDeg_nickel58Ion : (dimAtom 28 30 0).effectiveDegree = 899 := by decide
theorem effDeg_nickel58Atom : (dimAtom 28 30 28).effectiveDegree = 955 := by decide

theorem nickel_effDeg_exceeds_kerD6 :
    (dimAtom 28 30 0).effectiveDegree > 2 ∧
    (dimAtom 28 30 28).effectiveDegree > 2 := by decide

/-! ## Section 5: Mass Numbers -/

theorem Ni58_mass_number : nickelZ + neutrons_Ni58 = 58 := rfl
theorem Ni60_mass_number : nickelZ + neutrons_Ni60 = 60 := rfl

/-! ## Section 6: Summary -/

theorem nickel_classification :
    nickelZ = 28 ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = nickelZ) ∧
    neutrons_Fe56 = neutrons_Ni58 ∧
    (dimAtom 28 30 0).effectiveDegree > 2 ∧
    (dimAtom 28 30 28).effectiveDegree > 2 := by
  exact ⟨rfl, ⟨3, by omega, rfl⟩, rfl, by decide, by decide⟩

end FUST.Chemistry.Nickel
