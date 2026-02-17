/-
Chromium from D-operator Kernel Structure

Chromium Z = 24 = nuclearMagic(2) + 2·spinDegeneracy = 20 + 4.
Configuration: [Ar] 3d⁵ 4s¹ (anomalous — half-filled d-shell).
Cr-52 (Z=24, N=28): most abundant isotope.
Cr-52 has magic neutron number N = 28 = nuclearMagic(3).
-/

import FUST.Chemistry.Metals.Iron

namespace FUST.Chemistry.Chromium

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Iron
open FUST.Chemistry.Helium FUST.Chemistry.Dihydrogen

/-! ## Section 1: Chromium Parameters

chromiumZ = 24 = nuclearMagic(2) + 2·spinDegeneracy = 20 + 4.
Aufbau anomaly: [Ar] 3d⁵ 4s¹ (not 3d⁴ 4s²). Half-filled d-shell.
-/

abbrev chromiumZ : ℕ := 24

theorem chromiumZ_from_magic :
    Nuclear.nuclearMagic 2 + 2 * Nuclear.spinDegeneracy = chromiumZ := rfl

-- [Ar] 3d⁵ 4s¹ (anomalous: half-filled d-shell preferred)
abbrev chromium_3d_electrons : ℕ := 5

theorem chromiumZ_shell_filling :
    arCoreElectrons +
    chromium_3d_electrons +  -- 3d: 5 of 10 (half-filled!)
    1 = chromiumZ             -- 4s: 1
    := rfl

-- Half-filled 3d shell: 5 = maxElectrons(3,2) / 2
theorem chromium_3d_half_filled :
    Nuclear.subshellCapacity 2 / 2 = chromium_3d_electrons := rfl

-- 3d vacancy = 10 - 5 = 5
theorem chromium_3d_vacancy :
    Nuclear.subshellCapacity 2 - chromium_3d_electrons = 5 := rfl

/-! ## Section 2: Chromium Isotopes -/

def neutrons (A : ℕ) : ℕ := A - chromiumZ
abbrev neutrons_Cr52 : ℕ := neutrons 52
abbrev neutrons_Cr53 : ℕ := neutrons 53

theorem neutrons_Cr52_eq : neutrons_Cr52 = 28 := rfl
theorem neutrons_Cr53_eq : neutrons_Cr53 = 29 := rfl

-- Cr-52 has magic neutron number N = 28 = nuclearMagic(3)
theorem Cr52_neutron_magic :
    ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Cr52 := ⟨3, by omega, rfl⟩

/-! ## Section 3: State Functions -/

noncomputable def chromium52Ion (x : ℝ) : ℝ := atomStateFn 24 28 0 x
noncomputable def chromium52Atom (x : ℝ) : ℝ := atomStateFn 24 28 24 x

theorem chromium52Atom_eq (x : ℝ) :
    chromium52Atom x = x ^ 24 * (1 + x) ^ 28 * (1 + ψ * x) ^ 24 := rfl

/-! ## Section 4: FDim Structure -/

theorem effDeg_chromium52Ion : (dimAtom 24 28 0).effectiveDegree = 805 := by decide
theorem effDeg_chromium52Atom : (dimAtom 24 28 24).effectiveDegree = 853 := by decide

theorem chromium_effDeg_exceeds_kerD6 :
    (dimAtom 24 28 0).effectiveDegree > 2 ∧
    (dimAtom 24 28 24).effectiveDegree > 2 := by decide

/-! ## Section 5: Mass Numbers -/

theorem Cr52_mass_number : chromiumZ + neutrons_Cr52 = 52 := rfl
theorem Cr53_mass_number : chromiumZ + neutrons_Cr53 = 53 := rfl

/-! ## Section 6: Summary -/

theorem chromium_classification :
    chromiumZ = 24 ∧
    Nuclear.nuclearMagic 2 + 2 * Nuclear.spinDegeneracy = chromiumZ ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Cr52) ∧
    Nuclear.subshellCapacity 2 / 2 = chromium_3d_electrons ∧
    (dimAtom 24 28 0).effectiveDegree > 2 ∧
    (dimAtom 24 28 24).effectiveDegree > 2 := by
  exact ⟨rfl, rfl, ⟨3, by omega, rfl⟩, rfl, by decide, by decide⟩

end FUST.Chemistry.Chromium
