/-
Oxygen Isotopes and Ionization from D-operator Kernel Structure

FDim for each species: dimAtom(Z, N, e) with effectiveDegree = 16Z + 15N + 2e + 1.
O-16 (Z=8, N=8) is doubly magic, connecting to Nuclear.lean.
-/

import FUST.DifferenceOperators
import FUST.Physics.Nuclear
import FUST.Chemistry.AtomDim

namespace FUST.Chemistry.Oxygen

open FUST FUST.Dim FUST.Chemistry

/-! ## Section 1: Oxygen Parameters

oxygenZ = 8 = nuclearMagic(1), so oxygen's proton number is a nuclear magic number.
Neutron counts are derived from mass numbers: N = A - Z.
-/

abbrev oxygenZ : ℕ := Nuclear.nuclearMagic 1

theorem oxygenZ_eq : oxygenZ = 8 := rfl

-- Stable isotope neutron counts: N = A - Z
def neutrons (A : ℕ) : ℕ := A - oxygenZ
abbrev neutrons_O16 : ℕ := neutrons 16
abbrev neutrons_O17 : ℕ := neutrons 17
abbrev neutrons_O18 : ℕ := neutrons 18

theorem neutrons_O16_eq : neutrons_O16 = 8 := rfl
theorem neutrons_O17_eq : neutrons_O17 = 9 := rfl
theorem neutrons_O18_eq : neutrons_O18 = 10 := rfl

/-! ## Section 3: Oxygen Species State Functions -/

-- Bare nuclei (fully ionized)
noncomputable def oxygen16Ion (x : ℝ) : ℝ := atomStateFn 8 8 0 x
noncomputable def oxygen17Ion (x : ℝ) : ℝ := atomStateFn 8 9 0 x
noncomputable def oxygen18Ion (x : ℝ) : ℝ := atomStateFn 8 10 0 x

-- Neutral atoms
noncomputable def oxygen16Atom (x : ℝ) : ℝ := atomStateFn 8 8 8 x
noncomputable def oxygen17Atom (x : ℝ) : ℝ := atomStateFn 8 9 8 x
noncomputable def oxygen18Atom (x : ℝ) : ℝ := atomStateFn 8 10 8 x

-- Common ions
noncomputable def oxideAnion (x : ℝ) : ℝ := atomStateFn 8 8 10 x
noncomputable def superoxideAnion (x : ℝ) : ℝ := atomStateFn 8 8 9 x
noncomputable def oxygenCation (x : ℝ) : ℝ := atomStateFn 8 8 7 x

/-! ## Section 4: Factored Form Identities -/

theorem oxygen16Ion_eq (x : ℝ) :
    oxygen16Ion x = x ^ 8 * (1 + x) ^ 8 := by
  unfold oxygen16Ion atomStateFn; simp [pow_zero, mul_one]

theorem oxygen16Atom_eq (x : ℝ) :
    oxygen16Atom x = x ^ 8 * (1 + x) ^ 8 * (1 + ψ * x) ^ 8 := rfl

theorem oxideAnion_eq (x : ℝ) :
    oxideAnion x = x ^ 8 * (1 + x) ^ 8 * (1 + ψ * x) ^ 10 := rfl

/-! ## Section 5: FDim Structure -/

theorem effDeg_oxygen16Ion : (dimAtom 8 8 0).effectiveDegree = 249 := by decide
theorem effDeg_oxygen17Ion : (dimAtom 8 9 0).effectiveDegree = 264 := by decide
theorem effDeg_oxygen18Ion : (dimAtom 8 10 0).effectiveDegree = 279 := by decide
theorem effDeg_oxygen16Atom : (dimAtom 8 8 8).effectiveDegree = 265 := by decide
theorem effDeg_oxygen17Atom : (dimAtom 8 9 8).effectiveDegree = 280 := by decide
theorem effDeg_oxygen18Atom : (dimAtom 8 10 8).effectiveDegree = 295 := by decide
theorem effDeg_oxideAnion : (dimAtom 8 8 10).effectiveDegree = 269 := by decide
theorem effDeg_superoxideAnion : (dimAtom 8 8 9).effectiveDegree = 267 := by decide
theorem effDeg_oxygenCation : (dimAtom 8 8 7).effectiveDegree = 263 := by decide

/-! ## Section 6: Ionization Series -/

theorem ionization_effDeg_O16 :
    (dimAtom 8 8 0).effectiveDegree = 249 ∧   -- O⁸⁺
    (dimAtom 8 8 1).effectiveDegree = 251 ∧   -- O⁷⁺
    (dimAtom 8 8 2).effectiveDegree = 253 ∧   -- O⁶⁺
    (dimAtom 8 8 3).effectiveDegree = 255 ∧   -- O⁵⁺
    (dimAtom 8 8 4).effectiveDegree = 257 ∧   -- O⁴⁺
    (dimAtom 8 8 5).effectiveDegree = 259 ∧   -- O³⁺
    (dimAtom 8 8 6).effectiveDegree = 261 ∧   -- O²⁺
    (dimAtom 8 8 7).effectiveDegree = 263 ∧   -- O⁺
    (dimAtom 8 8 8).effectiveDegree = 265 ∧   -- O
    (dimAtom 8 8 9).effectiveDegree = 267 ∧   -- O⁻
    (dimAtom 8 8 10).effectiveDegree = 269     -- O²⁻
    := by decide

-- Each electron adds 2 to effectiveDegree (= 2 × dimElectron.effDeg - 1 binding)
theorem ionization_step_is_two :
    (dimAtom 8 8 1).effectiveDegree - (dimAtom 8 8 0).effectiveDegree = 2 := by decide

/-! ## Section 7: Nuclear Magic Number Connection

O-16 is doubly magic (Z=8, N=8). This connects to FUST.Nuclear.O16.
-/

theorem oxygen16_proton_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = 8 :=
  ⟨1, by omega, rfl⟩

theorem oxygen16_neutron_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = 8 :=
  ⟨1, by omega, rfl⟩

theorem oxygen16_mass_number : oxygenZ + neutrons_O16 = 16 := rfl
theorem oxygen17_mass_number : oxygenZ + neutrons_O17 = 17 := rfl
theorem oxygen18_mass_number : oxygenZ + neutrons_O18 = 18 := rfl

/-! ## Section 8: FDim Distinctness

Isotopes and ionization states have distinct FDim. -/

theorem oxygen_isotopes_distinct :
    dimAtom 8 8 0 ≠ dimAtom 8 9 0 ∧
    dimAtom 8 8 0 ≠ dimAtom 8 10 0 ∧
    dimAtom 8 9 0 ≠ dimAtom 8 10 0 := by decide

theorem oxygen_ion_atom_distinct :
    dimAtom 8 8 0 ≠ dimAtom 8 8 8 ∧
    dimAtom 8 8 8 ≠ dimAtom 8 8 10 := by decide

/-! ## Section 9: Electron Shell Filling -/

theorem oxygen_electron_count : oxygenZ = 8 := rfl

-- 1s² + 2s² + 2p⁴ = 8
theorem oxygen_shell_filling :
    Nuclear.subshellCapacity 0 +  -- 1s: 2
    Nuclear.subshellCapacity 0 +  -- 2s: 2
    4 = oxygenZ                               -- 2p: 4 of 6
    := rfl

-- Oxide O²⁻ fills the 2p shell completely
theorem oxide_fills_2p :
    Nuclear.subshellCapacity 0 +  -- 1s: 2
    Nuclear.subshellCapacity 0 +  -- 2s: 2
    Nuclear.subshellCapacity 1    -- 2p: 6
    = 10 := rfl

-- Shell 1 capacity + shell 2 capacity = 2 + 8 = 10
theorem oxide_fills_two_shells :
    Nuclear.shellCapacity 1 + Nuclear.shellCapacity 2 = 10 := rfl

/-! ## Section 10: Summary -/

theorem oxygen_isotope_classification :
    -- O-16 is doubly magic
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = oxygenZ) ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_O16) ∧
    -- All oxygen species have distinct FDim
    dimAtom 8 8 0 ≠ dimAtom 8 8 8 ∧
    -- effectiveDegree values
    (dimAtom 8 8 0).effectiveDegree = 249 ∧
    (dimAtom 8 8 8).effectiveDegree = 265 ∧
    (dimAtom 8 8 10).effectiveDegree = 269 := by
  exact ⟨⟨1, by omega, rfl⟩, ⟨1, by omega, rfl⟩, by decide, by decide, by decide, by decide⟩

end FUST.Chemistry.Oxygen
