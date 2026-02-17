/-
Hydrogen Embrittlement from FDim Theory

Each interstitial hydrogen atom adds ΔZ=1, ΔN=0, Δe=1 to the metal,
increasing the particle count by 2 = spinDegeneracy.
Fe-56 neutral atom particle count = 82 = nuclearMagic(5), a magic
stability point. Any absorbed hydrogen breaks this magic alignment,
providing a degree-based explanation for iron's vulnerability to HE.

d-shell vacancy governs HE susceptibility:
  Ti(8) > Cr(5) > Fe(4) > Ni(2) > Cu(0).
Cu's filled 3d shell (vacancy=0) explains its resistance to HE.
-/

import FUST.Chemistry.Metals.Copper
import FUST.Chemistry.Metals.Titanium
import FUST.Chemistry.Metals.Chromium
import FUST.Chemistry.Metals.Aluminum
import FUST.Chemistry.DihydrogenMolecules

namespace FUST.Chemistry.HydrogenEmbrittlement

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen
open FUST.Chemistry.Iron FUST.Chemistry.Nickel
open FUST.Chemistry.Titanium FUST.Chemistry.Aluminum
open FUST.Chemistry.Copper FUST.Chemistry.Chromium

/-! ## Section 1: Interstitial Hydrogen Effect

Each neutral protium atom absorbed interstitially adds ΔZ=1, ΔN=0, Δe=1
to the metal atom, giving Δ(particle count) = 2 = spinDegeneracy.
effectiveDegree increases by 18 per interstitial H.
-/

-- Each interstitial H adds 2 to particle count
theorem interstitial_H_particleCount (Z N : ℕ) :
    (Z + 1) + N + (Z + 1) = (Z + N + Z) + 2 := by omega

-- n interstitial H atoms add 2n to particle count
theorem interstitial_nH_particleCount (Z N n : ℕ) :
    (Z + n) + N + (Z + n) = (Z + N + Z) + 2 * n := by omega

-- Δ(particle count) per H = spinDegeneracy
theorem interstitial_H_delta_eq_spinDeg :
    2 = Nuclear.spinDegeneracy := rfl

/-! ## Section 2: Iron — Magic Particle Count Destruction

Fe-56 neutral atom has particle count = 82 = nuclearMagic(5).
This is a unique stability point among transition metals.
Interstitial hydrogen destroys this magic alignment.
-/

-- Fe-56 sits at a magic particle count
theorem iron56_at_magic_particleCount :
    ironZ + neutrons_Fe56 + ironZ = Nuclear.nuclearMagic 5 := rfl

-- Any interstitial H moves Fe past the magic particle count
theorem iron_hydride_exceeds_magic (n : ℕ) (hn : n > 0) :
    (ironZ + n) + neutrons_Fe56 + (ironZ + n) > Nuclear.nuclearMagic 5 := by
  have : Nuclear.nuclearMagic 5 = 82 := by decide
  rw [this]; unfold neutrons_Fe56 Iron.neutrons ironZ; omega

-- Fe + nH effectiveDegree values
theorem iron_hydride_effDeg_1H :
    (dimAtom (ironZ + 1) neutrons_Fe56 (ironZ + 1)).effectiveDegree = 937 := by decide
theorem iron_hydride_effDeg_2H :
    (dimAtom (ironZ + 2) neutrons_Fe56 (ironZ + 2)).effectiveDegree = 955 := by decide

-- Fe + 2H effectiveDegree = Ni-58 effectiveDegree
theorem iron_2H_effDeg_eq_nickel :
    (dimAtom (ironZ + 2) neutrons_Fe56 (ironZ + 2)).effectiveDegree =
    (dimAtom nickelZ neutrons_Ni58 nickelZ).effectiveDegree := by decide

/-! ## Section 3: d-Shell Vacancy Classification

3d-shell vacancy determines capacity for H bonding via electron sharing.
Higher vacancy → more available orbitals → greater HE susceptibility.
-/

-- 3d max capacity = 10
abbrev d3_max : ℕ := Nuclear.subshellCapacity 2

-- Vacancy = max - occupied
abbrev titanium_3d_vacancy : ℕ := d3_max - titanium_3d_electrons
abbrev chromium_3d_vac : ℕ := d3_max - chromium_3d_electrons
abbrev iron_3d_vac : ℕ := d3_max - iron_3d_electrons
abbrev nickel_3d_vac : ℕ := d3_max - nickel_3d_electrons
abbrev copper_3d_vac : ℕ := d3_max - copper_3d_electrons

theorem titanium_vacancy : titanium_3d_vacancy = 8 := rfl
theorem chromium_vacancy : chromium_3d_vac = 5 := rfl
theorem iron_vacancy : iron_3d_vac = 4 := rfl
theorem nickel_vacancy : nickel_3d_vac = 2 := rfl
theorem copper_vacancy : copper_3d_vac = 0 := rfl

-- Cu has completely filled d-shell
theorem copper_d_shell_filled : copper_3d_electrons = d3_max := rfl

-- Susceptibility ordering by d-vacancy: Ti(8) > Cr(5) > Fe(4) > Ni(2) > Cu(0)
theorem d_vacancy_ordering :
    titanium_3d_vacancy > chromium_3d_vac ∧
    chromium_3d_vac > iron_3d_vac ∧
    iron_3d_vac > nickel_3d_vac ∧
    nickel_3d_vac > copper_3d_vac := by decide

-- Al has no d-electrons (p-block metal)
theorem aluminum_no_d_electrons :
    aluminumZ < arCoreElectrons + Nuclear.subshellCapacity 0 := by decide

/-! ## Section 4: Iron-Nickel Alloy Stability

Fe-56 and Ni-58 share the same neutron count N=30.
This neutron identity underlies Fe-Ni alloy compatibility.
-/

theorem iron_nickel_neutron_identity :
    neutrons_Fe56 = neutrons_Ni58 := rfl

-- Fe-Ni have consecutive Z (differing by spinDegeneracy)
theorem iron_nickel_Z_diff :
    nickelZ - ironZ = Nuclear.spinDegeneracy := rfl

-- Iron-nickel effectiveDegree gap
theorem iron_nickel_effDeg_gap :
    (dimAtom nickelZ neutrons_Ni58 nickelZ).effectiveDegree -
    (dimAtom ironZ neutrons_Fe56 ironZ).effectiveDegree = 36 := by decide

/-! ## Section 5: Chromium Passivation

Cr-52 has magic neutron number N=28 = nuclearMagic(3).
Half-filled 3d shell provides extra stability.
Fe-Cr alloys (stainless steel) resist HE better than pure Fe.
-/

theorem chromium_magic_neutron :
    neutrons_Cr52 = Nuclear.nuclearMagic 3 := rfl

-- Cr has half-filled d-shell (5 = 10/2)
theorem chromium_half_filled_d :
    chromium_3d_electrons = Nuclear.subshellCapacity 2 / 2 := rfl

-- Fe-Cr: Cr brings magic-N stability to Fe alloy
theorem stainless_steel_magic :
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Cr52) ∧
    Nuclear.subshellCapacity 2 / 2 = chromium_3d_electrons :=
  ⟨⟨3, by omega, rfl⟩, rfl⟩

/-! ## Section 6: Magic Alignment Across Metals

Transition metals with particle counts near magic/hoMagic numbers
show enhanced nuclear binding stability.
-/

-- Ti-48 particle count = hoMagic(4) = 70
theorem titanium_magic_particleCount :
    titaniumZ + neutrons_Ti48 + titaniumZ = Nuclear.hoMagic 4 := rfl

-- Fe-56 particle count = nuclearMagic(5) = 82
theorem iron_magic_particleCount :
    ironZ + neutrons_Fe56 + ironZ = Nuclear.nuclearMagic 5 := rfl

-- Only Fe-56 among these metals has particle count equal to a nuclearMagic number
theorem iron_unique_magic_particleCount :
    ironZ + neutrons_Fe56 + ironZ = Nuclear.nuclearMagic 5 ∧
    nickelZ + neutrons_Ni58 + nickelZ ≠ Nuclear.nuclearMagic 5 ∧
    copperZ + neutrons_Cu63 + copperZ ≠ Nuclear.nuclearMagic 5 := by
  constructor
  · rfl
  constructor <;> decide

-- Ti-48 N = Fe Z (cross-element identity)
theorem titanium_iron_identity :
    neutrons_Ti48 = ironZ := rfl

/-! ## Section 7: Dihydrogen Dissociation at Metal Surface

H₂ → 2H at metal surface: each H adds 18 to the metal's effectiveDegree.
-/

-- H₂ dissociation on Fe: net Δ(effectiveDegree) = 36
theorem iron_H2_absorption_effDeg :
    (dimAtom (ironZ + 2) neutrons_Fe56 (ironZ + 2)).effectiveDegree -
    (dimAtom ironZ neutrons_Fe56 ironZ).effectiveDegree = 36 := by decide

/-! ## Section 8: Summary -/

set_option maxRecDepth 4096 in
theorem hydrogen_embrittlement_classification :
    -- Fe-56 at magic particle count
    ironZ + neutrons_Fe56 + ironZ = Nuclear.nuclearMagic 5 ∧
    -- d-vacancy ordering: Ti(8) > Fe(4) > Ni(2) > Cu(0)
    titanium_3d_vacancy > iron_3d_vac ∧
    iron_3d_vac > nickel_3d_vac ∧
    nickel_3d_vac > copper_3d_vac ∧
    copper_3d_vac = 0 ∧
    -- Fe-Ni neutron identity
    neutrons_Fe56 = neutrons_Ni58 ∧
    -- Ti-48 at hoMagic particle count
    titaniumZ + neutrons_Ti48 + titaniumZ = Nuclear.hoMagic 4 ∧
    -- Cr-52 magic N
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Cr52) := by
  exact ⟨rfl, by decide, by decide, by decide, rfl, rfl, rfl, 3, by omega, rfl⟩

end FUST.Chemistry.HydrogenEmbrittlement
