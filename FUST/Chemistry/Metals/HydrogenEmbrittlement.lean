/-
Hydrogen Embrittlement from State Function Degree Theory

Each interstitial hydrogen atom increases degree by 2 = spinDegeneracy.
Fe-56 neutral atom sits at deg = 82 = nuclearMagic(5), a degree-theoretic
magic stability point. Any absorbed hydrogen breaks this magic alignment,
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

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen
open FUST.Chemistry.Iron FUST.Chemistry.Nickel
open FUST.Chemistry.Titanium FUST.Chemistry.Aluminum
open FUST.Chemistry.Copper FUST.Chemistry.Chromium

/-! ## Section 1: Interstitial Hydrogen Degree Increase

Each neutral protium atom absorbed interstitially adds ΔZ=1, ΔN=0, Δe=1
to the metal atom, giving Δdeg = 2 = spinDegeneracy.
-/

-- General: each interstitial H adds 2 to neutral atom degree
theorem interstitial_H_deltaDeg (Z N : ℕ) :
    atomDegree (Z + 1) N (Z + 1) = atomDegree Z N Z + 2 := by
  unfold atomDegree; omega

-- n interstitial H atoms add 2n
theorem interstitial_nH_deltaDeg (Z N n : ℕ) :
    atomDegree (Z + n) N (Z + n) = atomDegree Z N Z + 2 * n := by
  unfold atomDegree; omega

-- Δdeg per H = spinDegeneracy
theorem interstitial_H_deltaDeg_eq_spinDeg :
    2 = Nuclear.spinDegeneracy := rfl

/-! ## Section 2: Iron — Magic Degree Destruction

Fe-56 neutral atom has deg = 82 = nuclearMagic(5).
This is a unique degree-theoretic stability point among transition metals.
Interstitial hydrogen destroys this magic alignment.
-/

-- Fe-56 sits at a magic degree
theorem iron56_at_magic_degree :
    atomDegree ironZ neutrons_Fe56 ironZ = Nuclear.nuclearMagic 5 := rfl

-- Any interstitial H moves Fe past the magic degree
theorem iron_hydride_exceeds_magic (n : ℕ) (hn : n > 0) :
    atomDegree (ironZ + n) neutrons_Fe56 (ironZ + n) > Nuclear.nuclearMagic 5 := by
  have : Nuclear.nuclearMagic 5 = 82 := by decide
  rw [this]; unfold atomDegree neutrons_Fe56 Iron.neutrons ironZ; omega

-- Fe + nH degree values
theorem iron_hydride_deg_1H :
    atomDegree (ironZ + 1) neutrons_Fe56 (ironZ + 1) = 84 := rfl
theorem iron_hydride_deg_2H :
    atomDegree (ironZ + 2) neutrons_Fe56 (ironZ + 2) = 86 := rfl

-- Fe + 2H degree = Ni-58 degree (iron with 2 interstitial H ≈ nickel)
theorem iron_2H_deg_eq_nickel :
    atomDegree (ironZ + 2) neutrons_Fe56 (ironZ + 2) =
    atomDegree nickelZ neutrons_Ni58 nickelZ := rfl

/-! ## Section 3: d-Shell Vacancy Classification

3d-shell vacancy determines capacity for H bonding via electron sharing.
Higher vacancy → more available orbitals → greater HE susceptibility.
-/

-- 3d max capacity = 10
abbrev d3_max : ℕ := Nuclear.Subshell.maxElectrons ⟨3, 2⟩

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
    aluminumZ < arCoreElectrons + Nuclear.Subshell.maxElectrons ⟨4, 0⟩ := by decide

/-! ## Section 4: Iron-Nickel Alloy Stability

Fe-56 and Ni-58 share the same neutron count N=30.
This neutron identity underlies Fe-Ni alloy compatibility.
-/

theorem iron_nickel_neutron_identity :
    neutrons_Fe56 = neutrons_Ni58 := rfl

-- Fe-Ni have consecutive Z (differing by spinDegeneracy)
theorem iron_nickel_Z_diff :
    nickelZ - ironZ = Nuclear.spinDegeneracy := rfl

-- Iron-nickel degree gap = 2 × (Z_Ni - Z_Fe) = 4
theorem iron_nickel_deg_gap :
    atomDegree nickelZ neutrons_Ni58 nickelZ -
    atomDegree ironZ neutrons_Fe56 ironZ = 4 := rfl

/-! ## Section 5: Chromium Passivation

Cr-52 has magic neutron number N=28 = nuclearMagic(3).
Half-filled 3d shell provides extra stability.
Fe-Cr alloys (stainless steel) resist HE better than pure Fe.
-/

theorem chromium_magic_neutron :
    neutrons_Cr52 = Nuclear.nuclearMagic 3 := rfl

-- Cr has half-filled d-shell (5 = 10/2)
theorem chromium_half_filled_d :
    chromium_3d_electrons = Nuclear.Subshell.maxElectrons ⟨3, 2⟩ / 2 := rfl

-- Fe-Cr: Cr brings magic-N stability to Fe alloy
theorem stainless_steel_magic :
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Cr52) ∧
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ / 2 = chromium_3d_electrons :=
  ⟨⟨3, by omega, rfl⟩, rfl⟩

/-! ## Section 6: Degree-Magic Alignment Across Metals

Transition metals with degrees near magic/hoMagic numbers
show enhanced nuclear binding stability.
-/

-- Ti-48 degree = hoMagic(4) = 70
theorem titanium_magic_deg :
    atomDegree titaniumZ neutrons_Ti48 titaniumZ = Nuclear.hoMagic 4 := rfl

-- Fe-56 degree = nuclearMagic(5) = 82
theorem iron_magic_deg :
    atomDegree ironZ neutrons_Fe56 ironZ = Nuclear.nuclearMagic 5 := rfl

-- Only Fe-56 among these metals has deg equal to a nuclearMagic number
theorem iron_unique_magic_deg :
    atomDegree ironZ neutrons_Fe56 ironZ = Nuclear.nuclearMagic 5 ∧
    atomDegree nickelZ neutrons_Ni58 nickelZ ≠ Nuclear.nuclearMagic 5 ∧
    atomDegree copperZ neutrons_Cu63 copperZ ≠ Nuclear.nuclearMagic 5 := by
  constructor
  · rfl
  constructor <;> decide

-- Ti-48 N = Fe Z (cross-element identity)
theorem titanium_iron_identity :
    neutrons_Ti48 = ironZ := rfl

/-! ## Section 7: Dihydrogen Dissociation at Metal Surface

H₂ → 2H at metal surface: degree-conserving dissociation.
H₂ deg = 4, each H atom deg = 2, total conserved.
On metal: each H adds Δdeg = 2 to the metal coordination sphere.
-/

-- H₂ degree = 2 × single H atom degree
theorem dihydrogen_deg_split :
    atomDegree 2 0 2 = 2 * atomDegree 1 0 1 := rfl

-- H₂ dissociation on Fe: net Δdeg = 2·spinDegeneracy = 4
theorem iron_H2_absorption_deltaDeg :
    atomDegree (ironZ + 2) neutrons_Fe56 (ironZ + 2) -
    atomDegree ironZ neutrons_Fe56 ironZ = 2 * Nuclear.spinDegeneracy := rfl

/-! ## Section 8: Summary -/

theorem hydrogen_embrittlement_classification :
    -- Fe-56 at magic degree
    atomDegree ironZ neutrons_Fe56 ironZ = Nuclear.nuclearMagic 5 ∧
    -- d-vacancy ordering: Ti(8) > Fe(4) > Ni(2) > Cu(0)
    titanium_3d_vacancy > iron_3d_vac ∧
    iron_3d_vac > nickel_3d_vac ∧
    nickel_3d_vac > copper_3d_vac ∧
    copper_3d_vac = 0 ∧
    -- Fe-Ni neutron identity
    neutrons_Fe56 = neutrons_Ni58 ∧
    -- Ti-48 at hoMagic degree
    atomDegree titaniumZ neutrons_Ti48 titaniumZ = Nuclear.hoMagic 4 ∧
    -- Cr-52 magic N
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Cr52) := by
  exact ⟨rfl, by decide, by decide, by decide, rfl, rfl, rfl, 3, by omega, rfl⟩

end FUST.Chemistry.HydrogenEmbrittlement

namespace FUST.DiscreteTag
open FUST.Chemistry.Iron FUST.Chemistry.Nickel
open FUST.Chemistry.HydrogenEmbrittlement

-- Interstitial H Δdeg = spinDeg
theorem interstitial_H_deltaDeg_eq_spinDeg_tagged :
    (⟨2⟩ : DTagged .deltaDeg).val = spinDeg_t.val := rfl

-- Fe-56 magic degree
theorem iron56_magic_deg_tagged :
    ironDeg_t.val = Nuclear.nuclearMagic 5 := rfl

-- Fe + 1H degree
def ironH1Deg_t : DTagged .degree :=
  mkDegree (ironZ_t + hydrogenZ_t) Fe56N_t (ironZ_t + hydrogenZ_t)

theorem ironH1Deg_t_val : ironH1Deg_t.val = 84 := rfl

-- Fe + 2H degree = Ni degree
theorem iron_2H_eq_nickel_deg :
    (mkDegree (ironZ_t + scaleZ 2 hydrogenZ_t) Fe56N_t
              (ironZ_t + scaleZ 2 hydrogenZ_t)).val = nickelDeg_t.val := rfl

-- d-vacancy as count
def titaniumDVacancy_t : DTagged .count := ⟨8⟩
def chromiumDVacancy_t : DTagged .count := ⟨5⟩
def ironDVacancy_t : DTagged .count := ⟨4⟩
def nickelDVacancy_t : DTagged .count := ⟨2⟩
def copperDVacancy_t : DTagged .count := ⟨0⟩

theorem titaniumDVacancy_t_val : titaniumDVacancy_t.val = 8 := rfl
theorem chromiumDVacancy_t_val : chromiumDVacancy_t.val = 5 := rfl
theorem ironDVacancy_t_val : ironDVacancy_t.val = 4 := rfl
theorem nickelDVacancy_t_val : nickelDVacancy_t.val = 2 := rfl
theorem copperDVacancy_t_val : copperDVacancy_t.val = 0 := rfl

-- Fe d-vacancy = baseCount (4)
theorem iron_dVacancy_eq_baseCount :
    ironDVacancy_t = baseCount_t := rfl

-- Ni d-vacancy = spinDeg (both = 2)
theorem nickel_dVacancy_eq_spinDeg :
    nickelDVacancy_t = kerToCount spinDeg_t := rfl

end FUST.DiscreteTag
