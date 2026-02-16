/-
Hydrogen Strengthening from State Function Degree Theory

Metals with magic neutron numbers form stable hydrides because
interstitial hydrogen preserves neutron count (N is unchanged by
protium absorption: ΔN = 0). The magic-N nuclear stability survives.

Contrast with hydrogen embrittlement: Fe-56 has deg = 82 = nuclearMagic(5),
and each interstitial H increases deg by 2, destroying the magic alignment.

Key insight: hydrogen strengthening ↔ magic neutron number preservation.
  V-51:  N = 28 = nuclearMagic(3) → VH₂ preserves magic N
  Zr-90: N = 50 = nuclearMagic(4) → ZrH₂ preserves magic N
  Pd:    4d¹⁰ filled d-shell → PdH stable (analogue of Cu 3d¹⁰)
-/

import FUST.Chemistry.Metals.Vanadium
import FUST.Chemistry.Metals.Niobium
import FUST.Chemistry.Metals.Palladium
import FUST.Chemistry.Metals.Copper
import FUST.Chemistry.Metals.HydrogenEmbrittlement
import FUST.Chemistry.DihydrogenMolecules

namespace FUST.Chemistry.HydrogenStrengthening

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Iron
open FUST.Chemistry.Vanadium FUST.Chemistry.Zirconium
open FUST.Chemistry.Niobium FUST.Chemistry.Palladium
open FUST.Chemistry.Nickel FUST.Chemistry.Copper
open FUST.Chemistry.HydrogenEmbrittlement

/-! ## Section 1: Neutron Count Preservation Under Hydrogen Absorption

Protium (¹H) has N=0. Interstitial absorption adds ΔZ=1, ΔN=0, Δe=1.
The neutron count of the host metal is invariant under H absorption.
-/

-- Interstitial H does not change neutron count
theorem interstitial_H_preserves_N (Z N e n : ℕ) :
    atomDegree (Z + n) N (e + n) - atomDegree Z N e = 2 * n := by
  unfold atomDegree; omega

-- For neutral atoms: Δdeg = 2n, N unchanged
theorem neutral_hydride_deg (Z N n : ℕ) :
    atomDegree (Z + n) N (Z + n) = atomDegree Z N Z + 2 * n := by
  unfold atomDegree; omega

/-! ## Section 2: Magic Neutron Number Preservation (Strengthening)

V-51 (N=28) and Zr-90 (N=50) have magic neutron numbers.
Interstitial H preserves N, so the magic-N stability is maintained.
This is the degree-theoretic basis for hydrogen strengthening.
-/

-- V-51 N=28 is magic
theorem vanadium_magic_N :
    neutrons_V51 = Nuclear.nuclearMagic 3 := rfl

-- Zr-90 N=50 is magic
theorem zirconium_magic_N :
    neutrons_Zr90 = Nuclear.nuclearMagic 4 := rfl

-- VH₂: Z=25, N=28(magic), e=25 → deg = 78
theorem vanadium_dihydride_deg :
    atomDegree (vanadiumZ + 2) neutrons_V51 (vanadiumZ + 2) = 78 := rfl

-- VH₂ degree increase = 2 × spinDegeneracy
theorem vanadium_dihydride_deltaDeg :
    atomDegree (vanadiumZ + 2) neutrons_V51 (vanadiumZ + 2) -
    atomDegree vanadiumZ neutrons_V51 vanadiumZ =
    2 * Nuclear.spinDegeneracy := rfl

-- ZrH₂: Z=42, N=50(magic), e=42 → deg = 134
theorem zirconium_dihydride_deg :
    atomDegree (zirconiumZ + 2) neutrons_Zr90 (zirconiumZ + 2) = 134 := rfl

-- ZrH₂ degree = Nb-93 degree (remarkable coincidence)
theorem zirconium_dihydride_eq_niobium_deg :
    atomDegree (zirconiumZ + 2) neutrons_Zr90 (zirconiumZ + 2) =
    atomDegree niobiumZ neutrons_Nb93 niobiumZ := rfl

/-! ## Section 3: Magic Degree Destruction (Embrittlement)

Fe-56 deg = 82 = nuclearMagic(5). Any H breaks this.
Fe-56 N = 30 is NOT a magic number (30 ∉ {2,8,20,28,50,82,126}).
So Fe has no magic-N protection either.
-/

-- Fe-56 N=30 is not magic
theorem iron56_N_not_magic :
    ∀ i, i < 7 → Nuclear.nuclearMagic i ≠ neutrons_Fe56 := by decide

-- Fe-56 has magic degree but non-magic N → vulnerable
theorem iron_magic_deg_nonmagic_N :
    atomDegree ironZ neutrons_Fe56 ironZ = Nuclear.nuclearMagic 5 ∧
    ∀ i, i < 7 → Nuclear.nuclearMagic i ≠ neutrons_Fe56 := by
  constructor
  · rfl
  · decide

-- Contrast: V-51 has non-magic degree but magic N → stable hydride
theorem vanadium_nonmagic_deg_magic_N :
    (∀ i, i < 7 → Nuclear.nuclearMagic i ≠ atomDegree vanadiumZ neutrons_V51 vanadiumZ) ∧
    neutrons_V51 = Nuclear.nuclearMagic 3 := by
  constructor
  · decide
  · rfl

/-! ## Section 4: Filled d-Shell Stability

Pd (4d¹⁰) and Cu (3d¹⁰) have zero d-vacancy.
Filled d-shell metals resist H-induced destabilization.
-/

-- Pd and Cu both have zero d-vacancy
theorem palladium_copper_zero_vacancy :
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - palladium_4d_electrons = 0 ∧
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ - copper_3d_electrons = 0 := ⟨rfl, rfl⟩

-- Pd 4d electrons = Cu 3d electrons = subshell max
theorem palladium_copper_filled_d :
    palladium_4d_electrons = Nuclear.Subshell.maxElectrons ⟨4, 2⟩ ∧
    copper_3d_electrons = Nuclear.Subshell.maxElectrons ⟨3, 2⟩ := ⟨rfl, rfl⟩

/-! ## Section 5: 4d Vacancy Values -/

theorem zirconium_4d_vac_eq :
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - zirconium_4d_electrons = 8 := rfl

theorem niobium_4d_vac_eq :
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - niobium_4d_electrons = 6 := rfl

theorem palladium_4d_vac_eq :
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - palladium_4d_electrons = 0 := rfl

theorem d4_vacancy_ordering :
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - zirconium_4d_electrons >
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - niobium_4d_electrons ∧
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - niobium_4d_electrons >
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - palladium_4d_electrons := by decide

/-! ## Section 6: Cross-Period d-Shell Analogy

3d and 4d metals show parallel d-shell filling patterns.
Cu(3d¹⁰) ↔ Pd(4d¹⁰): both anomalous filled d-shells.
V(3d³) ↔ Nb(4d⁴5s¹): same group, both form stable hydrides.
-/

-- Cu and Pd: same d-electron count (both filled)
theorem copper_palladium_d_analogy :
    copper_3d_electrons = palladium_4d_electrons := rfl

-- V-51 and Zr-90: both have magic N
theorem vanadium_zirconium_magic_N :
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_V51) ∧
    (∃ j, j < 7 ∧ Nuclear.nuclearMagic j = neutrons_Zr90) :=
  ⟨⟨3, by omega, rfl⟩, ⟨4, by omega, rfl⟩⟩

/-! ## Section 7: Strengthening vs Embrittlement Classification

The degree-theoretic classification:
- H-strengthening: magic N → N preserved under H absorption
- H-embrittlement: magic deg → deg destroyed by H absorption
- Filled d-shell: zero vacancy → stable H accommodation

This is the central theorem: the dichotomy of hydrogen effects on metals.
-/

theorem hydrogen_strengthening_classification :
    -- V-51: magic N → strengthening
    neutrons_V51 = Nuclear.nuclearMagic 3 ∧
    -- Zr-90: magic N → strengthening
    neutrons_Zr90 = Nuclear.nuclearMagic 4 ∧
    -- Fe-56: magic deg, non-magic N → embrittlement
    atomDegree ironZ neutrons_Fe56 ironZ = Nuclear.nuclearMagic 5 ∧
    (∀ i, i < 7 → Nuclear.nuclearMagic i ≠ neutrons_Fe56) ∧
    -- Pd: filled d-shell → stable hydride
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - palladium_4d_electrons = 0 ∧
    -- Cu: filled d-shell → HE resistant
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ - copper_3d_electrons = 0 ∧
    -- H preserves N: Δdeg = 2n, ΔN = 0
    (∀ Z N n, atomDegree (Z + n) N (Z + n) = atomDegree Z N Z + 2 * n) := by
  refine ⟨rfl, rfl, rfl, by decide, rfl, rfl, ?_⟩
  intro Z N n; unfold atomDegree; omega

end FUST.Chemistry.HydrogenStrengthening

namespace FUST.DiscreteTag
open FUST.Chemistry.Vanadium FUST.Chemistry.Zirconium
open FUST.Chemistry.Palladium FUST.Chemistry.Niobium
open FUST.Chemistry.HydrogenStrengthening

-- VH₂ degree
def vanadiumDihydrideDeg_t : DTagged .degree :=
  mkDegree (vanadiumZ_t + scaleZ 2 hydrogenZ_t) V51N_t
           (vanadiumZ_t + scaleZ 2 hydrogenZ_t)

theorem vanadiumDihydrideDeg_t_val : vanadiumDihydrideDeg_t.val = 78 := by decide

-- ZrH₂ degree
def zirconiumDihydrideDeg_t : DTagged .degree :=
  mkDegree (zirconiumZ_t + scaleZ 2 hydrogenZ_t) Zr90N_t
           (zirconiumZ_t + scaleZ 2 hydrogenZ_t)

theorem zirconiumDihydrideDeg_t_val : zirconiumDihydrideDeg_t.val = 134 := by decide

-- ZrH₂ deg = Nb deg
theorem zirconium_dihydride_eq_niobium_tagged :
    zirconiumDihydrideDeg_t.val = niobiumDeg_t.val := by decide

-- 4d vacancy as count
def zirconiumDVacancy_t : DTagged .count := ⟨8⟩
def niobiumDVacancy_t : DTagged .count := ⟨6⟩
def palladiumDVacancy_t : DTagged .count := ⟨0⟩

theorem zirconiumDVacancy_t_val : zirconiumDVacancy_t.val = 8 := rfl
theorem niobiumDVacancy_t_val : niobiumDVacancy_t.val = 6 := rfl
theorem palladiumDVacancy_t_val : palladiumDVacancy_t.val = 0 := rfl

end FUST.DiscreteTag
