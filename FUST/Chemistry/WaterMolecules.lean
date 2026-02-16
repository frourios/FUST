/-
Water, Dioxygen, and Hydroxide Molecules from the Multiplicative State Function Model

Molecular state function g(x) = x^Z · (1+x)^N · (1+ψx)^e
where Z, N, e are total proton, neutron, electron counts.

Key discovery: D₂O and H₂¹⁸O are isodegree (Z=10, N=10, e=10, deg=30).
-/

import FUST.DifferenceOperators
import FUST.Physics.Nuclear
import FUST.Chemistry.OxygenIsotopes
import FUST.Chemistry.DihydrogenMolecules
import FUST.Chemistry.HeliumInertness

namespace FUST.Chemistry.Water

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Dihydrogen

/-! ## Section 1: Molecular Parameter Derivation

Molecular (Z, N, e) = sum of atomic parameters.
Neutral molecules have e = Z (total proton count).
-/

-- H₂¹⁶O: Z = 2·H.Z + O.Z, N = 2·H.N + O16.N, e = Z (neutral)
theorem water_Z : 2 * hydrogenZ + oxygenZ = 10 := rfl
theorem water_N : 2 * protium_N + neutrons_O16 = 8 := rfl

noncomputable def water (x : ℝ) : ℝ := atomStateFn 10 8 10 x

-- D₂¹⁶O: N = 2·D.N + O16.N = 2+8 = 10
theorem heavyWater_N : 2 * deuterium_N + neutrons_O16 = 10 := rfl

noncomputable def heavyWater (x : ℝ) : ℝ := atomStateFn 10 10 10 x

-- HDO: N = H.N + D.N + O16.N = 0+1+8 = 9
theorem semiHeavyWater_N :
    protium_N + deuterium_N + neutrons_O16 = 9 := rfl

noncomputable def semiHeavyWater (x : ℝ) : ℝ := atomStateFn 10 9 10 x

-- T₂¹⁶O: N = 2·T.N + O16.N = 4+8 = 12
theorem tritiatedWater_N : 2 * tritium_N + neutrons_O16 = 12 := rfl

noncomputable def tritiatedWater (x : ℝ) : ℝ := atomStateFn 10 12 10 x

-- H₂¹⁸O: N = 2·H.N + O18.N = 0+10 = 10
theorem water_O18_N : 2 * protium_N + neutrons_O18 = 10 := rfl

noncomputable def water_O18 (x : ℝ) : ℝ := atomStateFn 10 10 10 x

/-! ## Section 2: Isotopologue Degeneracy

D₂¹⁶O and H₂¹⁸O have identical (Z,N,e) = (10,10,10) because
2·D.N + O16.N = 2·1 + 8 = 10 = 2·H.N + O18.N = 0 + 10.
-/

theorem D2O_eq_H2O18 : heavyWater = water_O18 := rfl

-- The algebraic reason: D.N + D.N + O16.N = H.N + H.N + O18.N
theorem isotopologue_degeneracy_reason :
    2 * deuterium_N + neutrons_O16 = 2 * protium_N + neutrons_O18 := rfl

theorem D2O_H2O18_degree : atomDegree 10 10 10 = 30 := rfl

/-! ## Section 3: Water Ions -/

-- H₃O⁺: Z = 3·H.Z + O.Z = 11, e = Z - 1 = 10
theorem hydronium_Z : 3 * hydrogenZ + oxygenZ = 11 := rfl

noncomputable def hydronium (x : ℝ) : ℝ := atomStateFn 11 8 10 x

-- OH⁻: Z = H.Z + O.Z = 9, e = Z + 1 = 10
theorem hydroxide_Z : hydrogenZ + oxygenZ = 9 := rfl

noncomputable def hydroxide (x : ℝ) : ℝ := atomStateFn 9 8 10 x

noncomputable def waterCation (x : ℝ) : ℝ := atomStateFn 10 8 9 x
noncomputable def waterAnion (x : ℝ) : ℝ := atomStateFn 10 8 11 x
noncomputable def deuteratedHydroxide (x : ℝ) : ℝ := atomStateFn 9 9 10 x

/-! ## Section 4: Dioxygen Molecule -/

-- O₂: Z = 2·O.Z = 16, N = 2·O16.N = 16
theorem dioxygen_Z : 2 * oxygenZ = 16 := rfl
theorem dioxygen_N : 2 * neutrons_O16 = 16 := rfl

noncomputable def dioxygen (x : ℝ) : ℝ := atomStateFn 16 16 16 x

-- ¹⁶O¹⁸O: N = O16.N + O18.N = 8+10 = 18
theorem dioxygen_16_18_N : neutrons_O16 + neutrons_O18 = 18 := rfl

noncomputable def dioxygen_16_18 (x : ℝ) : ℝ := atomStateFn 16 18 16 x

-- ¹⁸O₂: N = 2·O18.N = 20
theorem dioxygen_18_N : 2 * neutrons_O18 = 20 := rfl

noncomputable def dioxygen_18 (x : ℝ) : ℝ := atomStateFn 16 20 16 x

noncomputable def superoxide (x : ℝ) : ℝ := atomStateFn 16 16 17 x
noncomputable def peroxide (x : ℝ) : ℝ := atomStateFn 16 16 18 x

/-! ## Section 5: Hydrogen Peroxide -/

-- H₂O₂: Z = 2·H.Z + 2·O.Z = 18, N = 2·O16.N = 16
theorem hydrogenPeroxide_Z : 2 * hydrogenZ + 2 * oxygenZ = 18 := rfl
theorem hydrogenPeroxide_N : 2 * neutrons_O16 = 16 := rfl

noncomputable def hydrogenPeroxide (x : ℝ) : ℝ := atomStateFn 18 16 18 x

/-! ## Section 6: Factored Form Identities -/

theorem water_eq (x : ℝ) :
    water x = x ^ 10 * (1 + x) ^ 8 * (1 + ψ * x) ^ 10 := rfl

theorem heavyWater_eq (x : ℝ) :
    heavyWater x = x ^ 10 * (1 + x) ^ 10 * (1 + ψ * x) ^ 10 := rfl

theorem dioxygen_eq (x : ℝ) :
    dioxygen x = x ^ 16 * (1 + x) ^ 16 * (1 + ψ * x) ^ 16 := rfl

theorem hydroxide_eq (x : ℝ) :
    hydroxide x = x ^ 9 * (1 + x) ^ 8 * (1 + ψ * x) ^ 10 := rfl

theorem hydrogenPeroxide_eq (x : ℝ) :
    hydrogenPeroxide x = x ^ 18 * (1 + x) ^ 16 * (1 + ψ * x) ^ 18 := rfl

/-! ## Section 7: Degree Structure -/

-- Water family
theorem degree_water : atomDegree 10 8 10 = 28 := rfl
theorem degree_heavyWater : atomDegree 10 10 10 = 30 := rfl
theorem degree_semiHeavyWater : atomDegree 10 9 10 = 29 := rfl
theorem degree_tritiatedWater : atomDegree 10 12 10 = 32 := rfl

-- Water ions
theorem degree_hydronium : atomDegree 11 8 10 = 29 := rfl
theorem degree_hydroxide : atomDegree 9 8 10 = 27 := rfl
theorem degree_waterCation : atomDegree 10 8 9 = 27 := rfl
theorem degree_waterAnion : atomDegree 10 8 11 = 29 := rfl

-- Dioxygen
theorem degree_dioxygen : atomDegree 16 16 16 = 48 := rfl
theorem degree_dioxygen_16_18 : atomDegree 16 18 16 = 50 := rfl
theorem degree_dioxygen_18 : atomDegree 16 20 16 = 52 := rfl
theorem degree_superoxide : atomDegree 16 16 17 = 49 := rfl
theorem degree_peroxide : atomDegree 16 16 18 = 50 := rfl

-- Hydrogen peroxide
theorem degree_hydrogenPeroxide : atomDegree 18 16 18 = 52 := rfl

/-! ## Section 8: Water Autoionization Degree Conservation

H₂O + H₂O → H₃O⁺ + OH⁻
Total degree is conserved: 28 + 28 = 29 + 27 = 56
-/

theorem autoionization_degree_conservation :
    atomDegree 10 8 10 + atomDegree 10 8 10 =
    atomDegree 11 8 10 + atomDegree 9 8 10 := rfl

-- Total particle count is conserved
theorem autoionization_proton_conservation : 10 + 10 = 11 + 9 := rfl
theorem autoionization_neutron_conservation : (8 : ℕ) + 8 = 8 + 8 := rfl
theorem autoionization_electron_conservation : (10 : ℕ) + 10 = 10 + 10 := rfl

/-! ## Section 9: Magic Number Connections

O-16 nuclei carry Z=8 and N=8, both magic numbers.
In water H₂O, the neutron count N=8 inherits this magic structure.
-/

-- Water's neutron count is a magic number
theorem water_neutron_count_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = 8 :=
  ⟨1, by omega, rfl⟩

-- Dioxygen has doubly-magic nucleon counts in each oxygen
theorem dioxygen_doubly_magic_per_nucleus :
    Nuclear.nuclearMagic 1 = 8 ∧ Nuclear.nuclearMagic 1 = 8 := ⟨rfl, rfl⟩

-- ¹⁶O¹⁸O: dioxygen isotopologue has N=18 = shellCapacity 3
theorem dioxygen_16_18_neutron_shell :
    Nuclear.shellCapacity 3 = 18 := rfl

/-! ## Section 10: Electron Shell Structure -/

-- Water has 10 electrons = 1s² 2s² 2p⁶ (isoelectronic with Ne)
theorem water_electron_count :
    Nuclear.shellCapacity 1 + Nuclear.shellCapacity 2 = 10 := rfl

-- Water is isoelectronic with neon (all n≤2 shells filled)
theorem water_isoelectronic_neon :
    Nuclear.Subshell.maxElectrons ⟨1, 0⟩ +  -- 1s: 2
    Nuclear.Subshell.maxElectrons ⟨2, 0⟩ +  -- 2s: 2
    Nuclear.Subshell.maxElectrons ⟨2, 1⟩    -- 2p: 6
    = 10 := rfl

-- Hydroxide OH⁻ is also isoelectronic with neon (10 electrons)
theorem hydroxide_isoelectronic_neon :
    atomDegree 9 8 10 - 9 - 8 = 10 := rfl

/-! ## Section 11: Peroxide Degree Connection

¹⁶O¹⁸O and O₂²⁻ have the same degree 50 (another isotopologue degeneracy).
-/

theorem dioxygen_16_18_eq_peroxide_degree :
    atomDegree 16 18 16 = atomDegree 16 16 18 := rfl

/-! ## Section 12: Water Achieves Closed Shell

H₂O has e=10 = closedShellElectronCount(2), so it is a closed-shell molecule.
The constituent atoms H (e=1) and O (e=8) are not closed shell.
Water formation thus represents a transition from non-closed to closed shell.
-/

open Helium in
theorem water_is_closed_shell : isClosedShell 10 := neon_is_closed_shell

-- O has 2 electron vacancies, exactly matching 2 hydrogen atoms
open Helium in
theorem water_stoichiometry :
    closedShellElectronCount 2 - 8 = 2 ∧
    closedShellElectronCount 2 = 1 + 1 + 8 := by
  constructor <;> decide

-- O₂ is NOT closed shell (e=16)
open Helium in
private theorem closedShell_ge_28_of_ge_3 (n : ℕ) (hn : n ≥ 3) :
    closedShellElectronCount n ≥ 28 := by
  have h3 : closedShellElectronCount 3 = 28 := by decide
  have hmono := closedShellElectronCount_strict_mono
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k + 1 = 3
    · rw [hk, h3]
    · have hk3 : k ≥ 3 := by omega
      have := ih hk3
      have := hmono k (by omega)
      omega

open Helium in
theorem dioxygen_not_closed_shell : ¬ isClosedShell 16 := by
  intro ⟨n, hn, heq⟩
  by_cases h1 : n = 1
  · subst h1; simp [closedShell_1] at heq
  · by_cases h2 : n = 2
    · subst h2; simp [closedShell_2] at heq
    · have := closedShell_ge_28_of_ge_3 n (by omega)
      omega

-- Vacancy decrease: 2H₂ + O₂ → 2H₂O reduces total molecular vacancy
open Helium in
theorem water_formation_vacancy_decrease :
    let lhs_vacancy := 2 * (closedShellElectronCount 1 - 2) +
                        (closedShellElectronCount 3 - 16)
    let rhs_vacancy := 2 * (closedShellElectronCount 2 - 10)
    lhs_vacancy > rhs_vacancy := by
  decide

-- Atomic vacancy formulation: 4H + 2O atoms have 8 total vacancies
open Helium in
theorem water_atom_vacancy_decrease :
    4 * (closedShellElectronCount 1 - 1) + 2 * (closedShellElectronCount 2 - 8) = 8 ∧
    closedShellElectronCount 2 - 10 = 0 := by
  constructor <;> decide

-- The reaction 2H₂O → 2H₂ + O₂ increases vacancy (reverse direction unfavorable)
open Helium in
theorem water_decomposition_vacancy_increase :
    let product_vacancy := 2 * (closedShellElectronCount 1 - 2) +
                           (closedShellElectronCount 3 - 16)
    let reactant_vacancy := 2 * (closedShellElectronCount 2 - 10)
    product_vacancy > reactant_vacancy := by
  decide

/-! ## Section 13: Summary -/

theorem water_molecule_classification :
    -- Water family degrees
    atomDegree 10 8 10 = 28 ∧   -- H₂O
    atomDegree 10 9 10 = 29 ∧   -- HDO
    atomDegree 10 10 10 = 30 ∧  -- D₂O = H₂¹⁸O
    atomDegree 10 12 10 = 32 ∧  -- T₂O
    -- Dioxygen degrees
    atomDegree 16 16 16 = 48 ∧  -- O₂
    atomDegree 16 18 16 = 50 ∧  -- ¹⁶O¹⁸O
    -- Autoionization conservation
    atomDegree 10 8 10 + atomDegree 10 8 10 =
      atomDegree 11 8 10 + atomDegree 9 8 10 ∧
    -- Isotopologue degeneracy
    atomDegree 10 10 10 = atomDegree 10 10 10 ∧
    -- Peroxide degree degeneracy
    atomDegree 16 18 16 = atomDegree 16 16 18 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.Water

namespace FUST.DiscreteTag
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Oxygen

def waterZ_t : DTagged .protonNum := scaleZ 2 hydrogenZ_t + oxygenZ_t
def hydroniumZ_t : DTagged .protonNum := scaleZ 3 hydrogenZ_t + oxygenZ_t
def hydroxideZ_t : DTagged .protonNum := hydrogenZ_t + oxygenZ_t
def H2O2Z_t : DTagged .protonNum := scaleZ 2 hydrogenZ_t + scaleZ 2 oxygenZ_t

def waterDeg_t : DTagged .degree := mkDegree waterZ_t O16N_t waterZ_t
def heavyWaterDeg_t : DTagged .degree := mkDegree waterZ_t ⟨10⟩ waterZ_t
def hydroniumDeg_t : DTagged .degree := mkDegree hydroniumZ_t ⟨8⟩ waterZ_t
def hydroxideDeg_t : DTagged .degree := mkDegree hydroxideZ_t ⟨8⟩ waterZ_t

theorem waterZ_t_val : waterZ_t.val = 10 := rfl
theorem hydroniumZ_t_val : hydroniumZ_t.val = 11 := rfl
theorem hydroxideZ_t_val : hydroxideZ_t.val = 9 := rfl
theorem H2O2Z_t_val : H2O2Z_t.val = 18 := rfl
theorem waterDeg_t_val : waterDeg_t.val = 28 := rfl
theorem heavyWaterDeg_t_val : heavyWaterDeg_t.val = 30 := rfl
theorem hydroniumDeg_t_val : hydroniumDeg_t.val = 29 := rfl
theorem hydroxideDeg_t_val : hydroxideDeg_t.val = 27 := rfl

-- H₂O = 2H + O
theorem water_Z_tagged : waterZ_t = scaleZ 2 hydrogenZ_t + oxygenZ_t := rfl

-- H₃O⁺ = 3H + O
theorem hydronium_Z_tagged : hydroniumZ_t = scaleZ 3 hydrogenZ_t + oxygenZ_t := rfl

-- OH⁻ = H + O
theorem hydroxide_Z_tagged : hydroxideZ_t = hydrogenZ_t + oxygenZ_t := rfl

-- H₂O₂ = 2H + 2O
theorem H2O2_Z_tagged : H2O2Z_t = scaleZ 2 hydrogenZ_t + scaleZ 2 oxygenZ_t := rfl

-- Autoionization: 2·H₂O = H₃O⁺ + OH⁻
theorem autoionization_deg_tagged :
    waterDeg_t + waterDeg_t = hydroniumDeg_t + hydroxideDeg_t := rfl

-- Degree construction consistency
theorem water_deg_consistency :
    mkDegree waterZ_t O16N_t waterZ_t = waterDeg_t := rfl

end FUST.DiscreteTag
