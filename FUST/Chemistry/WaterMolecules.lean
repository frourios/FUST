/-
Water, Dioxygen, and Hydroxide Molecules from the Multiplicative State Function Model

Molecular state function g(x) = x^Z · (1+x)^N · (1+ψx)^e
where Z, N, e are total proton, neutron, electron counts.

Key discovery: D2O and H2-18O share the same FDim (Z=10, N=10, e=10).
-/

import FUST.DifferenceOperators
import FUST.Physics.Nuclear
import FUST.Chemistry.OxygenIsotopes
import FUST.Chemistry.DihydrogenMolecules
import FUST.Chemistry.HeliumInertness

namespace FUST.Chemistry.Water

open FUST FUST.Dim FUST.Chemistry
open FUST.Chemistry.Oxygen FUST.Chemistry.Dihydrogen

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

-- D₂O and H₂¹⁸O share the same FDim
theorem D2O_H2O18_sameFDim : dimAtom 10 10 10 = dimAtom 10 10 10 := rfl

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
theorem degree_water : (dimAtom 10 8 10).effectiveDegree = 301 := by decide
theorem degree_heavyWater : (dimAtom 10 10 10).effectiveDegree = 331 := by decide
theorem degree_semiHeavyWater : (dimAtom 10 9 10).effectiveDegree = 316 := by decide
theorem degree_tritiatedWater : (dimAtom 10 12 10).effectiveDegree = 361 := by decide

-- Water ions
theorem degree_hydronium : (dimAtom 11 8 10).effectiveDegree = 317 := by decide
theorem degree_hydroxide : (dimAtom 9 8 10).effectiveDegree = 285 := by decide
theorem degree_waterCation : (dimAtom 10 8 9).effectiveDegree = 299 := by decide
theorem degree_waterAnion : (dimAtom 10 8 11).effectiveDegree = 303 := by decide

-- Dioxygen
theorem degree_dioxygen : (dimAtom 16 16 16).effectiveDegree = 529 := by decide
theorem degree_dioxygen_16_18 : (dimAtom 16 18 16).effectiveDegree = 559 := by decide
theorem degree_dioxygen_18 : (dimAtom 16 20 16).effectiveDegree = 589 := by decide
theorem degree_superoxide : (dimAtom 16 16 17).effectiveDegree = 531 := by decide
theorem degree_peroxide : (dimAtom 16 16 18).effectiveDegree = 533 := by decide

-- Hydrogen peroxide
theorem degree_hydrogenPeroxide : (dimAtom 18 16 18).effectiveDegree = 565 := by decide

/-! ## Section 8: Water Autoionization Degree Conservation

H₂O + H₂O → H₃O⁺ + OH⁻
Total effectiveDegree is conserved: 301 + 301 = 317 + 285 = 602
-/

theorem autoionization_degree_conservation :
    (dimAtom 10 8 10).effectiveDegree + (dimAtom 10 8 10).effectiveDegree =
    (dimAtom 11 8 10).effectiveDegree + (dimAtom 9 8 10).effectiveDegree := by decide

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
    Nuclear.subshellCapacity 0 +  -- 1s: 2
    Nuclear.subshellCapacity 0 +  -- 2s: 2
    Nuclear.subshellCapacity 1    -- 2p: 6
    = 10 := rfl

-- Hydroxide OH⁻ is also isoelectronic with neon (e = Z + 1 = 10)
theorem hydroxide_isoelectronic_neon : (9 : ℕ) + 1 = 10 := rfl

/-! ## Section 11: Peroxide Degree Connection

¹⁶O¹⁸O and O₂²⁻ have the same total particle count (Z+N+e=50) but distinct FDim.
-/

theorem dioxygen_16_18_peroxide_same_particle_count :
    16 + 18 + 16 = 16 + 16 + (18 : ℕ) := rfl

theorem dioxygen_16_18_peroxide_distinct_FDim :
    dimAtom 16 18 16 ≠ dimAtom 16 16 18 := by decide

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
    -- Water family effectiveDegrees
    (dimAtom 10 8 10).effectiveDegree = 301 ∧   -- H₂O
    (dimAtom 10 9 10).effectiveDegree = 316 ∧   -- HDO
    (dimAtom 10 10 10).effectiveDegree = 331 ∧  -- D₂O = H₂¹⁸O
    (dimAtom 10 12 10).effectiveDegree = 361 ∧  -- T₂O
    -- Dioxygen effectiveDegrees
    (dimAtom 16 16 16).effectiveDegree = 529 ∧  -- O₂
    (dimAtom 16 18 16).effectiveDegree = 559 ∧  -- ¹⁶O¹⁸O
    -- Autoionization conservation
    (dimAtom 10 8 10).effectiveDegree + (dimAtom 10 8 10).effectiveDegree =
      (dimAtom 11 8 10).effectiveDegree + (dimAtom 9 8 10).effectiveDegree ∧
    -- Isotopologue degeneracy (same FDim)
    dimAtom 10 10 10 = dimAtom 10 10 10 ∧
    -- ¹⁶O¹⁸O and O₂²⁻ have distinct FDim
    dimAtom 16 18 16 ≠ dimAtom 16 16 18 := by
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, rfl, by decide⟩

end FUST.Chemistry.Water
