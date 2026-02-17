/-
Carbon Molecules from the Multiplicative State Function Model

Molecular state function g(x) = x^Z · (1+x)^N · (1+ψx)^e.

CH₄ (methane): Z=10, N=6, e=10 -- closed shell (isoelectronic with H₂O and Ne).
CO₂ (carbon dioxide): Z=22, N=22, e=22 -- triply symmetric (Z=N=e).
CO (carbon monoxide): Z=14, N=14, e=14 -- symmetric (Z=N=e).
-/

import FUST.DifferenceOperators
import FUST.Physics.Nuclear
import FUST.Chemistry.CarbonIsotopes
import FUST.Chemistry.DihydrogenMolecules
import FUST.Chemistry.WaterMolecules

namespace FUST.Chemistry.CarbonMol

open FUST FUST.Dim FUST.Chemistry
open FUST.Chemistry.Oxygen FUST.Chemistry.Dihydrogen
open FUST.Chemistry.Carbon FUST.Chemistry.Helium

/-! ## Section 1: Methane (CH₄)

Z = C.Z + 4·H.Z = 6 + 4 = 10, N = C12.N + 4·H.N = 6, e = Z = 10.
CH₄ has e = 10 = closedShellElectronCount(2), same as H₂O and Ne.
-/

theorem methane_Z : carbonZ + 4 * hydrogenZ = 10 := rfl
theorem methane_N : neutrons_C12 + 4 * protium_N = 6 := rfl

noncomputable def methane (x : ℝ) : ℝ := atomStateFn 10 6 10 x

theorem methane_eq (x : ℝ) :
    methane x = x ^ 10 * (1 + x) ^ 6 * (1 + ψ * x) ^ 10 := rfl

-- CH₄ is closed shell (e=10), isoelectronic with H₂O and Ne
theorem methane_is_closed_shell : isClosedShell 10 := neon_is_closed_shell

-- Carbon valence = 4 explains methane stoichiometry
theorem methane_stoichiometry :
    closedShellElectronCount 2 - carbonZ = 4 ∧
    closedShellElectronCount 2 = carbonZ + 4 * hydrogenZ := by
  constructor <;> decide

/-! ## Section 2: Carbon Dioxide (CO₂)

Z = C.Z + 2·O.Z = 6 + 16 = 22, N = 6 + 2·8 = 22, e = 22.
CO₂ has the remarkable property Z = N = e = 22.
-/

theorem CO2_Z : carbonZ + 2 * oxygenZ = 22 := rfl
theorem CO2_N : neutrons_C12 + 2 * neutrons_O16 = 22 := rfl

noncomputable def carbonDioxide (x : ℝ) : ℝ := atomStateFn 22 22 22 x

-- CO₂ is triply symmetric: Z = N = e
theorem CO2_triple_symmetry :
    carbonZ + 2 * oxygenZ = neutrons_C12 + 2 * neutrons_O16 ∧
    carbonZ + 2 * oxygenZ = carbonZ + 2 * oxygenZ := ⟨rfl, rfl⟩

theorem CO2_eq (x : ℝ) :
    carbonDioxide x = x ^ 22 * (1 + x) ^ 22 * (1 + ψ * x) ^ 22 := rfl

-- CO₂ = unitCell^22
theorem CO2_eq_unitCell_pow (x : ℝ) :
    carbonDioxide x = unitCell x ^ 22 := by
  unfold carbonDioxide atomStateFn unitCell; ring

/-! ## Section 3: Carbon Monoxide (CO)

Z = C.Z + O.Z = 14, N = 6 + 8 = 14, e = 14.
CO has Z = N = e = 14. Like CO₂, it is triply symmetric.
-/

theorem CO_Z : carbonZ + oxygenZ = 14 := rfl
theorem CO_N : neutrons_C12 + neutrons_O16 = 14 := rfl

noncomputable def carbonMonoxide (x : ℝ) : ℝ := atomStateFn 14 14 14 x

theorem CO_triple_symmetry :
    carbonZ + oxygenZ = neutrons_C12 + neutrons_O16 ∧
    carbonZ + oxygenZ = carbonZ + oxygenZ := ⟨rfl, rfl⟩

theorem CO_eq (x : ℝ) :
    carbonMonoxide x = x ^ 14 * (1 + x) ^ 14 * (1 + ψ * x) ^ 14 := rfl

-- CO = unitCell^14
theorem CO_eq_unitCell_pow (x : ℝ) :
    carbonMonoxide x = unitCell x ^ 14 := by
  unfold carbonMonoxide atomStateFn unitCell; ring

/-! ## Section 4: Degree Structure -/

theorem degree_methane :
    (dimAtom 10 6 10).effectiveDegree = 271 := by decide
theorem degree_CO2 :
    (dimAtom 22 22 22).effectiveDegree = 727 := by decide
theorem degree_CO :
    (dimAtom 14 14 14).effectiveDegree = 463 := by decide

/-! ## Section 5: Combustion: CH₄ + 2O₂ → CO₂ + 2H₂O -/

-- Particle conservation
theorem combustion_Z_conservation :
    (carbonZ + 4 * hydrogenZ) + 2 * (2 * oxygenZ) =
    (carbonZ + 2 * oxygenZ) + 2 * (2 * hydrogenZ + oxygenZ) := rfl

theorem combustion_N_conservation :
    (neutrons_C12 + 4 * protium_N) + 2 * (2 * neutrons_O16) =
    (neutrons_C12 + 2 * neutrons_O16) +
      2 * (2 * protium_N + neutrons_O16) := rfl

-- EffectiveDegree conservation
theorem combustion_degree_conservation :
    (dimAtom 10 6 10).effectiveDegree +
      2 * (dimAtom 16 16 16).effectiveDegree =
    (dimAtom 22 22 22).effectiveDegree +
      2 * (dimAtom 10 8 10).effectiveDegree := by decide

-- Vacancy analysis: O₂ is not closed shell, so reactants have vacancy
theorem combustion_vacancy_decrease :
    let lhs_vacancy := (closedShellElectronCount 2 - 10) +
                        2 * (closedShellElectronCount 3 - 16)
    let rhs_vacancy := (closedShellElectronCount 3 - 22) +
                        2 * (closedShellElectronCount 2 - 10)
    lhs_vacancy > rhs_vacancy := by
  decide

/-! ## Section 6: Ethane, Ethylene, Acetylene -/

-- C₂H₆ (ethane): Z = 2·6 + 6 = 18, N = 12, e = 18
theorem ethane_Z : 2 * carbonZ + 6 * hydrogenZ = 18 := rfl
theorem ethane_N : 2 * neutrons_C12 + 6 * protium_N = 12 := rfl

noncomputable def ethane (x : ℝ) : ℝ := atomStateFn 18 12 18 x

-- C₂H₄ (ethylene): Z = 2·6 + 4 = 16, N = 12, e = 16
theorem ethylene_Z : 2 * carbonZ + 4 * hydrogenZ = 16 := rfl
theorem ethylene_N : 2 * neutrons_C12 + 4 * protium_N = 12 := rfl

noncomputable def ethylene (x : ℝ) : ℝ := atomStateFn 16 12 16 x

-- C₂H₂ (acetylene): Z = 2·6 + 2 = 14, N = 12, e = 14
theorem acetylene_Z : 2 * carbonZ + 2 * hydrogenZ = 14 := rfl
theorem acetylene_N : 2 * neutrons_C12 + 2 * protium_N = 12 := rfl

noncomputable def acetylene (x : ℝ) : ℝ := atomStateFn 14 12 14 x

theorem degree_ethane :
    (dimAtom 18 12 18).effectiveDegree = 505 := by decide
theorem degree_ethylene :
    (dimAtom 16 12 16).effectiveDegree = 469 := by decide
theorem degree_acetylene :
    (dimAtom 14 12 14).effectiveDegree = 433 := by decide

-- Dehydrogenation pattern: each H₂ removal decreases effectiveDegree by 36
theorem dehydrogenation_pattern :
    (dimAtom 18 12 18).effectiveDegree -
      (dimAtom 16 12 16).effectiveDegree = 36 ∧
    (dimAtom 16 12 16).effectiveDegree -
      (dimAtom 14 12 14).effectiveDegree = 36 := by decide

/-! ## Section 7: CH₄ and H₂O Isoelectronic Relationship -/

-- Both methane and water are closed shell with e=10
theorem methane_water_isoelectronic :
    carbonZ + 4 * hydrogenZ = 2 * hydrogenZ + oxygenZ := rfl

-- But they differ in neutron count
theorem methane_water_neutron_diff :
    neutrons_C12 + 4 * protium_N ≠
      2 * protium_N + neutrons_O16 := by decide

theorem degree_methane_vs_water :
    (dimAtom 10 6 10).effectiveDegree = 271 ∧
    (dimAtom 10 8 10).effectiveDegree = 301 := by decide

/-! ## Section 8: Summary -/

theorem carbon_molecule_classification :
    -- CH₄ is closed shell
    isClosedShell 10 ∧
    -- Carbon valence = 4
    closedShellElectronCount 2 - carbonZ = 4 ∧
    -- CO₂ is triply symmetric (Z=N=e=22)
    carbonZ + 2 * oxygenZ =
      neutrons_C12 + 2 * neutrons_O16 ∧
    -- CO is triply symmetric (Z=N=e=14)
    carbonZ + oxygenZ = neutrons_C12 + neutrons_O16 ∧
    -- Combustion effectiveDegree conservation
    (dimAtom 10 6 10).effectiveDegree +
      2 * (dimAtom 16 16 16).effectiveDegree =
      (dimAtom 22 22 22).effectiveDegree +
      2 * (dimAtom 10 8 10).effectiveDegree ∧
    -- CH₄ and H₂O are isoelectronic
    carbonZ + 4 * hydrogenZ =
      2 * hydrogenZ + oxygenZ := by
  exact ⟨neon_is_closed_shell, by decide, rfl, rfl,
    by decide, rfl⟩

end FUST.Chemistry.CarbonMol
