/-
Carbon Molecules from the Multiplicative State Function Model

Molecular state function g(x) = x^Z · (1+x)^N · (1+ψx)^e.

CH₄ (methane): Z=10, N=6, e=10 — closed shell (isoelectronic with H₂O and Ne).
CO₂ (carbon dioxide): Z=22, N=22, e=22 — triply symmetric (Z=N=e).
CO (carbon monoxide): Z=14, N=14, e=14 — symmetric (Z=N=e).
-/

import FUST.DifferenceOperators
import FUST.Physics.Nuclear
import FUST.Chemistry.CarbonIsotopes
import FUST.Chemistry.DihydrogenMolecules
import FUST.Chemistry.WaterMolecules

namespace FUST.Chemistry.CarbonMol

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Dihydrogen
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

theorem degree_methane : atomDegree 10 6 10 = 26 := rfl
theorem degree_CO2 : atomDegree 22 22 22 = 66 := rfl
theorem degree_CO : atomDegree 14 14 14 = 42 := rfl

-- CO₂ degree = 3 × 22 = 66 (triple symmetry)
-- CO degree = 3 × 14 = 42

/-! ## Section 5: Combustion: CH₄ + 2O₂ → CO₂ + 2H₂O -/

-- Particle conservation
theorem combustion_Z_conservation :
    (carbonZ + 4 * hydrogenZ) + 2 * (2 * oxygenZ) =
    (carbonZ + 2 * oxygenZ) + 2 * (2 * hydrogenZ + oxygenZ) := rfl

theorem combustion_N_conservation :
    (neutrons_C12 + 4 * protium_N) + 2 * (2 * neutrons_O16) =
    (neutrons_C12 + 2 * neutrons_O16) + 2 * (2 * protium_N + neutrons_O16) := rfl

-- Degree conservation
theorem combustion_degree_conservation :
    atomDegree 10 6 10 + 2 * atomDegree 16 16 16 =
    atomDegree 22 22 22 + 2 * atomDegree 10 8 10 := rfl

-- Vacancy analysis: O₂ is not closed shell, so reactants have vacancy
-- CH₄(vac=0) + 2·O₂(vac=12 each) → CO₂(vac=6) + 2·H₂O(vac=0)
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

theorem degree_ethane : atomDegree 18 12 18 = 48 := rfl
theorem degree_ethylene : atomDegree 16 12 16 = 44 := rfl
theorem degree_acetylene : atomDegree 14 12 14 = 40 := rfl

-- Dehydrogenation degree pattern: each H₂ removal decreases degree by 4
theorem dehydrogenation_pattern :
    atomDegree 18 12 18 - atomDegree 16 12 16 = 4 ∧
    atomDegree 16 12 16 - atomDegree 14 12 14 = 4 := ⟨rfl, rfl⟩

/-! ## Section 7: CH₄ and H₂O Isoelectronic Relationship -/

-- Both methane and water are closed shell with e=10
theorem methane_water_isoelectronic :
    carbonZ + 4 * hydrogenZ = 2 * hydrogenZ + oxygenZ := rfl

-- But they differ in neutron count
theorem methane_water_neutron_diff :
    neutrons_C12 + 4 * protium_N ≠ 2 * protium_N + neutrons_O16 := by decide

theorem degree_methane_vs_water :
    atomDegree 10 6 10 = 26 ∧ atomDegree 10 8 10 = 28 := ⟨rfl, rfl⟩

/-! ## Section 8: Summary -/

theorem carbon_molecule_classification :
    -- CH₄ is closed shell
    isClosedShell 10 ∧
    -- Carbon valence = 4
    closedShellElectronCount 2 - carbonZ = 4 ∧
    -- CO₂ is triply symmetric (Z=N=e=22)
    carbonZ + 2 * oxygenZ = neutrons_C12 + 2 * neutrons_O16 ∧
    -- CO is triply symmetric (Z=N=e=14)
    carbonZ + oxygenZ = neutrons_C12 + neutrons_O16 ∧
    -- Combustion degree conservation
    atomDegree 10 6 10 + 2 * atomDegree 16 16 16 =
      atomDegree 22 22 22 + 2 * atomDegree 10 8 10 ∧
    -- CH₄ and H₂O are isoelectronic
    carbonZ + 4 * hydrogenZ = 2 * hydrogenZ + oxygenZ := by
  exact ⟨neon_is_closed_shell, by decide, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.CarbonMol

namespace FUST.DiscreteTag
open FUST.Chemistry.Carbon FUST.Chemistry.Dihydrogen FUST.Chemistry.Oxygen

def methaneZ_t : DTagged .protonNum := carbonZ_t + scaleZ 4 hydrogenZ_t
def CO2Z_t : DTagged .protonNum := carbonZ_t + scaleZ 2 oxygenZ_t
def COZ_t : DTagged .protonNum := carbonZ_t + oxygenZ_t
def dioxygenZ_t : DTagged .protonNum := scaleZ 2 oxygenZ_t
def ethaneZ_t : DTagged .protonNum := scaleZ 2 carbonZ_t + scaleZ 6 hydrogenZ_t
def ethyleneZ_t : DTagged .protonNum := scaleZ 2 carbonZ_t + scaleZ 4 hydrogenZ_t
def acetyleneZ_t : DTagged .protonNum := scaleZ 2 carbonZ_t + scaleZ 2 hydrogenZ_t

def methaneDeg_t : DTagged .degree := mkDegree methaneZ_t C12N_t methaneZ_t
def CO2Deg_t : DTagged .degree := mkDegree CO2Z_t ⟨22⟩ CO2Z_t
def CODeg_t : DTagged .degree := mkDegree COZ_t ⟨14⟩ COZ_t
def dioxygenDeg_t : DTagged .degree := mkDegree dioxygenZ_t ⟨16⟩ dioxygenZ_t
def dehydrogenationDeltaDeg_t : DTagged .deltaDeg :=
  ⟨atomDegree 18 12 18 - atomDegree 16 12 16⟩

theorem methaneZ_t_val : methaneZ_t.val = 10 := rfl
theorem CO2Z_t_val : CO2Z_t.val = 22 := rfl
theorem COZ_t_val : COZ_t.val = 14 := rfl
theorem dioxygenZ_t_val : dioxygenZ_t.val = 16 := rfl
theorem ethaneZ_t_val : ethaneZ_t.val = 18 := rfl
theorem ethyleneZ_t_val : ethyleneZ_t.val = 16 := rfl
theorem acetyleneZ_t_val : acetyleneZ_t.val = 14 := rfl
theorem methaneDeg_t_val : methaneDeg_t.val = 26 := rfl
theorem CO2Deg_t_val : CO2Deg_t.val = 66 := rfl
theorem CODeg_t_val : CODeg_t.val = 42 := rfl
theorem dioxygenDeg_t_val : dioxygenDeg_t.val = 48 := rfl
theorem dehydrogenationDeltaDeg_t_val : dehydrogenationDeltaDeg_t.val = 4 := rfl

-- CH₄ = C + 4H
theorem methane_Z_tagged : methaneZ_t = carbonZ_t + scaleZ 4 hydrogenZ_t := rfl
-- CO₂ = C + 2O
theorem CO2_Z_tagged : CO2Z_t = carbonZ_t + scaleZ 2 oxygenZ_t := rfl
-- CO = C + O
theorem CO_Z_tagged : COZ_t = carbonZ_t + oxygenZ_t := rfl
-- O₂ = 2O
theorem dioxygen_Z_tagged : dioxygenZ_t = scaleZ 2 oxygenZ_t := rfl

-- CO₂ triple symmetry (Z = N = e → deg = 3Z)
theorem CO2_deg_triple : CO2Deg_t = ⟨3 * CO2Z_t.val⟩ := rfl
-- CO triple symmetry
theorem CO_deg_triple : CODeg_t = ⟨3 * COZ_t.val⟩ := rfl

-- CH₄ + 2O₂ → CO₂ + 2H₂O
theorem combustion_deg_conservation :
    methaneDeg_t.val + 2 * dioxygenDeg_t.val =
    CO2Deg_t.val + 2 * waterDeg_t.val := rfl

-- Dehydrogenation per H₂ = 4
theorem dehydrogenation_deltaDeg_tagged : dehydrogenationDeltaDeg_t = ⟨4⟩ := rfl

-- Degree construction consistency
theorem methane_deg_consistency :
    mkDegree methaneZ_t C12N_t methaneZ_t = methaneDeg_t := rfl
theorem CO2_deg_consistency :
    mkDegree CO2Z_t ⟨22⟩ CO2Z_t = CO2Deg_t := rfl
theorem CO_deg_consistency :
    mkDegree COZ_t ⟨14⟩ COZ_t = CODeg_t := rfl
theorem dioxygen_deg_consistency :
    mkDegree dioxygenZ_t ⟨16⟩ dioxygenZ_t = dioxygenDeg_t := rfl

end FUST.DiscreteTag
