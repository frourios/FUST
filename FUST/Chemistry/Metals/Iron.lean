/-
Iron from D-operator Kernel Structure

Iron Z = 26 = nuclearMagic(3) - spinDegeneracy = 28 - 2.
Configuration: [Ar] 3d⁶ 4s² (period 4, Group VIII transition metal).
Fe-56 (Z=26, N=30): most abundant isotope.
Fe-56 neutral atom degree = 82 = nuclearMagic(5).
-/

import FUST.Chemistry.SulfurAtom

namespace FUST.Chemistry.Iron

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen

/-! ## Section 1: Iron Parameters

ironZ = 26 = nuclearMagic(3) - spinDegeneracy = 28 - 2.
Aufbau: 1s² 2s² 2p⁶ 3s² 3p⁶ 4s² 3d⁶.
-/

abbrev ironZ : ℕ := 26

theorem ironZ_from_magic :
    Nuclear.nuclearMagic 3 - Nuclear.spinDegeneracy = ironZ := rfl

-- Ar core (1s² 2s² 2p⁶ 3s² 3p⁶) = 18
abbrev arCoreElectrons : ℕ := 18

theorem arCore_eq :
    Nuclear.Subshell.maxElectrons ⟨1, 0⟩ +
    Nuclear.Subshell.maxElectrons ⟨2, 0⟩ +
    Nuclear.Subshell.maxElectrons ⟨2, 1⟩ +
    Nuclear.Subshell.maxElectrons ⟨3, 0⟩ +
    Nuclear.Subshell.maxElectrons ⟨3, 1⟩ = arCoreElectrons := rfl

-- [Ar] 3d⁶ 4s²
abbrev iron_3d_electrons : ℕ := 6

theorem ironZ_shell_filling :
    arCoreElectrons +
    Nuclear.Subshell.maxElectrons ⟨4, 0⟩ +  -- 4s: 2
    iron_3d_electrons = ironZ                 -- 3d: 6 of 10
    := rfl

-- 3d vacancy = 10 - 6 = 4
theorem iron_3d_vacancy :
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ - iron_3d_electrons = 4 := rfl

/-! ## Section 2: Iron Isotopes -/

def neutrons (A : ℕ) : ℕ := A - ironZ
abbrev neutrons_Fe54 : ℕ := neutrons 54
abbrev neutrons_Fe56 : ℕ := neutrons 56
abbrev neutrons_Fe57 : ℕ := neutrons 57
abbrev neutrons_Fe58 : ℕ := neutrons 58

theorem neutrons_Fe54_eq : neutrons_Fe54 = 28 := rfl
theorem neutrons_Fe56_eq : neutrons_Fe56 = 30 := rfl
theorem neutrons_Fe57_eq : neutrons_Fe57 = 31 := rfl
theorem neutrons_Fe58_eq : neutrons_Fe58 = 32 := rfl

-- Fe-54 has a magic neutron number N=28
theorem Fe54_neutron_magic :
    ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Fe54 := ⟨3, by omega, rfl⟩

/-! ## Section 3: State Functions -/

noncomputable def iron56Ion (x : ℝ) : ℝ := atomStateFn 26 30 0 x
noncomputable def iron56Atom (x : ℝ) : ℝ := atomStateFn 26 30 26 x

theorem iron56Atom_eq (x : ℝ) :
    iron56Atom x = x ^ 26 * (1 + x) ^ 30 * (1 + ψ * x) ^ 26 := rfl

/-! ## Section 4: Degree Structure -/

theorem degree_iron56Ion : atomDegree 26 30 0 = 56 := rfl
theorem degree_iron56Atom : atomDegree 26 30 26 = 82 := rfl

-- Fe-56 neutral atom degree = nuclearMagic(5) = 82
theorem iron56_deg_is_magic : atomDegree 26 30 26 = Nuclear.nuclearMagic 5 := rfl

theorem iron_degree_exceeds_kerD6 (N e : ℕ) :
    atomDegree 26 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 5: Mass Numbers -/

theorem Fe54_mass_number : ironZ + neutrons_Fe54 = 54 := rfl
theorem Fe56_mass_number : ironZ + neutrons_Fe56 = 56 := rfl
theorem Fe57_mass_number : ironZ + neutrons_Fe57 = 57 := rfl
theorem Fe58_mass_number : ironZ + neutrons_Fe58 = 58 := rfl

/-! ## Section 6: Summary -/

theorem iron_classification :
    ironZ = 26 ∧
    Nuclear.nuclearMagic 3 - Nuclear.spinDegeneracy = ironZ ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Fe54) ∧
    atomDegree 26 30 26 = Nuclear.nuclearMagic 5 ∧
    (∀ N e, atomDegree 26 N e > 2) := by
  refine ⟨rfl, rfl, ⟨3, by omega, rfl⟩, rfl, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Iron

namespace FUST.DiscreteTag
open FUST.Chemistry.Iron

def ironZ_t : DTagged .protonNum := ⟨ironZ⟩
def Fe56N_t : DTagged .neutronNum := ⟨neutrons_Fe56⟩
def Fe54N_t : DTagged .neutronNum := ⟨neutrons_Fe54⟩

def ironDeg_t : DTagged .degree := mkDegree ironZ_t Fe56N_t ironZ_t

theorem ironZ_t_val : ironZ_t.val = 26 := rfl
theorem Fe56N_t_val : Fe56N_t.val = 30 := rfl
theorem Fe54N_t_val : Fe54N_t.val = 28 := rfl
theorem ironDeg_t_val : ironDeg_t.val = 82 := rfl

-- Fe Z = nuclearMagic(3) - spinDeg
theorem ironZ_from_magic_tagged :
    ironZ_t = ⟨Nuclear.nuclearMagic 3⟩ - ⟨Nuclear.spinDegeneracy⟩ := rfl

-- Fe-56 degree = nuclearMagic(5)
theorem iron56_deg_magic_tagged :
    ironDeg_t.val = Nuclear.nuclearMagic 5 := rfl

-- Fe-54 N is magic
theorem Fe54N_is_magic : Fe54N_t.val = Nuclear.nuclearMagic 3 := rfl

-- Degree construction consistency
theorem iron_deg_consistency :
    mkDegree ironZ_t Fe56N_t ironZ_t = ironDeg_t := rfl

end FUST.DiscreteTag
