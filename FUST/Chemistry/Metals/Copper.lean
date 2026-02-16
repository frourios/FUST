/-
Copper from D-operator Kernel Structure

Copper Z = 29 = nuclearMagic(3) + hydrogenZ = 28 + 1.
Configuration: [Ar] 3d¹⁰ 4s¹ (anomalous — filled d-shell).
Cu-63 (Z=29, N=34): most abundant isotope.
Filled 3d shell (d-vacancy = 0) explains low hydrogen embrittlement susceptibility.
-/

import FUST.Chemistry.Metals.Nickel

namespace FUST.Chemistry.Copper

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Iron
open FUST.Chemistry.Nickel FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen

/-! ## Section 1: Copper Parameters

copperZ = 29 = nuclearMagic(3) + 1 = nickelZ + hydrogenZ.
Aufbau anomaly: [Ar] 3d¹⁰ 4s¹ (not 3d⁹ 4s²). Filled 3d shell.
-/

abbrev copperZ : ℕ := 29

theorem copperZ_from_nickel :
    nickelZ + hydrogenZ = copperZ := rfl

theorem copperZ_from_magic :
    Nuclear.nuclearMagic 3 + hydrogenZ = copperZ := rfl

-- [Ar] 3d¹⁰ 4s¹ (anomalous: full d-shell preferred over d⁹s²)
abbrev copper_3d_electrons : ℕ := 10

theorem copperZ_shell_filling :
    arCoreElectrons +
    copper_3d_electrons +  -- 3d: 10 of 10 (filled!)
    1 = copperZ            -- 4s: 1
    := rfl

-- 3d is completely filled: vacancy = 0
theorem copper_3d_filled :
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ = copper_3d_electrons := rfl

theorem copper_3d_vacancy :
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ - copper_3d_electrons = 0 := rfl

/-! ## Section 2: Copper Isotopes -/

def neutrons (A : ℕ) : ℕ := A - copperZ
abbrev neutrons_Cu63 : ℕ := neutrons 63
abbrev neutrons_Cu65 : ℕ := neutrons 65

theorem neutrons_Cu63_eq : neutrons_Cu63 = 34 := rfl
theorem neutrons_Cu65_eq : neutrons_Cu65 = 36 := rfl

/-! ## Section 3: State Functions -/

noncomputable def copper63Ion (x : ℝ) : ℝ := atomStateFn 29 34 0 x
noncomputable def copper63Atom (x : ℝ) : ℝ := atomStateFn 29 34 29 x

theorem copper63Atom_eq (x : ℝ) :
    copper63Atom x = x ^ 29 * (1 + x) ^ 34 * (1 + ψ * x) ^ 29 := rfl

/-! ## Section 4: Degree Structure -/

theorem degree_copper63Ion : atomDegree 29 34 0 = 63 := rfl
theorem degree_copper63Atom : atomDegree 29 34 29 = 92 := rfl

theorem copper_degree_exceeds_kerD6 (N e : ℕ) :
    atomDegree 29 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 5: Mass Numbers -/

theorem Cu63_mass_number : copperZ + neutrons_Cu63 = 63 := rfl
theorem Cu65_mass_number : copperZ + neutrons_Cu65 = 65 := rfl

/-! ## Section 6: Summary -/

theorem copper_classification :
    copperZ = 29 ∧
    Nuclear.nuclearMagic 3 + hydrogenZ = copperZ ∧
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ - copper_3d_electrons = 0 ∧
    (∀ N e, atomDegree 29 N e > 2) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Copper

namespace FUST.DiscreteTag
open FUST.Chemistry.Copper

def copperZ_t : DTagged .protonNum := ⟨copperZ⟩
def Cu63N_t : DTagged .neutronNum := ⟨neutrons_Cu63⟩

def copperDeg_t : DTagged .degree := mkDegree copperZ_t Cu63N_t copperZ_t

theorem copperZ_t_val : copperZ_t.val = 29 := rfl
theorem Cu63N_t_val : Cu63N_t.val = 34 := rfl
theorem copperDeg_t_val : copperDeg_t.val = 92 := rfl

-- Cu Z = Ni Z + H Z
theorem copperZ_eq_nickel_plus_H :
    copperZ_t = nickelZ_t + hydrogenZ_t := rfl

-- Degree construction consistency
theorem copper_deg_consistency :
    mkDegree copperZ_t Cu63N_t copperZ_t = copperDeg_t := rfl

end FUST.DiscreteTag
