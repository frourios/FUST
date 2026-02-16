/-
Niobium from D-operator Kernel Structure

Niobium Z = 41 = 2 × nuclearMagic(2) + hydrogenZ = 40 + 1.
Configuration: [Kr] 4d⁴ 5s¹ (anomalous — half-filled proximity).
Nb-93 (Z=41, N=52): only stable isotope.
Nb-93 N = 52 = nuclearMagic(4) + spinDegeneracy = 50 + 2.
NbH is a superconductor — hydrogen strengthening metal.
-/

import FUST.Chemistry.Metals.Zirconium

namespace FUST.Chemistry.Niobium

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Iron
open FUST.Chemistry.Zirconium

/-! ## Section 1: Niobium Parameters

niobiumZ = 41 = zirconiumZ + hydrogenZ = 40 + 1.
Aufbau anomaly: [Kr] 4d⁴ 5s¹ (not 4d³ 5s²).
-/

abbrev niobiumZ : ℕ := 41

theorem niobiumZ_from_zirconium :
    zirconiumZ + hydrogenZ = niobiumZ := rfl

-- [Kr] 4d⁴ 5s¹ (anomalous: 5s has only 1 electron)
abbrev niobium_4d_electrons : ℕ := 4

theorem niobiumZ_shell_filling :
    krCoreElectrons +
    niobium_4d_electrons +  -- 4d: 4 of 10
    1 = niobiumZ             -- 5s: 1
    := rfl

-- 4d vacancy = 10 - 4 = 6
theorem niobium_4d_vacancy :
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - niobium_4d_electrons = 6 := rfl

/-! ## Section 2: Niobium Isotopes -/

def neutrons (A : ℕ) : ℕ := A - niobiumZ
abbrev neutrons_Nb93 : ℕ := neutrons 93

theorem neutrons_Nb93_eq : neutrons_Nb93 = 52 := rfl

-- N = nuclearMagic(4) + spinDegeneracy = 50 + 2
theorem Nb93_N_from_magic :
    Nuclear.nuclearMagic 4 + Nuclear.spinDegeneracy = neutrons_Nb93 := rfl

/-! ## Section 3: State Functions -/

noncomputable def niobium93Ion (x : ℝ) : ℝ := atomStateFn 41 52 0 x
noncomputable def niobium93Atom (x : ℝ) : ℝ := atomStateFn 41 52 41 x

theorem niobium93Atom_eq (x : ℝ) :
    niobium93Atom x = x ^ 41 * (1 + x) ^ 52 * (1 + ψ * x) ^ 41 := rfl

/-! ## Section 4: Degree Structure -/

theorem degree_niobium93Ion : atomDegree 41 52 0 = 93 := rfl
theorem degree_niobium93Atom : atomDegree 41 52 41 = 134 := rfl

theorem niobium_degree_exceeds_kerD6 (N e : ℕ) :
    atomDegree 41 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 5: Mass Number -/

theorem Nb93_mass_number : niobiumZ + neutrons_Nb93 = 93 := rfl

/-! ## Section 6: Summary -/

theorem niobium_classification :
    niobiumZ = 41 ∧
    zirconiumZ + hydrogenZ = niobiumZ ∧
    Nuclear.nuclearMagic 4 + Nuclear.spinDegeneracy = neutrons_Nb93 ∧
    (∀ N e, atomDegree 41 N e > 2) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Niobium

namespace FUST.DiscreteTag
open FUST.Chemistry.Niobium

def niobiumZ_t : DTagged .protonNum := ⟨niobiumZ⟩
def Nb93N_t : DTagged .neutronNum := ⟨neutrons_Nb93⟩

def niobiumDeg_t : DTagged .degree := mkDegree niobiumZ_t Nb93N_t niobiumZ_t

theorem niobiumZ_t_val : niobiumZ_t.val = 41 := rfl
theorem Nb93N_t_val : Nb93N_t.val = 52 := rfl
theorem niobiumDeg_t_val : niobiumDeg_t.val = 134 := rfl

-- Degree construction consistency
theorem niobium_deg_consistency :
    mkDegree niobiumZ_t Nb93N_t niobiumZ_t = niobiumDeg_t := rfl

end FUST.DiscreteTag
