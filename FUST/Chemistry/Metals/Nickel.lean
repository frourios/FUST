/-
Nickel from D-operator Kernel Structure

Nickel Z = 28 = nuclearMagic(3) — proton number itself is a magic number.
Configuration: [Ar] 3d⁸ 4s².
Ni-58 (Z=28, N=30): most abundant isotope. N=30 = Fe-56.N.
-/

import FUST.Chemistry.Metals.Iron

namespace FUST.Chemistry.Nickel

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Iron
open FUST.Chemistry.Helium FUST.Chemistry.Dihydrogen

/-! ## Section 1: Nickel Parameters

nickelZ = 28 = nuclearMagic(3). Aufbau: [Ar] 3d⁸ 4s².
-/

abbrev nickelZ : ℕ := 28

theorem nickelZ_is_magic :
    ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = nickelZ := ⟨3, by omega, rfl⟩

theorem nickelZ_eq_magic3 : Nuclear.nuclearMagic 3 = nickelZ := rfl

-- [Ar] 3d⁸ 4s²
abbrev nickel_3d_electrons : ℕ := 8

theorem nickelZ_shell_filling :
    arCoreElectrons +
    Nuclear.Subshell.maxElectrons ⟨4, 0⟩ +  -- 4s: 2
    nickel_3d_electrons = nickelZ              -- 3d: 8 of 10
    := rfl

-- 3d vacancy = 10 - 8 = 2
theorem nickel_3d_vacancy :
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ - nickel_3d_electrons = 2 := rfl

/-! ## Section 2: Nickel Isotopes -/

def neutrons (A : ℕ) : ℕ := A - nickelZ
abbrev neutrons_Ni58 : ℕ := neutrons 58
abbrev neutrons_Ni60 : ℕ := neutrons 60

theorem neutrons_Ni58_eq : neutrons_Ni58 = 30 := rfl
theorem neutrons_Ni60_eq : neutrons_Ni60 = 32 := rfl

-- Fe-56 and Ni-58 share the same neutron count N=30
theorem iron_nickel_same_N : neutrons_Fe56 = neutrons_Ni58 := rfl

/-! ## Section 3: State Functions -/

noncomputable def nickel58Ion (x : ℝ) : ℝ := atomStateFn 28 30 0 x
noncomputable def nickel58Atom (x : ℝ) : ℝ := atomStateFn 28 30 28 x

theorem nickel58Atom_eq (x : ℝ) :
    nickel58Atom x = x ^ 28 * (1 + x) ^ 30 * (1 + ψ * x) ^ 28 := rfl

/-! ## Section 4: Degree Structure -/

theorem degree_nickel58Ion : atomDegree 28 30 0 = 58 := rfl
theorem degree_nickel58Atom : atomDegree 28 30 28 = 86 := rfl

theorem nickel_degree_exceeds_kerD6 (N e : ℕ) :
    atomDegree 28 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 5: Mass Numbers -/

theorem Ni58_mass_number : nickelZ + neutrons_Ni58 = 58 := rfl
theorem Ni60_mass_number : nickelZ + neutrons_Ni60 = 60 := rfl

/-! ## Section 6: Summary -/

theorem nickel_classification :
    nickelZ = 28 ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = nickelZ) ∧
    neutrons_Fe56 = neutrons_Ni58 ∧
    (∀ N e, atomDegree 28 N e > 2) := by
  refine ⟨rfl, ⟨3, by omega, rfl⟩, rfl, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Nickel

namespace FUST.DiscreteTag
open FUST.Chemistry.Nickel

def nickelZ_t : DTagged .protonNum := ⟨nickelZ⟩
def Ni58N_t : DTagged .neutronNum := ⟨neutrons_Ni58⟩

def nickelDeg_t : DTagged .degree := mkDegree nickelZ_t Ni58N_t nickelZ_t

theorem nickelZ_t_val : nickelZ_t.val = 28 := rfl
theorem Ni58N_t_val : Ni58N_t.val = 30 := rfl
theorem nickelDeg_t_val : nickelDeg_t.val = 86 := rfl

-- Ni Z is magic
theorem nickelZ_magic_tagged :
    nickelZ_t.val = Nuclear.nuclearMagic 3 := rfl

-- Fe-56 N = Ni-58 N
theorem iron_nickel_same_N_tagged : Fe56N_t = Ni58N_t := rfl

-- Degree construction consistency
theorem nickel_deg_consistency :
    mkDegree nickelZ_t Ni58N_t nickelZ_t = nickelDeg_t := rfl

end FUST.DiscreteTag
