/-
Sulfur Atom from D-operator Kernel Structure

Sulfur Z = 16 = closedShellElectronCount(2) + shellCapacity(2) - 2.
Configuration: 1s² 2s² 2p⁶ 3s² 3p⁴ (same group as oxygen).
S-32 (Z=16, N=16) is the most abundant isotope.
-/

import FUST.Chemistry.PhosphorusAtom

namespace FUST.Chemistry.Sulfur

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen

/-! ## Section 1: Sulfur Parameters

sulfurZ = 16 = oxygenZ + shellCapacity(2) = 8 + 8 = 16.
Oxygen and sulfur are Group VIA homologues.
-/

abbrev sulfurZ : ℕ := 16

-- S is in the same group as O, one period below
theorem sulfurZ_from_oxygen :
    oxygenZ + Nuclear.shellCapacity 2 = sulfurZ := rfl

-- Shell filling: 1s² 2s² 2p⁶ 3s² 3p⁴
theorem sulfurZ_shell_filling :
    Nuclear.Subshell.maxElectrons ⟨1, 0⟩ +  -- 1s: 2
    Nuclear.Subshell.maxElectrons ⟨2, 0⟩ +  -- 2s: 2
    Nuclear.Subshell.maxElectrons ⟨2, 1⟩ +  -- 2p: 6
    Nuclear.Subshell.maxElectrons ⟨3, 0⟩ +  -- 3s: 2
    4 = sulfurZ                               -- 3p: 4 of 6
    := rfl

-- S-32 (most abundant): N = 16
def neutrons (A : ℕ) : ℕ := A - sulfurZ
abbrev neutrons_S32 : ℕ := neutrons 32
abbrev neutrons_S33 : ℕ := neutrons 33
abbrev neutrons_S34 : ℕ := neutrons 34

theorem neutrons_S32_eq : neutrons_S32 = 16 := rfl
theorem neutrons_S33_eq : neutrons_S33 = 17 := rfl
theorem neutrons_S34_eq : neutrons_S34 = 18 := rfl

-- S-32 is a symmetric nucleus: Z = N
theorem sulfur32_symmetric : sulfurZ = neutrons_S32 := rfl

/-! ## Section 2: Sulfur Species State Functions -/

noncomputable def sulfur32Ion (x : ℝ) : ℝ := atomStateFn 16 16 0 x
noncomputable def sulfur32Atom (x : ℝ) : ℝ := atomStateFn 16 16 16 x
noncomputable def sulfideAnion (x : ℝ) : ℝ := atomStateFn 16 16 18 x

theorem sulfur32Atom_eq (x : ℝ) :
    sulfur32Atom x = x ^ 16 * (1 + x) ^ 16 * (1 + ψ * x) ^ 16 := rfl

/-! ## Section 3: Degree Structure -/

theorem degree_sulfur32Ion : atomDegree 16 16 0 = 32 := rfl
theorem degree_sulfur32Atom : atomDegree 16 16 16 = 48 := rfl
theorem degree_sulfideAnion : atomDegree 16 16 18 = 50 := rfl

-- O-S homology: both have valence 2 to closed shell
theorem oxygen_sulfur_valence :
    closedShellElectronCount 2 - oxygenZ = 2 ∧
    closedShellElectronCount 3 - sulfurZ = 12 := by decide

-- Sulfide S²⁻ (e=18) = shellCapacity(3) = closed third shell
theorem sulfide_electron_shell :
    Nuclear.shellCapacity 3 = 18 := rfl

/-! ## Section 4: Mass Number -/

theorem sulfur32_mass_number : sulfurZ + neutrons_S32 = 32 := rfl
theorem sulfur33_mass_number : sulfurZ + neutrons_S33 = 33 := rfl
theorem sulfur34_mass_number : sulfurZ + neutrons_S34 = 34 := rfl

/-! ## Section 5: Summary -/

theorem sulfur_classification :
    sulfurZ = 16 ∧
    oxygenZ + Nuclear.shellCapacity 2 = sulfurZ ∧
    sulfurZ = neutrons_S32 ∧
    (∀ N e, atomDegree 16 N e > 2) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Sulfur

namespace FUST.DiscreteTag
open FUST.Chemistry.Sulfur

def sulfurZ_t : DTagged .protonNum := ⟨sulfurZ⟩
def S32N_t : DTagged .neutronNum := ⟨neutrons_S32⟩

theorem sulfurZ_t_val : sulfurZ_t.val = 16 := rfl
theorem S32N_t_val : S32N_t.val = 16 := rfl

-- O + shellCapacity(2) = S
theorem oxygen_plus_shell2_eq_sulfur :
    oxygenZ_t + ⟨Nuclear.shellCapacity 2⟩ = sulfurZ_t := rfl

end FUST.DiscreteTag
