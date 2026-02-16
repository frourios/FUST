/-
Nitrogen Isotopes from D-operator Kernel Structure

State function g(x) = x^Z · (1+x)^N · (1+ψx)^e.
Nitrogen Z = closedShellElectronCount(1) + maxElectrons(2,0) + maxElectrons(2,1)/2 = 7.
N-14 (Z=N=7) is a symmetric nucleus. N-15 has magic neutron number N=8.
-/

import FUST.Chemistry.CarbonIsotopes
import FUST.Chemistry.DihydrogenMolecules

namespace FUST.Chemistry.Nitrogen

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Carbon
open FUST.Chemistry.Helium FUST.Chemistry.Dihydrogen

/-! ## Section 1: Nitrogen Parameters

nitrogenZ = closedShellElectronCount(1) + maxElectrons(⟨2,0⟩) + maxElectrons(⟨2,1⟩)/2
          = 2 + 2 + 3 = 7.
Half-filled 2p shell (3 of 6 electrons).
-/

abbrev nitrogenZ : ℕ := 7

-- Z derivation from shell structure
theorem nitrogenZ_derivation :
    closedShellElectronCount 1 +
    Nuclear.Subshell.maxElectrons ⟨2, 0⟩ +
    Nuclear.Subshell.maxElectrons ⟨2, 1⟩ / 2 = nitrogenZ := by decide

-- Neutron counts: N = A - Z
def neutrons (A : ℕ) : ℕ := A - nitrogenZ
abbrev neutrons_N14 : ℕ := neutrons 14
abbrev neutrons_N15 : ℕ := neutrons 15

theorem neutrons_N14_eq : neutrons_N14 = 7 := rfl
theorem neutrons_N15_eq : neutrons_N15 = 8 := rfl

-- N-14 is a symmetric nucleus: Z = N
theorem nitrogen14_symmetric : nitrogenZ = neutrons_N14 := rfl

-- N-15 has a magic neutron number
theorem nitrogen15_neutron_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_N15 :=
  ⟨1, by omega, rfl⟩

/-! ## Section 2: Nitrogen Species State Functions -/

noncomputable def nitrogen14Ion (x : ℝ) : ℝ := atomStateFn 7 7 0 x
noncomputable def nitrogen15Ion (x : ℝ) : ℝ := atomStateFn 7 8 0 x
noncomputable def nitrogen14Atom (x : ℝ) : ℝ := atomStateFn 7 7 7 x
noncomputable def nitrogen15Atom (x : ℝ) : ℝ := atomStateFn 7 8 7 x
noncomputable def nitrideAnion (x : ℝ) : ℝ := atomStateFn 7 7 10 x

theorem nitrogen14Atom_eq (x : ℝ) :
    nitrogen14Atom x = x ^ 7 * (1 + x) ^ 7 * (1 + ψ * x) ^ 7 := rfl

theorem nitrogen14Ion_eq (x : ℝ) :
    nitrogen14Ion x = x ^ 7 * (1 + x) ^ 7 := by
  unfold nitrogen14Ion atomStateFn; simp [pow_zero, mul_one]

/-! ## Section 3: Degree Structure -/

theorem degree_nitrogen14Ion : atomDegree 7 7 0 = 14 := rfl
theorem degree_nitrogen15Ion : atomDegree 7 8 0 = 15 := rfl
theorem degree_nitrogen14Atom : atomDegree 7 7 7 = 21 := rfl
theorem degree_nitrogen15Atom : atomDegree 7 8 7 = 22 := rfl
theorem degree_nitrideAnion : atomDegree 7 7 10 = 24 := rfl

theorem nitrogen_degree_exceeds_kerD6 (N e : ℕ) :
    atomDegree 7 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 4: Electron Shell Structure

Nitrogen: 1s² 2s² 2p³ (7 electrons). Half-filled 2p shell.
Valence = closedShellElectronCount(2) - 7 = 3.
-/

theorem nitrogen_shell_filling :
    Nuclear.Subshell.maxElectrons ⟨1, 0⟩ +  -- 1s: 2
    Nuclear.Subshell.maxElectrons ⟨2, 0⟩ +  -- 2s: 2
    3 = nitrogenZ                             -- 2p: 3 of 6
    := rfl

-- Half-filled p shell: exactly half of maxElectrons(2,1) = 6
theorem nitrogen_half_filled_2p :
    Nuclear.Subshell.maxElectrons ⟨2, 1⟩ / 2 = 3 := rfl

theorem nitrogen_valence :
    closedShellElectronCount 2 - nitrogenZ = 3 := by decide

private theorem closedShell_ge_10_of_ge_2 (n : ℕ) (hn : n ≥ 2) :
    closedShellElectronCount n ≥ 10 := by
  have hmono := closedShellElectronCount_strict_mono
  have h2 : closedShellElectronCount 2 = 10 := by decide
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k + 1 = 2
    · rw [hk, h2]
    · have hk2 : k ≥ 2 := by omega
      have ihk := ih hk2
      have := hmono k (by omega)
      omega

theorem nitrogen_not_closed_shell : ¬ isClosedShell 7 := by
  intro ⟨n, hn, heq⟩
  by_cases h1 : n = 1
  · subst h1; simp [closedShell_1] at heq
  · have hn2 : n ≥ 2 := by omega
    have := closedShell_ge_10_of_ge_2 n hn2
    omega

-- Nitride N³⁻ (e=10) achieves closed shell (isoelectronic with Ne)
theorem nitride_is_closed_shell : isClosedShell 10 := neon_is_closed_shell

/-! ## Section 5: Ammonia (NH₃)

Z = N.Z + 3·H.Z = 7 + 3 = 10, N = N14.N + 3·H.N = 7, e = Z = 10.
NH₃ is closed shell (e=10), isoelectronic with H₂O, CH₄, and Ne.
-/

theorem ammonia_Z : nitrogenZ + 3 * hydrogenZ = 10 := rfl
theorem ammonia_N : neutrons_N14 + 3 * protium_N = 7 := rfl

noncomputable def ammonia (x : ℝ) : ℝ := atomStateFn 10 7 10 x

theorem ammonia_eq (x : ℝ) :
    ammonia x = x ^ 10 * (1 + x) ^ 7 * (1 + ψ * x) ^ 10 := rfl

theorem ammonia_is_closed_shell : isClosedShell 10 := neon_is_closed_shell

-- NH₃ stoichiometry: nitrogen valence = 3 = number of H atoms
theorem ammonia_stoichiometry :
    closedShellElectronCount 2 - nitrogenZ = 3 ∧
    closedShellElectronCount 2 = nitrogenZ + 3 * hydrogenZ := by
  constructor <;> decide

theorem degree_ammonia : atomDegree 10 7 10 = 27 := rfl

-- NH₃, H₂O, CH₄ are all isoelectronic (e=10)
theorem ammonia_water_methane_isoelectronic :
    nitrogenZ + 3 * hydrogenZ = 2 * hydrogenZ + oxygenZ ∧
    nitrogenZ + 3 * hydrogenZ = carbonZ + 4 * hydrogenZ := ⟨rfl, rfl⟩

/-! ## Section 6: Mass Number Properties -/

theorem nitrogen14_mass_number : nitrogenZ + neutrons_N14 = 14 := rfl
theorem nitrogen15_mass_number : nitrogenZ + neutrons_N15 = 15 := rfl

/-! ## Section 7: Summary -/

theorem nitrogen_isotope_classification :
    nitrogenZ = 7 ∧
    nitrogenZ = neutrons_N14 ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_N15) ∧
    Helium.closedShellElectronCount 2 - nitrogenZ = 3 ∧
    ¬ Helium.isClosedShell 7 ∧ Helium.isClosedShell 10 ∧
    nitrogenZ + 3 * hydrogenZ = 10 ∧
    (∀ N e, atomDegree 7 N e > 2) := by
  refine ⟨rfl, rfl, ⟨1, by omega, rfl⟩, by decide,
    nitrogen_not_closed_shell, Helium.neon_is_closed_shell, rfl, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Nitrogen

namespace FUST.DiscreteTag
open FUST.Chemistry.Nitrogen

def nitrogenZ_t : DTagged .protonNum := ⟨nitrogenZ⟩
def N14N_t : DTagged .neutronNum := ⟨neutrons_N14⟩
def N15N_t : DTagged .neutronNum := ⟨neutrons_N15⟩

theorem nitrogenZ_t_val : nitrogenZ_t.val = 7 := rfl
theorem N14N_t_val : N14N_t.val = 7 := rfl
theorem N15N_t_val : N15N_t.val = 8 := rfl

def ammoniaZ_t : DTagged .protonNum := nitrogenZ_t + scaleZ 3 hydrogenZ_t
def ammoniaDeg_t : DTagged .degree := mkDegree ammoniaZ_t N14N_t ammoniaZ_t

theorem ammoniaZ_t_val : ammoniaZ_t.val = 10 := rfl
theorem ammoniaDeg_t_val : ammoniaDeg_t.val = 27 := rfl

-- N + H = O
theorem nitrogen_plus_H_eq_oxygen :
    nitrogenZ_t + hydrogenZ_t = oxygenZ_t := rfl

-- NH₃ = N + 3H
theorem ammonia_Z_tagged : ammoniaZ_t = nitrogenZ_t + scaleZ 3 hydrogenZ_t := rfl

-- Degree construction consistency
theorem ammonia_deg_consistency :
    mkDegree ammoniaZ_t N14N_t ammoniaZ_t = ammoniaDeg_t := rfl

-- N-14 symmetric (N = Z)
theorem N14_symmetric_N : N14N_t.val = nitrogenZ_t.val := rfl

-- N-15 has magic N = oxygenZ
theorem N15_magic_neutron : N15N_t.val = oxygenZ_t.val := rfl

end FUST.DiscreteTag
