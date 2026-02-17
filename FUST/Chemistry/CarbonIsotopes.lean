/-
Carbon Isotopes from D-operator Kernel Structure

State function g(x) = x^Z · (1+x)^N · (1+ψx)^e.
Carbon Z = spinDegeneracy × spatialDim = 6.
¹²C (Z=N=6) is a symmetric nucleus with g = unitCell^6.
¹⁴C has N = 8 = nuclearMagic(1), a magic neutron number.
-/

import FUST.DifferenceOperators
import FUST.Chemistry.HeliumInertness

namespace FUST.Chemistry.Carbon

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen FUST.Chemistry.Helium

/-! ## Section 1: Carbon Parameters

carbonZ = spinDegeneracy × spatialDim = 2 × 3 = 6.
-/

abbrev carbonZ : ℕ := Nuclear.spinDegeneracy * WaveEquation.spatialDim

theorem carbonZ_eq : carbonZ = 6 := rfl

-- Neutron counts from mass number: N = A - Z
def neutrons (A : ℕ) : ℕ := A - carbonZ
abbrev neutrons_C12 : ℕ := neutrons 12
abbrev neutrons_C13 : ℕ := neutrons 13
abbrev neutrons_C14 : ℕ := neutrons 14

theorem neutrons_C12_eq : neutrons_C12 = 6 := rfl
theorem neutrons_C13_eq : neutrons_C13 = 7 := rfl
theorem neutrons_C14_eq : neutrons_C14 = 8 := rfl

-- ¹²C is a symmetric nucleus: Z = N
theorem carbon12_symmetric : carbonZ = neutrons_C12 := rfl

-- ¹⁴C has a magic neutron number
theorem carbon14_neutron_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_C14 :=
  ⟨1, by omega, rfl⟩

/-! ## Section 2: Carbon Species State Functions -/

-- Bare nuclei
noncomputable def carbon12Ion (x : ℝ) : ℝ := atomStateFn 6 6 0 x
noncomputable def carbon13Ion (x : ℝ) : ℝ := atomStateFn 6 7 0 x
noncomputable def carbon14Ion (x : ℝ) : ℝ := atomStateFn 6 8 0 x

-- Neutral atoms
noncomputable def carbon12Atom (x : ℝ) : ℝ := atomStateFn 6 6 6 x
noncomputable def carbon13Atom (x : ℝ) : ℝ := atomStateFn 6 7 6 x
noncomputable def carbon14Atom (x : ℝ) : ℝ := atomStateFn 6 8 6 x

-- Common ions
noncomputable def carbonCation (x : ℝ) : ℝ := atomStateFn 6 6 5 x
noncomputable def carbideAnion (x : ℝ) : ℝ := atomStateFn 6 6 10 x

/-! ## Section 3: Factored Form Identities -/

theorem carbon12Ion_eq (x : ℝ) :
    carbon12Ion x = x ^ 6 * (1 + x) ^ 6 := by
  unfold carbon12Ion atomStateFn; simp [pow_zero, mul_one]

theorem carbon12Atom_eq (x : ℝ) :
    carbon12Atom x = x ^ 6 * (1 + x) ^ 6 * (1 + ψ * x) ^ 6 := rfl

-- ¹²C neutral = unitCell^6 = unitCell^(spinDegeneracy × spatialDim)
theorem carbon12Atom_eq_unitCell_pow (x : ℝ) :
    carbon12Atom x = unitCell x ^ 6 := by
  unfold carbon12Atom atomStateFn unitCell; ring

-- C-4 anion (e=10) has same electron count as neon
theorem carbideAnion_eq (x : ℝ) :
    carbideAnion x = x ^ 6 * (1 + x) ^ 6 * (1 + ψ * x) ^ 10 := rfl

/-! ## Section 4: Degree Structure -/

theorem degree_carbon12Ion : (dimAtom 6 6 0).effectiveDegree = 187 := by decide
theorem degree_carbon13Ion : (dimAtom 6 7 0).effectiveDegree = 202 := by decide
theorem degree_carbon14Ion : (dimAtom 6 8 0).effectiveDegree = 217 := by decide
theorem degree_carbon12Atom : (dimAtom 6 6 6).effectiveDegree = 199 := by decide
theorem degree_carbon13Atom : (dimAtom 6 7 6).effectiveDegree = 214 := by decide
theorem degree_carbon14Atom : (dimAtom 6 8 6).effectiveDegree = 229 := by decide
theorem degree_carbonCation : (dimAtom 6 6 5).effectiveDegree = 197 := by decide
theorem degree_carbideAnion : (dimAtom 6 6 10).effectiveDegree = 207 := by decide

-- All carbon species exceed ker(D6) threshold
theorem carbon_degree_exceeds_kerD6 :
    (dimAtom 6 6 0).effectiveDegree > 2 ∧
    (dimAtom 6 6 6).effectiveDegree > 2 ∧
    (dimAtom 6 6 10).effectiveDegree > 2 := by decide

/-! ## Section 5: Electron Shell Structure

Carbon: 1s² 2s² 2p² (6 electrons). Valence = 4 = closedShellElectronCount(2) - 6.
-/

theorem carbon_electron_count : carbonZ = 6 := rfl

theorem carbon_shell_filling :
    Nuclear.subshellCapacity 0 +  -- 1s: 2
    Nuclear.subshellCapacity 0 +  -- 2s: 2
    2 = carbonZ                               -- 2p: 2 of 6
    := rfl

-- Carbon valence = vacancy to next closed shell = 10 - 6 = 4
theorem carbon_valence :
    closedShellElectronCount 2 - carbonZ = 4 := by decide

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

theorem carbon_not_closed_shell : ¬ isClosedShell 6 := by
  intro ⟨n, hn, heq⟩
  by_cases h1 : n = 1
  · subst h1; simp [closedShell_1] at heq
  · have hn2 : n ≥ 2 := by omega
    have := closedShell_ge_10_of_ge_2 n hn2
    omega

-- Carbide C⁴⁻ (e=10) achieves closed shell
theorem carbide_is_closed_shell : isClosedShell 10 := neon_is_closed_shell

/-! ## Section 6: Symmetric Nucleus Classification

Lightest stable symmetric nuclei (Z=N): ⁴He, ¹²C, ¹⁶O.
Their state functions are unitCell^Z.
-/

theorem symmetric_nuclei_unitCell :
    -- He-4: unitCell^2
    (∀ x : ℝ, atomStateFn 2 2 2 x = unitCell x ^ 2) ∧
    -- C-12: unitCell^6
    (∀ x : ℝ, atomStateFn 6 6 6 x = unitCell x ^ 6) ∧
    -- O-16: unitCell^8
    (∀ x : ℝ, atomStateFn 8 8 8 x = unitCell x ^ 8) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩ <;>
  unfold atomStateFn unitCell <;> ring

-- The exponents are: 2, 6, 8 = nuclearMagic(0), carbonZ, nuclearMagic(1)
theorem symmetric_nuclei_exponents :
    Nuclear.nuclearMagic 0 = 2 ∧
    carbonZ = 6 ∧
    Nuclear.nuclearMagic 1 = 8 := ⟨rfl, rfl, rfl⟩

/-! ## Section 7: Mass Number Properties -/

theorem carbon12_mass_number : carbonZ + neutrons_C12 = 12 := rfl
theorem carbon13_mass_number : carbonZ + neutrons_C13 = 13 := rfl
theorem carbon14_mass_number : carbonZ + neutrons_C14 = 14 := rfl

-- ¹²C effectiveDegree
theorem carbon12_effDeg :
    (dimAtom 6 6 6).effectiveDegree = 199 := by decide

/-! ## Section 8: Ionization Series -/

theorem ionization_effDeg_C12 :
    (dimAtom 6 6 0).effectiveDegree = 187 ∧   -- C⁶⁺
    (dimAtom 6 6 1).effectiveDegree = 189 ∧   -- C⁵⁺
    (dimAtom 6 6 2).effectiveDegree = 191 ∧   -- C⁴⁺
    (dimAtom 6 6 3).effectiveDegree = 193 ∧   -- C³⁺
    (dimAtom 6 6 4).effectiveDegree = 195 ∧   -- C²⁺
    (dimAtom 6 6 5).effectiveDegree = 197 ∧   -- C⁺
    (dimAtom 6 6 6).effectiveDegree = 199 ∧   -- C
    (dimAtom 6 6 7).effectiveDegree = 201 ∧   -- C⁻
    (dimAtom 6 6 8).effectiveDegree = 203 ∧   -- C²⁻
    (dimAtom 6 6 9).effectiveDegree = 205 ∧   -- C³⁻
    (dimAtom 6 6 10).effectiveDegree = 207     -- C⁴⁻
    := by decide

/-! ## Section 9: Summary -/

theorem carbon_isotope_classification :
    -- carbonZ derived from D-operator kernels
    carbonZ = Nuclear.spinDegeneracy * WaveEquation.spatialDim ∧
    -- ¹²C is a symmetric nucleus (Z = N)
    carbonZ = neutrons_C12 ∧
    -- ¹⁴C has magic neutron number
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_C14) ∧
    -- ¹²C neutral = unitCell^6
    (∀ x : ℝ, carbon12Atom x = unitCell x ^ 6) ∧
    -- Carbon valence = 4
    closedShellElectronCount 2 - carbonZ = 4 ∧
    -- Carbon is not closed shell, carbide is
    ¬ isClosedShell 6 ∧ isClosedShell 10 ∧
    -- Key carbon species exceed ker(D6)
    (dimAtom 6 6 6).effectiveDegree > 2 := by
  refine ⟨rfl, rfl, ⟨1, by omega, rfl⟩, carbon12Atom_eq_unitCell_pow,
    by decide, carbon_not_closed_shell, neon_is_closed_shell, by decide⟩

end FUST.Chemistry.Carbon

