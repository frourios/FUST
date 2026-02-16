/-
Vanadium from D-operator Kernel Structure

Vanadium Z = 23 = nuclearMagic(2) + spatialDim = 20 + 3.
Configuration: [Ar] 3d³ 4s².
V-51 (Z=23, N=28): most abundant isotope.
V-51 has magic neutron number N = 28 = nuclearMagic(3).
Forms stable hydride VH₂ — hydrogen strengthening metal.
-/

import FUST.Chemistry.Metals.Iron

namespace FUST.Chemistry.Vanadium

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Iron

/-! ## Section 1: Vanadium Parameters

vanadiumZ = 23 = nuclearMagic(2) + spatialDim = 20 + 3.
Aufbau: [Ar] 3d³ 4s².
-/

abbrev vanadiumZ : ℕ := 23

theorem vanadiumZ_from_magic :
    Nuclear.nuclearMagic 2 + WaveEquation.spatialDim = vanadiumZ := by decide

-- [Ar] 3d³ 4s²
abbrev vanadium_3d_electrons : ℕ := 3

theorem vanadiumZ_shell_filling :
    arCoreElectrons +
    Nuclear.Subshell.maxElectrons ⟨4, 0⟩ +  -- 4s: 2
    vanadium_3d_electrons = vanadiumZ         -- 3d: 3 of 10
    := rfl

-- 3d vacancy = 10 - 3 = 7
theorem vanadium_3d_vacancy :
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ - vanadium_3d_electrons = 7 := rfl

/-! ## Section 2: Vanadium Isotopes -/

def neutrons (A : ℕ) : ℕ := A - vanadiumZ
abbrev neutrons_V51 : ℕ := neutrons 51
abbrev neutrons_V50 : ℕ := neutrons 50

theorem neutrons_V51_eq : neutrons_V51 = 28 := rfl
theorem neutrons_V50_eq : neutrons_V50 = 27 := rfl

-- V-51 has magic neutron number N = 28 = nuclearMagic(3)
theorem V51_neutron_magic :
    ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_V51 := ⟨3, by omega, rfl⟩

-- V-51 shares magic N with Fe-54 and Cr-52
theorem V51_N_eq_Fe54_N : neutrons_V51 = neutrons_Fe54 := rfl

/-! ## Section 3: State Functions -/

noncomputable def vanadium51Ion (x : ℝ) : ℝ := atomStateFn 23 28 0 x
noncomputable def vanadium51Atom (x : ℝ) : ℝ := atomStateFn 23 28 23 x

theorem vanadium51Atom_eq (x : ℝ) :
    vanadium51Atom x = x ^ 23 * (1 + x) ^ 28 * (1 + ψ * x) ^ 23 := rfl

/-! ## Section 4: Degree Structure -/

theorem degree_vanadium51Ion : atomDegree 23 28 0 = 51 := rfl
theorem degree_vanadium51Atom : atomDegree 23 28 23 = 74 := rfl

theorem vanadium_degree_exceeds_kerD6 (N e : ℕ) :
    atomDegree 23 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 5: Mass Numbers -/

theorem V51_mass_number : vanadiumZ + neutrons_V51 = 51 := rfl
theorem V50_mass_number : vanadiumZ + neutrons_V50 = 50 := rfl

/-! ## Section 6: Summary -/

theorem vanadium_classification :
    vanadiumZ = 23 ∧
    Nuclear.nuclearMagic 2 + WaveEquation.spatialDim = vanadiumZ ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_V51) ∧
    neutrons_V51 = neutrons_Fe54 ∧
    (∀ N e, atomDegree 23 N e > 2) := by
  refine ⟨rfl, by decide, ⟨3, by omega, rfl⟩, rfl, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Vanadium

namespace FUST.DiscreteTag
open FUST.Chemistry.Vanadium

def vanadiumZ_t : DTagged .protonNum := ⟨vanadiumZ⟩
def V51N_t : DTagged .neutronNum := ⟨neutrons_V51⟩

def vanadiumDeg_t : DTagged .degree := mkDegree vanadiumZ_t V51N_t vanadiumZ_t

theorem vanadiumZ_t_val : vanadiumZ_t.val = 23 := rfl
theorem V51N_t_val : V51N_t.val = 28 := rfl
theorem vanadiumDeg_t_val : vanadiumDeg_t.val = 74 := rfl

-- V-51 N is magic
theorem V51N_is_magic : V51N_t.val = Nuclear.nuclearMagic 3 := rfl

-- Degree construction consistency
theorem vanadium_deg_consistency :
    mkDegree vanadiumZ_t V51N_t vanadiumZ_t = vanadiumDeg_t := rfl

end FUST.DiscreteTag
