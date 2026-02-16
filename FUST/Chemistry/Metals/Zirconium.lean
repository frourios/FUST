/-
Zirconium from D-operator Kernel Structure

Zirconium Z = 40 = 2 × nuclearMagic(2) = 2 × 20.
Configuration: [Kr] 4d² 5s².
Zr-90 (Z=40, N=50): most abundant isotope.
Zr-90 has magic neutron number N = 50 = nuclearMagic(4).
Forms stable hydride ZrH₂ — hydrogen strengthening metal.
-/

import FUST.Chemistry.Metals.Iron

namespace FUST.Chemistry.Zirconium

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Iron

/-! ## Section 1: Zirconium Parameters

zirconiumZ = 40 = 2 × nuclearMagic(2) = 2 × 20.
Aufbau: [Kr] 4d² 5s². Kr core = Ar + 3d¹⁰ + 4s² + 4p⁶ = 36.
-/

-- Kr core: [Ar] 3d¹⁰ 4s² 4p⁶ = 18 + 10 + 2 + 6 = 36
abbrev krCoreElectrons : ℕ := 36

theorem krCore_eq :
    arCoreElectrons +
    Nuclear.Subshell.maxElectrons ⟨3, 2⟩ +  -- 3d: 10
    Nuclear.Subshell.maxElectrons ⟨4, 0⟩ +  -- 4s: 2
    Nuclear.Subshell.maxElectrons ⟨4, 1⟩    -- 4p: 6
    = krCoreElectrons := rfl

abbrev zirconiumZ : ℕ := 40

theorem zirconiumZ_from_magic :
    2 * Nuclear.nuclearMagic 2 = zirconiumZ := by decide

-- [Kr] 4d² 5s²
abbrev zirconium_4d_electrons : ℕ := 2

theorem zirconiumZ_shell_filling :
    krCoreElectrons +
    Nuclear.Subshell.maxElectrons ⟨5, 0⟩ +  -- 5s: 2
    zirconium_4d_electrons = zirconiumZ       -- 4d: 2 of 10
    := rfl

-- 4d vacancy = 10 - 2 = 8
theorem zirconium_4d_vacancy :
    Nuclear.Subshell.maxElectrons ⟨4, 2⟩ - zirconium_4d_electrons = 8 := rfl

/-! ## Section 2: Zirconium Isotopes -/

def neutrons (A : ℕ) : ℕ := A - zirconiumZ
abbrev neutrons_Zr90 : ℕ := neutrons 90
abbrev neutrons_Zr91 : ℕ := neutrons 91
abbrev neutrons_Zr92 : ℕ := neutrons 92

theorem neutrons_Zr90_eq : neutrons_Zr90 = 50 := rfl
theorem neutrons_Zr91_eq : neutrons_Zr91 = 51 := rfl
theorem neutrons_Zr92_eq : neutrons_Zr92 = 52 := rfl

-- Zr-90 has magic neutron number N = 50 = nuclearMagic(4)
theorem Zr90_neutron_magic :
    ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Zr90 := ⟨4, by omega, rfl⟩

/-! ## Section 3: State Functions -/

noncomputable def zirconium90Ion (x : ℝ) : ℝ := atomStateFn 40 50 0 x
noncomputable def zirconium90Atom (x : ℝ) : ℝ := atomStateFn 40 50 40 x

theorem zirconium90Atom_eq (x : ℝ) :
    zirconium90Atom x = x ^ 40 * (1 + x) ^ 50 * (1 + ψ * x) ^ 40 := rfl

/-! ## Section 4: Degree Structure -/

theorem degree_zirconium90Ion : atomDegree 40 50 0 = 90 := rfl
theorem degree_zirconium90Atom : atomDegree 40 50 40 = 130 := rfl

theorem zirconium_degree_exceeds_kerD6 (N e : ℕ) :
    atomDegree 40 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 5: Mass Numbers -/

theorem Zr90_mass_number : zirconiumZ + neutrons_Zr90 = 90 := rfl
theorem Zr91_mass_number : zirconiumZ + neutrons_Zr91 = 91 := rfl
theorem Zr92_mass_number : zirconiumZ + neutrons_Zr92 = 92 := rfl

/-! ## Section 6: Summary -/

theorem zirconium_classification :
    zirconiumZ = 40 ∧
    2 * Nuclear.nuclearMagic 2 = zirconiumZ ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_Zr90) ∧
    (∀ N e, atomDegree 40 N e > 2) := by
  refine ⟨rfl, by decide, ⟨4, by omega, rfl⟩, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Zirconium

namespace FUST.DiscreteTag
open FUST.Chemistry.Zirconium

def zirconiumZ_t : DTagged .protonNum := ⟨zirconiumZ⟩
def Zr90N_t : DTagged .neutronNum := ⟨neutrons_Zr90⟩

def zirconiumDeg_t : DTagged .degree := mkDegree zirconiumZ_t Zr90N_t zirconiumZ_t

theorem zirconiumZ_t_val : zirconiumZ_t.val = 40 := rfl
theorem Zr90N_t_val : Zr90N_t.val = 50 := rfl
theorem zirconiumDeg_t_val : zirconiumDeg_t.val = 130 := rfl

-- Zr-90 N is magic
theorem Zr90N_is_magic : Zr90N_t.val = Nuclear.nuclearMagic 4 := rfl

-- Degree construction consistency
theorem zirconium_deg_consistency :
    mkDegree zirconiumZ_t Zr90N_t zirconiumZ_t = zirconiumDeg_t := rfl

end FUST.DiscreteTag
