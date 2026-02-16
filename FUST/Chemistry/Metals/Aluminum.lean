/-
Aluminum from D-operator Kernel Structure

Aluminum Z = 13 = closedShellElectronCount(2) + spatialDim = 10 + 3.
Configuration: [Ne] 3s² 3p¹ (p-block metal, no d-electrons).
Al-27 (Z=13, N=14): only stable isotope. N = 2 × nitrogenZ.
-/

import FUST.Chemistry.SulfurAtom

namespace FUST.Chemistry.Aluminum

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Helium
open FUST.Chemistry.Dihydrogen FUST.Chemistry.Nitrogen

/-! ## Section 1: Aluminum Parameters

aluminumZ = 13 = closedShellElectronCount(2) + spatialDim = 10 + 3.
Aufbau: [Ne] 3s² 3p¹. p-block metal with no d-electrons.
-/

abbrev aluminumZ : ℕ := 13

theorem aluminumZ_derivation :
    closedShellElectronCount 2 + WaveEquation.spatialDim = aluminumZ := by decide

-- [Ne] 3s² 3p¹
theorem aluminumZ_shell_filling :
    closedShellElectronCount 2 +
    Nuclear.Subshell.maxElectrons ⟨3, 0⟩ +  -- 3s: 2
    1 = aluminumZ                             -- 3p: 1 of 6
    := by decide

-- Valence = 3 (group IIIA)
theorem aluminum_valence :
    aluminumZ - closedShellElectronCount 2 = WaveEquation.spatialDim := by decide

/-! ## Section 2: Aluminum Isotope -/

def neutrons (A : ℕ) : ℕ := A - aluminumZ
abbrev neutrons_Al27 : ℕ := neutrons 27

theorem neutrons_Al27_eq : neutrons_Al27 = 14 := rfl

-- Al-27 N = 2 × nitrogenZ
theorem Al27_N_eq_2nitrogenZ : neutrons_Al27 = 2 * nitrogenZ := rfl

/-! ## Section 3: State Functions -/

noncomputable def aluminum27Ion (x : ℝ) : ℝ := atomStateFn 13 14 0 x
noncomputable def aluminum27Atom (x : ℝ) : ℝ := atomStateFn 13 14 13 x

theorem aluminum27Atom_eq (x : ℝ) :
    aluminum27Atom x = x ^ 13 * (1 + x) ^ 14 * (1 + ψ * x) ^ 13 := rfl

/-! ## Section 4: Degree Structure -/

theorem degree_aluminum27Ion : atomDegree 13 14 0 = 27 := rfl
theorem degree_aluminum27Atom : atomDegree 13 14 13 = 40 := rfl

theorem aluminum_degree_exceeds_kerD6 (N e : ℕ) :
    atomDegree 13 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 5: Mass Number -/

theorem Al27_mass_number : aluminumZ + neutrons_Al27 = 27 := rfl

/-! ## Section 6: Summary -/

theorem aluminum_classification :
    aluminumZ = 13 ∧
    closedShellElectronCount 2 + WaveEquation.spatialDim = aluminumZ ∧
    neutrons_Al27 = 2 * nitrogenZ ∧
    (∀ N e, atomDegree 13 N e > 2) := by
  refine ⟨rfl, by decide, rfl, ?_⟩
  intro N e; unfold atomDegree; omega

end FUST.Chemistry.Aluminum

namespace FUST.DiscreteTag
open FUST.Chemistry.Aluminum

def aluminumZ_t : DTagged .protonNum := ⟨aluminumZ⟩
def Al27N_t : DTagged .neutronNum := ⟨neutrons_Al27⟩

def aluminumDeg_t : DTagged .degree := mkDegree aluminumZ_t Al27N_t aluminumZ_t

theorem aluminumZ_t_val : aluminumZ_t.val = 13 := rfl
theorem Al27N_t_val : Al27N_t.val = 14 := rfl
theorem aluminumDeg_t_val : aluminumDeg_t.val = 40 := rfl

-- Al-27 N = 2 × nitrogenZ
theorem Al27N_eq_2nitrogenZ_tagged :
    Al27N_t.val = 2 * nitrogenZ_t.val := rfl

-- Degree construction consistency
theorem aluminum_deg_consistency :
    mkDegree aluminumZ_t Al27N_t aluminumZ_t = aluminumDeg_t := rfl

end FUST.DiscreteTag
