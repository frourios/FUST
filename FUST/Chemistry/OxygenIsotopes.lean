/-
Oxygen Isotopes and Ionization from D-operator Kernel Structure

State function g(x) = x^Z · (1+x)^N · (1+ψx)^e
where Z = proton count, N = neutron count, e = electron count.

For oxygen (Z=8): all species have deg ≥ 16, hence all lie outside ker(D6).
O-16 (Z=8, N=8) is doubly magic, connecting to Nuclear.lean.
-/

import FUST.DifferenceOperators
import FUST.Physics.Nuclear
import FUST.Chemistry.HydrogenIsotopes

namespace FUST.Chemistry.Oxygen

open FUST FUST.Chemistry

/-! ## Section 1: General Atom State Function

g(x) = x^Z · (1+x)^N · (1+ψx)^e with deg(g) = Z + N + e.
-/

noncomputable def atomStateFn (Z N e : ℕ) (x : ℝ) : ℝ :=
  x ^ Z * (1 + x) ^ N * (1 + ψ * x) ^ e

def atomDegree (Z N e : ℕ) : ℕ := Z + N + e

theorem atomDegree_eq_speciesDegree_for_hydrogen (N e : ℕ) :
    atomDegree 1 N e = speciesDegree N e := by
  unfold atomDegree speciesDegree; omega

/-! ## Section 2: Oxygen Parameters

oxygenZ = 8 = nuclearMagic(1), so oxygen's proton number is a nuclear magic number.
Neutron counts are derived from mass numbers: N = A - Z.
-/

abbrev oxygenZ : ℕ := Nuclear.nuclearMagic 1

theorem oxygenZ_eq : oxygenZ = 8 := rfl

-- Stable isotope neutron counts: N = A - Z
def neutrons (A : ℕ) : ℕ := A - oxygenZ
abbrev neutrons_O16 : ℕ := neutrons 16
abbrev neutrons_O17 : ℕ := neutrons 17
abbrev neutrons_O18 : ℕ := neutrons 18

theorem neutrons_O16_eq : neutrons_O16 = 8 := rfl
theorem neutrons_O17_eq : neutrons_O17 = 9 := rfl
theorem neutrons_O18_eq : neutrons_O18 = 10 := rfl

/-! ## Section 3: Oxygen Species State Functions -/

-- Bare nuclei (fully ionized)
noncomputable def oxygen16Ion (x : ℝ) : ℝ := atomStateFn 8 8 0 x
noncomputable def oxygen17Ion (x : ℝ) : ℝ := atomStateFn 8 9 0 x
noncomputable def oxygen18Ion (x : ℝ) : ℝ := atomStateFn 8 10 0 x

-- Neutral atoms
noncomputable def oxygen16Atom (x : ℝ) : ℝ := atomStateFn 8 8 8 x
noncomputable def oxygen17Atom (x : ℝ) : ℝ := atomStateFn 8 9 8 x
noncomputable def oxygen18Atom (x : ℝ) : ℝ := atomStateFn 8 10 8 x

-- Common ions
noncomputable def oxideAnion (x : ℝ) : ℝ := atomStateFn 8 8 10 x
noncomputable def superoxideAnion (x : ℝ) : ℝ := atomStateFn 8 8 9 x
noncomputable def oxygenCation (x : ℝ) : ℝ := atomStateFn 8 8 7 x

/-! ## Section 4: Factored Form Identities -/

theorem oxygen16Ion_eq (x : ℝ) :
    oxygen16Ion x = x ^ 8 * (1 + x) ^ 8 := by
  unfold oxygen16Ion atomStateFn; simp [pow_zero, mul_one]

theorem oxygen16Atom_eq (x : ℝ) :
    oxygen16Atom x = x ^ 8 * (1 + x) ^ 8 * (1 + ψ * x) ^ 8 := rfl

theorem oxideAnion_eq (x : ℝ) :
    oxideAnion x = x ^ 8 * (1 + x) ^ 8 * (1 + ψ * x) ^ 10 := rfl

/-! ## Section 5: Degree Structure -/

theorem degree_oxygen16Ion : atomDegree 8 8 0 = 16 := rfl
theorem degree_oxygen17Ion : atomDegree 8 9 0 = 17 := rfl
theorem degree_oxygen18Ion : atomDegree 8 10 0 = 18 := rfl
theorem degree_oxygen16Atom : atomDegree 8 8 8 = 24 := rfl
theorem degree_oxygen17Atom : atomDegree 8 9 8 = 25 := rfl
theorem degree_oxygen18Atom : atomDegree 8 10 8 = 26 := rfl
theorem degree_oxideAnion : atomDegree 8 8 10 = 26 := rfl
theorem degree_superoxideAnion : atomDegree 8 8 9 = 25 := rfl
theorem degree_oxygenCation : atomDegree 8 8 7 = 23 := rfl

-- All oxygen species have degree ≥ 16
theorem oxygen_degree_lower_bound (N e : ℕ) (hN : N ≥ 8) :
    atomDegree 8 N e ≥ 16 := by
  unfold atomDegree; omega

-- All oxygen species far exceed ker(D6) threshold
theorem oxygen_degree_exceeds_kerD6 (N e : ℕ) (hN : N ≥ 8) :
    atomDegree 8 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 6: Ionization Series Degrees -/

theorem ionization_degrees_O16 :
    atomDegree 8 8 0 = 16 ∧   -- O⁸⁺
    atomDegree 8 8 1 = 17 ∧   -- O⁷⁺
    atomDegree 8 8 2 = 18 ∧   -- O⁶⁺
    atomDegree 8 8 3 = 19 ∧   -- O⁵⁺
    atomDegree 8 8 4 = 20 ∧   -- O⁴⁺
    atomDegree 8 8 5 = 21 ∧   -- O³⁺
    atomDegree 8 8 6 = 22 ∧   -- O²⁺
    atomDegree 8 8 7 = 23 ∧   -- O⁺
    atomDegree 8 8 8 = 24 ∧   -- O
    atomDegree 8 8 9 = 25 ∧   -- O⁻
    atomDegree 8 8 10 = 26    -- O²⁻
    := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 7: Nuclear Magic Number Connection

O-16 is doubly magic (Z=8, N=8). This connects to FUST.Nuclear.O16.
-/

theorem oxygen16_proton_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = 8 :=
  ⟨1, by omega, rfl⟩

theorem oxygen16_neutron_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = 8 :=
  ⟨1, by omega, rfl⟩

theorem oxygen16_mass_number : oxygenZ + neutrons_O16 = 16 := rfl
theorem oxygen17_mass_number : oxygenZ + neutrons_O17 = 17 := rfl
theorem oxygen18_mass_number : oxygenZ + neutrons_O18 = 18 := rfl

/-! ## Section 8: D6 Non-Kernel via Degree

For any species with Z + N + e ≥ 3, the state function is a polynomial of
degree ≥ 3, hence lies outside ker(D6) = span{1, x, x²}.

Note: D6(f)(x) may vanish at specific x ≠ 0 (as a rational function of x),
but the polynomial is not identically in ker(D6) as a function.
-/

-- All oxygen species vanish at x=0
theorem atomStateFn_vanishes_at_zero (Z N e : ℕ) (hZ : Z ≥ 1) :
    atomStateFn Z N e 0 = 0 := by
  unfold atomStateFn; simp [zero_pow (by omega : Z ≠ 0)]

theorem oxygen16Ion_vanishes_at_zero : oxygen16Ion 0 = 0 := by
  unfold oxygen16Ion; exact atomStateFn_vanishes_at_zero 8 8 0 (by omega)

/-! ## Section 9: General Degree Bound

For any element with Z ≥ 3, all species are outside ker(D6)
regardless of neutron count and ionization state.
-/

theorem general_degree_exceeds_kerD6 (Z N e : ℕ) (hZ : Z ≥ 3) :
    atomDegree Z N e > 2 := by
  unfold atomDegree; omega

-- This means ker(D6) membership is relevant only for Z ≤ 2 (H and He)
theorem kerD6_relevance :
    atomDegree 1 0 0 ≤ 2 ∧  -- H⁺: deg=1 ∈ ker
    atomDegree 1 1 0 ≤ 2 ∧  -- D⁺: deg=2 ∈ ker
    atomDegree 1 0 1 ≤ 2 ∧  -- H:  deg=2 ∈ ker
    atomDegree 2 0 0 ≤ 2 ∧  -- He²⁺: deg=2 ∈ ker (alpha particle core)
    ¬(atomDegree 1 2 0 ≤ 2) ∧ -- T⁺: deg=3 ∉ ker
    ¬(atomDegree 2 1 0 ≤ 2) ∧ -- He³⁺ nucleus: deg=3 ∉ ker
    ¬(atomDegree 3 0 0 ≤ 2)   -- Li³⁺: deg=3 ∉ ker, first Z≥3
    := by unfold atomDegree; omega

/-! ## Section 10: Electron Shell Filling

Oxygen: 1s² 2s² 2p⁴ (8 electrons).
Oxide O²⁻: 1s² 2s² 2p⁶ (10 electrons, filled shell).
-/

theorem oxygen_electron_count : oxygenZ = 8 := rfl

-- 1s² + 2s² + 2p⁴ = 8
theorem oxygen_shell_filling :
    Nuclear.Subshell.maxElectrons ⟨1, 0⟩ +  -- 1s: 2
    Nuclear.Subshell.maxElectrons ⟨2, 0⟩ +  -- 2s: 2
    4 = oxygenZ                               -- 2p: 4 of 6
    := rfl

-- Oxide O²⁻ fills the 2p shell completely
theorem oxide_fills_2p :
    Nuclear.Subshell.maxElectrons ⟨1, 0⟩ +  -- 1s: 2
    Nuclear.Subshell.maxElectrons ⟨2, 0⟩ +  -- 2s: 2
    Nuclear.Subshell.maxElectrons ⟨2, 1⟩    -- 2p: 6
    = 10 := rfl

-- Shell 1 capacity + shell 2 capacity = 2 + 8 = 10
theorem oxide_fills_two_shells :
    Nuclear.shellCapacity 1 + Nuclear.shellCapacity 2 = 10 := rfl

/-! ## Section 11: Summary -/

theorem oxygen_isotope_classification :
    -- O-16 is doubly magic
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = oxygenZ) ∧
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = neutrons_O16) ∧
    -- All oxygen isotope degrees
    atomDegree 8 8 0 = 16 ∧ atomDegree 8 9 0 = 17 ∧ atomDegree 8 10 0 = 18 ∧
    -- Neutral atom degrees
    atomDegree 8 8 8 = 24 ∧ atomDegree 8 9 8 = 25 ∧ atomDegree 8 10 8 = 26 ∧
    -- All exceed ker(D6) threshold
    (∀ N e, N ≥ 8 → atomDegree 8 N e > 2) := by
  refine ⟨⟨1, by omega, rfl⟩, ⟨1, by omega, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro N e hN; unfold atomDegree; omega

end FUST.Chemistry.Oxygen

namespace FUST.DiscreteTag
open FUST.Chemistry.Oxygen

def oxygenZ_t : DTagged .protonNum := ⟨oxygenZ⟩
def O16N_t : DTagged .neutronNum := ⟨neutrons_O16⟩
def O17N_t : DTagged .neutronNum := ⟨neutrons_O17⟩
def O18N_t : DTagged .neutronNum := ⟨neutrons_O18⟩

theorem oxygenZ_t_val : oxygenZ_t.val = 8 := rfl
theorem O16N_t_val : O16N_t.val = 8 := rfl
theorem O17N_t_val : O17N_t.val = 9 := rfl
theorem O18N_t_val : O18N_t.val = 10 := rfl

-- N = Z for O-16 (doubly magic)
theorem O16_neutron_magic : O16N_t.val = oxygenZ_t.val := rfl

end FUST.DiscreteTag
