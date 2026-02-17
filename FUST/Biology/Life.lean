/-
Minimal Life State from FDim Structure

The minimal life = deuterium atom (Z=1, N=1, e=1), uniquely determined by:
1. Three-constituent requirement: proton, neutron, electron (all present)
2. Minimality: bondCount(Z,N,e) = Z+N+e-1, minimum at (1,1,1) = 2
3. Deuterium has a unique FDim distinct from all elementary particles
-/

import FUST.Chemistry.HydrogenIsotopes
import FUST.Physics.LeastAction
import FUST.Chemistry.GeneticCode
import Mathlib.Data.Nat.Choose.Basic

namespace FUST.Biology

open FUST FUST.LeastAction FUST.Chemistry FUST.Dim
open FUST.Chemistry.Oxygen FUST.Chemistry.Dihydrogen
open FUST.Chemistry.Nucleotide FUST.Chemistry.GeneticCode
open FUST.Chemistry.Carbon

/-! ## Section 1: Minimal Life State — Three-Constituent Requirement

Life requires all three constituents:
  Z ≥ 1 (proton: nuclear identity), N ≥ 1 (neutron: nuclear stability),
  e ≥ 1 (electron: chemistry). -/

structure MinimalLifeState where
  Z : ℕ
  N : ℕ
  e : ℕ
  has_proton : Z ≥ 1
  has_neutron : N ≥ 1
  has_electron : e ≥ 1

/-! ## Section 2: Bond Count and Minimality

Each composite has bondCount = Z + N + e - 1 binding bonds.
The minimum three-constituent state is (1,1,1) with 2 bonds. -/

def bondCount (Z N e : ℕ) : ℕ := Z + N + e - 1

theorem minimalLife_bondCount_ge_two (L : MinimalLifeState) :
    bondCount L.Z L.N L.e ≥ 2 := by
  have := L.has_proton; have := L.has_neutron; have := L.has_electron
  unfold bondCount; omega

theorem minimalLife_minimum_exists :
    ∃ L : MinimalLifeState, bondCount L.Z L.N L.e = 2 :=
  ⟨⟨1, 1, 1, le_refl 1, le_refl 1, le_refl 1⟩, rfl⟩

theorem minimalLife_minimum_unique (L : MinimalLifeState)
    (hmin : bondCount L.Z L.N L.e = 2) :
    L.Z = 1 ∧ L.N = 1 ∧ L.e = 1 := by
  have := L.has_proton; have := L.has_neutron; have := L.has_electron
  unfold bondCount at hmin; omega

/-! ## Section 3: The Deuterium Atom — First Life State

Deuterium atom has FDim = dimDeuteriumAtom, distinct from all
elementary particles and from simpler hydrogen species. -/

theorem deuterium_is_minimal_life :
    dimDeuteriumAtom ≠ dimProton ∧
    dimDeuteriumAtom ≠ dimNeutron ∧
    dimDeuteriumAtom ≠ dimElectron := by decide

theorem deuterium_ne_hydrogen :
    dimDeuteriumAtom ≠ dimHydrogenAtom := by decide

/-! ## Section 4: Effective Degree Structure

Deuterium has effectiveDegree 34 = 17 + 16 + 3 - 2.
Each bond lowers the effective degree by 1 from the free sum. -/

theorem deuterium_effectiveDegree :
    dimDeuteriumAtom.effectiveDegree = 34 := by decide

theorem deuterium_lower_than_free_sum :
    dimDeuteriumAtom.effectiveDegree <
      dimProton.effectiveDegree + dimNeutron.effectiveDegree +
      dimElectron.effectiveDegree := by decide

/-! ## Section 5: Genetic Code Connection

bondCount(1,1,1) = 2, spatialDim = 3, codonLength = 3. -/

theorem minimalLife_bonds_eq_two :
    bondCount 1 1 1 = 2 := rfl

-- 2^deg = nuclearMagic(1) = 8
theorem two_pow_spatialDim :
    2 ^ WaveEquation.spatialDim = Nuclear.nuclearMagic 1 := rfl

-- baseCount^codonLength = codonCount = 64
theorem baseCount_pow_codonLength :
    baseCount ^ codonLength = codonCount := rfl

/-! ## Section 6: Information Content Hierarchy -/

abbrev infoContent (n : ℕ) : ℕ := Nat.choose n 2

theorem info_D2 : infoContent 2 = 1 := rfl
theorem info_D3 : infoContent 3 = 3 := rfl
theorem info_D4 : infoContent 4 = 6 := rfl
theorem info_D5 : infoContent 5 = 10 := rfl
theorem info_D6 : infoContent 6 = 15 := rfl

theorem info_monotone :
    infoContent 2 < infoContent 3 ∧
    infoContent 3 < infoContent 4 ∧
    infoContent 4 < infoContent 5 ∧
    infoContent 5 < infoContent 6 := by decide

-- Minimal life info = spatialDim = 3
theorem minimalLife_info : infoContent 3 = WaveEquation.spatialDim := rfl

/-! ## Section 7: φ-Evolution and Time Direction -/

theorem life_requires_time_direction :
    (φ > 1) ∧ (|ψ| < 1) ∧ (φ * |ψ| = 1) :=
  FUST.TimeTheorem.time_direction_unique

/-! ## Section 8: Summary -/

theorem minimal_life_classification :
    (∀ L : MinimalLifeState, bondCount L.Z L.N L.e ≥ 2) ∧
    (∃ L : MinimalLifeState, bondCount L.Z L.N L.e = 2) ∧
    (∀ L : MinimalLifeState, bondCount L.Z L.N L.e = 2 →
      L.Z = 1 ∧ L.N = 1 ∧ L.e = 1) ∧
    dimDeuteriumAtom ≠ dimProton ∧
    baseCount ^ codonLength = codonCount ∧
    (φ > 1 ∧ |ψ| < 1) := by
  exact ⟨minimalLife_bondCount_ge_two,
         minimalLife_minimum_exists,
         minimalLife_minimum_unique,
         by decide,
         rfl,
         FUST.TimeTheorem.phi_unique_expansion⟩

end FUST.Biology
