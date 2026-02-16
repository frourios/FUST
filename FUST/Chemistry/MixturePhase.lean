/-
Mixture State Functions and Phase Decomposition

A system of molecules has a total state function G(x) = Π gᵢ(x)^nᵢ.
Phase decomposition = partition of molecule counts among phases.
The polynomial G(x) is phase-independent: g^(a+b+c) = g^a · g^b · g^c.

Key formalization: a glass with ice, water, and steam is described by
a single state function g_H₂O^N with a partition N = N_s + N_l + N_g.
-/

import FUST.Chemistry.WaterMolecules

namespace FUST.Chemistry.MixturePhase

open FUST FUST.Chemistry.Oxygen

/-! ## Section 1: Species and Mixture

A species is identified by its particle counts (Z, N, e).
A mixture is a list of (species, count) pairs.
-/

structure Species where
  Z : ℕ
  N : ℕ
  e : ℕ
  deriving DecidableEq, Repr

noncomputable def Species.stateFn (sp : Species) : ℝ → ℝ := atomStateFn sp.Z sp.N sp.e

def Species.degree (sp : Species) : ℕ := atomDegree sp.Z sp.N sp.e

-- Standard species
def water_sp : Species := ⟨10, 8, 10⟩
def heavyWater_sp : Species := ⟨10, 10, 10⟩
def dioxygen_sp : Species := ⟨16, 16, 16⟩

theorem water_sp_degree : water_sp.degree = 28 := rfl
theorem heavyWater_sp_degree : heavyWater_sp.degree = 30 := rfl

/-! ## Section 2: System State Function

The system state function is the product of species state functions.
For N identical molecules: G(x) = g(x)^N.
-/

noncomputable def systemStateFn (sp : Species) (n : ℕ) (x : ℝ) : ℝ :=
  sp.stateFn x ^ n

def systemDegree (sp : Species) (n : ℕ) : ℕ := sp.degree * n

-- Degree is multiplicative
theorem systemDegree_eq (sp : Species) (n : ℕ) :
    systemDegree sp n = atomDegree sp.Z sp.N sp.e * n := rfl

/-! ## Section 3: Phase Decomposition

A phase decomposition partitions N molecules into phases.
The key theorem: the total state function is phase-independent.
-/

structure PhasePartition where
  solid : ℕ
  liquid : ℕ
  gas : ℕ

def PhasePartition.total (p : PhasePartition) : ℕ := p.solid + p.liquid + p.gas

-- Phase-decomposed state function = product of phase contributions
noncomputable def phaseStateFn (sp : Species) (p : PhasePartition) (x : ℝ) : ℝ :=
  sp.stateFn x ^ p.solid * sp.stateFn x ^ p.liquid * sp.stateFn x ^ p.gas

-- CORE THEOREM: phase decomposition is phase-independent
-- g^(a+b+c) = g^a · g^b · g^c
theorem phase_independent (sp : Species) (p : PhasePartition) (x : ℝ) :
    systemStateFn sp p.total x = phaseStateFn sp p x := by
  unfold systemStateFn phaseStateFn PhasePartition.total
  rw [pow_add, pow_add]

-- Degree is also phase-independent
theorem degree_phase_independent (sp : Species) (p : PhasePartition) :
    systemDegree sp p.total =
    systemDegree sp p.solid + systemDegree sp p.liquid + systemDegree sp p.gas := by
  unfold systemDegree PhasePartition.total; ring

/-! ## Section 4: Water Triple Point

At the triple point, ice + liquid water + steam coexist.
This is a partition N = N_s + N_l + N_g with all three nonzero.
-/

def triplePointPartition (n_s n_l n_g : ℕ) (_ : n_s > 0) (_ : n_l > 0) (_ : n_g > 0) :
    PhasePartition := ⟨n_s, n_l, n_g⟩

-- Example: 100 molecules partitioned as 30 ice + 60 liquid + 10 steam
def exampleTriplePoint : PhasePartition := ⟨30, 60, 10⟩

theorem exampleTriplePoint_total : exampleTriplePoint.total = 100 := rfl

theorem exampleTriplePoint_degree :
    systemDegree water_sp exampleTriplePoint.total = 2800 := rfl

-- The state function is the same regardless of partition
theorem triplePoint_eq_bulk (n_s n_l n_g : ℕ) (x : ℝ) :
    systemStateFn water_sp (n_s + n_l + n_g) x =
    phaseStateFn water_sp ⟨n_s, n_l, n_g⟩ x :=
  phase_independent water_sp ⟨n_s, n_l, n_g⟩ x

/-! ## Section 5: Mixed Species Systems

Salt water: NaCl dissolved in water. Multiple species coexist.
The system state function is the product over all species.
-/

noncomputable def mixedSystemStateFn (species : List (Species × ℕ)) (x : ℝ) : ℝ :=
  species.foldl (fun acc ⟨sp, n⟩ => acc * sp.stateFn x ^ n) 1

def mixedSystemDegree (species : List (Species × ℕ)) : ℕ :=
  species.foldl (fun acc ⟨sp, n⟩ => acc + sp.degree * n) 0

-- Two-component mixture: degree is additive
theorem binary_mixture_degree (sp₁ sp₂ : Species) (n₁ n₂ : ℕ) :
    mixedSystemDegree [(sp₁, n₁), (sp₂, n₂)] =
    sp₁.degree * n₁ + sp₂.degree * n₂ := by
  simp [mixedSystemDegree, Species.degree]

/-! ## Section 6: Gibbs Phase Rule

F = C - P + 2, where C = components, P = phases, F = degrees of freedom.
At the triple point of water: C=1, P=3, F=0 (unique T, P).
-/

def gibbsDOF (components phases : ℕ) : ℤ := components - phases + 2

theorem gibbs_one_phase : gibbsDOF 1 1 = 2 := rfl
theorem gibbs_two_phase : gibbsDOF 1 2 = 1 := rfl
theorem gibbs_triple_point : gibbsDOF 1 3 = 0 := rfl

-- Maximum phases for C components: P ≤ C + 2 (when F ≥ 0)
theorem gibbs_max_phases (C P : ℕ) (hF : gibbsDOF C P ≥ 0) : P ≤ C + 2 := by
  unfold gibbsDOF at hF; omega

-- For pure water (C=1): at most 3 phases
theorem water_max_phases (P : ℕ) (hF : gibbsDOF 1 P ≥ 0) : P ≤ 3 := by
  have := gibbs_max_phases 1 P hF; omega

/-! ## Section 7: State Function Roots

g_H₂O(x) = x^10 · (1+x)^8 · (1+ψx)^10 has three families of roots:
x = 0 (mult Z), x = -1 (mult N), x = -1/ψ = φ (mult e).
These are phase-independent — the same molecule in all phases.
-/

-- The three root locations
theorem root_at_zero (Z N e : ℕ) (hZ : Z ≥ 1) :
    atomStateFn Z N e 0 = 0 := by
  unfold atomStateFn; simp [zero_pow (by omega : Z ≠ 0)]

theorem root_at_neg_one (Z N e : ℕ) (hN : N ≥ 1) :
    atomStateFn Z N e (-1) = 0 := by
  unfold atomStateFn; simp [zero_pow (by omega : N ≠ 0)]

-- x = φ is a root when e ≥ 1, since 1 + ψ·φ = 1 + φψ = 1 + (-1) = 0
theorem root_at_phi (Z N e : ℕ) (he : e ≥ 1) :
    atomStateFn Z N e φ = 0 := by
  unfold atomStateFn
  have : 1 + ψ * φ = 0 := by linarith [phi_mul_psi]
  simp [this, zero_pow (by omega : e ≠ 0)]

-- Root multiplicities for water
theorem water_root_multiplicities :
    water_sp.Z = 10 ∧ water_sp.N = 8 ∧ water_sp.e = 10 := ⟨rfl, rfl, rfl⟩

/-! ## Section 8: Phase Transition as Repartition

A phase transition is a change in partition while preserving total count.
Melting: (N_s, N_l, N_g) → (N_s - k, N_l + k, N_g) for some k.
The state function polynomial is INVARIANT under phase transitions.
-/

-- Melting: move k molecules from solid to liquid
def melt (p : PhasePartition) (k : ℕ) : PhasePartition :=
  ⟨p.solid - k, p.liquid + k, p.gas⟩

-- Evaporation: move k molecules from liquid to gas
def evaporate (p : PhasePartition) (k : ℕ) : PhasePartition :=
  ⟨p.solid, p.liquid - k, p.gas + k⟩

-- Sublimation: move k molecules from solid to gas
def sublimate (p : PhasePartition) (k : ℕ) : PhasePartition :=
  ⟨p.solid - k, p.liquid, p.gas + k⟩

-- Phase transitions preserve total count
theorem melt_preserves_total (p : PhasePartition) (k : ℕ) (hk : k ≤ p.solid) :
    (melt p k).total = p.total := by
  simp [melt, PhasePartition.total]; omega

theorem evaporate_preserves_total (p : PhasePartition) (k : ℕ) (hk : k ≤ p.liquid) :
    (evaporate p k).total = p.total := by
  simp [evaporate, PhasePartition.total]; omega

theorem sublimate_preserves_total (p : PhasePartition) (k : ℕ) (hk : k ≤ p.solid) :
    (sublimate p k).total = p.total := by
  simp [sublimate, PhasePartition.total]; omega

-- STATE FUNCTION INVARIANCE under phase transition
theorem melt_stateFn_invariant (sp : Species) (p : PhasePartition) (k : ℕ)
    (hk : k ≤ p.solid) (x : ℝ) :
    systemStateFn sp (melt p k).total x = systemStateFn sp p.total x := by
  rw [melt_preserves_total _ _ hk]

theorem evaporate_stateFn_invariant (sp : Species) (p : PhasePartition) (k : ℕ)
    (hk : k ≤ p.liquid) (x : ℝ) :
    systemStateFn sp (evaporate p k).total x = systemStateFn sp p.total x := by
  rw [evaporate_preserves_total _ _ hk]

/-! ## Section 9: Summary -/

theorem mixture_phase_structure :
    -- The state function is phase-independent
    (∀ (n_s n_l n_g : ℕ) (x : ℝ),
      systemStateFn water_sp (n_s + n_l + n_g) x =
      phaseStateFn water_sp ⟨n_s, n_l, n_g⟩ x) ∧
    -- Water degree = 28 per molecule
    water_sp.degree = 28 ∧
    -- Gibbs: pure water has at most 3 coexisting phases
    (∀ P, gibbsDOF 1 P ≥ 0 → P ≤ 3) ∧
    -- State function has 3 root families at 0, -1, φ
    atomStateFn 10 8 10 0 = 0 ∧
    atomStateFn 10 8 10 (-1) = 0 ∧
    atomStateFn 10 8 10 φ = 0 := by
  refine ⟨triplePoint_eq_bulk, rfl, water_max_phases, ?_, ?_, ?_⟩
  · exact root_at_zero 10 8 10 (by omega)
  · exact root_at_neg_one 10 8 10 (by omega)
  · exact root_at_phi 10 8 10 (by omega)

end FUST.Chemistry.MixturePhase
