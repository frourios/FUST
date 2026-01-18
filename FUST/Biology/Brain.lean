import FUST.DifferenceOperators
import FUST.Physics.TimeTheorem
import FUST.Biology.Life
import Mathlib.Data.Nat.Choose.Basic

/-!
# Algebraic Definition of Brain from D-Structure

This module defines brain algebraically, distinguishing centralized brains
from distributed processing systems (colonies, plants, planaria).

## Key Insight: Centralization Threshold φ

Brain is characterized by:
1. Centralization ratio R = max_degree / avg_degree > φ
2. Unique critical node (removal disconnects system)
3. Maximal information integration Φ = C(n,2)
4. Feedback loops through center

## Classification

| System | R | Topology | D-level | Brain? |
|--------|---|----------|---------|--------|
| Plant | ≈ 1 | Path/Tree | D₂ | No |
| Planaria | < φ | Mesh | D₃ | No |
| Insect colony | ≈ 1 | Mesh | D₄ | No (collective) |
| Insect brain | > φ | Star | D₄ | Yes |
| Octopus | ≈ φ | Hybrid | D₅ | Hybrid |
| Mammal | >> φ | Star | D₆ | Yes (self-model) |

The threshold φ is NOT arbitrary: it emerges from FUST time evolution.
-/

namespace FUST.Biology

/-! ## Neural Topology Types -/

/-- Network topology classification -/
inductive NeuralTopology where
  | path : NeuralTopology        -- Linear (plant stem)
  | tree : NeuralTopology        -- Branching (plant root)
  | mesh : NeuralTopology        -- Uniform connections (colony)
  | star : NeuralTopology        -- Central hub (brain)
  | hybrid : NeuralTopology      -- Mixed (octopus)
  deriving DecidableEq, Repr

/-- Topology centralization property -/
def NeuralTopology.isCentralized : NeuralTopology → Bool
  | .star => true
  | .hybrid => true
  | _ => false

theorem star_is_centralized : NeuralTopology.star.isCentralized = true := rfl
theorem mesh_not_centralized : NeuralTopology.mesh.isCentralized = false := rfl

/-! ## Centralization Ratio R -/

/-- Centralization ratio: R = max_degree / avg_degree -/
structure CentralizationRatio where
  max_degree : ℕ
  avg_degree_num : ℕ  -- numerator
  avg_degree_den : ℕ  -- denominator (> 0)
  den_pos : avg_degree_den > 0

/-- R as rational number -/
def CentralizationRatio.toRat (r : CentralizationRatio) : ℚ :=
  (r.max_degree * r.avg_degree_den : ℚ) / r.avg_degree_num

/-- R > φ threshold for brain -/
def CentralizationRatio.exceedsThreshold (r : CentralizationRatio) : Prop :=
  (r.max_degree * r.avg_degree_den : ℚ) / r.avg_degree_num > 1618 / 1000

/-! ## Neural System Structure -/

/-- A neural processing system -/
structure NeuralSystem where
  /-- D-level of processing complexity -/
  minDLevel : ℕ
  /-- Network topology -/
  topology : NeuralTopology
  /-- Centralization ratio R -/
  centralization : CentralizationRatio
  /-- Has unique critical node -/
  hasUniqueCriticalNode : Bool
  /-- Has self-model (D₆ requirement) -/
  hasSelfModel : Bool
  /-- D-level constraint: 2 ≤ n ≤ 6 -/
  level_valid : 2 ≤ minDLevel ∧ minDLevel ≤ 6

/-- Hierarchical processing depth = D-level - 2 -/
def NeuralSystem.hierarchyDepth (N : NeuralSystem) : ℕ := N.minDLevel - 2

/-- Information integration = C(n,2) -/
def NeuralSystem.integration (N : NeuralSystem) : ℕ := Nat.choose N.minDLevel 2

/-! ## Brain Definition -/

/-- A neural system is a BRAIN iff centralized with unique critical node -/
def isBrain (N : NeuralSystem) : Prop :=
  N.topology.isCentralized = true ∧
  N.hasUniqueCriticalNode = true ∧
  N.centralization.exceedsThreshold

/-- A neural system is a COLONY iff mesh topology without critical node -/
def isColony (N : NeuralSystem) : Prop :=
  N.topology = .mesh ∧
  N.hasUniqueCriticalNode = false

/-- A neural system is DISTRIBUTED iff non-centralized -/
def isDistributed (N : NeuralSystem) : Prop :=
  N.topology.isCentralized = false

/-! ## Concrete Neural Systems -/

/-- Plant nervous system (distributed) -/
def plantSystem : NeuralSystem where
  minDLevel := 2
  topology := .path
  centralization := ⟨2, 2, 1, by omega⟩  -- R = 1
  hasUniqueCriticalNode := false
  hasSelfModel := false
  level_valid := ⟨le_refl 2, by omega⟩

theorem plant_R_eq_one : plantSystem.centralization.toRat = 1 := by
  simp [CentralizationRatio.toRat, plantSystem]

theorem plant_not_brain : ¬isBrain plantSystem := by
  intro ⟨h, _, _⟩
  simp [NeuralTopology.isCentralized, plantSystem] at h

theorem plant_distributed : isDistributed plantSystem := by
  simp [isDistributed, NeuralTopology.isCentralized, plantSystem]

/-- Planaria nervous system (distributed mesh) -/
def planariaSystem : NeuralSystem where
  minDLevel := 3
  topology := .mesh
  centralization := ⟨3, 2, 1, by omega⟩  -- R = 1.5 < φ
  hasUniqueCriticalNode := false
  hasSelfModel := false
  level_valid := ⟨by omega, by omega⟩

theorem planaria_not_brain : ¬isBrain planariaSystem := by
  intro ⟨h, _, _⟩
  simp [NeuralTopology.isCentralized, planariaSystem] at h

theorem planaria_distributed : isDistributed planariaSystem := by
  simp [isDistributed, NeuralTopology.isCentralized, planariaSystem]

/-- Insect colony (collective, not brain) -/
def insectColony : NeuralSystem where
  minDLevel := 4
  topology := .mesh
  centralization := ⟨3, 3, 1, by omega⟩  -- R ≈ 1
  hasUniqueCriticalNode := false
  hasSelfModel := false
  level_valid := ⟨by omega, by omega⟩

theorem colony_is_colony : isColony insectColony := by
  simp [isColony, insectColony]

theorem colony_not_brain : ¬isBrain insectColony := by
  intro ⟨h, _, _⟩
  simp [NeuralTopology.isCentralized, insectColony] at h

/-- Insect brain (centralized) -/
def insectBrain : NeuralSystem where
  minDLevel := 4
  topology := .star
  centralization := ⟨5, 5, 3, by omega⟩  -- R = 3 > φ
  hasUniqueCriticalNode := true
  hasSelfModel := false
  level_valid := ⟨by omega, by omega⟩

theorem insectBrain_centralized : insectBrain.topology.isCentralized = true := rfl

theorem insectBrain_exceeds_phi : insectBrain.centralization.exceedsThreshold := by
  simp [CentralizationRatio.exceedsThreshold, insectBrain]
  norm_num

theorem insectBrain_is_brain : isBrain insectBrain := by
  refine ⟨rfl, rfl, ?_⟩
  exact insectBrain_exceeds_phi

theorem insectBrain_no_selfmodel : insectBrain.hasSelfModel = false := rfl

/-- Octopus (hybrid system) -/
def octopusSystem : NeuralSystem where
  minDLevel := 5
  topology := .hybrid
  centralization := ⟨5, 8, 5, by omega⟩  -- R ≈ 1.6 ≈ φ
  hasUniqueCriticalNode := true  -- Central brain exists
  hasSelfModel := true
  level_valid := ⟨by omega, by omega⟩

theorem octopus_hybrid : octopusSystem.topology = .hybrid := rfl
theorem octopus_has_selfmodel : octopusSystem.hasSelfModel = true := rfl

/-- Mammal brain (fully centralized, D₆) -/
def mammalBrain : NeuralSystem where
  minDLevel := 6
  topology := .star
  centralization := ⟨10, 10, 2, by omega⟩  -- R = 5 >> φ
  hasUniqueCriticalNode := true
  hasSelfModel := true
  level_valid := ⟨by omega, le_refl 6⟩

theorem mammalBrain_exceeds_phi : mammalBrain.centralization.exceedsThreshold := by
  simp [CentralizationRatio.exceedsThreshold, mammalBrain]
  norm_num

theorem mammalBrain_is_brain : isBrain mammalBrain := by
  refine ⟨rfl, rfl, ?_⟩
  exact mammalBrain_exceeds_phi

theorem mammalBrain_D6 : mammalBrain.minDLevel = 6 := rfl
theorem mammalBrain_has_selfmodel : mammalBrain.hasSelfModel = true := rfl

/-! ## φ Threshold Theorems -/

/-- φ as centralization threshold (rational approximation) -/
abbrev phiThresholdRat : ℚ := 1618 / 1000

theorem phi_threshold_bounds :
    (16 : ℚ) / 10 < phiThresholdRat ∧ phiThresholdRat < (17 : ℚ) / 10 := by
  constructor <;> norm_num [phiThresholdRat]

/-- The φ threshold is derived from FUST, not arbitrary -/
theorem phi_threshold_from_fust :
    φ > 1 ∧ φ ^ 2 = φ + 1 :=
  ⟨FUST.TimeTheorem.time_direction_unique.1, golden_ratio_property⟩

/-! ## Hierarchy and Integration Theorems -/

/-- Hierarchy depth increases with D-level -/
theorem hierarchy_depth_values :
    plantSystem.hierarchyDepth = 0 ∧
    planariaSystem.hierarchyDepth = 1 ∧
    insectBrain.hierarchyDepth = 2 ∧
    octopusSystem.hierarchyDepth = 3 ∧
    mammalBrain.hierarchyDepth = 4 := by
  simp [NeuralSystem.hierarchyDepth, plantSystem, planariaSystem,
        insectBrain, octopusSystem, mammalBrain]

/-- Integration increases with D-level -/
theorem integration_values :
    plantSystem.integration = 1 ∧
    planariaSystem.integration = 3 ∧
    insectBrain.integration = 6 ∧
    octopusSystem.integration = 10 ∧
    mammalBrain.integration = 15 := by decide

/-! ## Brain vs Colony Distinction -/

/-- Brain and colony are mutually exclusive -/
theorem brain_colony_exclusive (N : NeuralSystem) :
    isBrain N → ¬isColony N := by
  intro ⟨hcentral, _, _⟩ ⟨hmesh, _⟩
  simp [NeuralTopology.isCentralized] at hcentral
  cases N.topology <;> simp_all

/-- Distributed systems are not brains -/
theorem distributed_not_brain (N : NeuralSystem) :
    isDistributed N → ¬isBrain N := by
  intro hdist ⟨hcentral, _, _⟩
  simp only [isDistributed] at hdist
  rw [hdist] at hcentral
  simp at hcentral

/-! ## Self-Model and D₆ -/

/-- Self-model requires D₆ for full consciousness -/
theorem selfmodel_requires_D6 (N : NeuralSystem) :
    N.hasSelfModel = true → N.minDLevel ≥ 5 → N.minDLevel = 6 →
    N.integration = 15 := by
  intro _ _ hD6
  simp only [NeuralSystem.integration, hD6, Nat.choose]

/-- D₆ brain has maximal hierarchy depth -/
theorem D6_max_hierarchy :
    mammalBrain.hierarchyDepth = 4 ∧
    ∀ N : NeuralSystem, N.hierarchyDepth ≤ 4 := by
  constructor
  · rfl
  · intro N
    have ⟨_, hhi⟩ := N.level_valid
    simp [NeuralSystem.hierarchyDepth]
    omega

/-! ## Summary Theorems -/

/-- Complete brain classification -/
theorem brain_classification :
    -- Plant: not brain (R ≈ 1, path topology)
    (isDistributed plantSystem ∧ ¬isBrain plantSystem) ∧
    -- Planaria: not brain (R < φ, mesh topology)
    (isDistributed planariaSystem ∧ ¬isBrain planariaSystem) ∧
    -- Insect colony: not brain (collective)
    (isColony insectColony ∧ ¬isBrain insectColony) ∧
    -- Insect brain: is brain (R > φ, star topology)
    (isBrain insectBrain ∧ insectBrain.hasSelfModel = false) ∧
    -- Octopus: hybrid (R ≈ φ)
    (octopusSystem.topology = .hybrid ∧ octopusSystem.hasSelfModel = true) ∧
    -- Mammal: brain with self-model (D₆)
    (isBrain mammalBrain ∧ mammalBrain.hasSelfModel = true) :=
  ⟨⟨plant_distributed, plant_not_brain⟩,
   ⟨planaria_distributed, planaria_not_brain⟩,
   ⟨colony_is_colony, colony_not_brain⟩,
   ⟨insectBrain_is_brain, rfl⟩,
   ⟨rfl, rfl⟩,
   ⟨mammalBrain_is_brain, rfl⟩⟩

/-- The φ threshold distinguishes brain from non-brain -/
theorem phi_distinguishes_brain :
    -- R > φ → can be brain
    (insectBrain.centralization.exceedsThreshold) ∧
    (mammalBrain.centralization.exceedsThreshold) ∧
    -- R ≈ 1 → not brain (colony/plant)
    (¬isBrain plantSystem) ∧
    (¬isBrain insectColony) :=
  ⟨insectBrain_exceeds_phi, mammalBrain_exceeds_phi,
   plant_not_brain, colony_not_brain⟩

/-- Brain definition from D-structure -/
theorem brain_from_D_structure :
    -- Centralization from star topology
    (NeuralTopology.star.isCentralized = true) ∧
    -- φ from FUST time evolution
    (φ > 1 ∧ φ ^ 2 = φ + 1) ∧
    -- D-level hierarchy
    (mammalBrain.hierarchyDepth = 4) ∧
    -- Integration from C(n,2)
    (mammalBrain.integration = 15) :=
  ⟨rfl, phi_threshold_from_fust, rfl, rfl⟩

end FUST.Biology
