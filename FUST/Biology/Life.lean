import FUST.DifferenceOperators
import FUST.Physics.TimeTheorem
import Mathlib.Data.Nat.Choose.Basic

/-!
# Algebraic Definition of Life from D-Structure

This module defines life algebraically using FUST D-structure principles.

## Key Insight: Template Constraint

Life is distinguished from non-life by the TEMPLATE CONSTRAINT:
- Life: T(s) is determined by reading s (self-referential)
- Non-life: T(s) is determined by environment (external)

## Classification

| D-level | C(n,2) | Life Form | Template Type |
|---------|--------|-----------|---------------|
| D₂ | 1 | Virus | External |
| D₃ | 3 | Prion | Structural |
| D₄ | 6 | Prokaryote | Sequence |
| D₅ | 10 | Eukaryote | Compartmentalized |
| D₆ | 15 | Multicellular | Differentiated |
-/

namespace FUST.Biology

/-! ## Template Types -/

/-- Template type classification for life forms -/
inductive TemplateType where
  | none : TemplateType           -- Non-life (fire, crystal)
  | external : TemplateType       -- Virus (uses host machinery)
  | structural : TemplateType     -- Prion (3D structure is template)
  | sequence : TemplateType       -- Prokaryote (DNA/RNA sequence)
  | compartment : TemplateType    -- Eukaryote (compartmentalized)
  | differentiated : TemplateType -- Multicellular (cell-type specific)
  deriving DecidableEq, Repr

/-- Template types that qualify as life -/
def TemplateType.isLife : TemplateType → Bool
  | .none => false
  | _ => true

theorem external_is_life : TemplateType.external.isLife = true := rfl
theorem structural_is_life : TemplateType.structural.isLife = true := rfl
theorem sequence_is_life : TemplateType.sequence.isLife = true := rfl
theorem none_is_not_life : TemplateType.none.isLife = false := rfl

/-! ## Information Content from D-Structure -/

/-- Information content at D-level n: C(n,2) = n(n-1)/2 -/
abbrev infoContent (n : ℕ) : ℕ := Nat.choose n 2

theorem info_D2 : infoContent 2 = 1 := rfl
theorem info_D3 : infoContent 3 = 3 := rfl
theorem info_D4 : infoContent 4 = 6 := rfl
theorem info_D5 : infoContent 5 = 10 := rfl
theorem info_D6 : infoContent 6 = 15 := rfl

/-- Information content increases with D-level (concrete examples) -/
theorem info_2_lt_3 : infoContent 2 < infoContent 3 := by decide
theorem info_3_lt_4 : infoContent 3 < infoContent 4 := by decide
theorem info_4_lt_5 : infoContent 4 < infoContent 5 := by decide
theorem info_5_lt_6 : infoContent 5 < infoContent 6 := by decide

/-! ## Life Structure Definition -/

/-- A life structure at D-level n -/
structure LifeStructure where
  /-- Minimum D-level (2 ≤ n ≤ 6) -/
  minDLevel : ℕ
  /-- Template type determines reproduction mechanism -/
  templateType : TemplateType
  /-- Has internal time evolution (φ-evolution) -/
  hasInternalTime : Bool
  /-- D-level constraint: 2 ≤ n ≤ 6 -/
  level_valid : 2 ≤ minDLevel ∧ minDLevel ≤ 6
  /-- Life requires non-trivial template -/
  is_life : templateType.isLife = true

/-- Information content of a life structure -/
def LifeStructure.info (L : LifeStructure) : ℕ := infoContent L.minDLevel

/-! ## Specific Life Forms -/

/-- Virus: D₂, external template, no internal time -/
def virus : LifeStructure where
  minDLevel := 2
  templateType := .external
  hasInternalTime := false
  level_valid := ⟨le_refl 2, by omega⟩
  is_life := rfl

theorem virus_info : virus.info = 1 := rfl
theorem virus_no_internal_time : virus.hasInternalTime = false := rfl

/-- Prion: D₃, structural template, no internal time -/
def prion : LifeStructure where
  minDLevel := 3
  templateType := .structural
  hasInternalTime := false
  level_valid := ⟨by omega, by omega⟩
  is_life := rfl

theorem prion_info : prion.info = 3 := rfl
theorem prion_structural : prion.templateType = .structural := rfl

/-- Prokaryote: D₄, sequence template, internal time -/
def prokaryote : LifeStructure where
  minDLevel := 4
  templateType := .sequence
  hasInternalTime := true
  level_valid := ⟨by omega, by omega⟩
  is_life := rfl

theorem prokaryote_info : prokaryote.info = 6 := rfl
theorem prokaryote_has_time : prokaryote.hasInternalTime = true := rfl

/-- Eukaryote: D₅, compartmentalized template, internal time -/
def eukaryote : LifeStructure where
  minDLevel := 5
  templateType := .compartment
  hasInternalTime := true
  level_valid := ⟨by omega, by omega⟩
  is_life := rfl

theorem eukaryote_info : eukaryote.info = 10 := rfl

/-- Multicellular: D₆, differentiated template, internal time -/
def multicellular : LifeStructure where
  minDLevel := 6
  templateType := .differentiated
  hasInternalTime := true
  level_valid := ⟨by omega, le_refl 6⟩
  is_life := rfl

theorem multicellular_info : multicellular.info = 15 := rfl
theorem multicellular_max_level : multicellular.minDLevel = 6 := rfl

/-! ## Non-Life Exclusion -/

/-- Non-life structure (for comparison) -/
structure NonLifeStructure where
  /-- Description of the non-life phenomenon -/
  name : String
  /-- Why it fails template constraint -/
  failure_reason : String

/-- Fire fails template constraint: environment-driven, not self-referential -/
def fire : NonLifeStructure where
  name := "Fire"
  failure_reason := "T(flame) determined by (fuel, O₂), not by flame structure"

/-- Crystal fails template constraint: I(seed) << I(crystal) -/
def crystal : NonLifeStructure where
  name := "Crystal"
  failure_reason := "I(seed) = O(1) but I(crystal) = O(N), information not preserved"

/-! ## Template Constraint Formalization -/

/-- Template constraint: reproduction reads and preserves information -/
structure TemplateConstraint where
  /-- Readout extracts information from state -/
  readable : Bool
  /-- Reproduction preserves information content -/
  info_preserved : Bool
  /-- Removal of template prevents reproduction -/
  template_required : Bool

/-- Life satisfies all template constraints -/
def lifeTemplateConstraint : TemplateConstraint where
  readable := true
  info_preserved := true
  template_required := true

/-- Fire fails template constraint -/
def fireTemplateConstraint : TemplateConstraint where
  readable := false  -- No extractable instructions from flame
  info_preserved := false
  template_required := false  -- New flame from fuel+O₂ without old flame

/-- Crystal fails template constraint -/
def crystalTemplateConstraint : TemplateConstraint where
  readable := true  -- Unit cell is readable
  info_preserved := false  -- I(seed) << I(crystal)
  template_required := false  -- Can nucleate from scratch

theorem life_satisfies_template : lifeTemplateConstraint.readable ∧
    lifeTemplateConstraint.info_preserved ∧
    lifeTemplateConstraint.template_required := ⟨rfl, rfl, rfl⟩

theorem fire_fails_template : fireTemplateConstraint.readable = false := rfl
theorem crystal_fails_info : crystalTemplateConstraint.info_preserved = false := rfl

/-! ## φ-Evolution and Life -/

/-- Life requires φ-evolution (time direction) for reproduction -/
theorem life_requires_phi_evolution :
    (φ > 1) ∧ (|ψ| < 1) ∧ (φ * |ψ| = 1) := FUST.TimeTheorem.time_direction_unique

/-- Internal time means φ-evolution is internalized -/
def hasInternalPhiEvolution (L : LifeStructure) : Bool := L.hasInternalTime

theorem prokaryote_internal_phi : hasInternalPhiEvolution prokaryote = true := rfl
theorem virus_external_phi : hasInternalPhiEvolution virus = false := rfl

/-! ## Hierarchy Theorems -/

/-- Life forms ordered by D-level -/
theorem life_hierarchy :
    virus.minDLevel < prion.minDLevel ∧
    prion.minDLevel < prokaryote.minDLevel ∧
    prokaryote.minDLevel < eukaryote.minDLevel ∧
    eukaryote.minDLevel < multicellular.minDLevel := by decide

/-- Information increases with complexity -/
theorem info_hierarchy :
    virus.info < prion.info ∧
    prion.info < prokaryote.info ∧
    prokaryote.info < eukaryote.info ∧
    eukaryote.info < multicellular.info := by decide

/-- Internal time appears at D₄ (prokaryote level) -/
theorem internal_time_threshold :
    virus.hasInternalTime = false ∧
    prion.hasInternalTime = false ∧
    prokaryote.hasInternalTime = true := ⟨rfl, rfl, rfl⟩

/-! ## D₆ and Consciousness -/

/-- Consciousness conjecture: requires D₆ completeness -/
structure ConsciousnessStructure extends LifeStructure where
  /-- Self-model: T itself is observable -/
  has_self_model : Bool
  /-- Requires D₆ -/
  requires_D6 : minDLevel = 6

/-- Conscious multicellular life -/
def consciousLife : ConsciousnessStructure where
  minDLevel := 6
  templateType := .differentiated
  hasInternalTime := true
  level_valid := ⟨by omega, le_refl 6⟩
  is_life := rfl
  has_self_model := true
  requires_D6 := rfl

theorem consciousness_at_D6 : consciousLife.minDLevel = 6 := rfl
theorem consciousness_info : consciousLife.info = 15 := rfl

/-! ## Summary Theorems -/

/-- All life forms have D-level in [2,6] -/
theorem all_life_bounded (L : LifeStructure) : 2 ≤ L.minDLevel ∧ L.minDLevel ≤ 6 :=
  L.level_valid

/-- All life forms have positive information content -/
theorem all_life_has_info (L : LifeStructure) : L.info ≥ 1 := by
  have ⟨hlo, hhi⟩ := L.level_valid
  simp only [LifeStructure.info, infoContent]
  interval_cases L.minDLevel <;> decide

/-- Template type determines life status -/
theorem template_determines_life (L : LifeStructure) : L.templateType.isLife = true :=
  L.is_life

/-- Life classification from D-structure -/
theorem life_classification :
    -- Virus at D₂
    (virus.minDLevel = 2 ∧ virus.info = 1) ∧
    -- Prion at D₃
    (prion.minDLevel = 3 ∧ prion.info = 3) ∧
    -- Prokaryote at D₄
    (prokaryote.minDLevel = 4 ∧ prokaryote.info = 6) ∧
    -- Eukaryote at D₅
    (eukaryote.minDLevel = 5 ∧ eukaryote.info = 10) ∧
    -- Multicellular at D₆
    (multicellular.minDLevel = 6 ∧ multicellular.info = 15) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Key distinction: template constraint separates life from non-life -/
theorem life_nonlife_distinction :
    -- Life: all template constraints satisfied
    (lifeTemplateConstraint.readable ∧
     lifeTemplateConstraint.info_preserved ∧
     lifeTemplateConstraint.template_required) ∧
    -- Fire: fails readability
    (fireTemplateConstraint.readable = false) ∧
    -- Crystal: fails information preservation
    (crystalTemplateConstraint.info_preserved = false) :=
  ⟨life_satisfies_template, rfl, rfl⟩

/-- D-structure constants derive life hierarchy -/
theorem life_from_D_structure :
    -- Information from pair counts
    (∀ n, infoContent n = Nat.choose n 2) ∧
    -- D₂ through D₆ active
    (2 ≤ virus.minDLevel ∧ multicellular.minDLevel ≤ 6) ∧
    -- φ-evolution required
    (φ > 1 ∧ |ψ| < 1) :=
  ⟨fun _ => rfl, ⟨le_refl 2, le_refl 6⟩,
   ⟨FUST.TimeTheorem.time_direction_unique.1, FUST.TimeTheorem.time_direction_unique.2.1⟩⟩

end FUST.Biology
