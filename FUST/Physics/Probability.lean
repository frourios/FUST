import FUST.DifferenceOperators
import FUST.FrourioLogarithm
import FUST.Physics.TimeTheorem
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

/-!
# FUST Probability Theory

Probability emerges structurally from D6 operator and φ-scale iteration.

## Key Results

1. **Theorem 3.1**: Same-degree ratio is gauge-invariant
2. **φ-scale iteration**: Generates observation sequences
3. **Empirical distribution**: Frequency-based probability
4. **Born rule**: Structural consequence of D6 action
-/

namespace FUST.Probability

open FUST FUST.FrourioLogarithm FUST.LeastAction

attribute [local instance] Classical.propDecidable

/-!
## Theorem 3.1: Same-Degree Ratio Gauge Invariance

For same-degree monomials f_A = a·x^n and f_B = b·x^n:
  |D6[f_A](x)| / |D6[f_B](x)| = |a| / |b|

This is independent of x (gauge-invariant).
-/

section SameDegreeRatio

/-- D6 is linear: D6[a·f] = a·D6[f] -/
theorem D6_linear_scalar (a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    D6 (fun t => a * f t) x = a * D6 f x := by
  simp only [D6]
  split_ifs with hx
  · simp
  · ring

/-- Same-degree ratio is gauge-invariant -/
theorem same_degree_ratio_gauge_invariant (a b : ℝ) (f : ℝ → ℝ) (x : ℝ)
    (hb : b ≠ 0) (hfx : D6 f x ≠ 0) :
    |D6 (fun t => a * f t) x| / |D6 (fun t => b * f t) x| = |a| / |b| := by
  rw [D6_linear_scalar, D6_linear_scalar]
  rw [abs_mul, abs_mul]
  have hbfx : |b| * |D6 f x| ≠ 0 := by
    apply mul_ne_zero
    · exact abs_ne_zero.mpr hb
    · exact abs_ne_zero.mpr hfx
  have hafx_eq : |a| * |D6 f x| / (|b| * |D6 f x|) = |a| / |b| := by
    field_simp
  exact hafx_eq

/-- For monomials: D6[a·x^n] / D6[b·x^n] = a/b (when both defined) -/
theorem monomial_ratio_invariant (a b : ℝ) (n : ℕ) (x y : ℝ)
    (hb : b ≠ 0) (_hx : x ≠ 0) (_hy : y ≠ 0) (_hn : n ≥ 3)
    (hfx : D6 (fun t => t ^ n) x ≠ 0) (hfy : D6 (fun t => t ^ n) y ≠ 0) :
    |D6 (fun t => a * t ^ n) x| / |D6 (fun t => b * t ^ n) x| =
    |D6 (fun t => a * t ^ n) y| / |D6 (fun t => b * t ^ n) y| := by
  rw [same_degree_ratio_gauge_invariant a b (fun t => t ^ n) x hb hfx]
  rw [same_degree_ratio_gauge_invariant a b (fun t => t ^ n) y hb hfy]

end SameDegreeRatio

/-!
## φ-Scale Iteration and Observation Sequences

The φ-scale transformation x ↦ φ^k · x generates observation sequences:
  A_f(k) := |D6[f](φ^k · x)|

This corresponds to "trials" in probability theory.
-/

section PhiScaleIteration

/-- Observation value at scale k -/
noncomputable def observationAt (f : ℝ → ℝ) (x₀ : ℝ) (k : ℤ) : ℝ :=
  |D6 f (φ ^ k * x₀)|

/-- Observation sequence is well-defined for x₀ > 0 -/
theorem observationAt_welldefined (_f : ℝ → ℝ) (x₀ : ℝ) (hx₀ : 0 < x₀) (k : ℤ) :
    φ ^ k * x₀ ≠ 0 := by
  apply mul_ne_zero
  · exact zpow_ne_zero k (ne_of_gt phi_pos)
  · exact ne_of_gt hx₀

/-- φ-scaling shifts the observation index -/
theorem observation_shift (f : ℝ → ℝ) (x₀ : ℝ) (_hx₀ : 0 < x₀) (k j : ℤ) :
    observationAt f (φ ^ j * x₀) k = observationAt f x₀ (k + j) := by
  simp only [observationAt]
  congr 2
  have h : φ ^ k * (φ ^ j * x₀) = (φ ^ k * φ ^ j) * x₀ := by ring
  rw [h, ← zpow_add₀ (ne_of_gt phi_pos) k j]

/-- Observation values are non-negative -/
theorem observationAt_nonneg (f : ℝ → ℝ) (x₀ : ℝ) (k : ℤ) :
    observationAt f x₀ k ≥ 0 :=
  abs_nonneg _

end PhiScaleIteration

/-!
## φ-Invariant Measure

The φ-scale invariant measure is uniquely determined:
  dμ = dx/x (Haar measure on multiplicative group)

This is NOT an external assumption but derived from φ-scale structure.
-/

section PhiInvariantMeasure

/-- Haar measure weight at scale k: log(φ) per step -/
noncomputable def haarWeight : ℝ := Real.log φ

/-- Haar weight is positive -/
theorem haarWeight_pos : haarWeight > 0 := by
  unfold haarWeight
  exact Real.log_pos φ_gt_one

/-- φ-scaling preserves the measure (discrete version) -/
theorem phi_scaling_measure_invariant (f : ℝ → ℝ) (x₀ : ℝ) (_hx₀ : 0 < x₀) (N : ℕ) :
    (Finset.Icc (-N : ℤ) N).sum (fun k => (observationAt f x₀ k) ^ 2 * haarWeight) =
    (Finset.Icc (-N : ℤ) N).sum (fun k => (observationAt f (φ * x₀) (k - 1)) ^ 2 * haarWeight) := by
  congr 1
  ext k
  simp only [observationAt]
  congr 3
  have h : φ ^ (k - 1) * (φ * x₀) = φ ^ (k - 1) * φ * x₀ := by ring
  rw [h, ← zpow_add_one₀ (ne_of_gt phi_pos) (k - 1)]
  simp only [sub_add_cancel]

end PhiInvariantMeasure

/-!
## Empirical Distribution (Frequency-Based Probability)

The empirical distribution function:
  ρ_f(t) = lim_{N→∞} (1/(2N+1)) · #{k ∈ [-N,N] | A_f(k) ≤ t}

When this limit exists, it defines the probability intrinsic to state f.
-/

section EmpiricalDistribution

/-- Count of observations below threshold in range [-N, N] -/
noncomputable def countBelow (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (t : ℝ) : ℕ :=
  ((Finset.Icc (-N : ℤ) N).filter (fun k => observationAt f x₀ k ≤ t)).card

/-- Empirical distribution at finite N -/
noncomputable def empiricalDistN (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (countBelow f x₀ N t : ℝ) / (2 * N + 1)

/-- Empirical distribution is in [0, 1] -/
theorem empiricalDistN_bounds (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ empiricalDistN f x₀ N t ∧ empiricalDistN f x₀ N t ≤ 1 := by
  constructor
  · unfold empiricalDistN
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
  · unfold empiricalDistN countBelow
    have hcard : ((Finset.Icc (-N : ℤ) N).filter (fun k => observationAt f x₀ k ≤ t)).card ≤
        (Finset.Icc (-N : ℤ) N).card := Finset.card_filter_le _ _
    have hsize : (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
      rw [Int.card_Icc]
      simp only [sub_neg_eq_add]
      omega
    rw [hsize] at hcard
    have h2N1_pos : (0 : ℝ) < 2 * (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    rw [div_le_one h2N1_pos]
    calc ((Finset.Icc (-N : ℤ) N).filter (fun k => observationAt f x₀ k ≤ t)).card
        ≤ ((2 * N + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard
      _ = 2 * (N : ℝ) + 1 := hcast

/-- At t = ∞, all observations are counted -/
theorem empiricalDistN_at_infinity (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (M t : ℝ)
    (hbound : ∀ k : ℤ, k ∈ Finset.Icc (-N : ℤ) N → observationAt f x₀ k ≤ M)
    (hM : M < t) :
    empiricalDistN f x₀ N t = 1 := by
  unfold empiricalDistN countBelow
  have hall : (Finset.Icc (-N : ℤ) N).filter (fun k => observationAt f x₀ k ≤ t) =
      Finset.Icc (-N : ℤ) N := by
    ext k
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hk
    have h1 := hbound k hk
    linarith
  rw [hall]
  have hsize : (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    simp only [sub_neg_eq_add]
    omega
  simp only [hsize]
  have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have h2N1_pos : (2 * (N : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  field_simp

end EmpiricalDistribution

/-!
## FUST Probability Definition

For set E ⊂ ℝ≥0: P_f(E) = lim_{N→∞} (1/(2N+1)) · #{k | A_f(k) ∈ E}
-/

section FUSTProbability

/-- Count of observations in set E -/
noncomputable def countInSet (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (E : Set ℝ) : ℕ :=
  ((Finset.Icc (-N : ℤ) N).filter (fun k => observationAt f x₀ k ∈ E)).card

/-- FUST probability at finite N -/
noncomputable def fustProbN (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (E : Set ℝ) : ℝ :=
  (countInSet f x₀ N E : ℝ) / (2 * N + 1)

/-- Normalization - P_f(ℝ≥0) = 1 -/
theorem fustProb_normalization (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) :
    fustProbN f x₀ N {y | y ≥ 0} = 1 := by
  unfold fustProbN countInSet
  have hall : (Finset.Icc (-N : ℤ) N).filter (fun k => observationAt f x₀ k ∈ {y | y ≥ 0}) =
      Finset.Icc (-N : ℤ) N := by
    ext k
    simp only [Finset.mem_filter, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro _
    exact observationAt_nonneg f x₀ k
  rw [hall]
  have hsize : (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    simp only [sub_neg_eq_add]
    omega
  simp only [hsize]
  have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have h2N1_pos : (2 * (N : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  field_simp

/-- Probability is non-negative -/
theorem fustProbN_nonneg (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (E : Set ℝ) :
    fustProbN f x₀ N E ≥ 0 := by
  unfold fustProbN
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith

/-- Probability is at most 1 -/
theorem fustProbN_le_one (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) (E : Set ℝ) :
    fustProbN f x₀ N E ≤ 1 := by
  unfold fustProbN countInSet
  have hcard : ((Finset.Icc (-N : ℤ) N).filter (fun k => observationAt f x₀ k ∈ E)).card ≤
      (Finset.Icc (-N : ℤ) N).card := Finset.card_filter_le _ _
  have hsize : (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    simp only [sub_neg_eq_add]
    omega
  rw [hsize] at hcard
  have h2N1_pos : (0 : ℝ) < 2 * (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
  rw [div_le_one h2N1_pos]
  calc (countInSet f x₀ N E : ℝ)
      ≤ ((2 * N + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard
    _ = 2 * (N : ℝ) + 1 := hcast

end FUSTProbability

/-!
## Born Rule as Structural Consequence

The FUST action: A[f] = ∫ |D6[f](x)|² dx/x

equals the probability expectation: A[f] = E_{P_f}[|D6[f]|²]
-/

section BornRule

/-- Discrete FUST action: sum of |D6[f]|² with Haar weight -/
noncomputable def discreteAction (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum (fun k => (observationAt f x₀ k)^2) * haarWeight

/-- Discrete expectation: average of |D6[f]|² -/
noncomputable def discreteExpectation (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum (fun k => (observationAt f x₀ k)^2) / (2 * N + 1)

/-- Born rule: Action = (2N+1) · log(φ) · Expectation -/
theorem born_rule_discrete (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) :
    discreteAction f x₀ N = (2 * N + 1) * haarWeight * discreteExpectation f x₀ N := by
  unfold discreteAction discreteExpectation haarWeight
  have h2N1_ne : (2 * (N : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  field_simp [h2N1_ne]

/-- Action is non-negative -/
theorem discreteAction_nonneg (f : ℝ → ℝ) (x₀ : ℝ) (N : ℕ) :
    discreteAction f x₀ N ≥ 0 := by
  unfold discreteAction
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro k _
    exact sq_nonneg _
  · exact le_of_lt haarWeight_pos

/-- For ker(D6) functions, action is zero -/
theorem action_zero_for_ker (f : ℝ → ℝ) (hf : IsInKerD6 f) (x₀ : ℝ) (hx₀ : 0 < x₀) (N : ℕ) :
    discreteAction f x₀ N = 0 := by
  unfold discreteAction
  have hsum : (Finset.Icc (-N : ℤ) N).sum (fun k => (observationAt f x₀ k)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp only [observationAt]
    have hne : φ ^ k * x₀ ≠ 0 := observationAt_welldefined f x₀ hx₀ k
    rw [IsInKerD6_implies_D6_zero f hf (φ ^ k * x₀) hne]
    simp
  rw [hsum]
  simp

end BornRule

/-!
## Complete Probability Theory Summary
-/

/-- FUST probability theory: complete structural derivation -/
theorem fust_probability_theory :
    -- (A) Same-degree ratio is gauge-invariant (Theorem 3.1)
    (∀ a b : ℝ, ∀ f : ℝ → ℝ, ∀ x : ℝ, b ≠ 0 → D6 f x ≠ 0 →
      |D6 (fun t => a * f t) x| / |D6 (fun t => b * f t) x| = |a| / |b|) ∧
    -- (B) Observation values are non-negative
    (∀ f : ℝ → ℝ, ∀ x₀ : ℝ, ∀ k : ℤ, observationAt f x₀ k ≥ 0) ∧
    -- (C) Normalization: P_f(ℝ≥0) = 1
    (∀ f : ℝ → ℝ, ∀ x₀ : ℝ, ∀ N : ℕ, fustProbN f x₀ N {y | y ≥ 0} = 1) ∧
    -- (D) Born rule: A = (2N+1)·log(φ)·E
    (∀ f : ℝ → ℝ, ∀ x₀ : ℝ, ∀ N : ℕ,
      discreteAction f x₀ N = (2 * N + 1) * haarWeight * discreteExpectation f x₀ N) ∧
    -- (E) ker(D6) states have zero action
    (∀ f : ℝ → ℝ, IsInKerD6 f → ∀ x₀ : ℝ, 0 < x₀ → ∀ N : ℕ, discreteAction f x₀ N = 0) :=
  ⟨same_degree_ratio_gauge_invariant,
   observationAt_nonneg,
   fustProb_normalization,
   born_rule_discrete,
   action_zero_for_ker⟩

end FUST.Probability
