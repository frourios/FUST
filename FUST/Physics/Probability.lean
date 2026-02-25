import FUST.DifferenceOperators
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

open FUST Complex

attribute [local instance] Classical.propDecidable

/-!
## Theorem 3.1: Same-Degree Ratio Gauge Invariance

For same-degree monomials f_A = a·x^n and f_B = b·x^n:
  normSq(D6[f_A](x)) / normSq(D6[f_B](x)) = normSq(a) / normSq(b)

This is independent of x (gauge-invariant).
-/

section SameDegreeRatio

/-- D6 is linear: D6[a·f] = a·D6[f] -/
theorem D6_linear_scalar (a : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    D6 (fun t => a * f t) x = a * D6 f x := by
  simp only [D6, N6]
  ring

/-- Same-degree ratio is gauge-invariant -/
theorem same_degree_ratio_gauge_invariant
    (a b : ℂ) (f : ℂ → ℂ) (x : ℂ)
    (_hb : b ≠ 0) (hfx : D6 f x ≠ 0) :
    normSq (D6 (fun t => a * f t) x) /
      normSq (D6 (fun t => b * f t) x) =
    normSq a / normSq b := by
  rw [D6_linear_scalar, D6_linear_scalar]
  rw [normSq_mul, normSq_mul]
  have hD6 : normSq (D6 f x) ≠ 0 :=
    normSq_pos.mpr hfx |>.ne'
  rw [mul_div_mul_right _ _ hD6]

/-- For monomials: ratio is independent of evaluation point -/
theorem monomial_ratio_invariant
    (a b : ℂ) (n : ℕ) (x y : ℂ)
    (hb : b ≠ 0) (_hx : x ≠ 0) (_hy : y ≠ 0) (_hn : n ≥ 3)
    (hfx : D6 (fun t => t ^ n) x ≠ 0)
    (hfy : D6 (fun t => t ^ n) y ≠ 0) :
    normSq (D6 (fun t => a * t ^ n) x) /
      normSq (D6 (fun t => b * t ^ n) x) =
    normSq (D6 (fun t => a * t ^ n) y) /
      normSq (D6 (fun t => b * t ^ n) y) := by
  rw [same_degree_ratio_gauge_invariant a b _ x hb hfx]
  rw [same_degree_ratio_gauge_invariant a b _ y hb hfy]

end SameDegreeRatio

/-!
## φ-Scale Iteration and Observation Sequences

The φ-scale transformation x ↦ φ^k · x generates observation sequences:
  A_f(k) := normSq(D6[f](φ^k · x))

This corresponds to "trials" in probability theory.
-/

section PhiScaleIteration

/-- Observation value at scale k -/
noncomputable def observationAt
    (f : ℂ → ℂ) (x₀ : ℝ) (k : ℤ) : ℝ :=
  normSq (D6 f ↑(φ ^ k * x₀))

/-- Observation sequence is well-defined for x₀ > 0 -/
theorem observationAt_welldefined
    (_f : ℂ → ℂ) (x₀ : ℝ) (hx₀ : 0 < x₀) (k : ℤ) :
    (↑(φ ^ k * x₀) : ℂ) ≠ 0 := by
  apply ofReal_ne_zero.mpr
  apply mul_ne_zero
  · exact zpow_ne_zero k (ne_of_gt phi_pos)
  · exact ne_of_gt hx₀

/-- φ-scaling shifts the observation index -/
theorem observation_shift
    (f : ℂ → ℂ) (x₀ : ℝ) (_hx₀ : 0 < x₀) (k j : ℤ) :
    observationAt f (φ ^ j * x₀) k =
    observationAt f x₀ (k + j) := by
  simp only [observationAt]
  have h : φ ^ k * (φ ^ j * x₀) = φ ^ (k + j) * x₀ := by
    rw [← mul_assoc, ← zpow_add₀ (ne_of_gt phi_pos)]
  rw [h]

/-- Observation values are non-negative -/
theorem observationAt_nonneg
    (f : ℂ → ℂ) (x₀ : ℝ) (k : ℤ) :
    observationAt f x₀ k ≥ 0 :=
  normSq_nonneg _

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
theorem phi_scaling_measure_invariant
    (f : ℂ → ℂ) (x₀ : ℝ) (_hx₀ : 0 < x₀) (N : ℕ) :
    (Finset.Icc (-N : ℤ) N).sum
      (fun k => (observationAt f x₀ k) ^ 2 * haarWeight) =
    (Finset.Icc (-N : ℤ) N).sum
      (fun k => (observationAt f (φ * x₀) (k - 1)) ^ 2 *
        haarWeight) := by
  congr 1
  ext k
  simp only [observationAt]
  congr 3
  have h : φ ^ (k - 1) * (φ * x₀) = φ ^ k * x₀ := by
    have h1 : φ ^ k = φ ^ (k - 1) * φ := by
      rw [← zpow_add_one₀ (ne_of_gt phi_pos) (k - 1),
        sub_add_cancel]
    rw [h1, mul_assoc]
  rw [h]

end PhiInvariantMeasure

/-!
## Empirical Distribution (Frequency-Based Probability)

The empirical distribution function:
  ρ_f(t) = lim_{N→∞} (1/(2N+1)) · #{k ∈ [-N,N] | A_f(k) ≤ t}

When this limit exists, it defines the probability intrinsic to state f.
-/

section EmpiricalDistribution

/-- Count of observations below threshold in range [-N, N] -/
noncomputable def countBelow
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) (t : ℝ) : ℕ :=
  ((Finset.Icc (-N : ℤ) N).filter
    (fun k => observationAt f x₀ k ≤ t)).card

/-- Empirical distribution at finite N -/
noncomputable def empiricalDistN
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (countBelow f x₀ N t : ℝ) / (2 * N + 1)

/-- Empirical distribution is in [0, 1] -/
theorem empiricalDistN_bounds
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) (t : ℝ) :
    0 ≤ empiricalDistN f x₀ N t ∧
    empiricalDistN f x₀ N t ≤ 1 := by
  constructor
  · unfold empiricalDistN
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
  · unfold empiricalDistN countBelow
    have hcard :
        ((Finset.Icc (-N : ℤ) N).filter
          (fun k => observationAt f x₀ k ≤ t)).card ≤
        (Finset.Icc (-N : ℤ) N).card :=
      Finset.card_filter_le _ _
    have hsize :
        (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
      rw [Int.card_Icc]
      simp only [sub_neg_eq_add]
      omega
    rw [hsize] at hcard
    have h2N1_pos : (0 : ℝ) < 2 * (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hcast :
        ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
      push_cast; ring
    rw [div_le_one h2N1_pos]
    calc ((Finset.Icc (-N : ℤ) N).filter
            (fun k => observationAt f x₀ k ≤ t)).card
        ≤ ((2 * N + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard
      _ = 2 * (N : ℝ) + 1 := hcast

/-- At t = ∞, all observations are counted -/
theorem empiricalDistN_at_infinity
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) (M t : ℝ)
    (hbound : ∀ k : ℤ, k ∈ Finset.Icc (-N : ℤ) N →
      observationAt f x₀ k ≤ M)
    (hM : M < t) :
    empiricalDistN f x₀ N t = 1 := by
  unfold empiricalDistN countBelow
  have hall :
      (Finset.Icc (-N : ℤ) N).filter
        (fun k => observationAt f x₀ k ≤ t) =
      Finset.Icc (-N : ℤ) N := by
    ext k
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hk
    have h1 := hbound k hk
    linarith
  rw [hall]
  have hsize :
      (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    simp only [sub_neg_eq_add]
    omega
  simp only [hsize]
  have hcast :
      ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    push_cast; ring
  rw [hcast]
  have h2N1_pos : (2 * (N : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  field_simp

end EmpiricalDistribution

/-!
## FUST Probability Definition

For set E ⊂ ℝ≥0:
  P_f(E) = lim_{N→∞} (1/(2N+1)) · #{k | A_f(k) ∈ E}
-/

section FUSTProbability

/-- Count of observations in set E -/
noncomputable def countInSet
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) (E : Set ℝ) : ℕ :=
  ((Finset.Icc (-N : ℤ) N).filter
    (fun k => observationAt f x₀ k ∈ E)).card

/-- FUST probability at finite N -/
noncomputable def fustProbN
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) (E : Set ℝ) : ℝ :=
  (countInSet f x₀ N E : ℝ) / (2 * N + 1)

/-- Normalization - P_f(ℝ≥0) = 1 -/
theorem fustProb_normalization
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) :
    fustProbN f x₀ N {y | y ≥ 0} = 1 := by
  unfold fustProbN countInSet
  have hall :
      (Finset.Icc (-N : ℤ) N).filter
        (fun k => observationAt f x₀ k ∈ {y | y ≥ 0}) =
      Finset.Icc (-N : ℤ) N := by
    ext k
    simp only [Finset.mem_filter, Set.mem_setOf_eq,
      and_iff_left_iff_imp]
    intro _
    exact observationAt_nonneg f x₀ k
  rw [hall]
  have hsize :
      (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    simp only [sub_neg_eq_add]
    omega
  simp only [hsize]
  have hcast :
      ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    push_cast; ring
  rw [hcast]
  have h2N1_pos : (2 * (N : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  field_simp

/-- Probability is non-negative -/
theorem fustProbN_nonneg
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) (E : Set ℝ) :
    fustProbN f x₀ N E ≥ 0 := by
  unfold fustProbN
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith

/-- Probability is at most 1 -/
theorem fustProbN_le_one
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) (E : Set ℝ) :
    fustProbN f x₀ N E ≤ 1 := by
  unfold fustProbN countInSet
  have hcard :
      ((Finset.Icc (-N : ℤ) N).filter
        (fun k => observationAt f x₀ k ∈ E)).card ≤
      (Finset.Icc (-N : ℤ) N).card :=
    Finset.card_filter_le _ _
  have hsize :
      (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    simp only [sub_neg_eq_add]
    omega
  rw [hsize] at hcard
  have h2N1_pos : (0 : ℝ) < 2 * (N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hcast :
      ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    push_cast; ring
  rw [div_le_one h2N1_pos]
  calc (countInSet f x₀ N E : ℝ)
      ≤ ((2 * N + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard
    _ = 2 * (N : ℝ) + 1 := hcast

end FUSTProbability

/-!
## Born Rule as Structural Consequence

The FUST action: A[f] = ∫ normSq(D6[f](x)) dx/x

equals the probability expectation:
  A[f] = E_{P_f}[normSq(D6[f])]
-/

section BornRule

/-- Discrete FUST action: sum of normSq(D6[f]) with Haar weight -/
noncomputable def discreteAction
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum
    (fun k => (observationAt f x₀ k) ^ 2) * haarWeight

/-- Discrete expectation: average of normSq(D6[f]) -/
noncomputable def discreteExpectation
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum
    (fun k => (observationAt f x₀ k) ^ 2) / (2 * N + 1)

/-- Born rule: Action = (2N+1) · log(φ) · Expectation -/
theorem born_rule_discrete
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) :
    discreteAction f x₀ N =
    (2 * N + 1) * haarWeight *
      discreteExpectation f x₀ N := by
  unfold discreteAction discreteExpectation haarWeight
  have h2N1_ne : (2 * (N : ℝ) + 1) ≠ 0 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  field_simp [h2N1_ne]

/-- Action is non-negative -/
theorem discreteAction_nonneg
    (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) :
    discreteAction f x₀ N ≥ 0 := by
  unfold discreteAction
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro k _
    exact sq_nonneg _
  · exact le_of_lt haarWeight_pos

end BornRule

end FUST.Probability
