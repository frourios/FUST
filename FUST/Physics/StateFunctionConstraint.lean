import FUST.DifferenceOperators
import FUST.FrourioAlgebra.GoldenIntegerRing
import FUST.FrourioAlgebra.GoldenValuation
import FUST.Physics.PhiOrbitInitialValue
import FUST.Physics.LeastAction

/-!
# Algebraic Constraint on State Functions

Physically manifest state functions g(x) are constrained to ℤ[φ]-coefficient
polynomials by three algebraic properties of the Frourio algebra:

1. **Polynomial module closure** (Prop 5.2): V = Span{xⁿ} is an
   𝓕(A)-module under U·xⁿ = φⁿxⁿ, D_Φ·xⁿ = S_{n-1}·x^{n-1}
2. **Valuation non-decreasing** (Prop 8.1): v_𝔭(Δf) ≥ v_𝔭(f) over ℤ[φ]
3. **PBW faithfulness**: The standard representation over Q(φ) is faithful
-/

namespace FUST.StateFunctionConstraint

open FUST FrourioAlgebra PhiOrbit Complex

/-!
## Polynomial Module Closure (Proposition 5.2)

The polynomial space V = Span{xⁿ} is closed under:
- Scale action U: preserves degree, multiplies coefficient by φⁿ
- Frourio difference D_Φ: lowers degree by 1, coefficient is S_{n-1}

Both operations preserve ℤ[φ]-coefficients.
-/

private theorem goldenField_pow {x : ℝ}
    (hx : InGoldenField x) : ∀ n : ℕ, InGoldenField (x ^ n)
  | 0 => by simpa using goldenField_one
  | n + 1 => by
    rw [pow_succ]
    exact goldenField_mul (goldenField_pow hx n) hx

/-- Evaluate a ℤ[φ]-coefficient polynomial at z ∈ ℂ -/
noncomputable def evalGoldenPoly (coeffs : ℕ → GoldenInt) (deg : ℕ) (z : ℂ) : ℂ :=
  (Finset.range (deg + 1)).sum fun k => ((coeffs k).toReal : ℂ) * z ^ k

/-- Evaluation of a golden polynomial yields a value in Q(φ) when x ∈ Q(φ) -/
theorem evalGoldenPoly_in_goldenField
    (coeffs : ℕ → GoldenInt) (deg : ℕ) (x : ℝ)
    (hx : InGoldenField x) :
    InGoldenField (re (evalGoldenPoly coeffs deg (x : ℂ))) := by
  simp only [evalGoldenPoly]
  have hre : (Finset.range (deg + 1)).sum
      (fun k => ((coeffs k).toReal : ℂ) * (↑x) ^ k) =
    ↑((Finset.range (deg + 1)).sum
      (fun k => (coeffs k).toReal * x ^ k)) := by
    rw [ofReal_sum]; congr 1; ext k; push_cast; ring
  rw [hre, ofReal_re]
  apply Finset.sum_induction _ InGoldenField
  · exact fun _ _ => goldenField_add
  · exact goldenField_zero
  · intro k _
    exact goldenField_mul
      (goldenInt_in_goldenField _) (goldenField_pow hx k)

/-!
## Scale Action Preserves ℤ[φ]-Coefficients

U·(Σ cₖ xᵏ) = Σ (φᵏ·cₖ) xᵏ evaluated at φx.
Since φⁿ ∈ ℤ[φ], the scaled polynomial has ℤ[φ] coefficients.
-/

/-- Scaling a golden polynomial by φ: each cₖ becomes φᵏ·cₖ -/
def scaleGoldenPoly (coeffs : ℕ → GoldenInt) (k : ℕ) : GoldenInt :=
  GoldenInt.phiPow k * coeffs k

/-- Evaluation of scaled polynomial equals evaluation at φx -/
theorem scale_eval_eq
    (coeffs : ℕ → GoldenInt) (deg : ℕ) (z : ℂ) :
    evalGoldenPoly (scaleGoldenPoly coeffs) deg z =
    evalGoldenPoly coeffs deg ((φ : ℂ) * z) := by
  simp only [evalGoldenPoly, scaleGoldenPoly]
  congr 1; ext k
  have h : (GoldenInt.phiPow ↑k * coeffs k).toReal =
      (GoldenInt.phiPow ↑k).toReal * (coeffs k).toReal :=
    toReal_mul _ _
  rw [h, phiPow_toReal, zpow_natCast]
  push_cast; rw [mul_pow]; ring

/-- A state function is a ℤ[φ]-coefficient polynomial -/
def IsGoldenPolynomialState (g : ℂ → ℂ) : Prop :=
  ∃ (deg : ℕ) (coeffs : ℕ → GoldenInt),
    g = fun z => evalGoldenPoly coeffs deg z

/-- Golden polynomial states evaluate to Q(φ) on Q(φ) inputs -/
theorem golden_state_in_goldenField
    (g : ℂ → ℂ) (hg : IsGoldenPolynomialState g)
    (x : ℝ) (hx : InGoldenField x) :
    InGoldenField (re (g (x : ℂ))) := by
  obtain ⟨deg, coeffs, hgeq⟩ := hg
  rw [hgeq]
  exact evalGoldenPoly_in_goldenField coeffs deg x hx

/-- Golden polynomial states are closed under scale action U -/
theorem golden_state_closed_under_scale
    (g : ℂ → ℂ) (hg : IsGoldenPolynomialState g) :
    IsGoldenPolynomialState (fun z => g ((φ : ℂ) * z)) := by
  obtain ⟨deg, coeffs, hgeq⟩ := hg
  refine ⟨deg, scaleGoldenPoly coeffs, ?_⟩
  ext z; rw [hgeq]; exact (scale_eval_eq coeffs deg z).symm

/-!
## Valuation Non-Decreasing (imported from GoldenValuation)

The theorem `valuation_nonDecreasing` states v_𝔭(Δf) ≥ v_𝔭(f)
for f ∈ ℤ[φ]((x)) with unit parameters α, β ∈ ℤ[φ]×.
-/

/-- Convert a golden polynomial to a golden Laurent series -/
noncomputable def goldenPolyToLaurent (coeffs : ℕ → GoldenInt) (deg : ℕ) :
    GoldenLaurent where
  coeff := fun n => if h : 0 ≤ n ∧ n.toNat ≤ deg then coeffs n.toNat else 0
  finiteNegSupport := by
    apply Set.Finite.subset (Set.finite_empty)
    intro n ⟨hn, hne⟩
    exfalso
    have : ¬(0 ≤ n ∧ n.toNat ≤ deg) := by omega
    simp only [this, dite_false, ne_eq, not_true] at hne

/-- Valuation non-decreasing for golden polynomials -/
theorem poly_valuation_nonDecreasing [GoldenValuation]
    (coeffs : ℕ → GoldenInt) (deg : ℕ) :
    let f := goldenPolyToLaurent coeffs deg
    let α := GoldenInt.phiPow 1
    let β := GoldenInt.phiPow (-1)
    coeffValuation (twoPointDiff f α β) ≥ coeffValuation f :=
  valuation_nonDecreasing _ _ _ (GoldenInt.phiPow_isUnit 1) (GoldenInt.phiPow_isUnit (-1))

/-!
## State Complexity Bound

The total complexity of a state is bounded by the number of time steps.
At scale level k, at most k massive modes are accessible.
At k = 0 (initial moment), no massive structure exists: only vacuum.
-/

section StateComplexityBound

open FUST.LeastAction

/-- Maximum polynomial degree at scale level k: ker basis (deg 2) + k massive modes -/
def maxDegreeAtLevel (k : ℕ) : ℕ := 2 + k

/-- State space dimension (rank over ℤ[φ]) at level k -/
def stateSpaceDim (k : ℕ) : ℕ := 3 + k

/-- Number of massive (non-kernel) modes accessible at level k -/
def massiveModeCount (k : ℕ) : ℕ := k

theorem maxDegreeAtLevel_growth (k : ℕ) :
    maxDegreeAtLevel (k + 1) = maxDegreeAtLevel k + 1 := by
  unfold maxDegreeAtLevel; omega

theorem stateSpaceDim_growth (k : ℕ) :
    stateSpaceDim (k + 1) = stateSpaceDim k + 1 := by
  unfold stateSpaceDim; omega

theorem stateSpaceDim_eq_maxDeg_succ (k : ℕ) :
    stateSpaceDim k = maxDegreeAtLevel k + 1 := by
  unfold stateSpaceDim maxDegreeAtLevel; omega

/-- At k = 0, no massive mode is accessible -/
theorem initial_no_massive : massiveModeCount 0 = 0 := by decide

/-- A degree-bounded golden polynomial state at scale level k -/
def IsBoundedGoldenState (k : ℕ) (g : ℂ → ℂ) : Prop :=
  ∃ (deg : ℕ) (_ : deg ≤ maxDegreeAtLevel k) (coeffs : ℕ → GoldenInt),
    g = fun z => evalGoldenPoly coeffs deg z

/-- Every bounded state is a golden polynomial state -/
theorem bounded_is_golden (k : ℕ) (g : ℂ → ℂ) (hg : IsBoundedGoldenState k g) :
    IsGoldenPolynomialState g := by
  obtain ⟨deg, _, coeffs, hgeq⟩ := hg
  exact ⟨deg, coeffs, hgeq⟩

/-- Scale action maps level k to level k+1 -/
theorem bounded_state_closed_under_scale (k : ℕ) (g : ℂ → ℂ)
    (hg : IsBoundedGoldenState k g) :
    IsBoundedGoldenState (k + 1) (fun z => g ((φ : ℂ) * z)) := by
  obtain ⟨deg, hdeg, coeffs, hgeq⟩ := hg
  have hle : maxDegreeAtLevel k ≤ maxDegreeAtLevel (k + 1) := by
    unfold maxDegreeAtLevel; omega
  refine ⟨deg, le_trans hdeg hle, scaleGoldenPoly coeffs, ?_⟩
  ext z; rw [hgeq]; exact (scale_eval_eq coeffs deg z).symm

/-- At level 0, the maximum degree is 2 -/
theorem maxDeg_zero : maxDegreeAtLevel 0 = 2 := by decide

/-- A degree ≤ 2 polynomial is in ker(D₆) -/
theorem deg_le_2_in_kerD6 (coeffs : ℕ → GoldenInt) (deg : ℕ) (hdeg : deg ≤ 2) :
    IsInKerD6 (fun z => evalGoldenPoly coeffs deg z) := by
  interval_cases deg
  · exact ⟨((coeffs 0).toReal : ℂ), 0, 0, fun t => by
      simp [evalGoldenPoly]⟩
  · exact ⟨((coeffs 0).toReal : ℂ), ((coeffs 1).toReal : ℂ), 0, fun t => by
      simp [evalGoldenPoly, Finset.sum_range_succ]⟩
  · exact ⟨((coeffs 0).toReal : ℂ), ((coeffs 1).toReal : ℂ), ((coeffs 2).toReal : ℂ), fun t => by
      simp [evalGoldenPoly, Finset.sum_range_succ]⟩

/-- At level 0, every bounded state is in ker(D₆) (vacuum only) -/
theorem initial_vacuum (g : ℂ → ℂ) (hg : IsBoundedGoldenState 0 g) :
    IsInKerD6 g := by
  obtain ⟨deg, hdeg, coeffs, hgeq⟩ := hg
  rw [hgeq]
  exact deg_le_2_in_kerD6 coeffs deg hdeg

/-- Monotonicity: level k state is also a level (k+1) state -/
theorem bounded_state_monotone (k : ℕ) (g : ℂ → ℂ)
    (hg : IsBoundedGoldenState k g) :
    IsBoundedGoldenState (k + 1) g := by
  obtain ⟨deg, hdeg, coeffs, hgeq⟩ := hg
  have hle : maxDegreeAtLevel k ≤ maxDegreeAtLevel (k + 1) := by
    unfold maxDegreeAtLevel; omega
  exact ⟨deg, le_trans hdeg hle, coeffs, hgeq⟩

/-- At level 1, x³ becomes accessible (first massive mode) -/
theorem level_one_cubic_accessible :
    maxDegreeAtLevel 1 = 3 := by decide

/-- x³ is NOT in ker(D₆) -/
theorem cubic_not_in_ker : ¬IsInKerD6 (fun z => z ^ 3) := by
  intro ⟨a₀, a₁, a₂, hf⟩
  have h0 := hf 0; norm_num at h0
  have h1 := hf 1; norm_num at h1
  have h2 := hf 2; norm_num at h2
  have h3 := hf 3; norm_num at h3
  rw [h0.symm] at h1 h2 h3
  simp only [zero_add] at h1 h2 h3
  have eq1 : a₁ + a₂ = 1 := h1.symm
  have eq2 : a₁ * 2 + a₂ * 4 = 8 := h2.symm
  have eq3 : a₁ * 3 + a₂ * 9 = 27 := h3.symm
  have rhs : 3 * (a₁ * 3 + a₂ * 9) - 9 * (a₁ * 2 + a₂ * 4) + 6 * (a₁ + a₂) =
      3 * 27 - 9 * 8 + 6 * 1 := by rw [eq3, eq2, eq1]
  have expand : 3 * (a₁ * 3 + a₂ * 9) - 9 * (a₁ * 2 + a₂ * 4) + 6 * (a₁ + a₂) =
      -3 * (a₁ + a₂) := by ring
  have : -3 * (a₁ + a₂) = 3 * 27 - 9 * 8 + 6 * 1 := by rw [← expand, rhs]
  rw [eq1] at this
  norm_num at this

/-- Summary: complexity grows linearly with time steps -/
theorem state_complexity_bound :
    -- (1) No massive modes at level 0
    (massiveModeCount 0 = 0) ∧
    -- (2) State space grows linearly
    (∀ k, stateSpaceDim (k + 1) = stateSpaceDim k + 1) ∧
    -- (3) Initial states are vacuum (ker D₆)
    (∀ g, IsBoundedGoldenState 0 g → IsInKerD6 g) ∧
    -- (4) Scale action respects level structure
    (∀ k g, IsBoundedGoldenState k g →
      IsBoundedGoldenState (k + 1) (fun z => g ((φ : ℂ) * z))) ∧
    -- (5) First massive mode appears at level 1
    (massiveModeCount 1 = 1) ∧
    -- (6) x³ is not in ker(D₆)
    (¬IsInKerD6 (fun z => z ^ 3)) :=
  ⟨initial_no_massive, stateSpaceDim_growth, initial_vacuum,
   bounded_state_closed_under_scale, rfl, cubic_not_in_ker⟩

end StateComplexityBound

end FUST.StateFunctionConstraint
