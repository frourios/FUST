import FUST.DifferenceOperators
import FUST.FrourioAlgebra.GoldenIntegerRing
import FUST.FrourioAlgebra.GoldenValuation
import FUST.Physics.PhiOrbitInitialValue

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

open FUST FrourioAlgebra

/-!
## Polynomial Module Closure (Proposition 5.2)

The polynomial space V = Span{xⁿ} is closed under:
- Scale action U: preserves degree, multiplies coefficient by φⁿ
- Frourio difference D_Φ: lowers degree by 1, coefficient is S_{n-1}

Both operations preserve ℤ[φ]-coefficients.
-/

/-- Evaluate a ℤ[φ]-coefficient polynomial at x ∈ ℝ -/
noncomputable def evalGoldenPoly (coeffs : ℕ → GoldenInt) (deg : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (deg + 1)).sum fun k => (coeffs k).toReal * x ^ k

/-- Evaluation of a golden polynomial yields a value in Q(φ) when x ∈ Q(φ) -/
theorem evalGoldenPoly_in_goldenField
    (coeffs : ℕ → GoldenInt) (deg : ℕ) (x : ℝ)
    (hx : PhiOrbit.InGoldenField x) :
    PhiOrbit.InGoldenField (evalGoldenPoly coeffs deg x) := by
  unfold evalGoldenPoly
  induction deg with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one]
    exact PhiOrbit.goldenInt_in_goldenField (coeffs 0)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    apply PhiOrbit.goldenField_add
    · exact ih
    · apply PhiOrbit.goldenField_mul
      · exact PhiOrbit.goldenInt_in_goldenField (coeffs (n + 1))
      · clear ih
        induction n with
        | zero => simpa using hx
        | succ k ihk =>
          rw [pow_succ]
          exact PhiOrbit.goldenField_mul ihk hx

/-!
## Scale Action Preserves ℤ[φ]-Coefficients

U·(Σ cₖ xᵏ) = Σ (φᵏ·cₖ) xᵏ evaluated at φx.
Since φⁿ ∈ ℤ[φ], the scaled polynomial has ℤ[φ] coefficients.
-/

/-- Scaling a golden polynomial by φ: each cₖ becomes φᵏ·cₖ -/
def scaleGoldenPoly (coeffs : ℕ → GoldenInt) (k : ℕ) : GoldenInt :=
  GoldenInt.phiPow k * coeffs k

/-- Evaluation of scaled polynomial equals evaluation at φx -/
theorem scale_eval_eq (coeffs : ℕ → GoldenInt) (deg : ℕ) (x : ℝ) :
    evalGoldenPoly (scaleGoldenPoly coeffs) deg x =
    evalGoldenPoly coeffs deg (φ * x) := by
  unfold evalGoldenPoly scaleGoldenPoly
  congr 1; ext k
  show (GoldenInt.phiPow ↑k * coeffs k).toReal * x ^ k =
    (coeffs k).toReal * (φ * x) ^ k
  have h1 : (GoldenInt.phiPow ↑k * coeffs k).toReal =
      (GoldenInt.phiPow ↑k).toReal * (coeffs k).toReal :=
    toReal_mul _ _
  rw [h1, phiPow_toReal]
  have h2 : φ ^ (k : ℤ) = φ ^ k := zpow_natCast φ k
  rw [h2, mul_pow]
  ring

/-- A state function is a ℤ[φ]-coefficient polynomial -/
def IsGoldenPolynomialState (g : ℝ → ℝ) : Prop :=
  ∃ (deg : ℕ) (coeffs : ℕ → GoldenInt),
    g = fun x => evalGoldenPoly coeffs deg x

/-- Golden polynomial states evaluate to Q(φ) on Q(φ) inputs -/
theorem golden_state_in_goldenField
    (g : ℝ → ℝ) (hg : IsGoldenPolynomialState g)
    (x : ℝ) (hx : PhiOrbit.InGoldenField x) :
    PhiOrbit.InGoldenField (g x) := by
  obtain ⟨deg, coeffs, hgeq⟩ := hg
  rw [hgeq]
  exact evalGoldenPoly_in_goldenField coeffs deg x hx

/-- Golden polynomial states are closed under scale action U -/
theorem golden_state_closed_under_scale
    (g : ℝ → ℝ) (hg : IsGoldenPolynomialState g) :
    IsGoldenPolynomialState (fun x => g (φ * x)) := by
  obtain ⟨deg, coeffs, hgeq⟩ := hg
  refine ⟨deg, scaleGoldenPoly coeffs, ?_⟩
  ext x; rw [hgeq]; exact (scale_eval_eq coeffs deg x).symm

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

end FUST.StateFunctionConstraint
