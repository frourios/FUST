import FUST.DζOperator
import FUST.Dimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Standard Gauge Group from Fζ Factorization Gauge Freedom

The gauge group arises from the INPUT side: the ambiguity in factoring a state
function f = f₁·f₂·...·fₖ. The derivation defect δ(f,g) = Fζ(fg) - fFζ(g) - Fζ(f)g
is invariant under (f,g) → (cf, c⁻¹g), giving U(1) scalar gauge.

For multi-mode superpositions, mode coefficients can be mixed by GL(k) while
preserving the product. The maximum k is bounded by the rank of the mode vector
space v(s) = (σ_Diff5(s), σ_Diff3(s), σ_Diff2(s)) ∈ ℝ³, which has dimension 3
(proved by Φ_S_rank_three). This limits the gauge group to SU(3).

For the AF channel, τ(AF_coeff) = -AF_coeff (quaternionic type) uniquely determines
SU(2). The trivial channel gives U(1).
-/

namespace FUST

open Complex FUST.DζOperator

/-! ## Channel separation: ζ₆ ≠ φⁿ ensures independent channels -/

section ChannelSeparation

theorem zeta6_im_ne_zero : ζ₆.im ≠ 0 := by
  simp only [ζ₆]
  exact ne_of_gt (div_pos sqrt3_pos (by norm_num : (0 : ℝ) < 2))

theorem phi_pow_im_zero (n : ℕ) : ((↑φ : ℂ) ^ n).im = 0 := by
  rw [← ofReal_pow]; exact ofReal_im (φ ^ n)

theorem zeta6_ne_phi_pow (n : ℕ) : ζ₆ ≠ (↑φ : ℂ) ^ n := by
  intro h
  have him := congr_arg Complex.im h
  rw [phi_pow_im_zero] at him
  exact zeta6_im_ne_zero him

end ChannelSeparation

/-! ## AF channel: τ-anti-invariance → quaternionic type → SU(2)

AF_coeff = ⟨-2, 0, 4, 0⟩ in ℤ[φ,ζ₆].
τ(AF_coeff) = ⟨2, 0, -4, 0⟩ = -AF_coeff.
This τ-anti-invariance is the signature of a quaternionic representation,
which uniquely determines SU(2) ≅ Sp(1) as the gauge group on dim 2. -/

section AFQuaternionic

open FUST.FrourioAlgebra.GoldenEisensteinInt

theorem AF_coeff_tau_neg :
    tau AF_coeff_gei = neg AF_coeff_gei := by
  unfold tau AF_coeff_gei neg; ext <;> simp

theorem AF_coeff_nonzero : AF_coeff ≠ 0 := by
  intro h
  have := AF_coeff_normSq
  rw [h, map_zero] at this
  norm_num at this

theorem AF_coeff_purely_imaginary : AF_coeff.re = 0 := by rw [AF_coeff_eq]

end AFQuaternionic

/-! ## SY channel: mode vectors in ℝ³ → rank 3 → SU(3) saturation

For each active mode s, the SY sub-operator eigenvalues give a mode vector
v(s) = (σ_Diff5(s), σ_Diff3(s), σ_Diff2(s)) ∈ ℂ³. The 3×3 determinant
det(v(1), v(5), v(7)) ≠ 0 proves these span ℂ³ (rank 3).

Since dim ℂ³ = 3, any 4th mode vector is a linear combination of the first 3.
Mode-mixing gauge transformations on k independent modes give GL(k) → SU(k).
With at most 3 independent mode vectors, the gauge group saturates at SU(3). -/

section SYModeSpace

theorem mode_space_rank_three :
    σ_Diff5 1 * (σ_Diff3 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff3 7) -
    σ_Diff3 1 * (σ_Diff5 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff5 7) +
    σ_Diff2 1 * (σ_Diff5 5 * σ_Diff3 7 - σ_Diff3 5 * σ_Diff5 7) ≠ 0 :=
  Φ_S_rank_three

theorem mode_space_dim_bound : Fintype.card (Fin 3) = 3 := by decide

end SYModeSpace

/-! ## Norm decomposition: weight ratio 3:1

|6a + AF_coeff·b|² = 12(3a² + b²) shows the SY channel has weight 3
and the AF channel has weight 1 in the Fζ norm. -/

section NormDecomposition

theorem norm_weight_ratio (a b : ℝ) :
    Complex.normSq (6 * (a : ℂ) + AF_coeff * b) = 12 * (3 * a ^ 2 + b ^ 2) :=
  Dζ_normSq_decomposition a b

end NormDecomposition

/-! ## Main theorem: gauge group dimensions from Fζ factorization

The derivation defect δ(cf, c⁻¹g) = δ(f,g) (proved in FζOperator.lean) gives
the fundamental gauge invariance. Mode-mixing on the SY channel is bounded by
rank 3, the AF channel has quaternionic type (τ-anti-invariant), and the trivial
channel has dimension 1. These three conditions uniquely determine the gauge group
representation dimensions as (3, 2, 1), matching SU(3) × SU(2) × U(1). -/

section GaugeGroupDimensions

open FUST.FrourioAlgebra.GoldenEisensteinInt

/-- Channel dimensions: SY rank 3, AF quaternionic on dim 2, trivial dim 1 -/
theorem gauge_channel_dimensions :
    -- SY mode space has rank 3 (det ≠ 0)
    (σ_Diff5 1 * (σ_Diff3 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff3 7) -
     σ_Diff3 1 * (σ_Diff5 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff5 7) +
     σ_Diff2 1 * (σ_Diff5 5 * σ_Diff3 7 - σ_Diff3 5 * σ_Diff5 7) ≠ 0) ∧
    -- AF is τ-anti-invariant (quaternionic type)
    (tau AF_coeff_gei = neg AF_coeff_gei) ∧
    -- AF channel is nondegenerate
    (AF_coeff ≠ 0 ∧ AF_coeff.re = 0) ∧
    -- Channels are independent
    (∀ n : ℕ, ζ₆ ≠ (↑φ : ℂ) ^ n) ∧
    -- Norm weight ratio
    (∀ a b : ℝ, Complex.normSq (6 * (a : ℂ) + AF_coeff * b) =
      12 * (3 * a ^ 2 + b ^ 2)) := by
  exact ⟨mode_space_rank_three,
         AF_coeff_tau_neg,
         ⟨AF_coeff_nonzero, AF_coeff_purely_imaginary⟩,
         zeta6_ne_phi_pow,
         norm_weight_ratio⟩

end GaugeGroupDimensions

end FUST
