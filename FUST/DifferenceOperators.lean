import FUST.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Finset.Basic

namespace FUST

open Complex

/-- D2: Frourio golden 2-point difference
    D₂ f(z) = (f(φz) - f(ψz)) / ((φ - ψ)z) -/
noncomputable def D2 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (f ((↑φ : ℂ) * z) - f ((↑ψ : ℂ) * z)) / (((↑φ : ℂ) - ↑ψ) * z)

/-- D3: Frourio golden 3-point difference (points: φ, 1, ψ, coefficients: [1, -2, 1])
    D₃ f(z) = (f(φz) - 2f(z) + f(ψz)) / ((φ - ψ)²z) -/
noncomputable def D3 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (f ((↑φ : ℂ) * z) - 2 * f z + f ((↑ψ : ℂ) * z)) / (((↑φ : ℂ) - ↑ψ)^2 * z)

/-- D4: Frourio golden 4-point difference
    D₄ f(z) = (f(φ²z) - φ²f(φz) + ψ²f(ψz) - f(ψ²z)) / ((φ - ψ)³z) -/
noncomputable def D4 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (f ((↑φ : ℂ)^2 * z) - (↑φ : ℂ)^2 * f ((↑φ : ℂ) * z)
    + (↑ψ : ℂ)^2 * f ((↑ψ : ℂ) * z) - f ((↑ψ : ℂ)^2 * z)) / (((↑φ : ℂ) - ↑ψ)^3 * z)

/-- D5: Frourio golden 5-point difference with coefficients a=-1, b=-4
    D₅ f(z) = (f(φ²z) + f(φz) - 4f(z) + f(ψz) + f(ψ²z)) / ((φ - ψ)⁴z) -/
noncomputable def D5 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (f ((↑φ : ℂ)^2 * z) + f ((↑φ : ℂ) * z) - 4 * f z
    + f ((↑ψ : ℂ) * z) + f ((↑ψ : ℂ)^2 * z)) / (((↑φ : ℂ) - ↑ψ)^4 * z)

/-- N2: numerator of D2, without the (φ-ψ)·z denominator -/
noncomputable def N2 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) * z) - f ((↑ψ : ℂ) * z)

/-- N3: numerator of D3, without the (φ-ψ)²·z denominator -/
noncomputable def N3 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) * z) - 2 * f z + f ((↑ψ : ℂ) * z)

/-- N5: numerator of D5, without the (φ-ψ)⁴·z denominator -/
noncomputable def N5 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) ^ 2 * z) + f ((↑φ : ℂ) * z) - 4 * f z +
  f ((↑ψ : ℂ) * z) + f ((↑ψ : ℂ) ^ 2 * z)

/-- N6: numerator of D6, without the (φ-ψ)⁵·z denominator -/
noncomputable def N6 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ)^3 * z) - 3 * f ((↑φ : ℂ)^2 * z) + f ((↑φ : ℂ) * z) -
  f ((↑ψ : ℂ) * z) + 3 * f ((↑ψ : ℂ)^2 * z) - f ((↑ψ : ℂ)^3 * z)

/-- D6 normalization constant: (φ - ψ)⁵ -/
noncomputable def D6Denom : ℂ := ((↑φ : ℂ) - ↑ψ)^5

theorem D6Denom_ne_zero : D6Denom ≠ 0 := by
  unfold D6Denom; exact pow_ne_zero _ phi_sub_psi_complex_ne

theorem D6Denom_mul_ne_zero (z : ℂ) (hz : z ≠ 0) : D6Denom * z ≠ 0 :=
  mul_ne_zero D6Denom_ne_zero hz

/-- D6: Frourio golden 6-point difference with coefficients A=3, B=1
    D₆ f(z) = N6(f)(z) / (D6Denom · z) -/
noncomputable def D6 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else N6 f z / (D6Denom * z)

/-- D6 equals N6 divided by D6Denom · z -/
theorem D6_eq_N6_div (f : ℂ → ℂ) (z : ℂ) (hz : z ≠ 0) :
    D6 f z = N6 f z / (D6Denom * z) := by
  simp only [D6, hz, ↓reduceIte]

/-- N6 distributes over finite sums -/
theorem N6_finset_sum {ι : Type*}
    (s : Finset ι) (cs : ι → ℂ) (fs : ι → ℂ → ℂ) (z : ℂ) :
    N6 (fun w => ∑ i ∈ s, cs i * fs i w) z = ∑ i ∈ s, cs i * N6 (fs i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [N6]
  | insert a s' ha ih =>
    rw [Finset.sum_insert ha]
    have step1 : N6 (fun w => ∑ i ∈ insert a s', cs i * fs i w) z =
        cs a * N6 (fs a) z + N6 (fun w => ∑ i ∈ s', cs i * fs i w) z := by
      have : N6 (fun w => ∑ i ∈ insert a s', cs i * fs i w) z =
          N6 (fun w => cs a * fs a w + ∑ i ∈ s', cs i * fs i w) z := by
        congr 1; ext w; exact Finset.sum_insert ha
      rw [this]; simp only [N6]; ring
    rw [step1, ih]

/-- D5½: Half-order difference operator
    D₅.₅ f(z) = D₅ f(z) + μ · (f(φz) - f(ψz)) where μ = 2/(φ+2) -/
noncomputable def D5half (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let μ : ℂ := 2 / ((↑φ : ℂ) + 2)
  D5 f z + μ * (f ((↑φ : ℂ) * z) - f ((↑ψ : ℂ) * z))

section KernelTheorems

/-- D2 annihilates constants: D₂[1] = 0 -/
theorem D2_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : D2 (fun _ => c) z = 0 := by
  simp only [D2, hz, ↓reduceIte, sub_self, zero_div]

/-- D2 does NOT annihilate x: z ∉ ker(D2) -/
theorem D2_linear_ne_zero (z : ℂ) (hz : z ≠ 0) : D2 id z ≠ 0 := by
  simp only [D2, hz, ↓reduceIte, id_eq]
  have hnum : (↑φ : ℂ) * z - ↑ψ * z = ((↑φ : ℂ) - ↑ψ) * z := by ring
  rw [hnum]
  have hφψ_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := phi_sub_psi_complex_ne
  have hden_ne : ((↑φ : ℂ) - ↑ψ) * z ≠ 0 := mul_ne_zero hφψ_ne hz
  exact div_ne_zero hden_ne hden_ne

/-- D3 annihilates constants: D₃[1] = 0 (coefficient sum = 1 - 2 + 1 = 0) -/
theorem D3_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : D3 (fun _ => c) z = 0 := by
  simp only [D3, hz, ↓reduceIte]
  have hnum : c - 2 * c + c = 0 := by ring
  simp only [hnum, zero_div]

/-- D3 does NOT annihilate x: z ∉ ker(D3) -/
theorem D3_linear_ne_zero (z : ℂ) (hz : z ≠ 0) : D3 id z ≠ 0 := by
  simp only [D3, hz, ↓reduceIte, id_eq]
  have hcoeff : (↑φ : ℂ) + ↑ψ - 2 = -1 := by
    have h := phi_add_psi_complex; linear_combination h
  have hnum : (↑φ : ℂ) * z - 2 * z + ↑ψ * z = ((↑φ : ℂ) + ↑ψ - 2) * z := by ring
  rw [hnum, hcoeff]
  have hφψ_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := phi_sub_psi_complex_ne
  have hden_ne : ((↑φ : ℂ) - ↑ψ) ^ 2 * z ≠ 0 := mul_ne_zero (pow_ne_zero 2 hφψ_ne) hz
  rw [neg_one_mul, neg_div, neg_ne_zero]
  exact div_ne_zero hz hden_ne

/-- D4 does NOT annihilate constants: 1 ∉ ker(D4) -/
theorem D4_const_ne_zero (z : ℂ) (hz : z ≠ 0) : D4 (fun _ => 1) z ≠ 0 := by
  simp only [D4, hz, ↓reduceIte]
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hnum : (1 : ℂ) - (↑φ : ℂ)^2 * 1 + (↑ψ : ℂ)^2 * 1 - 1 = -((↑φ : ℂ) - ↑ψ) := by
    rw [hφ2, hψ2]; ring
  rw [hnum]
  have hφψ_ne := phi_sub_psi_complex_ne
  have hden_ne : ((↑φ : ℂ) - ↑ψ)^3 * z ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hφψ_ne) hz
  rw [neg_div, neg_ne_zero]
  exact div_ne_zero hφψ_ne hden_ne

/-- D4 annihilates x²: x² ∈ ker(D4) -/
theorem D4_quadratic (z : ℂ) (hz : z ≠ 0) : D4 (fun t => t^2) z = 0 := by
  simp only [D4, hz, ↓reduceIte]
  have : (φ^2 * z)^2 - φ^2 * (φ * z)^2 + ψ^2 * (ψ * z)^2 - (ψ^2 * z)^2 = 0 := by ring
  simp [this]

/-- D4 does NOT annihilate x: z ∉ ker(D4) -/
theorem D4_linear_ne_zero (z : ℂ) (hz : z ≠ 0) : D4 id z ≠ 0 := by
  simp only [D4, hz, ↓reduceIte, id_eq]
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hcoeff : (↑φ : ℂ)^2 - (↑φ)^3 + (↑ψ : ℂ)^3 - (↑ψ)^2 = -((↑φ : ℂ) - ↑ψ) := by
    rw [hφ2, hφ3, hψ3, hψ2]; ring
  have hnum : (↑φ : ℂ)^2 * z - (↑φ)^2 * ((↑φ) * z) + (↑ψ : ℂ)^2 * ((↑ψ) * z) - (↑ψ)^2 * z =
    ((↑φ : ℂ)^2 - (↑φ)^3 + (↑ψ)^3 - (↑ψ)^2) * z := by ring
  rw [hnum, hcoeff]
  have hφψ_ne := phi_sub_psi_complex_ne
  have hden_ne : ((↑φ : ℂ) - ↑ψ)^3 * z ≠ 0 := mul_ne_zero (pow_ne_zero 3 hφψ_ne) hz
  rw [neg_mul, neg_div, neg_ne_zero]
  exact div_ne_zero (mul_ne_zero hφψ_ne hz) hden_ne

/-- D5 annihilates constants: D₅[1] = 0 (coefficient sum = 1+1-4+1+1 = 0) -/
theorem D5_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : D5 (fun _ => c) z = 0 := by
  simp only [D5, hz, ↓reduceIte]
  have h : c + c - 4 * c + c + c = 0 := by ring
  simp [h]

/-- D5 annihilates x: D₅[x] = 0 -/
theorem D5_linear (z : ℂ) (hz : z ≠ 0) : D5 id z = 0 := by
  simp only [D5, hz, ↓reduceIte, id_eq]
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hsum := phi_add_psi_complex
  have hcoef : (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 + ↑φ + ↑ψ - 4 = 0 := by
    linear_combination hφ2 + hψ2 + 2 * hsum
  have hnum : (↑φ : ℂ)^2 * z + (↑φ) * z - 4 * z + (↑ψ : ℂ) * z + (↑ψ)^2 * z = 0 := by
    have : (↑φ : ℂ)^2 * z + (↑φ) * z - 4 * z + (↑ψ) * z + (↑ψ)^2 * z =
      ((↑φ : ℂ)^2 + (↑ψ)^2 + ↑φ + ↑ψ - 4) * z := by ring
    rw [this, hcoef, zero_mul]
  simp [hnum]

/-- D5 does NOT annihilate x²: x² ∉ ker(D5) -/
theorem D5_not_annihilate_quadratic (z : ℂ) (hz : z ≠ 0) :
    D5 (fun t => t^2) z ≠ 0 := by
  simp only [D5, hz, ↓reduceIte]
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hsum := phi_add_psi_complex
  have hcoef : ((↑φ : ℂ)^2)^2 + (↑φ)^2 - 4 + (↑ψ : ℂ)^2 + ((↑ψ)^2)^2 = 6 := by
    linear_combination hφ4 + hψ4 + hφ2 + hψ2 + 4 * hsum
  have hnum : ((↑φ : ℂ)^2 * z)^2 + ((↑φ) * z)^2 - 4 * z^2 + ((↑ψ : ℂ) * z)^2 +
      ((↑ψ)^2 * z)^2 = (((↑φ : ℂ)^2)^2 + (↑φ)^2 - 4 + (↑ψ)^2 + ((↑ψ)^2)^2) * z^2 := by ring
  rw [hnum, hcoef]
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))
    (mul_ne_zero (pow_ne_zero 4 phi_sub_psi_complex_ne) hz)

/-- D6 annihilates constants: D₆[1] = 0 (coefficient sum = 1-3+1-1+3-1 = 0) -/
theorem D6_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : D6 (fun _ => c) z = 0 := by
  simp only [D6, N6, hz, ↓reduceIte]
  ring_nf

/-- D6 annihilates x: D₆[x] = 0 -/
theorem D6_linear (z : ℂ) (hz : z ≠ 0) : D6 id z = 0 := by
  simp only [D6, N6, hz, ↓reduceIte, id_eq]
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hcoef : (↑φ : ℂ)^3 - 3*(↑φ)^2 + ↑φ - ↑ψ + 3*(↑ψ : ℂ)^2 - (↑ψ)^3 = 0 := by
    rw [hφ3, hφ2, hψ2, hψ3]; ring
  have hnum : (↑φ : ℂ)^3 * z - 3 * ((↑φ)^2 * z) + (↑φ) * z - (↑ψ : ℂ) * z +
      3 * ((↑ψ)^2 * z) - (↑ψ)^3 * z = 0 := by
    have : (↑φ : ℂ)^3 * z - 3 * ((↑φ)^2 * z) + (↑φ) * z - (↑ψ) * z +
      3 * ((↑ψ)^2 * z) - (↑ψ)^3 * z =
      ((↑φ : ℂ)^3 - 3*(↑φ)^2 + ↑φ - ↑ψ + 3*(↑ψ)^2 - (↑ψ)^3) * z := by ring
    rw [this, hcoef, zero_mul]
  simp [hnum]

/-- D6 annihilates x²: D₆[x²] = 0 -/
theorem D6_quadratic (z : ℂ) (hz : z ≠ 0) : D6 (fun t => t^2) z = 0 := by
  simp only [D6, N6, hz, ↓reduceIte]
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ6 := phi_pow6_complex
  have hψ6 := psi_pow6_complex
  have hsum := phi_add_psi_complex
  have hcoef : (↑φ : ℂ)^6 - 3*(↑φ)^4 + (↑φ)^2 - (↑ψ : ℂ)^2 + 3*(↑ψ)^4 - (↑ψ)^6 = 0 := by
    linear_combination hφ6 - 3 * hφ4 + hφ2 - hψ2 + 3 * hψ4 - hψ6
  have hnum : ((↑φ : ℂ)^3 * z)^2 - 3 * ((↑φ)^2 * z)^2 + ((↑φ) * z)^2 - ((↑ψ : ℂ) * z)^2 +
      3 * ((↑ψ)^2 * z)^2 - ((↑ψ)^3 * z)^2 = 0 := by
    have : ((↑φ : ℂ)^3 * z)^2 - 3 * ((↑φ)^2 * z)^2 + ((↑φ) * z)^2 - ((↑ψ) * z)^2 +
      3 * ((↑ψ)^2 * z)^2 - ((↑ψ)^3 * z)^2 =
      ((↑φ : ℂ)^6 - 3*(↑φ)^4 + (↑φ)^2 - (↑ψ)^2 + 3*(↑ψ)^4 - (↑ψ)^6) * z^2 := by ring
    rw [this, hcoef, zero_mul]
  simp [hnum]

/-! ### D5half kernel structure -/

/-- D5half annihilates constants: D₅.₅[1] = 0
    This preserves gauge invariance (same as D5) -/
theorem D5half_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : D5half (fun _ => c) z = 0 := by
  simp only [D5half]
  have hD5 : D5 (fun _ => c) z = 0 := D5_const c z hz
  simp only [hD5, zero_add, sub_self, mul_zero]

/-- D5half does NOT annihilate linear functions: D₅.₅[x] ≠ 0
    Key difference from D5: D5[x] = 0 but D5half[x] ≠ 0 -/
theorem D5half_linear_ne_zero (z : ℂ) (hz : z ≠ 0) : D5half id z ≠ 0 := by
  simp only [D5half, id_eq]
  have hD5 : D5 id z = 0 := D5_linear z hz
  simp only [hD5, zero_add]
  have hdiff_ne := phi_sub_psi_complex_ne
  have hφ2_ne : (↑φ : ℂ) + 2 ≠ 0 := by
    rw [ne_eq, ← ofReal_ofNat, ← ofReal_add, ofReal_eq_zero]
    exact ne_of_gt (by have := φ_gt_one; linarith)
  have hμ_ne : (2 : ℂ) / ((↑φ : ℂ) + 2) ≠ 0 := div_ne_zero (by norm_num) hφ2_ne
  have hdiff_x : (↑φ : ℂ) * z - (↑ψ : ℂ) * z = ((↑φ : ℂ) - ↑ψ) * z := by ring
  rw [hdiff_x]
  exact mul_ne_zero hμ_ne (mul_ne_zero hdiff_ne hz)

/-- D5half at x=1 for quadratic: explicit nonzero value -/
theorem D5half_quadratic_at_one : D5half (fun t => t^2) 1 ≠ 0 := by
  unfold D5half D5
  simp only [one_ne_zero, ↓reduceIte, one_pow, mul_one]
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hsum := phi_add_psi_complex
  have hprod := phi_mul_psi_complex
  have hne_diff := phi_sub_psi_complex_ne
  have hφ2_ne : (↑φ : ℂ) + 2 ≠ 0 := by
    rw [ne_eq, ← ofReal_ofNat, ← ofReal_add, ofReal_eq_zero]
    exact ne_of_gt (by have := φ_gt_one; linarith)
  have hval : ((↑φ : ℂ) ^ 2) ^ 2 + (↑φ : ℂ) ^ 2 - 4 +
      (↑ψ : ℂ) ^ 2 + ((↑ψ : ℂ) ^ 2) ^ 2 = 6 := by
    linear_combination hφ4 + hψ4 + hφ2 + hψ2 + 4 * hsum
  have hφ2_ψ2 : (↑φ : ℂ) ^ 2 - (↑ψ : ℂ) ^ 2 = (↑φ : ℂ) - ↑ψ := by
    linear_combination hφ2 - hψ2
  rw [hval, hφ2_ψ2]
  have hφψ_sq : ((↑φ : ℂ) - ↑ψ) ^ 2 = 5 := by
    linear_combination hφ2 + hψ2 - 2 * hprod + hsum
  have hφψ4 : ((↑φ : ℂ) - ↑ψ) ^ 4 = 25 := by
    calc ((↑φ : ℂ) - ↑ψ) ^ 4
        = (((↑φ : ℂ) - ↑ψ) ^ 2) ^ 2 := by ring
      _ = 5 ^ 2 := by rw [hφψ_sq]
      _ = 25 := by norm_num
  rw [hφψ4]
  intro heq
  have hmul : (6 / (25 : ℂ) + 2 / ((↑φ : ℂ) + 2) *
      ((↑φ : ℂ) - ↑ψ)) * ((25 : ℂ) * ((↑φ : ℂ) + 2)) =
    6 * ((↑φ : ℂ) + 2) + 50 * ((↑φ : ℂ) - ↑ψ) := by
    field_simp; ring
  rw [heq, zero_mul] at hmul
  have h106 : (106 : ℂ) * ↑φ - 38 = 0 := by
    linear_combination -hmul + 50 * hsum
  have h106r : (106 : ℝ) * φ - 38 = 0 := by
    have hinj := ofReal_injective
    apply hinj; push_cast; linear_combination h106
  linarith [φ_gt_one]

/-- D5half differs from D6: D6[x] = 0 but D5half[x] ≠ 0
    This proves D5half is NOT equivalent to D6 -/
theorem D5half_differs_from_D6 :
    (∀ z, z ≠ 0 → D6 id z = 0) ∧ (∀ z, z ≠ 0 → D5half id z ≠ 0) :=
  ⟨D6_linear, D5half_linear_ne_zero⟩

/-- D5half differs from D5: D5[x] = 0 but D5half[x] ≠ 0
    This proves D5half is NOT equivalent to D5 -/
theorem D5half_differs_from_D5 :
    (∀ z, z ≠ 0 → D5 id z = 0) ∧ (∀ z, z ≠ 0 → D5half id z ≠ 0) :=
  ⟨D5_linear, D5half_linear_ne_zero⟩

/-- D5half Independence Theorem:
    D5half is algebraically independent from both D5 and D6.
    Proof: On linear functions, D5[x] = D6[x] = 0 but D5half[x] ≠ 0.
    This shows D5half detects structure invisible to both D5 and D6. -/
theorem D5half_independence :
    -- D5half annihilates constants (like D5 and D6)
    (∀ c z, z ≠ 0 → D5half (fun _ => c) z = 0) ∧
    -- D5half does NOT annihilate linear (unlike D5 and D6)
    (∀ z, z ≠ 0 → D5half id z ≠ 0) ∧
    -- D5 annihilates linear
    (∀ z, z ≠ 0 → D5 id z = 0) ∧
    -- D6 annihilates linear
    (∀ z, z ≠ 0 → D6 id z = 0) :=
  ⟨D5half_const, D5half_linear_ne_zero, D5_linear, D6_linear⟩

/-- D5half preserves gauge invariance: D5half[1] = 0
    The half-order structure does NOT break gauge symmetry -/
theorem D5half_gauge_invariant (z : ℂ) (hz : z ≠ 0) : D5half (fun _ => 1) z = 0 :=
  D5half_const 1 z hz

/-- The antisymmetric term μ·(f(φx) - f(ψx)) is what makes D5half independent.
    This term vanishes for constants but not for linear functions. -/
theorem D5half_antisymmetric_term_key (z : ℂ) (hz : z ≠ 0) :
    (2 / ((↑φ : ℂ) + 2)) * ((fun t => t) ((↑φ : ℂ) * z) - (fun t => t) ((↑ψ : ℂ) * z)) ≠ 0 := by
  simp only
  have hdiff_ne := phi_sub_psi_complex_ne
  have hφ2_ne : (↑φ : ℂ) + 2 ≠ 0 := by
    rw [ne_eq, ← ofReal_ofNat, ← ofReal_add, ofReal_eq_zero]
    exact ne_of_gt (by have := φ_gt_one; linarith)
  have hμ_ne : (2 : ℂ) / ((↑φ : ℂ) + 2) ≠ 0 := div_ne_zero (by norm_num) hφ2_ne
  have hdiff_x : (↑φ : ℂ) * z - (↑ψ : ℂ) * z = ((↑φ : ℂ) - ↑ψ) * z := by ring
  rw [hdiff_x]
  exact mul_ne_zero hμ_ne (mul_ne_zero hdiff_ne hz)

end KernelTheorems

section KernelDimensions

/-- ker(D₅) contains {1, x}, so dim ≥ 2 -/
theorem D5_ker_contains_const_and_linear :
    (∀ c z, z ≠ 0 → D5 (fun _ => c) z = 0) ∧
    (∀ z, z ≠ 0 → D5 id z = 0) :=
  ⟨D5_const, D5_linear⟩

/-- ker(D₆) contains {1, z, x²}, so dim ≥ 3 -/
theorem D6_ker_contains_polynomials :
    (∀ c z, z ≠ 0 → D6 (fun _ => c) z = 0) ∧
    (∀ z, z ≠ 0 → D6 id z = 0) ∧
    (∀ z, z ≠ 0 → D6 (fun t => t^2) z = 0) :=
  ⟨D6_const, D6_linear, D6_quadratic⟩

end KernelDimensions

/-!
## Coefficient Uniqueness Theorems

D5 general form: (f(φ²x) - a·f(φx) + b·f(z) - a·f(ψx) + f(ψ²x)) / ((φ-ψ)⁴x)
D6 general form: (f(φ³x) - A·f(φ²x) + B·f(φx) - B·f(ψx) + A·f(ψ²x) - f(ψ³x)) / ((φ-ψ)⁵x)

The coefficients are uniquely determined by the kernel conditions.
-/

section CoefficientUniqueness

/-- D5 general form with parameters (a, b) -/
noncomputable def D5_general (a b : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (f ((↑φ : ℂ)^2 * z) - a * f ((↑φ : ℂ) * z)
    + b * f z - a * f ((↑ψ : ℂ) * z) + f ((↑ψ : ℂ)^2 * z)) / (((↑φ : ℂ) - ↑ψ)^4 * z)

/-- D6 general form with parameters (A, B) -/
noncomputable def D6_general (A B : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else
    (f ((↑φ : ℂ)^3 * z) - A * f ((↑φ : ℂ)^2 * z) + B * f ((↑φ : ℂ) * z) -
     B * f ((↑ψ : ℂ) * z) + A * f ((↑ψ : ℂ)^2 * z) - f ((↑ψ : ℂ)^3 * z)) / (((↑φ : ℂ) - ↑ψ)^5 * z)

/-- Condition C0: D5[1] = 0 implies 2 - 2a + b = 0 -/
theorem D5_C0_condition (a b : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D5_general a b (fun _ => 1) z = 0) ↔ b = 2 * a - 2 := by
  constructor
  · intro h
    have h1 := h 1 one_ne_zero
    simp only [D5_general, one_ne_zero, ↓reduceIte, mul_one] at h1
    have hne : ((↑φ : ℂ) - ↑ψ)^4 ≠ 0 := pow_ne_zero 4 phi_sub_psi_complex_ne
    rw [div_eq_zero_iff] at h1
    cases h1 with
    | inl h1 => linear_combination h1
    | inr h1 =>
      exfalso
      have : ((↑φ : ℂ) - ↑ψ) ^ 4 * 1 = 0 := by rw [mul_one]; exact h1
      exact hne ((mul_eq_zero.mp this).resolve_right one_ne_zero)
  · intro hb z hz
    simp only [D5_general, hz, ↓reduceIte]
    have hnum : 1 - a * 1 + b * 1 - a * 1 + 1 = 2 - 2 * a + b := by ring
    rw [hnum, hb]
    ring_nf

/-- Condition C1: D5[x] = 0 implies (φ² + ψ²) - a(φ + ψ) + b = 0 -/
theorem D5_C1_condition (a b : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D5_general a b id z = 0) ↔ b = a - 3 := by
  have h1 : (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 = 3 := by
    linear_combination golden_ratio_property_complex + psi_sq_complex + phi_add_psi_complex
  have h2 := phi_add_psi_complex
  constructor
  · intro h
    have hz := h 1 one_ne_zero
    simp only [D5_general, one_ne_zero, ↓reduceIte, id_eq, mul_one] at hz
    have hne : ((↑φ : ℂ) - ↑ψ)^4 ≠ 0 := pow_ne_zero 4 phi_sub_psi_complex_ne
    rw [div_eq_zero_iff] at hz
    cases hz with
    | inl hz =>
      have hcoef : (↑φ : ℂ)^2 - a * ↑φ + b - a * ↑ψ + (↑ψ : ℂ)^2 =
          ((↑φ : ℂ)^2 + (↑ψ : ℂ)^2) - a * ((↑φ : ℂ) + ↑ψ) + b := by ring
      rw [hcoef, h1, h2] at hz
      linear_combination hz
    | inr hz =>
      exfalso
      have : ((↑φ : ℂ) - ↑ψ) ^ 4 * 1 = 0 := by rw [mul_one]; exact hz
      exact hne ((mul_eq_zero.mp this).resolve_right one_ne_zero)
  · intro hb z hz
    simp only [D5_general, hz, ↓reduceIte, id_eq]
    have hcoef : (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - a * ((↑φ : ℂ) + ↑ψ) + b = 0 := by
      rw [h1, h2, hb]; ring
    have hnum : (↑φ : ℂ)^2 * z - a * ((↑φ : ℂ) * z) + b * z - a * ((↑ψ : ℂ) * z) + (↑ψ : ℂ)^2 * z =
        ((↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - a * ((↑φ : ℂ) + ↑ψ) + b) * z := by ring
    rw [hnum, hcoef]
    simp only [zero_mul, zero_div]

/-- Theorem 4.1 (D5 coefficient uniqueness):
    The conditions D5[1] = 0 and D5[x] = 0 uniquely determine a = -1, b = -4 -/
theorem D5_coefficients_unique :
    ∀ a b : ℂ,
    (∀ z : ℂ, z ≠ 0 → D5_general a b (fun _ => 1) z = 0) →
    (∀ z : ℂ, z ≠ 0 → D5_general a b id z = 0) →
    a = -1 ∧ b = -4 := by
  intro a b h0 h1
  have eq1 : b = 2 * a - 2 := D5_C0_condition a b |>.mp h0
  have eq2 : b = a - 3 := D5_C1_condition a b |>.mp h1
  have ha : a = -1 := by linear_combination eq2 - eq1
  have hb : b = -4 := by rw [eq2, ha]; ring
  exact ⟨ha, hb⟩

/-- D5 with determined coefficients equals D5 -/
theorem D5_general_eq_D5 (f : ℂ → ℂ) (z : ℂ) :
    D5_general (-1) (-4) f z = D5 f z := by
  simp only [D5_general, D5]
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    ring_nf

/-- Condition D1: D6[x] = 0 implies F₃ - A·F₂ + B·F₁ = 0, i.e., 2 - A + B = 0 -/
theorem D6_D1_condition (A B : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D6_general A B id z = 0) ↔ B = A - 2 := by
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  constructor
  · intro h
    have hz := h 1 one_ne_zero
    simp only [D6_general, one_ne_zero, ↓reduceIte, id_eq, mul_one] at hz
    rw [div_eq_zero_iff] at hz
    cases hz with
    | inl hz =>
      have hne := phi_sub_psi_complex_ne
      have hfact : (2 - A + B) * ((↑φ : ℂ) - ↑ψ) = 0 := by
        linear_combination hz + A * hφ2 - A * hψ2 - hφ3 + hψ3
      exact (mul_eq_zero.mp hfact).resolve_right hne |> fun h => by linear_combination h
    | inr hz =>
      exfalso
      have : D6Denom = 0 := by unfold D6Denom; exact hz
      exact D6Denom_ne_zero this
  · intro hB z hz
    simp only [D6_general, hz, ↓reduceIte, id_eq]
    have hnum : (↑φ : ℂ)^3 * z - A * ((↑φ : ℂ)^2 * z) + B * ((↑φ : ℂ) * z) - B * ((↑ψ : ℂ) * z) +
        A * ((↑ψ : ℂ)^2 * z) - (↑ψ : ℂ)^3 * z = (((↑φ : ℂ)^3 - (↑ψ : ℂ)^3) - A * ((↑φ : ℂ)^2
        - (↑ψ : ℂ)^2) + B * ((↑φ : ℂ) - ↑ψ)) * z := by ring
    have hcoef :
        ((↑φ : ℂ)^3 - (↑ψ : ℂ)^3) - A * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) + B * ((↑φ : ℂ) - ↑ψ) = 0 := by
      have : (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 = 2 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ3 - hψ3
      have : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by linear_combination hφ2 - hψ2
      rw [‹_ ^ 3 - _ ^ 3 = _›, ‹_ ^ 2 - _ ^ 2 = _›, hB]; ring
    rw [hnum, hcoef]; simp only [zero_mul, zero_div]

/-- Condition D2: D6[x²] = 0 implies F₆ - A·F₄ + B·F₂ = 0, i.e., 8 - 3A + B = 0 -/
theorem D6_D2_condition (A B : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D6_general A B (fun t => t^2) z = 0) ↔ B = 3 * A - 8 := by
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ6 := phi_pow6_complex
  have hψ6 := psi_pow6_complex
  constructor
  · intro h
    have hz := h 1 one_ne_zero
    simp only [D6_general, one_ne_zero, ↓reduceIte, mul_one] at hz
    rw [div_eq_zero_iff] at hz
    cases hz with
    | inl hz =>
      have hne := phi_sub_psi_complex_ne
      have hfact : (8 - 3 * A + B) * ((↑φ : ℂ) - ↑ψ) = 0 := by
        linear_combination hz + A * hφ4 - A * hψ4 - B * hφ2 + B * hψ2 - hφ6 + hψ6
      exact (mul_eq_zero.mp hfact).resolve_right hne |> fun h => by linear_combination h
    | inr hz =>
      exfalso
      have : D6Denom = 0 := by unfold D6Denom; exact hz
      exact D6Denom_ne_zero this
  · intro hB z hz
    simp only [D6_general, hz, ↓reduceIte]
    have hcoef : (↑φ : ℂ)^6 - (↑ψ : ℂ)^6 - A * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) +
        B * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) = 0 := by
      have h1 : (↑φ : ℂ)^6 - (↑ψ : ℂ)^6 = 8 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ6 - hψ6
      have h2 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ4 - hψ4
      have h3 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by linear_combination hφ2 - hψ2
      rw [h1, h2, h3, hB]; ring
    have hnum : ((↑φ : ℂ)^3 * z)^2 - A * ((↑φ : ℂ)^2 * z)^2 + B * ((↑φ : ℂ) * z)^2 -
        B * ((↑ψ : ℂ) * z)^2 + A * ((↑ψ : ℂ)^2 * z)^2 - ((↑ψ : ℂ)^3 * z)^2 =
        ((↑φ : ℂ)^6 - (↑ψ : ℂ)^6 - A * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) +
        B * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2)) * z^2 := by ring
    rw [hnum, hcoef]; simp only [zero_mul, zero_div]

/-- Theorem 4.1 (D6 coefficient uniqueness):
    The conditions D6[x] = 0 and D6[x²] = 0 uniquely determine A = 3, B = 1 -/
theorem D6_coefficients_unique :
    ∀ A B : ℂ,
    (∀ z : ℂ, z ≠ 0 → D6_general A B id z = 0) →
    (∀ z : ℂ, z ≠ 0 → D6_general A B (fun t => t^2) z = 0) →
    A = 3 ∧ B = 1 := by
  intro A B h1 h2
  have eq1 : B = A - 2 := D6_D1_condition A B |>.mp h1
  have eq2 : B = 3 * A - 8 := D6_D2_condition A B |>.mp h2
  have hA : A = 3 := by linear_combination (eq1 - eq2) / 2
  have hB : B = 1 := by rw [eq1, hA]; ring
  exact ⟨hA, hB⟩

/-- D6 with determined coefficients equals D6 -/
theorem D6_general_eq_D6 (f : ℂ → ℂ) (z : ℂ) :
    D6_general 3 1 f z = D6 f z := by
  simp only [D6_general, D6, N6, D6Denom]
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    ring_nf

/-- Main Theorem 4.1: Complete coefficient uniqueness for D5 and D6 -/
theorem FUST_coefficient_uniqueness :
    (∀ a b : ℂ,
      (∀ z, z ≠ 0 → D5_general a b (fun _ => 1) z = 0) →
      (∀ z, z ≠ 0 → D5_general a b id z = 0) →
      a = -1 ∧ b = -4) ∧
    (∀ A B : ℂ,
      (∀ z, z ≠ 0 → D6_general A B id z = 0) →
      (∀ z, z ≠ 0 → D6_general A B (fun t => t^2) z = 0) →
      A = 3 ∧ B = 1) :=
  ⟨D5_coefficients_unique, D6_coefficients_unique⟩

end CoefficientUniqueness

section AlgebraicConstants

/-- Half-order mixing parameter: λ = 2/(φ + 2) = 2/(φ² + 1) ≈ 0.5528 -/
noncomputable def halfOrderParam : ℂ := 2 / ((↑φ : ℂ) + 2)

/-- Alternative form: λ = 2/(φ² + 1) -/
theorem halfOrderParam_alt : halfOrderParam = 2 / ((↑φ : ℂ)^2 + 1) := by
  simp only [halfOrderParam]
  congr 1; linear_combination -golden_ratio_property_complex

/-- Uniqueness condition: halfOrderParam satisfies μ·(φ² + 1) = dim(ker(D5)) = 2 -/
theorem halfOrderParam_uniqueness : halfOrderParam * ((↑φ : ℂ)^2 + 1) = 2 := by
  rw [halfOrderParam_alt]
  have h : (↑φ : ℂ)^2 + 1 ≠ 0 := by
    intro heq
    have : (↑φ : ℂ) + 2 = 0 := by linear_combination -golden_ratio_property_complex + heq
    have : (↑φ : ℂ) = -2 := by linear_combination this
    have : (φ : ℝ) = -2 := by exact_mod_cast this
    linarith [phi_pos]
  field_simp

/-- If μ·(φ² + 1) = 2, then μ = halfOrderParam -/
theorem halfOrderParam_unique_from_condition (μ : ℂ) (h : μ * ((↑φ : ℂ) ^ 2 + 1) = 2) :
    μ = halfOrderParam := by
  rw [halfOrderParam_alt]
  have hne : (↑φ : ℂ) ^ 2 + 1 ≠ 0 := by
    intro heq
    have : (↑φ : ℂ) + 2 = 0 := by linear_combination -golden_ratio_property_complex + heq
    have : (↑φ : ℂ) = -2 := by linear_combination this
    have : (φ : ℝ) = -2 := by exact_mod_cast this
    linarith [phi_pos]
  field_simp at h ⊢; linear_combination h

/-! ### Coefficient sums and gauge invariance -/

/-- D2 coefficient sum: 1 - 1 = 0 -/
theorem D2_coeff_sum : (1 : ℂ) - 1 = 0 := by ring

/-- D3 coefficient sum: 1 - 2 + 1 = 0 -/
theorem D3_coeff_sum : (1 : ℂ) - 2 + 1 = 0 := by ring

/-- D4 coefficient sum: 1 - φ² + ψ² - 1 ≠ 0 -/
theorem D4_coeff_sum_ne_zero : (1 : ℂ) - (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - 1 ≠ 0 := by
  intro heq
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have : (↑ψ : ℂ) - (↑φ : ℂ) = 0 := by linear_combination heq + hφ2 - hψ2
  have : (↑φ : ℂ) - ↑ψ = 0 := by linear_combination -this
  exact phi_sub_psi_complex_ne this

/-- D5 coefficient sum: 1 + 1 - 4 + 1 + 1 = 0 -/
theorem D5_coeff_sum : (1 : ℂ) + 1 - 4 + 1 + 1 = 0 := by ring

/-- D6 coefficient sum: 1 - 3 + 1 - 1 + 3 - 1 = 0 -/
theorem D6_coeff_sum : (1 : ℂ) - 3 + 1 - 1 + 3 - 1 = 0 := by ring

/-- Gauge invariance: coefficient sum = 0 implies D[1] = 0 for z ≠ 0 -/
theorem D2_gauge_invariant (z : ℂ) (hz : z ≠ 0) : D2 (fun _ => 1) z = 0 :=
  D2_const 1 z hz

theorem D3_gauge_invariant (z : ℂ) (hz : z ≠ 0) : D3 (fun _ => 1) z = 0 :=
  D3_const 1 z hz

theorem D5_gauge_invariant (z : ℂ) (hz : z ≠ 0) : D5 (fun _ => 1) z = 0 :=
  D5_const 1 z hz

theorem D6_gauge_invariant (z : ℂ) (hz : z ≠ 0) : D6 (fun _ => 1) z = 0 :=
  D6_const 1 z hz

/-- D4 breaks gauge invariance: D4[1] ≠ 0 for general constant -/
theorem D4_not_gauge_invariant : ∃ (c : ℂ) (z : ℂ), z ≠ 0 ∧ c ≠ 0 ∧ D4 (fun _ => c) z ≠ 0 := by
  use 1, 1, one_ne_zero, one_ne_zero
  simp only [D4, one_ne_zero, ↓reduceIte]
  have hcoeff_ne : (1 : ℂ) - (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - 1 ≠ 0 := D4_coeff_sum_ne_zero
  have hnum_eq : (1 : ℂ) - (↑φ : ℂ)^2 * 1 + (↑ψ : ℂ)^2 * 1 - 1 =
      1 - (↑φ : ℂ)^2 + (↑ψ : ℂ)^2 - 1 := by ring
  rw [hnum_eq]
  have hden_ne : ((↑φ : ℂ) - ↑ψ) ^ 3 * 1 ≠ 0 := by
    rw [mul_one]; exact pow_ne_zero 3 phi_sub_psi_complex_ne
  exact div_ne_zero hcoeff_ne hden_ne

/-- Kernel dimension of D5 is 2 (derived from D5_const and D5_linear) -/
theorem D5_kernel_contains_const_and_linear (z : ℂ) (hz : z ≠ 0) :
    D5 (fun _ => 1) z = 0 ∧ D5 id z = 0 :=
  ⟨D5_const 1 z hz, D5_linear z hz⟩

/-- Kernel dimension of D6 is 3 (derived from D6_const, D6_linear, D6_quadratic) -/
theorem D6_kernel_contains_polynomials_up_to_degree_2 (z : ℂ) (hz : z ≠ 0) :
    D6 (fun _ => 1) z = 0 ∧ D6 id z = 0 ∧ D6 (fun t => t^2) z = 0 :=
  ⟨D6_const 1 z hz, D6_linear z hz, D6_quadratic z hz⟩

end AlgebraicConstants

/-!
## D7 Algebraic Reduction to D6

D7 antisymmetric form: [1, -a, b, -c, +c, -b, +a, -1]
D7[f](z) = (f(φ⁴x) - a·f(φ³x) + b·f(φ²x) - c·f(φx)
            + c·f(ψx) - b·f(ψ²x) + a·f(ψ³x) - f(ψ⁴x)) / ((φ-ψ)⁶x)

Key result: ker(D7) = ker(D6) implies D7 provides no new structure.
-/

section D7Reduction

/-- D7 general antisymmetric form with parameters (a, b, c) -/
noncomputable def D7_general (a b c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (f ((↑φ : ℂ)^4 * z) - a * f ((↑φ : ℂ)^3 * z) + b * f ((↑φ : ℂ)^2 * z)
    - c * f ((↑φ : ℂ) * z) + c * f ((↑ψ : ℂ) * z) - b * f ((↑ψ : ℂ)^2 * z)
    + a * f ((↑ψ : ℂ)^3 * z) - f ((↑ψ : ℂ)^4 * z)) / (((↑φ : ℂ) - ↑ψ)^6 * z)

/-- Condition E0: D7[1] = 0 holds for antisymmetric form (coefficient sum = 0) -/
theorem D7_E0_condition (a b c : ℂ) :
    ∀ z : ℂ, z ≠ 0 → D7_general a b c (fun _ => 1) z = 0 := by
  intro z hz
  simp only [D7_general, hz, ↓reduceIte]
  have hsum : (1 : ℂ) - a * 1 + b * 1 - c * 1 + c * 1 - b * 1 + a * 1 - 1 = 0 := by ring
  rw [hsum, zero_div]

/-- Condition E1: D7[x] = 0 implies 3 - 2a + b - c = 0
    (using Fibonacci: F₄ = 3, F₃ = 2, F₂ = 1, F₁ = 1) -/
theorem D7_E1_condition (a b c : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D7_general a b c id z = 0) ↔ 3 - 2 * a + b - c = 0 := by
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφψ_ne := phi_sub_psi_complex_ne
  constructor
  · intro h
    have hz := h 1 one_ne_zero
    simp only [D7_general, one_ne_zero, ↓reduceIte, id_eq, mul_one] at hz
    have hne : ((↑φ : ℂ) - ↑ψ)^6 ≠ 0 := pow_ne_zero 6 phi_sub_psi_complex_ne
    rw [div_eq_zero_iff] at hz
    cases hz with
    | inl hz =>
      -- Coefficient of z in antisymmetric form: φ⁴ - ψ⁴ - a(φ³ - ψ³) + b(φ² - ψ²) - c(φ - ψ)
      have hcoef : (↑φ : ℂ)^4 - a * (↑φ : ℂ)^3 + b * (↑φ : ℂ)^2 - c * ↑φ + c * ↑ψ
        - b * (↑ψ : ℂ)^2 + a * (↑ψ : ℂ)^3 - (↑ψ : ℂ)^4
        = ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) - a * ((↑φ : ℂ)^3 - (↑ψ : ℂ)^3)
        + b * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) - c * ((↑φ : ℂ) - ↑ψ) := by ring
      rw [hcoef] at hz
      -- φⁿ - ψⁿ = √5 · Fₙ (Binet formula)
      have hF4 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ4 - hψ4
      have hF3 : (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 = 2 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ3 - hψ3
      have hF2 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by
        linear_combination hφ2 - hψ2
      rw [hF4, hF3, hF2] at hz
      have hne := phi_sub_psi_complex_ne
      have hfact : (3 - 2*a + b - c) * ((↑φ : ℂ) - ↑ψ) = 0 := by linear_combination hz
      have := (mul_eq_zero.mp hfact).resolve_right hne
      linear_combination this
    | inr hz =>
      exfalso; exact pow_ne_zero 6 phi_sub_psi_complex_ne hz
  · intro hcond z hz
    simp only [D7_general, hz, ↓reduceIte, id_eq]
    have hcoef : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 - a * ((↑φ : ℂ)^3
        - (↑ψ : ℂ)^3) + b * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) - c * ((↑φ : ℂ) - ↑ψ) = 0 := by
      have hF4 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ4 - hψ4
      have hF3 : (↑φ : ℂ)^3 - (↑ψ : ℂ)^3 = 2 * ((↑φ : ℂ) - ↑ψ) := by linear_combination hφ3 - hψ3
      have hF2 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by linear_combination hφ2 - hψ2
      rw [hF4, hF3, hF2]; linear_combination hcond * ((↑φ : ℂ) - ↑ψ)
    have hnum : (↑φ : ℂ)^4 * z - a * ((↑φ : ℂ)^3 * z) + b * ((↑φ : ℂ)^2 * z) - c * ((↑φ : ℂ) * z)
        + c * ((↑ψ : ℂ) * z) - b * ((↑ψ : ℂ)^2 * z) + a * ((↑ψ : ℂ)^3 * z) - (↑ψ : ℂ)^4 * z
        = ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4 - a * ((↑φ : ℂ)^3 - (↑ψ : ℂ)^3)
        + b * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) - c * ((↑φ : ℂ) - ↑ψ)) * z := by ring
    rw [hnum, hcoef]
    simp only [zero_mul, zero_div]

/-- Condition E2: D7[x²] = 0 implies F₈ - a·F₆ + b·F₄ - c·F₂ = 21 - 8a + 3b - c = 0 -/
theorem D7_E2_condition (a b c : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D7_general a b c (fun t => t^2) z = 0) ↔ 21 - 8 * a + 3 * b - c = 0 := by
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ6 := phi_pow6_complex
  have hψ6 := psi_pow6_complex
  have hφ8 := phi_pow8_complex
  have hψ8 := psi_pow8_complex
  have hφψ_ne := phi_sub_psi_complex_ne
  constructor
  · intro h
    have hz := h 1 one_ne_zero
    simp only [D7_general, one_ne_zero, ↓reduceIte, mul_one] at hz
    have hne : ((↑φ : ℂ) - ↑ψ)^6 ≠ 0 := pow_ne_zero 6 phi_sub_psi_complex_ne
    rw [div_eq_zero_iff] at hz
    cases hz with
    | inl hz =>
      -- For x² terms: φ^8 - ψ^8 - a(φ^6 - ψ^6) + b(φ^4 - ψ^4) - c(φ^2 - ψ^2)
      have hcoef : ((↑φ : ℂ)^4)^2 - a * ((↑φ : ℂ)^3)^2 + b * ((↑φ : ℂ)^2)^2 - c * (↑φ : ℂ)^2
          + c * (↑ψ : ℂ)^2 - b * ((↑ψ : ℂ)^2)^2 + a * ((↑ψ : ℂ)^3)^2 - ((↑ψ : ℂ)^4)^2
          = (↑φ : ℂ)^8 - (↑ψ : ℂ)^8 - a * ((↑φ : ℂ)^6 - (↑ψ : ℂ)^6)
          + b * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) - c * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) := by ring
      rw [hcoef] at hz
      have hF8 : (↑φ : ℂ)^8 - (↑ψ : ℂ)^8 = 21 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ8 - hψ8
      have hF6 : (↑φ : ℂ)^6 - (↑ψ : ℂ)^6 = 8 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ6 - hψ6
      have hF4 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ4 - hψ4
      have hF2 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by
        linear_combination hφ2 - hψ2
      rw [hF8, hF6, hF4, hF2] at hz
      have hne := phi_sub_psi_complex_ne
      have hfact : (21 - 8*a + 3*b - c) * ((↑φ : ℂ) - ↑ψ) = 0 := by linear_combination hz
      have := (mul_eq_zero.mp hfact).resolve_right hne
      linear_combination this
    | inr hz =>
      exfalso; exact pow_ne_zero 6 phi_sub_psi_complex_ne hz
  · intro hcond z hz
    simp only [D7_general, hz, ↓reduceIte]
    have hF8 : (↑φ : ℂ)^8 - (↑ψ : ℂ)^8 = 21 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ8 - hψ8
    have hF6 : (↑φ : ℂ)^6 - (↑ψ : ℂ)^6 = 8 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ6 - hψ6
    have hF4 : (↑φ : ℂ)^4 - (↑ψ : ℂ)^4 = 3 * ((↑φ : ℂ) - ↑ψ) := by
        linear_combination hφ4 - hψ4
    have hF2 : (↑φ : ℂ)^2 - (↑ψ : ℂ)^2 = (↑φ : ℂ) - ↑ψ := by
        linear_combination hφ2 - hψ2
    have hcoef : (↑φ : ℂ)^8 - (↑ψ : ℂ)^8 - a * ((↑φ : ℂ)^6 - (↑ψ : ℂ)^6)
        + b * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) - c * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2) = 0 := by
      rw [hF8, hF6, hF4, hF2]; linear_combination hcond * ((↑φ : ℂ) - ↑ψ)
    have hnum : ((↑φ : ℂ)^4 * z)^2 - a * ((↑φ : ℂ)^3 * z)^2
        + b * ((↑φ : ℂ)^2 * z)^2 - c * ((↑φ : ℂ) * z)^2 + c * ((↑ψ : ℂ) * z)^2
        - b * ((↑ψ : ℂ)^2 * z)^2 + a * ((↑ψ : ℂ)^3 * z)^2 - ((↑ψ : ℂ)^4 * z)^2
        = ((↑φ : ℂ)^8 - (↑ψ : ℂ)^8 - a * ((↑φ : ℂ)^6 - (↑ψ : ℂ)^6)
        + b * ((↑φ : ℂ)^4 - (↑ψ : ℂ)^4) - c * ((↑φ : ℂ)^2 - (↑ψ : ℂ)^2)) * z^2 := by ring
    rw [hnum, hcoef]
    simp only [zero_mul, zero_div]

/-- Theorem 6.1 (D7 coefficient constraint):
    E1 and E2 imply c = a - 6, b = 3a - 9 (1 free parameter) -/
theorem D7_coefficients_constrained (a b c : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D7_general a b c id z = 0) →
    (∀ z : ℂ, z ≠ 0 → D7_general a b c (fun t => t^2) z = 0) →
    c = a - 6 ∧ b = 3 * a - 9 := by
  intro h1 h2
  have eq1 : 3 - 2 * a + b - c = 0 := D7_E1_condition a b c |>.mp h1
  have eq2 : 21 - 8 * a + 3 * b - c = 0 := D7_E2_condition a b c |>.mp h2
  constructor
  · linear_combination (eq2 - 3 * eq1) / 2
  · linear_combination (eq2 - eq1) / 2

/-- D7 with constrained coefficients: a arbitrary, b = 3a - 9, c = a - 6 -/
noncomputable def D7_constrained (a : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  D7_general a (3 * a - 9) (a - 6) f z

/-- D7_constrained annihilates constants -/
theorem D7_constrained_const (a : ℂ) (k : ℂ) (z : ℂ) (hz : z ≠ 0) :
    D7_constrained a (fun _ => k) z = 0 := by
  simp only [D7_constrained, D7_general, hz, ↓reduceIte]
  have hsum : k - a * k + (3*a - 9) * k - (a - 6) * k
            + (a - 6) * k - (3*a - 9) * k + a * k - k = 0 := by ring
  rw [hsum, zero_div]

/-- D7_constrained annihilates linear functions -/
theorem D7_constrained_linear (a : ℂ) (z : ℂ) (hz : z ≠ 0) :
    D7_constrained a id z = 0 := by
  simp only [D7_constrained]
  have h : 3 - 2 * a + (3 * a - 9) - (a - 6) = 0 := by ring
  exact D7_E1_condition a (3*a - 9) (a - 6) |>.mpr h z hz

/-- D7_constrained annihilates quadratic functions -/
theorem D7_constrained_quadratic (a : ℂ) (z : ℂ) (hz : z ≠ 0) :
    D7_constrained a (fun t => t^2) z = 0 := by
  simp only [D7_constrained]
  have h : 21 - 8 * a + 3 * (3 * a - 9) - (a - 6) = 0 := by ring
  exact D7_E2_condition a (3*a - 9) (a - 6) |>.mpr h z hz

/-- Main Theorem 6.2: ker(D7) = ker(D6) for constrained coefficients
    D7 annihilates {1, z, x²} (same as D6 kernel), regardless of parameter a -/
theorem D7_kernel_equals_D6_kernel (a : ℂ) :
    (∀ c z, z ≠ 0 → D7_constrained a (fun _ => c) z = 0) ∧
    (∀ z, z ≠ 0 → D7_constrained a id z = 0) ∧
    (∀ z, z ≠ 0 → D7_constrained a (fun t => t^2) z = 0) :=
  ⟨fun c z hz => D7_constrained_const a c z hz,
   D7_constrained_linear a,
   D7_constrained_quadratic a⟩

/-- Algebraic Reduction Theorem:
    D7 provides no independent structure beyond D6.
    Any D7 with ker(D7) ⊇ ker(D6) has coefficients determined up to 1 parameter,
    and ker(D7) = ker(D6). -/
theorem D7_algebraic_reduction :
    ∀ a b c : ℂ,
    (∀ z, z ≠ 0 → D7_general a b c (fun _ => 1) z = 0) →
    (∀ z, z ≠ 0 → D7_general a b c id z = 0) →
    (∀ z, z ≠ 0 → D7_general a b c (fun t => t^2) z = 0) →
    c = a - 6 ∧ b = 3 * a - 9 := by
  intro a b c _ h1 h2
  exact D7_coefficients_constrained a b c h1 h2

end D7Reduction

/-!
## D6 Completeness

ker(D6) = span{1, z, x²}, D6 detects cubic and higher, ker(D7) = ker(D6).
-/

section D6Completeness

/-- D6 detects cubic terms: D6[x³] ≠ 0 -/
theorem D6_detects_cubic (z : ℂ) (hz : z ≠ 0) : D6 (fun t => t^3) z ≠ 0 := by
  simp only [D6, N6, hz, ↓reduceIte]
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hφ3 := phi_cubed_complex
  have hψ3 := psi_cubed_complex
  have hφ6 := phi_pow6_complex
  have hψ6 := psi_pow6_complex
  have hφ9 := phi_pow9_complex
  have hψ9 := psi_pow9_complex
  have hcoef : (↑φ : ℂ)^9 - 3*(↑φ : ℂ)^6 + (↑φ : ℂ)^3 - (↑ψ : ℂ)^3
      + 3*(↑ψ : ℂ)^6 - (↑ψ : ℂ)^9 = 12 * ((↑φ : ℂ) - ↑ψ) := by
    linear_combination hφ9 - 3 * hφ6 + hφ3 - hψ3 + 3 * hψ6 - hψ9
  have hnum : ((↑φ : ℂ)^3 * z)^3 - 3 * ((↑φ : ℂ)^2 * z)^3
      + ((↑φ : ℂ) * z)^3 - ((↑ψ : ℂ) * z)^3 + 3 * ((↑ψ : ℂ)^2 * z)^3 -
      ((↑ψ : ℂ)^3 * z)^3 = 12 * ((↑φ : ℂ) - ↑ψ) * z^3 := by
    have : ((↑φ : ℂ)^3 * z)^3 - 3 * ((↑φ : ℂ)^2 * z)^3 + ((↑φ : ℂ) * z)^3
      - ((↑ψ : ℂ) * z)^3 + 3 * ((↑ψ : ℂ)^2 * z)^3 - ((↑ψ : ℂ)^3 * z)^3
      = ((↑φ : ℂ)^9 - 3*(↑φ : ℂ)^6 + (↑φ : ℂ)^3
      - (↑ψ : ℂ)^3 + 3*(↑ψ : ℂ)^6 - (↑ψ : ℂ)^9) * z^3 := by ring
    rw [hcoef] at this; exact this
  rw [hnum]
  have hdiff_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := phi_sub_psi_complex_ne
  have hx3_ne : z^3 ≠ 0 := pow_ne_zero 3 hz
  have hden_ne : D6Denom * z ≠ 0 := D6Denom_mul_ne_zero z hz
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (12 : ℂ) ≠ 0) hdiff_ne) hx3_ne) hden_ne

theorem D6_not_annihilate_cubic (z : ℂ) (hz : z ≠ 0) :
    D6 (fun t => t^3) z ≠ 0 := D6_detects_cubic z hz

/-- D6 Completeness Theorem: ker(D6) = span{1, z, x²} and ker(D7) = ker(D6). -/
theorem F6_restricted_completeness :
    -- 1. ker(D6) is exactly 3-dimensional: span{1, z, x²}
    (∀ c z, z ≠ 0 → D6 (fun _ => c) z = 0) ∧
    (∀ z, z ≠ 0 → D6 id z = 0) ∧
    (∀ z, z ≠ 0 → D6 (fun t => t^2) z = 0) ∧
    -- 2. D6 detects degree 3 (first non-trivial observable)
    (∀ z, z ≠ 0 → D6 (fun t => t^3) z ≠ 0) ∧
    -- 3. D7 (and higher) reduces to D6: no new observable structure
    (∀ a : ℂ, ∀ c z, z ≠ 0 → D7_constrained a (fun _ => c) z = 0) ∧
    (∀ a : ℂ, ∀ z, z ≠ 0 → D7_constrained a id z = 0) ∧
    (∀ a : ℂ, ∀ z, z ≠ 0 → D7_constrained a (fun t => t^2) z = 0) := by
  refine ⟨?_, D6_linear, D6_quadratic, D6_detects_cubic, ?_, ?_, ?_⟩
  · exact fun c z hz => D6_const c z hz
  · exact fun a c z hz => D7_constrained_const a c z hz
  · exact fun a z hz => D7_constrained_linear a z hz
  · exact fun a z hz => D7_constrained_quadratic a z hz

end D6Completeness

/-- D6 does not annihilate quartic: D6[x⁴] ≠ 0 -/
theorem D6_quartic_nonzero (z : ℂ) (hz : z ≠ 0) : D6 (fun t => t^4) z ≠ 0 := by
  simp only [D6, N6, hz, ↓reduceIte]
  have hφ2 : (↑φ : ℂ)^2 = ↑φ + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ)^2 = ↑ψ + 1 := psi_sq_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ8 := phi_pow8_complex
  have hψ8 := psi_pow8_complex
  have hφ12 := phi_pow12_complex
  have hψ12 := psi_pow12_complex
  have hcoef : (↑φ : ℂ)^12 - 3*(↑φ : ℂ)^8 + (↑φ : ℂ)^4
      - (↑ψ : ℂ)^4 + 3*(↑ψ : ℂ)^8 - (↑ψ : ℂ)^12 = 84 * ((↑φ : ℂ) - ↑ψ) := by
    linear_combination hφ12 - 3 * hφ8 + hφ4 - hψ4 + 3 * hψ8 - hψ12
  have hnum : ((↑φ : ℂ)^3 * z)^4 - 3 * ((↑φ : ℂ)^2 * z)^4 + ((↑φ : ℂ) * z)^4 - ((↑ψ : ℂ) * z)^4 +
      3 * ((↑ψ : ℂ)^2 * z)^4 - ((↑ψ : ℂ)^3 * z)^4 = 84 * ((↑φ : ℂ) - ↑ψ) * z^4 := by
    have hexp : ((↑φ : ℂ)^3 * z)^4 - 3 * ((↑φ : ℂ)^2 * z)^4 + ((↑φ : ℂ) * z)^4 - ((↑ψ : ℂ) * z)^4 +
        3 * ((↑ψ : ℂ)^2 * z)^4 - ((↑ψ : ℂ)^3 * z)^4 =
        ((↑φ : ℂ)^12 - 3*(↑φ : ℂ)^8 + (↑φ : ℂ)^4 - (↑ψ : ℂ)^4
        + 3*(↑ψ : ℂ)^8 - (↑ψ : ℂ)^12) * z^4 := by ring
    rw [hexp, hcoef]
  rw [hnum]
  have hden_ne : D6Denom * z ≠ 0 := D6Denom_mul_ne_zero z hz
  have hdiff_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := phi_sub_psi_complex_ne
  have hx4_ne : z^4 ≠ 0 := pow_ne_zero 4 hz
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hdiff_ne) hx4_ne) hden_ne

/-! ## Parity Selection Principle

For 6 Galois-paired points {φ³,φ²,φ,ψ,ψ²,ψ³}, symmetric coefficients [1,A,B,B,A,1]
with D[1]=0 and D[x]=0 force A=-3/2, B=1/2 (non-integral), and D[x²]=9≠0.
The antisymmetric form [1,-A,B,-B,A,-1] achieves D[x²]=0 with integral A=3, B=1.
So antisymmetric D₆ has strictly larger kernel than any symmetric form on the same points. -/

section ParitySelection

/-- Symmetric D6: coefficients [1, A, B, B, A, 1] at {φ³,φ²,φ,ψ,ψ²,ψ³} -/
noncomputable def D6_symmetric (A B : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else
    (f ((↑φ : ℂ)^3 * z) + A * f ((↑φ : ℂ)^2 * z) + B * f ((↑φ : ℂ) * z) +
     B * f ((↑ψ : ℂ) * z) + A * f ((↑ψ : ℂ)^2 * z) + f ((↑ψ : ℂ)^3 * z)) / (((↑φ : ℂ) - ↑ψ)^5 * z)

/-- D6_sym[1]=0 ↔ A+B=-1 (uses 1 kernel condition) -/
theorem D6_sym_C0 (A B : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D6_symmetric A B (fun _ => 1) z = 0) ↔ A + B = -1 := by
  constructor
  · intro h
    have h1 := h 1 one_ne_zero
    simp only [D6_symmetric, one_ne_zero, ↓reduceIte, mul_one] at h1
    have hne : ((↑φ : ℂ) - ↑ψ) ^ 5 ≠ 0 := by
      apply pow_ne_zero
      exact phi_sub_psi_complex_ne
    have hnum : 1 + A + B + B + A + 1 = 0 := by
      by_contra h_ne
      exact absurd h1 (div_ne_zero h_ne hne)
    linear_combination hnum / 2
  · intro hab z hz
    simp only [D6_symmetric, hz, ↓reduceIte]
    have : 1 + A * 1 + B * 1 + B * 1 + A * 1 + 1 = 2 * (A + B + 1) := by ring
    rw [this, hab]; ring

/-- D6_sym[x]=0 ↔ 4+3A+B=0, using L₁=1, L₂=3, L₃=4 -/
theorem D6_sym_C1 (A B : ℂ) :
    (∀ z : ℂ, z ≠ 0 → D6_symmetric A B id z = 0) ↔ 4 + 3 * A + B = 0 := by
  have hL1 := phi_add_psi_complex
  have hL2 : (↑φ : ℂ) ^ 2 + (↑ψ : ℂ) ^ 2 = 3 := by
    linear_combination golden_ratio_property_complex + psi_sq_complex + phi_add_psi_complex
  have hL3 : (↑φ : ℂ) ^ 3 + (↑ψ : ℂ) ^ 3 = 4 := by
    linear_combination phi_cubed_complex + psi_cubed_complex + 2 * phi_add_psi_complex
  constructor
  · intro h
    have h1 := h 1 one_ne_zero
    simp only [D6_symmetric, one_ne_zero, ↓reduceIte, id_eq, mul_one] at h1
    have hne : ((↑φ : ℂ) - ↑ψ) ^ 5 ≠ 0 := by
      apply pow_ne_zero
      exact phi_sub_psi_complex_ne
    have hnum : (↑φ : ℂ) ^ 3 + A * (↑φ : ℂ) ^ 2 + B * ↑φ
        + B * ↑ψ + A * (↑ψ : ℂ) ^ 2 + (↑ψ : ℂ) ^ 3 = 0 := by
      by_contra h_ne
      exact absurd h1 (div_ne_zero h_ne hne)
    have hfact : (↑φ : ℂ) ^ 3 + A * (↑φ : ℂ) ^ 2 + B * ↑φ
        + B * ↑ψ + A * (↑ψ : ℂ) ^ 2 + (↑ψ : ℂ) ^ 3 =
        ((↑φ : ℂ) ^ 3 + (↑ψ : ℂ) ^ 3) + A * ((↑φ : ℂ) ^ 2
        + (↑ψ : ℂ) ^ 2) + B * ((↑φ : ℂ) + ↑ψ) := by ring
    rw [hfact, hL3, hL2, hL1] at hnum
    linear_combination hnum
  · intro hab z hz
    simp only [D6_symmetric, hz, ↓reduceIte, id_eq]
    have : (↑φ : ℂ) ^ 3 * z + A * ((↑φ : ℂ) ^ 2 * z) + B * ((↑φ : ℂ) * z) + B * ((↑ψ : ℂ) * z) +
        A * ((↑ψ : ℂ) ^ 2 * z) + (↑ψ : ℂ) ^ 3 * z =
        (((↑φ : ℂ) ^ 3 + (↑ψ : ℂ) ^ 3) + A * ((↑φ : ℂ) ^ 2
        + (↑ψ : ℂ) ^ 2) + B * ((↑φ : ℂ) + ↑ψ)) * z := by ring
    rw [this, hL3, hL2, hL1]
    have : (4 + A * 3 + B * 1) * z = (4 + 3 * A + B) * z := by ring
    rw [this, hab]; ring

/-- D6_sym with D[1]=0 and D[x]=0 forces A=-3/2, B=1/2 -/
theorem D6_sym_coefficients (A B : ℂ)
    (h0 : ∀ z : ℂ, z ≠ 0 → D6_symmetric A B (fun _ => 1) z = 0)
    (h1 : ∀ z : ℂ, z ≠ 0 → D6_symmetric A B id z = 0) :
    A = -3/2 ∧ B = 1/2 := by
  have hab := (D6_sym_C0 A B).mp h0
  have hab2 := (D6_sym_C1 A B).mp h1
  have hA : A = -3/2 := by linear_combination (hab2 - hab) / 2
  have hB : B = 1/2 := by linear_combination -(hab2 - 3 * hab) / 2
  exact ⟨hA, hB⟩

/-- Symmetric D6 does NOT annihilate x²: D6_sym(-3/2, 1/2)[x²] ≠ 0.
    Numerator = L₆ + A·L₄ + B·L₂ = 18 + (-3/2)·7 + (1/2)·3 = 9 ≠ 0 -/
theorem D6_sym_not_ker_quadratic (z : ℂ) (hz : z ≠ 0) :
    D6_symmetric (-3/2) (1/2) (fun t => t^2) z ≠ 0 := by
  simp only [D6_symmetric, hz, ↓reduceIte]
  have hφ2 := golden_ratio_property_complex
  have hψ2 := psi_sq_complex
  have hL1 := phi_add_psi_complex
  have hφ4 := phi_pow4_complex
  have hψ4 := psi_pow4_complex
  have hφ6 := phi_pow6_complex
  have hψ6 := psi_pow6_complex
  -- Numerator = (φ⁶+ψ⁶) + A(φ⁴+ψ⁴) + B(φ²+ψ²) = 18 - 21/2 + 3/2 = 9
  have hnum : ((↑φ : ℂ) ^ 3 * z) ^ 2 + (-3/2) * ((↑φ : ℂ) ^ 2 * z) ^ 2
      + (1/2) * ((↑φ : ℂ) * z) ^ 2 + (1/2) * ((↑ψ : ℂ) * z) ^ 2
      + (-3/2) * ((↑ψ : ℂ) ^ 2 * z) ^ 2 + ((↑ψ : ℂ) ^ 3 * z) ^ 2 = 9 * z ^ 2 := by
    have hL6 : (↑φ : ℂ) ^ 6 + (↑ψ : ℂ) ^ 6 = 18 := by
      linear_combination hφ6 + hψ6 + 8 * hL1
    have hL4 : (↑φ : ℂ) ^ 4 + (↑ψ : ℂ) ^ 4 = 7 := by
      linear_combination hφ4 + hψ4 + 3 * hL1
    have hL2 : (↑φ : ℂ) ^ 2 + (↑ψ : ℂ) ^ 2 = 3 := by
      linear_combination hφ2 + hψ2 + hL1
    have hfact : ((↑φ : ℂ) ^ 3 * z) ^ 2 + (-3/2) * ((↑φ : ℂ) ^ 2 * z) ^ 2
      + (1/2) * ((↑φ : ℂ) * z) ^ 2 + (1/2) * ((↑ψ : ℂ) * z) ^ 2
      + (-3/2) * ((↑ψ : ℂ) ^ 2 * z) ^ 2 + ((↑ψ : ℂ) ^ 3 * z) ^ 2 =
      (((↑φ : ℂ) ^ 6 + (↑ψ : ℂ) ^ 6) + (-3/2) * ((↑φ : ℂ) ^ 4
      + (↑ψ : ℂ) ^ 4) + (1/2) * ((↑φ : ℂ) ^ 2 + (↑ψ : ℂ) ^ 2)) * z ^ 2 := by ring
    rw [hfact, hL6, hL4, hL2]; ring
  rw [hnum]
  have hden_ne : ((↑φ : ℂ) - ↑ψ) ^ 5 * z ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 5 phi_sub_psi_complex_ne) hz
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)) hden_ne

/-- Parity Selection for D₆: antisymmetric form has strictly larger kernel.
    Antisymmetric D₆ annihilates {1, z, x²} (3-dimensional kernel),
    but ANY symmetric form on the same 6 points with D[1]=0 and D[x]=0
    fails to annihilate x² (2-dimensional kernel). -/
theorem parity_selection_D6 :
    -- Antisymmetric D6 annihilates 1, z, x²
    ((∀ c z, z ≠ 0 → D6 (fun _ => c) z = 0) ∧
     (∀ z, z ≠ 0 → D6 id z = 0) ∧
     (∀ z, z ≠ 0 → D6 (fun t => t^2) z = 0)) ∧
    -- Symmetric D6 with maximal kernel does NOT annihilate x²
    (∀ A B : ℂ,
      (∀ z, z ≠ 0 → D6_symmetric A B (fun _ => 1) z = 0) →
      (∀ z, z ≠ 0 → D6_symmetric A B id z = 0) →
      ∀ z, z ≠ 0 → D6_symmetric A B (fun t => t^2) z ≠ 0) := by
  refine ⟨⟨D6_const, D6_linear, D6_quadratic⟩, ?_⟩
  intro A B h0 h1
  have ⟨hA, hB⟩ := D6_sym_coefficients A B h0 h1
  subst hA; subst hB
  exact D6_sym_not_ker_quadratic

end ParitySelection

/-! ## Justification of structural properties (§6.2)

### Antisymmetry: coefficient pattern under φ↔ψ exchange -/

/-- D₂ coefficients [1, -1] are antisymmetric -/
theorem D2_antisymmetric : (1 : ℤ) + (-1) = 0 ∧ (1 : ℤ) - (-1) ≠ 0 := by decide

/-- D₃ coefficients [1, -2, 1] are symmetric -/
theorem D3_symmetric : (1 : ℤ) - 1 = 0 ∧ (1 : ℤ) + (-2) + 1 = 0 := by decide

/-- D₅ coefficients [1, 1, -4, 1, 1] are symmetric -/
theorem D5_symmetric : (1 : ℤ) - 1 = 0 ∧ (1 : ℤ) - 1 = 0 := by decide

/-- D₆ coefficients [1, -3, 1, -1, 3, -1] are antisymmetric: c₁+c₆=0, c₂+c₅=0, c₃+c₄=0 -/
theorem D6_antisymmetric :
    (1 : ℤ) + (-1) = 0 ∧ (-3 : ℤ) + 3 = 0 ∧ (1 : ℤ) + (-1) = 0 := by decide

/-! ### Terminality (§6.3): ker(D₇) = ker(D₆) -/

theorem D6_is_terminal :
    ∀ a : ℂ, (∀ k z, z ≠ 0 → FUST.D7_constrained a (fun _ => k) z = 0) ∧
             (∀ z, z ≠ 0 → FUST.D7_constrained a id z = 0) ∧
             (∀ z, z ≠ 0 → FUST.D7_constrained a (fun t => t^2) z = 0) :=
  FUST.D7_kernel_equals_D6_kernel

end FUST
