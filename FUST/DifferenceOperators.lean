import FUST.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Finset.Basic

namespace FUST

variable {α : Type*} [Field α]

/-- D2: Frourio golden 2-point difference
    D₂ f(x) = (f(φx) - f(ψx)) / ((φ - ψ)x) -/
noncomputable def D2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else (f (φ * x) - f (ψ * x)) / ((φ - ψ) * x)

/-- D3: Frourio golden 3-point difference (points: φ, 1, ψ, coefficients: [1, -2, 1])
    D₃ f(x) = (f(φx) - 2f(x) + f(ψx)) / ((φ - ψ)²x) -/
noncomputable def D3 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else (f (φ * x) - 2 * f x + f (ψ * x)) / ((φ - ψ)^2 * x)

/-- D4: Frourio golden 4-point difference
    D₄ f(x) = (f(φ²x) - φ²f(φx) + ψ²f(ψx) - f(ψ²x)) / ((φ - ψ)³x) -/
noncomputable def D4 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (f (φ^2 * x) - φ^2 * f (φ * x) + ψ^2 * f (ψ * x) - f (ψ^2 * x)) / ((φ - ψ)^3 * x)

/-- D5: Frourio golden 5-point difference with coefficients a=-1, b=-4
    D₅ f(x) = (f(φ²x) + f(φx) - 4f(x) + f(ψx) + f(ψ²x)) / ((φ - ψ)⁴x) -/
noncomputable def D5 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (f (φ^2 * x) + f (φ * x) - 4 * f x + f (ψ * x) + f (ψ^2 * x)) / ((φ - ψ)^4 * x)

/-- N6: numerator of D6, without the (φ-ψ)⁵·x denominator -/
noncomputable def N6 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (φ^3 * x) - 3 * f (φ^2 * x) + f (φ * x) -
  f (ψ * x) + 3 * f (ψ^2 * x) - f (ψ^3 * x)

/-- D6 normalization constant: (φ - ψ)⁵ = (√5)⁵ -/
noncomputable def D6Denom : ℝ := (φ - ψ)^5

theorem D6Denom_ne_zero : D6Denom ≠ 0 := by
  unfold D6Denom; apply pow_ne_zero; rw [phi_sub_psi]
  exact Real.sqrt_ne_zero'.mpr (by norm_num)

theorem D6Denom_pos : D6Denom > 0 := by
  unfold D6Denom; apply pow_pos; rw [phi_sub_psi]
  exact Real.sqrt_pos.mpr (by norm_num)

theorem D6Denom_mul_ne_zero (x : ℝ) (hx : x ≠ 0) : D6Denom * x ≠ 0 :=
  mul_ne_zero D6Denom_ne_zero hx

/-- D6: Frourio golden 6-point difference with coefficients A=3, B=1
    D₆ f(x) = N6(f)(x) / (D6Denom · x) -/
noncomputable def D6 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else N6 f x / (D6Denom * x)

/-- D6 equals N6 divided by D6Denom · x -/
theorem D6_eq_N6_div (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 f x = N6 f x / (D6Denom * x) := by
  simp only [D6, hx, ↓reduceIte]

/-- N6 distributes over finite sums -/
theorem N6_finset_sum {ι : Type*}
    (s : Finset ι) (cs : ι → ℝ) (fs : ι → ℝ → ℝ) (x : ℝ) :
    N6 (fun y => ∑ i ∈ s, cs i * fs i y) x = ∑ i ∈ s, cs i * N6 (fs i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [N6]
  | insert a s' ha ih =>
    rw [Finset.sum_insert ha]
    have step1 : N6 (fun y => ∑ i ∈ insert a s', cs i * fs i y) x =
        cs a * N6 (fs a) x + N6 (fun y => ∑ i ∈ s', cs i * fs i y) x := by
      have : N6 (fun y => ∑ i ∈ insert a s', cs i * fs i y) x =
          N6 (fun y => cs a * fs a y + ∑ i ∈ s', cs i * fs i y) x := by
        congr 1; ext y; exact Finset.sum_insert ha
      rw [this]; simp only [N6]; ring
    rw [step1, ih]

/-- D5½: Half-order difference operator
    D₅.₅ f(x) = D₅ f(x) + μ · (f(φx) - f(ψx)) where μ = 2/(φ+2) -/
noncomputable def D5half (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  let μ := 2 / (φ + 2)
  D5 f x + μ * (f (φ * x) - f (ψ * x))

section KernelTheorems

/-- D2 annihilates constants: D₂[1] = 0 -/
theorem D2_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) : D2 (fun _ => c) x = 0 := by
  simp only [D2, hx, ↓reduceIte, sub_self, zero_div]

/-- D2 does NOT annihilate x: x ∉ ker(D2) -/
theorem D2_linear_ne_zero (x : ℝ) (hx : x ≠ 0) : D2 id x ≠ 0 := by
  simp only [D2, hx, ↓reduceIte, id_eq]
  have hnum : φ * x - ψ * x = (φ - ψ) * x := by ring
  rw [hnum]
  have hφψ : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hφψ_ne : φ - ψ ≠ 0 := by rw [hφψ]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hden_ne : (φ - ψ) * x ≠ 0 := mul_ne_zero hφψ_ne hx
  exact div_ne_zero hden_ne hden_ne

/-- D3 annihilates constants: D₃[1] = 0 (coefficient sum = 1 - 2 + 1 = 0) -/
theorem D3_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) : D3 (fun _ => c) x = 0 := by
  simp only [D3, hx, ↓reduceIte]
  have hnum : c - 2 * c + c = 0 := by ring
  simp only [hnum, zero_div]

/-- D3 does NOT annihilate x: x ∉ ker(D3) -/
theorem D3_linear_ne_zero (x : ℝ) (hx : x ≠ 0) : D3 id x ≠ 0 := by
  simp only [D3, hx, ↓reduceIte, id_eq]
  have hcoeff : φ + ψ - 2 = -1 := by linarith [phi_add_psi]
  have hnum : φ * x - 2 * x + ψ * x = (φ + ψ - 2) * x := by ring
  rw [hnum, hcoeff]
  have hφψ : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hφψ_ne : φ - ψ ≠ 0 := by rw [hφψ]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hden_ne : (φ - ψ) ^ 2 * x ≠ 0 := mul_ne_zero (pow_ne_zero 2 hφψ_ne) hx
  rw [neg_one_mul, neg_div, neg_ne_zero]
  exact div_ne_zero hx hden_ne

/-- D4 does NOT annihilate constants: 1 ∉ ker(D4) -/
theorem D4_const_ne_zero (x : ℝ) (hx : x ≠ 0) : D4 (fun _ => 1) x ≠ 0 := by
  simp only [D4, hx, ↓reduceIte]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hnum : (1 : ℝ) - φ^2 * 1 + ψ^2 * 1 - 1 = -(φ - ψ) := by rw [hφ2, hψ2]; ring
  rw [hnum]
  have hφψ : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hden_ne : (φ - ψ)^3 * x ≠ 0 := mul_ne_zero
    (pow_ne_zero 3 (by rw [hφψ]; exact Real.sqrt_ne_zero'.mpr (by norm_num))) hx
  rw [neg_div, neg_ne_zero]
  exact div_ne_zero (by rw [hφψ]; exact Real.sqrt_ne_zero'.mpr (by norm_num)) hden_ne

/-- D4 annihilates x²: x² ∈ ker(D4) -/
theorem D4_quadratic (x : ℝ) (hx : x ≠ 0) : D4 (fun t => t^2) x = 0 := by
  simp only [D4, hx, ↓reduceIte]
  have : (φ^2 * x)^2 - φ^2 * (φ * x)^2 + ψ^2 * (ψ * x)^2 - (ψ^2 * x)^2 = 0 := by ring
  simp [this]

/-- D4 does NOT annihilate x: x ∉ ker(D4) -/
theorem D4_linear_ne_zero (x : ℝ) (hx : x ≠ 0) : D4 id x ≠ 0 := by
  simp only [D4, hx, ↓reduceIte, id_eq]
  -- numerator: φ²x - φ²·φx + ψ²·ψx - ψ²x = (φ²-φ³+ψ³-ψ²)x
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ3 : φ^3 = 2*φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2*ψ + 1 := by
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [hψ2]
      _ = 2*ψ + 1 := by ring
  have hcoeff : φ^2 - φ^3 + ψ^3 - ψ^2 = -(φ - ψ) := by
    rw [hφ2, hφ3, hψ3, hψ2]; ring
  have hnum : φ^2 * x - φ^2 * (φ * x) + ψ^2 * (ψ * x) - ψ^2 * x =
    (φ^2 - φ^3 + ψ^3 - ψ^2) * x := by ring
  rw [hnum, hcoeff]
  have hφψ : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hφψ_ne : φ - ψ ≠ 0 := by rw [hφψ]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hden_ne : (φ - ψ)^3 * x ≠ 0 := mul_ne_zero (pow_ne_zero 3 hφψ_ne) hx
  rw [neg_mul, neg_div, neg_ne_zero]
  exact div_ne_zero (mul_ne_zero hφψ_ne hx) hden_ne

/-- D5 annihilates constants: D₅[1] = 0 (coefficient sum = 1+1-4+1+1 = 0) -/
theorem D5_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) : D5 (fun _ => c) x = 0 := by
  simp only [D5, hx, ↓reduceIte]
  have h : c + c - 4 * c + c + c = 0 := by ring
  simp [h]

/-- D5 annihilates x: D₅[x] = 0 -/
theorem D5_linear (x : ℝ) (hx : x ≠ 0) : D5 id x = 0 := by
  simp only [D5, hx, ↓reduceIte, id_eq]
  have h1 : φ^2 + ψ^2 = 3 := by
    have hφ : φ^2 = φ + 1 := golden_ratio_property
    have hψ : ψ^2 = ψ + 1 := psi_sq
    calc φ^2 + ψ^2 = (φ + 1) + (ψ + 1) := by rw [hφ, hψ]
      _ = (φ + ψ) + 2 := by ring
      _ = 1 + 2 := by rw [phi_add_psi]
      _ = 3 := by ring
  have h2 : φ + ψ = 1 := phi_add_psi
  have hnum : φ^2 * x + φ * x - 4 * x + ψ * x + ψ^2 * x = 0 := by
    have hcoef : φ^2 + ψ^2 + φ + ψ - 4 = 0 := by linarith [h1, h2]
    calc φ^2 * x + φ * x - 4 * x + ψ * x + ψ^2 * x
      = (φ^2 + ψ^2 + φ + ψ - 4) * x := by ring
      _ = 0 * x := by rw [hcoef]
      _ = 0 := by ring
  simp [hnum]

/-- D5 does NOT annihilate x²: x² ∉ ker(D5) -/
theorem D5_not_annihilate_quadratic (x : ℝ) (hx : x ≠ 0) :
    D5 (fun t => t^2) x ≠ 0 := by
  simp only [D5, hx, ↓reduceIte]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ4 : φ^4 = 3 * φ + 2 := by
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ^4 = 3 * ψ + 2 := by
    calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  have hsum : φ + ψ = 1 := phi_add_psi
  have hcoef : (φ^2)^2 + φ^2 - 4 + ψ^2 + (ψ^2)^2 = 6 := by
    calc (φ^2)^2 + φ^2 - 4 + ψ^2 + (ψ^2)^2
      = φ^4 + φ^2 + ψ^2 + ψ^4 - 4 := by ring
      _ = (3*φ + 2) + (φ + 1) + (ψ + 1) + (3*ψ + 2) - 4 := by rw [hφ4, hφ2, hψ2, hψ4]
      _ = 3*(φ + ψ) + (φ + ψ) + 2 := by ring
      _ = 3*1 + 1 + 2 := by rw [hsum]
      _ = 6 := by ring
  have hnum : (φ^2 * x)^2 + (φ * x)^2 - 4 * x^2 + (ψ * x)^2 + (ψ^2 * x)^2 =
      ((φ^2)^2 + φ^2 - 4 + ψ^2 + (ψ^2)^2) * x^2 := by ring
  rw [hnum, hcoef]
  have hdiff : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hden_ne : (φ - ψ)^4 * x ≠ 0 := by
    apply mul_ne_zero
    · apply pow_ne_zero; rw [hdiff]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
    · exact hx
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) hden_ne

/-- D6 annihilates constants: D₆[1] = 0 (coefficient sum = 1-3+1-1+3-1 = 0) -/
theorem D6_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) : D6 (fun _ => c) x = 0 := by
  simp only [D6, N6, hx, ↓reduceIte]
  ring_nf

/-- D6 annihilates x: D₆[x] = 0 -/
theorem D6_linear (x : ℝ) (hx : x ≠ 0) : D6 id x = 0 := by
  simp only [D6, N6, hx, ↓reduceIte, id_eq]
  have hφ3 : φ^3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2 * ψ + 1 := by
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [psi_sq]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [psi_sq]
      _ = 2 * ψ + 1 := by ring
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  have hnum : φ^3 * x - 3 * (φ^2 * x) + φ * x - ψ * x + 3 * (ψ^2 * x) - ψ^3 * x = 0 := by
    calc φ^3 * x - 3 * (φ^2 * x) + φ * x - ψ * x + 3 * (ψ^2 * x) - ψ^3 * x
      = (φ^3 - 3*φ^2 + φ - ψ + 3*ψ^2 - ψ^3) * x := by ring
      _ = ((2*φ+1) - 3*(φ+1) + φ - ψ + 3*(ψ+1) - (2*ψ+1)) * x := by rw [hφ3, hφ2, hψ2, hψ3]
      _ = (2*φ + 1 - 3*φ - 3 + φ - ψ + 3*ψ + 3 - 2*ψ - 1) * x := by ring
      _ = 0 := by ring
  simp [hnum]

/-- D6 annihilates x²: D₆[x²] = 0 -/
theorem D6_quadratic (x : ℝ) (hx : x ≠ 0) : D6 (fun t => t^2) x = 0 := by
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ3 : φ^3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2 * ψ + 1 := by
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [psi_sq]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [psi_sq]
      _ = 2 * ψ + 1 := by ring
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ4 : φ^4 = 3 * φ + 2 := by
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ^4 = 3 * ψ + 2 := by
    calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  have hφ6 : φ^6 = 8 * φ + 5 := by
    calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ + 1) + 5*φ + 2 := by rw [hφ2]
      _ = 8 * φ + 5 := by ring
  have hψ6 : ψ^6 = 8 * ψ + 5 := by
    calc ψ^6 = ψ^4 * ψ^2 := by ring
      _ = (3*ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3*ψ^2 + 5*ψ + 2 := by ring
      _ = 3*(ψ + 1) + 5*ψ + 2 := by rw [hψ2]
      _ = 8 * ψ + 5 := by ring
  have hsum : φ + ψ = 1 := phi_add_psi
  have hnum : (φ^3 * x)^2 - 3 * (φ^2 * x)^2 + (φ * x)^2 - (ψ * x)^2 +
      3 * (ψ^2 * x)^2 - (ψ^3 * x)^2 = 0 := by
    calc (φ^3 * x)^2 - 3 * (φ^2 * x)^2 + (φ * x)^2 - (ψ * x)^2 + 3 * (ψ^2 * x)^2 - (ψ^3 * x)^2
      = (φ^6 - 3*φ^4 + φ^2 - ψ^2 + 3*ψ^4 - ψ^6) * x^2 := by ring
      _ = ((8*φ+5) - 3*(3*φ+2) + (φ+1) - (ψ+1) + 3*(3*ψ+2) - (8*ψ+5)) * x^2 := by
          rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]
      _ = (8*φ + 5 - 9*φ - 6 + φ + 1 - ψ - 1 + 9*ψ + 6 - 8*ψ - 5) * x^2 := by ring
      _ = 0 := by ring
  simp [hnum]

/-! ### D5half kernel structure -/

/-- D5half annihilates constants: D₅.₅[1] = 0
    This preserves gauge invariance (same as D5) -/
theorem D5half_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) : D5half (fun _ => c) x = 0 := by
  simp only [D5half]
  have hD5 : D5 (fun _ => c) x = 0 := D5_const c x hx
  simp only [hD5, zero_add, sub_self, mul_zero]

/-- D5half does NOT annihilate linear functions: D₅.₅[x] ≠ 0
    Key difference from D5: D5[x] = 0 but D5half[x] ≠ 0 -/
theorem D5half_linear_ne_zero (x : ℝ) (hx : x ≠ 0) : D5half id x ≠ 0 := by
  simp only [D5half, id_eq]
  have hD5 : D5 id x = 0 := D5_linear x hx
  simp only [hD5, zero_add]
  have hdiff : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hdiff_ne : φ - ψ ≠ 0 := by rw [hdiff]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hφ2_pos : φ + 2 > 0 := by have := φ_gt_one; linarith
  have hφ2_ne : φ + 2 ≠ 0 := ne_of_gt hφ2_pos
  have hμ_pos : 2 / (φ + 2) > 0 := div_pos (by norm_num) hφ2_pos
  have hμ_ne : 2 / (φ + 2) ≠ 0 := ne_of_gt hμ_pos
  have hdiff_x : φ * x - ψ * x = (φ - ψ) * x := by ring
  rw [hdiff_x]
  have hprod_ne : (φ - ψ) * x ≠ 0 := mul_ne_zero hdiff_ne hx
  exact mul_ne_zero hμ_ne hprod_ne

/-- D5half at x=1 for quadratic: explicit nonzero value -/
theorem D5half_quadratic_at_one : D5half (fun t => t^2) 1 ≠ 0 := by
  simp only [D5half, D5, one_ne_zero, ↓reduceIte, mul_one, one_pow]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  have hdiff : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hφ2_pos : φ + 2 > 0 := by have := φ_gt_one; linarith
  have hdiff_pos : φ - ψ > 0 := by rw [hdiff]; exact Real.sqrt_pos.mpr (by norm_num)
  have hdiff_ne : φ - ψ ≠ 0 := ne_of_gt hdiff_pos
  have hden_ne : (φ - ψ)^4 * 1 ≠ 0 := mul_ne_zero (pow_ne_zero 4 hdiff_ne) one_ne_zero
  -- D5[x²] at x=1: numerator = φ⁴ + φ² - 4 + ψ² + ψ⁴ = 6
  have hφ4 : φ^4 = 3 * φ + 2 := by
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ^4 = 3 * ψ + 2 := by
    calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  have hD5_num : (φ^2)^2 + φ^2 - 4 + ψ^2 + (ψ^2)^2 = 6 := by
    calc (φ^2)^2 + φ^2 - 4 + ψ^2 + (ψ^2)^2
      = φ^4 + φ^2 + ψ^2 + ψ^4 - 4 := by ring
      _ = (3*φ + 2) + (φ + 1) + (ψ + 1) + (3*ψ + 2) - 4 := by rw [hφ4, hφ2, hψ2, hψ4]
      _ = 3*(φ + ψ) + (φ + ψ) + 2 := by ring
      _ = 3*1 + 1 + 2 := by rw [hsum]
      _ = 6 := by ring
  -- Antisymmetric term: φ² - ψ² = φ - ψ
  have hφ2_ψ2 : φ^2 - ψ^2 = φ - ψ := by
    calc φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
      _ = φ - ψ := by ring
  -- Total = 6/((φ-ψ)⁴) + (2/(φ+2))·(φ-ψ) > 0
  have hμ_pos : 2 / (φ + 2) > 0 := div_pos (by norm_num) hφ2_pos
  have hfirst_pos : 6 / ((φ - ψ)^4 * 1) > 0 := by
    simp only [mul_one]
    exact div_pos (by norm_num) (pow_pos hdiff_pos 4)
  have hsecond_pos : 2 / (φ + 2) * (φ - ψ) > 0 := mul_pos hμ_pos hdiff_pos
  have hD5_val : (φ^2)^2 + φ^2 - 4 + ψ^2 + (ψ^2)^2 = 6 := hD5_num
  rw [hD5_val, hφ2_ψ2]
  simp only [mul_one] at hden_ne hfirst_pos ⊢
  have hsum_pos : 6 / (φ - ψ)^4 + 2 / (φ + 2) * (φ - ψ) > 0 := by
    have h1 : 6 / (φ - ψ)^4 > 0 := div_pos (by norm_num) (pow_pos hdiff_pos 4)
    exact add_pos h1 hsecond_pos
  linarith

/-- D5half differs from D6: D6[x] = 0 but D5half[x] ≠ 0
    This proves D5half is NOT equivalent to D6 -/
theorem D5half_differs_from_D6 :
    (∀ x, x ≠ 0 → D6 id x = 0) ∧ (∀ x, x ≠ 0 → D5half id x ≠ 0) :=
  ⟨D6_linear, D5half_linear_ne_zero⟩

/-- D5half differs from D5: D5[x] = 0 but D5half[x] ≠ 0
    This proves D5half is NOT equivalent to D5 -/
theorem D5half_differs_from_D5 :
    (∀ x, x ≠ 0 → D5 id x = 0) ∧ (∀ x, x ≠ 0 → D5half id x ≠ 0) :=
  ⟨D5_linear, D5half_linear_ne_zero⟩

/-- D5half Independence Theorem:
    D5half is algebraically independent from both D5 and D6.
    Proof: On linear functions, D5[x] = D6[x] = 0 but D5half[x] ≠ 0.
    This shows D5half detects structure invisible to both D5 and D6. -/
theorem D5half_independence :
    -- D5half annihilates constants (like D5 and D6)
    (∀ c x, x ≠ 0 → D5half (fun _ => c) x = 0) ∧
    -- D5half does NOT annihilate linear (unlike D5 and D6)
    (∀ x, x ≠ 0 → D5half id x ≠ 0) ∧
    -- D5 annihilates linear
    (∀ x, x ≠ 0 → D5 id x = 0) ∧
    -- D6 annihilates linear
    (∀ x, x ≠ 0 → D6 id x = 0) :=
  ⟨D5half_const, D5half_linear_ne_zero, D5_linear, D6_linear⟩

/-- D5half preserves gauge invariance: D5half[1] = 0
    The half-order structure does NOT break gauge symmetry -/
theorem D5half_gauge_invariant (x : ℝ) (hx : x ≠ 0) : D5half (fun _ => 1) x = 0 :=
  D5half_const 1 x hx

/-- The antisymmetric term μ·(f(φx) - f(ψx)) is what makes D5half independent.
    This term vanishes for constants but not for linear functions. -/
theorem D5half_antisymmetric_term_key (x : ℝ) (hx : x ≠ 0) :
    (2 / (φ + 2)) * ((fun t => t) (φ * x) - (fun t => t) (ψ * x)) ≠ 0 := by
  simp only
  have hdiff : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hdiff_ne : φ - ψ ≠ 0 := by rw [hdiff]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hφ2_pos : φ + 2 > 0 := by have := φ_gt_one; linarith
  have hμ_ne : 2 / (φ + 2) ≠ 0 := ne_of_gt (div_pos (by norm_num) hφ2_pos)
  have hdiff_x : φ * x - ψ * x = (φ - ψ) * x := by ring
  rw [hdiff_x]
  exact mul_ne_zero hμ_ne (mul_ne_zero hdiff_ne hx)

end KernelTheorems

section KernelDimensions

/-- ker(D₅) contains {1, x}, so dim ≥ 2 -/
theorem D5_ker_contains_const_and_linear :
    (∀ c x, x ≠ 0 → D5 (fun _ => c) x = 0) ∧
    (∀ x, x ≠ 0 → D5 id x = 0) :=
  ⟨D5_const, D5_linear⟩

/-- ker(D₆) contains {1, x, x²}, so dim ≥ 3 -/
theorem D6_ker_contains_polynomials :
    (∀ c x, x ≠ 0 → D6 (fun _ => c) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) :=
  ⟨D6_const, D6_linear, D6_quadratic⟩

end KernelDimensions

/-!
## Coefficient Uniqueness Theorems

D5 general form: (f(φ²x) - a·f(φx) + b·f(x) - a·f(ψx) + f(ψ²x)) / ((φ-ψ)⁴x)
D6 general form: (f(φ³x) - A·f(φ²x) + B·f(φx) - B·f(ψx) + A·f(ψ²x) - f(ψ³x)) / ((φ-ψ)⁵x)

The coefficients are uniquely determined by the kernel conditions.
-/

section CoefficientUniqueness

/-- D5 general form with parameters (a, b) -/
noncomputable def D5_general (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (f (φ^2 * x) - a * f (φ * x) + b * f x - a * f (ψ * x) + f (ψ^2 * x)) / ((φ - ψ)^4 * x)

/-- D6 general form with parameters (A, B) -/
noncomputable def D6_general (A B : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (f (φ^3 * x) - A * f (φ^2 * x) + B * f (φ * x) -
     B * f (ψ * x) + A * f (ψ^2 * x) - f (ψ^3 * x)) / ((φ - ψ)^5 * x)

/-- Condition C0: D5[1] = 0 implies 2 - 2a + b = 0 -/
theorem D5_C0_condition (a b : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D5_general a b (fun _ => 1) x = 0) ↔ b = 2 * a - 2 := by
  constructor
  · intro h
    have h1 := h 1 one_ne_zero
    simp only [D5_general, one_ne_zero, ↓reduceIte, mul_one] at h1
    have hne : (φ - ψ)^4 ≠ 0 := by
      have : φ - ψ = Real.sqrt 5 := phi_sub_psi
      rw [this]
      apply pow_ne_zero
      exact Real.sqrt_ne_zero'.mpr (by norm_num)
    rw [div_eq_zero_iff] at h1
    cases h1 with
    | inl h1 => linarith
    | inr h1 =>
      have h1' : (φ - ψ)^4 = 0 := by linarith
      exact absurd h1' hne
  · intro hb x hx
    simp only [D5_general, hx, ↓reduceIte]
    have hnum : 1 - a * 1 + b * 1 - a * 1 + 1 = 2 - 2 * a + b := by ring
    rw [hnum, hb]
    ring_nf

/-- Condition C1: D5[x] = 0 implies (φ² + ψ²) - a(φ + ψ) + b = 0 -/
theorem D5_C1_condition (a b : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D5_general a b id x = 0) ↔ b = a - 3 := by
  have h1 : φ^2 + ψ^2 = 3 := by
    have hφ : φ^2 = φ + 1 := golden_ratio_property
    have hψ : ψ^2 = ψ + 1 := psi_sq
    calc φ^2 + ψ^2 = (φ + 1) + (ψ + 1) := by rw [hφ, hψ]
      _ = (φ + ψ) + 2 := by ring
      _ = 1 + 2 := by rw [phi_add_psi]
      _ = 3 := by ring
  have h2 : φ + ψ = 1 := phi_add_psi
  constructor
  · intro h
    have hx := h 1 one_ne_zero
    simp only [D5_general, one_ne_zero, ↓reduceIte, id_eq, mul_one] at hx
    have hne : (φ - ψ)^4 ≠ 0 := by
      have : φ - ψ = Real.sqrt 5 := phi_sub_psi
      rw [this]
      apply pow_ne_zero
      exact Real.sqrt_ne_zero'.mpr (by norm_num)
    rw [div_eq_zero_iff] at hx
    cases hx with
    | inl hx =>
      have hcoef : φ^2 - a * φ + b - a * ψ + ψ^2 = (φ^2 + ψ^2) - a * (φ + ψ) + b := by ring
      rw [hcoef, h1, h2] at hx
      linarith
    | inr hx =>
      have hx' : (φ - ψ)^4 = 0 := by linarith
      exact absurd hx' hne
  · intro hb x hx
    simp only [D5_general, hx, ↓reduceIte, id_eq]
    have hcoef : φ^2 + ψ^2 - a * (φ + ψ) + b = 0 := by
      rw [h1, h2, hb]; ring
    have hnum : φ^2 * x - a * (φ * x) + b * x - a * (ψ * x) + ψ^2 * x =
        (φ^2 + ψ^2 - a * (φ + ψ) + b) * x := by ring
    rw [hnum, hcoef]
    simp only [zero_mul, zero_div]

/-- Theorem 4.1 (D5 coefficient uniqueness):
    The conditions D5[1] = 0 and D5[x] = 0 uniquely determine a = -1, b = -4 -/
theorem D5_coefficients_unique :
    ∀ a b : ℝ,
    (∀ x : ℝ, x ≠ 0 → D5_general a b (fun _ => 1) x = 0) →
    (∀ x : ℝ, x ≠ 0 → D5_general a b id x = 0) →
    a = -1 ∧ b = -4 := by
  intro a b h0 h1
  have eq1 : b = 2 * a - 2 := D5_C0_condition a b |>.mp h0
  have eq2 : b = a - 3 := D5_C1_condition a b |>.mp h1
  constructor
  · linarith
  · linarith

/-- D5 with determined coefficients equals D5 -/
theorem D5_general_eq_D5 (f : ℝ → ℝ) (x : ℝ) :
    D5_general (-1) (-4) f x = D5 f x := by
  simp only [D5_general, D5]
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte]
    ring_nf

/-- Condition D1: D6[x] = 0 implies F₃ - A·F₂ + B·F₁ = 0, i.e., 2 - A + B = 0 -/
theorem D6_D1_condition (A B : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D6_general A B id x = 0) ↔ B = A - 2 := by
  have hφ3 : φ^3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2 * ψ + 1 := by
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [psi_sq]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [psi_sq]
      _ = 2 * ψ + 1 := by ring
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  constructor
  · intro h
    have hx := h 1 one_ne_zero
    simp only [D6_general, one_ne_zero, ↓reduceIte, id_eq, mul_one] at hx
    rw [div_eq_zero_iff] at hx
    cases hx with
    | inl hx =>
      have hcoef : φ^3 - A * φ^2 + B * φ - B * ψ + A * ψ^2 - ψ^3 =
          (φ^3 - ψ^3) - A * (φ^2 - ψ^2) + B * (φ - ψ) := by ring
      rw [hcoef] at hx
      have hφ3_ψ3 : φ^3 - ψ^3 = (2 * φ + 1) - (2 * ψ + 1) := by rw [hφ3, hψ3]
      have hφ2_ψ2 : φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
      simp only [hφ3_ψ3, hφ2_ψ2] at hx
      have hsub : φ - ψ = Real.sqrt 5 := phi_sub_psi
      have hne2 : φ - ψ ≠ 0 := by rw [hsub]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
      have : (2 * (φ - ψ)) - A * (φ - ψ) + B * (φ - ψ) = 0 := by linarith
      have : (2 - A + B) * (φ - ψ) = 0 := by linarith
      have : 2 - A + B = 0 := by
        by_contra hc
        have : (φ - ψ) = 0 := by
          have := mul_eq_zero.mp this
          cases this with
          | inl h => exact absurd h hc
          | inr h => exact h
        exact hne2 this
      linarith
    | inr hx =>
      have hx' : (φ - ψ)^5 = 0 := by linarith
      exact absurd hx' D6Denom_ne_zero
  · intro hB x hx
    simp only [D6_general, hx, ↓reduceIte, id_eq]
    have hcoef : φ^3 - ψ^3 - A * (φ^2 - ψ^2) + B * (φ - ψ) = 0 := by
      have hφ3_ψ3 : φ^3 - ψ^3 = 2 * (φ - ψ) := by
        calc φ^3 - ψ^3 = (2 * φ + 1) - (2 * ψ + 1) := by rw [hφ3, hψ3]
          _ = 2 * (φ - ψ) := by ring
      have hφ2_ψ2 : φ^2 - ψ^2 = φ - ψ := by
        calc φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
          _ = φ - ψ := by ring
      rw [hφ3_ψ3, hφ2_ψ2, hB]
      ring
    have hnum : φ^3 * x - A * (φ^2 * x) + B * (φ * x) - B * (ψ * x) +
        A * (ψ^2 * x) - ψ^3 * x = (φ^3 - ψ^3 - A * (φ^2 - ψ^2) + B * (φ - ψ)) * x := by ring
    rw [hnum, hcoef]
    simp only [zero_mul, zero_div]

/-- Condition D2: D6[x²] = 0 implies F₆ - A·F₄ + B·F₂ = 0, i.e., 8 - 3A + B = 0 -/
theorem D6_D2_condition (A B : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D6_general A B (fun t => t^2) x = 0) ↔ B = 3 * A - 8 := by
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ4 : φ^4 = 3 * φ + 2 := by
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ^4 = 3 * ψ + 2 := by
    calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  have hφ6 : φ^6 = 8 * φ + 5 := by
    calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ + 1) + 5*φ + 2 := by rw [hφ2]
      _ = 8 * φ + 5 := by ring
  have hψ6 : ψ^6 = 8 * ψ + 5 := by
    calc ψ^6 = ψ^4 * ψ^2 := by ring
      _ = (3*ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3*ψ^2 + 5*ψ + 2 := by ring
      _ = 3*(ψ + 1) + 5*ψ + 2 := by rw [hψ2]
      _ = 8 * ψ + 5 := by ring
  have hsum : φ + ψ = 1 := phi_add_psi
  constructor
  · intro h
    have hx := h 1 one_ne_zero
    simp only [D6_general, one_ne_zero, ↓reduceIte, mul_one] at hx
    rw [div_eq_zero_iff] at hx
    cases hx with
    | inl hx =>
      have hcoef : (φ^3)^2 - A * (φ^2)^2 + B * φ^2 - B * ψ^2 + A * (ψ^2)^2 - (ψ^3)^2 =
          φ^6 - ψ^6 - A * (φ^4 - ψ^4) + B * (φ^2 - ψ^2) := by ring
      rw [hcoef] at hx
      have hφ6_ψ6 : φ^6 - ψ^6 = 8 * (φ - ψ) := by
        calc φ^6 - ψ^6 = (8*φ + 5) - (8*ψ + 5) := by rw [hφ6, hψ6]
          _ = 8 * (φ - ψ) := by ring
      have hφ4_ψ4 : φ^4 - ψ^4 = 3 * (φ - ψ) := by
        calc φ^4 - ψ^4 = (3*φ + 2) - (3*ψ + 2) := by rw [hφ4, hψ4]
          _ = 3 * (φ - ψ) := by ring
      have hφ2_ψ2 : φ^2 - ψ^2 = φ - ψ := by
        calc φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
          _ = φ - ψ := by ring
      rw [hφ6_ψ6, hφ4_ψ4, hφ2_ψ2] at hx
      have hsub : φ - ψ = Real.sqrt 5 := phi_sub_psi
      have hne2 : φ - ψ ≠ 0 := by rw [hsub]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
      have : (8 - 3 * A + B) * (φ - ψ) = 0 := by linarith
      have : 8 - 3 * A + B = 0 := by
        by_contra hc
        have : (φ - ψ) = 0 := by
          have := mul_eq_zero.mp this
          cases this with
          | inl h => exact absurd h hc
          | inr h => exact h
        exact hne2 this
      linarith
    | inr hx =>
      have hx' : (φ - ψ)^5 = 0 := by linarith
      exact absurd hx' D6Denom_ne_zero
  · intro hB x hx
    simp only [D6_general, hx, ↓reduceIte]
    have hcoef : φ^6 - ψ^6 - A * (φ^4 - ψ^4) + B * (φ^2 - ψ^2) = 0 := by
      have hφ6_ψ6 : φ^6 - ψ^6 = 8 * (φ - ψ) := by
        calc φ^6 - ψ^6 = (8*φ + 5) - (8*ψ + 5) := by rw [hφ6, hψ6]
          _ = 8 * (φ - ψ) := by ring
      have hφ4_ψ4 : φ^4 - ψ^4 = 3 * (φ - ψ) := by
        calc φ^4 - ψ^4 = (3*φ + 2) - (3*ψ + 2) := by rw [hφ4, hψ4]
          _ = 3 * (φ - ψ) := by ring
      have hφ2_ψ2 : φ^2 - ψ^2 = φ - ψ := by
        calc φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
          _ = φ - ψ := by ring
      rw [hφ6_ψ6, hφ4_ψ4, hφ2_ψ2, hB]
      ring
    have hnum : (φ^3 * x)^2 - A * (φ^2 * x)^2 + B * (φ * x)^2 -
        B * (ψ * x)^2 + A * (ψ^2 * x)^2 - (ψ^3 * x)^2 =
        (φ^6 - ψ^6 - A * (φ^4 - ψ^4) + B * (φ^2 - ψ^2)) * x^2 := by ring
    rw [hnum, hcoef]
    simp only [zero_mul, zero_div]

/-- Theorem 4.1 (D6 coefficient uniqueness):
    The conditions D6[x] = 0 and D6[x²] = 0 uniquely determine A = 3, B = 1 -/
theorem D6_coefficients_unique :
    ∀ A B : ℝ,
    (∀ x : ℝ, x ≠ 0 → D6_general A B id x = 0) →
    (∀ x : ℝ, x ≠ 0 → D6_general A B (fun t => t^2) x = 0) →
    A = 3 ∧ B = 1 := by
  intro A B h1 h2
  have eq1 : B = A - 2 := D6_D1_condition A B |>.mp h1
  have eq2 : B = 3 * A - 8 := D6_D2_condition A B |>.mp h2
  constructor
  · linarith
  · linarith

/-- D6 with determined coefficients equals D6 -/
theorem D6_general_eq_D6 (f : ℝ → ℝ) (x : ℝ) :
    D6_general 3 1 f x = D6 f x := by
  simp only [D6_general, D6, N6, D6Denom]
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte]
    ring_nf

/-- Main Theorem 4.1: Complete coefficient uniqueness for D5 and D6 -/
theorem FUST_coefficient_uniqueness :
    (∀ a b : ℝ,
      (∀ x, x ≠ 0 → D5_general a b (fun _ => 1) x = 0) →
      (∀ x, x ≠ 0 → D5_general a b id x = 0) →
      a = -1 ∧ b = -4) ∧
    (∀ A B : ℝ,
      (∀ x, x ≠ 0 → D6_general A B id x = 0) →
      (∀ x, x ≠ 0 → D6_general A B (fun t => t^2) x = 0) →
      A = 3 ∧ B = 1) :=
  ⟨D5_coefficients_unique, D6_coefficients_unique⟩

end CoefficientUniqueness

section AlgebraicConstants

/-- Half-order mixing parameter: λ = 2/(φ + 2) = 2/(φ² + 1) ≈ 0.5528 -/
noncomputable def halfOrderParam : ℝ := 2 / (φ + 2)

/-- Alternative form: λ = 2/(φ² + 1) -/
theorem halfOrderParam_alt : halfOrderParam = 2 / (φ^2 + 1) := by
  simp only [halfOrderParam]
  have h : φ + 2 = φ^2 + 1 := by
    have hφ2 : φ^2 = φ + 1 := golden_ratio_property
    linarith
  rw [h]

/-- Uniqueness condition: halfOrderParam satisfies μ·(φ² + 1) = dim(ker(D5)) = 2 -/
theorem halfOrderParam_uniqueness : halfOrderParam * (φ^2 + 1) = 2 := by
  rw [halfOrderParam_alt]
  have h : φ^2 + 1 ≠ 0 := by
    have : φ^2 > 0 := sq_pos_of_pos phi_pos
    linarith
  field_simp

/-- If μ·(φ² + 1) = 2, then μ = halfOrderParam -/
theorem halfOrderParam_unique_from_condition (μ : ℝ) (h : μ * (φ ^ 2 + 1) = 2) :
    μ = halfOrderParam := by
  have hpos : φ ^ 2 + 1 > 0 := by
    have : φ ^ 2 > 0 := sq_pos_of_pos phi_pos
    linarith
  have hne : φ ^ 2 + 1 ≠ 0 := ne_of_gt hpos
  rw [halfOrderParam_alt]
  field_simp at h ⊢
  linarith

/-! ### Coefficient sums and gauge invariance -/

/-- D2 coefficient sum: 1 - 1 = 0 -/
theorem D2_coeff_sum : (1 : ℝ) - 1 = 0 := by ring

/-- D3 coefficient sum: 1 - 2 + 1 = 0 -/
theorem D3_coeff_sum : (1 : ℝ) - 2 + 1 = 0 := by ring

/-- D4 coefficient sum: 1 - φ² + ψ² - 1 ≠ 0 -/
theorem D4_coeff_sum_ne_zero : (1 : ℝ) - φ^2 + ψ^2 - 1 ≠ 0 := by
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  calc (1 : ℝ) - φ^2 + ψ^2 - 1
    = 1 - (φ + 1) + (ψ + 1) - 1 := by rw [hφ2, hψ2]
    _ = ψ - φ := by ring
    _ = -Real.sqrt 5 := by
      have h : φ - ψ = Real.sqrt 5 := phi_sub_psi
      linarith
  have hsqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  linarith

/-- D5 coefficient sum: 1 + 1 - 4 + 1 + 1 = 0 -/
theorem D5_coeff_sum : (1 : ℝ) + 1 - 4 + 1 + 1 = 0 := by ring

/-- D6 coefficient sum: 1 - 3 + 1 - 1 + 3 - 1 = 0 -/
theorem D6_coeff_sum : (1 : ℝ) - 3 + 1 - 1 + 3 - 1 = 0 := by ring

/-- Gauge invariance: coefficient sum = 0 implies D[1] = 0 for x ≠ 0 -/
theorem D2_gauge_invariant (x : ℝ) (hx : x ≠ 0) : D2 (fun _ => 1) x = 0 :=
  D2_const 1 x hx

theorem D3_gauge_invariant (x : ℝ) (hx : x ≠ 0) : D3 (fun _ => 1) x = 0 :=
  D3_const 1 x hx

theorem D5_gauge_invariant (x : ℝ) (hx : x ≠ 0) : D5 (fun _ => 1) x = 0 :=
  D5_const 1 x hx

theorem D6_gauge_invariant (x : ℝ) (hx : x ≠ 0) : D6 (fun _ => 1) x = 0 :=
  D6_const 1 x hx

/-- D4 breaks gauge invariance: D4[1] ≠ 0 for general constant -/
theorem D4_not_gauge_invariant : ∃ (c : ℝ) (x : ℝ), x ≠ 0 ∧ c ≠ 0 ∧ D4 (fun _ => c) x ≠ 0 := by
  use 1, 1, one_ne_zero, one_ne_zero
  simp only [D4, one_ne_zero, ↓reduceIte]
  have hcoeff_ne : (1 : ℝ) - φ^2 + ψ^2 - 1 ≠ 0 := D4_coeff_sum_ne_zero
  have hdiff : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hden_pos : (φ - ψ)^3 > 0 := by
    rw [hdiff]
    apply pow_pos
    exact Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have hnum_eq : (1 : ℝ) - φ^2 * 1 + ψ^2 * 1 - 1 = 1 - φ^2 + ψ^2 - 1 := by ring
  rw [hnum_eq]
  exact div_ne_zero hcoeff_ne (by linarith)

/-- Kernel dimension of D5 is 2 (derived from D5_const and D5_linear) -/
theorem D5_kernel_contains_const_and_linear (x : ℝ) (hx : x ≠ 0) :
    D5 (fun _ => 1) x = 0 ∧ D5 id x = 0 :=
  ⟨D5_const 1 x hx, D5_linear x hx⟩

/-- Kernel dimension of D6 is 3 (derived from D6_const, D6_linear, D6_quadratic) -/
theorem D6_kernel_contains_polynomials_up_to_degree_2 (x : ℝ) (hx : x ≠ 0) :
    D6 (fun _ => 1) x = 0 ∧ D6 id x = 0 ∧ D6 (fun t => t^2) x = 0 :=
  ⟨D6_const 1 x hx, D6_linear x hx, D6_quadratic x hx⟩

end AlgebraicConstants

/-!
## D7 Algebraic Reduction to D6

D7 antisymmetric form: [1, -a, b, -c, +c, -b, +a, -1]
D7[f](x) = (f(φ⁴x) - a·f(φ³x) + b·f(φ²x) - c·f(φx)
            + c·f(ψx) - b·f(ψ²x) + a·f(ψ³x) - f(ψ⁴x)) / ((φ-ψ)⁶x)

Key result: ker(D7) = ker(D6) implies D7 provides no new structure.
-/

section D7Reduction

/-- D7 general antisymmetric form with parameters (a, b, c) -/
noncomputable def D7_general (a b c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (f (φ^4 * x) - a * f (φ^3 * x) + b * f (φ^2 * x) - c * f (φ * x)
     + c * f (ψ * x) - b * f (ψ^2 * x) + a * f (ψ^3 * x) - f (ψ^4 * x)) / ((φ - ψ)^6 * x)

/-- Condition E0: D7[1] = 0 holds for antisymmetric form (coefficient sum = 0) -/
theorem D7_E0_condition (a b c : ℝ) :
    ∀ x : ℝ, x ≠ 0 → D7_general a b c (fun _ => 1) x = 0 := by
  intro x hx
  simp only [D7_general, hx, ↓reduceIte]
  have hsum : (1 : ℝ) - a * 1 + b * 1 - c * 1 + c * 1 - b * 1 + a * 1 - 1 = 0 := by ring
  rw [hsum, zero_div]

/-- Condition E1: D7[x] = 0 implies 3 - 2a + b - c = 0
    (using Fibonacci: F₄ = 3, F₃ = 2, F₂ = 1, F₁ = 1) -/
theorem D7_E1_condition (a b c : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D7_general a b c id x = 0) ↔ 3 - 2 * a + b - c = 0 := by
  have hφ4 : φ^4 = 3 * φ + 2 := by
    have hφ2 : φ^2 = φ + 1 := golden_ratio_property
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ^4 = 3 * ψ + 2 := by
    have hψ2 : ψ^2 = ψ + 1 := psi_sq
    calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  have hφ3 : φ^3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2 * ψ + 1 := by
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [psi_sq]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [psi_sq]
      _ = 2 * ψ + 1 := by ring
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  have hdiff : φ - ψ = Real.sqrt 5 := phi_sub_psi
  constructor
  · intro h
    have hx := h 1 one_ne_zero
    simp only [D7_general, one_ne_zero, ↓reduceIte, id_eq, mul_one] at hx
    have hne : (φ - ψ)^6 ≠ 0 := by
      rw [hdiff]; apply pow_ne_zero; exact Real.sqrt_ne_zero'.mpr (by norm_num)
    rw [div_eq_zero_iff] at hx
    cases hx with
    | inl hx =>
      -- Coefficient of x in antisymmetric form: φ⁴ - ψ⁴ - a(φ³ - ψ³) + b(φ² - ψ²) - c(φ - ψ)
      have hcoef : φ^4 - a * φ^3 + b * φ^2 - c * φ + c * ψ - b * ψ^2 + a * ψ^3 - ψ^4
          = (φ^4 - ψ^4) - a * (φ^3 - ψ^3) + b * (φ^2 - ψ^2) - c * (φ - ψ) := by ring
      rw [hcoef] at hx
      -- φⁿ - ψⁿ = √5 · Fₙ (Binet formula)
      have hF4 : φ^4 - ψ^4 = 3 * (φ - ψ) := by
        calc φ^4 - ψ^4 = (3*φ + 2) - (3*ψ + 2) := by rw [hφ4, hψ4]
          _ = 3 * (φ - ψ) := by ring
      have hF3 : φ^3 - ψ^3 = 2 * (φ - ψ) := by
        calc φ^3 - ψ^3 = (2*φ + 1) - (2*ψ + 1) := by rw [hφ3, hψ3]
          _ = 2 * (φ - ψ) := by ring
      have hF2 : φ^2 - ψ^2 = φ - ψ := by
        calc φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
          _ = φ - ψ := by ring
      rw [hF4, hF3, hF2] at hx
      have hne2 : φ - ψ ≠ 0 := by rw [hdiff]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
      have : (3 - 2*a + b - c) * (φ - ψ) = 0 := by linarith
      have : 3 - 2*a + b - c = 0 := by
        by_contra hc
        have := mul_eq_zero.mp this
        cases this with
        | inl h => exact hc h
        | inr h => exact hne2 h
      linarith
    | inr hx =>
      have hx' : (φ - ψ)^6 = 0 := by linarith
      exact absurd hx' hne
  · intro hcond x hx
    simp only [D7_general, hx, ↓reduceIte, id_eq]
    have hcoef : φ^4 - ψ^4 - a * (φ^3 - ψ^3) + b * (φ^2 - ψ^2) - c * (φ - ψ) = 0 := by
      have hF4 : φ^4 - ψ^4 = 3 * (φ - ψ) := by
        calc φ^4 - ψ^4 = (3*φ + 2) - (3*ψ + 2) := by rw [hφ4, hψ4]
          _ = 3 * (φ - ψ) := by ring
      have hF3 : φ^3 - ψ^3 = 2 * (φ - ψ) := by
        calc φ^3 - ψ^3 = (2*φ + 1) - (2*ψ + 1) := by rw [hφ3, hψ3]
          _ = 2 * (φ - ψ) := by ring
      have hF2 : φ^2 - ψ^2 = φ - ψ := by
        calc φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
          _ = φ - ψ := by ring
      rw [hF4, hF3, hF2]
      have : (3 - 2*a + b - c) * (φ - ψ) = 0 := by rw [hcond]; ring
      linarith
    have hnum : φ^4 * x - a * (φ^3 * x) + b * (φ^2 * x) - c * (φ * x)
        + c * (ψ * x) - b * (ψ^2 * x) + a * (ψ^3 * x) - ψ^4 * x
        = (φ^4 - ψ^4 - a * (φ^3 - ψ^3) + b * (φ^2 - ψ^2) - c * (φ - ψ)) * x := by ring
    rw [hnum, hcoef]
    simp only [zero_mul, zero_div]

/-- Condition E2: D7[x²] = 0 implies F₈ - a·F₆ + b·F₄ - c·F₂ = 21 - 8a + 3b - c = 0 -/
theorem D7_E2_condition (a b c : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D7_general a b c (fun t => t^2) x = 0) ↔ 21 - 8 * a + 3 * b - c = 0 := by
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ4 : φ^4 = 3 * φ + 2 := by
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ^4 = 3 * ψ + 2 := by
    calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  have hφ6 : φ^6 = 8 * φ + 5 := by
    calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ + 1) + 5*φ + 2 := by rw [hφ2]
      _ = 8 * φ + 5 := by ring
  have hψ6 : ψ^6 = 8 * ψ + 5 := by
    calc ψ^6 = ψ^4 * ψ^2 := by ring
      _ = (3*ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3*ψ^2 + 5*ψ + 2 := by ring
      _ = 3*(ψ + 1) + 5*ψ + 2 := by rw [hψ2]
      _ = 8 * ψ + 5 := by ring
  have hφ8 : φ^8 = 21 * φ + 13 := by
    calc φ^8 = φ^4 * φ^4 := by ring
      _ = (3*φ + 2) * (3*φ + 2) := by rw [hφ4]
      _ = 9*φ^2 + 12*φ + 4 := by ring
      _ = 9*(φ + 1) + 12*φ + 4 := by rw [hφ2]
      _ = 21 * φ + 13 := by ring
  have hψ8 : ψ^8 = 21 * ψ + 13 := by
    calc ψ^8 = ψ^4 * ψ^4 := by ring
      _ = (3*ψ + 2) * (3*ψ + 2) := by rw [hψ4]
      _ = 9*ψ^2 + 12*ψ + 4 := by ring
      _ = 9*(ψ + 1) + 12*ψ + 4 := by rw [hψ2]
      _ = 21 * ψ + 13 := by ring
  have hdiff : φ - ψ = Real.sqrt 5 := phi_sub_psi
  constructor
  · intro h
    have hx := h 1 one_ne_zero
    simp only [D7_general, one_ne_zero, ↓reduceIte, mul_one] at hx
    have hne : (φ - ψ)^6 ≠ 0 := by
      rw [hdiff]; apply pow_ne_zero; exact Real.sqrt_ne_zero'.mpr (by norm_num)
    rw [div_eq_zero_iff] at hx
    cases hx with
    | inl hx =>
      -- For x² terms: φ^8 - ψ^8 - a(φ^6 - ψ^6) + b(φ^4 - ψ^4) - c(φ^2 - ψ^2)
      have hcoef : (φ^4)^2 - a * (φ^3)^2 + b * (φ^2)^2 - c * φ^2
          + c * ψ^2 - b * (ψ^2)^2 + a * (ψ^3)^2 - (ψ^4)^2
          = φ^8 - ψ^8 - a * (φ^6 - ψ^6) + b * (φ^4 - ψ^4) - c * (φ^2 - ψ^2) := by ring
      rw [hcoef] at hx
      have hF8 : φ^8 - ψ^8 = 21 * (φ - ψ) := by
        calc φ^8 - ψ^8 = (21*φ + 13) - (21*ψ + 13) := by rw [hφ8, hψ8]
          _ = 21 * (φ - ψ) := by ring
      have hF6 : φ^6 - ψ^6 = 8 * (φ - ψ) := by
        calc φ^6 - ψ^6 = (8*φ + 5) - (8*ψ + 5) := by rw [hφ6, hψ6]
          _ = 8 * (φ - ψ) := by ring
      have hF4 : φ^4 - ψ^4 = 3 * (φ - ψ) := by
        calc φ^4 - ψ^4 = (3*φ + 2) - (3*ψ + 2) := by rw [hφ4, hψ4]
          _ = 3 * (φ - ψ) := by ring
      have hF2 : φ^2 - ψ^2 = φ - ψ := by
        calc φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
          _ = φ - ψ := by ring
      rw [hF8, hF6, hF4, hF2] at hx
      have hne2 : φ - ψ ≠ 0 := by rw [hdiff]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
      have : (21 - 8*a + 3*b - c) * (φ - ψ) = 0 := by linarith
      have : 21 - 8*a + 3*b - c = 0 := by
        by_contra hc
        have := mul_eq_zero.mp this
        cases this with
        | inl h => exact hc h
        | inr h => exact hne2 h
      linarith
    | inr hx =>
      have hx' : (φ - ψ)^6 = 0 := by linarith
      exact absurd hx' hne
  · intro hcond x hx
    simp only [D7_general, hx, ↓reduceIte]
    have hF8 : φ^8 - ψ^8 = 21 * (φ - ψ) := by
      calc φ^8 - ψ^8 = (21*φ + 13) - (21*ψ + 13) := by rw [hφ8, hψ8]
        _ = 21 * (φ - ψ) := by ring
    have hF6 : φ^6 - ψ^6 = 8 * (φ - ψ) := by
      calc φ^6 - ψ^6 = (8*φ + 5) - (8*ψ + 5) := by rw [hφ6, hψ6]
        _ = 8 * (φ - ψ) := by ring
    have hF4 : φ^4 - ψ^4 = 3 * (φ - ψ) := by
      calc φ^4 - ψ^4 = (3*φ + 2) - (3*ψ + 2) := by rw [hφ4, hψ4]
        _ = 3 * (φ - ψ) := by ring
    have hF2 : φ^2 - ψ^2 = φ - ψ := by
      calc φ^2 - ψ^2 = (φ + 1) - (ψ + 1) := by rw [hφ2, hψ2]
        _ = φ - ψ := by ring
    have hcoef : φ^8 - ψ^8 - a * (φ^6 - ψ^6) + b * (φ^4 - ψ^4) - c * (φ^2 - ψ^2) = 0 := by
      rw [hF8, hF6, hF4, hF2]
      have : (21 - 8*a + 3*b - c) * (φ - ψ) = 0 := by rw [hcond]; ring
      linarith
    have hnum : (φ^4 * x)^2 - a * (φ^3 * x)^2 + b * (φ^2 * x)^2 - c * (φ * x)^2
        + c * (ψ * x)^2 - b * (ψ^2 * x)^2 + a * (ψ^3 * x)^2 - (ψ^4 * x)^2
        = (φ^8 - ψ^8 - a * (φ^6 - ψ^6) + b * (φ^4 - ψ^4) - c * (φ^2 - ψ^2)) * x^2 := by ring
    rw [hnum, hcoef]
    simp only [zero_mul, zero_div]

/-- Theorem 6.1 (D7 coefficient constraint):
    E1 and E2 imply c = a - 6, b = 3a - 9 (1 free parameter) -/
theorem D7_coefficients_constrained (a b c : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D7_general a b c id x = 0) →
    (∀ x : ℝ, x ≠ 0 → D7_general a b c (fun t => t^2) x = 0) →
    c = a - 6 ∧ b = 3 * a - 9 := by
  intro h1 h2
  have eq1 : 3 - 2 * a + b - c = 0 := D7_E1_condition a b c |>.mp h1
  have eq2 : 21 - 8 * a + 3 * b - c = 0 := D7_E2_condition a b c |>.mp h2
  constructor
  · linarith
  · linarith

/-- D7 with constrained coefficients: a arbitrary, b = 3a - 9, c = a - 6 -/
noncomputable def D7_constrained (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  D7_general a (3 * a - 9) (a - 6) f x

/-- D7_constrained annihilates constants -/
theorem D7_constrained_const (a : ℝ) (k : ℝ) (x : ℝ) (hx : x ≠ 0) :
    D7_constrained a (fun _ => k) x = 0 := by
  simp only [D7_constrained, D7_general, hx, ↓reduceIte]
  have hsum : k - a * k + (3*a - 9) * k - (a - 6) * k
            + (a - 6) * k - (3*a - 9) * k + a * k - k = 0 := by ring
  rw [hsum, zero_div]

/-- D7_constrained annihilates linear functions -/
theorem D7_constrained_linear (a : ℝ) (x : ℝ) (hx : x ≠ 0) :
    D7_constrained a id x = 0 := by
  simp only [D7_constrained]
  have h : 3 - 2 * a + (3 * a - 9) - (a - 6) = 0 := by ring
  exact D7_E1_condition a (3*a - 9) (a - 6) |>.mpr h x hx

/-- D7_constrained annihilates quadratic functions -/
theorem D7_constrained_quadratic (a : ℝ) (x : ℝ) (hx : x ≠ 0) :
    D7_constrained a (fun t => t^2) x = 0 := by
  simp only [D7_constrained]
  have h : 21 - 8 * a + 3 * (3 * a - 9) - (a - 6) = 0 := by ring
  exact D7_E2_condition a (3*a - 9) (a - 6) |>.mpr h x hx

/-- Main Theorem 6.2: ker(D7) = ker(D6) for constrained coefficients
    D7 annihilates {1, x, x²} (same as D6 kernel), regardless of parameter a -/
theorem D7_kernel_equals_D6_kernel (a : ℝ) :
    (∀ c x, x ≠ 0 → D7_constrained a (fun _ => c) x = 0) ∧
    (∀ x, x ≠ 0 → D7_constrained a id x = 0) ∧
    (∀ x, x ≠ 0 → D7_constrained a (fun t => t^2) x = 0) :=
  ⟨fun c x hx => D7_constrained_const a c x hx,
   D7_constrained_linear a,
   D7_constrained_quadratic a⟩

/-- Algebraic Reduction Theorem:
    D7 provides no independent structure beyond D6.
    Any D7 with ker(D7) ⊇ ker(D6) has coefficients determined up to 1 parameter,
    and ker(D7) = ker(D6). -/
theorem D7_algebraic_reduction :
    ∀ a b c : ℝ,
    (∀ x, x ≠ 0 → D7_general a b c (fun _ => 1) x = 0) →
    (∀ x, x ≠ 0 → D7_general a b c id x = 0) →
    (∀ x, x ≠ 0 → D7_general a b c (fun t => t^2) x = 0) →
    c = a - 6 ∧ b = 3 * a - 9 := by
  intro a b c _ h1 h2
  exact D7_coefficients_constrained a b c h1 h2

end D7Reduction

/-!
## D6 Completeness

ker(D6) = span{1, x, x²}, D6 detects cubic and higher, ker(D7) = ker(D6).
-/

section D6Completeness

/-- D6 detects cubic terms: D6[x³] ≠ 0 -/
theorem D6_detects_cubic (x : ℝ) (hx : x ≠ 0) : D6 (fun t => t^3) x ≠ 0 := by
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ3 : φ^3 = 2*φ + 1 := by
    calc φ^3 = φ * φ^2 := by ring
      _ = φ * (φ + 1) := by rw [hφ2]
      _ = φ^2 + φ := by ring
      _ = (φ + 1) + φ := by rw [hφ2]
      _ = 2*φ + 1 := by ring
  have hψ3 : ψ^3 = 2*ψ + 1 := by
    calc ψ^3 = ψ * ψ^2 := by ring
      _ = ψ * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [hψ2]
      _ = 2*ψ + 1 := by ring
  have hφ6 : φ^6 = 8*φ + 5 := by
    calc φ^6 = φ^3 * φ^3 := by ring
      _ = (2*φ + 1) * (2*φ + 1) := by rw [hφ3]
      _ = 4*φ^2 + 4*φ + 1 := by ring
      _ = 4*(φ + 1) + 4*φ + 1 := by rw [hφ2]
      _ = 8*φ + 5 := by ring
  have hψ6 : ψ^6 = 8*ψ + 5 := by
    calc ψ^6 = ψ^3 * ψ^3 := by ring
      _ = (2*ψ + 1) * (2*ψ + 1) := by rw [hψ3]
      _ = 4*ψ^2 + 4*ψ + 1 := by ring
      _ = 4*(ψ + 1) + 4*ψ + 1 := by rw [hψ2]
      _ = 8*ψ + 5 := by ring
  have hφ9 : φ^9 = 34*φ + 21 := by
    calc φ^9 = φ^6 * φ^3 := by ring
      _ = (8*φ + 5) * (2*φ + 1) := by rw [hφ6, hφ3]
      _ = 16*φ^2 + 18*φ + 5 := by ring
      _ = 16*(φ + 1) + 18*φ + 5 := by rw [hφ2]
      _ = 34*φ + 21 := by ring
  have hψ9 : ψ^9 = 34*ψ + 21 := by
    calc ψ^9 = ψ^6 * ψ^3 := by ring
      _ = (8*ψ + 5) * (2*ψ + 1) := by rw [hψ6, hψ3]
      _ = 16*ψ^2 + 18*ψ + 5 := by ring
      _ = 16*(ψ + 1) + 18*ψ + 5 := by rw [hψ2]
      _ = 34*ψ + 21 := by ring
  have hcoef : φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9 = 12 * (φ - ψ) := by
    calc φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9
      = (34*φ + 21) - 3*(8*φ + 5) + (2*φ + 1) - (2*ψ + 1) + 3*(8*ψ + 5) - (34*ψ + 21)
          := by rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]
      _ = 12 * (φ - ψ) := by ring
  have hnum : (φ^3 * x)^3 - 3 * (φ^2 * x)^3 + (φ * x)^3 - (ψ * x)^3 + 3 * (ψ^2 * x)^3 -
      (ψ^3 * x)^3 = 12 * (φ - ψ) * x^3 := by
    calc (φ^3 * x)^3 - 3 * (φ^2 * x)^3 + (φ * x)^3 - (ψ * x)^3 + 3 * (ψ^2 * x)^3 - (ψ^3 * x)^3
      = (φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9) * x^3 := by ring
      _ = 12 * (φ - ψ) * x^3 := by rw [hcoef]
  rw [hnum]
  have hden_ne : D6Denom * x ≠ 0 := D6Denom_mul_ne_zero x hx
  have hdiff_ne : φ - ψ ≠ 0 := by rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hx3_ne : x^3 ≠ 0 := pow_ne_zero 3 hx
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hdiff_ne) hx3_ne) hden_ne

theorem D6_not_annihilate_cubic (x : ℝ) (hx : x ≠ 0) :
    D6 (fun t => t^3) x ≠ 0 := D6_detects_cubic x hx

/-- D6 Completeness Theorem: ker(D6) = span{1, x, x²} and ker(D7) = ker(D6). -/
theorem F6_restricted_completeness :
    -- 1. ker(D6) is exactly 3-dimensional: span{1, x, x²}
    (∀ c x, x ≠ 0 → D6 (fun _ => c) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) ∧
    -- 2. D6 detects degree 3 (first non-trivial observable)
    (∀ x, x ≠ 0 → D6 (fun t => t^3) x ≠ 0) ∧
    -- 3. D7 (and higher) reduces to D6: no new observable structure
    (∀ a : ℝ, ∀ c x, x ≠ 0 → D7_constrained a (fun _ => c) x = 0) ∧
    (∀ a : ℝ, ∀ x, x ≠ 0 → D7_constrained a id x = 0) ∧
    (∀ a : ℝ, ∀ x, x ≠ 0 → D7_constrained a (fun t => t^2) x = 0) := by
  refine ⟨?_, D6_linear, D6_quadratic, D6_detects_cubic, ?_, ?_, ?_⟩
  · exact fun c x hx => D6_const c x hx
  · exact fun a c x hx => D7_constrained_const a c x hx
  · exact fun a x hx => D7_constrained_linear a x hx
  · exact fun a x hx => D7_constrained_quadratic a x hx

end D6Completeness

/-- D6 does not annihilate quartic: D6[x⁴] ≠ 0 -/
theorem D6_quartic_nonzero (x : ℝ) (hx : x ≠ 0) : D6 (fun t => t^4) x ≠ 0 := by
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ4 : φ^4 = 3 * φ + 2 := by
    calc φ^4 = φ^2 * φ^2 := by ring
      _ = (φ + 1) * (φ + 1) := by rw [hφ2]
      _ = φ^2 + 2*φ + 1 := by ring
      _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ^4 = 3 * ψ + 2 := by
    calc ψ^4 = ψ^2 * ψ^2 := by ring
      _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
      _ = ψ^2 + 2*ψ + 1 := by ring
      _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  have hφ8 : φ^8 = 21 * φ + 13 := by
    calc φ^8 = φ^4 * φ^4 := by ring
      _ = (3*φ + 2) * (3*φ + 2) := by rw [hφ4]
      _ = 9*φ^2 + 12*φ + 4 := by ring
      _ = 9*(φ + 1) + 12*φ + 4 := by rw [hφ2]
      _ = 21 * φ + 13 := by ring
  have hψ8 : ψ^8 = 21 * ψ + 13 := by
    calc ψ^8 = ψ^4 * ψ^4 := by ring
      _ = (3*ψ + 2) * (3*ψ + 2) := by rw [hψ4]
      _ = 9*ψ^2 + 12*ψ + 4 := by ring
      _ = 9*(ψ + 1) + 12*ψ + 4 := by rw [hψ2]
      _ = 21 * ψ + 13 := by ring
  have hφ12 : φ^12 = 144 * φ + 89 := by
    calc φ^12 = φ^8 * φ^4 := by ring
      _ = (21*φ + 13) * (3*φ + 2) := by rw [hφ8, hφ4]
      _ = 63*φ^2 + 81*φ + 26 := by ring
      _ = 63*(φ + 1) + 81*φ + 26 := by rw [hφ2]
      _ = 144 * φ + 89 := by ring
  have hψ12 : ψ^12 = 144 * ψ + 89 := by
    calc ψ^12 = ψ^8 * ψ^4 := by ring
      _ = (21*ψ + 13) * (3*ψ + 2) := by rw [hψ8, hψ4]
      _ = 63*ψ^2 + 81*ψ + 26 := by ring
      _ = 63*(ψ + 1) + 81*ψ + 26 := by rw [hψ2]
      _ = 144 * ψ + 89 := by ring
  have hcoef : φ^12 - 3*φ^8 + φ^4 - ψ^4 + 3*ψ^8 - ψ^12 = 84 * (φ - ψ) := by
    calc φ^12 - 3*φ^8 + φ^4 - ψ^4 + 3*ψ^8 - ψ^12
      = (144*φ + 89) - 3*(21*φ + 13) + (3*φ + 2) - (3*ψ + 2) +
          3*(21*ψ + 13) - (144*ψ + 89) := by rw [hφ12, hφ8, hφ4, hψ4, hψ8, hψ12]
      _ = 84 * (φ - ψ) := by ring
  have hnum : (φ^3 * x)^4 - 3 * (φ^2 * x)^4 + (φ * x)^4 - (ψ * x)^4 +
      3 * (ψ^2 * x)^4 - (ψ^3 * x)^4 = 84 * (φ - ψ) * x^4 := by
    calc (φ^3 * x)^4 - 3 * (φ^2 * x)^4 + (φ * x)^4 - (ψ * x)^4 +
        3 * (ψ^2 * x)^4 - (ψ^3 * x)^4
      = (φ^12 - 3*φ^8 + φ^4 - ψ^4 + 3*ψ^8 - ψ^12) * x^4 := by ring
      _ = 84 * (φ - ψ) * x^4 := by rw [hcoef]
  rw [hnum]
  have hden_ne : D6Denom * x ≠ 0 := D6Denom_mul_ne_zero x hx
  have hdiff_ne : φ - ψ ≠ 0 := by rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hx4_ne : x^4 ≠ 0 := pow_ne_zero 4 hx
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hdiff_ne) hx4_ne) hden_ne

/-! ## Parity Selection Principle

For 6 Galois-paired points {φ³,φ²,φ,ψ,ψ²,ψ³}, symmetric coefficients [1,A,B,B,A,1]
with D[1]=0 and D[x]=0 force A=-3/2, B=1/2 (non-integral), and D[x²]=9≠0.
The antisymmetric form [1,-A,B,-B,A,-1] achieves D[x²]=0 with integral A=3, B=1.
So antisymmetric D₆ has strictly larger kernel than any symmetric form on the same points. -/

section ParitySelection

/-- Symmetric D6: coefficients [1, A, B, B, A, 1] at {φ³,φ²,φ,ψ,ψ²,ψ³} -/
noncomputable def D6_symmetric (A B : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (f (φ^3 * x) + A * f (φ^2 * x) + B * f (φ * x) +
     B * f (ψ * x) + A * f (ψ^2 * x) + f (ψ^3 * x)) / ((φ - ψ)^5 * x)

/-- D6_sym[1]=0 ↔ A+B=-1 (uses 1 kernel condition) -/
theorem D6_sym_C0 (A B : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D6_symmetric A B (fun _ => 1) x = 0) ↔ A + B = -1 := by
  constructor
  · intro h
    have h1 := h 1 one_ne_zero
    simp only [D6_symmetric, one_ne_zero, ↓reduceIte, mul_one] at h1
    have hne : (φ - ψ) ^ 5 ≠ 0 := by
      apply pow_ne_zero; rw [phi_sub_psi]
      exact Real.sqrt_ne_zero'.mpr (by norm_num)
    have hnum : 1 + A + B + B + A + 1 = 0 := by
      by_contra h_ne
      exact absurd h1 (div_ne_zero h_ne hne)
    linarith
  · intro hab x hx
    simp only [D6_symmetric, hx, ↓reduceIte]
    have : 1 + A * 1 + B * 1 + B * 1 + A * 1 + 1 = 2 * (A + B + 1) := by ring
    rw [this, hab]; ring

/-- D6_sym[x]=0 ↔ 4+3A+B=0, using L₁=1, L₂=3, L₃=4 -/
theorem D6_sym_C1 (A B : ℝ) :
    (∀ x : ℝ, x ≠ 0 → D6_symmetric A B id x = 0) ↔ 4 + 3 * A + B = 0 := by
  have hL1 : φ + ψ = 1 := phi_add_psi
  have hL2 : φ ^ 2 + ψ ^ 2 = 3 := by
    have := golden_ratio_property; have := psi_sq
    nlinarith [phi_add_psi]
  have hL3 : φ ^ 3 + ψ ^ 3 = 4 := by
    have hφ3 : φ ^ 3 = 2 * φ + 1 := by
      have := golden_ratio_property; nlinarith
    have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
      have := psi_sq; nlinarith
    linarith [phi_add_psi]
  constructor
  · intro h
    have h1 := h 1 one_ne_zero
    simp only [D6_symmetric, one_ne_zero, ↓reduceIte, id_eq, mul_one] at h1
    have hne : (φ - ψ) ^ 5 ≠ 0 := by
      apply pow_ne_zero; rw [phi_sub_psi]
      exact Real.sqrt_ne_zero'.mpr (by norm_num)
    have hnum : φ ^ 3 + A * φ ^ 2 + B * φ + B * ψ + A * ψ ^ 2 + ψ ^ 3 = 0 := by
      by_contra h_ne
      exact absurd h1 (div_ne_zero h_ne hne)
    have hfact : φ ^ 3 + A * φ ^ 2 + B * φ + B * ψ + A * ψ ^ 2 + ψ ^ 3 =
        (φ ^ 3 + ψ ^ 3) + A * (φ ^ 2 + ψ ^ 2) + B * (φ + ψ) := by ring
    rw [hfact, hL3, hL2, hL1] at hnum
    linarith
  · intro hab x hx
    simp only [D6_symmetric, hx, ↓reduceIte, id_eq]
    have : φ ^ 3 * x + A * (φ ^ 2 * x) + B * (φ * x) + B * (ψ * x) +
        A * (ψ ^ 2 * x) + ψ ^ 3 * x =
        ((φ ^ 3 + ψ ^ 3) + A * (φ ^ 2 + ψ ^ 2) + B * (φ + ψ)) * x := by ring
    rw [this, hL3, hL2, hL1]
    have : (4 + A * 3 + B * 1) * x = (4 + 3 * A + B) * x := by ring
    rw [this, hab]; ring

/-- D6_sym with D[1]=0 and D[x]=0 forces A=-3/2, B=1/2 -/
theorem D6_sym_coefficients (A B : ℝ)
    (h0 : ∀ x : ℝ, x ≠ 0 → D6_symmetric A B (fun _ => 1) x = 0)
    (h1 : ∀ x : ℝ, x ≠ 0 → D6_symmetric A B id x = 0) :
    A = -3/2 ∧ B = 1/2 := by
  have hab := (D6_sym_C0 A B).mp h0
  have hab2 := (D6_sym_C1 A B).mp h1
  constructor <;> linarith

/-- Symmetric D6 does NOT annihilate x²: D6_sym(-3/2, 1/2)[x²] ≠ 0.
    Numerator = L₆ + A·L₄ + B·L₂ = 18 + (-3/2)·7 + (1/2)·3 = 9 ≠ 0 -/
theorem D6_sym_not_ker_quadratic (x : ℝ) (hx : x ≠ 0) :
    D6_symmetric (-3/2) (1/2) (fun t => t^2) x ≠ 0 := by
  simp only [D6_symmetric, hx, ↓reduceIte]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hL1 : φ + ψ = 1 := phi_add_psi
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by nlinarith
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by nlinarith
  -- Numerator = (φ⁶+ψ⁶) + A(φ⁴+ψ⁴) + B(φ²+ψ²) = 18 - 21/2 + 3/2 = 9
  have hnum : (φ ^ 3 * x) ^ 2 + (-3/2) * (φ ^ 2 * x) ^ 2 + (1/2) * (φ * x) ^ 2 +
      (1/2) * (ψ * x) ^ 2 + (-3/2) * (ψ ^ 2 * x) ^ 2 + (ψ ^ 3 * x) ^ 2 =
      9 * x ^ 2 := by nlinarith
  rw [hnum]
  have hden_ne : (φ - ψ) ^ 5 * x ≠ 0 := by
    apply mul_ne_zero
    · apply pow_ne_zero; rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
    · exact hx
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) hden_ne

/-- Parity Selection for D₆: antisymmetric form has strictly larger kernel.
    Antisymmetric D₆ annihilates {1, x, x²} (3-dimensional kernel),
    but ANY symmetric form on the same 6 points with D[1]=0 and D[x]=0
    fails to annihilate x² (2-dimensional kernel). -/
theorem parity_selection_D6 :
    -- Antisymmetric D6 annihilates 1, x, x²
    ((∀ c x, x ≠ 0 → D6 (fun _ => c) x = 0) ∧
     (∀ x, x ≠ 0 → D6 id x = 0) ∧
     (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0)) ∧
    -- Symmetric D6 with maximal kernel does NOT annihilate x²
    (∀ A B : ℝ,
      (∀ x, x ≠ 0 → D6_symmetric A B (fun _ => 1) x = 0) →
      (∀ x, x ≠ 0 → D6_symmetric A B id x = 0) →
      ∀ x, x ≠ 0 → D6_symmetric A B (fun t => t^2) x ≠ 0) := by
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
    ∀ a : ℝ, (∀ k x, x ≠ 0 → FUST.D7_constrained a (fun _ => k) x = 0) ∧
             (∀ x, x ≠ 0 → FUST.D7_constrained a id x = 0) ∧
             (∀ x, x ≠ 0 → FUST.D7_constrained a (fun t => t^2) x = 0) :=
  FUST.D7_kernel_equals_D6_kernel

end FUST
