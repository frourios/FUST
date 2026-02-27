import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Fin.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace FUST

open Complex

noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2
noncomputable def ψ : ℝ := (1 - Real.sqrt 5) / 2

lemma golden_ratio_property : φ^2 = φ + 1 := Real.goldenRatio_sq
lemma phi_pos : 0 < φ := Real.goldenRatio_pos
theorem φ_gt_one : 1 < φ := Real.one_lt_goldenRatio

lemma phi_inv : φ⁻¹ = φ - 1 := by
  have h1 : φ⁻¹ = -ψ := Real.inv_goldenRatio
  have h2 : φ + ψ = 1 := Real.goldenRatio_add_goldenConj
  linarith

theorem phi_cubed : φ ^ 3 = 2 * φ + 1 := by
  nlinarith [golden_ratio_property]

lemma psi_neg : ψ < 0 := Real.goldenConj_neg
lemma phi_sub_psi : φ - ψ = Real.sqrt 5 := Real.goldenRatio_sub_goldenConj
lemma phi_add_psi : φ + ψ = 1 := Real.goldenRatio_add_goldenConj
lemma phi_mul_psi : φ * ψ = -1 := Real.goldenRatio_mul_goldenConj
lemma psi_sq : ψ ^ 2 = ψ + 1 := Real.goldenConj_sq

lemma abs_psi_lt_one : |ψ| < 1 := by
  have hψ : ψ < 0 := psi_neg
  have hψ_gt : ψ > -1 := by
    have h : ψ ^ 2 = ψ + 1 := psi_sq
    have hψ : ψ < 0 := psi_neg
    have hψ2_pos : ψ ^ 2 > 0 := sq_pos_of_neg hψ
    linarith
  rw [abs_of_neg hψ]
  linarith

section ComplexGolden

lemma phi_ne_zero : φ ≠ 0 := ne_of_gt phi_pos

lemma psi_ne_zero : ψ ≠ 0 := ne_of_lt psi_neg

lemma phi_sub_psi_ne : φ - ψ ≠ 0 := by
  rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)

lemma phi_sub_psi_complex_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := by
  rw [← ofReal_sub, ne_eq, ofReal_eq_zero]; exact phi_sub_psi_ne

lemma golden_ratio_property_complex : (↑φ : ℂ) ^ 2 = ↑φ + 1 := by
  have h := golden_ratio_property
  have : (↑(φ ^ 2) : ℂ) = ↑(φ + 1) := congrArg _ h
  simp only [ofReal_pow, ofReal_add, ofReal_one] at this; exact this

lemma psi_sq_complex : (↑ψ : ℂ) ^ 2 = ↑ψ + 1 := by
  have h := psi_sq
  have : (↑(ψ ^ 2) : ℂ) = ↑(ψ + 1) := congrArg _ h
  simp only [ofReal_pow, ofReal_add, ofReal_one] at this; exact this

lemma phi_cubed_complex : (↑φ : ℂ) ^ 3 = 2 * ↑φ + 1 := by
  have h := phi_cubed
  have : (↑(φ ^ 3) : ℂ) = ↑(2 * φ + 1) := congrArg _ h
  simp only [ofReal_pow, ofReal_add, ofReal_mul, ofReal_one, ofReal_ofNat] at this; exact this

lemma psi_cubed_complex : (↑ψ : ℂ) ^ 3 = 2 * ↑ψ + 1 := by
  have h : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [psi_sq]
  have : (↑(ψ ^ 3) : ℂ) = ↑(2 * ψ + 1) := congrArg _ h
  simp only [ofReal_pow, ofReal_add, ofReal_mul, ofReal_one, ofReal_ofNat] at this; exact this

lemma phi_mul_psi_complex : (↑φ : ℂ) * ↑ψ = -1 := by
  rw [← ofReal_mul]
  simp [phi_mul_psi]

lemma phi_add_psi_complex : (↑φ : ℂ) + ↑ψ = 1 := by
  rw [← ofReal_add, ← ofReal_one]
  exact congrArg _ phi_add_psi

private lemma liftR {a b : ℝ} (h : a = b) : (↑a : ℂ) = ↑b := congrArg ofReal h

lemma psi_cubed_alt : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [psi_sq]

private lemma phi_pow4_r : φ ^ 4 = 3 * φ + 2 := by nlinarith [golden_ratio_property]
private lemma psi_pow4_r : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [psi_sq]
private lemma phi_pow6_r : φ ^ 6 = 8 * φ + 5 := by nlinarith [golden_ratio_property, phi_pow4_r]
private lemma psi_pow6_r : ψ ^ 6 = 8 * ψ + 5 := by nlinarith [psi_sq, psi_pow4_r]
private lemma phi_pow8_r : φ ^ 8 = 21 * φ + 13 := by nlinarith [golden_ratio_property, phi_pow4_r]
private lemma psi_pow8_r : ψ ^ 8 = 21 * ψ + 13 := by nlinarith [psi_sq, psi_pow4_r]

lemma phi_pow4_complex : (↑φ : ℂ) ^ 4 = 3 * ↑φ + 2 := by
  have := liftR phi_pow4_r; push_cast at this; exact this
lemma psi_pow4_complex : (↑ψ : ℂ) ^ 4 = 3 * ↑ψ + 2 := by
  have := liftR psi_pow4_r; push_cast at this; exact this
lemma phi_pow6_complex : (↑φ : ℂ) ^ 6 = 8 * ↑φ + 5 := by
  have := liftR phi_pow6_r; push_cast at this; exact this
lemma psi_pow6_complex : (↑ψ : ℂ) ^ 6 = 8 * ↑ψ + 5 := by
  have := liftR psi_pow6_r; push_cast at this; exact this
lemma phi_pow8_complex : (↑φ : ℂ) ^ 8 = 21 * ↑φ + 13 := by
  have := liftR phi_pow8_r; push_cast at this; exact this
lemma psi_pow8_complex : (↑ψ : ℂ) ^ 8 = 21 * ↑ψ + 13 := by
  have := liftR psi_pow8_r; push_cast at this; exact this

end ComplexGolden

section Zeta6

attribute [local ext] Complex.ext

/-- ζ₆ = e^{iπ/3} = (1 + i√3)/2 -/
noncomputable def ζ₆ : ℂ := ⟨1/2, Real.sqrt 3 / 2⟩

/-- ζ₆' = e^{-iπ/3} = (1 - i√3)/2 -/
noncomputable def ζ₆' : ℂ := ⟨1/2, -(Real.sqrt 3 / 2)⟩

lemma sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- ζ₆ + ζ₆' = 1 (same trace as φ + ψ = 1) -/
theorem zeta6_add_conj : ζ₆ + ζ₆' = 1 := by ext <;> simp [ζ₆, ζ₆']; ring

/-- ζ₆ · ζ₆' = +1 (contrast with φψ = -1) -/
theorem zeta6_mul_conj : ζ₆ * ζ₆' = 1 := by
  ext <;> simp [ζ₆, ζ₆', mul_re, mul_im]
  · have h := sqrt3_sq; nlinarith
  · ring

/-- ζ₆² = ζ₆ - 1 (contrast with φ² = φ + 1) -/
theorem zeta6_sq : ζ₆ ^ 2 = ζ₆ - 1 := by
  ext <;> simp [ζ₆, sq, mul_re, mul_im]
  · have h := sqrt3_sq; nlinarith
  · ring

/-- ζ₆³ = -1 -/
theorem zeta6_cubed : ζ₆ ^ 3 = -1 := by
  have : ζ₆ ^ 3 = ζ₆ ^ 2 * ζ₆ := by ring
  rw [this, zeta6_sq]
  ext <;> simp [ζ₆, mul_re, mul_im]
  · have h := sqrt3_sq; nlinarith
  · ring

/-- ζ₆⁶ = 1 -/
theorem zeta6_pow_six : ζ₆ ^ 6 = 1 := by
  have : ζ₆ ^ 6 = (ζ₆ ^ 3) ^ 2 := by ring
  rw [this, zeta6_cubed]; norm_num

/-- |ζ₆| = 1 (compact: isometric action) -/
theorem norm_zeta6 : ‖ζ₆‖ = 1 :=
  norm_eq_one_of_pow_eq_one zeta6_pow_six (by norm_num)

/-- ζ₆ ≠ 0 -/
theorem zeta6_ne_zero : ζ₆ ≠ 0 := by
  intro h
  have h1 : ‖ζ₆‖ = 0 := by rw [h, norm_zero]
  linarith [norm_zeta6]

/-- ζ₆⁴ = -ζ₆ -/
theorem zeta6_pow_four : ζ₆ ^ 4 = -ζ₆ := by
  have : ζ₆ ^ 4 = ζ₆ ^ 3 * ζ₆ := by ring
  rw [this, zeta6_cubed]; ring

/-- ζ₆⁵ = 1 - ζ₆ -/
theorem zeta6_pow_five : ζ₆ ^ 5 = 1 - ζ₆ := by
  have : ζ₆ ^ 5 = ζ₆ ^ 3 * ζ₆ ^ 2 := by ring
  rw [this, zeta6_cubed, zeta6_sq]; ring

/-! ## ζ₆ - ζ₆' properties -/

/-- ζ₆ - ζ₆' = i√3 -/
theorem zeta6_sub_conj : ζ₆ - ζ₆' = ⟨0, Real.sqrt 3⟩ := by
  ext <;> simp [ζ₆, ζ₆']

/-- ζ₆ - ζ₆' ≠ 0 -/
theorem zeta6_sub_conj_ne_zero : ζ₆ - ζ₆' ≠ 0 := by
  rw [zeta6_sub_conj]
  intro h
  have him := congr_arg Complex.im h
  simp at him

/-- ζ₆' ≠ 0 -/
theorem zeta6'_ne_zero : ζ₆' ≠ 0 := by
  intro h; have := congr_arg Complex.re h
  simp [ζ₆'] at this

/-- ζ₆' = ζ₆⁻¹ -/
theorem zeta6'_eq_inv : ζ₆' = ζ₆⁻¹ :=
  eq_inv_of_mul_eq_one_right zeta6_mul_conj

/-- |ζ₆'| = 1 -/
theorem norm_zeta6' : ‖ζ₆'‖ = 1 := by
  rw [zeta6'_eq_inv, norm_inv, norm_zeta6, inv_one]

/-- ζ₆' = starRingEnd ℂ ζ₆ (complex conjugate) -/
theorem zeta6'_eq_starRingEnd : ζ₆' = starRingEnd ℂ ζ₆ := by
  ext <;> simp [ζ₆, ζ₆']

end Zeta6

end FUST
