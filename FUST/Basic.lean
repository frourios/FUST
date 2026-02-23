import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace FUST

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

section FrourioExponential
/-!
## F-Exponential Function and Frourio Constant

$$
\exp_{\mathsf{F}}(x) = \sum_{n=0}^{\infty} \frac{x^n}{n!_F}, \quad
\mathfrak{f} := \exp_{\mathsf{F}}(1) \approx 3.7045
$$

### Key Properties

1. **Eigenfunction**: $D_{\mathsf{F}}[\exp_{\mathsf{F}}] = \exp_{\mathsf{F}}$
2. **Umbral addition**: $\exp_F(x \oplus y) = \exp_F(x) \cdot \exp_F(y)$
3. **Free variable**: $\mathfrak{f} = \exp_{\mathsf{F}}(1 \oplus r) / \exp_{\mathsf{F}}(r)$

### Binet Formula

$$c_n^F = \frac{\varphi^n - \psi^n}{\sqrt{5}} = F_n$$

where φ = (1+√5)/2 and ψ = (1-√5)/2 are conjugate golden ratios.
-/

/-- Binet formula: c_n^F = (φ^n - ψ^n) / √5 = F_n (Fibonacci number) -/
noncomputable def FStructureConst (n : ℕ) : ℝ :=
  (φ ^ n - ψ ^ n) / Real.sqrt 5

/-- F-factorial: n!_F = ∏_{k=1}^n c_k^F -/
noncomputable def FFactorial (n : ℕ) : ℝ :=
  (Finset.range n).prod (fun k => FStructureConst (k + 1))

/-- Frourio constant: 𝔣 = exp_F(1) = Σ_{n=0}^∞ 1/n!_F ≈ 3.7045 -/
noncomputable def frourioConst : ℝ :=
  (Finset.range 20).sum (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n)

/-- FStructureConst(1) = 1 (first Fibonacci number) -/
lemma FStructureConst_one : FStructureConst 1 = 1 := by
  simp only [FStructureConst, pow_one]
  have h : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hsqrt : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (5 : ℝ) > 0)
  rw [h]
  field_simp

/-- FStructureConst(2) = 1 (second Fibonacci number) -/
lemma FStructureConst_two : FStructureConst 2 = 1 := by
  simp only [FStructureConst]
  have h : φ ^ 2 - ψ ^ 2 = Real.sqrt 5 := by
    have : φ ^ 2 - ψ ^ 2 = (φ - ψ) * (φ + ψ) := by ring
    rw [this, phi_sub_psi, phi_add_psi]
    ring
  have hsqrt : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (5 : ℝ) > 0)
  rw [h]
  field_simp

/-- FStructureConst(3) = 2 (third Fibonacci number) -/
lemma FStructureConst_three : FStructureConst 3 = 2 := by
  simp only [FStructureConst]
  have h3 : φ ^ 3 - ψ ^ 3 = 2 * Real.sqrt 5 := by
    have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
    have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
      have hsq : ψ ^ 2 = ψ + 1 := psi_sq
      calc ψ ^ 3 = ψ ^ 2 * ψ := by ring
        _ = (ψ + 1) * ψ := by rw [hsq]
        _ = ψ ^ 2 + ψ := by ring
        _ = (ψ + 1) + ψ := by rw [hsq]
        _ = 2 * ψ + 1 := by ring
    calc φ ^ 3 - ψ ^ 3 = (2 * φ + 1) - (2 * ψ + 1) := by rw [hφ3, hψ3]
      _ = 2 * (φ - ψ) := by ring
      _ = 2 * Real.sqrt 5 := by rw [phi_sub_psi]
  have hsqrt : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (5 : ℝ) > 0)
  rw [h3]
  field_simp

/-- FFactorial(0) = 1 (empty product) -/
lemma FFactorial_zero : FFactorial 0 = 1 := by simp [FFactorial]

/-- FFactorial(1) = 1 -/
lemma FFactorial_one : FFactorial 1 = 1 := by
  simp [FFactorial, FStructureConst_one]

/-- FFactorial(2) = 1 -/
lemma FFactorial_two : FFactorial 2 = 1 := by
  simp [FFactorial, Finset.prod_range_succ, FStructureConst_one, FStructureConst_two]

/-- FFactorial(3) = 2 -/
lemma FFactorial_three : FFactorial 3 = 2 := by
  simp [FFactorial, Finset.prod_range_succ, FStructureConst_one, FStructureConst_two,
        FStructureConst_three]

/-- φ^4 - ψ^4 = 3√5 -/
lemma phi_pow_four_sub_psi : φ ^ 4 - ψ ^ 4 = 3 * Real.sqrt 5 := by
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by
    calc φ ^ 4 = (φ ^ 2) ^ 2 := by ring
      _ = (φ + 1) ^ 2 := by rw [hφ2]
      _ = φ ^ 2 + 2 * φ + 1 := by ring
      _ = (φ + 1) + 2 * φ + 1 := by rw [hφ2]
      _ = 3 * φ + 2 := by ring
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by
    calc ψ ^ 4 = (ψ ^ 2) ^ 2 := by ring
      _ = (ψ + 1) ^ 2 := by rw [hψ2]
      _ = ψ ^ 2 + 2 * ψ + 1 := by ring
      _ = (ψ + 1) + 2 * ψ + 1 := by rw [hψ2]
      _ = 3 * ψ + 2 := by ring
  calc φ ^ 4 - ψ ^ 4 = (3 * φ + 2) - (3 * ψ + 2) := by rw [hφ4, hψ4]
    _ = 3 * (φ - ψ) := by ring
    _ = 3 * Real.sqrt 5 := by rw [phi_sub_psi]

/-- FStructureConst(4) = 3 (fourth Fibonacci number) -/
lemma FStructureConst_four : FStructureConst 4 = 3 := by
  simp only [FStructureConst]
  have h := phi_pow_four_sub_psi
  have hsqrt : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (5 : ℝ) > 0)
  rw [h]
  field_simp

/-- φ^5 - ψ^5 = 5√5 -/
lemma phi_pow_five_sub_psi : φ ^ 5 - ψ ^ 5 = 5 * Real.sqrt 5 := by
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ5 : φ ^ 5 = 5 * φ + 3 := by
    calc φ ^ 5 = φ ^ 4 * φ := by ring
      _ = (φ ^ 2) ^ 2 * φ := by ring
      _ = (φ + 1) ^ 2 * φ := by rw [hφ2]
      _ = (φ ^ 2 + 2 * φ + 1) * φ := by ring
      _ = ((φ + 1) + 2 * φ + 1) * φ := by rw [hφ2]
      _ = (3 * φ + 2) * φ := by ring
      _ = 3 * φ ^ 2 + 2 * φ := by ring
      _ = 3 * (φ + 1) + 2 * φ := by rw [hφ2]
      _ = 5 * φ + 3 := by ring
  have hψ5 : ψ ^ 5 = 5 * ψ + 3 := by
    calc ψ ^ 5 = ψ ^ 4 * ψ := by ring
      _ = (ψ ^ 2) ^ 2 * ψ := by ring
      _ = (ψ + 1) ^ 2 * ψ := by rw [hψ2]
      _ = (ψ ^ 2 + 2 * ψ + 1) * ψ := by ring
      _ = ((ψ + 1) + 2 * ψ + 1) * ψ := by rw [hψ2]
      _ = (3 * ψ + 2) * ψ := by ring
      _ = 3 * ψ ^ 2 + 2 * ψ := by ring
      _ = 3 * (ψ + 1) + 2 * ψ := by rw [hψ2]
      _ = 5 * ψ + 3 := by ring
  calc φ ^ 5 - ψ ^ 5 = (5 * φ + 3) - (5 * ψ + 3) := by rw [hφ5, hψ5]
    _ = 5 * (φ - ψ) := by ring
    _ = 5 * Real.sqrt 5 := by rw [phi_sub_psi]

/-- FStructureConst(5) = 5 (fifth Fibonacci number) -/
lemma FStructureConst_five : FStructureConst 5 = 5 := by
  simp only [FStructureConst]
  have h := phi_pow_five_sub_psi
  have hsqrt : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (5 : ℝ) > 0)
  rw [h]
  field_simp

/-- FFactorial(4) = 6 -/
lemma FFactorial_four : FFactorial 4 = 6 := by
  simp [FFactorial, Finset.prod_range_succ, FStructureConst_one, FStructureConst_two,
        FStructureConst_three, FStructureConst_four]
  norm_num

/-- FFactorial(5) = 30 -/
lemma FFactorial_five : FFactorial 5 = 30 := by
  simp [FFactorial, Finset.prod_range_succ, FStructureConst_one, FStructureConst_two,
        FStructureConst_three, FStructureConst_four, FStructureConst_five]
  norm_num

/-- φ^6 - ψ^6 = 8√5 -/
lemma phi_pow_six_sub_psi : φ ^ 6 - ψ ^ 6 = 8 * Real.sqrt 5 := by
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by
    calc φ ^ 6 = (φ ^ 2) ^ 3 := by ring
      _ = (φ + 1) ^ 3 := by rw [hφ2]
      _ = φ ^ 3 + 3 * φ ^ 2 + 3 * φ + 1 := by ring
      _ = (2 * φ + 1) + 3 * (φ + 1) + 3 * φ + 1 := by rw [phi_cubed, hφ2]
      _ = 8 * φ + 5 := by ring
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by
    have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
      calc ψ ^ 3 = ψ ^ 2 * ψ := by ring
        _ = (ψ + 1) * ψ := by rw [hψ2]
        _ = ψ ^ 2 + ψ := by ring
        _ = (ψ + 1) + ψ := by rw [hψ2]
        _ = 2 * ψ + 1 := by ring
    calc ψ ^ 6 = (ψ ^ 2) ^ 3 := by ring
      _ = (ψ + 1) ^ 3 := by rw [hψ2]
      _ = ψ ^ 3 + 3 * ψ ^ 2 + 3 * ψ + 1 := by ring
      _ = (2 * ψ + 1) + 3 * (ψ + 1) + 3 * ψ + 1 := by rw [hψ3, hψ2]
      _ = 8 * ψ + 5 := by ring
  calc φ ^ 6 - ψ ^ 6 = (8 * φ + 5) - (8 * ψ + 5) := by rw [hφ6, hψ6]
    _ = 8 * (φ - ψ) := by ring
    _ = 8 * Real.sqrt 5 := by rw [phi_sub_psi]

/-- FStructureConst(6) = 8 (sixth Fibonacci number) -/
lemma FStructureConst_six : FStructureConst 6 = 8 := by
  simp only [FStructureConst]
  have h := phi_pow_six_sub_psi
  have hsqrt : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (5 : ℝ) > 0)
  rw [h]
  field_simp

/-- FFactorial(6) = 240 -/
lemma FFactorial_six : FFactorial 6 = 240 := by
  simp [FFactorial, Finset.prod_range_succ, FStructureConst_one, FStructureConst_two,
        FStructureConst_three, FStructureConst_four, FStructureConst_five, FStructureConst_six]
  norm_num

/-- ψ + 1 > 0 (needed for FFactorial positivity) -/
lemma psi_add_one_pos : ψ + 1 > 0 := by
  have h : ψ ^ 2 = ψ + 1 := psi_sq
  have hψ : ψ < 0 := psi_neg
  have hψ2_pos : ψ ^ 2 > 0 := sq_pos_of_neg hψ
  linarith

/-- |ψ| < 1 -/
lemma abs_psi_lt_one : |ψ| < 1 := by
  have hψ : ψ < 0 := psi_neg
  have hψ_gt : ψ > -1 := by
    have h : ψ + 1 > 0 := psi_add_one_pos
    linarith
  rw [abs_of_neg hψ]
  linarith

/-- φ^n > ψ^n for all n ≥ 1 -/
lemma phi_pow_gt_psi_pow (n : ℕ) (hn : n ≥ 1) : φ ^ n > ψ ^ n := by
  have hφ : φ > 0 := phi_pos
  have hψ : ψ < 0 := psi_neg
  have hφ_gt : φ > 1 := φ_gt_one
  have hφn_pos : φ ^ n > 0 := pow_pos hφ n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 2k (even): ψ^n > 0 but |ψ|^n < 1 < φ^n
    rcases k with _ | k
    · omega
    · have hn_eq : n = 2 * (k + 1) := by omega
      have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
      have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
      have hψ2_pos : 0 < ψ ^ 2 := sq_pos_of_neg hψ
      have hψ2_lt : ψ ^ 2 < 1 := by
        rw [hψ2]
        have := psi_add_one_pos
        have hψ_gt : ψ > -1 := by linarith
        linarith [psi_neg]
      have hφ2_gt : φ ^ 2 > 1 := by rw [hφ2]; linarith
      have h1 : (ψ ^ 2) ^ (k + 1) < 1 := pow_lt_one₀ hψ2_pos.le hψ2_lt (by omega)
      have h2 : (φ ^ 2) ^ (k + 1) > 1 := one_lt_pow₀ hφ2_gt (by omega : k + 1 ≠ 0)
      calc φ ^ n = φ ^ (2 * (k + 1)) := by rw [hn_eq]
        _ = (φ ^ 2) ^ (k + 1) := by ring
        _ > 1 := h2
        _ > (ψ ^ 2) ^ (k + 1) := h1
        _ = ψ ^ (2 * (k + 1)) := by ring
        _ = ψ ^ n := by rw [hn_eq]
  · -- n = 2k + 1 (odd): ψ^n < 0 < φ^n
    have hn_eq : n = 2 * k + 1 := by omega
    have hψ_odd : ψ ^ n < 0 := by
      rw [hn_eq]
      have h1 : ψ ^ (2 * k + 1) = ψ ^ (2 * k) * ψ := by ring
      rw [h1]
      have hψ2k_pos : ψ ^ (2 * k) > 0 := by
        have : ψ ^ (2 * k) = (ψ ^ 2) ^ k := by ring
        rw [this]
        exact pow_pos (sq_pos_of_neg hψ) k
      exact mul_neg_of_pos_of_neg hψ2k_pos hψ
    linarith

/-- FStructureConst(n) ≥ 1 for n ≥ 1 -/
lemma FStructureConst_ge_one (n : ℕ) (hn : n ≥ 1) : FStructureConst n ≥ 1 := by
  match n with
  | 1 => simp [FStructureConst_one]
  | 2 => simp [FStructureConst_two]
  | n + 3 =>
    simp only [FStructureConst]
    have hsqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
    rw [ge_iff_le, le_div_iff₀ hsqrt5_pos]
    have hphi_gt : φ ^ (n + 3) ≥ φ ^ 3 := by
      have hφ_gt1 : φ > 1 := φ_gt_one
      exact pow_le_pow_right₀ hφ_gt1.le (by omega : 3 ≤ n + 3)
    have hphi3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
    have hpsi_abs : |ψ ^ (n + 3)| < 1 := by
      have habs := abs_psi_lt_one
      calc |ψ ^ (n + 3)| = |ψ| ^ (n + 3) := abs_pow ψ (n + 3)
        _ < 1 := pow_lt_one₀ (abs_nonneg ψ) habs (by omega)
    have hpsi_bound : ψ ^ (n + 3) > -1 ∧ ψ ^ (n + 3) < 1 := abs_lt.mp hpsi_abs
    have hsqrt5_gt2 : Real.sqrt 5 > 2 := by
      have h1 : (2 : ℝ) < Real.sqrt 5 := by
        have : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)]
        rw [← this]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    have hφ_val : φ = (1 + Real.sqrt 5) / 2 := rfl
    have hφ_gt15 : φ > 3/2 := by rw [hφ_val]; linarith
    have hphi3_gt : φ ^ 3 > Real.sqrt 5 := by
      rw [hphi3, hφ_val]
      calc 2 * ((1 + Real.sqrt 5) / 2) + 1 = Real.sqrt 5 + 2 := by ring
        _ > Real.sqrt 5 := by linarith
    have hpsi_lt : ψ ^ (n + 3) < 1 := hpsi_bound.2
    have hphi3_val : φ ^ 3 > 2 := by rw [hphi3]; linarith
    have hcalc : 1 * Real.sqrt 5 < φ ^ (n + 3) - ψ ^ (n + 3) :=
      calc 1 * Real.sqrt 5 = Real.sqrt 5 := by ring
        _ < φ ^ 3 - 1 := by linarith
        _ < φ ^ 3 - ψ ^ (n + 3) := by linarith
        _ ≤ φ ^ (n + 3) - ψ ^ (n + 3) := by linarith
    exact le_of_lt hcalc

/-- F-factorial is positive for all n -/
lemma FFactorial_pos (n : ℕ) : 0 < FFactorial n := by
  induction n with
  | zero => simp [FFactorial]
  | succ n ih =>
    simp only [FFactorial, Finset.prod_range_succ]
    apply mul_pos ih
    exact lt_of_lt_of_le one_pos (FStructureConst_ge_one (n + 1) (by omega))

/-- FFactorial is nonzero for all n -/
lemma FFactorial_ne_zero (n : ℕ) : FFactorial n ≠ 0 := ne_of_gt (FFactorial_pos n)

/-- FFactorial is monotone increasing for n ≥ 0 -/
lemma FFactorial_mono {m n : ℕ} (h : m ≤ n) : FFactorial m ≤ FFactorial n := by
  induction h with
  | refl => exact le_refl _
  | @step k _ ih =>
    calc FFactorial m ≤ FFactorial k := ih
      _ ≤ FFactorial k * FStructureConst (k + 1) := by
          have hf_ge_one := FStructureConst_ge_one (k + 1) (by omega)
          nlinarith [FFactorial_pos k]
      _ = FFactorial (k + 1) := by simp [FFactorial, Finset.prod_range_succ]

/-- The Frourio constant is greater than 3.7 -/
theorem frourioConst_gt_37 : frourioConst > 37/10 := by
  unfold frourioConst
  have hf0 : FFactorial 0 = 1 := FFactorial_zero
  have hf1 : FFactorial 1 = 1 := FFactorial_one
  have hf2 : FFactorial 2 = 1 := FFactorial_two
  have hf3 : FFactorial 3 = 2 := FFactorial_three
  have hf4 : FFactorial 4 = 6 := FFactorial_four
  have hf5 : FFactorial 5 = 30 := FFactorial_five
  have h_first6 : (Finset.range 6).sum
      (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n) = 37/10 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               FFactorial_ne_zero, ↓reduceIte, hf0, hf1, hf2, hf3, hf4, hf5]
    norm_num
  have h_tail_pos : ∀ x ∈ Finset.range 20,
      (if FFactorial x = 0 then (0 : ℝ) else 1 / FFactorial x) ≥ 0 := by
    intro x _
    split_ifs
    · exact le_refl 0
    · exact le_of_lt (div_pos one_pos (FFactorial_pos x))
  have h6 : 6 ∈ Finset.range 20 \ Finset.range 6 := by simp
  have h6_pos : (if FFactorial 6 = 0 then (0 : ℝ) else 1 / FFactorial 6) > 0 := by
    simp only [FFactorial_ne_zero, ↓reduceIte]
    exact div_pos one_pos (FFactorial_pos 6)
  have h_rest_gt : (Finset.range 20 \ Finset.range 6).sum
      (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n) > 0 := by
    calc (Finset.range 20 \ Finset.range 6).sum
          (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n)
        ≥ (if FFactorial 6 = 0 then (0 : ℝ) else 1 / FFactorial 6) := Finset.single_le_sum
            (fun x hx => by
              simp only [Finset.mem_sdiff, Finset.mem_range] at hx
              exact h_tail_pos x (by simp; omega)) h6
      _ > 0 := h6_pos
  calc (Finset.range 20).sum (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n)
      = (Finset.range 6).sum (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n)
        + (Finset.range 20 \ Finset.range 6).sum
          (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n) := by
        rw [← Finset.sum_union (Finset.disjoint_sdiff)]; congr 1
    _ > 37/10 + 0 := by linarith [h_first6, h_rest_gt]
    _ = 37/10 := by ring

/-- Upper bound: frourioConst < 4 (crude bound using finite sum) -/
theorem frourioConst_upper_bound : frourioConst < 4 := by
  unfold frourioConst
  have h_tail_pos : ∀ x ∈ Finset.range 20,
      (if FFactorial x = 0 then (0 : ℝ) else 1 / FFactorial x) ≥ 0 := by
    intro x _
    split_ifs
    · exact le_refl 0
    · exact le_of_lt (div_pos one_pos (FFactorial_pos x))
  have h_sum_le : (Finset.range 20).sum
      (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n) ≤
      (Finset.range 7).sum (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n)
      + 13 * (1/240) := by
    have hf6 : FFactorial 6 = 240 := FFactorial_six
    have h_split : (Finset.range 20).sum
        (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n) =
        (Finset.range 7).sum (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n)
        + (Finset.range 20 \ Finset.range 7).sum
          (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n) := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff)]; congr 1
    rw [h_split]
    have h_card : (Finset.range 20 \ Finset.range 7).card = 13 := by
      rw [Finset.card_sdiff_of_subset (by simp : Finset.range 7 ⊆ Finset.range 20)]
      simp
    have h_tail_le : (Finset.range 20 \ Finset.range 7).sum
        (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n) ≤ 13 * (1/240) := by
      calc (Finset.range 20 \ Finset.range 7).sum
            (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n)
          ≤ (Finset.range 20 \ Finset.range 7).sum (fun _ => (1 : ℝ) / 240) := by
            apply Finset.sum_le_sum
            intro n hn
            simp only [Finset.mem_sdiff, Finset.mem_range, FFactorial_ne_zero, ↓reduceIte] at hn ⊢
            have hn_ge7 : n ≥ 7 := by omega
            have hf_ge : FFactorial n ≥ 240 := by
              have h6 : FFactorial 6 = 240 := FFactorial_six
              have hmono : FFactorial 6 ≤ FFactorial n := FFactorial_mono (by omega : 6 ≤ n)
              linarith
            exact one_div_le_one_div_of_le (by norm_num) hf_ge
        _ = 13 * (1/240) := by simp [h_card]
    linarith
  have h_first7 : (Finset.range 7).sum
      (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n) = 37/10 + 1/240 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
               FFactorial_ne_zero, ↓reduceIte, FFactorial_zero, FFactorial_one,
               FFactorial_two, FFactorial_three, FFactorial_four, FFactorial_five, FFactorial_six]
    norm_num
  calc (Finset.range 20).sum (fun n => if FFactorial n = 0 then 0 else 1 / FFactorial n)
      ≤ (37/10 + 1/240) + 13 * (1/240) := by linarith [h_sum_le, h_first7]
    _ = 37/10 + 14/240 := by ring
    _ < 4 := by norm_num

/-- The Frourio constant is approximately 3.7045 -/
theorem frourioConst_approx : 3.7 < frourioConst ∧ frourioConst < 4 := by
  constructor
  · have h := frourioConst_gt_37
    linarith
  · exact frourioConst_upper_bound

end FrourioExponential

section ComplexGolden

open Complex

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
private lemma phi_pow9_r : φ ^ 9 = 34 * φ + 21 := by
  nlinarith [golden_ratio_property, phi_cubed, phi_pow6_r]
private lemma psi_pow9_r : ψ ^ 9 = 34 * ψ + 21 := by
  nlinarith [psi_sq, psi_cubed_alt, psi_pow6_r]
private lemma phi_pow12_r : φ ^ 12 = 144 * φ + 89 := by
  nlinarith [golden_ratio_property, phi_pow4_r, phi_pow6_r, phi_pow8_r]
private lemma psi_pow12_r : ψ ^ 12 = 144 * ψ + 89 := by
  nlinarith [psi_sq, psi_pow4_r, psi_pow6_r, psi_pow8_r]

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
lemma phi_pow9_complex : (↑φ : ℂ) ^ 9 = 34 * ↑φ + 21 := by
  have := liftR phi_pow9_r; push_cast at this; exact this
lemma psi_pow9_complex : (↑ψ : ℂ) ^ 9 = 34 * ↑ψ + 21 := by
  have := liftR psi_pow9_r; push_cast at this; exact this
lemma phi_pow12_complex : (↑φ : ℂ) ^ 12 = 144 * ↑φ + 89 := by
  have := liftR phi_pow12_r; push_cast at this; exact this
lemma psi_pow12_complex : (↑ψ : ℂ) ^ 12 = 144 * ↑ψ + 89 := by
  have := liftR psi_pow12_r; push_cast at this; exact this

end ComplexGolden

/-! ## Golden Ratio Uniqueness — Why φ and not √2 or √3?

For a real quadratic unit α with Galois conjugate β, define D₅ and D₆ operators
at φ-power evaluation points. The operator coefficients are determined by
kernel conditions (D[1]=0, D[x]=0, D[x²]=0).

Theorem: Among all norm(-1) quadratic units (αβ = -1) with α > 1 > |β|,
φ = (1+√5)/2 is the UNIQUE one for which D₆ has integer coefficients.

Key identity: (s²+1)(s²+2) = (s²+s+2)(s²-s+2) - 2
where s = α + β ∈ ℤ.

D₆ coefficient A = (s²+1)(s²+2)/(s²-s+2), so A ∈ ℤ ⟺ (s²-s+2) | 2.
Since s²-s+2 ≥ 2 for all s ∈ ℤ with equality iff s ∈ {0,1}, and s=0 is
degenerate (α=1), the unique valid solution is s=1, giving α = φ. -/

section GoldenUniqueness

-- The key polynomial identity: (s²+1)(s²+2) = (s²+s+2)(s²-s+2) - 2
theorem golden_key_identity (s : ℤ) :
    (s^2 + 1) * (s^2 + 2) = (s^2 + s + 2) * (s^2 - s + 2) - 2 := by ring

-- D₆ coefficient A for a norm(-1) unit with trace s
noncomputable def D6_coeff_A (s : ℤ) : ℚ :=
  ((s^2 + 1) * (s^2 + 2) : ℤ) / (s^2 - s + 2 : ℤ)

-- s²-s+2 > 0 for all integers (it equals (2s-1)²/4 + 7/4 ≥ 7/4)
theorem trace_denom_pos (s : ℤ) : s ^ 2 - s + 2 > 0 := by nlinarith [sq_nonneg (2*s - 1)]

-- s²-s+2 ≥ 2 for all integers
theorem trace_denom_ge_two (s : ℤ) : s ^ 2 - s + 2 ≥ 2 := by nlinarith [sq_nonneg (s - 1)]

-- A is integral iff (s²-s+2) | 2
theorem D6_integral_iff_dvd (s : ℤ) :
    (s ^ 2 - s + 2 : ℤ) ∣ (s ^ 2 + 1) * (s ^ 2 + 2) ↔
    (s ^ 2 - s + 2 : ℤ) ∣ 2 := by
  have hid := golden_key_identity s
  have hpos : s ^ 2 - s + 2 > 0 := trace_denom_pos s
  constructor
  · intro ⟨k, hk⟩
    refine ⟨(s ^ 2 + s + 2) - k, ?_⟩
    nlinarith
  · intro ⟨k, hk⟩
    refine ⟨(s ^ 2 + s + 2) * 1 - k, ?_⟩
    nlinarith

-- The only integers s with (s²-s+2) | 2 are s = 0 and s = 1
theorem trace_dvd_two_solutions (s : ℤ) :
    (s ^ 2 - s + 2 : ℤ) ∣ 2 → s = 0 ∨ s = 1 := by
  intro ⟨k, hk⟩
  have hge : s ^ 2 - s + 2 ≥ 2 := trace_denom_ge_two s
  -- s²-s+2 ≥ 2 and (s²-s+2)*k = 2, so k ≥ 1 and s²-s+2 ≤ 2, i.e. s²-s+2 = 2
  have hk_pos : k > 0 := by nlinarith
  have hle : s ^ 2 - s + 2 ≤ 2 := by nlinarith
  have : s ^ 2 - s = 0 := by omega
  have : s * (s - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h <;> omega

-- s = 0 gives a degenerate unit: α² = 1, so α = ±1, not > 1
-- s = 1 gives x² - x - 1 = 0, which is the golden ratio equation
-- So φ is the unique non-degenerate solution.

-- The golden ratio is the unique root > 1 of x² - x - 1 = 0
-- (already known: golden_ratio_property : φ² = φ + 1)

-- Main theorem: φ is unique among norm(-1) quadratic units with integer D₆
theorem phi_unique_D6_integral (α β : ℝ)
    (hprod : α * β = -1)
    (hα_gt : α > 1)
    (hD6 : ∃ s : ℤ, α + β = s ∧ (s ^ 2 - s + 2 : ℤ) ∣ (s ^ 2 + 1) * (s ^ 2 + 2)) :
    α + β = 1 := by
  obtain ⟨s, hs, hdvd⟩ := hD6
  have h02 := (D6_integral_iff_dvd s).mp hdvd
  have h01 := trace_dvd_two_solutions s h02
  rcases h01 with rfl | rfl
  · -- s = 0: α + β = 0, αβ = -1 → α² = 1, contradicts α > 1
    exfalso
    push_cast at hs
    have hβ : β = -α := by linarith
    rw [hβ] at hprod
    have hsq : α ^ 2 = 1 := by nlinarith
    nlinarith [sq_nonneg (α - 1)]
  · -- s = 1: α + β = 1 ✓
    push_cast at hs; linarith

-- The trace s=1 with norm p=-1 gives the golden ratio equation
theorem trace_one_is_golden (α : ℝ) (hα_gt : α > 1) (hα_eq : α ^ 2 - α - 1 = 0) :
    α = φ := by
  have hφ : φ ^ 2 - φ - 1 = 0 := by have := golden_ratio_property; linarith
  have hdiff : α ^ 2 - φ ^ 2 - (α - φ) = 0 := by linarith
  have hfactor : (α - φ) * (α + φ - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · exfalso; nlinarith [phi_pos]

-- Combined: D₆ integrality + norm(-1) + α > 1 → α = φ
theorem phi_uniqueness (α β : ℝ)
    (hprod : α * β = -1) (hα_gt : α > 1)
    (hsum : ∃ s : ℤ, α + β = ↑s)
    (hD6_int : ∀ s : ℤ, α + β = ↑s →
      (s ^ 2 - s + 2 : ℤ) ∣ (s ^ 2 + 1) * (s ^ 2 + 2)) :
    α = φ := by
  obtain ⟨s, hs⟩ := hsum
  have hdvd := hD6_int s hs
  have h02 := (D6_integral_iff_dvd s).mp hdvd
  have h01 := trace_dvd_two_solutions s h02
  rcases h01 with rfl | rfl
  · -- s = 0: degenerate
    exfalso
    push_cast at hs
    have : β = -α := by linarith
    rw [this] at hprod
    have : α ^ 2 = 1 := by nlinarith
    have : α ≤ 1 := by nlinarith [sq_nonneg (α - 1)]
    linarith
  · -- s = 1: golden
    push_cast at hs
    have hβ : β = 1 - α := by linarith
    rw [hβ] at hprod
    have hα_eq : α ^ 2 - α - 1 = 0 := by nlinarith
    exact trace_one_is_golden α hα_gt hα_eq

end GoldenUniqueness

end FUST
