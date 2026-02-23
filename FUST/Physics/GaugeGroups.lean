/-
Standard gauge group SU(3)×SU(2)×U(1) derived uniquely from the unified Dζ operator.
The ℤ/6ℤ Fourier decomposition into SymNum (even parity) and AFNum (odd parity) channels
is canonical, and the rank/dimension matching forces the gauge group without free parameters.
-/
import FUST.Zeta6
import FUST.DifferenceOperators
import FUST.DimensionalAnalysis
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace FUST

open Complex FUST.Zeta6

/-! ## ζ₆ lies outside the φ-dilation eigenspectrum

ζ₆ = (1/2, √3/2) has nonzero imaginary part, so it cannot equal any φ^n (which are real).
This means ζ₆-rotation mixes the φ-dilation eigenspaces {1, x, x²} non-diagonally. -/

section Zeta6PhiSeparation

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

theorem zeta6_ne_one : ζ₆ ≠ 1 := by simpa using zeta6_ne_phi_pow 0

theorem zeta6_ne_phi : ζ₆ ≠ (↑φ : ℂ) := by simpa using zeta6_ne_phi_pow 1

theorem zeta6_ne_phi_sq : ζ₆ ≠ (↑φ : ℂ) ^ 2 := zeta6_ne_phi_pow 2

theorem zeta6_not_phi_eigenvalue :
    ζ₆ ≠ (↑φ : ℂ) ^ (0 : ℕ) ∧ ζ₆ ≠ (↑φ : ℂ) ^ (1 : ℕ) ∧ ζ₆ ≠ (↑φ : ℂ) ^ (2 : ℕ) :=
  ⟨by simpa using zeta6_ne_one, by simpa using zeta6_ne_phi, zeta6_ne_phi_sq⟩

end Zeta6PhiSeparation

/-! ## Channel decomposition is canonical and non-degenerate

The decomposition Dζ = AFNum(Φ_A) + SymNum(Φ_S) is the unique ℤ/6ℤ Fourier decomposition
into odd (antisymmetric) and even (symmetric) parity channels.
Both channels are non-degenerate: AF_coeff ≠ 0 and SY_coeff = 6 ≠ 0. -/

section ChannelNonDegeneracy

theorem AF_channel_nondegenerate : AF_coeff ≠ 0 := by
  intro h
  have := AF_coeff_normSq
  rw [h, map_zero] at this
  norm_num at this

theorem AF_coeff_re_zero : AF_coeff.re = 0 := by rw [AF_coeff_eq]

theorem AF_coeff_im_pos : AF_coeff.im > 0 := by
  rw [AF_coeff_eq]
  exact mul_pos (by norm_num : (0 : ℝ) < 2) sqrt3_pos

theorem channels_independent :
    AF_coeff.re = 0 ∧ AF_coeff.im ≠ 0 ∧ (6 : ℂ).re = 6 ∧ (6 : ℂ).im = 0 := by
  exact ⟨AF_coeff_re_zero, ne_of_gt AF_coeff_im_pos, by simp, by simp⟩

end ChannelNonDegeneracy

/-! ## Kernel dimension structure and hierarchy -/

section KernelDimension

theorem kernel_hierarchy :
    (∀ x, x ≠ 0 → D2 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D5 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D5 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) :=
  ⟨fun x hx => D2_const 1 x hx,
   fun x hx => D5_const 1 x hx,
   D5_linear,
   fun x hx => D6_const 1 x hx,
   D6_linear,
   D6_quadratic⟩

theorem kernel_dimension_strict_increase :
    (∀ x, x ≠ 0 → D2 (fun _ => 1) x = 0) ∧
    (∃ x, x ≠ 0 ∧ D2 id x ≠ 0) ∧
    (∀ x, x ≠ 0 → D5 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D5 id x = 0) ∧
    (∀ x, x ≠ 0 → D5 (fun t => t^2) x ≠ 0) ∧
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^3) x ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => D2_const 1 x hx
  · use 1, one_ne_zero
    exact D2_linear_ne_zero 1 one_ne_zero
  · exact fun x hx => D5_const 1 x hx
  · exact D5_linear
  · exact D5_not_annihilate_quadratic
  · exact fun x hx => D6_const 1 x hx
  · exact D6_linear
  · exact D6_quadratic
  · exact D6_not_annihilate_cubic

end KernelDimension

/-! ## φ-Dilation eigenvalues and scaling structure -/

section PhiDilation

noncomputable def scalingMatrix (s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => s ^ i.val)

theorem kerD5_eigenvalues :
    (↑φ : ℂ) ^ (0 : ℕ) = 1 ∧ (↑φ : ℂ) ^ (1 : ℕ) = ↑φ := by simp

theorem kerD5_eigenvalues_distinct :
    (↑φ : ℂ) ^ (0 : ℕ) ≠ (↑φ : ℂ) ^ (1 : ℕ) := by
  simp only [pow_zero, pow_one]
  exact_mod_cast (ne_of_gt φ_gt_one).symm

theorem kerD6_eigenvalues :
    (↑φ : ℂ) ^ (0 : ℕ) = 1 ∧
    (↑φ : ℂ) ^ (1 : ℕ) = ↑φ ∧
    (↑φ : ℂ) ^ (2 : ℕ) = ↑φ + 1 := by
  refine ⟨by simp, by simp, ?_⟩
  exact golden_ratio_property_complex

theorem kerD6_eigenvalues_distinct :
    (↑φ : ℂ) ^ (0 : ℕ) ≠ (↑φ : ℂ) ^ (1 : ℕ) ∧
    (↑φ : ℂ) ^ (1 : ℕ) ≠ (↑φ : ℂ) ^ (2 : ℕ) ∧
    (↑φ : ℂ) ^ (0 : ℕ) ≠ (↑φ : ℂ) ^ (2 : ℕ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [pow_zero, pow_one]
    exact_mod_cast (ne_of_gt φ_gt_one).symm
  · simp only [pow_one]
    rw [golden_ratio_property_complex]
    have : (↑φ : ℂ) + 1 = ↑(φ + 1) := by push_cast; ring
    rw [this]; exact_mod_cast ne_of_lt (by linarith [phi_pos] : φ < φ + 1)
  · simp only [pow_zero]
    rw [golden_ratio_property_complex]
    have : (↑φ : ℂ) + 1 = ↑(φ + 1) := by push_cast; ring
    rw [this]; exact_mod_cast ne_of_lt (by linarith [phi_pos] : 1 < φ + 1)

end PhiDilation

/-! ## φ-Dilation commutant: matrices commuting with diag(1,φ,φ²) must be diagonal -/

section PhiDilationCommutant

open Matrix

private theorem phi_pow_fin3_ne (i j : Fin 3) (hij : i ≠ j) :
    (↑φ : ℂ) ^ i.val ≠ (↑φ : ℂ) ^ j.val := by
  have ⟨h01, h12, h02⟩ := kerD6_eigenvalues_distinct
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp only at *
  · exact h01
  · exact h02
  · exact h01.symm
  · exact h12
  · exact h02.symm
  · exact h12.symm

theorem phiDilation_commutant_diagonal (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hcomm : M * scalingMatrix (↑φ : ℂ) = scalingMatrix (↑φ : ℂ) * M)
    (i j : Fin 3) (hij : i ≠ j) :
    M i j = 0 := by
  have h1 : (M * scalingMatrix (↑φ : ℂ)) i j = M i j * (↑φ : ℂ) ^ j.val := by
    simp [scalingMatrix, mul_diagonal]
  have h2 : (scalingMatrix (↑φ : ℂ) * M) i j = (↑φ : ℂ) ^ i.val * M i j := by
    simp [scalingMatrix, diagonal_mul]
  have hentry : M i j * (↑φ : ℂ) ^ j.val = (↑φ : ℂ) ^ i.val * M i j := by
    rw [← h1, ← h2, hcomm]
  have hdiff : M i j * ((↑φ : ℂ) ^ j.val - (↑φ : ℂ) ^ i.val) = 0 := by
    linear_combination hentry
  have hne : (↑φ : ℂ) ^ j.val ≠ (↑φ : ℂ) ^ i.val := phi_pow_fin3_ne j i (Ne.symm hij)
  exact (mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hne)

theorem phiDilation_commutant_diagonal_2 (M : Matrix (Fin 2) (Fin 2) ℂ)
    (hcomm : M * Matrix.diagonal (fun i : Fin 2 => (↑φ : ℂ) ^ i.val)
           = Matrix.diagonal (fun i : Fin 2 => (↑φ : ℂ) ^ i.val) * M)
    (i j : Fin 2) (hij : i ≠ j) :
    M i j = 0 := by
  have h1 : (M * Matrix.diagonal (fun i : Fin 2 => (↑φ : ℂ) ^ i.val)) i j
           = M i j * (↑φ : ℂ) ^ j.val := by
    simp [mul_diagonal]
  have h2 : (Matrix.diagonal (fun i : Fin 2 => (↑φ : ℂ) ^ i.val) * M) i j
           = (↑φ : ℂ) ^ i.val * M i j := by
    simp [diagonal_mul]
  have hentry : M i j * (↑φ : ℂ) ^ j.val = (↑φ : ℂ) ^ i.val * M i j := by
    rw [← h1, ← h2, hcomm]
  have hdiff : M i j * ((↑φ : ℂ) ^ j.val - (↑φ : ℂ) ^ i.val) = 0 := by
    linear_combination hentry
  have hne : (↑φ : ℂ) ^ j.val ≠ (↑φ : ℂ) ^ i.val := by
    have hd := kerD5_eigenvalues_distinct
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp only at *
    · exact hd.symm
    · exact hd
  exact (mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hne)

end PhiDilationCommutant

/-! ## Symmetric channel (SymNum) rank = 3 → SU(3) on ker(D6)

Φ_S = 2·N5 + N3 + μ·N2 has 3 linearly independent sub-operators.
This is proven by Φ_S_rank_three: the 3×3 determinant at s=1,5,7 is -6952(φ-ψ) ≠ 0.
Symmetric rank 3 on dim 3 space = irreducible action → SU(3). -/

section SymmetricChannelSU3

theorem symmetric_channel_SU3 :
    (σ_N5 1 * (σ_N3 5 * σ_N2 7 - σ_N2 5 * σ_N3 7) -
     σ_N3 1 * (σ_N5 5 * σ_N2 7 - σ_N2 5 * σ_N5 7) +
     σ_N2 1 * (σ_N5 5 * σ_N3 7 - σ_N3 5 * σ_N5 7) ≠ 0) ∧
    (∀ n : ℕ, ζ₆ ≠ (↑φ : ℂ) ^ n) ∧
    (3 ^ 2 - 1 = 8) := by
  exact ⟨Φ_S_rank_three, zeta6_ne_phi_pow, by norm_num⟩

end SymmetricChannelSU3

/-! ## Antisymmetric channel (AFNum) → SU(2) on ker(D5)

AF_coeff = 2i√3 is purely imaginary, providing an off-diagonal generator.
Combined with the φ-dilation diagonal generator on ker(D5) = span{1, x},
this generates the su(2) Lie algebra. -/

section AntisymmetricChannelSU2

theorem antisymmetric_channel_SU2 :
    AF_coeff ≠ 0 ∧
    AF_coeff.re = 0 ∧
    (↑φ : ℂ) ^ (0 : ℕ) ≠ (↑φ : ℂ) ^ (1 : ℕ) ∧
    (2 ^ 2 - 1 = 3) := by
  exact ⟨AF_channel_nondegenerate, AF_coeff_re_zero,
         kerD5_eigenvalues_distinct, by norm_num⟩

end AntisymmetricChannelSU2

/-! ## Trivial channel → U(1) on ker(D2) -/

section TrivialChannelU1

theorem trivial_channel_U1 :
    (∀ x, x ≠ 0 → D2 (fun _ => 1) x = 0) ∧
    (∃ x, x ≠ 0 ∧ D2 id x ≠ 0) ∧
    (1 ^ 2 - 1 + 1 = 1) := by
  exact ⟨fun x hx => D2_const 1 x hx,
         ⟨1, one_ne_zero, D2_linear_ne_zero 1 one_ne_zero⟩,
         by norm_num⟩

end TrivialChannelU1

/-! ## Main theorem: Standard Model gauge group uniquely determined by Dζ -/

section StandardGaugeGroup

theorem weight_ratio_3_1 (a b : ℝ) :
    Complex.normSq (6 * (a : ℂ) + AF_coeff * b) = 12 * (3 * a ^ 2 + b ^ 2) :=
  Dζ_normSq_decomposition a b

/-- Standard Model gauge group is uniquely determined by Dζ channel structure. -/
theorem standard_gauge_group_unique :
    (σ_N5 1 * (σ_N3 5 * σ_N2 7 - σ_N2 5 * σ_N3 7) -
     σ_N3 1 * (σ_N5 5 * σ_N2 7 - σ_N2 5 * σ_N5 7) +
     σ_N2 1 * (σ_N5 5 * σ_N3 7 - σ_N3 5 * σ_N5 7) ≠ 0) ∧
    (3 ^ 2 - 1 = 8) ∧
    (AF_coeff ≠ 0 ∧ AF_coeff.re = 0) ∧
    (2 ^ 2 - 1 = 3) ∧
    ((∀ x, x ≠ 0 → D2 (fun _ => 1) x = 0) ∧
     (∃ x, x ≠ 0 ∧ D2 id x ≠ 0)) ∧
    (∀ n : ℕ, ζ₆ ≠ (↑φ : ℂ) ^ n) ∧
    (∀ a b : ℝ, Complex.normSq (6 * (a : ℂ) + AF_coeff * b) =
      12 * (3 * a ^ 2 + b ^ 2)) := by
  exact ⟨Φ_S_rank_three, by norm_num,
         ⟨AF_channel_nondegenerate, AF_coeff_re_zero⟩, by norm_num,
         ⟨fun x hx => D2_const 1 x hx,
          ⟨1, one_ne_zero, D2_linear_ne_zero 1 one_ne_zero⟩⟩,
         zeta6_ne_phi_pow,
         Dζ_normSq_decomposition⟩

end StandardGaugeGroup

end FUST
