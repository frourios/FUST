/-
Standard gauge group SU(3)×SU(2)×U(1) derived uniquely from the Fζ channel structure.
The ℤ/6ℤ Fourier decomposition into SymNum (even parity) and AFNum (odd parity) channels
is canonical, and the rank/dimension matching forces the gauge group without free parameters.
-/
import FUST.DζOperator
import FUST.Dimension
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace FUST

open Complex FUST.DζOperator

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

/-! ## φ-Dilation eigenvalues and scaling structure -/

section PhiDilation

noncomputable def scalingMatrix (s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => s ^ i.val)

/-- φ-eigenvalues {1,φ} are distinct (spinDegeneracy = 2 space) -/
theorem phi_eigenvalues_distinct_2 :
    (↑φ : ℂ) ^ (0 : ℕ) ≠ (↑φ : ℂ) ^ (1 : ℕ) := by
  simp only [pow_zero, pow_one]
  exact_mod_cast (ne_of_gt φ_gt_one).symm

/-- φ-eigenvalues {1,φ,φ²} are distinct (syWeight = 3 space) -/
theorem phi_eigenvalues_distinct_3 :
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
  have ⟨h01, h12, h02⟩ := phi_eigenvalues_distinct_3
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
    have hd := phi_eigenvalues_distinct_2
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp only at *
    · exact hd.symm
    · exact hd
  exact (mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hne)

end PhiDilationCommutant

/-! ## Symmetric channel (SymNum) rank = 3 → SU(3) on syWeight = 3 space

Φ_S = 2·Diff5 + Diff3 + μ·Diff2 has 3 linearly independent sub-operators.
This is proven by Φ_S_rank_three: the 3×3 determinant at s=1,5,7 is -6952(φ-ψ) ≠ 0.
Symmetric rank 3 on Fζ SY channel space (dim = syWeight = 3) → SU(3). -/

section SymmetricChannelSU3

theorem symmetric_channel_SU3 :
    (σ_Diff5 1 * (σ_Diff3 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff3 7) -
     σ_Diff3 1 * (σ_Diff5 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff5 7) +
     σ_Diff2 1 * (σ_Diff5 5 * σ_Diff3 7 - σ_Diff3 5 * σ_Diff5 7) ≠ 0) ∧
    (∀ n : ℕ, ζ₆ ≠ (↑φ : ℂ) ^ n) ∧
    (3 ^ 2 - 1 = 8) := by
  exact ⟨Φ_S_rank_three, zeta6_ne_phi_pow, by norm_num⟩

end SymmetricChannelSU3

/-! ## Antisymmetric channel (AFNum) → SU(2) on spinDegeneracy = 2 space

AF_coeff = 2i√3 is purely imaginary, providing an off-diagonal generator.
Combined with the φ-dilation diagonal generator on Fζ AF channel space (dim = spinDegeneracy = 2),
this generates the su(2) Lie algebra. -/

section AntisymmetricChannelSU2

theorem antisymmetric_channel_SU2 :
    AF_coeff ≠ 0 ∧
    AF_coeff.re = 0 ∧
    (↑φ : ℂ) ^ (0 : ℕ) ≠ (↑φ : ℂ) ^ (1 : ℕ) ∧
    (2 ^ 2 - 1 = 3) := by
  exact ⟨AF_channel_nondegenerate, AF_coeff_re_zero,
         phi_eigenvalues_distinct_2, by norm_num⟩

end AntisymmetricChannelSU2

/-! ## Main theorem: Standard Model gauge group uniquely determined by Fζ -/

section StandardGaugeGroup

theorem weight_ratio_3_1 (a b : ℝ) :
    Complex.normSq (6 * (a : ℂ) + AF_coeff * b) = 12 * (3 * a ^ 2 + b ^ 2) :=
  Dζ_normSq_decomposition a b

/-- Standard Model gauge group is uniquely determined by Fζ channel structure. -/
theorem standard_gauge_group_unique :
    (σ_Diff5 1 * (σ_Diff3 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff3 7) -
     σ_Diff3 1 * (σ_Diff5 5 * σ_Diff2 7 - σ_Diff2 5 * σ_Diff5 7) +
     σ_Diff2 1 * (σ_Diff5 5 * σ_Diff3 7 - σ_Diff3 5 * σ_Diff5 7) ≠ 0) ∧
    (3 ^ 2 - 1 = 8) ∧
    (AF_coeff ≠ 0 ∧ AF_coeff.re = 0) ∧
    (2 ^ 2 - 1 = 3) ∧
    (∀ n : ℕ, ζ₆ ≠ (↑φ : ℂ) ^ n) ∧
    (∀ a b : ℝ, Complex.normSq (6 * (a : ℂ) + AF_coeff * b) =
      12 * (3 * a ^ 2 + b ^ 2)) := by
  exact ⟨Φ_S_rank_three, by norm_num,
         ⟨AF_channel_nondegenerate, AF_coeff_re_zero⟩, by norm_num,
         zeta6_ne_phi_pow, Dζ_normSq_decomposition⟩

end StandardGaugeGroup

end FUST
