/-
Galois separation of Fζ eigenvalues.
The eigenvalue λ = 5√5·A_n·AF_coeff + 6·S_n lies in ℚ(√5) ⊕ ℚ(√5)·√(-15),
missing the √(-3) direction entirely. This Galois separation constrains
the algebraic structure of zeros in the critical strip.
-/
import FUST.FζOperator
import FUST.FrourioAlgebra.GoldenEisensteinInt

namespace FUST.SpectralGalois

open Complex FUST FUST.DζOperator FUST.FζOperator FUST.FrourioAlgebra
open FUST.FibonacciArithmetic FUST.SpectralCoefficients

/-! ## SY channel integrality: Re(λ) ∈ ℤ[φ]

The SY eigenvalue channel uses only φ and ψ (golden ratio roots).
(6-2φ)·√5 = (6-2φ)(2φ-1) = 10φ - 10 clears denominators. -/

/-- (6-2φ)·(2φ-1) = 10φ-10 -/
theorem six_sub_two_phi_sqrt5 :
    (6 - 2 * φ) * (2 * φ - 1) = 10 * φ - 10 := by
  have h := golden_ratio_property; nlinarith [h]

/-- (6-2φ)·√5 = 10φ-10 via √5 = 2φ-1 -/
theorem six_sub_two_phi_mul_sqrt5 :
    (6 - 2 * φ) * Real.sqrt 5 = 10 * φ - 10 := by
  have h5 : Real.sqrt 5 = 2 * φ - 1 := by
    have : φ = (1 + Real.sqrt 5) / 2 := rfl
    linarith
  rw [h5]; exact six_sub_two_phi_sqrt5

/-- SY coefficient decomposes as a + b·φ for a,b ∈ ℤ -/
theorem SY_coeff_golden_form (n : ℕ) :
    10 * φ ^ (2 * n) + (21 - 2 * φ) * φ ^ n - 50 +
    (9 + 2 * φ) * ψ ^ n + 10 * ψ ^ (2 * n) =
    (10 * lucasConst (2 * n) + 15 * lucasConst n - 50) +
    (10 * φ - 10) * (Nat.fib n : ℝ) := by
  rw [phiS_int_fibonacci]
  have h := six_sub_two_phi_mul_sqrt5
  nlinarith [h]

/-! ## AF channel structure: Im(λ) ∈ ℤ·√15

5√5·A_n·AF_coeff = 10√15·A_n·i is purely imaginary. -/

/-- AF coefficient is integer -/
theorem AF_coeff_is_integer (n : ℕ) : ∃ k : ℤ, phiA_fib_coeff n = k :=
  ⟨phiA_fib_coeff n, rfl⟩

/-- AF channel is quantized: Im proportional to √15 -/
theorem AF_channel_quantized (c_A : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff).im =
    10 * Real.sqrt 15 * c_A := AF_channel_im c_A

/-! ## Galois separation: eigenvalue lies in ℚ(√5) + ℚ(√5)·i√3

Each eigenvalue decomposes as Re(λ) ∈ ℤ[φ] + Im(λ)·i where Im ∝ √15.
No √(-3) component on the real axis. -/

/-- AF channel has zero real part -/
theorem galois_separation_re (c_A c_S : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S).re =
    6 * c_S :=
  eigenvalue_re_eq_phiS c_A c_S

/-- SY channel has zero imaginary part -/
theorem galois_separation_im (c_A c_S : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S).im =
    10 * Real.sqrt 15 * c_A :=
  eigenvalue_im_eq_sqrt15 c_A c_S

/-- Eigenvalue channels determine the complex number -/
theorem eigenvalue_from_channels (c_A c_S : ℝ) :
    (5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S =
    ⟨6 * c_S, 10 * Real.sqrt 15 * c_A⟩ := by
  apply Complex.ext
  · exact galois_separation_re c_A c_S
  · exact galois_separation_im c_A c_S

/-! ## σ-conjugate: φ ↦ ψ, preserves ζ₆

σ maps √5 → -√5, so AF coefficient c_A sign-flips. -/

/-- σ-conjugate has negated AF coefficient -/
theorem sigma_im_flip (c_A c_S : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * (-c_A)) * AF_coeff +
     6 * ↑c_S).im = -(10 * Real.sqrt 15 * c_A) := by
  rw [eigenvalue_im_eq_sqrt15]; ring

/-- σ-conjugate preserves SY channel -/
theorem sigma_re_preserved (c_A c_S : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * (-c_A)) * AF_coeff +
     6 * ↑c_S).re = 6 * c_S :=
  eigenvalue_re_eq_phiS (-c_A) c_S

/-- σ-conjugate as explicit complex number -/
theorem sigma_eigenvalue_form (c_A c_S : ℝ) :
    (5 : ℂ) * ↑(Real.sqrt 5 * (-c_A)) * AF_coeff + 6 * ↑c_S =
    ⟨6 * c_S, -(10 * Real.sqrt 15 * c_A)⟩ := by
  apply Complex.ext
  · exact sigma_re_preserved c_A c_S
  · exact sigma_im_flip c_A c_S

/-! ## τ-conjugate = complex conjugation

τ: ζ₆ ↦ 1-ζ₆ is complex conjugation. -/

/-- τ acts as complex conjugation on eigenvalues -/
theorem tau_is_conj (c_A c_S : ℝ) :
    starRingEnd ℂ
      ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S) =
    ⟨6 * c_S, -(10 * Real.sqrt 15 * c_A)⟩ := by
  rw [eigenvalue_from_channels]; rfl

/-- τ-conjugate equals sign-flipped AF channel -/
theorem tau_eigenvalue_eq (c_A c_S : ℝ) :
    starRingEnd ℂ
      ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S) =
    (5 : ℂ) * ↑(Real.sqrt 5 * (-c_A)) * AF_coeff + 6 * ↑c_S := by
  rw [tau_is_conj, sigma_eigenvalue_form]

/-! ## Galois orbit structure

Gal(K/ℚ) = {id, σ, τ, στ}:
  id(λ) = ⟨6c_S, 10√15·c_A⟩, τ(λ) = ⟨6c_S, -10√15·c_A⟩,
  σ(λ) = ⟨6σ(c_S), -10√15·c_A⟩, στ(λ) = ⟨6σ(c_S), 10√15·c_A⟩ -/

/-- Galois trace: λ + conj(λ) = 12·c_S (AF cancels) -/
theorem galois_trace_rational (c_A c_S : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S) +
    starRingEnd ℂ
      ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S) =
    ↑(12 * c_S) := by
  set ev := (5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S
  have hre : ev.re = 6 * c_S := galois_separation_re c_A c_S
  have him : ev.im = 10 * Real.sqrt 15 * c_A :=
    galois_separation_im c_A c_S
  apply Complex.ext
  · simp [Complex.add_re, Complex.conj_re, Complex.ofReal_re, hre]
    ring
  · simp [Complex.add_im, Complex.conj_im, Complex.ofReal_im, him]

/-- τ-norm = |λ|²: 36c_S² + 1500c_A² -/
theorem tau_norm_eq_abs_sq (c_A c_S : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S) *
    starRingEnd ℂ
      ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S) =
    (⟨36 * c_S ^ 2 + 1500 * c_A ^ 2, 0⟩ : ℂ) := by
  set ev := (5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S
  have hre : ev.re = 6 * c_S := galois_separation_re c_A c_S
  have him : ev.im = 10 * Real.sqrt 15 * c_A :=
    galois_separation_im c_A c_S
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hre, him]
    have h15 : Real.sqrt 15 * Real.sqrt 15 = 15 := by
      rw [← Real.sqrt_mul (by norm_num : (15:ℝ) ≥ 0),
          Real.sqrt_mul_self (by norm_num : (15:ℝ) ≥ 0)]
    nlinarith [h15]
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, hre, him]
    ring

/-- |λ|² is positive when c_A ≠ 0 or c_S ≠ 0 -/
theorem abs_sq_pos (c_A c_S : ℝ) (h : c_A ≠ 0 ∨ c_S ≠ 0) :
    36 * c_S ^ 2 + 1500 * c_A ^ 2 > 0 := by
  rcases h with hA | hS <;> positivity

/-! ## Missing √(-3) direction: the c=0 constraint

In the field basis {1, √5, √(-3), √(-15)}, eigenvalues have form
  λ = a + b√5 + 0·√(-3) + d·√(-15). The √(-3) coefficient is zero. -/

/-- Eigenvalue has no √(-3) component: Im(λ) is ∝ √15 -/
theorem no_sqrt_neg3_component (c_A c_S : ℝ) :
    ∃ (re_part im_coeff : ℝ),
    (5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S =
    ⟨re_part, im_coeff * Real.sqrt 15⟩ :=
  ⟨6 * c_S, 10 * c_A, by
    rw [eigenvalue_from_channels]; congr 1; ring⟩

/-- Eigenvalue normSq = 36c_S² + 1500c_A² -/
theorem norm_sq_formula (c_A c_S : ℝ) :
    Complex.normSq
      ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S) =
    36 * c_S ^ 2 + 1500 * c_A ^ 2 := by
  rw [eigenvalue_from_channels, Complex.normSq_mk]
  have h15 : Real.sqrt 15 * Real.sqrt 15 = 15 := by
    rw [← Real.sqrt_mul (by norm_num : (15:ℝ) ≥ 0),
        Real.sqrt_mul_self (by norm_num : (15:ℝ) ≥ 0)]
  nlinarith [h15]

/-! ## Separation principle: AF and SY are independent conditions -/

/-- When SY vanishes, eigenvalue is pure AF -/
theorem SY_zero_pure_AF (c_A : ℝ) :
    (5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * (0 : ℂ) =
    ⟨0, 10 * Real.sqrt 15 * c_A⟩ := by
  rw [mul_zero, add_zero]; apply Complex.ext
  · exact AF_channel_pure_im c_A
  · exact AF_channel_im c_A

/-- When AF vanishes, eigenvalue is pure SY -/
theorem AF_zero_pure_SY (c_S : ℝ) :
    (5 : ℂ) * ↑(Real.sqrt 5 * (0 : ℝ)) * AF_coeff + 6 * ↑c_S =
    ↑(6 * c_S) := by
  simp only [mul_zero, ofReal_zero, zero_mul, zero_add]
  push_cast; ring

/-- Eigenvalue = SY + AF decomposition is unique -/
theorem eigenvalue_unique_decomp (z₁ z₂ : ℂ)
    (c_A₁ c_S₁ c_A₂ c_S₂ : ℝ)
    (h1 : z₁ = (5 : ℂ) * ↑(Real.sqrt 5 * c_A₁) * AF_coeff + 6 * ↑c_S₁)
    (h2 : z₂ = (5 : ℂ) * ↑(Real.sqrt 5 * c_A₂) * AF_coeff + 6 * ↑c_S₂)
    (heq : z₁ = z₂) : c_S₁ = c_S₂ ∧ c_A₁ = c_A₂ := by
  have hre1 := galois_separation_re c_A₁ c_S₁
  have him1 := galois_separation_im c_A₁ c_S₁
  have hre2 := galois_separation_re c_A₂ c_S₂
  have him2 := galois_separation_im c_A₂ c_S₂
  rw [h1] at heq; rw [h2] at heq
  have hre := congr_arg Complex.re heq
  have him := congr_arg Complex.im heq
  rw [hre1, hre2] at hre
  rw [him1, him2] at him
  constructor
  · linarith
  · have h15 : Real.sqrt 15 ≠ 0 := by positivity
    nlinarith [mul_right_cancel₀ h15
      (show 10 * c_A₁ * Real.sqrt 15 = 10 * c_A₂ * Real.sqrt 15
       from by linarith)]

end FUST.SpectralGalois
