import FUST.DζOperator
import FUST.FrourioAlgebra.GoldenEisensteinInt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace FUST.FζOperator

open Complex FUST.DζOperator

/-! ## Rescaled symmetric operator: 5·Φ_S with ℤ[φ] coefficients -/

/-- 5·Φ_S: coefficients [10, 21-2φ, -50, 9+2φ, 10] ∈ ℤ[φ] -/
noncomputable def Φ_S_int (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  10 * f ((↑φ : ℂ) ^ 2 * z) + (21 - 2 * (↑φ : ℂ)) * f ((↑φ : ℂ) * z) -
  50 * f z + (9 + 2 * (↑φ : ℂ)) * f ((↑ψ : ℂ) * z) +
  10 * f ((↑ψ : ℂ) ^ 2 * z)

/-- Φ_S_int = 5 · Φ_S -/
theorem Φ_S_int_eq (f : ℂ → ℂ) (z : ℂ) : Φ_S_int f z = 5 * Φ_S f z := by
  simp only [Φ_S_int, Φ_S, Diff5, Diff3, Diff2]
  have hne := phi_plus_two_ne
  have hP : (↑φ : ℂ) * ↑φ - ↑φ - 1 = 0 := by
    have h := by
      have h := golden_ratio_property
      have : φ * φ = φ + 1 := by nlinarith [h]
      calc (↑φ : ℂ) * ↑φ = ↑(φ * φ) := by push_cast; ring
        _ = ↑(φ + 1) := congrArg _ this
        _ = ↑φ + 1 := by push_cast; ring
    linear_combination h
  set P := (↑φ : ℂ)
  set fφ2 := f (P ^ 2 * z)
  set fφ := f (P * z)
  set f0 := f z
  set fψ := f ((↑ψ : ℂ) * z)
  set fψ2 := f ((↑ψ : ℂ) ^ 2 * z)
  -- Goal: 10*fφ2 + (21-2P)*fφ - 50*f0 + (9+2P)*fψ + 10*fψ2
  --     = 5 * (2*fφ2 + (3 + 2/(P+2))*fφ - 10*f0 + (3 - 2/(P+2))*fψ + 2*fψ2)
  -- Suffices: (21-2P) = 5*(3+2/(P+2)) and (9+2P) = 5*(3-2/(P+2))
  suffices h3p : (21 - 2 * P) = 5 * (3 + 2 / (P + 2)) by
    suffices h3m : (9 + 2 * P) = 5 * (3 - 2 / (P + 2)) by
      rw [h3p, h3m]; ring
    field_simp; linear_combination (2 : ℂ) * hP
  field_simp; linear_combination (-2 : ℂ) * hP

/-! ## Integral Dζ: Fζ = AFNum(5·Φ_A) + SymNum(Φ_S_int) = 5z·Dζ -/

/-- Fζ: integral form, closed on ℤ[φ,ζ₆][z] -/
noncomputable def Fζ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  AFNum (fun w => 5 * Φ_A f w) z + SymNum (Φ_S_int f) z

/-- AFNum is linear: AFNum(c·g) = c · AFNum(g) -/
theorem AFNum_smul (g : ℂ → ℂ) (c : ℂ) (z : ℂ) :
    AFNum (fun w => c * g w) z = c * AFNum g z := by
  unfold AFNum; ring

/-- SymNum is linear: SymNum(c·g) = c · SymNum(g) -/
theorem SymNum_smul (g : ℂ → ℂ) (c : ℂ) (z : ℂ) :
    SymNum (fun w => c * g w) z = c * SymNum g z := by
  unfold SymNum; ring

/-- SymNum of rescaled: SymNum(5·g) = 5 · SymNum(g) -/
theorem SymNum_of_Φ_S_int (f : ℂ → ℂ) (z : ℂ) :
    SymNum (Φ_S_int f) z = 5 * SymNum (Φ_S f) z := by
  have h : Φ_S_int f = fun w => 5 * Φ_S f w := by
    funext w; exact Φ_S_int_eq f w
  rw [h]
  exact SymNum_smul (Φ_S f) 5 z

/-- Fζ = 5z · Dζ -/
theorem Fζ_eq (f : ℂ → ℂ) (z : ℂ) (hz : z ≠ 0) :
    Fζ f z = 5 * z * Dζ f z := by
  unfold Fζ Dζ
  rw [AFNum_smul (Φ_A f) 5 z, SymNum_of_Φ_S_int f z]
  field_simp

/-! ## Kernel: Fζ annihilates {1, z²} (but NOT z: Dζ(id) ≠ 0) -/

theorem Fζ_kernel_const (z : ℂ) : Fζ (fun _ => 1) z = 0 := by
  by_cases hz : z = 0
  · subst hz; unfold Fζ AFNum SymNum Φ_A Diff6 Diff2 Diff4 Φ_S_int; ring
  · rw [Fζ_eq (fun _ => 1) z hz, Dζ_const z]; ring

private lemma zeta6_pow8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
  have : ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
  rw [this, zeta6_pow_six, one_mul]

private lemma zeta6_pow10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
  have : ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
  rw [this, zeta6_pow_six, one_mul]

/-- AFNum kills any g(w) = c·w² -/
private theorem AFNum_kills_sq (g : ℂ → ℂ) (c : ℂ) (z : ℂ)
    (hg : ∀ w, g w = c * w ^ 2) : AFNum g z = 0 := by
  simp only [AFNum, hg]
  have : c * (ζ₆ * z) ^ 2 + c * (ζ₆ ^ 2 * z) ^ 2 -
    c * (ζ₆ ^ 4 * z) ^ 2 - c * (ζ₆ ^ 5 * z) ^ 2 =
    c * z ^ 2 * (ζ₆ ^ 2 + ζ₆ ^ 4 - ζ₆ ^ 8 - ζ₆ ^ 10) := by ring
  rw [this, zeta6_pow8, zeta6_pow10]; ring

/-- SymNum kills any g(w) = c·w² -/
private theorem SymNum_kills_sq (g : ℂ → ℂ) (c : ℂ) (z : ℂ)
    (hg : ∀ w, g w = c * w ^ 2) : SymNum g z = 0 := by
  simp only [SymNum, hg]
  have : 2 * (c * z ^ 2) + c * (ζ₆ * z) ^ 2 - c * (ζ₆ ^ 2 * z) ^ 2 -
    2 * (c * (ζ₆ ^ 3 * z) ^ 2) - c * (ζ₆ ^ 4 * z) ^ 2 +
    c * (ζ₆ ^ 5 * z) ^ 2 =
    c * z ^ 2 * (2 + ζ₆ ^ 2 - ζ₆ ^ 4 - 2 * ζ₆ ^ 6 - ζ₆ ^ 8 + ζ₆ ^ 10) := by ring
  rw [this, zeta6_pow_six, zeta6_pow8, zeta6_pow10]; ring

private lemma five_phiA_sq (w : ℂ) :
    5 * Φ_A (fun t => t ^ 2) w =
    (5 * ((↑φ : ℂ) ^ 6 - 4 * (↑φ : ℂ) ^ 4 + (3 + ↑φ) * (↑φ : ℂ) ^ 2 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 2 + 4 * (↑ψ : ℂ) ^ 4 - (↑ψ : ℂ) ^ 6)) * w ^ 2 := by
  simp only [Φ_A, Diff6, Diff2, Diff4]
  have hφ2 : (↑φ : ℂ) ^ 2 = ↑φ + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ) ^ 2 = ↑ψ + 1 := psi_sq_complex
  conv_lhs => rw [show (↑φ : ℂ) ^ 2 * ((↑φ : ℂ) * w) ^ 2 =
    ((↑φ : ℂ) + 1) * ((↑φ : ℂ) * w) ^ 2 from by rw [hφ2]]
  conv_lhs => rw [show (↑ψ : ℂ) ^ 2 * ((↑ψ : ℂ) * w) ^ 2 =
    ((↑ψ : ℂ) + 1) * ((↑ψ : ℂ) * w) ^ 2 from by rw [hψ2]]
  ring

private lemma phiS_int_sq (w : ℂ) :
    Φ_S_int (fun t => t ^ 2) w =
    (10 * (↑φ : ℂ) ^ 4 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 2 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 2 + 10 * (↑ψ : ℂ) ^ 4) * w ^ 2 := by
  unfold Φ_S_int; ring

/-- Fζ annihilates w² (ζ₆ squared-power cancellation in both channels) -/
theorem Fζ_kernel_quad (z : ℂ) : Fζ (fun w => w ^ 2) z = 0 := by
  unfold Fζ
  have hAF := AFNum_kills_sq (fun w => 5 * Φ_A (fun t => t ^ 2) w)
    (5 * ((↑φ : ℂ) ^ 6 - 4 * (↑φ : ℂ) ^ 4 + (3 + ↑φ) * (↑φ : ℂ) ^ 2 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 2 + 4 * (↑ψ : ℂ) ^ 4 - (↑ψ : ℂ) ^ 6))
    z (fun w => five_phiA_sq w)
  have hSY := SymNum_kills_sq (Φ_S_int (fun t => t ^ 2))
    (10 * (↑φ : ℂ) ^ 4 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 2 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 2 + 10 * (↑ψ : ℂ) ^ 4)
    z (fun w => phiS_int_sq w)
  rw [hAF, hSY]; ring

/-! ## Extended kernel: Fζ annihilates w³ and w⁴ (mod 6 vanishing)

Fζ(wⁿ) = 0 for all n with gcd(n,6) > 1. Both AFNum and SymNum kill
w^n when n ≡ 0,2,3,4 mod 6 via ζ₆ root-of-unity cancellation. -/

private lemma AFNum_kills_cube (g : ℂ → ℂ) (c : ℂ) (z : ℂ)
    (hg : ∀ w, g w = c * w ^ 3) : AFNum g z = 0 := by
  have h : g = fun w => c * w ^ 3 := funext hg
  rw [h, show (3 : ℕ) = 6 * 0 + 3 from by ring, AFNum_smul, AFNum_pow_mod6_3, mul_zero]

private lemma SymNum_kills_cube (g : ℂ → ℂ) (c : ℂ) (z : ℂ)
    (hg : ∀ w, g w = c * w ^ 3) : SymNum g z = 0 := by
  have h : g = fun w => c * w ^ 3 := funext hg
  rw [h, show (3 : ℕ) = 6 * 0 + 3 from by ring, SymNum_smul, SymNum_pow_mod6_3, mul_zero]

private lemma five_phiA_cube (w : ℂ) :
    5 * Φ_A (fun t => t ^ 3) w =
    (5 * ((↑φ : ℂ) ^ 9 - 4 * (↑φ : ℂ) ^ 6 + (3 + ↑φ) * (↑φ : ℂ) ^ 3 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 3 + 4 * (↑ψ : ℂ) ^ 6 - (↑ψ : ℂ) ^ 9)) * w ^ 3 := by
  simp only [Φ_A, Diff6, Diff2, Diff4]
  have hφ2 : (↑φ : ℂ) ^ 2 = ↑φ + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ) ^ 2 = ↑ψ + 1 := psi_sq_complex
  conv_lhs => rw [show (↑φ : ℂ) ^ 2 * ((↑φ : ℂ) * w) ^ 3 =
    ((↑φ : ℂ) + 1) * ((↑φ : ℂ) * w) ^ 3 from by rw [hφ2]]
  conv_lhs => rw [show (↑ψ : ℂ) ^ 2 * ((↑ψ : ℂ) * w) ^ 3 =
    ((↑ψ : ℂ) + 1) * ((↑ψ : ℂ) * w) ^ 3 from by rw [hψ2]]
  ring

private lemma phiS_int_cube (w : ℂ) :
    Φ_S_int (fun t => t ^ 3) w =
    (10 * (↑φ : ℂ) ^ 6 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 3 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 3 + 10 * (↑ψ : ℂ) ^ 6) * w ^ 3 := by
  unfold Φ_S_int; ring

/-- Fζ annihilates w³ (ζ₆³ = -1 cancellation in both channels) -/
theorem Fζ_kernel_cube (z : ℂ) : Fζ (fun w => w ^ 3) z = 0 := by
  unfold Fζ
  have hAF := AFNum_kills_cube (fun w => 5 * Φ_A (fun t => t ^ 3) w)
    (5 * ((↑φ : ℂ) ^ 9 - 4 * (↑φ : ℂ) ^ 6 + (3 + ↑φ) * (↑φ : ℂ) ^ 3 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 3 + 4 * (↑ψ : ℂ) ^ 6 - (↑ψ : ℂ) ^ 9))
    z (fun w => five_phiA_cube w)
  have hSY := SymNum_kills_cube (Φ_S_int (fun t => t ^ 3))
    (10 * (↑φ : ℂ) ^ 6 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 3 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 3 + 10 * (↑ψ : ℂ) ^ 6)
    z (fun w => phiS_int_cube w)
  rw [hAF, hSY]; ring

private lemma AFNum_kills_fourth (g : ℂ → ℂ) (c : ℂ) (z : ℂ)
    (hg : ∀ w, g w = c * w ^ 4) : AFNum g z = 0 := by
  have h : g = fun w => c * w ^ 4 := funext hg
  rw [h, show (4 : ℕ) = 6 * 0 + 4 from by ring, AFNum_smul, AFNum_pow_mod6_4, mul_zero]

private lemma SymNum_kills_fourth (g : ℂ → ℂ) (c : ℂ) (z : ℂ)
    (hg : ∀ w, g w = c * w ^ 4) : SymNum g z = 0 := by
  have h : g = fun w => c * w ^ 4 := funext hg
  rw [h, show (4 : ℕ) = 6 * 0 + 4 from by ring, SymNum_smul, SymNum_pow_mod6_4, mul_zero]

private lemma five_phiA_fourth (w : ℂ) :
    5 * Φ_A (fun t => t ^ 4) w =
    (5 * ((↑φ : ℂ) ^ 12 - 4 * (↑φ : ℂ) ^ 8 + (3 + ↑φ) * (↑φ : ℂ) ^ 4 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 4 + 4 * (↑ψ : ℂ) ^ 8 - (↑ψ : ℂ) ^ 12)) * w ^ 4 := by
  simp only [Φ_A, Diff6, Diff2, Diff4]
  have hφ2 : (↑φ : ℂ) ^ 2 = ↑φ + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ) ^ 2 = ↑ψ + 1 := psi_sq_complex
  conv_lhs => rw [show (↑φ : ℂ) ^ 2 * ((↑φ : ℂ) * w) ^ 4 =
    ((↑φ : ℂ) + 1) * ((↑φ : ℂ) * w) ^ 4 from by rw [hφ2]]
  conv_lhs => rw [show (↑ψ : ℂ) ^ 2 * ((↑ψ : ℂ) * w) ^ 4 =
    ((↑ψ : ℂ) + 1) * ((↑ψ : ℂ) * w) ^ 4 from by rw [hψ2]]
  ring

private lemma phiS_int_fourth (w : ℂ) :
    Φ_S_int (fun t => t ^ 4) w =
    (10 * (↑φ : ℂ) ^ 8 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 4 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 4 + 10 * (↑ψ : ℂ) ^ 8) * w ^ 4 := by
  unfold Φ_S_int; ring

/-- Fζ annihilates w⁴ (ζ₆⁴ = -ζ₆ cancellation in both channels) -/
theorem Fζ_kernel_fourth (z : ℂ) : Fζ (fun w => w ^ 4) z = 0 := by
  unfold Fζ
  have hAF := AFNum_kills_fourth (fun w => 5 * Φ_A (fun t => t ^ 4) w)
    (5 * ((↑φ : ℂ) ^ 12 - 4 * (↑φ : ℂ) ^ 8 + (3 + ↑φ) * (↑φ : ℂ) ^ 4 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 4 + 4 * (↑ψ : ℂ) ^ 8 - (↑ψ : ℂ) ^ 12))
    z (fun w => five_phiA_fourth w)
  have hSY := SymNum_kills_fourth (Φ_S_int (fun t => t ^ 4))
    (10 * (↑φ : ℂ) ^ 8 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 4 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 4 + 10 * (↑ψ : ℂ) ^ 8)
    z (fun w => phiS_int_fourth w)
  rw [hAF, hSY]; ring

/-! ## Translation equivariance: Fζ(f(c·))(z) = Fζ(f)(cz) -/

private lemma mul_comm_assoc' (c a z : ℂ) : c * (a * z) = a * (c * z) := by ring

theorem Fζ_translate (f : ℂ → ℂ) (c z : ℂ) :
    Fζ (fun t => f (c * t)) z = Fζ f (c * z) := by
  unfold Fζ
  -- Φ_A and Φ_S_int are translation-equivariant
  have hA : (fun w => 5 * Φ_A (fun t => f (c * t)) w) =
    (fun w => 5 * Φ_A f (c * w)) := by
    funext w; rw [Φ_A_translate f c w]
  have hS : Φ_S_int (fun t => f (c * t)) = fun w => Φ_S_int f (c * w) := by
    funext w; unfold Φ_S_int; simp only [mul_comm_assoc']
  rw [hA, hS]
  rw [AFNum_translate (fun w => 5 * Φ_A f w) c z]
  rw [SymNum_translate (Φ_S_int f) c z]

/-! ## General monomial factoring: Φ_A(wⁿ) and Φ_S_int(wⁿ) -/

/-- Φ_A factors on monomials: Φ_A(wⁿ)(z) = c_A(n) · zⁿ -/
theorem phiA_monomial (n : ℕ) (w : ℂ) :
    Φ_A (fun t => t ^ n) w =
    ((↑φ : ℂ) ^ (3 * n) - 4 * (↑φ : ℂ) ^ (2 * n) +
     (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ n -
     (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ n +
     4 * (↑ψ : ℂ) ^ (2 * n) - (↑ψ : ℂ) ^ (3 * n)) * w ^ n := by
  simp only [Φ_A, Diff6, Diff2, Diff4]
  have hφ2 : (↑φ : ℂ) ^ 2 = ↑φ + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ) ^ 2 = ↑ψ + 1 := psi_sq_complex
  conv_lhs => rw [show (↑φ : ℂ) ^ 2 * ((↑φ : ℂ) * w) ^ n =
    ((↑φ : ℂ) + 1) * ((↑φ : ℂ) * w) ^ n from by rw [hφ2]]
  conv_lhs => rw [show (↑ψ : ℂ) ^ 2 * ((↑ψ : ℂ) * w) ^ n =
    ((↑ψ : ℂ) + 1) * ((↑ψ : ℂ) * w) ^ n from by rw [hψ2]]
  ring

/-- Φ_S_int factors on monomials: Φ_S_int(wⁿ)(z) = c_S(n) · zⁿ -/
theorem phiS_int_monomial (n : ℕ) (w : ℂ) :
    Φ_S_int (fun t => t ^ n) w =
    (10 * (↑φ : ℂ) ^ (2 * n) +
     (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ n - 50 +
     (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ n +
     10 * (↑ψ : ℂ) ^ (2 * n)) * w ^ n := by
  unfold Φ_S_int; ring

/-! ## Eigenvalue formula for n ≡ 1 mod 6

Fζ(w^{6k+1})(z) = (5·c_A·AF_coeff + 6·c_S) · z^{6k+1} -/

/-- Fζ on w^{6k+1}: explicit eigenvalue formula -/
theorem Fζ_eigenvalue_mod6_1 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k + 1)) z =
    (5 * ((↑φ : ℂ) ^ (3 * (6 * k + 1)) -
      4 * (↑φ : ℂ) ^ (2 * (6 * k + 1)) +
      (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 1) -
      (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 1) +
      4 * (↑ψ : ℂ) ^ (2 * (6 * k + 1)) -
      (↑ψ : ℂ) ^ (3 * (6 * k + 1))) * AF_coeff +
     6 * (10 * (↑φ : ℂ) ^ (2 * (6 * k + 1)) +
      (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 1) - 50 +
      (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 1) +
      10 * (↑ψ : ℂ) ^ (2 * (6 * k + 1)))) *
    z ^ (6 * k + 1) := by
  unfold Fζ
  -- Factor out Φ_A and Φ_S_int as monomials
  have hA : (fun w => 5 * Φ_A (fun t => t ^ (6 * k + 1)) w) =
      fun w => (5 * ((↑φ : ℂ) ^ (3 * (6 * k + 1)) -
        4 * (↑φ : ℂ) ^ (2 * (6 * k + 1)) +
        (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 1) -
        (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 1) +
        4 * (↑ψ : ℂ) ^ (2 * (6 * k + 1)) -
        (↑ψ : ℂ) ^ (3 * (6 * k + 1)))) *
      w ^ (6 * k + 1) := by
    funext w; rw [phiA_monomial]; ring
  have hS : Φ_S_int (fun t => t ^ (6 * k + 1)) =
      fun w => (10 * (↑φ : ℂ) ^ (2 * (6 * k + 1)) +
        (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 1) - 50 +
        (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 1) +
        10 * (↑ψ : ℂ) ^ (2 * (6 * k + 1))) *
      w ^ (6 * k + 1) := by
    funext w; rw [phiS_int_monomial]
  rw [hA, hS, AFNum_smul, AFNum_pow_mod6_1,
      SymNum_smul, SymNum_pow_mod6_1]; ring

/-- Fζ on w^{6k+5}: eigenvalue with negated AF_coeff -/
theorem Fζ_eigenvalue_mod6_5 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k + 5)) z =
    (-5 * ((↑φ : ℂ) ^ (3 * (6 * k + 5)) -
      4 * (↑φ : ℂ) ^ (2 * (6 * k + 5)) +
      (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 5) -
      (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 5) +
      4 * (↑ψ : ℂ) ^ (2 * (6 * k + 5)) -
      (↑ψ : ℂ) ^ (3 * (6 * k + 5))) * AF_coeff +
     6 * (10 * (↑φ : ℂ) ^ (2 * (6 * k + 5)) +
      (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 5) - 50 +
      (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 5) +
      10 * (↑ψ : ℂ) ^ (2 * (6 * k + 5)))) *
    z ^ (6 * k + 5) := by
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => t ^ (6 * k + 5)) w) =
      fun w => (5 * ((↑φ : ℂ) ^ (3 * (6 * k + 5)) -
        4 * (↑φ : ℂ) ^ (2 * (6 * k + 5)) +
        (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 5) -
        (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 5) +
        4 * (↑ψ : ℂ) ^ (2 * (6 * k + 5)) -
        (↑ψ : ℂ) ^ (3 * (6 * k + 5)))) *
      w ^ (6 * k + 5) := by
    funext w; rw [phiA_monomial]; ring
  have hS : Φ_S_int (fun t => t ^ (6 * k + 5)) =
      fun w => (10 * (↑φ : ℂ) ^ (2 * (6 * k + 5)) +
        (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 5) - 50 +
        (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 5) +
        10 * (↑ψ : ℂ) ^ (2 * (6 * k + 5))) *
      w ^ (6 * k + 5) := by
    funext w; rw [phiS_int_monomial]
  rw [hA, hS, AFNum_smul, AFNum_pow_mod6_5,
      SymNum_smul, SymNum_pow_mod6_5]; ring

/-! ## General mod 6 vanishing: Fζ(z^n) = 0 when gcd(n,6) > 1 -/

theorem Fζ_vanish_mod6_0 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k)) z = 0 := by
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => t ^ (6 * k)) w) =
      fun w => (5 * ((↑φ : ℂ) ^ (3 * (6 * k)) -
        4 * (↑φ : ℂ) ^ (2 * (6 * k)) +
        (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k) -
        (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * k) +
        4 * (↑ψ : ℂ) ^ (2 * (6 * k)) -
        (↑ψ : ℂ) ^ (3 * (6 * k)))) * w ^ (6 * k) := by
    funext w; rw [phiA_monomial]; ring
  have hS : Φ_S_int (fun t => t ^ (6 * k)) =
      fun w => (10 * (↑φ : ℂ) ^ (2 * (6 * k)) +
        (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k) - 50 +
        (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * k) +
        10 * (↑ψ : ℂ) ^ (2 * (6 * k))) * w ^ (6 * k) := by
    funext w; rw [phiS_int_monomial]
  rw [hA, hS, AFNum_smul, AFNum_pow_mod6_0, SymNum_smul, SymNum_pow_mod6_0]
  ring

theorem Fζ_vanish_mod6_2 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k + 2)) z = 0 := by
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => t ^ (6 * k + 2)) w) =
      fun w => (5 * ((↑φ : ℂ) ^ (3 * (6 * k + 2)) -
        4 * (↑φ : ℂ) ^ (2 * (6 * k + 2)) +
        (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 2) -
        (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 2) +
        4 * (↑ψ : ℂ) ^ (2 * (6 * k + 2)) -
        (↑ψ : ℂ) ^ (3 * (6 * k + 2)))) * w ^ (6 * k + 2) := by
    funext w; rw [phiA_monomial]; ring
  have hS : Φ_S_int (fun t => t ^ (6 * k + 2)) =
      fun w => (10 * (↑φ : ℂ) ^ (2 * (6 * k + 2)) +
        (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 2) - 50 +
        (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 2) +
        10 * (↑ψ : ℂ) ^ (2 * (6 * k + 2))) * w ^ (6 * k + 2) := by
    funext w; rw [phiS_int_monomial]
  rw [hA, hS, AFNum_smul, AFNum_pow_mod6_2, SymNum_smul, SymNum_pow_mod6_2]
  ring

theorem Fζ_vanish_mod6_3 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k + 3)) z = 0 := by
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => t ^ (6 * k + 3)) w) =
      fun w => (5 * ((↑φ : ℂ) ^ (3 * (6 * k + 3)) -
        4 * (↑φ : ℂ) ^ (2 * (6 * k + 3)) +
        (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 3) -
        (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 3) +
        4 * (↑ψ : ℂ) ^ (2 * (6 * k + 3)) -
        (↑ψ : ℂ) ^ (3 * (6 * k + 3)))) * w ^ (6 * k + 3) := by
    funext w; rw [phiA_monomial]; ring
  have hS : Φ_S_int (fun t => t ^ (6 * k + 3)) =
      fun w => (10 * (↑φ : ℂ) ^ (2 * (6 * k + 3)) +
        (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 3) - 50 +
        (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 3) +
        10 * (↑ψ : ℂ) ^ (2 * (6 * k + 3))) * w ^ (6 * k + 3) := by
    funext w; rw [phiS_int_monomial]
  rw [hA, hS, AFNum_smul, AFNum_pow_mod6_3, SymNum_smul, SymNum_pow_mod6_3]
  ring

theorem Fζ_vanish_mod6_4 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k + 4)) z = 0 := by
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => t ^ (6 * k + 4)) w) =
      fun w => (5 * ((↑φ : ℂ) ^ (3 * (6 * k + 4)) -
        4 * (↑φ : ℂ) ^ (2 * (6 * k + 4)) +
        (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 4) -
        (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 4) +
        4 * (↑ψ : ℂ) ^ (2 * (6 * k + 4)) -
        (↑ψ : ℂ) ^ (3 * (6 * k + 4)))) * w ^ (6 * k + 4) := by
    funext w; rw [phiA_monomial]; ring
  have hS : Φ_S_int (fun t => t ^ (6 * k + 4)) =
      fun w => (10 * (↑φ : ℂ) ^ (2 * (6 * k + 4)) +
        (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * k + 4) - 50 +
        (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * k + 4) +
        10 * (↑ψ : ℂ) ^ (2 * (6 * k + 4))) * w ^ (6 * k + 4) := by
    funext w; rw [phiS_int_monomial]
  rw [hA, hS, AFNum_smul, AFNum_pow_mod6_4, SymNum_smul, SymNum_pow_mod6_4]
  ring

/-! ## Derivation defect: Fζ(fg) - f·Fζ(g) - Fζ(f)·g

The derivation defect of any linear operator L is the unique bilinear form
δ_L(f,g) = L(fg) - f·L(g) - L(f)·g. This is not an arbitrary definition:
it is the standard obstruction to L being a derivation. -/

/-- Derivation defect of Fζ evaluated at z -/
noncomputable def derivDefect (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  Fζ (fun w => f w * g w) z - f z * Fζ g z - Fζ f z * g z

/-- On monomials: δ(zᵃ,zᵇ) = Fζ(z^{a+b}) - zᵃ·Fζ(zᵇ) - Fζ(zᵃ)·zᵇ -/
theorem derivDefect_monomial (a b : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ a) (fun w => w ^ b) z =
    Fζ (fun w => w ^ (a + b)) z -
    z ^ a * Fζ (fun w => w ^ b) z -
    Fζ (fun w => w ^ a) z * z ^ b := by
  unfold derivDefect
  have h : (fun w : ℂ => w ^ a * w ^ b) = (fun w => w ^ (a + b)) := by
    funext w; rw [pow_add]
  rw [h]

/-! ## Emergence: ker × ker → active

When gcd(a,6)>1 and gcd(b,6)>1 but gcd(a+b,6)=1,
the defect equals the full eigenvalue: δ(zᵃ,zᵇ) = Fζ(z^{a+b}). -/

/-- z³·z⁴ → z⁷: both in ker, product is active -/
theorem emergence_3_4 (z : ℂ) :
    derivDefect (fun w => w ^ 3) (fun w => w ^ 4) z =
    Fζ (fun w => w ^ 7) z := by
  rw [derivDefect_monomial,
    show (3 + 4 : ℕ) = 7 from by ring,
    show (3 : ℕ) = 6 * 0 + 3 from by ring, Fζ_vanish_mod6_3 0,
    show (4 : ℕ) = 6 * 0 + 4 from by ring, Fζ_vanish_mod6_4 0]
  ring

/-! ## Fζ is ℂ-linear in the function argument -/

theorem Fζ_const_smul (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    Fζ (fun w => c * f w) z = c * Fζ f z := by
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => c * f t) w) =
      fun w => c * (5 * Φ_A f w) := by
    funext w; simp only [Φ_A, Diff6, Diff2, Diff4]; ring
  have hS : Φ_S_int (fun t => c * f t) = fun w => c * Φ_S_int f w := by
    funext w; unfold Φ_S_int; ring
  rw [hA, hS, AFNum_smul, SymNum_smul]; ring

/-! ## Gauge invariance: δ(c·f, c⁻¹·g) = δ(f, g) for constant c ∈ ℂ×

This follows from Fζ's ℂ-linearity and c·c⁻¹ = 1. -/

theorem derivDefect_const_gauge (c : ℂ) (hc : c ≠ 0) (f g : ℂ → ℂ) (z : ℂ) :
    derivDefect (fun w => c * f w) (fun w => c⁻¹ * g w) z =
    derivDefect f g z := by
  unfold derivDefect
  have hfg : (fun w : ℂ => c * f w * (c⁻¹ * g w)) = (fun w => f w * g w) := by
    funext w; field_simp
  rw [hfg, Fζ_const_smul, Fζ_const_smul]; ring_nf; field_simp

/-! ## GEI decomposition of eigenvalue

The eigenvalue 5·c_A·AF_coeff + 6·c_S decomposes as a+bφ+cζ₆+dφζ₆.
Using AF_coeff = 4ζ₆-2 and grouping: the AF channel contributes to ζ₆
components while the SY channel contributes to the φ components. -/

/-- √5 = 2φ - 1 in ℂ (from φ = (1+√5)/2) -/
private theorem sqrt5_eq_two_phi_sub_one :
    (↑(Real.sqrt 5) : ℂ) = 2 * (↑φ : ℂ) - 1 := by
  simp only [φ]; push_cast; ring

/-- Eigenvalue decomposes on {1,φ,ζ₆,φζ₆} basis.
  cA: Φ_A coefficient / √5, cS_rat: rational part, cS_irr: √5 part. -/
private theorem eigenvalue_gei_decomp (cA cS_rat cS_irr : ℂ) :
    5 * (2 * (↑φ : ℂ) - 1) * cA * (4 * ζ₆ - 2) +
    6 * (cS_rat + (6 - 2 * (↑φ : ℂ)) * cS_irr) =
    (10 * cA + 6 * cS_rat + 36 * cS_irr) +
    (-20 * cA - 12 * cS_irr) * (↑φ : ℂ) +
    (-20 * cA) * ζ₆ +
    (40 * cA) * (↑φ : ℂ) * ζ₆ := by
  ring

/-! ## General emergence: δ(ker, ker) = Fζ at active sum

For ANY kernel pair whose sum is active, the derivation defect equals
the full Fζ eigenvalue. The two emergence channels are:
- mod 3 + mod 4 → mod 1 (matter)
- mod 2 + mod 3 → mod 5 (antimatter) -/

/-- General matter emergence: δ(z^{6j+3}, z^{6k+4}) = Fζ(z^{6(j+k)+7}) -/
theorem emergence_matter (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 3)) (fun w => w ^ (6 * k + 4)) z =
    Fζ (fun w => w ^ (6 * j + 3 + (6 * k + 4))) z := by
  rw [derivDefect_monomial, Fζ_vanish_mod6_3, Fζ_vanish_mod6_4]
  ring

/-- General antimatter emergence: δ(z^{6j+2}, z^{6k+3}) = Fζ(z^{6(j+k)+5}) -/
theorem emergence_antimatter (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 2)) (fun w => w ^ (6 * k + 3)) z =
    Fζ (fun w => w ^ (6 * j + 2 + (6 * k + 3))) z := by
  rw [derivDefect_monomial, Fζ_vanish_mod6_2, Fζ_vanish_mod6_3]
  ring

/-- Emergence norm identity: |δ(ker,ker)(z)|² = |Fζ(z^{a+b})(z)|²
    Combined with eigenvalue evaluation, this gives |δ|² = tauNormSq. -/
theorem emergence_normSq_matter (j k : ℕ) (z : ℂ) :
    Complex.normSq (derivDefect (fun w => w ^ (6 * j + 3)) (fun w => w ^ (6 * k + 4)) z) =
    Complex.normSq (Fζ (fun w => w ^ (6 * j + 3 + (6 * k + 4))) z) := by
  rw [emergence_matter]

theorem emergence_normSq_antimatter (j k : ℕ) (z : ℂ) :
    Complex.normSq (derivDefect (fun w => w ^ (6 * j + 2)) (fun w => w ^ (6 * k + 3)) z) =
    Complex.normSq (Fζ (fun w => w ^ (6 * j + 2 + (6 * k + 3))) z) := by
  rw [emergence_antimatter]

/-! ## τ-symmetry: charge conjugation from AF_coeff² = -12

The Galois involution τ: ζ₆ → 1-ζ₆ sends AF_coeff → -AF_coeff.
For eigenvalues λ = ε·5c_A·AF + 6c_S, τ flips the AF sign.
The key algebraic fact AF² = -12 makes the τ-norm positive definite. -/

/-- AF_coeff² = -12: the key identity for τ-norm -/
theorem AF_coeff_sq : AF_coeff ^ 2 = -12 := by
  rw [AF_coeff_eq, sq]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.neg_re]; ring_nf; simp; norm_num
  · simp only [Complex.mul_im, Complex.neg_im]; ring_nf; simp

/-- τ-trace: (c_A·AF + c_S) + (-c_A·AF + c_S) = 2c_S -/
theorem tau_trace (c_A c_S : ℂ) :
    (c_A * AF_coeff + c_S) + (-c_A * AF_coeff + c_S) = 2 * c_S := by ring

/-- Eigenvalue τ-trace on Fζ: mod1 + mod5 eigenvalues cancel AF channel.
    For any c_A, c_S, the sum of (5c_A·AF + 6c_S) and (-5c_A·AF + 6c_S) = 12c_S. -/
theorem eigenvalue_tau_trace (c_A c_S : ℂ) :
    (5 * c_A * AF_coeff + 6 * c_S) + (-5 * c_A * AF_coeff + 6 * c_S) =
    12 * c_S := by ring

/-- Eigenvalue τ-norm on Fζ: product uses AF²=-12.
    (5c_A·AF + 6c_S)·(-5c_A·AF + 6c_S) = 36c_S² + 300c_A². -/
theorem eigenvalue_tau_norm (c_A c_S : ℂ) :
    (5 * c_A * AF_coeff + 6 * c_S) * (-5 * c_A * AF_coeff + 6 * c_S) =
    36 * c_S ^ 2 + 300 * c_A ^ 2 := by
  have h := AF_coeff_sq
  calc (5 * c_A * AF_coeff + 6 * c_S) * (-5 * c_A * AF_coeff + 6 * c_S)
      = 36 * c_S ^ 2 - 25 * c_A ^ 2 * AF_coeff ^ 2 := by ring
    _ = 36 * c_S ^ 2 - 25 * c_A ^ 2 * (-12) := by rw [h]
    _ = 36 * c_S ^ 2 + 300 * c_A ^ 2 := by ring


/-! ## Hermitian/anti-Hermitian structure of AFNum and SymNum

For any function g satisfying Schwarz reflection g(conj z) = conj(g z),
AFNum is anti-Hermitian and SymNum is Hermitian under complex conjugation.
This gives the algebraic origin of spacetime: AF = space, SY = time.

Key identities: ζ₆⁵ = ζ₆' = conj(ζ₆), ζ₆⁴ = conj(ζ₆²), ζ₆³ = -1. -/

private lemma zeta6'_eq_pow5 : ζ₆' = ζ₆ ^ 5 := by
  have h1 := zeta6_add_conj
  have : ζ₆' = 1 - ζ₆ := by linear_combination h1
  rw [this]
  have h5 : ζ₆ ^ 5 = ζ₆ ^ 3 * ζ₆ ^ 2 := by ring
  rw [h5, zeta6_cubed, zeta6_sq]; ring

private lemma conj_zeta6_eq : starRingEnd ℂ ζ₆ = ζ₆ ^ 5 := by
  rw [← zeta6'_eq_starRingEnd, zeta6'_eq_pow5]

private lemma z6_5_2 : (ζ₆ ^ 5) ^ 2 = ζ₆ ^ 4 := by
  have : (ζ₆ ^ 5) ^ 2 = (ζ₆ ^ 6) * ζ₆ ^ 4 := by ring
  rw [this, zeta6_pow_six, one_mul]

private lemma z6_5_3 : (ζ₆ ^ 5) ^ 3 = ζ₆ ^ 3 := by
  have : (ζ₆ ^ 5) ^ 3 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 3 := by ring
  rw [this, zeta6_pow_six]; ring

private lemma z6_5_4 : (ζ₆ ^ 5) ^ 4 = ζ₆ ^ 2 := by
  have : (ζ₆ ^ 5) ^ 4 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
  rw [this, zeta6_pow_six]; ring

private lemma z6_5_5 : (ζ₆ ^ 5) ^ 5 = ζ₆ := by
  have : (ζ₆ ^ 5) ^ 5 = (ζ₆ ^ 6) ^ 4 * ζ₆ := by ring
  rw [this, zeta6_pow_six]; ring

/-- AFNum is anti-Hermitian: AFNum(g)(s̄) = -conj(AFNum(g)(s))
    when g satisfies Schwarz reflection g(z̄) = conj(g(z)). -/
theorem AFNum_anti_hermitian (g : ℂ → ℂ)
    (hg : ∀ z, g (starRingEnd ℂ z) = starRingEnd ℂ (g z)) (s : ℂ) :
    AFNum g (starRingEnd ℂ s) = -(starRingEnd ℂ (AFNum g s)) := by
  unfold AFNum
  simp only [map_add, map_sub]
  rw [← hg (ζ₆ * s), ← hg (ζ₆ ^ 2 * s), ← hg (ζ₆ ^ 4 * s), ← hg (ζ₆ ^ 5 * s)]
  simp only [map_mul, map_pow, conj_zeta6_eq]
  rw [z6_5_2, z6_5_4, z6_5_5]
  ring

/-- SymNum is Hermitian: SymNum(g)(s̄) = conj(SymNum(g)(s))
    when g satisfies Schwarz reflection g(z̄) = conj(g(z)). -/
theorem SymNum_hermitian (g : ℂ → ℂ)
    (hg : ∀ z, g (starRingEnd ℂ z) = starRingEnd ℂ (g z)) (s : ℂ) :
    SymNum g (starRingEnd ℂ s) = starRingEnd ℂ (SymNum g s) := by
  unfold SymNum
  simp only [map_add, map_sub, map_mul, map_ofNat]
  rw [← hg s, ← hg (ζ₆ * s), ← hg (ζ₆ ^ 2 * s), ← hg (ζ₆ ^ 3 * s),
      ← hg (ζ₆ ^ 4 * s), ← hg (ζ₆ ^ 5 * s)]
  simp only [map_mul, map_pow, conj_zeta6_eq]
  rw [z6_5_2, z6_5_3, z6_5_4, z6_5_5]
  ring

/-- For real s, AFNum is pure imaginary: Re(AFNum(g)(s)) = 0 -/
theorem AFNum_real_pure_im (g : ℂ → ℂ)
    (hg : ∀ z, g (starRingEnd ℂ z) = starRingEnd ℂ (g z))
    (s : ℝ) : (AFNum g (↑s)).re = 0 := by
  have h := AFNum_anti_hermitian g hg (↑s : ℂ)
  simp only [Complex.conj_ofReal] at h
  set w := AFNum g ↑s with hw_def
  have hw : w = -(starRingEnd ℂ w) := h
  have : w.re = (-(starRingEnd ℂ w)).re := congrArg Complex.re hw
  simp [Complex.neg_re, Complex.conj_re] at this
  linarith

/-- For real s, SymNum is real: Im(SymNum(g)(s)) = 0 -/
theorem SymNum_real_pure_re (g : ℂ → ℂ)
    (hg : ∀ z, g (starRingEnd ℂ z) = starRingEnd ℂ (g z))
    (s : ℝ) : (SymNum g (↑s)).im = 0 := by
  have h := SymNum_hermitian g hg (↑s : ℂ)
  simp only [Complex.conj_ofReal] at h
  set w := SymNum g ↑s with hw_def
  have hw : w = starRingEnd ℂ w := h
  have : w.im = (starRingEnd ℂ w).im := congrArg Complex.im hw
  simp [Complex.conj_im] at this
  linarith

/-! ## Spacetime √15 factorization: AF channel is pure imaginary, SY is real -/

private lemma sqrt15_eq : Real.sqrt 15 = Real.sqrt 5 * Real.sqrt 3 := by
  rw [show (15 : ℝ) = 5 * 3 from by norm_num,
      Real.sqrt_mul (by norm_num : (5:ℝ) ≥ 0)]

/-- Re(5·(√5·A)·AF_coeff) = 0: AF channel is pure imaginary -/
theorem AF_channel_pure_im (A : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * A) * AF_coeff).re = 0 := by
  rw [AF_coeff_eq]; simp only [Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,
    show (5:ℂ).re = 5 from by simp, show (5:ℂ).im = 0 from by simp]; ring

/-- Im(5·(√5·A)·AF_coeff) = 10√15·A: space channel proportional to √15 -/
theorem AF_channel_im (A : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * A) * AF_coeff).im = 10 * Real.sqrt 15 * A := by
  rw [AF_coeff_eq, sqrt15_eq]; simp only [Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    show (5:ℂ).re = 5 from by simp, show (5:ℂ).im = 0 from by simp]; ring

/-- Im(λ) = 10√15·A_n: eigenvalue space channel -/
theorem eigenvalue_im_eq_sqrt15 (c_A c_S : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S).im =
    10 * Real.sqrt 15 * c_A := by
  rw [Complex.add_im, show (6 * ↑c_S : ℂ).im = 0 from by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
               show (6:ℂ).re = 6 from by simp, show (6:ℂ).im = 0 from by simp]; ring,
    add_zero]
  exact AF_channel_im c_A

/-- Re(λ) = 6·c_S: eigenvalue time channel -/
theorem eigenvalue_re_eq_phiS (c_A c_S : ℝ) :
    ((5 : ℂ) * ↑(Real.sqrt 5 * c_A) * AF_coeff + 6 * ↑c_S).re =
    6 * c_S := by
  rw [AF_coeff_eq]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
             Complex.ofReal_re, Complex.ofReal_im,
             show (5:ℂ).re = 5 from by simp, show (5:ℂ).im = 0 from by simp,
             show (6:ℂ).re = 6 from by simp, show (6:ℂ).im = 0 from by simp]
  ring

end FUST.FζOperator
