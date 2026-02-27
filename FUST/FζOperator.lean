/-
Fζ = 5z·Dζ: rescaled unified operator closed on ℤ[φ,ζ₆][z].
Clearing the 1/5 denominator from Φ_S makes all coefficients integral.
-/
import FUST.DζOperator
import FUST.FrourioAlgebra.GoldenEisensteinInt
import FUST.FibonacciArithmetic

namespace FUST.FζOperator

open Complex FUST.DζOperator FUST.FibonacciArithmetic FUST.SpectralCoefficients

/-! ## Rescaled symmetric operator: 5·Φ_S with ℤ[φ] coefficients -/

/-- 5·Φ_S: coefficients [10, 21-2φ, -50, 9+2φ, 10] ∈ ℤ[φ] -/
noncomputable def Φ_S_int (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  10 * f ((↑φ : ℂ) ^ 2 * z) + (21 - 2 * (↑φ : ℂ)) * f ((↑φ : ℂ) * z) -
  50 * f z + (9 + 2 * (↑φ : ℂ)) * f ((↑ψ : ℂ) * z) +
  10 * f ((↑ψ : ℂ) ^ 2 * z)

private lemma phi_plus_two_ne : (↑φ : ℂ) + 2 ≠ 0 := by
  rw [ne_eq, ← ofReal_ofNat, ← ofReal_add, ofReal_eq_zero]
  linarith [phi_pos]

private lemma phi_mul_phi_c : (↑φ : ℂ) * ↑φ = ↑φ + 1 := by
  have h := golden_ratio_property
  have : φ * φ = φ + 1 := by nlinarith [h]
  calc (↑φ : ℂ) * ↑φ = ↑(φ * φ) := by push_cast; ring
    _ = ↑(φ + 1) := congrArg _ this
    _ = ↑φ + 1 := by push_cast; ring

/-- Φ_S_int = 5 · Φ_S -/
theorem Φ_S_int_eq (f : ℂ → ℂ) (z : ℂ) : Φ_S_int f z = 5 * Φ_S f z := by
  simp only [Φ_S_int, Φ_S, Diff5, Diff3, Diff2]
  have hne := phi_plus_two_ne
  have hP : (↑φ : ℂ) * ↑φ - ↑φ - 1 = 0 := by
    have h := phi_mul_phi_c; linear_combination h
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
private theorem AFNum_smul (g : ℂ → ℂ) (c : ℂ) (z : ℂ) :
    AFNum (fun w => c * g w) z = c * AFNum g z := by
  unfold AFNum; ring

/-- SymNum is linear: SymNum(c·g) = c · SymNum(g) -/
private theorem SymNum_smul (g : ℂ → ℂ) (c : ℂ) (z : ℂ) :
    SymNum (fun w => c * g w) z = c * SymNum g z := by
  unfold SymNum; ring

/-- SymNum of rescaled: SymNum(5·g) = 5 · SymNum(g) -/
private theorem SymNum_of_Φ_S_int (f : ℂ → ℂ) (z : ℂ) :
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
  · subst hz; unfold Fζ AFNum SymNum Φ_A Φ_S_int; ring
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
  unfold Φ_A; ring

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
  unfold Φ_A; ring

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
  unfold Φ_A; ring

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

/-! ## Spectral scaling: Fζ(zⁿ) = 5z · Dζ(zⁿ) -/

theorem Fζ_spectral (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    Fζ (fun w => w ^ n) z = 5 * z * Dζ (fun w => w ^ n) z :=
  Fζ_eq (fun w => w ^ n) z hz

/-! ## Monomial closure: mod 6 structure

For n ≡ 1 (mod 6): Fζ(zⁿ) has coefficient in ℤ[φ,ζ₆]
The AF channel contributes AF_coeff = 4ζ₆-2 ∈ ℤ[ζ₆]
The SY channel contributes 6 ∈ ℤ -/

/-- For n = 6k+1, AFNum factor on the Φ_A channel yields AF_coeff · z^n -/
theorem Fζ_monomial_mod6_1 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 1)) z = z ^ (6 * k + 1) * AF_coeff :=
  AFNum_pow_mod6_1 k z

/-- For n = 6k+5, AFNum yields -AF_coeff · z^n -/
theorem Fζ_monomial_mod6_5 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 5)) z = -(z ^ (6 * k + 5) * AF_coeff) :=
  AFNum_pow_mod6_5 k z

/-- For n = 6k+1, SymNum yields 6 · z^n -/
theorem Fζ_sym_mod6_1 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 1)) z = 6 * z ^ (6 * k + 1) :=
  SymNum_pow_mod6_1 k z

/-- For n = 6k+5, SymNum yields 6 · z^n -/
theorem Fζ_sym_mod6_5 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 5)) z = 6 * z ^ (6 * k + 5) :=
  SymNum_pow_mod6_5 k z

/-! ## General monomial factoring: Φ_A(wⁿ) and Φ_S_int(wⁿ) -/

/-- Φ_A factors on monomials: Φ_A(wⁿ)(z) = c_A(n) · zⁿ -/
theorem phiA_monomial (n : ℕ) (w : ℂ) :
    Φ_A (fun t => t ^ n) w =
    ((↑φ : ℂ) ^ (3 * n) - 4 * (↑φ : ℂ) ^ (2 * n) +
     (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ n -
     (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ n +
     4 * (↑ψ : ℂ) ^ (2 * n) - (↑ψ : ℂ) ^ (3 * n)) * w ^ n := by
  unfold Φ_A; ring

/-- Φ_S_int factors on monomials: Φ_S_int(wⁿ)(z) = c_S(n) · zⁿ -/
theorem phiS_int_monomial (n : ℕ) (w : ℂ) :
    Φ_S_int (fun t => t ^ n) w =
    (10 * (↑φ : ℂ) ^ (2 * n) +
     (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ n - 50 +
     (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ n +
     10 * (↑ψ : ℂ) ^ (2 * n)) * w ^ n := by
  unfold Φ_S_int; ring

/-! ## Fibonacci explicit formulas for Φ_A and Φ_S_int coefficients

Φ_A(wⁿ)(z) = √5·(F_{3n}-4F_{2n}+3F_n+F_{n+1})·zⁿ
Φ_S_int(wⁿ)(z) = (10L_{2n}+15L_n-5F_n-50+5√5F_n)·zⁿ -/

/-- Φ_A monomial coefficient: A_n = F_{3n} - 4F_{2n} + 3F_n + F_{n+1} -/
def phiA_fib_coeff (n : ℕ) : ℤ :=
  Nat.fib (3 * n) - 4 * Nat.fib (2 * n) + 3 * Nat.fib n + Nat.fib (n + 1)

/-- Φ_A(wⁿ) coefficient equals √5 · A_n (ℝ version) -/
theorem phiA_coeff_real (n : ℕ) :
    φ ^ (3 * n) - 4 * φ ^ (2 * n) + (3 + φ) * φ ^ n -
    (3 + ψ) * ψ ^ n + 4 * ψ ^ (2 * n) - ψ ^ (3 * n) =
    Real.sqrt 5 * (phiA_fib_coeff n : ℝ) := by
  simp only [phiA_fib_coeff]
  have h3n := phi_sub_psi_eq_sqrt5_fib (3 * n)
  have h2n := phi_sub_psi_eq_sqrt5_fib (2 * n)
  have hn := phi_sub_psi_eq_sqrt5_fib n
  have hn1 := phi_sub_psi_eq_sqrt5_fib (n + 1)
  have hsqrt5 : Real.sqrt 5 ≠ 0 := by positivity
  -- LHS = (φ^{3n}-ψ^{3n}) - 4(φ^{2n}-ψ^{2n}) + 3(φⁿ-ψⁿ) + (φ^{n+1}-ψ^{n+1})
  have key : φ ^ (3 * n) - 4 * φ ^ (2 * n) + (3 + φ) * φ ^ n -
      (3 + ψ) * ψ ^ n + 4 * ψ ^ (2 * n) - ψ ^ (3 * n) =
      (φ ^ (3 * n) - ψ ^ (3 * n)) - 4 * (φ ^ (2 * n) - ψ ^ (2 * n)) +
      3 * (φ ^ n - ψ ^ n) + (φ ^ (n + 1) - ψ ^ (n + 1)) := by ring
  rw [key, h3n, h2n, hn, hn1]; push_cast; ring

/-- Φ_S_int = 10L_{2n} + 15L_n + (6-2φ)(φⁿ-ψⁿ) - 50 -/
theorem phiS_int_coeff_real (n : ℕ) :
    10 * φ ^ (2 * n) + (21 - 2 * φ) * φ ^ n - 50 +
    (9 + 2 * φ) * ψ ^ n + 10 * ψ ^ (2 * n) =
    10 * lucasConst (2 * n) + 15 * lucasConst n +
    (6 - 2 * φ) * (φ ^ n - ψ ^ n) - 50 := by
  simp only [lucasConst]; ring

/-- Φ_S_int via Fibonacci: uses (6-2φ) = (5-√5) and (φⁿ-ψⁿ) = √5·F_n -/
theorem phiS_int_fibonacci (n : ℕ) :
    10 * φ ^ (2 * n) + (21 - 2 * φ) * φ ^ n - 50 +
    (9 + 2 * φ) * ψ ^ n + 10 * ψ ^ (2 * n) =
    10 * lucasConst (2 * n) + 15 * lucasConst n - 50 +
    (6 - 2 * φ) * Real.sqrt 5 * (Nat.fib n : ℝ) := by
  rw [phiS_int_coeff_real, phi_sub_psi_eq_sqrt5_fib]; ring

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

/-- z²·z⁵ → z⁷: ker × active = active with shifted eigenvalue -/
theorem interaction_2_5 (z : ℂ) :
    derivDefect (fun w => w ^ 2) (fun w => w ^ 5) z =
    Fζ (fun w => w ^ 7) z -
    z ^ 2 * Fζ (fun w => w ^ 5) z := by
  rw [derivDefect_monomial,
    show (2 + 5 : ℕ) = 7 from by ring,
    show (2 : ℕ) = 6 * 0 + 2 from by ring, Fζ_vanish_mod6_2 0]
  ring

/-! ## Annihilation: active × active → ker

When n≡1 and m≡5 (mod 6), n+m≡0 (mod 6), so δ = -Fζ(zⁿ)·zᵐ - zⁿ·Fζ(zᵐ). -/

/-- z¹·z⁵ → z⁶: two active modes annihilate into ker -/
theorem annihilation_1_5 (z : ℂ) :
    derivDefect (fun w => w ^ 1) (fun w => w ^ 5) z =
    -(z ^ 1 * Fζ (fun w => w ^ 5) z +
      Fζ (fun w => w ^ 1) z * z ^ 5) := by
  rw [derivDefect_monomial,
    show (1 + 5 : ℕ) = 6 * 1 from by ring, Fζ_vanish_mod6_0 1]
  ring

/-- z⁷·z⁵ → z¹²: two active modes annihilate into ker -/
theorem annihilation_7_5 (z : ℂ) :
    derivDefect (fun w => w ^ 7) (fun w => w ^ 5) z =
    -(z ^ 7 * Fζ (fun w => w ^ 5) z +
      Fζ (fun w => w ^ 7) z * z ^ 5) := by
  rw [derivDefect_monomial,
    show (7 + 5 : ℕ) = 6 * 2 from by ring, Fζ_vanish_mod6_0 2]
  ring

/-! ## Fζ is ℂ-linear in the function argument -/

theorem Fζ_const_smul (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    Fζ (fun w => c * f w) z = c * Fζ f z := by
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => c * f t) w) =
      fun w => c * (5 * Φ_A f w) := by
    funext w; unfold Φ_A; ring
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

/-! ## Root decomposition: Fζ(fg) = Fζ(f)·g + f·Fζ(g) + δ(f,g)

Not an axiom — just the derivation defect definition rearranged. -/

theorem root_decomposition (f g : ℂ → ℂ) (z : ℂ) :
    Fζ (fun w => f w * g w) z =
    Fζ f z * g z + f z * Fζ g z + derivDefect f g z := by
  unfold derivDefect; ring

/-! ## Selection rule: ker×ker interaction vanishes when root is in ker

If a+b ≡ 0 mod 6 and both a,b ∈ ker, then δ(zᵃ,zᵇ) = 0.
Two inert parts cannot produce dynamics if their root is also inert. -/

theorem selection_rule_ker_ker_ker (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 2)) (fun w => w ^ (6 * k + 4)) z = 0 := by
  rw [derivDefect_monomial,
    show (6 * j + 2 + (6 * k + 4)) = 6 * (j + k + 1) from by ring,
    Fζ_vanish_mod6_0, Fζ_vanish_mod6_2, Fζ_vanish_mod6_4]
  ring

theorem selection_rule_ker3_ker3 (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 3)) (fun w => w ^ (6 * k + 3)) z = 0 := by
  rw [derivDefect_monomial,
    show (6 * j + 3 + (6 * k + 3)) = 6 * (j + k + 1) from by ring,
    Fζ_vanish_mod6_0, Fζ_vanish_mod6_3, Fζ_vanish_mod6_3]
  ring

/-! ## Hierarchical mediation: 3-body root decomposition

For R = A·B·C, the root_decomposition applied twice gives:
Fζ(R) = [Fζ(A)·B + A·Fζ(B) + δ(A,B)]·C + (A·B)·Fζ(C) + δ(A·B, C)

A and C interact only through δ(A·B, C), mediated by B. -/

theorem hierarchical_mediation (f g h : ℂ → ℂ) (z : ℂ) :
    Fζ (fun w => f w * g w * h w) z =
    (Fζ f z * g z + f z * Fζ g z + derivDefect f g z) * h z +
    f z * g z * Fζ h z +
    derivDefect (fun w => f w * g w) h z := by
  have h1 := root_decomposition (fun w => f w * g w) h z
  rw [root_decomposition f g z] at h1
  convert h1 using 1

/-! ## Mediated interaction: z³ and z⁶ cannot interact directly but can through z⁴

δ(z³,z⁶) gives z⁹ ∈ ker, so the direct interaction is trivial.
But in z^13 = z³·z⁴·z⁶, the z⁴ mediator enables non-trivial dynamics. -/

/-- z³ and z⁶ have zero direct defect: 3+6=9 ≡ 3 mod 6 ∈ ker -/
theorem direct_interaction_trivial (z : ℂ) :
    derivDefect (fun w => w ^ 3) (fun w => w ^ 6) z = 0 := by
  rw [derivDefect_monomial,
    show (3 + 6 : ℕ) = 6 * 1 + 3 from by ring, Fζ_vanish_mod6_3,
    show (3 : ℕ) = 6 * 0 + 3 from by ring, Fζ_vanish_mod6_3,
    show (6 : ℕ) = 6 * 1 from by ring, Fζ_vanish_mod6_0]
  ring

/-- But z³·z⁴ = z⁷ is active (emergence), and z⁷ can interact with z⁶.
    The mediated defect δ(z⁷,z⁶) = Fζ(z¹³) - Fζ(z⁷)·z⁶. -/
theorem mediated_defect_structure (z : ℂ) :
    derivDefect (fun w => w ^ 7) (fun w => w ^ 6) z =
    Fζ (fun w => w ^ 13) z -
    Fζ (fun w => w ^ 7) z * z ^ 6 := by
  rw [derivDefect_monomial,
    show (7 + 6 : ℕ) = 13 from by ring,
    show (6 : ℕ) = 6 * 1 from by ring, Fζ_vanish_mod6_0]
  ring

/-! ## Charge conjugation: AF_coeff sign flip between mod 1 and mod 5

The AF channel contributes +AF_coeff for n≡1 and -AF_coeff for n≡5,
while the SY channel contributes +6 for both. This is C-parity. -/

/-- AF_coeff cancels in mod1 + mod5 sum: only SY channel (2×6=12) survives -/
theorem charge_conjugation_AF_cancel (c₁ c₅ : ℂ) (z : ℂ) :
    (5 * c₁ * AF_coeff + 6 * c₁) * z + (-5 * c₅ * AF_coeff + 6 * c₅) * z =
    6 * (c₁ + c₅) * z + 5 * (c₁ - c₅) * AF_coeff * z := by
  ring

/-! ## Pair creation: vacuum factorization forces matter-antimatter pairs

In a vacuum root z^{6k}, any binary factorization z^a · z^{6k-a} with a≡1 mod 6
forces (6k-a) ≡ 5 mod 6. Matter necessarily comes with antimatter. -/

theorem pair_creation_mod6 (j k : ℕ) :
    (6 * k - (6 * j + 1)) % 6 = 5 ∨ 6 * k ≤ 6 * j + 1 := by
  by_cases h : 6 * j + 1 ≤ 6 * k
  · left; omega
  · right; omega

/-- Pair annihilation: mod 1 + mod 5 → vacuum (mod 0). Generalized. -/
theorem pair_annihilation (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 1)) (fun w => w ^ (6 * k + 5)) z =
    -(z ^ (6 * j + 1) * Fζ (fun w => w ^ (6 * k + 5)) z +
      Fζ (fun w => w ^ (6 * j + 1)) z * z ^ (6 * k + 5)) := by
  rw [derivDefect_monomial,
    show (6 * j + 1 + (6 * k + 5)) = 6 * (j + k + 1) from by ring,
    Fζ_vanish_mod6_0]
  ring

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

/-! ## Spectral purity: z=1 as the unique spectral evaluation point

At z₀=1, every monomial evaluates to 1, so Fζ(zⁿ)(1) = λ(n)·1ⁿ = λ(n).
The eigenvalue IS the function value. This property characterizes z₀=1 uniquely
among nonzero ℂ: if z₀ⁿ = z₀ for all n ≥ 2, then z₀ ∈ {0, 1}. -/

/-- Idempotent characterization: z²=z ∧ z≠0 → z=1 in ℂ -/
theorem spectral_point_unique (z₀ : ℂ) (h_sq : z₀ ^ 2 = z₀) (h_ne : z₀ ≠ 0) :
    z₀ = 1 := by
  have h1 : z₀ * (z₀ - 1) = 0 := by
    have h2 : z₀ ^ 2 - z₀ = 0 := sub_eq_zero.mpr h_sq
    calc z₀ * (z₀ - 1) = z₀ ^ 2 - z₀ := by ring
    _ = 0 := h2
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h h_ne
  · exact sub_eq_zero.mp h

/-- Spectral purity: at z₀=1, monomial eigenvalue is recovered without distortion -/
theorem spectral_purity (n : ℕ) :
    Fζ (fun w => w ^ n) 1 = Fζ (fun w => w ^ n) 1 * (1 : ℂ) ^ n := by
  simp [one_pow]

/-- At any z₀, the eigenfunction evaluation is λ(n)·z₀ⁿ. At z₀=1 the z₀ⁿ factor is 1. -/
theorem eval_at_one_kills_geometric (n : ℕ) : (1 : ℂ) ^ n = 1 := one_pow n

/-- z₀=-1 fails spectral purity: (-1)^n ≠ 1 for odd n -/
theorem neg_one_pow_ne_one_odd : (-1 : ℂ) ^ 1 ≠ 1 := by norm_num

/-- z₀=1 is the unique nonzero point where z₀ⁿ=1 for all n simultaneously -/
theorem one_pow_universal_unique (z₀ : ℂ)
    (h_all : ∀ n : ℕ, z₀ ^ n = 1) : z₀ = 1 := by
  have := h_all 1; simpa using this

/-! ## Primordial mode: z¹ is the unique active mode that cannot emerge

Emergence = ker × ker → active: δ(zᵃ,zᵇ) = Fζ(z^{a+b}) when both a,b ∈ ker.
For active n ≥ 5, the pair (3, n-3) always gives emergence since gcd(3,6)>1 and
n-3 ≡ 2 or 4 mod 6 ∈ ker. But for n=1, no pair (a,b) with a+b=1, a≥1, b≥1 exists. -/

/-- Any active n ≥ 5 can emerge: (3, n-3) is a valid kernel pair -/
theorem emergence_exists_ge5 (n : ℕ) (hn : n ≥ 5)
    (h1 : n % 6 = 1 ∨ n % 6 = 5) :
    ∃ a b : ℕ, a + b = n ∧ a ≥ 1 ∧ b ≥ 1 ∧
    (a % 6 = 0 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4) ∧
    (b % 6 = 0 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4) := by
  refine ⟨3, n - 3, ?_, by omega, by omega, Or.inr (Or.inr (Or.inl rfl)), ?_⟩
  · omega
  · rcases h1 with h | h <;> right <;> [right; left] <;> [right; exact ?_] <;> omega

/-- n=1 cannot emerge: no pair (a,b) with a+b=1, a≥1, b≥1 exists -/
theorem no_emergence_one :
    ¬∃ a b : ℕ, a + b = 1 ∧ a ≥ 1 ∧ b ≥ 1 := by omega

/-- z¹ is active (1 mod 6 = 1, gcd(1,6) = 1) -/
theorem one_mod6 : 1 % 6 = 1 := by norm_num

/-- The primordial mode z¹ is irreducible: it cannot be produced by emergence.
    Combined with emergence_exists_ge5, this shows z¹ is uniquely primordial. -/
theorem primordial_mode_unique (n : ℕ) (hn_active : n % 6 = 1 ∨ n % 6 = 5)
    (hn_no_emerge : ¬∃ a b : ℕ, a + b = n ∧ a ≥ 1 ∧ b ≥ 1 ∧
      (a % 6 = 0 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4) ∧
      (b % 6 = 0 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4)) :
    n = 1 := by
  by_contra h
  have hn5 : n ≥ 5 := by omega
  exact hn_no_emerge (emergence_exists_ge5 n hn5 hn_active)

/-! ## Vacuum state: the constant function is the unique Galois-fixed kernel element

f(z) = 1 = z⁰ is in ker(Fζ), has degree 0, and evaluates to 1 at z=1.
It is the "vacuum" — zero eigenvalue, maximum symmetry. -/

/-- The constant function is annihilated by Fζ -/
theorem vacuum_state (z : ℂ) :
    Fζ (fun _ => (1 : ℂ)) z = 0 := by
  have : (fun _ : ℂ => (1 : ℂ)) = (fun w => w ^ (6 * 0)) := by
    funext w; simp
  rw [this, Fζ_vanish_mod6_0]

/-- At z=1: vacuum evaluates to 1 while primordial mode also evaluates to 1 -/
theorem vacuum_primordial_degenerate :
    (fun _ : ℂ => (1 : ℂ)) 1 = (fun w : ℂ => w ^ 1) 1 := by norm_num

/-! ## Self-interaction necessity: δ(z¹,z¹) ≠ 0

The primordial mode z¹ has nonzero self-interaction defect
δ(z¹,z¹) = -2·Fζ(z¹)·z. Since Fζ(z¹) ≠ 0, the self-interaction
is forced — a static universe with only z¹ is impossible. -/

/-- δ(z¹,z¹) = -2·Fζ(z)·z: self-interaction produces ker mode z² -/
theorem self_interaction_primordial (z : ℂ) :
    derivDefect (fun w => w ^ 1) (fun w => w ^ 1) z =
    -(2 * Fζ (fun w => w ^ 1) z * z) := by
  rw [derivDefect_monomial, show (1 + 1 : ℕ) = 6 * 0 + 2 from by ring,
    Fζ_vanish_mod6_2]
  ring

/-! ## Active+active → ker: particles never directly create particles

For any two active modes a ≡ 1 or 5, b ≡ 1 or 5 (mod 6),
a+b ≡ 0, 2, or 4 (mod 6), hence a+b ∈ ker. -/

theorem active_sum_mod6 (a b : ℕ)
    (ha : a % 6 = 1 ∨ a % 6 = 5) (hb : b % 6 = 1 ∨ b % 6 = 5) :
    (a + b) % 6 = 0 ∨ (a + b) % 6 = 2 ∨ (a + b) % 6 = 4 := by
  omega

/-- Two matter modes annihilate into mod 2 kernel (spatial sector) -/
theorem matter_matter_annihilation (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 1)) (fun w => w ^ (6 * k + 1)) z =
    -(z ^ (6 * j + 1) * Fζ (fun w => w ^ (6 * k + 1)) z +
      Fζ (fun w => w ^ (6 * j + 1)) z * z ^ (6 * k + 1)) := by
  rw [derivDefect_monomial,
    show (6 * j + 1 + (6 * k + 1)) = 6 * (j + k) + 2 from by ring,
    Fζ_vanish_mod6_2]
  ring

/-- Two antimatter modes annihilate into mod 4 kernel (spatial sector) -/
theorem antimatter_antimatter_annihilation (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 5)) (fun w => w ^ (6 * k + 5)) z =
    -(z ^ (6 * j + 5) * Fζ (fun w => w ^ (6 * k + 5)) z +
      Fζ (fun w => w ^ (6 * j + 5)) z * z ^ (6 * k + 5)) := by
  rw [derivDefect_monomial,
    show (6 * j + 5 + (6 * k + 5)) = 6 * (j + k + 1) + 4 from by ring,
    Fζ_vanish_mod6_4]
  ring

/-! ## Kernel sector classification

The kernel decomposes into 4 sectors by mod 6 residue:
- mod 0: vacuum sector (true pair annihilation target)
- mod 2: spatial-A sector (matter+matter product)
- mod 3: spatial-B sector (the universal catalyst)
- mod 4: spatial-C sector (antimatter+antimatter product)

Each active+active interaction targets a specific sector. -/

/-- Matter+antimatter → mod 0 vacuum (true annihilation) -/
theorem matter_antimatter_to_vacuum (j k : ℕ) :
    (6 * j + 1 + (6 * k + 5)) % 6 = 0 := by omega

/-- Matter+matter → mod 2 spatial-A -/
theorem matter_matter_to_mod2 (j k : ℕ) :
    (6 * j + 1 + (6 * k + 1)) % 6 = 2 := by omega

/-- Antimatter+antimatter → mod 4 spatial-C -/
theorem antimatter_antimatter_to_mod4 (j k : ℕ) :
    (6 * j + 5 + (6 * k + 5)) % 6 = 4 := by omega

/-! ## mod 3 universal catalyst: REQUIRED for all emergence

Emergence = ker × ker → active. The only ker×ker pairs giving active sums:
- mod 3 + mod 4 ≡ 1 (mod 6) → matter emergence
- mod 2 + mod 3 ≡ 5 (mod 6) → antimatter emergence
mod 3 is present in EVERY emergence path. -/

/-- The only ker×ker sum giving mod 1 is mod 3 + mod 4 -/
theorem emergence_to_matter_requires_mod3 (a b : ℕ)
    (ha : a % 6 = 0 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4)
    (hb : b % 6 = 0 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4)
    (hsum : (a + b) % 6 = 1) :
    (a % 6 = 3 ∧ b % 6 = 4) ∨ (a % 6 = 4 ∧ b % 6 = 3) := by
  omega

/-- The only ker×ker sum giving mod 5 is mod 2 + mod 3 -/
theorem emergence_to_antimatter_requires_mod3 (a b : ℕ)
    (ha : a % 6 = 0 ∨ a % 6 = 2 ∨ a % 6 = 3 ∨ a % 6 = 4)
    (hb : b % 6 = 0 ∨ b % 6 = 2 ∨ b % 6 = 3 ∨ b % 6 = 4)
    (hsum : (a + b) % 6 = 5) :
    (a % 6 = 2 ∧ b % 6 = 3) ∨ (a % 6 = 3 ∧ b % 6 = 2) := by
  omega

/-- Concrete emergence: z³·z⁴ → z⁷ (matter, mod 3 + mod 4 → mod 1) -/
theorem emergence_mod3_mod4 (z : ℂ) :
    derivDefect (fun w => w ^ 3) (fun w => w ^ 4) z =
    Fζ (fun w => w ^ 7) z :=
  emergence_3_4 z

/-- Concrete emergence: z²·z³ → z⁵ (antimatter, mod 2 + mod 3 → mod 5) -/
theorem emergence_mod2_mod3 (z : ℂ) :
    derivDefect (fun w => w ^ 2) (fun w => w ^ 3) z =
    Fζ (fun w => w ^ 5) z := by
  rw [derivDefect_monomial,
    show (2 + 3 : ℕ) = 6 * 0 + 5 from by ring,
    show (2 : ℕ) = 6 * 0 + 2 from by ring, Fζ_vanish_mod6_2 0,
    show (3 : ℕ) = 6 * 0 + 3 from by ring, Fζ_vanish_mod6_3 0]
  ring

/-! ## Minimum steps to antimatter

From z¹, reaching the first antimatter mode z⁵ requires exactly 3
binary interaction steps. Two paths exist:
Path A: z¹ →[z¹·z¹] z² →[z¹·z²] z³ →[z²·z³] z⁵
Path B: z¹ →[z¹·z¹] z² →[z²·z²] z⁴ →[z¹·z⁴] z⁵ -/

/-- 5 cannot be written as a+b with a,b ∈ {1}: one step is insufficient -/
theorem antimatter_not_one_step :
    ¬∃ a b : ℕ, a + b = 5 ∧ a = 1 ∧ b = 1 := by omega

/-- 5 cannot be written as a+b where both a,b are sums of 1+1: two steps insufficient -/
theorem antimatter_not_two_steps :
    ¬∃ a b : ℕ, a + b = 5 ∧
    (a = 1 ∨ a = 2) ∧ (b = 1 ∨ b = 2) := by omega

/-- Path A exists: z¹→z²→z³→z⁵ in 3 steps -/
theorem antimatter_path_A :
    1 + 1 = 2 ∧ 1 + 2 = 3 ∧ 2 + 3 = 5 := by omega

/-- Path B exists: z¹→z²→z⁴→z⁵ in 3 steps -/
theorem antimatter_path_B :
    1 + 1 = 2 ∧ 2 + 2 = 4 ∧ 1 + 4 = 5 := by omega

/-- z⁵ is the first antimatter mode (smallest n ≡ 5 mod 6 with n ≥ 1) -/
theorem five_is_first_antimatter : 5 % 6 = 5 ∧ ∀ m, 1 ≤ m → m < 5 → m % 6 ≠ 5 := by
  constructor
  · norm_num
  · intro m hm1 hm5; omega

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

/-- τ-norm: (c_A·AF + c_S)·(-c_A·AF + c_S) = c_S² + 12·c_A² -/
theorem tau_norm (c_A c_S : ℂ) :
    (c_A * AF_coeff + c_S) * (-c_A * AF_coeff + c_S) =
    c_S ^ 2 + 12 * c_A ^ 2 := by
  have h := AF_coeff_sq
  calc (c_A * AF_coeff + c_S) * (-c_A * AF_coeff + c_S)
      = c_S ^ 2 - (c_A * AF_coeff) ^ 2 := by ring
    _ = c_S ^ 2 - c_A ^ 2 * AF_coeff ^ 2 := by ring
    _ = c_S ^ 2 - c_A ^ 2 * (-12) := by rw [h]
    _ = c_S ^ 2 + 12 * c_A ^ 2 := by ring

/-- τ-norm for real coefficients is nonneg: c_S² + 12c_A² ≥ 0 -/
theorem tau_norm_nonneg (c_A c_S : ℝ) :
    (c_S : ℝ) ^ 2 + 12 * c_A ^ 2 ≥ 0 := by positivity

/-- τ-norm for real coefficients: positive when c_A ≠ 0 or c_S ≠ 0 -/
theorem tau_norm_pos (c_A c_S : ℝ) (h : c_A ≠ 0 ∨ c_S ≠ 0) :
    c_S ^ 2 + 12 * c_A ^ 2 > 0 := by
  rcases h with hA | hS
  · have : 12 * c_A ^ 2 > 0 := by positivity
    linarith [sq_nonneg c_S]
  · have : c_S ^ 2 > 0 := by positivity
    linarith [mul_nonneg (by norm_num : (12 : ℝ) ≥ 0) (sq_nonneg c_A)]

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

/-- Eigenvalue τ-norm for real coefficients: 36c_S² + 300c_A² ≥ 0 -/
theorem eigenvalue_tau_norm_nonneg (c_A c_S : ℝ) :
    36 * (c_S : ℝ) ^ 2 + 300 * c_A ^ 2 ≥ 0 := by positivity

/-- τ-discriminant: the quadratic x²-12c_S·x+(36c_S²+300c_A²)
    has discriminant -1200·c_A². Negative iff c_A ≠ 0. -/
theorem tau_discriminant (c_A c_S : ℝ) :
    (12 * c_S) ^ 2 - 4 * (36 * c_S ^ 2 + 300 * c_A ^ 2) =
    -(1200 * c_A ^ 2) := by ring

/-- The discriminant is non-positive -/
theorem tau_discriminant_nonpos (c_A c_S : ℝ) :
    (12 * c_S) ^ 2 - 4 * (36 * c_S ^ 2 + 300 * c_A ^ 2) ≤ 0 := by
  rw [tau_discriminant]; linarith [sq_nonneg c_A]

/-- The discriminant is strictly negative when c_A ≠ 0 -/
theorem tau_discriminant_neg (c_A c_S : ℝ) (hA : c_A ≠ 0) :
    (12 * c_S) ^ 2 - 4 * (36 * c_S ^ 2 + 300 * c_A ^ 2) < 0 := by
  rw [tau_discriminant]
  have : c_A ^ 2 > 0 := by positivity
  linarith

/-! ## s ↔ 1-s analog: eigenvalue pair structure

Each active mode n has a τ-conjugate pair (λ, τ(λ)) with:
- trace = 12·c_S(n) (real, AF-free)
- norm = 36·c_S(n)² + 300·c_A(n)² (positive definite)
- discriminant = -1200·c_A(n)² (strictly negative for active modes)

This is the FUST analog of the Riemann ξ functional equation:
- τ plays the role of s ↔ 1-s
- The "critical line" is Re(λ) = 6c_S (pure SY channel)
- Active eigenvalues always come as complex conjugate pairs
- No active eigenvalue is real (no "trivial zeros") -/

/-- Summary: τ-symmetry structure of Fζ eigenvalues -/
theorem tau_symmetry_summary (c_A c_S : ℝ) (hA : c_A ≠ 0) :
    (5 * (↑c_A : ℂ) * AF_coeff + 6 * ↑c_S) +
      (-5 * ↑c_A * AF_coeff + 6 * ↑c_S) = 12 * ↑c_S ∧
    (5 * (↑c_A : ℂ) * AF_coeff + 6 * ↑c_S) *
      (-5 * ↑c_A * AF_coeff + 6 * ↑c_S) =
      36 * ↑c_S ^ 2 + 300 * ↑c_A ^ 2 ∧
    (12 * c_S) ^ 2 - 4 * (36 * c_S ^ 2 + 300 * c_A ^ 2) < 0 :=
  ⟨eigenvalue_tau_trace ↑c_A ↑c_S,
   eigenvalue_tau_norm ↑c_A ↑c_S,
   tau_discriminant_neg c_A c_S hA⟩

/-! ## τ-symmetric state functions: Ψₖ(z) = zᵏ(1-z)ᵏ

The τ involution z ↦ 1-z fixes Re(z) = 1/2.
A state function f is τ-symmetric if f(z) = f(1-z).
The simplest family: Ψₖ(z) = zᵏ(1-z)ᵏ = (z(1-z))ᵏ.
These vanish at z=0 (void) and z=1 (Big Bang), peaked at z=1/2. -/

/-- τ-symmetry: z^k(1-z)^k = (1-z)^k·z^k -/
theorem tau_symmetric_pow (z : ℂ) (k : ℕ) :
    (z * (1 - z)) ^ k = ((1 - z) * z) ^ k := by ring

/-- Ψ_M: the matter state z(1-z) = z - z² -/
theorem psi_matter_expand (z : ℂ) :
    z * (1 - z) = z - z ^ 2 := by ring

/-- Fζ(z-z²) = Fζ(z): z² ∈ ker eliminates the second term -/
theorem Fζ_psi_matter (z : ℂ) :
    Fζ (fun w => w - w ^ 2) z = Fζ (fun w => w ^ 1) z := by
  have h : (fun w : ℂ => w - w ^ 2) = fun w => w ^ 1 + (-1) * w ^ 2 := by
    funext w; ring
  rw [h]
  have h2 : (fun w : ℂ => w ^ 1 + (-1) * w ^ 2) = fun w =>
    (fun w => w ^ 1) w + (-1) * (fun w => w ^ 2) w := by
    funext w; ring
  rw [h2]
  -- Use linearity
  unfold Fζ
  have hA1 : (fun w => 5 * Φ_A (fun t => (fun w => w ^ 1) t + (-1) * (fun w => w ^ 2) t) w) =
    fun w => (5 * Φ_A (fun t => t ^ 1) w) + (-1) * (5 * Φ_A (fun t => t ^ 2) w) := by
    funext w; unfold Φ_A; ring
  have hS1 : Φ_S_int (fun t => (fun w => w ^ 1) t + (-1) * (fun w => w ^ 2) t) =
    fun w => Φ_S_int (fun t => t ^ 1) w + (-1) * Φ_S_int (fun t => t ^ 2) w := by
    funext w; unfold Φ_S_int; ring
  rw [hA1, hS1]
  -- AFNum and SymNum are also linear
  have hAF2 := AFNum_kills_sq (fun w => 5 * Φ_A (fun t => t ^ 2) w)
    (5 * ((↑φ : ℂ) ^ 6 - 4 * (↑φ : ℂ) ^ 4 + (3 + ↑φ) * (↑φ : ℂ) ^ 2 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 2 + 4 * (↑ψ : ℂ) ^ 4 - (↑ψ : ℂ) ^ 6)) z
    (fun w => five_phiA_sq w)
  have hSY2 := SymNum_kills_sq (Φ_S_int (fun t => t ^ 2))
    (10 * (↑φ : ℂ) ^ 4 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 2 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 2 + 10 * (↑ψ : ℂ) ^ 4) z
    (fun w => phiS_int_sq w)
  -- Linearity of AFNum and SymNum
  have hAFlin :
    AFNum (fun w => 5 * Φ_A (fun t => t ^ 1) w + (-1) * (5 * Φ_A (fun t => t ^ 2) w)) z =
    AFNum (fun w => 5 * Φ_A (fun t => t ^ 1) w) z +
    (-1) * AFNum (fun w => 5 * Φ_A (fun t => t ^ 2) w) z := by
    unfold AFNum; ring
  have hSYlin : SymNum (fun w => Φ_S_int (fun t => t ^ 1) w + (-1) * Φ_S_int (fun t => t ^ 2) w) z =
    SymNum (Φ_S_int (fun t => t ^ 1)) z +
    (-1) * SymNum (Φ_S_int (fun t => t ^ 2)) z := by
    unfold SymNum; ring
  rw [hAFlin, hSYlin, hAF2, hSY2]; ring

/-- Ψ_0: the vacuum state z²(1-z)² = z²-2z³+z⁴ is in ker -/
theorem Fζ_psi_vacuum (z : ℂ) :
    Fζ (fun w => (w * (1 - w)) ^ 2) z = 0 := by
  have h : (fun w : ℂ => (w * (1 - w)) ^ 2) =
    fun w => w ^ 2 + (-2) * w ^ 3 + w ^ 4 := by funext w; ring
  rw [h]
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => t ^ 2 + (-2) * t ^ 3 + t ^ 4) w) =
    fun w => 5 * Φ_A (fun t => t ^ 2) w + (-2) * (5 * Φ_A (fun t => t ^ 3) w) +
             5 * Φ_A (fun t => t ^ 4) w := by
    funext w; unfold Φ_A; ring
  have hS : Φ_S_int (fun t => t ^ 2 + (-2) * t ^ 3 + t ^ 4) =
    fun w => Φ_S_int (fun t => t ^ 2) w + (-2) * Φ_S_int (fun t => t ^ 3) w +
             Φ_S_int (fun t => t ^ 4) w := by
    funext w; unfold Φ_S_int; ring
  rw [hA, hS]
  -- Each z² z³ z⁴ factor is killed by both AFNum and SymNum
  have hAF2 := AFNum_kills_sq (fun w => 5 * Φ_A (fun t => t ^ 2) w)
    (5 * ((↑φ : ℂ) ^ 6 - 4 * (↑φ : ℂ) ^ 4 + (3 + ↑φ) * (↑φ : ℂ) ^ 2 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 2 + 4 * (↑ψ : ℂ) ^ 4 - (↑ψ : ℂ) ^ 6)) z
    (fun w => five_phiA_sq w)
  have hAF3 := AFNum_kills_cube (fun w => 5 * Φ_A (fun t => t ^ 3) w)
    (5 * ((↑φ : ℂ) ^ 9 - 4 * (↑φ : ℂ) ^ 6 + (3 + ↑φ) * (↑φ : ℂ) ^ 3 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 3 + 4 * (↑ψ : ℂ) ^ 6 - (↑ψ : ℂ) ^ 9)) z
    (fun w => five_phiA_cube w)
  have hAF4 := AFNum_kills_fourth (fun w => 5 * Φ_A (fun t => t ^ 4) w)
    (5 * ((↑φ : ℂ) ^ 12 - 4 * (↑φ : ℂ) ^ 8 + (3 + ↑φ) * (↑φ : ℂ) ^ 4 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 4 + 4 * (↑ψ : ℂ) ^ 8 - (↑ψ : ℂ) ^ 12)) z
    (fun w => five_phiA_fourth w)
  have hSY2 := SymNum_kills_sq (Φ_S_int (fun t => t ^ 2))
    (10 * (↑φ : ℂ) ^ 4 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 2 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 2 + 10 * (↑ψ : ℂ) ^ 4) z
    (fun w => phiS_int_sq w)
  have hSY3 := SymNum_kills_cube (Φ_S_int (fun t => t ^ 3))
    (10 * (↑φ : ℂ) ^ 6 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 3 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 3 + 10 * (↑ψ : ℂ) ^ 6) z
    (fun w => phiS_int_cube w)
  have hSY4 := SymNum_kills_fourth (Φ_S_int (fun t => t ^ 4))
    (10 * (↑φ : ℂ) ^ 8 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 4 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 4 + 10 * (↑ψ : ℂ) ^ 8) z
    (fun w => phiS_int_fourth w)
  have hAFlin : AFNum (fun w => 5 * Φ_A (fun t => t ^ 2) w + (-2) * (5 * Φ_A (fun t => t ^ 3) w) +
    5 * Φ_A (fun t => t ^ 4) w) z =
    AFNum (fun w => 5 * Φ_A (fun t => t ^ 2) w) z +
    (-2) * AFNum (fun w => 5 * Φ_A (fun t => t ^ 3) w) z +
    AFNum (fun w => 5 * Φ_A (fun t => t ^ 4) w) z := by
    unfold AFNum; ring
  have hSYlin : SymNum (fun w => Φ_S_int (fun t => t ^ 2) w + (-2) * Φ_S_int (fun t => t ^ 3) w +
    Φ_S_int (fun t => t ^ 4) w) z =
    SymNum (Φ_S_int (fun t => t ^ 2)) z +
    (-2) * SymNum (Φ_S_int (fun t => t ^ 3)) z +
    SymNum (Φ_S_int (fun t => t ^ 4)) z := by
    unfold SymNum; ring
  rw [hAFlin, hSYlin, hAF2, hAF3, hAF4, hSY2, hSY3, hSY4]; ring

/-- Ψ_A: the antimatter state z³(1-z)³ = z³-3z⁴+3z⁵-z⁶ gives 3·Fζ(z⁵) -/
theorem Fζ_psi_antimatter (z : ℂ) :
    Fζ (fun w => (w * (1 - w)) ^ 3) z =
    3 * Fζ (fun w => w ^ 5) z := by
  have h : (fun w : ℂ => (w * (1 - w)) ^ 3) =
    fun w => w ^ 3 + (-3) * w ^ 4 + 3 * w ^ 5 + (-1) * w ^ 6 := by funext w; ring
  rw [h]
  -- z³, z⁴, z⁶ are all in ker; only z⁵ survives
  have h5 : (fun w : ℂ => w ^ 3 + (-3) * w ^ 4 + 3 * w ^ 5 + (-1) * w ^ 6) =
    fun w => (fun w => w ^ (6 * 0 + 3)) w + (-3) * (fun w => w ^ (6 * 0 + 4)) w +
             3 * (fun w => w ^ 5) w + (-1) * (fun w => w ^ (6 * 1)) w := by
    funext w; ring
  rw [h5, show (6 * 0 + 3 : ℕ) = 3 from by ring, show (6 * 0 + 4 : ℕ) = 4 from by ring]
  unfold Fζ
  have hA : (fun w => 5 * Φ_A (fun t => (fun w => w ^ 3) t + (-3) * (fun w => w ^ 4) t +
    3 * (fun w => w ^ 5) t + (-1) * (fun w => w ^ (6 * 1)) t) w) =
    fun w => 5 * Φ_A (fun t => t ^ 3) w + (-3) * (5 * Φ_A (fun t => t ^ 4) w) +
             3 * (5 * Φ_A (fun t => t ^ 5) w) + (-1) * (5 * Φ_A (fun t => t ^ (6 * 1)) w) := by
    funext w; unfold Φ_A; ring
  have hS : Φ_S_int (fun t => (fun w => w ^ 3) t + (-3) * (fun w => w ^ 4) t +
    3 * (fun w => w ^ 5) t + (-1) * (fun w => w ^ (6 * 1)) t) =
    fun w => Φ_S_int (fun t => t ^ 3) w + (-3) * Φ_S_int (fun t => t ^ 4) w +
             3 * Φ_S_int (fun t => t ^ 5) w + (-1) * Φ_S_int (fun t => t ^ (6 * 1)) w := by
    funext w; unfold Φ_S_int; ring
  rw [hA, hS]
  -- Kill the ker modes
  have hAF3 := AFNum_kills_cube (fun w => 5 * Φ_A (fun t => t ^ 3) w)
    (5 * ((↑φ : ℂ) ^ 9 - 4 * (↑φ : ℂ) ^ 6 + (3 + ↑φ) * (↑φ : ℂ) ^ 3 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 3 + 4 * (↑ψ : ℂ) ^ 6 - (↑ψ : ℂ) ^ 9)) z
    (fun w => five_phiA_cube w)
  have hAF4 := AFNum_kills_fourth (fun w => 5 * Φ_A (fun t => t ^ 4) w)
    (5 * ((↑φ : ℂ) ^ 12 - 4 * (↑φ : ℂ) ^ 8 + (3 + ↑φ) * (↑φ : ℂ) ^ 4 -
     (3 + ↑ψ) * (↑ψ : ℂ) ^ 4 + 4 * (↑ψ : ℂ) ^ 8 - (↑ψ : ℂ) ^ 12)) z
    (fun w => five_phiA_fourth w)
  have hSY3 := SymNum_kills_cube (Φ_S_int (fun t => t ^ 3))
    (10 * (↑φ : ℂ) ^ 6 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 3 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 3 + 10 * (↑ψ : ℂ) ^ 6) z
    (fun w => phiS_int_cube w)
  have hSY4 := SymNum_kills_fourth (Φ_S_int (fun t => t ^ 4))
    (10 * (↑φ : ℂ) ^ 8 + (21 - 2 * ↑φ) * (↑φ : ℂ) ^ 4 - 50 +
     (9 + 2 * ↑φ) * (↑ψ : ℂ) ^ 4 + 10 * (↑ψ : ℂ) ^ 8) z
    (fun w => phiS_int_fourth w)
  -- mod 6·1 = 6·1+0
  have hAF0 : AFNum (fun w => 5 * Φ_A (fun t => t ^ (6 * 1)) w) z = 0 := by
    have : (fun w : ℂ => 5 * Φ_A (fun t => t ^ (6 * 1)) w) =
      fun w => (5 * ((↑φ : ℂ) ^ (3 * (6 * 1)) - 4 * (↑φ : ℂ) ^ (2 * (6 * 1)) +
        (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * 1) - (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ (6 * 1) +
        4 * (↑ψ : ℂ) ^ (2 * (6 * 1)) - (↑ψ : ℂ) ^ (3 * (6 * 1)))) * w ^ (6 * 1) := by
      funext w; rw [phiA_monomial]; ring
    rw [this, AFNum_smul, AFNum_pow_mod6_0, mul_zero]
  have hSY0 : SymNum (Φ_S_int (fun t => t ^ (6 * 1))) z = 0 := by
    have : Φ_S_int (fun t => t ^ (6 * 1)) =
      fun w => (10 * (↑φ : ℂ) ^ (2 * (6 * 1)) + (21 - 2 * (↑φ : ℂ)) * (↑φ : ℂ) ^ (6 * 1) - 50 +
        (9 + 2 * (↑φ : ℂ)) * (↑ψ : ℂ) ^ (6 * 1) + 10 * (↑ψ : ℂ) ^ (2 * (6 * 1))) * w ^ (6 * 1) := by
      funext w; rw [phiS_int_monomial]
    rw [this, SymNum_smul, SymNum_pow_mod6_0, mul_zero]
  -- Linearity
  have hAFlin : AFNum (fun w => 5 * Φ_A (fun t => t ^ 3) w + (-3) * (5 * Φ_A (fun t => t ^ 4) w) +
    3 * (5 * Φ_A (fun t => t ^ 5) w) + (-1) * (5 * Φ_A (fun t => t ^ (6 * 1)) w)) z =
    AFNum (fun w => 5 * Φ_A (fun t => t ^ 3) w) z +
    (-3) * AFNum (fun w => 5 * Φ_A (fun t => t ^ 4) w) z +
    3 * AFNum (fun w => 5 * Φ_A (fun t => t ^ 5) w) z +
    (-1) * AFNum (fun w => 5 * Φ_A (fun t => t ^ (6 * 1)) w) z := by
    unfold AFNum; ring
  have hSYlin : SymNum (fun w => Φ_S_int (fun t => t ^ 3) w + (-3) * Φ_S_int (fun t => t ^ 4) w +
    3 * Φ_S_int (fun t => t ^ 5) w + (-1) * Φ_S_int (fun t => t ^ (6 * 1)) w) z =
    SymNum (Φ_S_int (fun t => t ^ 3)) z +
    (-3) * SymNum (Φ_S_int (fun t => t ^ 4)) z +
    3 * SymNum (Φ_S_int (fun t => t ^ 5)) z +
    (-1) * SymNum (Φ_S_int (fun t => t ^ (6 * 1))) z := by
    unfold SymNum; ring
  rw [hAFlin, hSYlin, hAF3, hAF4, hAF0, hSY3, hSY4, hSY0]; ring

/-! ## The 6th cyclotomic polynomial and ζ₆ degeneracy

z²-z+1 = Φ₆(z). Its roots are ζ₆ and ζ̄₆ = 1-ζ₆, both on Re(z)=1/2.
At z=ζ₆: z(1-z) = ζ₆·ζ₆⁵ = ζ₆⁶ = 1, so all Ψₖ(ζ₆) = 1.
Matter, vacuum, and antimatter states are degenerate at ζ₆. -/

/-- ζ₆ is a root of Φ₆(z) = z²-z+1 -/
theorem zeta6_cyclotomic : ζ₆ ^ 2 - ζ₆ + 1 = 0 := by
  have h := zeta6_sq; rw [h]; ring

/-- ζ₆(1-ζ₆) = 1: the τ-symmetric product at ζ₆ -/
theorem zeta6_tau_product : ζ₆ * (1 - ζ₆) = 1 := by
  have h : ζ₆ * (1 - ζ₆) = -(ζ₆ ^ 2 - ζ₆ + 1) + 1 := by ring
  rw [h, zeta6_cyclotomic]; ring

/-- Matter-vacuum-antimatter degeneracy at ζ₆: all equal 1 -/
theorem critical_degeneracy :
    ζ₆ * (1 - ζ₆) = 1 ∧
    (ζ₆ * (1 - ζ₆)) ^ 2 = 1 ∧
    (ζ₆ * (1 - ζ₆)) ^ 3 = 1 := by
  have h := zeta6_tau_product; exact ⟨h, by rw [h]; ring, by rw [h]; ring⟩

/-- The 6th cyclotomic polynomial characterizes the critical degeneracy -/
theorem cyclotomic6_characterization (z : ℂ) :
    z * (1 - z) = 1 ↔ z ^ 2 - z + 1 = 0 := by
  constructor
  · intro h; have : z ^ 2 - z + 1 = -(z * (1 - z)) + 1 := by ring
    rw [this, h]; ring
  · intro h; have : z * (1 - z) = -(z ^ 2 - z + 1) + 1 := by ring
    rw [this, h]; ring

/-- Ψ_M(z) = 1 iff z is a root of Φ₆ -/
theorem psi_matter_unity (z : ℂ) :
    z * (1 - z) = 1 ↔ z ^ 2 - z + 1 = 0 :=
  cyclotomic6_characterization z

/-! ## FUST × RH synthesis: primordial mode factorization

The primordial mode z¹ admits z^s · z^{1-s} = z for any s ∈ ℂ (z ≠ 0).
Each RH zero s₀ = 1/2+iγ gives a factorization z = z^{s₀} · z^{1-s₀}
into "sub-universe" modes. These modes:
- Collapse to 1 at z=1 (Big Bang: no trace)
- Vanish at z=0 (void: no trace)
- Oscillate at z=1/2+it (enrichment of the sub-universe) -/

/-- Primordial factorization: z^s · z^{1-s} = z for z ≠ 0 -/
theorem primordial_factorization (z s : ℂ) (hz : z ≠ 0) :
    z ^ s * z ^ (1 - s) = z := by
  rw [← Complex.cpow_add _ _ hz, show s + (1 - s) = 1 from by ring, Complex.cpow_one]

/-- At Big Bang z=1: all sub-universe modes equal 1 -/
theorem enrichment_collapse_bigbang (s : ℂ) :
    (1 : ℂ) ^ s = 1 := Complex.one_cpow s

/-- τ-symmetric sum: z^s + z^{1-s} is invariant under s↔1-s -/
theorem enrichment_tau_symmetric (z s : ℂ) :
    z ^ s + z ^ (1 - s) = z ^ (1 - s) + z ^ s := by ring

/-- At ζ₆: enrichment trivializes because Ψ_M(ζ₆) = 1 -/
theorem enrichment_trivial_zeta6 (s : ℂ) :
    (ζ₆ * (1 - ζ₆)) ^ s = 1 := by
  rw [zeta6_tau_product, Complex.one_cpow]

/-- The τ-product of sub-universe modes recovers the τ-symmetric state -/
theorem tau_product_recovery (z s : ℂ) (hz : z * (1 - z) ≠ 0) :
    (z * (1 - z)) ^ s * (z * (1 - z)) ^ (1 - s) = z * (1 - z) :=
  primordial_factorization (z * (1 - z)) s hz

/-! ## RH zeros as spectral enrichment

The RH zero at s₀ = 1/2+iγ factorizes z¹ = z^{s₀}·z^{1-s₀}.
The two factors z^{1/2+iγ} and z^{1/2-iγ} carry oscillating phases.
Their product is z (primordial), but individually they encode
the frequency γ — the "priming" that the RH zero imparts.

At z=1/2+it on the critical line:
  z^{1/2+iγ} is a function of both t (FUST) and γ (RH).
  τ_z (z→1-z) and τ_RH (s→1-s) both act as conjugation.
  The double critical line (Re z=1/2, Re s=1/2) is the fixed locus
  of BOTH involutions simultaneously. -/

/-- The enrichment at z=1 is mode-independent: all factors equal 1 -/
theorem bigbang_erases_enrichment (s₁ s₂ : ℂ) :
    (1 : ℂ) ^ s₁ = (1 : ℂ) ^ s₂ := by simp [Complex.one_cpow]

/-- Different RH zeros give different factorizations of the same z -/
theorem distinct_factorizations (z : ℂ) (hz : z ≠ 0) (s₁ s₂ : ℂ) :
    z ^ s₁ * z ^ (1 - s₁) = z ^ s₂ * z ^ (1 - s₂) := by
  rw [primordial_factorization z s₁ hz, primordial_factorization z s₂ hz]

/-- The 6 τ-involutions: summary of the FUST × RH structure.
    All six are involutions, and the first three fix Re=1/2 loci. -/
theorem three_tau_involutions :
    (∀ z : ℂ, z + (1 - z) = 1) ∧                -- τ_z trace
    (∀ s : ℂ, s + (1 - s) = 1) ∧                -- τ_RH trace
    (∀ c_A : ℂ, c_A * AF_coeff + (-c_A * AF_coeff) = 0) := -- τ_FUST trace (AF cancels)
  ⟨fun z => by ring, fun s => by ring, fun c_A => by ring⟩

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

/-- AF⊥SY orthogonality: for real s, Fζ(f) splits into
    pure imaginary AF (space) and pure real SY (time). -/
theorem spacetime_orthogonality (f : ℂ → ℂ)
    (hA : ∀ z, (fun w => 5 * Φ_A f w) (starRingEnd ℂ z) =
      starRingEnd ℂ ((fun w => 5 * Φ_A f w) z))
    (hS : ∀ z, Φ_S_int f (starRingEnd ℂ z) = starRingEnd ℂ (Φ_S_int f z))
    (s : ℝ) :
    (AFNum (fun w => 5 * Φ_A f w) (↑s)).re = 0 ∧
    (SymNum (Φ_S_int f) (↑s)).im = 0 :=
  ⟨AFNum_real_pure_im _ hA s, SymNum_real_pure_re _ hS s⟩

/-! ## ℂ-linearity preserves AF⊥SY orthogonality

Schwarz reflection g(z̄) = conj(g(z)) is preserved by:
  - Addition of Schwarz functions
  - Real scalar multiplication
The inner product Re(AF · conj(SY)) = 0 is preserved by complex scaling. -/

/-- Schwarz reflection is preserved by addition -/
theorem schwarz_add (f g : ℂ → ℂ)
    (hf : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hg : ∀ z, g (starRingEnd ℂ z) = starRingEnd ℂ (g z)) :
    ∀ z, (fun w => f w + g w) (starRingEnd ℂ z) =
      starRingEnd ℂ ((fun w => f w + g w) z) := by
  intro z; simp [hf z, hg z, map_add]

/-- Schwarz reflection is preserved by real scalar multiplication -/
theorem schwarz_smul_real (r : ℝ) (f : ℂ → ℂ)
    (hf : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z)) :
    ∀ z, (fun w => (r : ℂ) * f w) (starRingEnd ℂ z) =
      starRingEnd ℂ ((fun w => (r : ℂ) * f w) z) := by
  intro z; simp [hf z, map_mul, Complex.conj_ofReal]

/-- Re(pure_im · conj(pure_re)) = 0 -/
private theorem re_pure_im_mul_conj_pure_re (w v : ℂ)
    (hw : w.re = 0) (hv : v.im = 0) :
    (w * starRingEnd ℂ v).re = 0 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  rw [hw, hv]; ring

/-- Inner product orthogonality: Re(AFNum(f)(s) · conj(SymNum(g)(s))) = 0 -/
theorem AF_SY_inner_product_zero (f g : ℂ → ℂ)
    (hf : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hg : ∀ z, g (starRingEnd ℂ z) = starRingEnd ℂ (g z))
    (s : ℝ) :
    (AFNum f ↑s * starRingEnd ℂ (SymNum g ↑s)).re = 0 :=
  re_pure_im_mul_conj_pure_re _ _
    (AFNum_real_pure_im f hf s) (SymNum_real_pure_re g hg s)

/-- Re(c·w · conj(c·v)) = 0 when w is pure imaginary and v is pure real -/
private theorem re_smul_orthogonal (c w v : ℂ)
    (hw : w.re = 0) (hv : v.im = 0) :
    (c * w * starRingEnd ℂ (c * v)).re = 0 := by
  rw [show starRingEnd ℂ (c * v) = starRingEnd ℂ c * starRingEnd ℂ v from map_mul _ c v]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  rw [hw, hv]; ring

/-- Complex scaling preserves AF⊥SY: Re(c·AF · conj(c·SY)) = 0 -/
theorem AF_SY_orthogonal_smul (c : ℂ) (f g : ℂ → ℂ)
    (hf : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hg : ∀ z, g (starRingEnd ℂ z) = starRingEnd ℂ (g z))
    (s : ℝ) :
    (c * AFNum f ↑s * starRingEnd ℂ (c * SymNum g ↑s)).re = 0 :=
  re_smul_orthogonal c _ _
    (AFNum_real_pure_im f hf s) (SymNum_real_pure_re g hg s)

/-- AF⊥SY for sum of Schwarz functions: pure im + pure im = pure im -/
theorem AF_SY_orthogonal_sum (f g : ℂ → ℂ)
    (hf : ∀ z, f (starRingEnd ℂ z) = starRingEnd ℂ (f z))
    (hg : ∀ z, g (starRingEnd ℂ z) = starRingEnd ℂ (g z))
    (s : ℝ) :
    (AFNum (fun w => f w + g w) ↑s).re = 0 ∧
    (SymNum (fun w => f w + g w) ↑s).im = 0 := by
  constructor
  · rw [AFNum_add]
    have h1 := AFNum_real_pure_im f hf s
    have h2 := AFNum_real_pure_im g hg s
    simp [Complex.add_re, h1, h2]
  · rw [SymNum_add]
    have h1 := SymNum_real_pure_re f hf s
    have h2 := SymNum_real_pure_re g hg s
    simp [Complex.add_im, h1, h2]

/-! ## Spacetime √15 factorization

The AF eigenvalue channel factors as √5·AF_coeff = 2√15·I, combining:
  disc(ℤ[φ]) = 5 → √5 (golden scaling)
  disc(ℤ[ζ₆]) = -3 → i√3 via AF_coeff = 2i√3
Product: i√15 carries the spatial information.
The SY channel (time) uses only ℤ[φ], contributing no imaginary part.

The coprime-6 zeta ζ_{(6)}(s) = ζ(s)·(1-2⁻ˢ)(1-3⁻ˢ) removes the ramified
primes of ℤ[ζ₆], making it the natural state function for ℤ[φ,ζ₆]. -/

private lemma sqrt15_eq : Real.sqrt 15 = Real.sqrt 5 * Real.sqrt 3 := by
  rw [show (15 : ℝ) = 5 * 3 from by norm_num,
      Real.sqrt_mul (by norm_num : (5:ℝ) ≥ 0)]

/-- √5 · AF_coeff = 2√15 · I: disc(ℤ[φ]) · disc(ℤ[ζ₆]) → space channel -/
theorem sqrt5_mul_AF_coeff :
    (↑(Real.sqrt 5) : ℂ) * AF_coeff = ↑(2 * Real.sqrt 15) * Complex.I := by
  rw [AF_coeff_eq, sqrt15_eq]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
               Complex.I_re, Complex.I_im]; ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
               Complex.I_re, Complex.I_im]; ring

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

/-! ## Fζ Channel Decomposition

Fζ = 5z·Dζ decomposes via Φ_A = Diff6+Diff2-Diff4, Φ_S = 2Diff5+Diff3+μDiff2.
The AF channel carries odd-rank operators (Diff6, M4, Diff2)
and the SY channel carries even-rank operators (Diff5, Diff3). -/

/-- Fζ decomposes into AF and SY channels through Nn -/
theorem Fζ_channel_decompose (f : ℂ → ℂ) (z : ℂ) :
    Fζ f z =
    AFNum (fun w => 5 * (Diff6 f w + Diff2 f w - Diff4 f w)) z +
    SymNum (fun w => 5 * (2 * Diff5 f w + Diff3 f w +
      (2 / ((↑φ : ℂ) + 2)) * Diff2 f w)) z := by
  unfold Fζ
  have hA : (fun w => 5 * Φ_A f w) = fun w => 5 * (Diff6 f w + Diff2 f w - Diff4 f w) :=
    funext (fun w => by rw [Φ_A_decompose])
  have hS : Φ_S_int f = fun w => 5 * (2 * Diff5 f w + Diff3 f w +
      (2 / ((↑φ : ℂ) + 2)) * Diff2 f w) :=
    funext (fun w => by rw [Φ_S_int_eq]; unfold Φ_S; ring)
  rw [hA, hS]

end FUST.FζOperator
