/-
Fibonacci Arithmetic: Lucas numbers, D_t vs D6 discrepancy, Fibonacci divisibility.

Key results:
1. Lucas-Binet: L_n = φ^n + ψ^n (Lucas numbers via golden ratio)
2. Lucas-Fibonacci identity: L_n² - 5·F_n² = 4·(-1)^n
3. D_t eigenvalue at t=logφ vs D6Coeff discrepancy formula
4. Fibonacci integrality of D6Coeff/√5
-/
import FUST.SpectralCoefficients
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace FUST.FibonacciArithmetic

open FUST FUST.SpectralCoefficients Real

/-! ## Section 1: Lucas Numbers via Binet Formula -/

section LucasNumbers

/-- Lucas number L_n = φ^n + ψ^n (Binet form) -/
noncomputable def lucasConst (n : ℕ) : ℝ := φ ^ n + ψ ^ n

theorem lucasConst_zero : lucasConst 0 = 2 := by
  simp only [lucasConst, pow_zero]; norm_num

theorem lucasConst_one : lucasConst 1 = 1 := by
  simp only [lucasConst, pow_one]; linarith [phi_add_psi]

theorem lucasConst_two : lucasConst 2 = 3 := by
  simp only [lucasConst]
  rw [golden_ratio_property, psi_sq]
  linarith [phi_add_psi]

theorem lucasConst_three : lucasConst 3 = 4 := by
  simp only [lucasConst]
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
    calc ψ ^ 3 = ψ ^ 2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [psi_sq]
      _ = ψ ^ 2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [psi_sq]
      _ = 2 * ψ + 1 := by ring
  rw [hφ3, hψ3]; linarith [phi_add_psi]

/-- Lucas recurrence: L_{n+2} = L_{n+1} + L_n -/
theorem lucasConst_recurrence (n : ℕ) :
    lucasConst (n + 2) = lucasConst (n + 1) + lucasConst n := by
  simp only [lucasConst]
  have hφ : φ ^ (n + 2) = φ ^ (n + 1) + φ ^ n := by
    calc φ ^ (n + 2) = φ ^ n * φ ^ 2 := by ring
      _ = φ ^ n * (φ + 1) := by rw [golden_ratio_property]
      _ = φ ^ (n + 1) + φ ^ n := by ring
  have hψ : ψ ^ (n + 2) = ψ ^ (n + 1) + ψ ^ n := by
    calc ψ ^ (n + 2) = ψ ^ n * ψ ^ 2 := by ring
      _ = ψ ^ n * (ψ + 1) := by rw [psi_sq]
      _ = ψ ^ (n + 1) + ψ ^ n := by ring
  linarith

/-- Product identity: φ^n · ψ^n = (-1)^n -/
theorem phi_psi_pow_prod (n : ℕ) : φ ^ n * ψ ^ n = (-1 : ℝ) ^ n := by
  rw [← mul_pow, phi_mul_psi]

/-- Lucas-Fibonacci identity: L_n² - 5·F_n² = 4·(-1)^n -/
theorem lucas_fibonacci_identity (n : ℕ) :
    lucasConst n ^ 2 - 5 * FStructureConst n ^ 2 = 4 * (-1 : ℝ) ^ n := by
  simp only [lucasConst, FStructureConst]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
  have hsqrt5_ne : Real.sqrt 5 ≠ 0 := by positivity
  have hprod := phi_psi_pow_prod n
  field_simp
  nlinarith [h5, hprod, sq_nonneg (φ ^ n), sq_nonneg (ψ ^ n)]

/-- FStructureConst matches Nat.fib (from Mathlib Binet) -/
theorem FStructureConst_eq_fib (n : ℕ) : FStructureConst n = Nat.fib n := by
  simp only [FStructureConst]
  have h : φ = goldenRatio := rfl
  have h' : ψ = goldenConj := rfl
  rw [h, h', coe_fib_eq n]

end LucasNumbers

/-! ## Section 2: Continuous D_t Eigenvalue

The continuous analog of D6 uses sinh instead of Fibonacci:
  D_t(n) = 2sinh(3nt) - 6sinh(2nt) + 2sinh(nt)

At t = log(φ), we have φ^{-1} = -ψ (from φψ = -1), so:
  2sinh(kn·logφ) = φ^{kn} - φ^{-kn} = φ^{kn} - (-ψ)^{kn}

The difference from D6Coeff arises because (-ψ)^{kn} ≠ ψ^{kn} for odd kn. -/

section ContinuousDiscrete

/-- Continuous D_t eigenvalue at t=logφ:
    φ^{3n} - (-ψ)^{3n} - 3(φ^{2n} - (-ψ)^{2n}) + φ^n - (-ψ)^n -/
noncomputable def DtEigenvalue (n : ℕ) : ℝ :=
  φ ^ (3 * n) - (-ψ) ^ (3 * n) - 3 * (φ ^ (2 * n) - (-ψ) ^ (2 * n)) +
  φ ^ n - (-ψ) ^ n

/-- (-ψ)^{2k} = ψ^{2k} (even powers absorb sign) -/
theorem neg_psi_even_pow (k : ℕ) : (-ψ) ^ (2 * k) = ψ ^ (2 * k) :=
  (even_two_mul k).neg_pow ψ

/-- For even n: D_t = D6Coeff exactly -/
theorem DtEigenvalue_even (n : ℕ) (hn : Even n) :
    DtEigenvalue n = D6Coeff n := by
  simp only [DtEigenvalue, D6Coeff]
  have h3 : Even (3 * n) := hn.mul_left 3
  have h2 : Even (2 * n) := even_two_mul n
  rw [h3.neg_pow, h2.neg_pow, hn.neg_pow]; ring

/-- For odd n: (-ψ)^n = -ψ^n -/
theorem neg_psi_odd_pow (n : ℕ) (hn : Odd n) : (-ψ) ^ n = -(ψ ^ n) := by
  rw [neg_pow, Odd.neg_one_pow hn]; ring

/-- Discrepancy for odd n: D_t - D6 = 2(ψ^{3n} + ψ^n) -/
theorem DtEigenvalue_odd_discrepancy (n : ℕ) (hn : Odd n) :
    DtEigenvalue n = D6Coeff n + 2 * (ψ ^ (3 * n) + ψ ^ n) := by
  simp only [DtEigenvalue, D6Coeff]
  have h3n_odd : Odd (3 * n) := by rw [Nat.odd_mul]; exact ⟨⟨1, rfl⟩, hn⟩
  rw [neg_psi_odd_pow _ h3n_odd, neg_psi_even_pow, neg_psi_odd_pow _ hn]
  ring

/-- Unified discrepancy formula:
    D_t(n) = D6Coeff(n) + (1 - (-1)^n) · (ψ^{3n} + ψ^n) -/
theorem DtEigenvalue_unified (n : ℕ) :
    DtEigenvalue n = D6Coeff n + (1 - (-1 : ℝ) ^ n) * (ψ ^ (3 * n) + ψ ^ n) := by
  rcases Nat.even_or_odd n with hn | hn
  · rw [DtEigenvalue_even n hn, Even.neg_one_pow hn]; ring
  · rw [DtEigenvalue_odd_discrepancy n hn, Odd.neg_one_pow hn]; ring

/-- The discrepancy decays exponentially: |ψ^{3n} + ψ^n| ≤ 2|ψ|^n -/
theorem discrepancy_bound (n : ℕ) :
    |ψ ^ (3 * n) + ψ ^ n| ≤ 2 * |ψ| ^ n := by
  have h3n : |ψ ^ (3 * n)| = |ψ| ^ (3 * n) := abs_pow ψ (3 * n)
  have hn' : |ψ ^ n| = |ψ| ^ n := abs_pow ψ n
  have h_abs_lt : |ψ| < 1 := abs_psi_lt_one
  have h3le : |ψ| ^ (3 * n) ≤ |ψ| ^ n := by
    apply pow_le_pow_of_le_one (abs_nonneg _) (le_of_lt h_abs_lt); omega
  calc |ψ ^ (3 * n) + ψ ^ n| ≤ |ψ ^ (3 * n)| + |ψ ^ n| := abs_add_le _ _
    _ = |ψ| ^ (3 * n) + |ψ| ^ n := by rw [h3n, hn']
    _ ≤ |ψ| ^ n + |ψ| ^ n := by linarith [h3le]
    _ = 2 * |ψ| ^ n := by ring

/-- Discrepancy vanishes in limit: |ψ|^n < 1 for n ≥ 1 -/
theorem abs_psi_pow_lt (n : ℕ) (hn : 1 ≤ n) : |ψ| ^ n < 1 :=
  pow_lt_one₀ (abs_nonneg _) abs_psi_lt_one (by omega)

end ContinuousDiscrete

/-! ## Section 3: D6Coeff Integrality

D6Coeff(n) / √5 = F_{3n} - 3F_{2n} + F_n ∈ ℤ -/

section Integrality

/-- The Fibonacci combination F_{3n} - 3F_{2n} + F_n is an integer -/
def fibCombination (n : ℕ) : ℤ :=
  Nat.fib (3 * n) - 3 * Nat.fib (2 * n) + Nat.fib n

/-- D6Coeff(n) = √5 · fibCombination(n) -/
theorem D6Coeff_eq_sqrt5_mul_int (n : ℕ) :
    D6Coeff n = Real.sqrt 5 * (fibCombination n : ℝ) := by
  rw [D6Coeff_fibonacci]
  simp only [fibCombination, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Int.cast_ofNat]

theorem fibCombination_zero : fibCombination 0 = 0 := by
  simp [fibCombination]

theorem fibCombination_one : fibCombination 1 = 0 := by
  decide

theorem fibCombination_two : fibCombination 2 = 0 := by
  decide

theorem fibCombination_three : fibCombination 3 = 12 := by
  decide

theorem fibCombination_four : fibCombination 4 = 84 := by
  decide

theorem fibCombination_five : fibCombination 5 = 450 := by
  decide

/-- fibCombination vanishes iff n ≤ 2 -/
theorem fibCombination_eq_zero_iff (n : ℕ) :
    fibCombination n = 0 ↔ n ≤ 2 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hD6 := D6Coeff_ne_zero_of_ge_three n hne
    rw [D6Coeff_eq_sqrt5_mul_int] at hD6
    simp [h] at hD6
  · intro h
    interval_cases n
    · exact fibCombination_zero
    · exact fibCombination_one
    · exact fibCombination_two

end Integrality

/-! ## Section 4: Fibonacci Strong Divisibility

F_m | F_n when m | n. This is Nat.fib_dvd from Mathlib. -/

section FibonacciDivisibility

/-- Fibonacci strong divisibility (from Mathlib) -/
theorem fib_dvd_of_dvd (m n : ℕ) (h : m ∣ n) : Nat.fib m ∣ Nat.fib n :=
  Nat.fib_dvd m n h

/-- Consecutive Fibonacci numbers are coprime (from Mathlib) -/
theorem fib_coprime_succ (n : ℕ) : Nat.Coprime (Nat.fib n) (Nat.fib (n + 1)) :=
  Nat.fib_coprime_fib_succ n

/-- GCD of Fibonacci = Fibonacci of GCD (from Mathlib) -/
theorem fib_gcd (m n : ℕ) : Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) :=
  Nat.fib_gcd m n

/-- 3 | n → F_3 = 2 divides F_n -/
theorem fib_even_of_three_dvd (n : ℕ) (h : 3 ∣ n) : 2 ∣ Nat.fib n := by
  have h3 : Nat.fib 3 = 2 := by decide
  have := fib_dvd_of_dvd 3 n h
  rwa [h3] at this

/-- 4 | n → F_4 = 3 divides F_n -/
theorem fib_three_dvd_of_four_dvd (n : ℕ) (h : 4 ∣ n) : 3 ∣ Nat.fib n := by
  have h4 : Nat.fib 4 = 3 := by decide
  have := fib_dvd_of_dvd 4 n h
  rwa [h4] at this

/-- 5 | n → F_5 = 5 divides F_n -/
theorem fib_five_dvd_of_five_dvd (n : ℕ) (h : 5 ∣ n) : 5 ∣ Nat.fib n := by
  have h5 : Nat.fib 5 = 5 := by decide
  have := fib_dvd_of_dvd 5 n h
  rwa [h5] at this

end FibonacciDivisibility

/-! ## Section 5: D6Coeff via Lucas and Fibonacci

Express D6Coeff using both Fibonacci (φ^n-ψ^n)/√5 and Lucas (φ^n+ψ^n). -/

section LucasFibonacci

/-- D6Coeff via triple factorization with Lucas:
    C_n = (φ^n-ψ^n) · (L_{2n} - 3·L_n + (-1)^n + 1) -/
theorem D6Coeff_lucas_fibonacci (n : ℕ) :
    D6Coeff n = (φ ^ n - ψ ^ n) *
      (lucasConst (2 * n) - 3 * lucasConst n + (-1 : ℝ) ^ n + 1) := by
  have h := D6Coeff_factored n
  simp only [lucasConst]; rw [h]; ring

/-- D_t eigenvalue via Lucas numbers (for odd n):
    D_t(n) = L_{3n} - 3·(φ^{2n}-ψ^{2n}) + L_n -/
theorem DtEigenvalue_odd_via_lucas (n : ℕ) (hn : Odd n) :
    DtEigenvalue n = lucasConst (3 * n) - 3 * (φ ^ (2 * n) - ψ ^ (2 * n)) +
      lucasConst n := by
  simp only [DtEigenvalue, lucasConst]
  have h3n_odd : Odd (3 * n) := by rw [Nat.odd_mul]; exact ⟨⟨1, rfl⟩, hn⟩
  rw [neg_psi_odd_pow _ h3n_odd, neg_psi_even_pow, neg_psi_odd_pow _ hn]
  ring

/-- D_t uses Lucas where D6 uses Fibonacci (for odd harmonics) -/
theorem Dt_lucas_D6_fibonacci_odd (n : ℕ) (hn : Odd n) :
    DtEigenvalue n - D6Coeff n = 2 * ψ ^ (3 * n) + 2 * ψ ^ n := by
  have := DtEigenvalue_odd_discrepancy n hn; linarith

end LucasFibonacci

/-! ## Section 6: Summary -/

/-- Complete characterization of continuous-discrete discrepancy -/
theorem continuous_discrete_summary :
    (∀ n, Even n → DtEigenvalue n = D6Coeff n) ∧
    (∀ n, Odd n → DtEigenvalue n = D6Coeff n + 2 * (ψ ^ (3 * n) + ψ ^ n)) ∧
    (∀ n, DtEigenvalue n = D6Coeff n + (1 - (-1 : ℝ) ^ n) * (ψ ^ (3 * n) + ψ ^ n)) ∧
    (∀ n, |ψ ^ (3 * n) + ψ ^ n| ≤ 2 * |ψ| ^ n) ∧
    (∀ n, lucasConst n ^ 2 - 5 * FStructureConst n ^ 2 = 4 * (-1 : ℝ) ^ n) :=
  ⟨DtEigenvalue_even,
   DtEigenvalue_odd_discrepancy,
   DtEigenvalue_unified,
   discrepancy_bound,
   lucas_fibonacci_identity⟩

end FUST.FibonacciArithmetic
