/-
D₁₂: 12-point alternating DFT on ζ₁₂ = e^{iπ/6}, detecting mode 6.
Euler operator θ = z·d/dz: the unique complete detector (ker = {constants}).
-/
import FUST.Zeta6
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace FUST.EulerOperator

open Complex FUST.Zeta6

attribute [local ext] Complex.ext

section D12

/-- Primitive 12th root of unity: ζ₁₂ = e^{iπ/6} = (√3/2 + i/2) -/
noncomputable def ζ₁₂ : ℂ := ⟨Real.sqrt 3 / 2, 1 / 2⟩

/-- ζ₁₂² = ζ₆ -/
theorem zeta12_sq : ζ₁₂ ^ 2 = ζ₆ := by
  ext <;> simp [ζ₁₂, ζ₆, sq, mul_re, mul_im]
  · have h := sqrt3_sq; nlinarith
  · ring

/-- ζ₁₂⁶ = -1 -/
theorem zeta12_pow_six : ζ₁₂ ^ 6 = -1 := by
  have : ζ₁₂ ^ 6 = (ζ₁₂ ^ 2) ^ 3 := by ring
  rw [this, zeta12_sq, zeta6_cubed]

/-- ζ₁₂¹² = 1 -/
theorem zeta12_pow_twelve : ζ₁₂ ^ 12 = 1 := by
  have : ζ₁₂ ^ 12 = (ζ₁₂ ^ 6) ^ 2 := by ring
  rw [this, zeta12_pow_six]; norm_num

/-- Reduction: ζ₁₂^{m+12} = ζ₁₂^m -/
private theorem zeta12_reduce (m : ℕ) : ζ₁₂ ^ (m + 12) = ζ₁₂ ^ m := by
  have : ζ₁₂ ^ (m + 12) = ζ₁₂ ^ m * ζ₁₂ ^ 12 := by ring
  rw [this, zeta12_pow_twelve, mul_one]

/-- General reduction: ζ₁₂^{m+12q} = ζ₁₂^m -/
private theorem zeta12_reduce_mod (m q : ℕ) : ζ₁₂ ^ (m + 12 * q) = ζ₁₂ ^ m := by
  induction q with
  | zero => simp
  | succ q ih =>
    have : m + 12 * (q + 1) = (m + 12 * q) + 12 := by omega
    rw [this, zeta12_reduce, ih]

/-- ζ₁₂³ = i -/
theorem zeta12_cubed : ζ₁₂ ^ 3 = I := by
  have : ζ₁₂ ^ 3 = ζ₁₂ ^ 2 * ζ₁₂ := by ring
  rw [this, zeta12_sq]
  ext <;> simp [ζ₆, ζ₁₂, mul_re, mul_im, I]
  · have h := sqrt3_sq; nlinarith
  · have h := sqrt3_sq; nlinarith

/-- N12: 12-point alternating sum at 12th roots of unity.
    Extracts DFT mode 6: detects n ≡ 6 mod 12. -/
noncomputable def N12 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z - f (ζ₁₂ * z) + f (ζ₁₂ ^ 2 * z) - f (ζ₁₂ ^ 3 * z) +
  f (ζ₁₂ ^ 4 * z) - f (ζ₁₂ ^ 5 * z) + f (ζ₁₂ ^ 6 * z) -
  f (ζ₁₂ ^ 7 * z) + f (ζ₁₂ ^ 8 * z) - f (ζ₁₂ ^ 9 * z) +
  f (ζ₁₂ ^ 10 * z) - f (ζ₁₂ ^ 11 * z)

noncomputable def D12 (f : ℂ → ℂ) (z : ℂ) : ℂ := N12 f z / 12

/-- N12 annihilates constants -/
theorem N12_const (c : ℂ) (z : ℂ) : N12 (fun _ => c) z = 0 := by
  unfold N12; ring

/-- ζ₁₂^{k+6} = -ζ₁₂^k (half-period negation) -/
private theorem zeta12_half_period (k : ℕ) : ζ₁₂ ^ (k + 6) = -(ζ₁₂ ^ k) := by
  have : ζ₁₂ ^ (k + 6) = ζ₁₂ ^ k * ζ₁₂ ^ 6 := by ring
  rw [this, zeta12_pow_six]; ring

/-- Alternating 12th-root sum at n=1 vanishes -/
private theorem alt12_sum_one :
    (1 : ℂ) - ζ₁₂ + ζ₁₂ ^ 2 - ζ₁₂ ^ 3 + ζ₁₂ ^ 4 - ζ₁₂ ^ 5 +
    ζ₁₂ ^ 6 - ζ₁₂ ^ 7 + ζ₁₂ ^ 8 - ζ₁₂ ^ 9 + ζ₁₂ ^ 10 - ζ₁₂ ^ 11 = 0 := by
  have h6 := zeta12_pow_six
  have h7 : ζ₁₂ ^ 7 = -(ζ₁₂ ^ 1) := zeta12_half_period 1
  have h8 : ζ₁₂ ^ 8 = -(ζ₁₂ ^ 2) := zeta12_half_period 2
  have h9 : ζ₁₂ ^ 9 = -(ζ₁₂ ^ 3) := zeta12_half_period 3
  have h10 : ζ₁₂ ^ 10 = -(ζ₁₂ ^ 4) := zeta12_half_period 4
  have h11 : ζ₁₂ ^ 11 = -(ζ₁₂ ^ 5) := zeta12_half_period 5
  rw [h6, h7, h8, h9, h10, h11]; ring

theorem N12_ker_one (z : ℂ) : N12 (fun w => w ^ 1) z = 0 := by
  simp only [N12]
  have : z ^ 1 - (ζ₁₂ * z) ^ 1 + (ζ₁₂ ^ 2 * z) ^ 1 - (ζ₁₂ ^ 3 * z) ^ 1 +
    (ζ₁₂ ^ 4 * z) ^ 1 - (ζ₁₂ ^ 5 * z) ^ 1 + (ζ₁₂ ^ 6 * z) ^ 1 -
    (ζ₁₂ ^ 7 * z) ^ 1 + (ζ₁₂ ^ 8 * z) ^ 1 - (ζ₁₂ ^ 9 * z) ^ 1 +
    (ζ₁₂ ^ 10 * z) ^ 1 - (ζ₁₂ ^ 11 * z) ^ 1 =
    ((1 : ℂ) - ζ₁₂ + ζ₁₂ ^ 2 - ζ₁₂ ^ 3 + ζ₁₂ ^ 4 - ζ₁₂ ^ 5 +
     ζ₁₂ ^ 6 - ζ₁₂ ^ 7 + ζ₁₂ ^ 8 - ζ₁₂ ^ 9 + ζ₁₂ ^ 10 - ζ₁₂ ^ 11) * z := by ring
  rw [this, alt12_sum_one, zero_mul]

/-- For n=2: reduce all powers mod 12, then use half-period cancellation -/
private theorem alt12_sum_two :
    (1 : ℂ) - ζ₁₂ ^ 2 + ζ₁₂ ^ 4 - ζ₁₂ ^ 6 + ζ₁₂ ^ 8 - ζ₁₂ ^ 10 +
    ζ₁₂ ^ 12 - ζ₁₂ ^ 14 + ζ₁₂ ^ 16 - ζ₁₂ ^ 18 + ζ₁₂ ^ 20 - ζ₁₂ ^ 22 = 0 := by
  have h12 := zeta12_pow_twelve
  have h14 : ζ₁₂ ^ 14 = ζ₁₂ ^ 2 := by
    rw [show (14 : ℕ) = 2 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h16 : ζ₁₂ ^ 16 = ζ₁₂ ^ 4 := by
    rw [show (16 : ℕ) = 4 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h18 : ζ₁₂ ^ 18 = ζ₁₂ ^ 6 := by
    rw [show (18 : ℕ) = 6 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h20 : ζ₁₂ ^ 20 = ζ₁₂ ^ 8 := by
    rw [show (20 : ℕ) = 8 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h22 : ζ₁₂ ^ 22 = ζ₁₂ ^ 10 := by
    rw [show (22 : ℕ) = 10 + 12 * 1 from by omega, zeta12_reduce_mod]
  rw [h12, h14, h16, h18, h20, h22]
  have h6 := zeta12_pow_six
  have h8 : ζ₁₂ ^ 8 = -(ζ₁₂ ^ 2) := zeta12_half_period 2
  have h10 : ζ₁₂ ^ 10 = -(ζ₁₂ ^ 4) := zeta12_half_period 4
  rw [h6, h8, h10]
  have h4 : ζ₁₂ ^ 4 = (ζ₁₂ ^ 2) ^ 2 := by ring
  rw [h4, zeta12_sq, zeta6_sq]; ring

theorem N12_ker_two (z : ℂ) : N12 (fun w => w ^ 2) z = 0 := by
  simp only [N12]
  have : z ^ 2 - (ζ₁₂ * z) ^ 2 + (ζ₁₂ ^ 2 * z) ^ 2 - (ζ₁₂ ^ 3 * z) ^ 2 +
    (ζ₁₂ ^ 4 * z) ^ 2 - (ζ₁₂ ^ 5 * z) ^ 2 + (ζ₁₂ ^ 6 * z) ^ 2 -
    (ζ₁₂ ^ 7 * z) ^ 2 + (ζ₁₂ ^ 8 * z) ^ 2 - (ζ₁₂ ^ 9 * z) ^ 2 +
    (ζ₁₂ ^ 10 * z) ^ 2 - (ζ₁₂ ^ 11 * z) ^ 2 =
    ((1 : ℂ) - ζ₁₂ ^ 2 + ζ₁₂ ^ 4 - ζ₁₂ ^ 6 + ζ₁₂ ^ 8 - ζ₁₂ ^ 10 +
     ζ₁₂ ^ 12 - ζ₁₂ ^ 14 + ζ₁₂ ^ 16 - ζ₁₂ ^ 18 + ζ₁₂ ^ 20 - ζ₁₂ ^ 22) * z ^ 2 := by ring
  rw [this, alt12_sum_two, zero_mul]

private theorem alt12_sum_three :
    (1 : ℂ) - ζ₁₂ ^ 3 + ζ₁₂ ^ 6 - ζ₁₂ ^ 9 + ζ₁₂ ^ 12 - ζ₁₂ ^ 15 +
    ζ₁₂ ^ 18 - ζ₁₂ ^ 21 + ζ₁₂ ^ 24 - ζ₁₂ ^ 27 + ζ₁₂ ^ 30 - ζ₁₂ ^ 33 = 0 := by
  have h12 := zeta12_pow_twelve
  have h15 : ζ₁₂ ^ 15 = ζ₁₂ ^ 3 := by
    rw [show (15 : ℕ) = 3 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h18 : ζ₁₂ ^ 18 = ζ₁₂ ^ 6 := by
    rw [show (18 : ℕ) = 6 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h21 : ζ₁₂ ^ 21 = ζ₁₂ ^ 9 := by
    rw [show (21 : ℕ) = 9 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h24 : ζ₁₂ ^ 24 = 1 := by
    rw [show (24 : ℕ) = 0 + 12 * 2 from by omega, zeta12_reduce_mod]; simp
  have h27 : ζ₁₂ ^ 27 = ζ₁₂ ^ 3 := by
    rw [show (27 : ℕ) = 3 + 12 * 2 from by omega, zeta12_reduce_mod]
  have h30 : ζ₁₂ ^ 30 = ζ₁₂ ^ 6 := by
    rw [show (30 : ℕ) = 6 + 12 * 2 from by omega, zeta12_reduce_mod]
  have h33 : ζ₁₂ ^ 33 = ζ₁₂ ^ 9 := by
    rw [show (33 : ℕ) = 9 + 12 * 2 from by omega, zeta12_reduce_mod]
  rw [h12, h15, h18, h21, h24, h27, h30, h33]
  have h6 := zeta12_pow_six
  have h9 : ζ₁₂ ^ 9 = -(ζ₁₂ ^ 3) := zeta12_half_period 3
  rw [h6, h9]; ring

/-- N12 annihilates z³ (mode 3 is invisible to D₁₂) -/
theorem N12_ker_three (z : ℂ) : N12 (fun w => w ^ 3) z = 0 := by
  simp only [N12]
  have : z ^ 3 - (ζ₁₂ * z) ^ 3 + (ζ₁₂ ^ 2 * z) ^ 3 - (ζ₁₂ ^ 3 * z) ^ 3 +
    (ζ₁₂ ^ 4 * z) ^ 3 - (ζ₁₂ ^ 5 * z) ^ 3 + (ζ₁₂ ^ 6 * z) ^ 3 -
    (ζ₁₂ ^ 7 * z) ^ 3 + (ζ₁₂ ^ 8 * z) ^ 3 - (ζ₁₂ ^ 9 * z) ^ 3 +
    (ζ₁₂ ^ 10 * z) ^ 3 - (ζ₁₂ ^ 11 * z) ^ 3 =
    ((1 : ℂ) - ζ₁₂ ^ 3 + ζ₁₂ ^ 6 - ζ₁₂ ^ 9 + ζ₁₂ ^ 12 - ζ₁₂ ^ 15 +
     ζ₁₂ ^ 18 - ζ₁₂ ^ 21 + ζ₁₂ ^ 24 - ζ₁₂ ^ 27 + ζ₁₂ ^ 30 - ζ₁₂ ^ 33) * z ^ 3 := by ring
  rw [this, alt12_sum_three, zero_mul]

private theorem alt12_sum_four :
    (1 : ℂ) - ζ₁₂ ^ 4 + ζ₁₂ ^ 8 - ζ₁₂ ^ 12 + ζ₁₂ ^ 16 - ζ₁₂ ^ 20 +
    ζ₁₂ ^ 24 - ζ₁₂ ^ 28 + ζ₁₂ ^ 32 - ζ₁₂ ^ 36 + ζ₁₂ ^ 40 - ζ₁₂ ^ 44 = 0 := by
  have h12 := zeta12_pow_twelve
  have h16 : ζ₁₂ ^ 16 = ζ₁₂ ^ 4 := by
    rw [show (16 : ℕ) = 4 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h20 : ζ₁₂ ^ 20 = ζ₁₂ ^ 8 := by
    rw [show (20 : ℕ) = 8 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h24 : ζ₁₂ ^ 24 = 1 := by
    rw [show (24 : ℕ) = 0 + 12 * 2 from by omega, zeta12_reduce_mod]; simp
  have h28 : ζ₁₂ ^ 28 = ζ₁₂ ^ 4 := by
    rw [show (28 : ℕ) = 4 + 12 * 2 from by omega, zeta12_reduce_mod]
  have h32 : ζ₁₂ ^ 32 = ζ₁₂ ^ 8 := by
    rw [show (32 : ℕ) = 8 + 12 * 2 from by omega, zeta12_reduce_mod]
  have h36 : ζ₁₂ ^ 36 = 1 := by
    rw [show (36 : ℕ) = 0 + 12 * 3 from by omega, zeta12_reduce_mod]; simp
  have h40 : ζ₁₂ ^ 40 = ζ₁₂ ^ 4 := by
    rw [show (40 : ℕ) = 4 + 12 * 3 from by omega, zeta12_reduce_mod]
  have h44 : ζ₁₂ ^ 44 = ζ₁₂ ^ 8 := by
    rw [show (44 : ℕ) = 8 + 12 * 3 from by omega, zeta12_reduce_mod]
  have h8' : ζ₁₂ ^ 8 = -(ζ₁₂ ^ 2) := zeta12_half_period 2
  rw [h12, h16, h20, h24, h28, h32, h36, h40, h44, h8']
  have h4 : ζ₁₂ ^ 4 = (ζ₁₂ ^ 2) ^ 2 := by ring
  rw [h4, zeta12_sq, zeta6_sq]; ring

theorem N12_ker_four (z : ℂ) : N12 (fun w => w ^ 4) z = 0 := by
  simp only [N12]
  have : z ^ 4 - (ζ₁₂ * z) ^ 4 + (ζ₁₂ ^ 2 * z) ^ 4 - (ζ₁₂ ^ 3 * z) ^ 4 +
    (ζ₁₂ ^ 4 * z) ^ 4 - (ζ₁₂ ^ 5 * z) ^ 4 + (ζ₁₂ ^ 6 * z) ^ 4 -
    (ζ₁₂ ^ 7 * z) ^ 4 + (ζ₁₂ ^ 8 * z) ^ 4 - (ζ₁₂ ^ 9 * z) ^ 4 +
    (ζ₁₂ ^ 10 * z) ^ 4 - (ζ₁₂ ^ 11 * z) ^ 4 =
    ((1 : ℂ) - ζ₁₂ ^ 4 + ζ₁₂ ^ 8 - ζ₁₂ ^ 12 + ζ₁₂ ^ 16 - ζ₁₂ ^ 20 +
     ζ₁₂ ^ 24 - ζ₁₂ ^ 28 + ζ₁₂ ^ 32 - ζ₁₂ ^ 36 + ζ₁₂ ^ 40 - ζ₁₂ ^ 44) * z ^ 4 := by ring
  rw [this, alt12_sum_four, zero_mul]

private theorem alt12_sum_five :
    (1 : ℂ) - ζ₁₂ ^ 5 + ζ₁₂ ^ 10 - ζ₁₂ ^ 15 + ζ₁₂ ^ 20 - ζ₁₂ ^ 25 +
    ζ₁₂ ^ 30 - ζ₁₂ ^ 35 + ζ₁₂ ^ 40 - ζ₁₂ ^ 45 + ζ₁₂ ^ 50 - ζ₁₂ ^ 55 = 0 := by
  have h15 : ζ₁₂ ^ 15 = ζ₁₂ ^ 3 := by
    rw [show (15 : ℕ) = 3 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h20 : ζ₁₂ ^ 20 = ζ₁₂ ^ 8 := by
    rw [show (20 : ℕ) = 8 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h25 : ζ₁₂ ^ 25 = ζ₁₂ ^ 1 := by
    rw [show (25 : ℕ) = 1 + 12 * 2 from by omega, zeta12_reduce_mod]
  have h30 : ζ₁₂ ^ 30 = ζ₁₂ ^ 6 := by
    rw [show (30 : ℕ) = 6 + 12 * 2 from by omega, zeta12_reduce_mod]
  have h35 : ζ₁₂ ^ 35 = ζ₁₂ ^ 11 := by
    rw [show (35 : ℕ) = 11 + 12 * 2 from by omega, zeta12_reduce_mod]
  have h40 : ζ₁₂ ^ 40 = ζ₁₂ ^ 4 := by
    rw [show (40 : ℕ) = 4 + 12 * 3 from by omega, zeta12_reduce_mod]
  have h45 : ζ₁₂ ^ 45 = ζ₁₂ ^ 9 := by
    rw [show (45 : ℕ) = 9 + 12 * 3 from by omega, zeta12_reduce_mod]
  have h50 : ζ₁₂ ^ 50 = ζ₁₂ ^ 2 := by
    rw [show (50 : ℕ) = 2 + 12 * 4 from by omega, zeta12_reduce_mod]
  have h55 : ζ₁₂ ^ 55 = ζ₁₂ ^ 7 := by
    rw [show (55 : ℕ) = 7 + 12 * 4 from by omega, zeta12_reduce_mod]
  have h6 := zeta12_pow_six
  have h7 : ζ₁₂ ^ 7 = -(ζ₁₂ ^ 1) := zeta12_half_period 1
  have h8 : ζ₁₂ ^ 8 = -(ζ₁₂ ^ 2) := zeta12_half_period 2
  have h9 : ζ₁₂ ^ 9 = -(ζ₁₂ ^ 3) := zeta12_half_period 3
  have h10' : ζ₁₂ ^ 10 = -(ζ₁₂ ^ 4) := zeta12_half_period 4
  have h11 : ζ₁₂ ^ 11 = -(ζ₁₂ ^ 5) := zeta12_half_period 5
  rw [h15, h20, h25, h30, h35, h40, h45, h50, h55]
  rw [h6, h7, h8, h9, h10', h11]
  have h4 : ζ₁₂ ^ 4 = (ζ₁₂ ^ 2) ^ 2 := by ring
  rw [h4, zeta12_sq, zeta6_sq]; ring

theorem N12_ker_five (z : ℂ) : N12 (fun w => w ^ 5) z = 0 := by
  simp only [N12]
  have : z ^ 5 - (ζ₁₂ * z) ^ 5 + (ζ₁₂ ^ 2 * z) ^ 5 - (ζ₁₂ ^ 3 * z) ^ 5 +
    (ζ₁₂ ^ 4 * z) ^ 5 - (ζ₁₂ ^ 5 * z) ^ 5 + (ζ₁₂ ^ 6 * z) ^ 5 -
    (ζ₁₂ ^ 7 * z) ^ 5 + (ζ₁₂ ^ 8 * z) ^ 5 - (ζ₁₂ ^ 9 * z) ^ 5 +
    (ζ₁₂ ^ 10 * z) ^ 5 - (ζ₁₂ ^ 11 * z) ^ 5 =
    ((1 : ℂ) - ζ₁₂ ^ 5 + ζ₁₂ ^ 10 - ζ₁₂ ^ 15 + ζ₁₂ ^ 20 - ζ₁₂ ^ 25 +
     ζ₁₂ ^ 30 - ζ₁₂ ^ 35 + ζ₁₂ ^ 40 - ζ₁₂ ^ 45 + ζ₁₂ ^ 50 - ζ₁₂ ^ 55) * z ^ 5 := by ring
  rw [this, alt12_sum_five, zero_mul]

/-- Alternating sum at n=6: ζ₁₂^{6k} = (-1)^k, so Σ(-1)^k·(-1)^k = 12 -/
private theorem alt12_sum_six :
    (1 : ℂ) - ζ₁₂ ^ 6 + ζ₁₂ ^ 12 - ζ₁₂ ^ 18 + ζ₁₂ ^ 24 - ζ₁₂ ^ 30 +
    ζ₁₂ ^ 36 - ζ₁₂ ^ 42 + ζ₁₂ ^ 48 - ζ₁₂ ^ 54 + ζ₁₂ ^ 60 - ζ₁₂ ^ 66 = 12 := by
  have h6 := zeta12_pow_six
  have h12 := zeta12_pow_twelve
  have h18 : ζ₁₂ ^ 18 = ζ₁₂ ^ 6 := by
    rw [show (18 : ℕ) = 6 + 12 * 1 from by omega, zeta12_reduce_mod]
  have h24 : ζ₁₂ ^ 24 = 1 := by
    rw [show (24 : ℕ) = 0 + 12 * 2 from by omega, zeta12_reduce_mod]; simp
  have h30 : ζ₁₂ ^ 30 = ζ₁₂ ^ 6 := by
    rw [show (30 : ℕ) = 6 + 12 * 2 from by omega, zeta12_reduce_mod]
  have h36 : ζ₁₂ ^ 36 = 1 := by
    rw [show (36 : ℕ) = 0 + 12 * 3 from by omega, zeta12_reduce_mod]; simp
  have h42 : ζ₁₂ ^ 42 = ζ₁₂ ^ 6 := by
    rw [show (42 : ℕ) = 6 + 12 * 3 from by omega, zeta12_reduce_mod]
  have h48 : ζ₁₂ ^ 48 = 1 := by
    rw [show (48 : ℕ) = 0 + 12 * 4 from by omega, zeta12_reduce_mod]; simp
  have h54 : ζ₁₂ ^ 54 = ζ₁₂ ^ 6 := by
    rw [show (54 : ℕ) = 6 + 12 * 4 from by omega, zeta12_reduce_mod]
  have h60 : ζ₁₂ ^ 60 = 1 := by
    rw [show (60 : ℕ) = 0 + 12 * 5 from by omega, zeta12_reduce_mod]; simp
  have h66 : ζ₁₂ ^ 66 = ζ₁₂ ^ 6 := by
    rw [show (66 : ℕ) = 6 + 12 * 5 from by omega, zeta12_reduce_mod]
  rw [h18, h30, h42, h54, h66, h12, h24, h36, h48, h60, h6]; norm_num

/-- N12[z⁶] = 12z⁶ -/
theorem N12_detects_six (z : ℂ) : N12 (fun w => w ^ 6) z = 12 * z ^ 6 := by
  simp only [N12]
  have : z ^ 6 - (ζ₁₂ * z) ^ 6 + (ζ₁₂ ^ 2 * z) ^ 6 - (ζ₁₂ ^ 3 * z) ^ 6 +
    (ζ₁₂ ^ 4 * z) ^ 6 - (ζ₁₂ ^ 5 * z) ^ 6 + (ζ₁₂ ^ 6 * z) ^ 6 -
    (ζ₁₂ ^ 7 * z) ^ 6 + (ζ₁₂ ^ 8 * z) ^ 6 - (ζ₁₂ ^ 9 * z) ^ 6 +
    (ζ₁₂ ^ 10 * z) ^ 6 - (ζ₁₂ ^ 11 * z) ^ 6 =
    ((1 : ℂ) - ζ₁₂ ^ 6 + ζ₁₂ ^ 12 - ζ₁₂ ^ 18 + ζ₁₂ ^ 24 - ζ₁₂ ^ 30 +
     ζ₁₂ ^ 36 - ζ₁₂ ^ 42 + ζ₁₂ ^ 48 - ζ₁₂ ^ 54 + ζ₁₂ ^ 60 - ζ₁₂ ^ 66) * z ^ 6 := by ring
  rw [this, alt12_sum_six]

/-- D12[z⁶] = z⁶ -/
theorem D12_sixth (z : ℂ) : D12 (fun w => w ^ 6) z = z ^ 6 := by
  simp only [D12, N12_detects_six]; field_simp

/-- D₁₂ detects z⁶ -/
theorem D12_detects_sixth (z : ℂ) (hz : z ≠ 0) : D12 (fun w => w ^ 6) z ≠ 0 := by
  rw [D12_sixth]; exact pow_ne_zero 6 hz

end D12

section EulerOperator

/-- Euler operator θ = z·d/dz: the unique complete detector (ker = {constants}).
    θ[z^n] = n·z^n. -/
noncomputable def euler (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv f z

/-- θ[z^n] = n·z^n -/
theorem euler_monomial (n : ℕ) (z : ℂ) :
    euler (fun w => w ^ n) z = n * z ^ n := by
  simp only [euler, deriv_pow_field]
  cases n with
  | zero => simp
  | succ k => simp [pow_succ]; ring

/-- θ[c] = 0 -/
theorem euler_const (c : ℂ) (z : ℂ) : euler (fun _ => c) z = 0 := by
  simp [euler, deriv_const]

/-- θ[z] = z -/
theorem euler_linear (z : ℂ) : euler id z = z := by
  simp [euler, deriv_id']

/-- θ detects all n ≥ 1: ker(θ) = {constants} -/
theorem euler_detects (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ≠ 0) :
    euler (fun w => w ^ n) z ≠ 0 := by
  rw [euler_monomial]
  apply mul_ne_zero
  · exact_mod_cast (show (n : ℕ) ≠ 0 by omega)
  · exact pow_ne_zero n hz

/-- θ is strictly finer than D₁₂ -/
theorem euler_finer_than_D12 :
    euler (fun w => w ^ 3) (1 : ℂ) ≠ 0 ∧ N12 (fun w => w ^ 3) (1 : ℂ) = 0 := by
  exact ⟨by rw [euler_monomial]; norm_num, by rw [N12_ker_three]⟩

end EulerOperator

section StandardDerivative

/-- Standard derivative recovered from Euler: d/dz = θ/z -/
noncomputable def standardDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ := euler f z / z

/-- θ/z agrees with d/dz on monomials: n·z^{n-1} -/
theorem standardDeriv_monomial (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    standardDeriv (fun w => w ^ n) z = ↑n * z ^ (n - 1) := by
  simp only [standardDeriv, euler_monomial]
  cases n with
  | zero => simp
  | succ k =>
    rw [show (k + 1 : ℕ) - 1 = k from by omega]
    rw [Nat.cast_succ]
    field_simp
    ring

/-- θ/z = deriv for monomials (matching Mathlib's deriv) -/
theorem standardDeriv_eq_deriv_monomial (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    standardDeriv (fun w => w ^ n) z = deriv (fun w => w ^ n) z := by
  rw [standardDeriv_monomial n z hz, deriv_pow_field]

/-- θ/z on constants: d/dz[c] = 0 -/
theorem standardDeriv_const (c : ℂ) (z : ℂ) :
    standardDeriv (fun _ => c) z = 0 := by
  simp [standardDeriv, euler_const, zero_div]

/-- θ/z on z: d/dz[z] = 1 -/
theorem standardDeriv_id (z : ℂ) (hz : z ≠ 0) :
    standardDeriv id z = 1 := by
  simp [standardDeriv, euler_linear, div_self hz]

/-- θ/z on z²: d/dz[z²] = 2z -/
theorem standardDeriv_sq (z : ℂ) (hz : z ≠ 0) :
    standardDeriv (fun w => w ^ 2) z = 2 * z := by
  rw [standardDeriv_monomial 2 z hz]; norm_num

/-- θ/z on z³: d/dz[z³] = 3z² -/
theorem standardDeriv_cube (z : ℂ) (hz : z ≠ 0) :
    standardDeriv (fun w => w ^ 3) z = 3 * z ^ 2 := by
  rw [standardDeriv_monomial 3 z hz]; norm_num

/-- d²/dz²[z²] = 2 from θ: d/dz(2z) = 2 -/
theorem standardDeriv_sq_twice (z : ℂ) (hz : z ≠ 0) :
    standardDeriv (fun w => 2 * w) z = 2 := by
  simp only [standardDeriv, euler]
  have hd : deriv (fun w : ℂ => 2 * w) z = 2 := by
    have heq : (fun w : ℂ => 2 * w) = (fun w => (2 : ℂ) * w ^ 1) := by
      funext w; ring
    rw [heq, deriv_const_mul_field, deriv_pow_field]; norm_num
  rw [hd]; field_simp

/-- d²/dz²[z³] = 6z from θ: d/dz(3z²) = 6z -/
theorem standardDeriv_cube_twice (z : ℂ) (hz : z ≠ 0) :
    standardDeriv (fun w => 3 * w ^ 2) z = 6 * z := by
  simp only [standardDeriv, euler]
  have hd : deriv (fun w : ℂ => 3 * w ^ 2) z = 6 * z := by
    rw [deriv_const_mul_field, deriv_pow_field]; ring
  rw [hd]; field_simp

end StandardDerivative

end FUST.EulerOperator
