import FUST.Zeta6
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace FUST.ScalingLimit

open Complex Filter Topology

/-! ## Symmetric scaling operator D_t and Euler operator θ

D_t(f)(z) = (f(e^t·z) - f(e^{-t}·z)) / (2·sinh(t)·z).
On monomials: D_t(z^n) = sinh(nt)/sinh(t) · z^{n-1}.
Since lim_{t→0} sinh(nt)/sinh(t) = n, we get lim z·D_t = θ = z·d/dz. -/

/-- Symmetric scaling operator at parameter t -/
noncomputable def D_t (t : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if t = 0 then 0
  else (f (↑(Real.exp t) * z) - f (↑(Real.exp (-t)) * z)) /
    (2 * ↑(Real.sinh t) * z)

private lemma exp_pow_eq (t : ℝ) (n : ℕ) :
    (↑(Real.exp t) : ℂ) ^ n = ↑(Real.exp (↑n * t)) := by
  rw [← ofReal_pow, Real.exp_nat_mul]

/-- D_t on monomials: sinh(nt)/sinh(t) · z^{n-1} -/
theorem D_t_monomial (n : ℕ) (t : ℝ) (ht : t ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    D_t t (fun w => w ^ n) z =
    ↑(Real.sinh (↑n * t) / Real.sinh t) * z ^ (n - 1) := by
  simp only [D_t, ht, ↓reduceIte, mul_pow, exp_pow_eq]
  have hst : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  cases n with
  | zero => simp [Real.sinh_zero]
  | succ k =>
    rw [show k + 1 - 1 = k from rfl]
    have hz2 : (2 : ℂ) * ↑(Real.sinh t) * z ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero _ _) hz
      · exact two_ne_zero
      · exact ofReal_ne_zero.mpr hst
    rw [show ↑(k + 1) * -t = -(↑(k + 1) * t) from by ring] at *
    conv_lhs => rw [show (↑(Real.exp (↑(k + 1) * t)) : ℂ) * z ^ (k + 1) -
        ↑(Real.exp (-(↑(k + 1) * t))) * z ^ (k + 1) =
        (↑(Real.exp (↑(k + 1) * t)) - ↑(Real.exp (-(↑(k + 1) * t)))) *
        z ^ (k + 1) from by ring]
    rw [← ofReal_sub, show Real.exp (↑(k + 1) * t) - Real.exp (-(↑(k + 1) * t)) =
        2 * Real.sinh (↑(k + 1) * t) from by rw [Real.sinh_eq]; ring]
    simp only [ofReal_mul, ofReal_ofNat, ofReal_div]
    have hst2 : (↑(Real.sinh t) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hst
    field_simp
    ring

/-- Euler operator θ = z·d/dz -/
noncomputable def euler (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv f z

/-- θ[z^n] = n·z^n -/
theorem euler_monomial (n : ℕ) (z : ℂ) :
    euler (fun w => w ^ n) z = n * z ^ n := by
  simp only [euler, deriv_pow_field]
  cases n with
  | zero => simp
  | succ k => simp [pow_succ]; ring

/-- θ annihilates constants -/
theorem euler_const (c : ℂ) (z : ℂ) : euler (fun _ => c) z = 0 := by
  simp [euler, deriv_const]

/-- θ detects all n ≥ 1 -/
theorem euler_detects (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ≠ 0) :
    euler (fun w => w ^ n) z ≠ 0 := by
  rw [euler_monomial]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pow_ne_zero n hz)

/-- z·D_t on monomials: sinh(nt)/sinh(t) · z^n -/
theorem z_D_t_monomial (n : ℕ) (t : ℝ) (ht : t ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    z * D_t t (fun w => w ^ n) z =
    ↑(Real.sinh (↑n * t) / Real.sinh t) * z ^ n := by
  rw [D_t_monomial n t ht z hz]
  cases n with
  | zero => simp [Real.sinh_zero]
  | succ k =>
    rw [show k + 1 - 1 = k from rfl]
    ring

private lemma sinh_div_tendsto :
    Tendsto (fun t => Real.sinh t / t) (𝓝[≠] 0) (nhds 1) := by
  have hd : HasDerivAt Real.sinh 1 0 := by
    simpa [Real.cosh_zero] using Real.hasDerivAt_sinh (0 : ℝ)
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field] at hd
  simpa [Real.sinh_zero] using hd

private lemma sinh_nt_div_tendsto (n : ℕ) :
    Tendsto (fun t => Real.sinh (↑n * t) / t) (𝓝[≠] 0) (nhds ↑n) := by
  have hd : HasDerivAt (fun t => Real.sinh (↑n * t)) (↑n : ℝ) 0 := by
    have h1 : HasDerivAt Real.sinh 1 (↑n * (0 : ℝ)) := by
      simp only [mul_zero]
      simpa [Real.cosh_zero] using Real.hasDerivAt_sinh (0 : ℝ)
    have h2 : HasDerivAt (fun t : ℝ => (↑n : ℝ) * t) (↑n) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (↑n : ℝ)
    convert h1.comp 0 h2 using 1; ring
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field] at hd
  simpa [Real.sinh_zero, mul_zero] using hd

/-- sinh(nt)/sinh(t) → n as t → 0 -/
theorem tendsto_sinh_ratio (n : ℕ) :
    Tendsto (fun t => Real.sinh (↑n * t) / Real.sinh t) (𝓝[≠] 0) (nhds ↑n) := by
  have h1 := sinh_nt_div_tendsto n
  have h2 := sinh_div_tendsto
  have h3 : Tendsto (fun t => Real.sinh (↑n * t) / t / (Real.sinh t / t))
      (𝓝[≠] 0) (nhds (↑n / 1)) := h1.div h2 one_ne_zero
  simp only [div_one] at h3
  exact h3.congr (fun x => by
    by_cases hx : x = 0
    · simp [hx, Real.sinh_zero]
    · have hsx : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
      field_simp)

/-- z·D_t(z^n) → n·z^n = θ(z^n) as t → 0 -/
theorem scaling_limit_monomial (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    Tendsto (fun t => z * D_t t (fun w => w ^ n) z)
      (𝓝[≠] 0) (nhds (↑n * z ^ n)) := by
  have hmono : Set.EqOn (fun t => ↑(Real.sinh (↑n * t) / Real.sinh t) * z ^ n)
      (fun t => z * D_t t (fun w => w ^ n) z) ({0}ᶜ : Set ℝ) :=
    fun t ht => (z_D_t_monomial n t (Set.mem_compl_singleton_iff.mp ht) z hz).symm
  rw [show (↑n : ℂ) * z ^ n = ↑(↑n : ℝ) * z ^ n from by simp]
  exact Filter.Tendsto.congr' (hmono.eventuallyEq_nhdsWithin)
    ((tendsto_sinh_ratio n |>.ofReal).mul tendsto_const_nhds)

/-- CD2 is D_t at t = ln(φ), up to ψ sign correction -/
theorem D_t_at_lnphi (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    D_t (Real.log φ) (fun w => w ^ n) z =
    ↑(Real.sinh (↑n * Real.log φ) / Real.sinh (Real.log φ)) * z ^ (n - 1) := by
  exact D_t_monomial n (Real.log φ) (ne_of_gt (Real.log_pos φ_gt_one)) z hz

end FUST.ScalingLimit
