import FUST.Basic
import FUST.DifferenceOperators
import FUST.SpectralCoefficients
import FUST.Physics.PhiBloch
import FUST.Physics.GravitationalCoupling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.DiscreteSubset

namespace FUST.MellinSampling

open FUST FUST.SpectralCoefficients FUST.FrourioLogarithm Real Complex Filter
  Topology Asymptotics Bornology

/-! ## D6 Structure Preservation -/

section D6Preservation

structure KernelDecomposition (f : ℝ → ℝ) where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  complement : ℝ → ℝ
  decomp : ∀ x, x ≠ 0 → f x = a * x⁻¹ ^ 2 + b + c * x + d * x ^ 2 + complement x

theorem kernel_part_annihilated (a b c d : ℝ) (x : ℝ) (hx : x ≠ 0) :
    D6 (fun t => a * t⁻¹ ^ 2 + b + c * t + d * t ^ 2) x = 0 := by
  have h1 := D6_const b x hx
  have h2 := D6_linear x hx
  have h3 := D6_quadratic x hx
  have h4 := FUST.GravitationalCoupling.D6_inv_sq_zero x hx
  simp only [D6, N6, hx, ↓reduceIte] at h1 h2 h3 h4 ⊢
  have h_denom : D6Denom * x ≠ 0 := D6Denom_mul_ne_zero x hx
  rw [div_eq_zero_iff] at h1 h2 h3 h4 ⊢
  left
  have n2 := h2.resolve_right h_denom
  have n3 := h3.resolve_right h_denom
  have n4 := h4.resolve_right h_denom
  simp [id] at n2
  linear_combination a * n4 + c * n2 + d * n3

def KernelRecoverable (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃! p : ℝ × ℝ × ℝ × ℝ, ∀ n ∈ ({0, 1, 2, 3} : Set ℤ),
    PhiBloch.phiLatticeSample f x₀ n =
      p.1 * (φ ^ n * x₀)⁻¹ ^ 2 + p.2.1 + p.2.2.1 * (φ ^ n * x₀) + p.2.2.2 * (φ ^ n * x₀) ^ 2

end D6Preservation

/-! ## Analytic Continuation Framework -/

section AnalyticContinuation

-- Euler's identity: exp(πi) = -1
theorem euler_identity : Complex.exp (↑Real.pi * Complex.I) = -1 := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi, Real.sin_pi]
  simp

-- Complex sinc: entire extension of real sinc
noncomputable def sincC (z : ℂ) : ℂ :=
  if z = 0 then 1 else Complex.sin (↑Real.pi * z) / (↑Real.pi * z)

theorem sincC_zero : sincC 0 = 1 := by simp [sincC]

theorem sincC_int (n : ℤ) (hn : n ≠ 0) : sincC (↑(n : ℤ)) = 0 := by
  simp only [sincC]
  have hne : (↑(n : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [if_neg hne,
      show ↑Real.pi * (↑(n : ℤ) : ℂ) = ↑(n : ℤ) * ↑Real.pi from by ring,
      Complex.sin_int_mul_pi]
  simp

-- Rotation offset: τ = π/logφ is the imaginary shift for π-rotation
noncomputable def frourioRotationOffset : ℝ := Real.pi / Real.log φ

theorem frourioRotationOffset_pos : frourioRotationOffset > 0 :=
  div_pos Real.pi_pos (Real.log_pos φ_gt_one)

-- exp(logφ · iτ) = exp(iπ) = -1
theorem phi_imaginary_rotation :
    Complex.exp (↑(Real.log φ) * (↑frourioRotationOffset * Complex.I)) = -1 := by
  unfold frourioRotationOffset
  have hlog : (↑(Real.log φ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.log_pos φ_gt_one)
  have : ↑(Real.log φ) * (↑(Real.pi / Real.log φ) * Complex.I) =
    ↑Real.pi * Complex.I := by push_cast; field_simp
  rw [this]; exact euler_identity

-- Complex frourio time and rotated frourio time
noncomputable def complexFrourioTime (x : ℝ) : ℂ :=
  ↑(Real.log x / Real.log φ)

noncomputable def rotatedFrourioTime (x : ℝ) : ℂ :=
  ↑(Real.log x / Real.log φ) + ↑frourioRotationOffset * Complex.I

-- sincC(m - n) = δ_{mn} for integers
theorem sincC_delta (m n : ℤ) :
    sincC (↑m - ↑n : ℂ) = if m = n then 1 else 0 := by
  simp only [← Int.cast_sub]
  split_ifs with h
  · rw [h, sub_self, Int.cast_zero, sincC_zero]
  · exact sincC_int (m - n) (sub_ne_zero.mpr h)

-- Complex sinc reconstruction: g(z) = Σ_n a_n · sincC(z - n)
noncomputable def sincRecon (a : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, a n * sincC (z - ↑n)

-- φ-lattice sinc reconstruction
noncomputable def phiSincRecon (f : ℝ → ℝ) (x₀ : ℝ) (z : ℂ) : ℂ :=
  sincRecon (fun n => ↑(PhiBloch.phiLatticeSample f x₀ n)) z

-- Interpolation: sincRecon evaluated at integer m = a_m
theorem sincRecon_eval_int (a : ℤ → ℂ) (m : ℤ) :
    sincRecon a ↑m = a m := by
  unfold sincRecon
  rw [tsum_eq_single m]
  · rw [sincC_delta, if_pos rfl, mul_one]
  · intro n hn
    rw [sincC_delta, if_neg (Ne.symm hn), mul_zero]

-- Finite sinc extraction
theorem sincC_delta_extract_finite (a : ℤ → ℂ) (m : ℤ) (S : Finset ℤ)
    (hm : m ∈ S) :
    ∑ n ∈ S, a n * sincC (↑m - ↑n) = a m := by
  rw [Finset.sum_eq_single m]
  · rw [sincC_delta, if_pos rfl, mul_one]
  · intro n _ hn
    rw [sincC_delta, if_neg (Ne.symm hn), mul_zero]
  · intro habs; exact absurd hm habs

-- Injectivity: integer samples determine sinc coefficients
theorem sincRecon_injective (a b : ℤ → ℂ)
    (heq : ∀ m : ℤ, sincRecon a ↑m = sincRecon b ↑m) :
    a = b := by
  funext m
  rw [← sincRecon_eval_int a m, ← sincRecon_eval_int b m]
  exact heq m

-- Complex sinc preserves lattice interpolation property
theorem sincC_lattice_interpolation :
    sincC 0 = 1 ∧ (∀ n : ℤ, n ≠ 0 → sincC ↑n = 0) :=
  ⟨sincC_zero, sincC_int⟩

-- Discrete-analytic equivalence: samples ↔ sinc series (bijection within PW_π)
theorem discrete_analytic_bijection (a b : ℤ → ℂ) :
    (∀ z : ℂ, sincRecon a z = sincRecon b z) ↔ a = b := by
  constructor
  · intro heq
    exact sincRecon_injective a b (fun m => heq ↑m)
  · intro hab
    rw [hab]
    intro _
    rfl

-- sincC is even
theorem sincC_even (z : ℂ) : sincC (-z) = sincC z := by
  simp only [sincC]
  by_cases hz : z = 0
  · simp [hz]
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [if_neg hnz, if_neg hz]
    rw [show ↑Real.pi * (-z) = -(↑Real.pi * z) from by ring, Complex.sin_neg]
    field_simp

private def intReflect : ℤ ≃ ℤ where
  toFun n := 1 - n
  invFun n := 1 - n
  left_inv n := by ring
  right_inv n := by ring

-- Discrete FE on samples implies global FE on sincRecon
theorem discrete_FE_implies_global_FE (a : ℤ → ℂ)
    (hdfe : ∀ n : ℤ, a n = a (1 - n)) (s : ℂ) :
    sincRecon a s = sincRecon a (1 - s) := by
  unfold sincRecon
  have step1 : (fun n => a n * sincC ((1 - s) - ↑n)) =
      fun n => a n * sincC (s - ↑(1 - n)) := by
    ext n; congr 1
    rw [show (1 : ℂ) - s - ↑n = -(s - ↑(1 - n)) from by push_cast; ring]
    exact sincC_even _
  rw [step1, ← Equiv.tsum_eq intReflect]
  congr 1; ext m
  simp only [intReflect, Equiv.coe_fn_mk]
  rw [show a (1 - m) = a m from (hdfe m).symm]

-- Analytic hypotheses for Carlson-type uniqueness
def IsEntire (h : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, DifferentiableAt ℂ h z

def ExponentialType_le_pi (h : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ z : ℂ, ‖h z‖ ≤ C * Real.exp (Real.pi * ‖z‖)

def SquareIntegrableOnReals (h : ℂ → ℂ) : Prop :=
  MeasureTheory.Integrable (fun t : ℝ => ‖h ↑t‖ ^ 2) MeasureTheory.volume

-- sin(πz) = 0 ↔ z ∈ ℤ
theorem sin_pi_mul_eq_zero_iff (z : ℂ) :
    Complex.sin (↑Real.pi * z) = 0 ↔ ∃ n : ℤ, z = ↑n := by
  rw [Complex.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_right_cancel₀ hpi (by linear_combination hk)
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

-- cos(πn) ≠ 0 for integer n
theorem cos_pi_int_ne_zero (n : ℤ) : Complex.cos (↑Real.pi * ↑n) ≠ 0 := by
  rw [show (↑Real.pi : ℂ) * (↑n : ℂ) = ↑((n : ℝ) * Real.pi) from by push_cast; ring,
      ← Complex.ofReal_cos]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  rw [show (n : ℝ) * Real.pi = ↑n * Real.pi from by norm_cast, Real.cos_int_mul_pi]
  exact zpow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)

-- d/dz sin(πz)|_{z=n} = π cos(πn) ≠ 0
theorem sin_pi_deriv_ne_zero (n : ℤ) :
    ↑Real.pi * Complex.cos (↑Real.pi * (↑n : ℂ)) ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (cos_pi_int_ne_zero n)

private noncomputable def sinPiC : ℂ → ℂ := fun z => Complex.sin (↑Real.pi * z)

private theorem sinPiC_differentiable : Differentiable ℂ sinPiC :=
  Complex.differentiable_sin.comp (differentiable_const _ |>.mul differentiable_id)

private theorem sinPiC_int_eq_zero (n : ℤ) : sinPiC (↑n : ℂ) = 0 := by
  simp [sinPiC, show (↑Real.pi : ℂ) * (↑n : ℂ) = ↑n * ↑Real.pi from by ring,
        Complex.sin_int_mul_pi]

private theorem sinPiC_hasDerivAt (z : ℂ) :
    HasDerivAt sinPiC (↑Real.pi * Complex.cos (↑Real.pi * z)) z := by
  convert (Complex.hasDerivAt_sin (↑Real.pi * z)).comp z
    (hasDerivAt_const_mul (↑Real.pi : ℂ)) using 1; ring

private theorem dslope_sinPiC_at_int_ne_zero (n : ℤ) :
    dslope sinPiC (↑n : ℂ) ↑n ≠ 0 := by
  rw [dslope_same, (sinPiC_hasDerivAt ↑n).deriv]
  exact sin_pi_deriv_ne_zero n

private theorem dslope_of_entire (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c : ℂ) :
    Differentiable ℂ (dslope f c) := by
  intro z
  have hd : DifferentiableOn ℂ (dslope f c) Set.univ := by
    rw [differentiableOn_dslope (Filter.univ_mem)]
    exact fun z _ => (hf z).differentiableWithinAt
  exact (hd z (Set.mem_univ z)).differentiableAt
    (IsOpen.mem_nhds isOpen_univ (Set.mem_univ z))

private theorem sinPiC_eventually_ne_zero (n : ℤ) :
    ∀ᶠ z in 𝓝[≠] (↑n : ℂ), sinPiC z ≠ 0 := by
  have hAn := sinPiC_differentiable.analyticAt (↑n : ℂ)
  refine hAn.eventually_eq_zero_or_eventually_ne_zero.resolve_left ?_
  intro hid
  have hne : deriv sinPiC (↑n : ℂ) ≠ 0 := by
    rw [(sinPiC_hasDerivAt ↑n).deriv]; exact sin_pi_deriv_ne_zero n
  have heq : sinPiC =ᶠ[𝓝 (↑n : ℂ)] (fun _ => (0 : ℂ)) := hid
  rw [heq.deriv_eq, deriv_const] at hne; exact hne rfl

private theorem div_eq_dslope_ratio' (f : ℂ → ℂ) (n : ℤ) (z : ℂ)
    (hzn : z ≠ (↑n : ℂ)) (hfn : f (↑n : ℂ) = 0) :
    f z / sinPiC z = dslope f (↑n : ℂ) z / dslope sinPiC (↑n : ℂ) z := by
  have hsub : z - ↑n ≠ 0 := sub_ne_zero.mpr hzn
  have hf_eq : f z = (z - ↑n) * dslope f (↑n : ℂ) z := by
    have h := sub_smul_dslope f (↑n : ℂ) z
    simp only [smul_eq_mul] at h; rw [hfn, sub_zero] at h; exact h.symm
  have hs_eq : sinPiC z = (z - ↑n) * dslope sinPiC (↑n : ℂ) z := by
    have h := sub_smul_dslope sinPiC (↑n : ℂ) z
    simp only [smul_eq_mul] at h; rw [sinPiC_int_eq_zero, sub_zero] at h; exact h.symm
  rw [hf_eq, hs_eq, mul_div_mul_left _ _ hsub]

private noncomputable def divSinPiC (f : ℂ → ℂ) : ℂ → ℂ := fun z =>
  if sinPiC z ≠ 0 then f z / sinPiC z
  else deriv f z / (↑Real.pi * Complex.cos (↑Real.pi * z))

private theorem divSinPiC_of_ne (f : ℂ → ℂ) (z : ℂ) (hz : sinPiC z ≠ 0) :
    divSinPiC f z = f z / sinPiC z := if_pos hz

private theorem divSinPiC_eq_dslope_at_int (f : ℂ → ℂ) (n : ℤ) :
    divSinPiC f (↑n : ℂ) = dslope f (↑n : ℂ) (↑n : ℂ) / dslope sinPiC (↑n : ℂ) (↑n : ℂ) := by
  rw [dslope_same, dslope_same, (sinPiC_hasDerivAt ↑n).deriv]
  simp [divSinPiC, sinPiC_int_eq_zero]

-- Entire function vanishing at all integers equals sin(πz) · g(z) for some entire g
-- Uses dslope factorization + removable singularity theorem.
theorem entire_vanish_int_div_sin (f : ℂ → ℂ) (hf : IsEntire f)
    (hvan : ∀ n : ℤ, f ↑n = 0) :
    ∃ g : ℂ → ℂ, IsEntire g ∧ ∀ z, f z = Complex.sin (↑Real.pi * z) * g z := by
  have hfD : Differentiable ℂ f := fun z => hf z
  set g := divSinPiC f
  refine ⟨g, fun z => ?_, fun z => ?_⟩
  · -- g is entire: AnalyticAt at every point → DifferentiableAt
    by_cases hs : sinPiC z ≠ 0
    · -- Non-integer: g = f/sinPiC, analytic by quotient rule
      have hne : ∀ᶠ w in 𝓝 z, sinPiC w ≠ 0 :=
        sinPiC_differentiable.continuous.continuousAt.eventually (isOpen_ne.mem_nhds hs)
      have heq : (fun w => g w) =ᶠ[𝓝 z] fun w => f w / sinPiC w := by
        filter_upwards [hne] with w hw; exact divSinPiC_of_ne f w hw
      exact (((hfD.analyticAt z).div (sinPiC_differentiable.analyticAt z) hs).congr
        heq.symm).differentiableAt
    · -- Integer: use removable singularity theorem
      push_neg at hs
      have ⟨m, hm⟩ := (sin_pi_mul_eq_zero_iff z).mp (by rwa [sinPiC] at hs)
      rw [hm]
      have hAnalytic : AnalyticAt ℂ g (↑m : ℂ) := by
        apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt (E := ℂ)
        · filter_upwards [sinPiC_eventually_ne_zero m] with w hw
          have hne' : ∀ᶠ u in 𝓝 w, sinPiC u ≠ 0 :=
            sinPiC_differentiable.continuous.continuousAt.eventually (isOpen_ne.mem_nhds hw)
          exact (((hfD.analyticAt w).div (sinPiC_differentiable.analyticAt w) hw).congr
            (by filter_upwards [hne'] with u hu; exact (divSinPiC_of_ne f u hu).symm)
            ).differentiableAt
        · set φ := fun w => dslope f (↑m : ℂ) w / dslope sinPiC (↑m : ℂ) w
          have hφ_cont : ContinuousAt φ (↑m : ℂ) :=
            (dslope_of_entire f hfD ↑m).continuous.continuousAt.div
              (dslope_of_entire sinPiC sinPiC_differentiable ↑m).continuous.continuousAt
              (dslope_sinPiC_at_int_ne_zero m)
          have heq_punc : (fun w => g w) =ᶠ[𝓝[≠] (↑m : ℂ)] φ := by
            filter_upwards [sinPiC_eventually_ne_zero m, self_mem_nhdsWithin] with w hw hwm
            exact (divSinPiC_of_ne f w hw).trans (div_eq_dslope_ratio' f m w hwm (hvan m))
          have hval : g (↑m : ℂ) = φ (↑m : ℂ) := divSinPiC_eq_dslope_at_int f m
          exact hφ_cont.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE heq_punc hval).symm
      exact hAnalytic.differentiableAt
  · -- f = sin(πz) · g everywhere
    change f z = sinPiC z * g z
    by_cases hs : sinPiC z ≠ 0
    · have : g z = f z / sinPiC z := divSinPiC_of_ne f z hs
      rw [this, mul_div_cancel₀ (f z) hs]
    · push_neg at hs
      have ⟨m, hm⟩ := (sin_pi_mul_eq_zero_iff z).mp (by rwa [sinPiC] at hs)
      rw [hm, show sinPiC (↑m : ℂ) = 0 from sinPiC_int_eq_zero m, zero_mul, hvan]

private theorem normSq_sin_ge_sq_sinh_im (z : ℂ) :
    Complex.normSq (Complex.sin z) ≥ Real.sinh z.im ^ 2 := by
  have heq := Complex.sin_eq z
  have hre : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    rw [heq]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
      Complex.sin_ofReal_im, Complex.cosh_ofReal_im,
      Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
      Complex.cos_ofReal_im, Complex.sinh_ofReal_im]
  have him : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
    rw [heq]
    simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
      Complex.sin_ofReal_im, Complex.cosh_ofReal_im,
      Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
      Complex.cos_ofReal_im, Complex.sinh_ofReal_im]
  rw [Complex.normSq_apply, hre, him]
  have h_cosh : Real.cosh z.im ^ 2 = Real.sinh z.im ^ 2 + 1 := by
    have hc := Complex.cosh_sq (↑z.im : ℂ); exact_mod_cast hc
  nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.cos z.re),
    sq_nonneg (Real.sinh z.im), Real.sin_sq_add_cos_sq z.re]

private theorem norm_sin_ge_abs_sinh_im (z : ℂ) :
    ‖Complex.sin z‖ ≥ |Real.sinh z.im| := by
  have h1 : ‖Complex.sin z‖ ^ 2 ≥ Real.sinh z.im ^ 2 := by
    rw [Complex.sq_norm]; exact normSq_sin_ge_sq_sinh_im z
  exact le_of_sq_le_sq (by rwa [sq_abs]) (norm_nonneg _)

private theorem sinh_ge_exp_div_four {t : ℝ} (ht : t ≥ 1) :
    Real.sinh t ≥ Real.exp t / 4 := by
  rw [Real.sinh_eq]
  have hexp_neg_le : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hexp_ge_two : Real.exp t ≥ 2 := by linarith [Real.exp_le_exp.mpr ht, Real.exp_one_gt_d9]
  linarith

private theorem abs_sinh_ge {t : ℝ} (ht : |t| ≥ 1) :
    |Real.sinh t| ≥ Real.exp |t| / 4 := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢
    rw [abs_of_nonneg (le_of_lt (Real.sinh_pos_iff.mpr (by linarith)))]
    exact sinh_ge_exp_div_four ht
  · rw [abs_of_neg h] at ht ⊢
    rw [abs_of_nonpos (le_of_lt (Real.sinh_neg_iff.mpr h))]
    have : Real.sinh t = -Real.sinh (-t) := by rw [Real.sinh_neg]; ring
    rw [this]; ring_nf; linarith [sinh_ge_exp_div_four ht]

-- |sin(πz)| ≥ c·exp(π|Im z|) when |Im z| ≥ 1
private theorem sin_pi_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ z : ℂ, |z.im| ≥ 1 →
      ‖Complex.sin (↑Real.pi * z)‖ ≥ c * Real.exp (Real.pi * |z.im|) := by
  refine ⟨1/4, by norm_num, ?_⟩
  intro z him
  have him_pi : |Real.pi * z.im| ≥ 1 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_gt_three]
  have h1 : ‖Complex.sin (↑Real.pi * z)‖ ≥ |Real.sinh (Real.pi * z.im)| := by
    have := norm_sin_ge_abs_sinh_im (↑Real.pi * z)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at this
    exact this
  have h2 : |Real.sinh (Real.pi * z.im)| ≥ Real.exp |Real.pi * z.im| / 4 :=
    abs_sinh_ge him_pi
  rw [abs_mul, abs_of_pos Real.pi_pos] at h2; linarith

-- ‖z‖ - |Im z| ≤ |Re z| for complex z
private theorem norm_sub_im_le_re (z : ℂ) : ‖z‖ - |z.im| ≤ |z.re| :=
  sub_le_iff_le_add.mpr (Complex.norm_le_abs_re_add_abs_im z)

-- g = f/sin(πz) growth: |g(z)| ≤ C' exp(π|Re z|) for |Im z| ≥ 1
theorem div_sin_growth (f g : ℂ → ℂ) (hf_type : ExponentialType_le_pi f)
    (hfg : ∀ z, f z = Complex.sin (↑Real.pi * z) * g z) :
    ∃ C : ℝ, C > 0 ∧ ∀ z : ℂ, |z.im| ≥ 1 →
      ‖g z‖ ≤ C * Real.exp (Real.pi * |z.re|) := by
  obtain ⟨Cf, hCf_pos, hCf⟩ := hf_type
  obtain ⟨cs, hcs_pos, hcs⟩ := sin_pi_lower_bound
  refine ⟨Cf / cs, div_pos hCf_pos hcs_pos, ?_⟩
  intro z him
  have hsin_ne : Complex.sin (↑Real.pi * z) ≠ 0 := by
    intro h; obtain ⟨n, hn⟩ := (sin_pi_mul_eq_zero_iff z).mp h
    rw [hn] at him; simp at him; linarith
  have hsin_pos : ‖Complex.sin (↑Real.pi * z)‖ > 0 := norm_pos_iff.mpr hsin_ne
  have hg_eq : ‖g z‖ = ‖f z‖ / ‖Complex.sin (↑Real.pi * z)‖ := by
    rw [hfg z, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hsin_ne)]
  rw [hg_eq, div_le_iff₀ hsin_pos]
  have hsin_bound := hcs z him
  calc ‖f z‖ ≤ Cf * Real.exp (Real.pi * ‖z‖) := hCf z
    _ ≤ Cf * Real.exp (Real.pi * (|z.re| + |z.im|)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im z)
          (le_of_lt Real.pi_pos))) (le_of_lt hCf_pos)
    _ = Cf * (Real.exp (Real.pi * |z.re|) * Real.exp (Real.pi * |z.im|)) := by
      rw [← Real.exp_add]; ring_nf
    _ = Cf / cs * Real.exp (Real.pi * |z.re|) * (cs * Real.exp (Real.pi * |z.im|)) := by
      field_simp
    _ ≤ Cf / cs * Real.exp (Real.pi * |z.re|) * ‖Complex.sin (↑Real.pi * z)‖ :=
      mul_le_mul_of_nonneg_left hsin_bound
        (mul_nonneg (le_of_lt (div_pos hCf_pos hcs_pos)) (le_of_lt (Real.exp_pos _)))

private lemma norm_exp_I_pi_mul (z : ℂ) :
    ‖Complex.exp (↑Real.pi * Complex.I * z)‖ = Real.exp (-Real.pi * z.im) := by
  rw [Complex.norm_exp]; congr 1
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, sub_zero]; ring

private lemma norm_exp_neg_I_pi_mul (z : ℂ) :
    ‖Complex.exp (-(↑Real.pi * Complex.I) * z)‖ = Real.exp (Real.pi * z.im) := by
  rw [Complex.norm_exp]; congr 1
  simp only [Complex.neg_im, Complex.neg_re, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, sub_zero, neg_zero]; ring

private lemma g_plus_global_bound (f : ℂ → ℂ) (Cf : ℝ) (_ : Cf > 0)
    (hCf : ∀ z : ℂ, ‖f z‖ ≤ Cf * Real.exp (Real.pi * ‖z‖)) (w : ℂ) :
    ‖f w * Complex.exp (↑Real.pi * Complex.I * w)‖ ≤ Cf * Real.exp (2 * Real.pi * ‖w‖) := by
  rw [norm_mul, norm_exp_I_pi_mul]
  have h1 : -Real.pi * w.im ≤ Real.pi * ‖w‖ := by
    have := neg_abs_le w.im
    have := Complex.abs_im_le_norm w
    nlinarith [Real.pi_pos]
  calc ‖f w‖ * Real.exp (-Real.pi * w.im)
      ≤ Cf * Real.exp (Real.pi * ‖w‖) * Real.exp (Real.pi * ‖w‖) :=
        mul_le_mul (hCf w) (Real.exp_le_exp.mpr h1) (le_of_lt (Real.exp_pos _))
          (mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _)))
    _ = Cf * (Real.exp (Real.pi * ‖w‖) * Real.exp (Real.pi * ‖w‖)) := by ring
    _ = Cf * Real.exp (2 * Real.pi * ‖w‖) := by congr 1; rw [← Real.exp_add]; ring_nf

private lemma g_minus_global_bound (f : ℂ → ℂ) (Cf : ℝ) (_ : Cf > 0)
    (hCf : ∀ z : ℂ, ‖f z‖ ≤ Cf * Real.exp (Real.pi * ‖z‖)) (w : ℂ) :
    ‖f w * Complex.exp (-(↑Real.pi * Complex.I) * w)‖ ≤
      Cf * Real.exp (2 * Real.pi * ‖w‖) := by
  rw [norm_mul, norm_exp_neg_I_pi_mul]
  have h1 : Real.pi * w.im ≤ Real.pi * ‖w‖ :=
    mul_le_mul_of_nonneg_left (Complex.im_le_norm w) (le_of_lt Real.pi_pos)
  calc ‖f w‖ * Real.exp (Real.pi * w.im)
      ≤ Cf * Real.exp (Real.pi * ‖w‖) * Real.exp (Real.pi * ‖w‖) :=
        mul_le_mul (hCf w) (Real.exp_le_exp.mpr h1) (le_of_lt (Real.exp_pos _))
          (mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _)))
    _ = Cf * (Real.exp (Real.pi * ‖w‖) * Real.exp (Real.pi * ‖w‖)) := by ring
    _ = Cf * Real.exp (2 * Real.pi * ‖w‖) := by congr 1; rw [← Real.exp_add]; ring_nf

private lemma f_exp_bound_real_plus (f : ℂ → ℂ) (M : ℝ) (hfM : ∀ x : ℝ, ‖f ↑x‖ ≤ M)
    (x : ℝ) : ‖f ↑x * Complex.exp (↑Real.pi * Complex.I * ↑x)‖ ≤ M := by
  rw [norm_mul, norm_exp_I_pi_mul]
  simp only [Complex.ofReal_im, mul_zero, Real.exp_zero, mul_one]; exact hfM x

private lemma f_exp_bound_real_minus (f : ℂ → ℂ) (M : ℝ) (hfM : ∀ x : ℝ, ‖f ↑x‖ ≤ M)
    (x : ℝ) : ‖f ↑x * Complex.exp (-(↑Real.pi * Complex.I) * ↑x)‖ ≤ M := by
  rw [norm_mul, norm_exp_neg_I_pi_mul]
  simp only [Complex.ofReal_im, mul_zero, Real.exp_zero, mul_one]; exact hfM x

private lemma f_exp_imag_pos (f : ℂ → ℂ) (Cf : ℝ)
    (hCf : ∀ z : ℂ, ‖f z‖ ≤ Cf * Real.exp (Real.pi * ‖z‖))
    (y : ℝ) (hy : 0 ≤ y) :
    ‖f (↑y * Complex.I) * Complex.exp (↑Real.pi * Complex.I * (↑y * Complex.I))‖ ≤ Cf := by
  rw [norm_mul, norm_exp_I_pi_mul]
  have him : (↑y * Complex.I).im = y := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [him]
  have hnorm : ‖(↑y : ℂ) * Complex.I‖ = |y| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hfb : ‖f (↑y * Complex.I)‖ ≤ Cf * Real.exp (Real.pi * y) := by
    have h := hCf (↑y * Complex.I); rwa [hnorm, abs_of_nonneg hy] at h
  linarith [mul_le_mul_of_nonneg_right hfb (le_of_lt (Real.exp_pos (-Real.pi * y))),
    show Cf * Real.exp (Real.pi * y) * Real.exp (-Real.pi * y) = Cf from by
      rw [mul_assoc, ← Real.exp_add]; simp]

private lemma f_exp_imag_neg (f : ℂ → ℂ) (Cf : ℝ)
    (hCf : ∀ z : ℂ, ‖f z‖ ≤ Cf * Real.exp (Real.pi * ‖z‖))
    (y : ℝ) (hy : y ≤ 0) :
    ‖f (↑y * Complex.I) * Complex.exp (-(↑Real.pi * Complex.I) * (↑y * Complex.I))‖ ≤
      Cf := by
  rw [norm_mul, norm_exp_neg_I_pi_mul]
  have him : (↑y * Complex.I).im = y := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [him]
  have hnorm : ‖(↑y : ℂ) * Complex.I‖ = |y| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hfb : ‖f (↑y * Complex.I)‖ ≤ Cf * Real.exp (Real.pi * (-y)) := by
    have h := hCf (↑y * Complex.I); rwa [hnorm, abs_of_nonpos hy] at h
  linarith [mul_le_mul_of_nonneg_right hfb (le_of_lt (Real.exp_pos (Real.pi * y))),
    show Cf * Real.exp (Real.pi * -y) * Real.exp (Real.pi * y) = Cf from by
      rw [mul_assoc, ← Real.exp_add]; simp]

-- PHL: f·exp(iπz) bounded in upper half-plane
private theorem f_exp_plus_bounded_uhp (f : ℂ → ℂ) (hf : IsEntire f)
    (Cf : ℝ) (hCf_pos : Cf > 0)
    (hCf : ∀ z : ℂ, ‖f z‖ ≤ Cf * Real.exp (Real.pi * ‖z‖))
    (M : ℝ) (_ : M > 0) (hfM : ∀ x : ℝ, ‖f ↑x‖ ≤ M)
    (z : ℂ) (hz_im : 0 ≤ z.im) :
    ‖f z * Complex.exp (↑Real.pi * Complex.I * z)‖ ≤ max M Cf := by
  set g : ℂ → ℂ := fun w => f w * Complex.exp (↑Real.pi * Complex.I * w)
  have hDiff : Differentiable ℂ g := fun w =>
    (hf w).mul (((differentiableAt_const _).mul differentiableAt_id).cexp)
  have hGrowth : ∀ Q : Set ℂ,
      ∃ c < (2 : ℝ), ∃ B : ℝ, g =O[cobounded ℂ ⊓ 𝓟 Q]
        fun w => Real.exp (B * ‖w‖ ^ c) := by
    intro Q; refine ⟨1, by norm_num, 2 * Real.pi, ?_⟩
    apply IsBigO.of_bound Cf
    rw [Filter.eventually_inf_principal]
    apply Filter.Eventually.of_forall
    intro w _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_one]
    exact g_plus_global_bound f Cf hCf_pos hCf w
  rcases le_or_gt 0 z.re with hre | hre
  · exact PhragmenLindelof.quadrant_I (f := g) hDiff.diffContOnCl (hGrowth _)
      (fun x hx => (f_exp_bound_real_plus f M hfM x).trans (le_max_left _ _))
      (fun y hy => (f_exp_imag_pos f Cf hCf y hy).trans (le_max_right _ _)) hre hz_im
  · exact PhragmenLindelof.quadrant_II (f := g) hDiff.diffContOnCl (hGrowth _)
      (fun x hx => (f_exp_bound_real_plus f M hfM x).trans (le_max_left _ _))
      (fun y hy => (f_exp_imag_pos f Cf hCf y hy).trans (le_max_right _ _))
      (le_of_lt hre) hz_im

-- PHL: f·exp(-iπz) bounded in lower half-plane
private theorem f_exp_minus_bounded_lhp (f : ℂ → ℂ) (hf : IsEntire f)
    (Cf : ℝ) (hCf_pos : Cf > 0)
    (hCf : ∀ z : ℂ, ‖f z‖ ≤ Cf * Real.exp (Real.pi * ‖z‖))
    (M : ℝ) (_ : M > 0) (hfM : ∀ x : ℝ, ‖f ↑x‖ ≤ M)
    (z : ℂ) (hz_im : z.im ≤ 0) :
    ‖f z * Complex.exp (-(↑Real.pi * Complex.I) * z)‖ ≤ max M Cf := by
  set g : ℂ → ℂ := fun w => f w * Complex.exp (-(↑Real.pi * Complex.I) * w)
  have hDiff : Differentiable ℂ g := fun w =>
    (hf w).mul (((differentiableAt_const _).mul differentiableAt_id).cexp)
  have hGrowth : ∀ Q : Set ℂ,
      ∃ c < (2 : ℝ), ∃ B : ℝ, g =O[cobounded ℂ ⊓ 𝓟 Q]
        fun w => Real.exp (B * ‖w‖ ^ c) := by
    intro Q; refine ⟨1, by norm_num, 2 * Real.pi, ?_⟩
    apply IsBigO.of_bound Cf
    rw [Filter.eventually_inf_principal]
    apply Filter.Eventually.of_forall
    intro w _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_one]
    exact g_minus_global_bound f Cf hCf_pos hCf w
  rcases le_or_gt 0 z.re with hre | hre
  · exact PhragmenLindelof.quadrant_IV (f := g) hDiff.diffContOnCl (hGrowth _)
      (fun x hx => (f_exp_bound_real_minus f M hfM x).trans (le_max_left _ _))
      (fun y hy => (f_exp_imag_neg f Cf hCf y hy).trans (le_max_right _ _)) hre hz_im
  · exact PhragmenLindelof.quadrant_III (f := g) hDiff.diffContOnCl (hGrowth _)
      (fun x hx => (f_exp_bound_real_minus f M hfM x).trans (le_max_left _ _))
      (fun y hy => (f_exp_imag_neg f Cf hCf y hy).trans (le_max_right _ _))
      (le_of_lt hre) hz_im

-- Strip bound: type ≤ π + bounded on ℝ → ‖f z‖ ≤ B · exp(π|Im z|)
private theorem entire_type_pi_bounded_strip (f : ℂ → ℂ) (hf : IsEntire f)
    (hf_type : ExponentialType_le_pi f)
    (M : ℝ) (hM_pos : M > 0) (hfM : ∀ x : ℝ, ‖f ↑x‖ ≤ M) :
    ∃ B : ℝ, B > 0 ∧ ∀ z : ℂ, ‖f z‖ ≤ B * Real.exp (Real.pi * |z.im|) := by
  obtain ⟨Cf, hCf_pos, hCf⟩ := hf_type
  set B := max M Cf
  have hB_pos : B > 0 := lt_max_of_lt_left hM_pos
  refine ⟨B, hB_pos, fun z => ?_⟩
  rcases le_or_gt z.im 0 with him | him
  · have hg := f_exp_minus_bounded_lhp f hf Cf hCf_pos hCf M hM_pos hfM z him
    rw [norm_mul, norm_exp_neg_I_pi_mul] at hg
    rw [abs_of_nonpos him]
    have hexp_pos := Real.exp_pos (Real.pi * z.im)
    have : ‖f z‖ ≤ B / Real.exp (Real.pi * z.im) := by rwa [le_div_iff₀ hexp_pos]
    calc ‖f z‖ ≤ B / Real.exp (Real.pi * z.im) := this
      _ = B * Real.exp (Real.pi * -z.im) := by rw [div_eq_mul_inv, ← Real.exp_neg]; ring_nf
  · have hg := f_exp_plus_bounded_uhp f hf Cf hCf_pos hCf M hM_pos hfM z (le_of_lt him)
    rw [norm_mul, norm_exp_I_pi_mul] at hg
    rw [abs_of_pos him]
    have hexp_pos := Real.exp_pos (-Real.pi * z.im)
    have : ‖f z‖ ≤ B / Real.exp (-Real.pi * z.im) := by rwa [le_div_iff₀ hexp_pos]
    calc ‖f z‖ ≤ B / Real.exp (-Real.pi * z.im) := this
      _ = B * Real.exp (Real.pi * z.im) := by rw [div_eq_mul_inv, ← Real.exp_neg]; ring_nf

-- Bernstein via Cauchy: strip bound → derivative bounded
private theorem bernstein_via_cauchy' (f : ℂ → ℂ) (hf : IsEntire f)
    (B : ℝ) (_ : B > 0) (hstrip : ∀ z : ℂ, ‖f z‖ ≤ B * Real.exp (Real.pi * |z.im|)) :
    ∀ x : ℝ, ‖deriv f ↑x‖ ≤ B * (Real.pi * Real.exp 1) := by
  intro x
  have hR : (0 : ℝ) < Real.pi⁻¹ := inv_pos.mpr Real.pi_pos
  have hDiff : Differentiable ℂ f := fun z => hf z
  have hd : DiffContOnCl ℂ f (Metric.ball (↑x : ℂ) Real.pi⁻¹) := hDiff.diffContOnCl
  have hC : ∀ z ∈ Metric.sphere (↑x : ℂ) Real.pi⁻¹, ‖f z‖ ≤ B * Real.exp 1 := by
    intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have him : |z.im| ≤ Real.pi⁻¹ := by
      have h1 : |z.im - (↑x : ℂ).im| ≤ ‖z - ↑x‖ := Complex.abs_im_le_norm (z - ↑x)
      simp only [Complex.ofReal_im, sub_zero] at h1; linarith [hz]
    calc ‖f z‖ ≤ B * Real.exp (Real.pi * |z.im|) := hstrip z
      _ ≤ B * Real.exp (Real.pi * Real.pi⁻¹) := by gcongr
      _ = B * Real.exp 1 := by rw [mul_inv_cancel₀ Real.pi_ne_zero]
  calc ‖deriv f ↑x‖ ≤ B * Real.exp 1 / Real.pi⁻¹ :=
      norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hC
    _ = B * Real.exp 1 * Real.pi := by rw [div_inv_eq_mul]
    _ = B * (Real.pi * Real.exp 1) := by ring

-- MVT via chain rule: ‖f(↑x) - f(↑n)‖ ≤ Md · |x - n|
private lemma entire_mvt_real (f : ℂ → ℂ) (hf : IsEntire f)
    (Md : ℝ) (hMd : ∀ x : ℝ, ‖deriv f ↑x‖ ≤ Md) (x : ℝ) (n : ℤ) :
    ‖f ↑x - f ↑n‖ ≤ Md * |x - ↑n| := by
  have hd : ∀ t ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (fun y : ℝ => f ↑y) t :=
    fun t _ => ((hf ↑t).hasDerivAt.comp_ofReal).differentiableAt
  have hb : ∀ t ∈ (Set.univ : Set ℝ), ‖deriv (fun y : ℝ => f ↑y) t‖ ≤ Md := by
    intro t _; rw [((hf ↑t).hasDerivAt.comp_ofReal).deriv]; exact hMd t
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) hd hb convex_univ
    (Set.mem_univ (↑n : ℝ)) (Set.mem_univ x)
  rwa [Real.norm_eq_abs] at h

-- Jordan: |sin(πt)| ≥ 2|t| for |t| ≤ 1/2
private lemma sin_pi_jordan {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.sin (Real.pi * t)| ≥ 2 * |t| := by
  have hpt : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    linarith [mul_le_mul_of_nonneg_left ht (le_of_lt Real.pi_pos)]
  have h1 := Real.mul_abs_le_abs_sin hpt
  rw [abs_mul, abs_of_pos Real.pi_pos] at h1
  linarith [show 2 / Real.pi * (Real.pi * |t|) = 2 * |t| from by field_simp]

private lemma sin_pi_at_int_shift (x : ℝ) (n : ℤ) :
    |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * (x - ↑n))| := by
  conv_lhs => rw [show Real.pi * x = Real.pi * (x - ↑n) + ↑n * Real.pi from by ring]
  rw [Real.sin_add_int_mul_pi]; simp [abs_mul, abs_neg, abs_one]

private lemma norm_csin_pi_real (x : ℝ) :
    ‖Complex.sin (↑Real.pi * ↑x)‖ = |Real.sin (Real.pi * x)| := by
  rw [show (↑Real.pi : ℂ) * (↑x : ℂ) = ↑(Real.pi * x) from by push_cast; ring,
      ← Complex.ofReal_sin]
  exact Complex.norm_real _

-- g at integer: g(m) = f'(m)/(π cos(πm)), so ‖g(m)‖ ≤ Md/π
private lemma g_int_bound (f g : ℂ → ℂ) (_ : IsEntire f) (hg : IsEntire g)
    (hfg : ∀ z, f z = Complex.sin (↑Real.pi * z) * g z)
    (m : ℤ) (Md : ℝ) (hMd : ∀ x : ℝ, ‖deriv f ↑x‖ ≤ Md) :
    ‖g (↑m : ℂ)‖ ≤ Md / Real.pi := by
  have hsin_m : Complex.sin (↑Real.pi * (↑m : ℂ)) = 0 := by
    rw [show (↑Real.pi : ℂ) * (↑m : ℂ) = ↑m * ↑Real.pi from by ring]
    exact Complex.sin_int_mul_pi m
  have h1 : HasDerivAt (fun z => Complex.sin (↑Real.pi * z))
      (↑Real.pi * Complex.cos (↑Real.pi * ↑m)) (↑m : ℂ) := by
    convert (Complex.hasDerivAt_sin (↑Real.pi * ↑m)).comp (↑m : ℂ)
      (hasDerivAt_const_mul _) using 1; ring
  have hprod := h1.mul ((hg ↑m).hasDerivAt)
  have hdf : HasDerivAt f (↑Real.pi * Complex.cos (↑Real.pi * ↑m) * g ↑m) (↑m : ℂ) := by
    have hev : f =ᶠ[𝓝 (↑m : ℂ)] (fun z => Complex.sin (↑Real.pi * z) * g z) :=
      Filter.Eventually.of_forall (fun z => hfg z)
    have := hprod.congr_of_eventuallyEq hev
    rwa [hsin_m, zero_mul, add_zero] at this
  have hcos_ne : Complex.cos (↑Real.pi * (↑m : ℂ)) ≠ 0 := by
    rw [show (↑Real.pi : ℂ) * (↑m : ℂ) = ↑((↑m : ℝ) * Real.pi) from by push_cast; ring,
        ← Complex.ofReal_cos, show (↑m : ℝ) * Real.pi = ↑m * Real.pi from by norm_cast,
        Real.cos_int_mul_pi]
    exact Complex.ofReal_ne_zero.mpr (zpow_ne_zero m (by norm_num : (-1 : ℝ) ≠ 0))
  have hpi_ne : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg_val : g (↑m : ℂ) = deriv f ↑m / (↑Real.pi * Complex.cos (↑Real.pi * ↑m)) := by
    rw [hdf.deriv]; field_simp [mul_ne_zero hpi_ne hcos_ne]
  rw [hg_val, norm_div, norm_mul]
  have : ‖Complex.cos (↑Real.pi * (↑m : ℂ))‖ = 1 := by
    rw [show (↑Real.pi : ℂ) * (↑m : ℂ) = ↑((↑m : ℝ) * Real.pi) from by push_cast; ring,
        ← Complex.ofReal_cos, show (↑m : ℝ) * Real.pi = ↑m * Real.pi from by norm_cast,
        Real.cos_int_mul_pi, Complex.norm_real]; simp
  rw [this, mul_one, show ‖(↑Real.pi : ℂ)‖ = Real.pi from by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]]
  exact div_le_div_of_nonneg_right (hMd ↑m) (le_of_lt Real.pi_pos)

private theorem not_integrable_of_periodic_pos {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf_per : Function.Periodic f T) (hf_nn : ∀ x, 0 ≤ f x)
    (hf_int_pos : 0 < ∫ x in (0 : ℝ)..T, f x) :
    ¬MeasureTheory.Integrable f MeasureTheory.volume := by
  intro hf_int
  have htend := hf_per.tendsto_atTop_intervalIntegral_of_pos hf_int_pos hT
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun t => ∫ x in (0 : ℝ)..t, f x) := by
    refine ⟨∫ x, f x, ?_⟩
    rw [Filter.eventually_map, Filter.eventually_atTop]
    exact ⟨0, fun t ht => by
      rw [intervalIntegral.integral_of_le ht]
      exact MeasureTheory.setIntegral_le_integral hf_int (Eventually.of_forall hf_nn)⟩
  exact not_isBoundedUnder_of_tendsto_atTop htend hbdd

private theorem norm_sin_mul_sq_periodic (c : ℂ) :
    Function.Periodic (fun t : ℝ => ‖Complex.sin (↑Real.pi * ↑t) * c‖ ^ 2) 1 := by
  intro t; change ‖Complex.sin (↑Real.pi * ↑(t + 1)) * c‖ ^ 2 = _
  congr 1
  have : (↑Real.pi : ℂ) * ↑(t + 1) = ↑Real.pi * ↑t + ↑Real.pi := by push_cast; ring
  rw [this, Complex.sin_add_pi, neg_mul, norm_neg]

-- sin(πx)·c is not L²(ℝ) unless c = 0
theorem sin_const_not_L2 (c : ℂ) (hc : c ≠ 0) :
    ¬MeasureTheory.Integrable
      (fun t : ℝ => ‖Complex.sin (↑Real.pi * ↑t) * c‖ ^ 2)
      MeasureTheory.volume := by
  apply not_integrable_of_periodic_pos one_pos (norm_sin_mul_sq_periodic c) (fun x => by positivity)
  apply intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
  · exact (Continuous.pow (Continuous.norm (Continuous.mul
      (Complex.continuous_sin.comp (continuous_const.mul Complex.continuous_ofReal))
      continuous_const)) 2).continuousOn
  · intro x _; positivity
  · refine ⟨1/2, ⟨by norm_num, by norm_num⟩, pow_pos (norm_pos_iff.mpr (mul_ne_zero ?_ hc)) 2⟩
    rw [show (↑Real.pi : ℂ) * ↑(1/2 : ℝ) = ↑(Real.pi / 2 : ℝ) from by push_cast; ring]
    simp only [ne_eq]
    intro h; have := congr_arg Complex.re h; simp at this

end AnalyticContinuation

/-! ## FE Preservation and Zero Pairing under Bandlimiting -/

section ZeroCorrespondence

-- Functional equation: f(s) = f(1-s)
def FunctionalEquation (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, f s = f (1 - s)

-- Real-valued on critical line
def RealOnCriticalLine (f : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, (f (1 / 2 + ↑t * Complex.I)).im = 0

-- Even Mellin spectrum
def EvenMellinSpectrum (fhat : ℝ → ℂ) : Prop :=
  Function.Even fhat

-- Bandlimiting preserves even spectrum: χ_{|ω|≤ωN} is even → f̂·χ is even
theorem bandlimit_preserves_even (fhat : ℝ → ℂ) (omegaN : ℝ)
    (heven : EvenMellinSpectrum fhat) :
    EvenMellinSpectrum (fun ω => if |ω| ≤ omegaN then fhat ω else 0) := by
  intro ω
  simp only [abs_neg]
  split_ifs with h1
  · exact heven ω
  · rfl

-- FE + zero → paired zero: g(ρ)=0 → g(1-ρ)=0
theorem functional_equation_zero_pair (g : ℂ → ℂ)
    (hFE : FunctionalEquation g) (s : ℂ) (hs : g s = 0) :
    g (1 - s) = 0 := hFE s ▸ hs

-- Critical line preserved under s ↦ 1-s
theorem critical_line_pair (s : ℂ) (hre : s.re = 1 / 2) :
    (1 - s).re = 1 / 2 := by
  simp only [Complex.sub_re, Complex.one_re]; linarith

-- Off-line zeros are distinct from their FE pair
theorem off_line_distinct (s : ℂ) (hre : s.re ≠ 1 / 2) :
    s ≠ 1 - s := by
  intro h
  apply hre
  have := congr_arg Complex.re h
  simp only [Complex.sub_re, Complex.one_re] at this; linarith

-- Critical line zero has Re = 1/2 (from parametrization)
theorem critical_line_zero_re (t₀ : ℝ) :
    (1 / 2 + ↑t₀ * Complex.I).re = 1 / 2 := by
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re]

-- s = 1-s implies Re(s) = 1/2 (note: also forces Im(s) = 0, so s = 1/2)
theorem re_half_from_FE_uniqueness
    (g : ℂ → ℂ) (_ : FunctionalEquation g)
    (rho_tilde : ℂ) (_ : g rho_tilde = 0)
    (hself : rho_tilde = 1 - rho_tilde) :
    rho_tilde.re = 1 / 2 := by
  have := congr_arg Complex.re hself
  simp only [Complex.sub_re, Complex.one_re] at this; linarith

-- Structural properties of a bandlimited FE-preserving function
-- Proven: FE pairing, real on critical line, critical-line zeros have Re=1/2 (tautological)
-- NOT proven: all zeros lie on the critical line (equivalent to RH for g)
structure BandlimitedZeroStructure where
  g : ℂ → ℂ
  g_FE : FunctionalEquation g
  g_real : RealOnCriticalLine g
  G : ℝ → ℝ
  G_eq : ∀ t : ℝ, (↑(G t) : ℂ) = g (1 / 2 + ↑t * Complex.I)
  zero_pair : ∀ s, g s = 0 → g (1 - s) = 0
  -- Tautological: critical-line zeros (parametrized by real t) have Re = 1/2
  re_half : ∀ t₀ : ℝ, G t₀ = 0 → (1/2 + ↑t₀ * Complex.I).re = 1/2

-- Construct the structure from FE
def mkBandlimitedZeroStructure (g : ℂ → ℂ) (G : ℝ → ℝ)
    (hFE : FunctionalEquation g) (hreal : RealOnCriticalLine g)
    (hG : ∀ t : ℝ, (↑(G t) : ℂ) = g (1 / 2 + ↑t * Complex.I)) :
    BandlimitedZeroStructure where
  g := g
  g_FE := hFE
  g_real := hreal
  G := G
  G_eq := hG
  zero_pair := fun s hs => functional_equation_zero_pair g hFE s hs
  re_half := fun t₀ _ => critical_line_zero_re t₀

-- Spectral decomposition: f = bandlimited + high-frequency
def SpectrallyFiltered (f g : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, ∃ fBL fperp : ℂ,
    f s = fBL + fperp ∧ g s = fBL

-- Zeros of f that are not zeros of g come from the high-frequency part
theorem spectral_trivial_zeros (f g : ℂ → ℂ) (_ : SpectrallyFiltered f g)
    (s : ℂ) (hf : f s = 0) (hg : g s ≠ 0) :
    f s - g s ≠ 0 := by
  rw [hf, zero_sub]; exact neg_ne_zero.mpr hg

-- Zero set definitions
def ZeroSet (g : ℂ → ℂ) : Set ℂ := {s | g s = 0}
def DiscreteZeroSet (a : ℤ → ℂ) : Set ℤ := {n | a n = 0}
def CriticalLineZeroSet (g : ℂ → ℂ) : Set ℝ :=
  {t | g (1 / 2 + ↑t * Complex.I) = 0}

-- DiscreteZeroSet is countable (ℤ is countable)
theorem discreteZeroSet_countable (a : ℤ → ℂ) :
    (DiscreteZeroSet a).Countable :=
  Set.countable_univ.mono (Set.subset_univ _)

-- FE symmetry on ZeroSet
theorem zeroSet_FE_symm (g : ℂ → ℂ) (hFE : FunctionalEquation g) (s : ℂ) :
    s ∈ ZeroSet g ↔ (1 - s) ∈ ZeroSet g := by
  simp only [ZeroSet, Set.mem_setOf_eq]
  exact ⟨fun hs => by rwa [← hFE s], fun h1s => by rwa [hFE s]⟩

-- Lattice zeros embed into continuous zeros
theorem discreteZero_to_continuousZero (a : ℤ → ℂ) (m : ℤ)
    (hm : m ∈ DiscreteZeroSet a) :
    (↑m : ℂ) ∈ ZeroSet (sincRecon a) := by
  simp only [ZeroSet, Set.mem_setOf_eq, sincRecon_eval_int]; exact hm

-- Continuous zeros at integers imply discrete zeros
theorem continuousZero_to_discreteZero (a : ℤ → ℂ) (m : ℤ)
    (hm : (↑m : ℂ) ∈ ZeroSet (sincRecon a)) :
    m ∈ DiscreteZeroSet a := by
  simp only [ZeroSet, Set.mem_setOf_eq, sincRecon_eval_int] at hm; exact hm

-- Exact correspondence: ZeroSet(sincRecon a) at integers = DiscreteZeroSet a
theorem zeroSet_int_iff_discreteZeroSet (a : ℤ → ℂ) (m : ℤ) :
    (↑m : ℂ) ∈ ZeroSet (sincRecon a) ↔ m ∈ DiscreteZeroSet a := by
  simp only [ZeroSet, DiscreteZeroSet, Set.mem_setOf_eq, sincRecon_eval_int]

-- Nonzero samples are preserved: a(n) ≠ 0 → sincRecon a n ≠ 0
theorem nonzero_sample_preserved (a : ℤ → ℂ) (m : ℤ) (hm : a m ≠ 0) :
    sincRecon a ↑m ≠ 0 := by
  rw [sincRecon_eval_int]; exact hm

-- Discrete zero lifts to continuous zero preserving real part
theorem discrete_zero_lifts_to_continuous (a : ℤ → ℂ) (m : ℤ)
    (hm : m ∈ DiscreteZeroSet a) :
    ∃ ρ ∈ ZeroSet (sincRecon a), ρ.re = ↑m :=
  ⟨↑m, discreteZero_to_continuousZero a m hm, Complex.intCast_re m⟩

-- Continuous zero at integer projects back to discrete zero
theorem continuous_integer_zero_projects (a : ℤ → ℂ) (m : ℤ)
    (hm : (↑m : ℂ) ∈ ZeroSet (sincRecon a)) :
    ∃ n ∈ DiscreteZeroSet a, (↑m : ℂ).re = (↑n : ℝ) :=
  ⟨m, continuousZero_to_discreteZero a m hm, rfl⟩

-- Re-projection of ZeroSet at integers = image of DiscreteZeroSet
theorem re_projection_correspondence (a : ℤ → ℂ) :
    (fun ρ => ρ.re) '' (ZeroSet (sincRecon a) ∩ Set.range (fun m : ℤ => (↑m : ℂ))) =
    (fun m : ℤ => (↑m : ℝ)) '' (DiscreteZeroSet a) := by
  ext x
  simp only [Set.mem_image, Set.mem_inter_iff, ZeroSet, Set.mem_setOf_eq,
    Set.mem_range, DiscreteZeroSet]
  constructor
  · rintro ⟨ρ, ⟨hρ_zero, m, rfl⟩, rfl⟩
    rw [sincRecon_eval_int] at hρ_zero
    exact ⟨m, hρ_zero, by simp [Complex.intCast_re]⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨↑m, ⟨by rw [sincRecon_eval_int]; exact hm, m, rfl⟩, Complex.intCast_re m⟩

-- ZeroSet of sincC is infinite (zeros at all nonzero integers)
theorem sincC_zeroSet_infinite : Set.Infinite (ZeroSet sincC) := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (↑((n : ℤ) + 1) : ℂ))
  · intro a b hab
    simp only at hab
    have : (a : ℤ) + 1 = (b : ℤ) + 1 := by exact_mod_cast hab
    omega
  · intro n
    simp only [ZeroSet, Set.mem_setOf_eq]
    exact sincC_int ((n : ℤ) + 1) (by omega)

-- Zeros of non-constant entire function are isolated (identity theorem)
theorem entire_zeros_isolated (g : ℂ → ℂ) (h_entire : IsEntire g)
    (h_nz : ∃ z₀ : ℂ, g z₀ ≠ 0) (z : ℂ) (_ : g z = 0) :
    ∀ᶠ w in nhdsWithin z {z}ᶜ, g w ≠ 0 := by
  have h_diff : Differentiable ℂ g := h_entire
  rcases (h_diff.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with
      h_all_zero | h_isolated
  · exfalso
    obtain ⟨z₀, hz₀⟩ := h_nz
    have h_aon : AnalyticOnNhd ℂ g Set.univ :=
      h_diff.differentiableOn.analyticOnNhd isOpen_univ
    have h_freq : ∃ᶠ w in nhdsWithin z {z}ᶜ, g w = 0 :=
      (h_all_zero.filter_mono nhdsWithin_le_nhds).frequently
    exact hz₀ (h_aon.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ z) h_freq (Set.mem_univ z₀))
  · exact h_isolated

-- ZeroSet of entire function is IsDiscrete
theorem entire_zeroSet_isDiscrete (g : ℂ → ℂ) (h_entire : IsEntire g)
    (h_nz : ∃ z₀ : ℂ, g z₀ ≠ 0) :
    IsDiscrete (ZeroSet g) := by
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  rw [Filter.inf_principal_eq_bot]
  exact (entire_zeros_isolated g h_entire h_nz z hz).mono fun w hw hmem => hw hmem

-- ZeroSet of entire function is closed
theorem entire_zeroSet_isClosed (g : ℂ → ℂ) (h_entire : IsEntire g) :
    IsClosed (ZeroSet g) :=
  isClosed_singleton.preimage (show Differentiable ℂ g from h_entire).continuous

-- ZeroSet ∩ closedBall is finite (compact + discrete)
theorem zeroSet_inter_ball_finite (g : ℂ → ℂ) (h_entire : IsEntire g)
    (h_nz : ∃ z₀ : ℂ, g z₀ ≠ 0) (n : ℕ) :
    (ZeroSet g ∩ Metric.closedBall 0 (↑n)).Finite :=
  ((isCompact_closedBall 0 ↑n).inter_left
    (entire_zeroSet_isClosed g h_entire)).finite
    ((entire_zeroSet_isDiscrete g h_entire h_nz).mono Set.inter_subset_left)

-- ZeroSet of non-constant entire function is countable
theorem entire_zeroSet_countable (g : ℂ → ℂ)
    (h_entire : IsEntire g) (h_nz : ∃ z : ℂ, g z ≠ 0) :
    (ZeroSet g).Countable := by
  have : ZeroSet g = ⋃ n : ℕ, ZeroSet g ∩ Metric.closedBall 0 (n : ℝ) := by
    ext z; constructor
    · intro hz
      refine Set.mem_iUnion.mpr ⟨⌈‖z‖⌉₊, hz, ?_⟩
      exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact Nat.le_ceil _)
    · intro hz
      obtain ⟨_, h, _⟩ := Set.mem_iUnion.mp hz
      exact h
  rw [this]
  exact Set.countable_iUnion fun n =>
    (zeroSet_inter_ball_finite g h_entire h_nz n).countable

end ZeroCorrespondence

/-! ## Mellin-Poisson Aliasing Structure -/

section MellinPoisson

-- Aliased spectrum: periodic folding with period T
noncomputable def aliasedSpectrum (fhat : ℝ → ℂ) (T : ℝ) (ω : ℝ) : ℂ :=
  ∑' k : ℤ, fhat (ω + k * T)

private def intNeg : ℤ ≃ ℤ where
  toFun k := -k
  invFun k := -k
  left_inv k := by ring
  right_inv k := by ring

-- Aliasing preserves even spectrum
theorem aliasing_preserves_even (fhat : ℝ → ℂ) (T : ℝ)
    (heven : ∀ ω : ℝ, fhat (-ω) = fhat ω) :
    ∀ ω : ℝ, aliasedSpectrum fhat T (-ω) = aliasedSpectrum fhat T ω := by
  intro ω
  unfold aliasedSpectrum
  have step1 : (fun k : ℤ => fhat (-ω + ↑k * T)) =
      fun k : ℤ => fhat (ω - ↑k * T) := by
    ext k
    rw [show -ω + ↑k * T = -(ω - ↑k * T) from by ring]
    exact heven _
  rw [step1, ← Equiv.tsum_eq intNeg]
  congr 1; ext k
  simp [intNeg]

end MellinPoisson

/-! ## φ-Lattice D6 Compatibility -/

section LatticeCompatibility

def D6Compatible (b : ℝ) : Prop :=
  ∃ k : ℕ, k ≥ 1 ∧ b ^ k = φ

theorem phi_D6_compatible : D6Compatible φ :=
  ⟨1, le_refl 1, pow_one φ⟩

theorem phi_coarsest_compatible (b : ℝ) (hb : 1 < b) (hcompat : D6Compatible b) :
    b ≤ φ := by
  obtain ⟨k, hk, hbk⟩ := hcompat
  by_cases hk1 : k = 1
  · rw [hk1, pow_one] at hbk; linarith
  · have hk_ge2 : k ≥ 2 := by omega
    have hb_pos : 0 < b := by linarith
    have : b ^ k ≥ b ^ 2 := pow_le_pow_right₀ (le_of_lt hb) hk_ge2
    have : b ^ 2 > b := by nlinarith
    rw [hbk] at *
    nlinarith [φ_gt_one]

end LatticeCompatibility

/-! ## Discrete Rotation Representation -/

section DiscreteRotation

private lemma psi_eq_neg_phi_inv : ψ = -1 * φ⁻¹ := by
  have h : φ⁻¹ = -ψ := Real.inv_goldenRatio
  nlinarith

private theorem psi_zpow_decomp (k : ℤ) : ψ ^ k = (-1) ^ k * φ ^ (-k) := by
  rw [show ψ = -1 * φ⁻¹ from psi_eq_neg_phi_inv, mul_zpow, inv_zpow, zpow_neg]

theorem psi_on_phi_lattice (n k : ℤ) (x₀ : ℝ) :
    ψ ^ k * (φ ^ n * x₀) = (-1) ^ k * (φ ^ (n - k) * x₀) := by
  have hφ : φ ≠ 0 := ne_of_gt phi_pos
  rw [psi_zpow_decomp]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, ← zpow_add₀ hφ]
  congr 1
  ring_nf

-- ψ^k on φ-lattice: odd k → π-rotation, even k → pure shift
theorem D6_rotation_parity (k : ℤ) (hk : Odd k) (n : ℤ) (x₀ : ℝ) :
    ψ ^ k * (φ ^ n * x₀) = -(φ ^ (n - k) * x₀) := by
  rw [psi_on_phi_lattice, hk.neg_one_zpow]; ring

theorem D6_shift_parity (k : ℤ) (hk : Even k) (n : ℤ) (x₀ : ℝ) :
    ψ ^ k * (φ ^ n * x₀) = φ ^ (n - k) * x₀ := by
  rw [psi_on_phi_lattice, hk.neg_one_zpow]; ring

-- D6 probes both f and π-rotated f simultaneously
theorem D6_dual_probe (f : ℝ → ℝ) (n : ℤ) (x₀ : ℝ) :
    (f (ψ ^ (1:ℤ) * (φ ^ n * x₀)) = f (-(φ ^ (n-1) * x₀))) ∧
    (f (ψ ^ (2:ℤ) * (φ ^ n * x₀)) = f (φ ^ (n-2) * x₀)) ∧
    (f (ψ ^ (3:ℤ) * (φ ^ n * x₀)) = f (-(φ ^ (n-3) * x₀))) :=
  ⟨by congr 1; exact D6_rotation_parity 1 ⟨0, by ring⟩ n x₀,
   by congr 1; exact D6_shift_parity 2 ⟨1, by ring⟩ n x₀,
   by congr 1; exact D6_rotation_parity 3 ⟨1, by ring⟩ n x₀⟩

end DiscreteRotation

end FUST.MellinSampling
