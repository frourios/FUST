/-
Hurwitz Transfer Principle

Proved via the minimum modulus principle (max modulus applied to 1/f):
1. Topological transfer: limits of Re=c points stay on Re=c
2. Limit analyticity: locally uniform limits are holomorphic
3. Isolated zeros: non-trivial analytic limits have isolated zeros
4. Min modulus contradiction: non-vanishing + small center + large boundary → ⊥
5. Eventually zero: F_N eventually has zeros near zeros of f
6. Full Hurwitz transfer: no Rouché needed
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace FUST.Hurwitz

open Complex Filter Set Topology Metric

/-! ## Section 1: Vertical Line Topology -/

theorem isClosed_re_eq (c : ℝ) : IsClosed {s : ℂ | s.re = c} :=
  isClosed_eq Complex.reCLM.continuous continuous_const

theorem re_eq_of_tendsto (c : ℝ) (s_seq : ℕ → ℂ) (s : ℂ)
    (h_re : ∀ n, (s_seq n).re = c)
    (h_lim : Tendsto s_seq atTop (nhds s)) : s.re = c :=
  (isClosed_re_eq c).mem_of_tendsto h_lim (Eventually.of_forall h_re)

/-! ## Section 2: Limit Analyticity -/

theorem differentiableOn_of_tendstoLocallyUniformly
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ N, DifferentiableOn ℂ (F N) univ)
    (hconv : TendstoLocallyUniformly F f atTop) :
    DifferentiableOn ℂ f univ :=
  (tendstoLocallyUniformlyOn_univ.mpr hconv).differentiableOn
    (Eventually.of_forall hF) isOpen_univ

theorem analyticOnNhd_of_tendstoLocallyUniformly
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ N, DifferentiableOn ℂ (F N) univ)
    (hconv : TendstoLocallyUniformly F f atTop) :
    AnalyticOnNhd ℂ f univ :=
  (differentiableOn_of_tendstoLocallyUniformly F f hF hconv).analyticOnNhd isOpen_univ

theorem isolated_zeros_of_analytic (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ)
    (hne : ∃ s, f s ≠ 0) (s₀ : ℂ) :
    f s₀ ≠ 0 ∨ ∀ᶠ z in nhdsWithin s₀ {s₀}ᶜ, f z ≠ 0 := by
  have ha : AnalyticAt ℂ f s₀ := hf s₀ (mem_univ s₀)
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
  · right; exfalso; obtain ⟨w, hw⟩ := hne
    exact hw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ s₀) h (mem_univ w))
  · exact Or.inr h

theorem isolated_zeros_of_limit
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ N, DifferentiableOn ℂ (F N) univ)
    (hconv : TendstoLocallyUniformly F f atTop)
    (hne : ∃ s, f s ≠ 0) (s₀ : ℂ) :
    f s₀ ≠ 0 ∨ ∀ᶠ z in nhdsWithin s₀ {s₀}ᶜ, f z ≠ 0 :=
  isolated_zeros_of_analytic f
    (analyticOnNhd_of_tendstoLocallyUniformly F f hF hconv) hne s₀

/-! ## Section 3: Minimum Modulus Principle -/

/-- Non-vanishing holomorphic f with |f(s₀)| < δ and |f| ≥ δ on sphere → ⊥ -/
theorem min_modulus_contradiction (c s₀ : ℂ) (r δ : ℝ) (f : ℂ → ℂ) (hr : 0 < r)
    (hd : DiffContOnCl ℂ f (ball c r))
    (hne : ∀ z ∈ closedBall c r, f z ≠ 0)
    (hs₀ : s₀ ∈ ball c r)
    (hδ : 0 < δ)
    (hsphere : ∀ z ∈ sphere c r, δ ≤ ‖f z‖)
    (hsmall : ‖f s₀‖ < δ) : False := by
  set g := fun z => (f z)⁻¹ with hg_def
  have hg_diff : DiffContOnCl ℂ g (ball c r) := by
    constructor
    · intro z hz
      exact ((hd.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hz)).inv
        (hne z (ball_subset_closedBall hz))).differentiableWithinAt
    · rw [closure_ball c (ne_of_gt hr)]
      exact hd.continuousOn_ball.inv₀ (fun z hz => hne z hz)
  obtain ⟨z_max, hz_max_mem, hz_max_max⟩ :=
    (isCompact_closedBall c r).exists_isMaxOn
      ⟨s₀, ball_subset_closedBall hs₀⟩
      (continuous_norm.comp_continuousOn hg_diff.continuousOn_ball)
  have hmax_s₀ : ‖g s₀‖ ≤ ‖g z_max‖ := hz_max_max (ball_subset_closedBall hs₀)
  have hg_s₀_bound : δ⁻¹ < ‖g s₀‖ := by
    simp only [hg_def, norm_inv]
    exact inv_strictAnti₀ (norm_pos_iff.mpr (hne s₀ (ball_subset_closedBall hs₀))) hsmall
  have hg_sphere : ∀ z ∈ sphere c r, ‖g z‖ ≤ δ⁻¹ := by
    intro z hz; simp only [hg_def, norm_inv]; exact inv_anti₀ hδ (hsphere z hz)
  have hz_max_ball : z_max ∈ ball c r := by
    by_contra h
    have : z_max ∈ sphere c r := by
      rw [← ball_union_sphere] at hz_max_mem
      exact hz_max_mem.elim (fun h' => absurd h' h) id
    linarith [hg_sphere z_max this, hmax_s₀]
  have heq : EqOn (norm ∘ g) (Function.const ℂ ‖g z_max‖) (closure (ball c r)) :=
    Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn
      (convex_ball c r).isPreconnected isOpen_ball hg_diff hz_max_ball
      (fun z hz => hz_max_max (ball_subset_closedBall hz))
  rw [closure_ball c (ne_of_gt hr)] at heq
  obtain ⟨z₁, hz₁⟩ : (sphere c r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have h_eq_z₁ : ‖g z₁‖ = ‖g z_max‖ := heq (sphere_subset_closedBall hz₁)
  have h_le_z₁ : ‖g z₁‖ ≤ δ⁻¹ := hg_sphere z₁ hz₁
  linarith

/-! ## Section 4: Isolated Zeros and Ball Selection -/

theorem exists_ball_no_other_zeros (f : ℂ → ℂ) (s₀ : ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (hne : ∃ s, f s ≠ 0) :
    ∃ r > 0, ∀ z ∈ closedBall s₀ r, z ≠ s₀ → f z ≠ 0 := by
  have hiso : ∀ᶠ z in nhdsWithin s₀ {s₀}ᶜ, f z ≠ 0 := by
    rcases (hf s₀ (mem_univ s₀)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso; obtain ⟨w, hw⟩ := hne
      exact hw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ s₀) h (mem_univ w))
    · exact h
  rw [eventually_nhdsWithin_iff] at hiso
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hiso
  exact ⟨ε / 2, half_pos hε, fun z hz hne_z =>
    hball (lt_of_le_of_lt hz (half_lt_self hε)) (Set.mem_compl_singleton_iff.mpr hne_z)⟩

/-! ## Section 5: Hurwitz Zero Convergence (proved via min modulus) -/

/-- F_N eventually has a zero in closedBall s₀ r -/
theorem hurwitz_eventually_zero
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF_diff : ∀ N, DifferentiableOn ℂ (F N) univ)
    (hconv : TendstoLocallyUniformly F f atTop)
    (s₀ : ℂ) (hs₀ : f s₀ = 0)
    (r : ℝ) (hr : 0 < r)
    (hf_nz : ∀ z ∈ closedBall s₀ r, z ≠ s₀ → f z ≠ 0) :
    ∀ᶠ N in atTop, ∃ z ∈ closedBall s₀ r, F N z = 0 := by
  have hf_cont : ContinuousOn f (closedBall s₀ r) :=
    ((differentiableOn_of_tendstoLocallyUniformly F f hF_diff hconv).continuousOn).mono
      (fun _ _ => mem_univ _)
  have hf_sphere_nz : ∀ z ∈ sphere s₀ r, f z ≠ 0 := fun z hz =>
    hf_nz z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.ne')
  obtain ⟨z_min, hz_min_mem, hz_min_min⟩ :=
    (isCompact_sphere s₀ r).exists_isMinOn (NormedSpace.sphere_nonempty.mpr hr.le)
      (continuous_norm.comp_continuousOn (hf_cont.mono sphere_subset_closedBall))
  set δ := ‖f z_min‖
  have hδ : 0 < δ := norm_pos_iff.mpr (hf_sphere_nz z_min hz_min_mem)
  have hconv_unif : TendstoUniformlyOn F f atTop (closedBall s₀ r) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv)
      (closedBall s₀ r) (isCompact_closedBall s₀ r)
  have hsphere_bound : ∀ z ∈ sphere s₀ r, δ ≤ ‖f z‖ := fun z hz => hz_min_min hz
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv_unif (δ / 2) (half_pos hδ)]
    with N hN
  by_contra hno_zero
  push_neg at hno_zero
  have hFN_small : ‖F N s₀‖ < δ / 2 := by
    have h := hN s₀ (mem_closedBall_self hr.le)
    rwa [hs₀, dist_zero_left] at h
  have hFN_sphere : ∀ z ∈ sphere s₀ r, δ / 2 ≤ ‖F N z‖ := by
    intro z hz
    have hdist : dist (f z) (F N z) < δ / 2 := hN z (sphere_subset_closedBall hz)
    rw [dist_eq_norm] at hdist
    linarith [norm_sub_norm_le (f z) (F N z), hsphere_bound z hz]
  exact min_modulus_contradiction s₀ s₀ r (δ / 2) (F N) hr
    ((hF_diff N).diffContOnCl_ball (fun _ _ => mem_univ _))
    (fun z hz h0 => hno_zero z hz h0)
    (mem_ball_self hr) (half_pos hδ) hFN_sphere hFN_small

/-- Hurwitz zero convergence: zeros of the limit are approached by zeros of F_N -/
theorem hurwitz_zero_convergence
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF_diff : ∀ N, DifferentiableOn ℂ (F N) univ)
    (hconv : TendstoLocallyUniformly F f atTop)
    (hne : ∃ s, f s ≠ 0) (s₀ : ℂ) (hs₀ : f s₀ = 0) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∃ z ∈ ball s₀ ε, F N z = 0 := by
  have hf_analytic : AnalyticOnNhd ℂ f univ :=
    (differentiableOn_of_tendstoLocallyUniformly F f hF_diff hconv).analyticOnNhd isOpen_univ
  obtain ⟨r₀, hr₀, hno_other⟩ := exists_ball_no_other_zeros f s₀ hf_analytic hne
  intro ε hε
  set r := min r₀ (ε / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hε)
  filter_upwards [hurwitz_eventually_zero F f hF_diff hconv s₀ hs₀ r hr
    (fun z hz hne_z => hno_other z (closedBall_subset_closedBall (min_le_left r₀ _) hz) hne_z)]
    with N ⟨z, hz_mem, hz_zero⟩
  exact ⟨z, closedBall_subset_ball
    (lt_of_le_of_lt (min_le_right r₀ _) (half_lt_self hε)) hz_mem, hz_zero⟩

/-! ## Section 6: Topological Transfer and Full Hurwitz Transfer -/

/-- Topological transfer: if F_N zeros near f zeros have Re = c, then f zeros have Re = c -/
theorem topological_hurwitz_transfer (c : ℝ)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF_zeros : ∀ N s, F N s = 0 → s.re = c)
    (hzero_conv : ∀ s, f s = 0 →
      ∀ ε > 0, ∀ᶠ N in atTop, ∃ z ∈ ball s ε, F N z = 0) :
    ∀ s, f s = 0 → s.re = c := by
  intro s hs
  by_contra hne
  set d := |s.re - c|
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨_, z, hz_ball, hz_zero⟩ := (hzero_conv s hs (d / 2) (half_pos hd)).exists
  have hz_re : z.re = c := hF_zeros _ z hz_zero
  have hz_dist : dist z s < d / 2 := mem_ball.mp hz_ball
  have hre_dist : |z.re - s.re| ≤ ‖z - s‖ := abs_re_le_norm (z - s)
  rw [Complex.dist_eq] at hz_dist
  rw [hz_re] at hre_dist
  linarith [abs_sub_comm s.re c]

/-- Hurwitz transfer: locally uniform limits preserve vertical line zeros -/
theorem hurwitzTransfer (c : ℝ)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF_diff : ∀ N, DifferentiableOn ℂ (F N) univ)
    (hF_zeros : ∀ N s, F N s = 0 → s.re = c)
    (hconv : TendstoLocallyUniformly F f atTop)
    (hne : ∃ s, f s ≠ 0) :
    ∀ s, f s = 0 → s.re = c :=
  topological_hurwitz_transfer c F f hF_zeros
    (fun s hs => hurwitz_zero_convergence F f hF_diff hconv hne s hs)

end FUST.Hurwitz
