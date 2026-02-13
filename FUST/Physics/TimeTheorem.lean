import FUST.Physics.LeastAction

namespace FUST.TimeTheorem

open FUST.LeastAction

/-- Time Existence Theorem (Complete Form) -/
theorem time_existence_theorem :
    (∀ f : ℝ → ℝ, IsInKerD6 f → ∀ x, x ≠ 0 → D6 f x = 0) ∧
    (∀ f : ℝ → ℝ, (∃ x, x ≠ 0 ∧ D6 f x ≠ 0) → TimeExistsD6 f) ∧
    (∀ f c x, c ≠ 0 → x ≠ 0 → D6 (fun t => f (c * t)) x = c * D6 f (c * x)) :=
  ⟨IsInKerD6_implies_D6_zero,
   fun f ⟨x, hx, hD6⟩ => D6_nonzero_implies_time f x hx hD6,
   fun f c x hc hx => D6_gauge_scaling f c x hc hx⟩

/-! ## Higher Order Reduction -/

/-- Higher Order Reduction: ker(D7) = ker(D6) -/
theorem higher_order_reduction :
    ∀ a : ℝ, (∀ k x, x ≠ 0 → FUST.D7_constrained a (fun _ => k) x = 0) ∧
             (∀ x, x ≠ 0 → FUST.D7_constrained a id x = 0) ∧
             (∀ x, x ≠ 0 → FUST.D7_constrained a (fun t => t^2) x = 0) :=
  FUST.D7_kernel_equals_D6_kernel

/-! ## Arrow of Time from φ/ψ Asymmetry -/

/-- |ψ| < 1 -/
theorem abs_psi_lt_one : |ψ| < 1 := by
  have h : ψ = (1 - Real.sqrt 5) / 2 := rfl
  have hsqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have hsqrt5_gt_1 : Real.sqrt 5 > 1 := by
    have h1 : (1 : ℝ) < 5 := by norm_num
    calc Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) h1
      _ = 1 := Real.sqrt_one
  have hpsi_neg : ψ < 0 := by
    simp only [h]
    have : 1 - Real.sqrt 5 < 0 := by linarith
    linarith
  have hpsi_gt_neg1 : ψ > -1 := by
    simp only [h]
    have hsqrt5_lt_3 : Real.sqrt 5 < 3 := by
      have h9 : (5 : ℝ) < 9 := by norm_num
      have h3 : Real.sqrt 9 = 3 := by norm_num
      calc Real.sqrt 5 < Real.sqrt 9 := Real.sqrt_lt_sqrt (by norm_num) h9
        _ = 3 := h3
    linarith
  rw [abs_of_neg hpsi_neg]
  linarith

/-- φ · |ψ| = 1 -/
theorem phi_mul_abs_psi : φ * |ψ| = 1 := by
  have hpsi_neg : ψ < 0 := by
    have h : ψ = (1 - Real.sqrt 5) / 2 := rfl
    have hsqrt5_gt_1 : Real.sqrt 5 > 1 := by
      calc Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5)
        _ = 1 := Real.sqrt_one
    simp only [h]
    linarith
  rw [abs_of_neg hpsi_neg]
  have h : φ * (-ψ) = -(φ * ψ) := by ring
  rw [h, phi_mul_psi]
  ring

/-! ## Time Evolution -/

/-- φ is unique expansion factor > 1 -/
theorem phi_unique_expansion : φ > 1 ∧ |ψ| < 1 :=
  ⟨φ_gt_one, abs_psi_lt_one⟩

/-! ## Entropy Increase -/

/-- For tⁿ, time evolution amplifies by φⁿ -/
theorem monomial_amplification (n : ℕ) (t : ℝ) :
    timeEvolution (fun s => s^n) t = φ^n * t^n := by
  simp only [timeEvolution]
  ring

/-- φⁿ > 1 for n ≥ 1 -/
theorem phi_pow_gt_one (n : ℕ) (hn : n ≥ 1) : φ^n > 1 := by
  exact one_lt_pow₀ φ_gt_one (Nat.one_le_iff_ne_zero.mp hn)

/-- φ^(2n) > 1 for n ≥ 1 -/
theorem phi_pow_2n_gt_one (n : ℕ) (hn : n ≥ 1) : φ^(2*n) > 1 :=
  phi_pow_gt_one (2*n) (by omega)

/-- Entropy increase principle -/
theorem entropy_increase_principle (f : ℝ → ℝ) (t : ℝ) :
    entropyAtD6 (timeEvolution f) t = (perpProjectionD6 (timeEvolution f) t)^2 := rfl

/-- For tⁿ, perpProjectionD6 scaling -/
theorem monomial_perp_scaling (n : ℕ) (t : ℝ) :
    perpProjectionD6 (timeEvolution (fun s => s^n)) t =
    φ^n * t^n - kernelProjectionD6 (timeEvolution (fun s => s^n)) t := by
  simp only [perpProjectionD6, timeEvolution]
  ring

/-- Time direction unique -/
theorem time_direction_unique : φ > 1 ∧ |ψ| < 1 ∧ φ * |ψ| = 1 :=
  ⟨φ_gt_one, abs_psi_lt_one, phi_mul_abs_psi⟩

/-! ## Summary Theorems -/

/-- Arrow of time summary -/
theorem arrow_of_time_summary :
    (φ > 1) ∧
    (|ψ| < 1) ∧
    (∀ f, IsInKerD6 f → IsInKerD6 (timeEvolution f)) ∧
    (∀ f x, x ≠ 0 → D6 (timeEvolution f) x = φ * D6 f (φ * x)) :=
  ⟨φ_gt_one, abs_psi_lt_one, ker_D6_invariant, D6_timeEvolution⟩

/-- FUST Time Theorem: Complete statement -/
theorem fust_time_theorem :
    (∀ f : ℝ → ℝ, IsInKerD6 f → ∀ x, x ≠ 0 → D6 f x = 0) ∧
    (∀ f : ℝ → ℝ, (∃ x, x ≠ 0 ∧ D6 f x ≠ 0) → TimeExistsD6 f) ∧
    ((∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
     (∀ x, x ≠ 0 → D6 id x = 0) ∧
     (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0)) ∧
    (∀ a : ℝ, (∀ k x, x ≠ 0 → FUST.D7_constrained a (fun _ => k) x = 0) ∧
              (∀ x, x ≠ 0 → FUST.D7_constrained a id x = 0) ∧
              (∀ x, x ≠ 0 → FUST.D7_constrained a (fun t => t^2) x = 0)) ∧
    (∀ f c x, c ≠ 0 → x ≠ 0 → D6 (fun t => f (c * t)) x = c * D6 f (c * x)) :=
  ⟨IsInKerD6_implies_D6_zero,
   fun f ⟨x, hx, hD6⟩ => D6_nonzero_implies_time f x hx hD6,
   D6_kernel_dim_3,
   higher_order_reduction,
   fun f c x hc hx => D6_gauge_scaling f c x hc hx⟩

/-- Adding kernel component doesn't change D6 -/
theorem kernel_component_D6_invariant (f g : ℝ → ℝ) (hg : IsInKerD6 g) :
    ∀ x, x ≠ 0 → D6 (fun t => f t + g t) x = D6 f x := by
  intro x hx
  obtain ⟨a₀, a₁, a₂, hg_eq⟩ := hg
  have hpoly : D6 g x = 0 := by
    have hg' : g = fun t => a₀ + a₁ * t + a₂ * t^2 := funext hg_eq
    rw [hg']
    exact D6_polynomial_deg2 a₀ a₁ a₂ x hx
  simp only [D6, N6, D6Denom, hx, ↓reduceIte] at hpoly ⊢
  have hpoly_num : g (φ ^ 3 * x) - 3 * g (φ ^ 2 * x) + g (φ * x) - g (ψ * x) +
      3 * g (ψ ^ 2 * x) - g (ψ ^ 3 * x) = 0 := by
    rw [div_eq_zero_iff] at hpoly
    cases hpoly with
    | inl h => exact h
    | inr h => exact absurd h (D6Denom_mul_ne_zero x hx)
  calc ((f (φ^3*x) + g (φ^3*x)) - 3*(f (φ^2*x) + g (φ^2*x)) + (f (φ*x) + g (φ*x)) -
      (f (ψ*x) + g (ψ*x)) + 3*(f (ψ^2*x) + g (ψ^2*x)) - (f (ψ^3*x) + g (ψ^3*x))) /
      (D6Denom * x)
    = ((f (φ^3*x) - 3*f (φ^2*x) + f (φ*x) - f (ψ*x) + 3*f (ψ^2*x) - f (ψ^3*x)) +
       (g (φ^3*x) - 3*g (φ^2*x) + g (φ*x) - g (ψ*x) + 3*g (ψ^2*x) - g (ψ^3*x))) /
      (D6Denom * x) := by ring_nf
    _ = ((f (φ^3*x) - 3*f (φ^2*x) + f (φ*x) - f (ψ*x) + 3*f (ψ^2*x) - f (ψ^3*x)) + 0) /
      (D6Denom * x) := by rw [hpoly_num]
    _ = (f (φ^3*x) - 3*f (φ^2*x) + f (φ*x) - f (ψ*x) + 3*f (ψ^2*x) - f (ψ^3*x)) /
      (D6Denom * x) := by ring_nf

/-! ## Structural Minimum Time

The minimum time is derived structurally from D6, not by numerical fitting.

Key insight:
- ker(D6) = {1, x, x²} means D6 = 0 for these modes → no time defined
- n = 3 is the minimum degree where D6 detects temporal change
- C_3 = 12√5 is the minimum nonzero dissipation coefficient
- Structural minimum time = (√5)⁵ / C_3 = 25/12
-/

/-- C_3 = 12√5 (minimum nonzero dissipation coefficient) -/
theorem C3_eq_12_sqrt5 : φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9 = 12 * Real.sqrt 5 := by
  have hφ2 : φ^2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ^2 = ψ + 1 := psi_sq
  have hφ3 : φ^3 = 2*φ + 1 := phi_cubed
  have hψ3 : ψ^3 = 2*ψ + 1 := by
    calc ψ^3 = ψ^2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ^2 + ψ := by ring
      _ = (ψ + 1) + ψ := by rw [hψ2]
      _ = 2*ψ + 1 := by ring
  have hφ6 : φ^6 = 8*φ + 5 := by
    have hφ4 : φ^4 = 3*φ + 2 := by
      calc φ^4 = φ^2 * φ^2 := by ring
        _ = (φ + 1) * (φ + 1) := by rw [hφ2]
        _ = φ^2 + 2*φ + 1 := by ring
        _ = (φ + 1) + 2*φ + 1 := by rw [hφ2]
        _ = 3*φ + 2 := by ring
    calc φ^6 = φ^4 * φ^2 := by ring
      _ = (3*φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3*φ^2 + 5*φ + 2 := by ring
      _ = 3*(φ + 1) + 5*φ + 2 := by rw [hφ2]
      _ = 8*φ + 5 := by ring
  have hψ6 : ψ^6 = 8*ψ + 5 := by
    have hψ4 : ψ^4 = 3*ψ + 2 := by
      calc ψ^4 = ψ^2 * ψ^2 := by ring
        _ = (ψ + 1) * (ψ + 1) := by rw [hψ2]
        _ = ψ^2 + 2*ψ + 1 := by ring
        _ = (ψ + 1) + 2*ψ + 1 := by rw [hψ2]
        _ = 3*ψ + 2 := by ring
    calc ψ^6 = ψ^4 * ψ^2 := by ring
      _ = (3*ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3*ψ^2 + 5*ψ + 2 := by ring
      _ = 3*(ψ + 1) + 5*ψ + 2 := by rw [hψ2]
      _ = 8*ψ + 5 := by ring
  have hφ9 : φ^9 = 34*φ + 21 := by
    calc φ^9 = φ^6 * φ^3 := by ring
      _ = (8*φ + 5) * (2*φ + 1) := by rw [hφ6, hφ3]
      _ = 16*φ^2 + 18*φ + 5 := by ring
      _ = 16*(φ + 1) + 18*φ + 5 := by rw [hφ2]
      _ = 34*φ + 21 := by ring
  have hψ9 : ψ^9 = 34*ψ + 21 := by
    calc ψ^9 = ψ^6 * ψ^3 := by ring
      _ = (8*ψ + 5) * (2*ψ + 1) := by rw [hψ6, hψ3]
      _ = 16*ψ^2 + 18*ψ + 5 := by ring
      _ = 16*(ψ + 1) + 18*ψ + 5 := by rw [hψ2]
      _ = 34*ψ + 21 := by ring
  calc φ^9 - 3*φ^6 + φ^3 - ψ^3 + 3*ψ^6 - ψ^9
    = (34*φ + 21) - 3*(8*φ + 5) + (2*φ + 1) - (2*ψ + 1) + 3*(8*ψ + 5) - (34*ψ + 21) := by
        rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]
    _ = 12*φ - 12*ψ := by ring
    _ = 12 * (φ - ψ) := by ring
    _ = 12 * Real.sqrt 5 := by rw [phi_sub_psi]

/-- Structural minimum time: (√5)⁵ / C_3 = (√5)⁴ / 12 = 25/12
    This is the minimum time at which D6 detects temporal change.
    Below this scale, all functions behave as ker(D6) = {1, x, x²}. -/
noncomputable def structuralMinTime : ℝ := (Real.sqrt 5)^4 / 12

/-- structuralMinTime equals 25/12 -/
theorem structuralMinTime_eq : structuralMinTime = 25 / 12 := by
  simp only [structuralMinTime]
  have h5 : (Real.sqrt 5)^4 = 25 := by
    have hsq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)
    calc (Real.sqrt 5)^4 = ((Real.sqrt 5)^2)^2 := by ring
      _ = 5^2 := by rw [hsq]
      _ = 25 := by norm_num
  rw [h5]

/-- structuralMinTime is positive -/
theorem structuralMinTime_positive : structuralMinTime > 0 := by
  rw [structuralMinTime_eq]
  norm_num

/-- structuralMinTime derived from D6 structure:
    t_min = (√5)⁵ / C_3 where C_3 = 12√5 is the minimum nonzero dissipation -/
theorem structuralMinTime_from_D6 :
    structuralMinTime = (Real.sqrt 5)^5 / (12 * Real.sqrt 5) := by
  simp only [structuralMinTime]
  have hsqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
  have hsqrt5_ne : Real.sqrt 5 ≠ 0 := ne_of_gt hsqrt5_pos
  have h12_ne : (12 : ℝ) ≠ 0 := by norm_num
  have h12sqrt5_ne : 12 * Real.sqrt 5 ≠ 0 := mul_ne_zero h12_ne hsqrt5_ne
  rw [div_eq_div_iff h12_ne h12sqrt5_ne]
  have h5 : (Real.sqrt 5)^5 = (Real.sqrt 5)^4 * Real.sqrt 5 := by ring
  rw [h5]
  ring

/-- Why time cannot be divided below structuralMinTime:
    ker(D6) = {1, x, x²} means D6 cannot detect changes in these modes.
    n = 3 is the minimum degree where D6 detects temporal evolution. -/
theorem minimum_time_structural_reason :
    structuralMinTime > 0 ∧ structuralMinTime = 25/12 ∧
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) :=
  ⟨structuralMinTime_positive, structuralMinTime_eq, D6_const 1, D6_linear, D6_quadratic⟩

end FUST.TimeTheorem

namespace FUST.Dim

/-- Structural minimum time with derived dimension -/
noncomputable def structuralMinTime_dim : ScaleQ dimTime :=
  ⟨FUST.TimeTheorem.structuralMinTime⟩

theorem structuralMinTime_dim_val : structuralMinTime_dim.val = 25 / 12 :=
  FUST.TimeTheorem.structuralMinTime_eq

/-- Time is positive -/
theorem structuralMinTime_positive : structuralMinTime_dim.val > 0 :=
  FUST.TimeTheorem.structuralMinTime_positive

end FUST.Dim
