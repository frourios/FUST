import FUST.Physics.LeastAction

namespace FUST.TimeTheorem

open FUST.LeastAction

/-! ## Higher Order Reduction -/

/-- Higher Order Reduction: ker(D7) = ker(D6) -/
theorem higher_order_reduction :
    ∀ a : ℝ, (∀ k x, x ≠ 0 → FUST.D7_constrained a (fun _ => k) x = 0) ∧
             (∀ x, x ≠ 0 → FUST.D7_constrained a id x = 0) ∧
             (∀ x, x ≠ 0 → FUST.D7_constrained a (fun t => t^2) x = 0) :=
  FUST.D7_kernel_equals_D6_kernel

/-! ## Arrow of Time from φ/ψ Asymmetry

The arrow of time is a shared property of ALL Dm operators (m ≥ 2).
Time evolution f(t) ↦ f(φt) uses φ > 1, so |φ| > 1 and |ψ| < 1.
This asymmetry is intrinsic to the golden ratio, not specific to D6.
-/

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

/-- For tⁿ, time evolution amplifies by φⁿ -/
theorem monomial_amplification (n : ℕ) (t : ℝ) :
    timeEvolution (fun s => s^n) t = φ^n * t^n := by
  simp only [timeEvolution]; ring

/-- φⁿ > 1 for n ≥ 1 -/
theorem phi_pow_gt_one (n : ℕ) (hn : n ≥ 1) : φ^n > 1 := by
  exact one_lt_pow₀ φ_gt_one (Nat.one_le_iff_ne_zero.mp hn)

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

/-! ## Structural Minimum Time for All Operators

Each Dm has its own structural minimum time derived from spectral structure:
  t_min^Dm = (√5)^{m-1} / |C_{d_min}|

where C_{d_min} is the spectral coefficient at the minimum massive degree.

  D2: (√5)^1 / √5           = 1      (d_min = 1, C_1 = φ-ψ = √5)
  D3: (√5)^2 / 1             = 5      (d_min = 1, |C_1| = |φ+ψ-2| = 1)
  D4: (√5)^3 / √5            = 5      (d_min = 0, |C_0| = |-(φ²-ψ²)| = √5)
  D5: (√5)^4 / 6             = 25/6   (d_min = 2, C_2 = 6)
  D6: (√5)^4 / 12            = 25/12  (d_min = 3, |C_3| = 12√5)
-/

section StructuralMinTimes

/-- D2: t_min = (√5)^1 / |C_1|, where C_1 = φ-ψ = √5 -/
noncomputable def structuralMinTimeD2 : ℝ := Real.sqrt 5 / Real.sqrt 5

/-- D3: t_min = (√5)^2 / |C_1|, where |C_1| = |φ+ψ-2| = 1 -/
noncomputable def structuralMinTimeD3 : ℝ := (Real.sqrt 5)^2 / 1

/-- D4: t_min = (√5)^3 / |C_0|, where |C_0| = √5 -/
noncomputable def structuralMinTimeD4 : ℝ := (Real.sqrt 5)^3 / Real.sqrt 5

/-- D5: t_min = (√5)^4 / C_2, where C_2 = 6 -/
noncomputable def structuralMinTimeD5 : ℝ := (Real.sqrt 5)^4 / 6

/-- D6: t_min = (√5)^5 / |C_3| = (√5)^4 / 12, since |C_3| = 12√5 -/
noncomputable def structuralMinTimeD6 : ℝ := (Real.sqrt 5)^4 / 12

private theorem sqrt5_sq : (Real.sqrt 5)^2 = 5 :=
  Real.sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)

private theorem sqrt5_pow4 : (Real.sqrt 5)^4 = 25 := by
  calc (Real.sqrt 5)^4 = ((Real.sqrt 5)^2)^2 := by ring
    _ = 5^2 := by rw [sqrt5_sq]
    _ = 25 := by norm_num

private theorem sqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)

private theorem sqrt5_ne_zero : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos

theorem structuralMinTimeD2_eq : structuralMinTimeD2 = 1 := by
  simp only [structuralMinTimeD2]; exact div_self sqrt5_ne_zero

theorem structuralMinTimeD3_eq : structuralMinTimeD3 = 5 := by
  simp only [structuralMinTimeD3, div_one]; exact sqrt5_sq

theorem structuralMinTimeD4_eq : structuralMinTimeD4 = 5 := by
  simp only [structuralMinTimeD4]
  rw [show (Real.sqrt 5)^3 = (Real.sqrt 5)^2 * Real.sqrt 5 from by ring]
  rw [mul_div_cancel_of_imp fun h => absurd h sqrt5_ne_zero]
  exact sqrt5_sq

theorem structuralMinTimeD5_eq : structuralMinTimeD5 = 25 / 6 := by
  simp only [structuralMinTimeD5]; rw [sqrt5_pow4]

theorem structuralMinTimeD6_eq : structuralMinTimeD6 = 25 / 12 := by
  simp only [structuralMinTimeD6]; rw [sqrt5_pow4]

theorem structuralMinTimeD2_positive : structuralMinTimeD2 > 0 := by
  rw [structuralMinTimeD2_eq]; norm_num

theorem structuralMinTimeD3_positive : structuralMinTimeD3 > 0 := by
  rw [structuralMinTimeD3_eq]; norm_num

theorem structuralMinTimeD4_positive : structuralMinTimeD4 > 0 := by
  rw [structuralMinTimeD4_eq]; norm_num

theorem structuralMinTimeD5_positive : structuralMinTimeD5 > 0 := by
  rw [structuralMinTimeD5_eq]; norm_num

theorem structuralMinTimeD6_positive : structuralMinTimeD6 > 0 := by
  rw [structuralMinTimeD6_eq]; norm_num

/-- C_3 = 12√5 (D6 minimum nonzero spectral coefficient) -/
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

/-- D6 minimum time expressed as (√5)^5 / (12√5) -/
theorem structuralMinTimeD6_from_D6 :
    structuralMinTimeD6 = (Real.sqrt 5)^5 / (12 * Real.sqrt 5) := by
  simp only [structuralMinTimeD6]
  have h12_ne : (12 : ℝ) ≠ 0 := by norm_num
  have h12sqrt5_ne : 12 * Real.sqrt 5 ≠ 0 := mul_ne_zero h12_ne sqrt5_ne_zero
  rw [div_eq_div_iff h12_ne h12sqrt5_ne]
  have h5 : (Real.sqrt 5)^5 = (Real.sqrt 5)^4 * Real.sqrt 5 := by ring
  rw [h5]; ring

/-- Hierarchy: t_D6 < t_D5 < t_D4 = t_D3 > t_D2 -/
theorem structural_min_time_hierarchy :
    structuralMinTimeD6 < structuralMinTimeD5 ∧
    structuralMinTimeD5 < structuralMinTimeD4 ∧
    structuralMinTimeD4 = structuralMinTimeD3 ∧
    structuralMinTimeD2 < structuralMinTimeD3 := by
  rw [structuralMinTimeD2_eq, structuralMinTimeD3_eq, structuralMinTimeD4_eq,
      structuralMinTimeD5_eq, structuralMinTimeD6_eq]
  norm_num

end StructuralMinTimes

end FUST.TimeTheorem

namespace FUST.Dim

/-- Structural minimum time with derived dimension -/
noncomputable def structuralMinTime_dim : ScaleQ dimTime :=
  ⟨FUST.TimeTheorem.structuralMinTimeD6⟩

theorem structuralMinTime_dim_val : structuralMinTime_dim.val = 25 / 12 :=
  FUST.TimeTheorem.structuralMinTimeD6_eq

/-- Time is positive -/
theorem structuralMinTime_positive : structuralMinTime_dim.val > 0 :=
  FUST.TimeTheorem.structuralMinTimeD6_positive

end FUST.Dim
