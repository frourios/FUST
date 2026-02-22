/-
Complex-valued golden difference operators CD2-CD6.
Same structure as DifferenceOperators.lean but f : ℂ → ℂ, z : ℂ.
Singularity only at z = 0.
-/
import FUST.Basic
import FUST.DifferenceOperators

namespace FUST

open Complex

/-- CD2: complex golden 2-point difference -/
noncomputable def CD2 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (f (↑φ * z) - f (↑ψ * z)) / ((↑φ - ↑ψ) * z)

/-- CD3: complex golden 3-point difference -/
noncomputable def CD3 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (f (↑φ * z) - 2 * f z + f (↑ψ * z)) / ((↑φ - ↑ψ) ^ 2 * z)

/-- CD4: complex golden 4-point difference -/
noncomputable def CD4 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else
    (f ((↑φ : ℂ) ^ 2 * z) - (↑φ : ℂ) ^ 2 * f (↑φ * z) +
     (↑ψ : ℂ) ^ 2 * f (↑ψ * z) - f ((↑ψ : ℂ) ^ 2 * z)) /
    ((↑φ - ↑ψ) ^ 3 * z)

/-- CD5: complex golden 5-point difference -/
noncomputable def CD5 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else
    (f ((↑φ : ℂ) ^ 2 * z) + f (↑φ * z) - 4 * f z +
     f (↑ψ * z) + f ((↑ψ : ℂ) ^ 2 * z)) /
    ((↑φ - ↑ψ) ^ 4 * z)

/-- CN6: complex numerator of CD6 -/
noncomputable def CN6 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) ^ 3 * z) - 3 * f ((↑φ : ℂ) ^ 2 * z) + f (↑φ * z) -
  f (↑ψ * z) + 3 * f ((↑ψ : ℂ) ^ 2 * z) - f ((↑ψ : ℂ) ^ 3 * z)

/-- CD6Denom: (φ - ψ)⁵ as complex -/
noncomputable def CD6Denom : ℂ := (↑φ - ↑ψ) ^ 5

/-- CD6: complex golden 6-point difference -/
noncomputable def CD6 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else CN6 f z / (CD6Denom * z)

/-- CD5half: complex half-order difference -/
noncomputable def CD5half (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let μ : ℂ := 2 / ((↑φ : ℂ) + 2)
  CD5 f z + μ * (f (↑φ * z) - f (↑ψ * z))

private lemma phi_sub_psi_complex_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := by
  rw [← ofReal_sub, ne_eq, ofReal_eq_zero, sub_eq_zero]
  intro h; linarith [phi_pos, psi_neg]

section KernelTheorems

/-- CD2 annihilates constants -/
theorem CD2_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : CD2 (fun _ => c) z = 0 := by
  simp only [CD2, hz, ↓reduceIte, sub_self, zero_div]

/-- CD3 annihilates constants -/
theorem CD3_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : CD3 (fun _ => c) z = 0 := by
  simp only [CD3, hz, ↓reduceIte]
  have : c - 2 * c + c = 0 := by ring
  rw [this, zero_div]

/-- CD4 does NOT annihilate constants -/
theorem CD4_const_ne_zero (z : ℂ) (hz : z ≠ 0) : CD4 (fun _ => (1 : ℂ)) z ≠ 0 := by
  simp only [CD4, hz, ↓reduceIte]
  have hφ2 : (↑φ : ℂ) ^ 2 = ↑φ + 1 := by
    have h := golden_ratio_property
    have : (↑(φ ^ 2) : ℂ) = ↑(φ + 1) := congrArg _ h
    simp only [ofReal_pow, ofReal_add, ofReal_one] at this; exact this
  have hψ2 : (↑ψ : ℂ) ^ 2 = ↑ψ + 1 := by
    have h := psi_sq
    have : (↑(ψ ^ 2) : ℂ) = ↑(ψ + 1) := congrArg _ h
    simp only [ofReal_pow, ofReal_add, ofReal_one] at this; exact this
  have hnum : (1 : ℂ) - (↑φ : ℂ) ^ 2 * 1 + (↑ψ : ℂ) ^ 2 * 1 - 1 = -(↑φ - ↑ψ) := by
    rw [mul_one, mul_one, hφ2, hψ2]; ring
  rw [hnum, neg_div, neg_ne_zero]
  exact div_ne_zero (phi_sub_psi_complex_ne)
    (mul_ne_zero (pow_ne_zero 3 phi_sub_psi_complex_ne) hz)

/-- CD5 annihilates constants -/
theorem CD5_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : CD5 (fun _ => c) z = 0 := by
  simp only [CD5, hz, ↓reduceIte]
  have : c + c - 4 * c + c + c = 0 := by ring
  rw [this, zero_div]

/-- CD6 annihilates constants -/
theorem CD6_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : CD6 (fun _ => c) z = 0 := by
  simp only [CD6, hz, ↓reduceIte, CN6]
  have : c - 3 * c + c - c + 3 * c - c = 0 := by ring
  rw [this, zero_div]

/-- CD5half annihilates constants -/
theorem CD5half_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) : CD5half (fun _ => c) z = 0 := by
  simp only [CD5half, CD5_const c z hz, sub_self, mul_zero, add_zero]

end KernelTheorems

end FUST
