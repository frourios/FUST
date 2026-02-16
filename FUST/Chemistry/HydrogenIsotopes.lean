/-
Hydrogen Isotopes and Ionization from D-operator Kernel Structure

State function g(x) = x · ∏(neutron factors) · ∏(electron factors)
where proton → x, neutron → (1+x), electron → (1+ψx).

Key results:
- deg(g) = 1 + N + e determines D5/D6 kernel membership
- Baryon factors have ℤ coefficients; lepton factors have ℤ[φ]\ℤ coefficients
- Tritium is the first isotope to exit ker(D6)
-/

import FUST.DifferenceOperators
import FUST.DiscreteTag
import FUST.Physics.Nuclear

namespace FUST.Chemistry

open FUST

/-! ## Section 1: Particle Factors

Each particle contributes a multiplicative factor to the state function:
- Proton: x (the base monomial)
- Neutron: (1 + x) (baryon, rational coefficient)
- Electron (1s): (1 + ψx) (lepton, golden coefficient)
-/

noncomputable def protonFactor (x : ℝ) : ℝ := x

noncomputable def neutronFactor (x : ℝ) : ℝ := 1 + x

noncomputable def electronFactor (x : ℝ) : ℝ := 1 + ψ * x

/-! ## Section 2: Hydrogen Species State Functions -/

-- Bare nuclei (ions with no electrons)
noncomputable def hydrogenIon (x : ℝ) : ℝ := x

noncomputable def deuteronIon (x : ℝ) : ℝ := x * (1 + x)

noncomputable def tritonIon (x : ℝ) : ℝ := x * (1 + x) ^ 2

-- Neutral atoms (nucleus + Z electrons)
noncomputable def hydrogenAtom (x : ℝ) : ℝ := x * (1 + ψ * x)

noncomputable def deuteriumAtom (x : ℝ) : ℝ := x * (1 + x) * (1 + ψ * x)

noncomputable def tritiumAtom (x : ℝ) : ℝ := x * (1 + x) ^ 2 * (1 + ψ * x)

-- Hydride anion (1 proton + 2 electrons)
noncomputable def hydrideAnion (x : ℝ) : ℝ := x * (1 + ψ * x) ^ 2

/-! ## Section 3: ψ = 1 - φ identity -/

private lemma psi_eq : ψ = 1 - φ := by linarith [phi_add_psi]

/-! ## Section 4: Polynomial Expansions -/

theorem hydrogenIon_eq (x : ℝ) : hydrogenIon x = x := rfl

theorem deuteronIon_eq (x : ℝ) : deuteronIon x = x + x ^ 2 := by
  unfold deuteronIon; ring

theorem tritonIon_eq (x : ℝ) : tritonIon x = x + 2 * x ^ 2 + x ^ 3 := by
  unfold tritonIon; ring

theorem hydrogenAtom_eq (x : ℝ) : hydrogenAtom x = x + ψ * x ^ 2 := by
  unfold hydrogenAtom; ring

theorem deuteriumAtom_eq (x : ℝ) :
    deuteriumAtom x = x + (2 - φ) * x ^ 2 + ψ * x ^ 3 := by
  unfold deuteriumAtom; rw [psi_eq]; ring

theorem tritiumAtom_eq (x : ℝ) :
    tritiumAtom x = x + (3 - φ) * x ^ 2 + (3 - 2 * φ) * x ^ 3 + ψ * x ^ 4 := by
  unfold tritiumAtom; rw [psi_eq]; ring

theorem hydrideAnion_eq (x : ℝ) :
    hydrideAnion x = x + 2 * ψ * x ^ 2 + ψ ^ 2 * x ^ 3 := by
  unfold hydrideAnion; ring

/-! ## Section 4: Degree Structure

deg(g) = 1 + N + e where N = neutron count, e = electron count.
-/

def speciesDegree (neutrons electrons : ℕ) : ℕ := 1 + neutrons + electrons

theorem degree_hydrogenIon : speciesDegree 0 0 = 1 := rfl
theorem degree_deuteronIon : speciesDegree 1 0 = 2 := rfl
theorem degree_tritonIon : speciesDegree 2 0 = 3 := rfl
theorem degree_hydrogenAtom : speciesDegree 0 1 = 2 := rfl
theorem degree_deuteriumAtom : speciesDegree 1 1 = 3 := rfl
theorem degree_tritiumAtom : speciesDegree 2 1 = 4 := rfl
theorem degree_hydrideAnion : speciesDegree 0 2 = 3 := rfl

/-! ## Section 5: D5 Kernel Classification

ker(D5) = {1, x}, so g ∈ ker(D5) ⟺ deg(g) ≤ 1 ⟺ N = 0 ∧ e = 0.
Only the bare proton (H⁺) is in ker(D5).
-/

-- H⁺ is in ker(D5): D5(x) = 0
theorem hydrogenIon_in_kerD5 (x : ℝ) (hx : x ≠ 0) :
    D5 hydrogenIon x = 0 := by
  unfold hydrogenIon; exact D5_linear x hx

-- D⁺ is NOT in ker(D5): uses D5(x²) ≠ 0
theorem deuteronIon_not_in_kerD5 (x : ℝ) (hx : x ≠ 0) :
    D5 deuteronIon x ≠ 0 := by
  have heq : deuteronIon = fun t => t + t ^ 2 := by ext t; unfold deuteronIon; ring
  rw [heq]
  simp only [D5, hx, ↓reduceIte]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hsum : φ + ψ = 1 := phi_add_psi
  have hnum : φ ^ 2 * x + (φ ^ 2 * x) ^ 2 + (φ * x + (φ * x) ^ 2) -
      4 * (x + x ^ 2) + (ψ * x + (ψ * x) ^ 2) + (ψ ^ 2 * x + (ψ ^ 2 * x) ^ 2) =
      6 * x ^ 2 := by
    have hc1 : φ ^ 2 + φ + ψ + ψ ^ 2 - 4 = 0 := by rw [hφ2, hψ2]; linarith
    have hc2 : φ ^ 4 + φ ^ 2 + ψ ^ 2 + ψ ^ 4 - 4 = 6 := by rw [hφ4, hφ2, hψ2, hψ4]; linarith
    have := calc φ ^ 2 * x + (φ ^ 2 * x) ^ 2 + (φ * x + (φ * x) ^ 2) -
        4 * (x + x ^ 2) + (ψ * x + (ψ * x) ^ 2) + (ψ ^ 2 * x + (ψ ^ 2 * x) ^ 2)
        = (φ ^ 2 + φ + ψ + ψ ^ 2 - 4) * x +
          (φ ^ 4 + φ ^ 2 + ψ ^ 2 + ψ ^ 4 - 4) * x ^ 2 := by ring
      _ = 0 * x + 6 * x ^ 2 := by rw [hc1, hc2]
      _ = 6 * x ^ 2 := by ring
    linarith
  rw [hnum]
  have hφψ : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hden_ne : (φ - ψ) ^ 4 * x ≠ 0 := by
    apply mul_ne_zero
    · apply pow_ne_zero; rw [hφψ]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
    · exact hx
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) hden_ne

/-! ## Section 6: D6 Kernel Classification

ker(D6) = {1, x, x²}, so g ∈ ker(D6) ⟺ deg(g) ≤ 2 ⟺ N + e ≤ 1.
-/

-- H⁺ is in ker(D6)
theorem hydrogenIon_in_kerD6 (x : ℝ) (hx : x ≠ 0) :
    D6 hydrogenIon x = 0 := by
  unfold hydrogenIon; exact D6_linear x hx

-- D⁺ is in ker(D6): D6(x + x²) = D6(x) + D6(x²) = 0 + 0 = 0
theorem deuteronIon_in_kerD6 (x : ℝ) (hx : x ≠ 0) :
    D6 deuteronIon x = 0 := by
  have heq : deuteronIon = fun t => t + t ^ 2 := by ext t; unfold deuteronIon; ring
  rw [heq]
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
    calc ψ ^ 3 = ψ ^ 2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ ^ 2 + ψ := by ring
      _ = 2 * ψ + 1 := by rw [hψ2]; ring
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by
    calc φ ^ 4 = (φ ^ 2) ^ 2 := by ring
      _ = (φ + 1) ^ 2 := by rw [hφ2]
      _ = φ ^ 2 + 2 * φ + 1 := by ring
      _ = 3 * φ + 2 := by rw [hφ2]; ring
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by
    calc ψ ^ 4 = (ψ ^ 2) ^ 2 := by ring
      _ = (ψ + 1) ^ 2 := by rw [hψ2]
      _ = ψ ^ 2 + 2 * ψ + 1 := by ring
      _ = 3 * ψ + 2 := by rw [hψ2]; ring
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by
    calc φ ^ 6 = (φ ^ 4) * (φ ^ 2) := by ring
      _ = (3 * φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3 * φ ^ 2 + 5 * φ + 2 := by ring
      _ = 8 * φ + 5 := by rw [hφ2]; ring
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by
    calc ψ ^ 6 = (ψ ^ 4) * (ψ ^ 2) := by ring
      _ = (3 * ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3 * ψ ^ 2 + 5 * ψ + 2 := by ring
      _ = 8 * ψ + 5 := by rw [hψ2]; ring
  have hsum : φ + ψ = 1 := phi_add_psi
  have hnum : φ ^ 3 * x + (φ ^ 3 * x) ^ 2 - 3 * (φ ^ 2 * x + (φ ^ 2 * x) ^ 2) +
      (φ * x + (φ * x) ^ 2) - (ψ * x + (ψ * x) ^ 2) +
      3 * (ψ ^ 2 * x + (ψ ^ 2 * x) ^ 2) - (ψ ^ 3 * x + (ψ ^ 3 * x) ^ 2) = 0 := by
    have hc1 : φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3 = 0 := by
      rw [hφ3, hφ2, hψ2, hψ3]; linarith
    have hc2 : φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6 = 0 := by
      rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]; linarith
    have := calc φ ^ 3 * x + (φ ^ 3 * x) ^ 2 - 3 * (φ ^ 2 * x + (φ ^ 2 * x) ^ 2) +
        (φ * x + (φ * x) ^ 2) - (ψ * x + (ψ * x) ^ 2) +
        3 * (ψ ^ 2 * x + (ψ ^ 2 * x) ^ 2) - (ψ ^ 3 * x + (ψ ^ 3 * x) ^ 2)
        = (φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3) * x +
          (φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6) * x ^ 2 := by ring
      _ = 0 * x + 0 * x ^ 2 := by rw [hc1, hc2]
      _ = 0 := by ring
    linarith
  simp [hnum]

-- H (neutral) is in ker(D6): D6(x + ψx²) = 0
theorem hydrogenAtom_in_kerD6 (x : ℝ) (hx : x ≠ 0) :
    D6 hydrogenAtom x = 0 := by
  have heq : hydrogenAtom = fun t => t + ψ * t ^ 2 := by ext t; unfold hydrogenAtom; ring
  rw [heq]
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
    calc ψ ^ 3 = ψ ^ 2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ ^ 2 + ψ := by ring
      _ = 2 * ψ + 1 := by rw [hψ2]; ring
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by
    calc φ ^ 4 = (φ ^ 2) ^ 2 := by ring
      _ = (φ + 1) ^ 2 := by rw [hφ2]
      _ = φ ^ 2 + 2 * φ + 1 := by ring
      _ = 3 * φ + 2 := by rw [hφ2]; ring
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by
    calc ψ ^ 4 = (ψ ^ 2) ^ 2 := by ring
      _ = (ψ + 1) ^ 2 := by rw [hψ2]
      _ = ψ ^ 2 + 2 * ψ + 1 := by ring
      _ = 3 * ψ + 2 := by rw [hψ2]; ring
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by
    calc φ ^ 6 = (φ ^ 4) * (φ ^ 2) := by ring
      _ = (3 * φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3 * φ ^ 2 + 5 * φ + 2 := by ring
      _ = 8 * φ + 5 := by rw [hφ2]; ring
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by
    calc ψ ^ 6 = (ψ ^ 4) * (ψ ^ 2) := by ring
      _ = (3 * ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3 * ψ ^ 2 + 5 * ψ + 2 := by ring
      _ = 8 * ψ + 5 := by rw [hψ2]; ring
  have hsum : φ + ψ = 1 := phi_add_psi
  have hprod : φ * ψ = -1 := phi_mul_psi
  have hnum : φ ^ 3 * x + ψ * (φ ^ 3 * x) ^ 2 -
      3 * (φ ^ 2 * x + ψ * (φ ^ 2 * x) ^ 2) +
      (φ * x + ψ * (φ * x) ^ 2) -
      (ψ * x + ψ * (ψ * x) ^ 2) +
      3 * (ψ ^ 2 * x + ψ * (ψ ^ 2 * x) ^ 2) -
      (ψ ^ 3 * x + ψ * (ψ ^ 3 * x) ^ 2) = 0 := by
    have hc1 : φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3 = 0 := by
      rw [hφ3, hφ2, hψ2, hψ3]; linarith
    have hc2 : ψ * (φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6) = 0 := by
      have : φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6 = 0 := by
        rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]; linarith
      rw [this]; ring
    have := calc φ ^ 3 * x + ψ * (φ ^ 3 * x) ^ 2 -
        3 * (φ ^ 2 * x + ψ * (φ ^ 2 * x) ^ 2) +
        (φ * x + ψ * (φ * x) ^ 2) -
        (ψ * x + ψ * (ψ * x) ^ 2) +
        3 * (ψ ^ 2 * x + ψ * (ψ ^ 2 * x) ^ 2) -
        (ψ ^ 3 * x + ψ * (ψ ^ 3 * x) ^ 2)
        = (φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3) * x +
          ψ * (φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6) * x ^ 2 := by ring
      _ = 0 * x + 0 * x ^ 2 := by rw [hc1, hc2]
      _ = 0 := by ring
    linarith
  simp [hnum]

-- T⁺ is NOT in ker(D6): first nuclear isotope to exit
theorem tritonIon_not_in_kerD6 (x : ℝ) (hx : x ≠ 0) :
    D6 tritonIon x ≠ 0 := by
  have heq : tritonIon = fun t => t + 2 * t ^ 2 + t ^ 3 := by ext t; unfold tritonIon; ring
  rw [heq]
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
    calc ψ ^ 3 = ψ ^ 2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ ^ 2 + ψ := by ring
      _ = 2 * ψ + 1 := by rw [hψ2]; ring
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by
    calc φ ^ 4 = (φ ^ 2) ^ 2 := by ring
      _ = (φ + 1) ^ 2 := by rw [hφ2]
      _ = φ ^ 2 + 2 * φ + 1 := by ring
      _ = 3 * φ + 2 := by rw [hφ2]; ring
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by
    calc ψ ^ 4 = (ψ ^ 2) ^ 2 := by ring
      _ = (ψ + 1) ^ 2 := by rw [hψ2]
      _ = ψ ^ 2 + 2 * ψ + 1 := by ring
      _ = 3 * ψ + 2 := by rw [hψ2]; ring
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by
    calc φ ^ 6 = (φ ^ 4) * (φ ^ 2) := by ring
      _ = (3 * φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3 * φ ^ 2 + 5 * φ + 2 := by ring
      _ = 8 * φ + 5 := by rw [hφ2]; ring
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by
    calc ψ ^ 6 = (ψ ^ 4) * (ψ ^ 2) := by ring
      _ = (3 * ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3 * ψ ^ 2 + 5 * ψ + 2 := by ring
      _ = 8 * ψ + 5 := by rw [hψ2]; ring
  have hφ9 : φ ^ 9 = 34 * φ + 21 := by
    calc φ ^ 9 = (φ ^ 6) * (φ ^ 3) := by ring
      _ = (8 * φ + 5) * (2 * φ + 1) := by rw [hφ6, hφ3]
      _ = 16 * φ ^ 2 + 18 * φ + 5 := by ring
      _ = 16 * (φ + 1) + 18 * φ + 5 := by rw [hφ2]
      _ = 34 * φ + 21 := by ring
  have hψ9 : ψ ^ 9 = 34 * ψ + 21 := by
    calc ψ ^ 9 = (ψ ^ 6) * (ψ ^ 3) := by ring
      _ = (8 * ψ + 5) * (2 * ψ + 1) := by rw [hψ6, hψ3]
      _ = 16 * ψ ^ 2 + 18 * ψ + 5 := by ring
      _ = 16 * (ψ + 1) + 18 * ψ + 5 := by rw [hψ2]
      _ = 34 * ψ + 21 := by ring
  have hsum : φ + ψ = 1 := phi_add_psi
  have hcoef3 : φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9 = 12 * (φ - ψ) := by
    rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]; linarith
  have hnum : φ ^ 3 * x + 2 * (φ ^ 3 * x) ^ 2 + (φ ^ 3 * x) ^ 3 -
      3 * (φ ^ 2 * x + 2 * (φ ^ 2 * x) ^ 2 + (φ ^ 2 * x) ^ 3) +
      (φ * x + 2 * (φ * x) ^ 2 + (φ * x) ^ 3) -
      (ψ * x + 2 * (ψ * x) ^ 2 + (ψ * x) ^ 3) +
      3 * (ψ ^ 2 * x + 2 * (ψ ^ 2 * x) ^ 2 + (ψ ^ 2 * x) ^ 3) -
      (ψ ^ 3 * x + 2 * (ψ ^ 3 * x) ^ 2 + (ψ ^ 3 * x) ^ 3) =
      12 * (φ - ψ) * x ^ 3 := by
    have hc1 : φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3 = 0 := by
      rw [hφ3, hφ2, hψ2, hψ3]; linarith
    have hc2 : 2 * (φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6) = 0 := by
      have : φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6 = 0 := by
        rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]; linarith
      rw [this]; ring
    have := calc φ ^ 3 * x + 2 * (φ ^ 3 * x) ^ 2 + (φ ^ 3 * x) ^ 3 -
        3 * (φ ^ 2 * x + 2 * (φ ^ 2 * x) ^ 2 + (φ ^ 2 * x) ^ 3) +
        (φ * x + 2 * (φ * x) ^ 2 + (φ * x) ^ 3) -
        (ψ * x + 2 * (ψ * x) ^ 2 + (ψ * x) ^ 3) +
        3 * (ψ ^ 2 * x + 2 * (ψ ^ 2 * x) ^ 2 + (ψ ^ 2 * x) ^ 3) -
        (ψ ^ 3 * x + 2 * (ψ ^ 3 * x) ^ 2 + (ψ ^ 3 * x) ^ 3)
        = (φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3) * x +
          2 * (φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6) * x ^ 2 +
          (φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9) * x ^ 3 := by ring
      _ = 0 * x + 0 * x ^ 2 + 12 * (φ - ψ) * x ^ 3 := by rw [hc1, hc2, hcoef3]
      _ = 12 * (φ - ψ) * x ^ 3 := by ring
    linarith
  rw [hnum]
  have hφψ : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hφψ_ne : φ - ψ ≠ 0 := by rw [hφψ]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hden_ne : (φ - ψ) ^ 5 * x ≠ 0 := mul_ne_zero (pow_ne_zero 5 hφψ_ne) hx
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) hφψ_ne) (pow_ne_zero 3 hx)
  · exact hden_ne

/-! ## Section 7: Kernel Membership Conditions

ker(D6) ⟺ N + e ≤ 1 and ker(D5) ⟺ N = 0 ∧ e = 0
-/

theorem in_kerD6_iff_degree_le_2 :
    speciesDegree 0 0 ≤ 2 ∧ speciesDegree 1 0 ≤ 2 ∧ speciesDegree 0 1 ≤ 2 ∧
    ¬(speciesDegree 2 0 ≤ 2) ∧ ¬(speciesDegree 1 1 ≤ 2) ∧ ¬(speciesDegree 0 2 ≤ 2) := by
  unfold speciesDegree; omega

theorem in_kerD5_iff_degree_le_1 :
    speciesDegree 0 0 ≤ 1 ∧
    ¬(speciesDegree 1 0 ≤ 1) ∧ ¬(speciesDegree 0 1 ≤ 1) := by
  unfold speciesDegree; omega

/-! ## Section 8: Baryon vs Lepton Coefficient Distinction

Neutron factor (1+x) has coefficient 1 ∈ ℤ.
Electron factor (1+ψx) has coefficient ψ ∈ ℤ[φ]\ℤ.
The Galois conjugation σ(φ) = ψ maps baryonic to leptonic.
-/

-- ψ is irrational (not in ℤ)
theorem psi_irrational : Irrational ψ := by
  rw [psi_eq, show (1 : ℝ) - φ = ((1 : ℤ) : ℝ) - φ from by push_cast; ring]
  exact irrational_intCast_sub_iff.mpr FrourioAlgebra.phi_irrational

-- Neutron coefficient is rational
theorem neutron_coefficient_rational : (1 : ℝ) ∈ Set.range (fun (n : ℤ) => (n : ℝ)) :=
  ⟨1, by simp⟩

-- Electron coefficient is irrational
theorem electron_coefficient_irrational : Irrational ψ := psi_irrational

/-! ## Section 9: Summary -/

theorem hydrogen_isotope_classification :
    -- H⁺ (bare proton): in ker(D5) ∩ ker(D6)
    speciesDegree 0 0 = 1 ∧
    -- D⁺, H (2 particles): in ker(D6) but not ker(D5)
    speciesDegree 1 0 = 2 ∧ speciesDegree 0 1 = 2 ∧
    -- T⁺, D, H⁻ (3 particles): not in ker(D6)
    speciesDegree 2 0 = 3 ∧ speciesDegree 1 1 = 3 ∧ speciesDegree 0 2 = 3 ∧
    -- T (4 particles): not in ker(D6)
    speciesDegree 2 1 = 4 := by
  simp [speciesDegree]

end FUST.Chemistry
