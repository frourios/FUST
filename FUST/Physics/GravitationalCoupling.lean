import FUST.Physics.WaveEquation
import Mathlib.Data.Nat.Choose.Basic

/-!
# Gravitational Coupling from D-Structure Hierarchy

This module derives the gravitational coupling constant from D-structure hierarchy.

## Main Results

The electron-to-Planck mass ratio:
  m_e / m_Pl = φ^(-107 - 5/63)

Where:
- 107 = T(4) × (T(4)+1) - C(3,2) = 10 × 11 - 3
- 5/63 = α_exponent / (C(3,2) × T(6))

## Physical Interpretation

Gravity emerges from the complete D-hierarchy through:
- Lepton mass structure (107)
- Electromagnetic structure (5 = α exponent)
- Weak structure (3 = C(3,2))
- Full D₆ hierarchy (21 = T(6))
-/

namespace FUST.GravitationalCoupling

open FUST.WaveEquation FUST.LeastAction

/-! ## Triangular Numbers and Binomial Coefficients

Triangular numbers T(n) = n(n+1)/2 = C(n+1, 2) count pairs in D_{n+1}.
-/

/-- Triangular number: T(n) = n(n+1)/2 = C(n+1, 2) -/
abbrev triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- T(n) = C(n+1, 2): triangular numbers are pair counts -/
theorem triangular_eq_choose (n : ℕ) : triangular n = Nat.choose (n + 1) 2 := by
  simp only [triangular, Nat.choose_two_right, Nat.add_sub_cancel]
  ring_nf

theorem T3_eq : triangular 3 = 6 := rfl
theorem T4_eq : triangular 4 = 10 := rfl
theorem T5_eq : triangular 5 = 15 := rfl
theorem T6_eq : triangular 6 = 21 := rfl
theorem T9_eq : triangular 9 = 45 := rfl

/-- T(4) = C(5,2): D₅ pair count -/
theorem T4_as_D5_pairs : triangular 4 = Nat.choose 5 2 := rfl

/-- T(6) = C(7,2): extended hierarchy pair count -/
theorem T6_as_pairs : triangular 6 = Nat.choose 7 2 := rfl

theorem C32_eq : Nat.choose 3 2 = 3 := rfl
theorem C62_eq : Nat.choose 6 2 = 15 := rfl

/-! ## Lepton Mass Exponent: 107

107 = p₃ + e₃ + d = Σ L(k)³ + Π L(k) + kerDim(D₆) = 92 + 12 + 3.
-/

/-- 107 from triangular numbers (equivalent to sector-invariant form) -/
theorem leptonMassExponent_eq : triangular 4 * (triangular 4 + 1) - Nat.choose 3 2 = 107 := by
  decide

/-! ## Fractional Correction: 5/63 -/

/-- Denominator 63 = C(3,2) × T(6) = 3 × 21 -/
theorem gravityCorrectionDenom_eq : Nat.choose 3 2 * triangular 6 = 63 := by decide

/-- Numerator 5 = active D-levels = 6 - 2 + 1 -/
theorem alpha_exponent_eq : 6 - 2 + 1 = 5 := rfl

/-- Lepton exponent from D-structure: T(4) × (T(4)+1) - C(3,2) -/
abbrev leptonExponent : ℕ := triangular 4 * (triangular 4 + 1) - Nat.choose 3 2

/-- Active D-levels = 6 - 2 + 1 = 5 -/
abbrev activeDLevels : ℕ := 6 - 2 + 1

/-- Correction denominator = C(3,2) × T(6) = 3 × 21 -/
abbrev correctionDenom : ℕ := Nat.choose 3 2 * triangular 6

/-- Full gravitational exponent: -(leptonExponent + activeDLevels/correctionDenom) -/
noncomputable abbrev gravitationalExponent : ℝ :=
  -((leptonExponent : ℝ) + (activeDLevels : ℝ) / correctionDenom)

/-- Gravitational exponent derivation -/
theorem gravitationalExponent_derivation :
    leptonExponent = 107 ∧ activeDLevels = 5 ∧ correctionDenom = 63 := by decide

/-- The electron-to-Planck mass ratio formula -/
noncomputable abbrev electronPlanckRatio : ℝ := φ ^ gravitationalExponent

theorem electronPlanckRatio_eq :
    electronPlanckRatio = φ ^ (-(107 + 5/63 : ℝ)) := by
  unfold electronPlanckRatio gravitationalExponent
  congr 1

/-! ## Gravitational Coupling Constant -/

/-- Gravitational coupling α_G = (m_e/m_Pl)² -/
noncomputable abbrev gravitationalCoupling : ℝ := electronPlanckRatio ^ 2

theorem gravitationalCoupling_exponent :
    gravitationalCoupling = φ ^ (-(214 + 10/63 : ℝ)) := by
  unfold gravitationalCoupling electronPlanckRatio gravitationalExponent
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt phi_pos)]
  congr 1
  simp only [leptonExponent, activeDLevels, correctionDenom, triangular, Nat.choose]
  norm_num

/-! ## D-Hierarchy Pair Counts -/

theorem totalDHierarchyPairs_eq :
    Nat.choose 2 2 + Nat.choose 3 2 + Nat.choose 4 2 + Nat.choose 5 2 + Nat.choose 6 2 = 35 := by
  decide

theorem D_structure_pairs :
    Nat.choose 2 2 = 1 ∧
    Nat.choose 3 2 = 3 ∧
    Nat.choose 4 2 = 6 ∧
    Nat.choose 5 2 = 10 ∧
    Nat.choose 6 2 = 15 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Connection to Kernel Structure

The gravitational coupling derives from D-structure hierarchy,
where D₃ through D₆ contribute via their pair counts and kernel dimensions.
-/

theorem D3_gauge_invariance : ∀ x, x ≠ 0 → D3 (fun _ => 1) x = 0 :=
  fun x hx => D3_const 1 x hx

/-! ## CMB Temperature: 152

T_CMB/T_Pl = φ^(-152). Decomposition: 152 = 107 + 45.
φ^(-107) ≈ m_e/m_Pl (mass scale), φ^(-45) = T_CMB/m_e (thermal factor).
Both terms are dimensionless exponents. 152 = 2 × L(9).
-/

/-- CMB decoupling factor = C(3,2) × T(5) -/
abbrev cmbDecouplingFactor : ℕ := Nat.choose 3 2 * triangular 5

/-- CMB decoupling: C(3,2)×T(5) = 45 -/
theorem cmbDecouplingFactor_eq : Nat.choose 3 2 * triangular 5 = 45 := by decide

/-- CMB temperature exponent = leptonExponent + cmbDecouplingFactor -/
abbrev cmbTemperatureExponent : ℕ := leptonExponent + cmbDecouplingFactor

/-- CMB exponent: 107 + 45 = 152 -/
theorem cmbTemperatureExponent_eq : leptonExponent + cmbDecouplingFactor = 152 := by decide

theorem cmbTemperatureExponent_value : cmbTemperatureExponent = 152 := by decide

noncomputable abbrev cmbTemperatureRatio : ℝ := φ ^ (-(cmbTemperatureExponent : ℤ))

/-! ## Cosmological Constant: 582

ρ_Λ/ρ_Pl = φ^(-582). Dimensional separation via Stefan-Boltzmann ρ ∝ T⁴:
  φ^(-582) = (T_CMB/T_Pl)⁴ × φ^26
  582 = 4 × 152 - 26
where 4 = spacetimeDim (from ρ ∝ T⁴) and 26 = Σ L(k)² (sector trace squares).
-/

/-- Sector trace square sum (ℕ version) -/
abbrev sectorTraceSq : ℕ := 1 ^ 2 + 3 ^ 2 + 4 ^ 2

theorem sectorTraceSq_eq : sectorTraceSq = 26 := by decide

/-- Cosmological exponent: 582 = spacetimeDim × cmbExponent - sectorTraceSq -/
abbrev cosmologicalExponent : ℕ :=
  spacetimeDim * cmbTemperatureExponent - sectorTraceSq

/-- 582 = 4×152 - 26 (Stefan-Boltzmann + sector correction) -/
theorem cosmologicalExponent_eq :
    spacetimeDim * cmbTemperatureExponent - sectorTraceSq = 582 := by decide

theorem cosmologicalExponent_value : cosmologicalExponent = 582 := by decide

noncomputable abbrev cosmologicalDensityRatio : ℝ := φ ^ (-(cosmologicalExponent : ℤ))

/-! ## Summary Theorem -/

theorem gravitational_coupling_summary :
    -- Exponent 107 decomposition
    (triangular 4 * (triangular 4 + 1) - Nat.choose 3 2 = 107) ∧
    -- Fractional correction structure
    (6 - 2 + 1 = 5) ∧
    (Nat.choose 3 2 * triangular 6 = 63) ∧
    -- D-structure pairs
    (Nat.choose 2 2 + Nat.choose 3 2 + Nat.choose 4 2 +
     Nat.choose 5 2 + Nat.choose 6 2 = 35) ∧
    -- D₃ gauge invariance
    (∀ x, x ≠ 0 → D3 (fun _ => 1) x = 0) := by
  refine ⟨leptonMassExponent_eq, rfl, gravityCorrectionDenom_eq,
         totalDHierarchyPairs_eq, D3_gauge_invariance⟩

theorem cosmological_summary :
    (cmbTemperatureExponent = 152) ∧
    (cosmologicalExponent = 582) ∧
    (cmbDecouplingFactor = 45) ∧
    (sectorTraceSq = 26) := by
  refine ⟨cmbTemperatureExponent_value, cosmologicalExponent_value,
         by decide, rfl⟩

/-! ## D₆ Coefficient Structure

The D₆ coefficients [1, -3, 1, -1, 3, -1] satisfy:
- Signed sum = 0 (kills constants)
- Absolute sum = 10 = C(5,2)
- Positive/negative part sums = 5 = activeLevels
- Evaluation point sum φ³+φ²+φ+ψ+ψ²+ψ³ = 8 = L(1)+L(2)+L(3)
-/

theorem D6_coeff_sum : (1 : ℤ) + (-3) + 1 + (-1) + 3 + (-1) = 0 := by decide

theorem D6_coeff_abs_sum : (1 : ℕ) + 3 + 1 + 1 + 3 + 1 = Nat.choose 5 2 := by decide

theorem D6_coeff_positive_sum : (1 : ℕ) + 1 + 3 = 6 - 2 + 1 := by decide

theorem D6_coeff_negative_sum : (3 : ℕ) + 1 + 1 = 6 - 2 + 1 := by decide

/-- Sum of D₆ evaluation multipliers: φ³+φ²+φ+ψ+ψ²+ψ³ = 8 -/
theorem D6_eval_multiplier_sum :
    φ ^ 3 + φ ^ 2 + φ + ψ + ψ ^ 2 + ψ ^ 3 = 8 := by
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [hψ2]
  rw [hφ2, hψ2, hφ3, hψ3]; linarith [phi_add_psi]

/-! ## D₆ Spectral Invariants

The D₆ evaluation multipliers {φ³,φ²,φ,ψ,ψ²,ψ³} have elementary symmetric polynomials:
- e₁ = 8 (trace, proven above as D6_eval_multiplier_sum)
- e₂ = 18 (pairwise products)
- e₃ = 6 (triple products)
- e₄ = -12 (4-tuple products)
- e₅ = -2 (5-tuple products)
- e₆ = 1 (determinant = (φψ)⁶ = 1)

The characteristic polynomial p(x) = x⁶ - 8x⁵ + 18x⁴ - 6x³ - 12x² + 2x + 1
determines the 6th-order recurrence for dissipation coefficients.
-/

/-- D₆ characteristic polynomial: x⁶ - 8x⁵ + 18x⁴ - 6x³ - 12x² + 2x + 1 -/
noncomputable def D6_charPoly (x : ℝ) : ℝ :=
  x ^ 6 - 8 * x ^ 5 + 18 * x ^ 4 - 6 * x ^ 3 - 12 * x ^ 2 + 2 * x + 1

/-- Product of all D₆ evaluation multipliers: e₆ = (φψ)⁶ = 1 -/
theorem D6_eval_multiplier_product :
    φ ^ 3 * φ ^ 2 * φ * ψ * ψ ^ 2 * ψ ^ 3 = 1 := by
  have : φ ^ 3 * φ ^ 2 * φ * ψ * ψ ^ 2 * ψ ^ 3 = (φ * ψ) ^ 6 := by ring
  rw [this, phi_mul_psi]; norm_num

/-- e₂ = 18: sum of pairwise products of D₆ evaluation multipliers -/
theorem D6_eval_pairwise_sum :
    φ ^ 3 * φ ^ 2 + φ ^ 3 * φ + φ ^ 3 * ψ + φ ^ 3 * ψ ^ 2 + φ ^ 3 * ψ ^ 3 +
    φ ^ 2 * φ + φ ^ 2 * ψ + φ ^ 2 * ψ ^ 2 + φ ^ 2 * ψ ^ 3 +
    φ * ψ + φ * ψ ^ 2 + φ * ψ ^ 3 +
    ψ * ψ ^ 2 + ψ * ψ ^ 3 +
    ψ ^ 2 * ψ ^ 3 = 18 := by
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  have hprod : φ * ψ = -1 := phi_mul_psi
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [hψ2]
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hφ5 : φ ^ 5 = 5 * φ + 3 := by nlinarith [hφ2, hφ4]
  have hψ5 : ψ ^ 5 = 5 * ψ + 3 := by nlinarith [hψ2, hψ4]
  have cross1 : φ ^ 3 * ψ = (2*φ+1)*ψ := by rw [hφ3]
  have cross2 : φ ^ 3 * ψ ^ 2 = (2*φ+1)*(ψ+1) := by rw [hφ3, hψ2]
  have cross3 : φ ^ 3 * ψ ^ 3 = (φ * ψ) ^ 3 := by ring
  have cross4 : φ ^ 2 * ψ = (φ+1)*ψ := by rw [hφ2]
  have cross5 : φ ^ 2 * ψ ^ 2 = (φ * ψ) ^ 2 := by ring
  have cross6 : φ ^ 2 * ψ ^ 3 = (φ+1)*(2*ψ+1) := by rw [hφ2, hψ3]
  have cross7 : φ * ψ ^ 2 = φ*(ψ+1) := by rw [hψ2]
  have cross8 : φ * ψ ^ 3 = φ*(2*ψ+1) := by rw [hψ3]
  nlinarith [hφ5, hψ5, hφ4, hψ4, hφ3, hψ3, hφ2, hψ2, hsum, hprod,
             cross1, cross2, cross3, cross4, cross5, cross6, cross7, cross8,
             mul_comm φ ψ]

/-- e₃ = 6: sum of triple products (φ^a·ψ^b form) -/
theorem D6_eval_triple_sum :
    ψ ^ 6 + φ * ψ ^ 3 + φ * ψ ^ 4 + φ * ψ ^ 5 +
    φ ^ 2 * ψ ^ 3 + φ ^ 2 * ψ ^ 4 + φ ^ 2 * ψ ^ 5 +
    φ ^ 3 * ψ + φ ^ 3 * ψ ^ 2 + 2 * (φ ^ 3 * ψ ^ 3) +
    φ ^ 3 * ψ ^ 4 + φ ^ 3 * ψ ^ 5 + φ ^ 4 * ψ + φ ^ 4 * ψ ^ 2 +
    φ ^ 4 * ψ ^ 3 + φ ^ 5 * ψ + φ ^ 5 * ψ ^ 2 + φ ^ 5 * ψ ^ 3 + φ ^ 6 = 6 := by
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  have hprod : φ * ψ = -1 := phi_mul_psi
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [hψ2]
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hφ5 : φ ^ 5 = 5 * φ + 3 := by nlinarith [hφ2, hφ4]
  have hψ5 : ψ ^ 5 = 5 * ψ + 3 := by nlinarith [hψ2, hψ4]
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by nlinarith [hφ2, hφ4]
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by nlinarith [hψ2, hψ4]
  nlinarith [hφ6, hψ6, hφ5, hψ5, hφ4, hψ4, hφ3, hψ3, hφ2, hψ2, hsum, hprod]

/-- e₄ = -12: sum of 4-tuple products -/
theorem D6_eval_4tuple_sum :
    φ * ψ ^ 6 + φ ^ 2 * ψ ^ 6 + φ ^ 3 * ψ ^ 5 + φ ^ 3 * ψ ^ 4 + φ ^ 3 * ψ ^ 3 +
    φ ^ 3 * ψ ^ 6 + φ ^ 4 * ψ ^ 5 + φ ^ 4 * ψ ^ 4 + φ ^ 4 * ψ ^ 3 +
    φ ^ 5 * ψ ^ 5 + φ ^ 5 * ψ ^ 4 + φ ^ 5 * ψ ^ 3 +
    φ ^ 6 * ψ ^ 3 + φ ^ 6 * ψ ^ 2 + φ ^ 6 * ψ = -12 := by
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  have hprod : φ * ψ = -1 := phi_mul_psi
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [hψ2]
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hφ5 : φ ^ 5 = 5 * φ + 3 := by nlinarith [hφ2, hφ4]
  have hψ5 : ψ ^ 5 = 5 * ψ + 3 := by nlinarith [hψ2, hψ4]
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by nlinarith [hφ2, hφ4]
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by nlinarith [hψ2, hψ4]
  nlinarith [hφ6, hψ6, hφ5, hψ5, hφ4, hψ4, hφ3, hψ3, hφ2, hψ2, hsum, hprod]

/-- e₅ = -2: sum of 5-tuple products -/
theorem D6_eval_5tuple_sum :
    φ ^ 3 * ψ ^ 6 + φ ^ 4 * ψ ^ 6 + φ ^ 5 * ψ ^ 6 +
    φ ^ 6 * ψ ^ 5 + φ ^ 6 * ψ ^ 4 + φ ^ 6 * ψ ^ 3 = -2 := by
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hsum : φ + ψ = 1 := phi_add_psi
  have hprod : φ * ψ = -1 := phi_mul_psi
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [hψ2]
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hφ5 : φ ^ 5 = 5 * φ + 3 := by nlinarith [hφ2, hφ4]
  have hψ5 : ψ ^ 5 = 5 * ψ + 3 := by nlinarith [hψ2, hψ4]
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by nlinarith [hφ2, hφ4]
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by nlinarith [hψ2, hψ4]
  nlinarith [hφ6, hψ6, hφ5, hψ5, hφ4, hψ4, hφ3, hψ3, hφ2, hψ2, hsum, hprod]

private lemma charPoly_root_phi : D6_charPoly φ = 0 := by
  simp only [D6_charPoly]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hφ5 : φ ^ 5 = 5 * φ + 3 := by nlinarith [hφ2, hφ4]
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by nlinarith [hφ2, hφ4]
  nlinarith [phi_cubed]

private lemma charPoly_root_psi : D6_charPoly ψ = 0 := by
  simp only [D6_charPoly]
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hψ5 : ψ ^ 5 = 5 * ψ + 3 := by nlinarith [hψ2, hψ4]
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by nlinarith [hψ2, hψ4]
  nlinarith

private lemma charPoly_root_phi2 : D6_charPoly (φ ^ 2) = 0 := by
  simp only [D6_charPoly]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by nlinarith [hφ2, hφ4]
  have hφ8 : φ ^ 8 = 21 * φ + 13 := by nlinarith [hφ2, hφ4]
  have hφ10 : φ ^ 10 = 55 * φ + 34 := by nlinarith [hφ2, hφ8]
  have hφ12 : φ ^ 12 = 144 * φ + 89 := by nlinarith [hφ2, hφ10]
  nlinarith

private lemma charPoly_root_psi2 : D6_charPoly (ψ ^ 2) = 0 := by
  simp only [D6_charPoly]
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by nlinarith [hψ2, hψ4]
  have hψ8 : ψ ^ 8 = 21 * ψ + 13 := by nlinarith [hψ2, hψ4]
  have hψ10 : ψ ^ 10 = 55 * ψ + 34 := by nlinarith [hψ2, hψ8]
  have hψ12 : ψ ^ 12 = 144 * ψ + 89 := by nlinarith [hψ2, hψ10]
  nlinarith

-- nlinarith needs φ^18 = 2584φ+1597 reduction chain
private lemma charPoly_root_phi3 : D6_charPoly (φ ^ 3) = 0 := by
  simp only [D6_charPoly]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hφ5 : φ ^ 5 = 5 * φ + 3 := by nlinarith [hφ2, hφ4]
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by nlinarith [hφ2, hφ4]
  have hφ8 : φ ^ 8 = 21 * φ + 13 := by nlinarith [hφ2, hφ4]
  have hφ9 : φ ^ 9 = 34 * φ + 21 := by nlinarith [hφ4, hφ5]
  have hφ10 : φ ^ 10 = 55 * φ + 34 := by nlinarith [hφ2, hφ8]
  have hφ12 : φ ^ 12 = 144 * φ + 89 := by nlinarith [hφ2, hφ10]
  have hφ15 : φ ^ 15 = 610 * φ + 377 := by nlinarith [hφ6, hφ9]
  have hφ18 : φ ^ 18 = 2584 * φ + 1597 := by nlinarith [hφ8, hφ10]
  nlinarith [phi_cubed]

-- nlinarith needs ψ^18 = 2584ψ+1597 reduction chain
private lemma charPoly_root_psi3 : D6_charPoly (ψ ^ 3) = 0 := by
  simp only [D6_charPoly]
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hψ5 : ψ ^ 5 = 5 * ψ + 3 := by nlinarith [hψ2, hψ4]
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by nlinarith [hψ2, hψ4]
  have hψ8 : ψ ^ 8 = 21 * ψ + 13 := by nlinarith [hψ2, hψ4]
  have hψ9 : ψ ^ 9 = 34 * ψ + 21 := by nlinarith [hψ4, hψ5]
  have hψ10 : ψ ^ 10 = 55 * ψ + 34 := by nlinarith [hψ2, hψ8]
  have hψ12 : ψ ^ 12 = 144 * ψ + 89 := by nlinarith [hψ2, hψ10]
  have hψ15 : ψ ^ 15 = 610 * ψ + 377 := by nlinarith [hψ6, hψ9]
  have hψ18 : ψ ^ 18 = 2584 * ψ + 1597 := by nlinarith [hψ8, hψ10]
  nlinarith

/-- Each D₆ evaluation multiplier is a root of the characteristic polynomial -/
theorem D6_charPoly_roots :
    D6_charPoly (φ ^ 3) = 0 ∧ D6_charPoly (φ ^ 2) = 0 ∧ D6_charPoly φ = 0 ∧
    D6_charPoly ψ = 0 ∧ D6_charPoly (ψ ^ 2) = 0 ∧ D6_charPoly (ψ ^ 3) = 0 :=
  ⟨charPoly_root_phi3, charPoly_root_phi2, charPoly_root_phi,
   charPoly_root_psi, charPoly_root_psi2, charPoly_root_psi3⟩

/-- D₆ spectral invariants summary -/
theorem D6_spectral_invariants :
    (φ ^ 3 + φ ^ 2 + φ + ψ + ψ ^ 2 + ψ ^ 3 = 8) ∧
    (φ ^ 3 * φ ^ 2 * φ * ψ * ψ ^ 2 * ψ ^ 3 = 1) ∧
    (D6_charPoly (φ ^ 3) = 0 ∧ D6_charPoly (φ ^ 2) = 0 ∧ D6_charPoly φ = 0 ∧
     D6_charPoly ψ = 0 ∧ D6_charPoly (ψ ^ 2) = 0 ∧ D6_charPoly (ψ ^ 3) = 0) :=
  ⟨D6_eval_multiplier_sum, D6_eval_multiplier_product, D6_charPoly_roots⟩

/-! ## D₆ Sector Factorization

The characteristic polynomial factors into three quadratic sectors:
  p(x) = (x²-x-1)(x²-3x+1)(x²-4x-1)
corresponding to matter (φ,ψ), gauge (φ²,ψ²), gravity (φ³,ψ³).
-/

/-- D₆ charPoly factors as product of three sector polynomials -/
theorem D6_charPoly_factorization (x : ℝ) :
    D6_charPoly x =
    (x ^ 2 - x - 1) * (x ^ 2 - 3 * x + 1) * (x ^ 2 - 4 * x - 1) := by
  unfold D6_charPoly; ring

/-- Sector traces: φᵏ+ψᵏ for k=1,2,3 -/
theorem sector_traces :
    φ + ψ = 1 ∧ φ ^ 2 + ψ ^ 2 = 3 ∧ φ ^ 3 + ψ ^ 3 = 4 := by
  constructor
  · exact phi_add_psi
  constructor
  · have hφ2 := golden_ratio_property; have hψ2 := psi_sq
    nlinarith [phi_add_psi]
  · nlinarith [phi_cubed, psi_sq, phi_add_psi]

/-- Gravity sector trace = spacetimeDim: φ³+ψ³ = 4 -/
theorem gravity_trace_eq_spacetimeDim :
    φ ^ 3 + ψ ^ 3 = spacetimeDim := by
  simp only [spacetimeDim, spatialDim, timeDim]; push_cast
  nlinarith [phi_cubed, psi_sq, phi_add_psi]

/-- Gravity sector determinant = -1: (φψ)³ = (-1)³ = -1 -/
theorem gravity_sector_det : (φ * ψ) ^ 3 = -1 := by
  rw [phi_mul_psi]; norm_num

/-- Gravity sector discriminant = C(6,3) = spacetimeDim × activeDLevels -/
theorem gravity_sector_discriminant :
    (4 : ℕ) ^ 2 + 4 * 1 = Nat.choose 6 3 := by decide

theorem gravity_disc_eq_spacetime_times_active :
    Nat.choose 6 3 = spacetimeDim * (6 - 2 + 1) := by
  simp only [spacetimeDim, spatialDim, timeDim]; decide

/-- Matter and gauge sectors have equal discriminant = 5 = activeDLevels -/
theorem matter_gauge_discriminant :
    (1 : ℕ) ^ 2 + 4 * 1 = 5 ∧ (3 : ℕ) ^ 2 - 4 * 1 = 5 := ⟨rfl, rfl⟩

/-- Complete sector discriminant structure -/
theorem sector_discriminants :
    -- Matter (x²-x-1): Δ = 1+4 = 5
    ((1 : ℕ) ^ 2 + 4 * 1 = 5) ∧
    -- Gauge (x²-3x+1): Δ = 9-4 = 5
    ((3 : ℕ) ^ 2 - 4 * 1 = 5) ∧
    -- Gravity (x²-4x-1): Δ = 16+4 = 20 = C(6,3)
    ((4 : ℕ) ^ 2 + 4 * 1 = Nat.choose 6 3) :=
  ⟨rfl, rfl, by decide⟩

/-- Sector trace squares: 1²+3²+4² = 26 -/
theorem sector_trace_sq_sum : (1 : ℝ) ^ 2 + 3 ^ 2 + 4 ^ 2 = 26 := by norm_num

/-! ## Sector-Invariant Derivation of Physical Exponents

The D₆ characteristic polynomial factors as
  p(x) = (x²-x-1)(x²-3x+1)(x²-4x-1)
with sector traces tₖ = L(k): t₁=1 (matter), t₂=3 (gauge), t₃=4 (gravity).

All physical exponents derive from three spectral invariants plus
the vacuum dimension d = kerDim(D₆) = spatialDim = 3:
  p₃ = Σ tₖ³ = 92     (sector self-interaction)
  e₃ = Π tₖ  = 12      (cross-sector coupling)
  σ  = Σ tₖ² = 26      (sector trace square sum)
  D  = t₃ = L(3) = spacetimeDim = 4

Formulas:
  107 = p₃ + e₃ + d
  45  = d × (e₃ + d)
  152 = p₃ + D × (e₃ + d)
  582 = D × 152 - σ
-/

/-- 1³+3³+4³ = 92: third power sum of sector traces -/
theorem sector_trace_cube_sum :
    (1 : ℝ) ^ 3 + 3 ^ 3 + 4 ^ 3 = 92 := by norm_num

/-- 1×3×4 = 12: product of all sector traces -/
theorem sector_trace_product : (1 : ℝ) * 3 * 4 = 12 := by norm_num

/-- e₃ + d = C(6,2): sector product + vacuum dim = total pairs -/
theorem sector_product_plus_kerDim_eq_pairs :
    1 * 3 * 4 + spatialDim = Nat.choose 6 2 := by decide

/-- 107 = p₃ + e₃ + d -/
theorem leptonExponent_from_sector_invariants :
    (1 : ℝ) ^ 3 + 3 ^ 3 + 4 ^ 3 + 1 * 3 * 4 +
    (spatialDim : ℝ) = 107 := by
  norm_num [spatialDim]

/-- Equivalence: sector-invariant derivation = leptonExponent -/
theorem leptonExponent_old_eq_sector :
    (1 : ℝ) ^ 3 + 3 ^ 3 + 4 ^ 3 + 1 * 3 * 4 +
    (spatialDim : ℝ) = (leptonExponent : ℝ) := by
  simp only [spatialDim, leptonExponent, triangular, Nat.choose]; norm_num

/-- 45 = d × (e₃ + d) = spatialDim × C(6,2) -/
theorem cmbDecoupling_from_sector_invariants :
    (spatialDim : ℝ) * ((1 : ℝ) * 3 * 4 +
    (spatialDim : ℝ)) = (cmbDecouplingFactor : ℝ) := by
  simp only [spatialDim, cmbDecouplingFactor, triangular, Nat.choose]; norm_num

/-- 152 = p₃ + D × (e₃ + d) -/
theorem cmbExponent_from_sector_invariants :
    (1 : ℝ) ^ 3 + 3 ^ 3 + 4 ^ 3 +
    (spacetimeDim : ℝ) * ((1 : ℝ) * 3 * 4 +
    (spatialDim : ℝ)) = (cmbTemperatureExponent : ℝ) := by
  simp only [spacetimeDim, spatialDim, timeDim, cmbTemperatureExponent,
    leptonExponent, cmbDecouplingFactor, triangular, Nat.choose]; norm_num

/-- 582 = D × 152 - σ -/
theorem cosmoExponent_from_sector_invariants :
    (spacetimeDim : ℝ) * (cmbTemperatureExponent : ℝ) -
    ((1 : ℝ) ^ 2 + 3 ^ 2 + 4 ^ 2) = (cosmologicalExponent : ℝ) := by
  simp only [spacetimeDim, spatialDim, timeDim, cmbTemperatureExponent,
    cosmologicalExponent, leptonExponent, cmbDecouplingFactor,
    sectorTraceSq, triangular, Nat.choose]; norm_num

/-- All exponents from sector invariants (ℕ summary) -/
theorem sector_invariant_derivation :
    -- p₃ = 92
    (1 ^ 3 + 3 ^ 3 + 4 ^ 3 = 92) ∧
    -- e₃ = 12
    (1 * 3 * 4 = 12) ∧
    -- σ = 26
    (1 ^ 2 + 3 ^ 2 + 4 ^ 2 = 26) ∧
    -- e₃ + d = C(6,2)
    (1 * 3 * 4 + spatialDim = Nat.choose 6 2) ∧
    -- 107 = p₃ + e₃ + d
    (1 ^ 3 + 3 ^ 3 + 4 ^ 3 + 1 * 3 * 4 + spatialDim = 107) ∧
    -- 45 = d(e₃ + d)
    (spatialDim * (1 * 3 * 4 + spatialDim) = 45) ∧
    -- 152 = p₃ + D(e₃ + d)
    (1 ^ 3 + 3 ^ 3 + 4 ^ 3 + spacetimeDim * (1 * 3 * 4 + spatialDim) = 152) ∧
    -- 582 = D × 152 - σ
    (spacetimeDim * 152 - (1 ^ 2 + 3 ^ 2 + 4 ^ 2) = 582) := by
  simp only [spatialDim, spacetimeDim, timeDim]; decide

/-! ## Inverse Square Law from D₆ Algebra

Newton's inverse square law F ∝ 1/r² is derived purely from the D₆ operator structure:
1. φ⁻¹ = -ψ (golden conjugate inversion)
2. D₆(t⁻¹²) = 0 (inverse-square monomial is in extended kernel)
3. D₆(t⁻¹)(x) = 6/((φ-ψ)⁴x²) ∝ x⁻² (force is inverse-square)
4. □_φ(t⁻¹) = D₆(D₆(t⁻¹)) = 0 (1/r potential is harmonic under FUST d'Alembertian)
-/

section InverseSquareLaw

lemma phi_inv_eq_neg_psi : φ⁻¹ = -ψ := Real.inv_goldenRatio

lemma psi_ne_zero : ψ ≠ 0 := ne_of_lt psi_neg

lemma phi_ne_zero : φ ≠ 0 := ne_of_gt phi_pos

lemma psi_inv_eq_neg_phi : ψ⁻¹ = -φ := by
  have key : (-φ) * ψ = 1 := by linarith [phi_mul_psi]
  exact mul_right_cancel₀ psi_ne_zero (show ψ⁻¹ * ψ = (-φ) * ψ from by
    rw [inv_mul_cancel₀ psi_ne_zero, key])

/-- D₆ annihilates t⁻¹²: the inverse-square monomial is in the extended kernel.
    Uses φ⁻² = ψ² and ψ⁻² = φ² from golden conjugate inversion. -/
theorem D6_inv_sq_zero (x : ℝ) (hx : x ≠ 0) : D6 (fun t => t⁻¹ ^ 2) x = 0 := by
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ_ne := phi_ne_zero
  have hψ_ne := psi_ne_zero
  have expand (a : ℝ) (ha : a * x ≠ 0) : (a * x)⁻¹ ^ 2 = a⁻¹ ^ 2 * x⁻¹ ^ 2 := by
    rw [mul_inv_rev, mul_pow, mul_comm]
  rw [expand _ (mul_ne_zero (pow_ne_zero 3 hφ_ne) hx),
      expand _ (mul_ne_zero (pow_ne_zero 2 hφ_ne) hx),
      expand _ (mul_ne_zero hφ_ne hx),
      expand _ (mul_ne_zero hψ_ne hx),
      expand _ (mul_ne_zero (pow_ne_zero 2 hψ_ne) hx),
      expand _ (mul_ne_zero (pow_ne_zero 3 hψ_ne) hx)]
  rw [show (φ ^ 3)⁻¹ = φ⁻¹ ^ 3 from (inv_pow φ 3).symm,
      show (φ ^ 2)⁻¹ = φ⁻¹ ^ 2 from (inv_pow φ 2).symm,
      show (ψ ^ 2)⁻¹ = ψ⁻¹ ^ 2 from (inv_pow ψ 2).symm,
      show (ψ ^ 3)⁻¹ = ψ⁻¹ ^ 3 from (inv_pow ψ 3).symm]
  rw [phi_inv_eq_neg_psi, psi_inv_eq_neg_phi]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by nlinarith [hφ2, hφ4]
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by nlinarith [hψ2, hψ4]
  have hsum : φ + ψ = 1 := phi_add_psi
  have hnum : ((-ψ) ^ 3) ^ 2 * x⁻¹ ^ 2 - 3 * (((-ψ) ^ 2) ^ 2 * x⁻¹ ^ 2) +
      (-ψ) ^ 2 * x⁻¹ ^ 2 - (-φ) ^ 2 * x⁻¹ ^ 2 +
      3 * (((-φ) ^ 2) ^ 2 * x⁻¹ ^ 2) - ((-φ) ^ 3) ^ 2 * x⁻¹ ^ 2 = 0 := by
    have h1 : ((-ψ) ^ 3) ^ 2 = ψ ^ 6 := by ring
    have h2 : ((-ψ) ^ 2) ^ 2 = ψ ^ 4 := by ring
    have h3 : (-ψ) ^ 2 = ψ ^ 2 := by ring
    have h4 : (-φ) ^ 2 = φ ^ 2 := by ring
    have h5 : ((-φ) ^ 2) ^ 2 = φ ^ 4 := by ring
    have h6 : ((-φ) ^ 3) ^ 2 = φ ^ 6 := by ring
    nlinarith [hφ2, hψ2, hφ4, hψ4, hφ6, hψ6, hsum]
  calc _ = (((-ψ) ^ 3) ^ 2 * x⁻¹ ^ 2 - 3 * (((-ψ) ^ 2) ^ 2 * x⁻¹ ^ 2) +
      (-ψ) ^ 2 * x⁻¹ ^ 2 - (-φ) ^ 2 * x⁻¹ ^ 2 +
      3 * (((-φ) ^ 2) ^ 2 * x⁻¹ ^ 2) - ((-φ) ^ 3) ^ 2 * x⁻¹ ^ 2) / (D6Denom * x) := by ring_nf
    _ = 0 / (D6Denom * x) := by rw [hnum]
    _ = 0 := by ring

/-- D₆(t⁻¹)(x) = 6/((φ-ψ)⁴x²): the gravitational force is inverse-square.
    The coefficient C(-1) = 6(φ-ψ) = 6√5 is nonzero, confirming the force exists. -/
theorem D6_inv_one (x : ℝ) (hx : x ≠ 0) :
    D6 (fun t => t⁻¹) x = 6 / ((φ - ψ) ^ 4 * x ^ 2) := by
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ_ne := phi_ne_zero
  have hψ_ne := psi_ne_zero
  have expand (a : ℝ) (ha : a ≠ 0) : (a * x)⁻¹ = a⁻¹ * x⁻¹ := by
    rw [mul_inv_rev, mul_comm]
  rw [expand (φ ^ 3) (pow_ne_zero 3 hφ_ne), expand (φ ^ 2) (pow_ne_zero 2 hφ_ne),
      expand φ hφ_ne, expand ψ hψ_ne,
      expand (ψ ^ 2) (pow_ne_zero 2 hψ_ne), expand (ψ ^ 3) (pow_ne_zero 3 hψ_ne)]
  rw [show (φ ^ 3)⁻¹ = φ⁻¹ ^ 3 from (inv_pow φ 3).symm,
      show (φ ^ 2)⁻¹ = φ⁻¹ ^ 2 from (inv_pow φ 2).symm,
      show (ψ ^ 2)⁻¹ = ψ⁻¹ ^ 2 from (inv_pow ψ 2).symm,
      show (ψ ^ 3)⁻¹ = ψ⁻¹ ^ 3 from (inv_pow ψ 3).symm]
  rw [phi_inv_eq_neg_psi, psi_inv_eq_neg_phi]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by nlinarith [hψ2]
  have hdiff_ne : φ - ψ ≠ 0 := by
    rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hcoef : -(ψ ^ 3) - 3 * ψ ^ 2 - ψ + φ + 3 * φ ^ 2 + φ ^ 3 = 6 * (φ - ψ) := by
    rw [hφ3, hφ2, hψ3, hψ2]; ring
  have hx_ne : x ≠ 0 := hx
  have hdiff5x_ne : D6Denom * x ≠ 0 := D6Denom_mul_ne_zero x hx
  have hdiff4x2_ne : (φ - ψ) ^ 4 * x ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 hdiff_ne) (pow_ne_zero 2 hx)
  rw [show ((-ψ) ^ 3 * x⁻¹ - 3 * ((-ψ) ^ 2 * x⁻¹) + (-ψ) * x⁻¹ - (-φ) * x⁻¹ +
      3 * ((-φ) ^ 2 * x⁻¹) - (-φ) ^ 3 * x⁻¹) / (D6Denom * x) =
      (-(ψ ^ 3) - 3 * ψ ^ 2 - ψ + φ + 3 * φ ^ 2 + φ ^ 3) * x⁻¹ /
      (D6Denom * x) from by unfold D6Denom; ring]
  rw [hcoef]
  rw [show 6 * (φ - ψ) * x⁻¹ / (D6Denom * x) = 6 / ((φ - ψ) ^ 4 * x ^ 2) from by
    unfold D6Denom; field_simp]

/-- D₆ preserves pointwise equality at evaluation points -/
lemma D6_congr_nonzero (f g : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hfg : ∀ y, y ≠ 0 → f y = g y) : D6 f x = D6 g x := by
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ_ne := phi_ne_zero
  have hψ_ne := psi_ne_zero
  rw [hfg _ (mul_ne_zero (pow_ne_zero 3 hφ_ne) hx),
      hfg _ (mul_ne_zero (pow_ne_zero 2 hφ_ne) hx),
      hfg _ (mul_ne_zero hφ_ne hx),
      hfg _ (mul_ne_zero hψ_ne hx),
      hfg _ (mul_ne_zero (pow_ne_zero 2 hψ_ne) hx),
      hfg _ (mul_ne_zero (pow_ne_zero 3 hψ_ne) hx)]

/-- The 1/r potential is harmonic under the FUST d'Alembertian:
    □_φ(t⁻¹) = D₆(D₆(t⁻¹)) = 0.
    This follows because D₆(t⁻¹) ∝ t⁻¹² and D₆(t⁻¹²) = 0. -/
theorem dAlembertian_inv_zero (x : ℝ) (hx : x ≠ 0) :
    FUSTDAlembertian (fun t => t⁻¹) x = 0 := by
  simp only [FUSTDAlembertian]
  have hdiff_ne : φ - ψ ≠ 0 := by
    rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hfg : ∀ y, y ≠ 0 →
      D6 (fun t => t⁻¹) y = (6 / (φ - ψ) ^ 4) * (fun t => t⁻¹ ^ 2) y := by
    intro y hy
    simp only
    rw [D6_inv_one y hy]
    field_simp
  rw [D6_congr_nonzero _ _ x hx hfg]
  rw [D6_homogeneous]
  rw [D6_inv_sq_zero x hx]
  ring

/-- Inverse square law derivation from D₆ structure -/
theorem inverse_square_law_derivation :
    -- (1) Spatial dimension from ker(D₆) = 3
    spatialDim = 3 ∧
    -- (2) D₆(t⁻¹²) = 0: inverse-square monomial in extended kernel
    (∀ x, x ≠ 0 → D6 (fun t => t⁻¹ ^ 2) x = 0) ∧
    -- (3) Force is inverse-square: D₆(t⁻¹) ∝ x⁻²
    (∀ x, x ≠ 0 → D6 (fun t => t⁻¹) x = 6 / ((φ - ψ) ^ 4 * x ^ 2)) ∧
    -- (4) 1/r potential is harmonic: □_φ(t⁻¹) = 0
    (∀ x, x ≠ 0 → FUSTDAlembertian (fun t => t⁻¹) x = 0) := by
  exact ⟨rfl, D6_inv_sq_zero, D6_inv_one, dAlembertian_inv_zero⟩

/-! ### Extended d'Alembertian Kernel

□_φ[tⁿ] = 0 for n ∈ {-1, 0, 1, 2, 3}.
For n=0,1,2: D₆[tⁿ]=0, so □_φ[tⁿ]=D₆(0)=0.
For n=3: D₆[t³] ∝ t², then D₆[t²]=0.
For n=-1: D₆[t⁻¹] ∝ t⁻², then D₆[t⁻²]=0.
-/

theorem dAlembertian_cubic_zero (x : ℝ) (hx : x ≠ 0) :
    FUSTDAlembertian (fun t => t ^ 3) x = 0 := by
  simp only [FUSTDAlembertian]
  have hdiff_ne : φ - ψ ≠ 0 := by
    rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hD6_cubic : ∀ y, y ≠ 0 → D6 (fun t => t ^ 3) y =
      ((φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9) / D6Denom) * y ^ 2 := by
    intro y hy
    simp only [D6, N6, hy, ↓reduceIte]
    unfold D6Denom; field_simp
  have hfg : ∀ y, y ≠ 0 → D6 (fun t => t ^ 3) y =
      ((φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9) / D6Denom) * (fun t => t ^ 2) y := by
    intro y hy; simp only; exact hD6_cubic y hy
  rw [D6_congr_nonzero _ _ x hx hfg, D6_homogeneous, D6_quadratic x hx, mul_zero]

/-- □_φ kernel: □_φ[tⁿ] = 0 for n = -1, 0, 1, 2, 3 -/
theorem dAlembertian_extended_kernel :
    (∀ x, x ≠ 0 → FUSTDAlembertian (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → FUSTDAlembertian (fun t => t) x = 0) ∧
    (∀ x, x ≠ 0 → FUSTDAlembertian (fun t => t ^ 2) x = 0) ∧
    (∀ x, x ≠ 0 → FUSTDAlembertian (fun t => t ^ 3) x = 0) ∧
    (∀ x, x ≠ 0 → FUSTDAlembertian (fun t => t⁻¹) x = 0) := by
  refine ⟨?_, ?_, ?_, dAlembertian_cubic_zero, dAlembertian_inv_zero⟩
  · intro x hx
    exact dAlembertian_zero_on_kernel _ ⟨1, 0, 0, fun t => by ring⟩ x hx
  · intro x hx
    exact dAlembertian_zero_on_kernel _ ⟨0, 1, 0, fun t => by ring⟩ x hx
  · intro x hx
    exact dAlembertian_zero_on_kernel _ ⟨0, 0, 1, fun t => by ring⟩ x hx

end InverseSquareLaw

/-! ## Dimensional Derivation Structure

D₆[tⁿ](x) = C(n)·xⁿ/(φ-ψ)⁵ where C(n) is the dissipation coefficient.
The monomial eigenvalue Λ(n) = C(n)/(φ-ψ)⁵ vanishes for n ∈ {0,1,2}:
  Δ=0 (constants), Δ=1 (mass), Δ=2 (kinetic energy).
Since D₆ annihilates Δ=1, mass ratios m_e/m_Pl are boundary data, not eigenvalue data.
Physical exponents thus form a three-layer structure:
  Layer 1: D₆ eigenvalues → d=3, d+1=4, σ=26, F∝1/r²
  Layer 2: D-hierarchy combinatorics → 107, 45 (boundary conditions)
  Layer 3: Physical assembly with dimensional intermediates → 152, 582
-/

/-- D₆ annihilates Δ=0 (constants), Δ=1 (mass), Δ=2 (kinetic energy) -/
theorem D6_kernel_dimensions :
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t ^ 2) x = 0) :=
  FUST.LeastAction.D6_kernel_dim_3

/-- D₆ does NOT annihilate Δ=-1: the force operator is outside the kernel -/
theorem D6_force_dimension_active (x : ℝ) (hx : x ≠ 0) :
    D6 (fun t => t⁻¹) x ≠ 0 := by
  rw [D6_inv_one x hx]
  have hdiff : (φ - ψ) ^ 4 ≠ 0 := by
    apply pow_ne_zero; rw [phi_sub_psi]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  exact div_ne_zero (by norm_num) (mul_ne_zero hdiff hx2)

/-- Layer 1: D₆ eigenvalue structure determines physical framework -/
theorem derivation_layer1_eigenvalues :
    spatialDim = 3 ∧
    spacetimeDim = 4 ∧
    sectorTraceSq = 26 ∧
    (∀ x, x ≠ 0 → D6 (fun t => t⁻¹) x = 6 / ((φ - ψ) ^ 4 * x ^ 2)) := by
  exact ⟨rfl, rfl, rfl, D6_inv_one⟩

/-- Layer 3: physical assembly with dimensional intermediates.
    152 = 107 + 45: T_CMB/T_Pl = (m_e/m_Pl) × (T_CMB/m_e), via [M] intermediate.
    582 = 4×152 - 26: ρ_Λ/ρ_Pl = (T_CMB/T_Pl)⁴ × φ^26, via [M⁴] intermediate. -/
theorem derivation_layer3_assembly :
    cmbTemperatureExponent = leptonExponent + cmbDecouplingFactor ∧
    cosmologicalExponent = spacetimeDim * cmbTemperatureExponent - sectorTraceSq ∧
    cmbTemperatureExponent = 152 ∧
    cosmologicalExponent = 582 := by
  refine ⟨rfl, rfl, cmbTemperatureExponent_value, cosmologicalExponent_value⟩

/-! ## Graviton Structural Prediction

The graviton is predicted (not postulated) by the D₆ operator structure:
1. Existence: D₆ charPoly = (matter)(gauge)(gravity) has a gravity sector (x²-4x-1)
2. Massless: □_φ(t⁻¹) = 0 (graviton propagator has no mass term)
3. Spin-2: max spin for massless particle = spatialDim - 1 = 2
4. Inverse square: D₆(t⁻¹) ∝ x⁻² (force law from operator algebra)
5. Coupling: m_e/m_Pl = φ^(-107-5/63) from D-hierarchy combinatorics

The gravity sector polynomial x²-4x-1 encodes:
- Trace = L(3) = 4 = spacetimeDim (gravity couples to spacetime dimension)
- Determinant = (φψ)³ = -1 (parity-odd, like matter sector)
- Discriminant = 20 = C(6,3) = spacetimeDim × activeDLevels
-/

/-- Graviton masslessness: □_φ(t⁻¹) = 0 means the graviton mode
    propagates without a mass term in the d'Alembertian. -/
theorem graviton_massless :
    ∀ x, x ≠ 0 → FUSTDAlembertian (fun t => t⁻¹) x = 0 :=
  dAlembertian_inv_zero

/-- Graviton spin = spatialDim - timeDim = 3 - 1 = 2 -/
theorem graviton_spin_from_spacetime :
    spatialDim - timeDim = 2 := by
  simp only [spatialDim, timeDim]

/-- Graviton spin = spacetimeDim / 2 = 4 / 2 = 2 -/
theorem graviton_spin_from_spacetimeDim :
    spacetimeDim / 2 = 2 := by
  simp only [spacetimeDim, spatialDim, timeDim]

/-- Complete graviton structural prediction -/
theorem graviton_prediction :
    -- Existence: gravity sector in D₆ charPoly factorization
    (∀ x : ℝ, D6_charPoly x =
      (x ^ 2 - x - 1) * (x ^ 2 - 3 * x + 1) * (x ^ 2 - 4 * x - 1)) ∧
    -- Gravity sector trace = spacetimeDim
    (φ ^ 3 + ψ ^ 3 = spacetimeDim) ∧
    -- Gravity sector determinant
    ((φ * ψ) ^ 3 = -1) ∧
    -- Gravity sector discriminant = C(6,3)
    ((4 : ℕ) ^ 2 + 4 * 1 = Nat.choose 6 3) ∧
    -- Massless: □_φ(t⁻¹) = 0
    (∀ x, x ≠ 0 → FUSTDAlembertian (fun t => t⁻¹) x = 0) ∧
    -- Spin-2 from spacetime structure
    (spatialDim - timeDim = 2) ∧
    -- Inverse square force law
    (∀ x, x ≠ 0 → D6 (fun t => t⁻¹) x = 6 / ((φ - ψ) ^ 4 * x ^ 2)) := by
  exact ⟨D6_charPoly_factorization, gravity_trace_eq_spacetimeDim,
         gravity_sector_det, gravity_sector_discriminant,
         dAlembertian_inv_zero, graviton_spin_from_spacetime, D6_inv_one⟩

end FUST.GravitationalCoupling
