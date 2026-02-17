import FUST.SpectralCoefficients
import FUST.Physics.MassGap
import FUST.DimensionalAnalysis

/-!
# Neutrino Mass Structure from D₅ ⊂ D₆ Kernel Filtration

All neutrino mass predictions from FUST D-structure:
- 3 flavors from dim ker(D₆) = 3
- Mass hierarchy from ker(D₅) ⊂ ker(D₆), dim = 2, 3
- Δm²₂₁/Δm²₃₁ = 1/30 from kerDimD5 × C(6,2)
- m_ν₃/m_e = Δ × φ^(-32) where 32 = kerDimD5^5
- Laurent boundary: D₆ annihilates t⁻², t² but D₅ detects both with coefficient 6
-/

namespace FUST.NeutrinoMass

open FUST.Dim FUST.SpectralCoefficients

/-! ## Part 1: D₅ Kernel Structure

ker(D₅) = {1, x} (dim = 2), ker(D₆) = {1, x, x²} (dim = 3).
The filtration ker(D₂) ⊂ ker(D₅) ⊂ ker(D₆) with dim = 1, 2, 3
determines the neutrino mass hierarchy. -/

/-- dim ker(D₅) = 2: D₅ annihilates {1, x} but not x² -/
abbrev kerDimD5 : ℕ := 2

/-- ker(D₅) contains 1 and x (proof: D5_const, D5_linear) -/
theorem kerD5_basis :
    (∀ x, x ≠ 0 → D5 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D5 id x = 0) :=
  ⟨fun x hx => D5_const 1 x hx, D5_linear⟩

/-- x² ∉ ker(D₅): the Higgs DOF separating ν₃ from ν₁,ν₂ -/
theorem kerD5_boundary :
    ∀ x, x ≠ 0 → D5 (fun t => t^2) x ≠ 0 := D5_not_annihilate_quadratic

/-! ## Part 2: Neutrino Mass Squared Ratio

Δm²₂₁/Δm²₃₁ = 1/(kerDimD5 × C(6,2)) = 1/30
where kerDimD5 = 2 (dim of solar pair) and C(6,2) = 15 (D₆ pair count). -/

/-- Neutrino mass squared denominator: kerDimD5 × C(6,2) = 2 × 15 = 30 -/
abbrev neutrinoMassSqDenom : ℕ := kerDimD5 * Nat.choose 6 2

theorem neutrinoMassSqDenom_eq : neutrinoMassSqDenom = 30 := rfl

/-- Structural decomposition: 30 = dim(ker D₅) × pairs(D₆) -/
theorem neutrinoMassSqDenom_structural :
    neutrinoMassSqDenom = kerDimD5 * Nat.choose 6 2 ∧
    kerDimD5 = 2 ∧ Nat.choose 6 2 = 15 := ⟨rfl, rfl, rfl⟩

/-- Neutrino mass squared ratio: Δm²₂₁/Δm²₃₁ = 1/30 -/
noncomputable abbrev neutrinoMassSqRatio : ℚ := 1 / neutrinoMassSqDenom

theorem neutrinoMassSqRatio_eq : neutrinoMassSqRatio = 1 / 30 := rfl

/-- Neutrino mass ratio m₂/m₃ = √(1/30) -/
noncomputable abbrev neutrinoMassRatio : ℝ := Real.sqrt (1 / 30)

/-- Neutrino mass hierarchy from kernel filtration -/
theorem neutrino_hierarchy_from_kernel :
    kerDimD5 = 2 ∧
    (∀ x, x ≠ 0 → D5 (fun t => t^2) x ≠ 0) ∧
    neutrinoMassSqDenom = 30 :=
  ⟨rfl, D5_not_annihilate_quadratic, rfl⟩

/-! ## Part 3: Absolute Mass Scale from D₅ Structure

m_ν₃/m_e = Δ × φ^(-32) where:
- Δ = 12/25 (D₆ mass gap)
- 32 = 2⁵ = (dim ker D₅)^(D₅ order) = kerDimD5^5

This gives m_ν₃ = Δ² × φ^(-32) in FUST units: the neutrino mass
acquires an extra Δ suppression factor (seesaw-like) from D₅ perturbation. -/

/-- Neutrino mass suppression exponent: 2⁵ = (dim ker D₅)^(D₅ order) -/
abbrev neutrinoMassExponent : ℕ := kerDimD5 ^ 5

theorem neutrinoMassExponent_eq : neutrinoMassExponent = 32 := rfl

theorem neutrinoMassExponent_structural :
    neutrinoMassExponent = kerDimD5 ^ 5 ∧
    kerDimD5 = 2 ∧ (5 : ℕ) = 5 := ⟨rfl, rfl, rfl⟩

/-- m_ν₃/m_e = Δ × φ^(-32): heaviest neutrino mass ratio -/
noncomputable abbrev nu3ElectronRatio : ℝ :=
  (12 : ℝ) / 25 * φ ^ (-(neutrinoMassExponent : ℤ))

theorem nu3ElectronRatio_eq :
    nu3ElectronRatio = (12 : ℝ) / 25 * φ ^ (-(32 : ℤ)) := rfl

/-- m_ν₂/m_e = Δ × φ^(-32) × √(1/30) -/
noncomputable abbrev nu2ElectronRatio : ℝ :=
  nu3ElectronRatio * Real.sqrt (1 / neutrinoMassSqDenom)

theorem nu2ElectronRatio_eq :
    nu2ElectronRatio = (12 : ℝ) / 25 * φ ^ (-(32 : ℤ)) * Real.sqrt (1 / 30) := rfl

/-- m_ν₃/m_e is positive -/
theorem nu3ElectronRatio_pos : nu3ElectronRatio > 0 := by
  unfold nu3ElectronRatio neutrinoMassExponent kerDimD5
  apply mul_pos (by norm_num : (0 : ℝ) < 12 / 25)
  exact zpow_pos phi_pos _

/-- Complete neutrino mass derivation from D₅ structure -/
theorem neutrino_mass_from_D5_structure :
    (neutrinoMassExponent = kerDimD5 ^ 5) ∧
    (neutrinoMassSqDenom = kerDimD5 * Nat.choose 6 2) ∧
    (∀ x, x ≠ 0 → D5 (fun t => t^2) x ≠ 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) :=
  ⟨rfl, rfl, D5_not_annihilate_quadratic, D6_quadratic⟩

/-! ## Part 4: Laurent Boundary Structure

Laurent ker(D₆) = {t⁻², 1, t, t²} (dim 4).
D₅ detects both t⁻² and t² with equal coefficient 6 (D₅ duality).
This boundary structure connects the spectral theory to the mass formula. -/

/-- Laurent boundary: D₅ detects both t² and t⁻² in ker(D₆) with equal coefficient -/
theorem neutrino_Laurent_boundary :
    D6CoeffZ (-2) = 0 ∧ D6CoeffZ 2 = 0 ∧
    D5CoeffZ (-2) = 6 ∧ D5CoeffZ 2 = 6 :=
  ⟨D6CoeffZ_neg_two, D6CoeffZ_two, D5CoeffZ_neg_two, D5CoeffZ_two⟩

/-- D₅ coefficient at d=2 equals C(4,2) = 6 (pair count of D₃) -/
theorem D5Coeff_two_eq_choose : D5CoeffZ 2 = Nat.choose 4 2 := by
  rw [D5CoeffZ_two]; simp [Nat.choose]

/-! ## Part 5: Dimensioned Neutrino Masses

Neutrinos have unique FDim in the D₆² sector:
m_ν₃ = Δ² × φ^(-32), m_ν₂ = m_ν₃ × √(1/30). -/

-- Neutrino FDim: D₆² sector
def dimNu3 : FDim := dimLagrangian * dimTimeD2 ^ (-(32 : ℤ))
def dimNu2 : FDim := dimNu3 * deriveFDim 2

/-- Neutrino mass squared ratio as RatioQ -/
def neutrinoMassSqRatio_dimQ : RatioQ :=
  ⟨1 / (kerDimD5 * Nat.choose 6 2 : ℚ)⟩

theorem neutrinoMassSqRatio_dimQ_val :
    neutrinoMassSqRatio_dimQ.val = 1 / 30 := by
  simp only [neutrinoMassSqRatio_dimQ, kerDimD5, Nat.choose]; norm_num

/-- m_ν₃ = Δ × Δ × φ^(-32) = Δ² × φ^(-2⁵) -/
noncomputable def nu3Mass : ScaleQ dimNu3 :=
  ⟨FUST.massGapΔ * nu3ElectronRatio⟩

theorem nu3Mass_val :
    nu3Mass.val = (12 / 25) * ((12 : ℝ) / 25 * φ ^ (-(32 : ℤ))) := by
  simp only [nu3Mass, nu3ElectronRatio_eq, FUST.massGapΔ]

/-- m_ν₃ / m_e = Δ × φ^(-32) (where m_e = Δ = massGapΔ) -/
theorem nu3_electron_ratio :
    nu3Mass.val / FUST.massGapΔ =
    (12 : ℝ) / 25 * φ ^ (-(32 : ℤ)) := by
  simp only [nu3Mass_val]
  unfold FUST.massGapΔ
  field_simp

/-- m_ν₂ = m_ν₃ × √(1/30) -/
noncomputable def nu2Mass : ScaleQ dimNu2 :=
  ⟨nu3Mass.val * Real.sqrt (1 / 30)⟩

theorem nu2_nu3_ratio :
    nu2Mass.val / nu3Mass.val = Real.sqrt (1 / 30) := by
  simp only [nu2Mass]
  have h : nu3Mass.val > 0 := by
    rw [nu3Mass_val]
    apply mul_pos (by norm_num : (0 : ℝ) < 12 / 25)
    apply mul_pos (by norm_num : (0 : ℝ) < 12 / 25)
    exact zpow_pos phi_pos _
  field_simp

/-- m_ν₃ > 0 -/
theorem nu3Mass_pos : 0 < nu3Mass.val := by
  rw [nu3Mass_val]
  apply mul_pos (by norm_num : (0 : ℝ) < 12 / 25)
  apply mul_pos (by norm_num : (0 : ℝ) < 12 / 25)
  exact zpow_pos phi_pos _

/-- m_ν₃ < m_e: neutrinos are lighter than electron -/
theorem nu3_lt_electron : nu3Mass.val < FUST.massGapΔ := by
  rw [nu3Mass_val]
  change (12 : ℝ) / 25 * (12 / 25 * φ ^ (-(32 : ℤ))) < 12 / 25
  have hΔ : (12 : ℝ) / 25 < 1 := by norm_num
  have hΔ_pos : (0 : ℝ) < 12 / 25 := by norm_num
  have hφ32 : φ ^ (-(32 : ℤ)) < 1 :=
    zpow_lt_one_of_neg₀ (by linarith [φ_gt_one]) (by norm_num)
  have hφ32_pos : (0 : ℝ) < φ ^ (-(32 : ℤ)) := zpow_pos phi_pos _
  nlinarith [mul_lt_mul_of_pos_left hΔ hΔ_pos,
             mul_lt_mul_of_pos_left hφ32 hΔ_pos]

/-- Complete neutrino mass chain -/
theorem neutrino_mass_chain :
    (nu3Mass.val / FUST.massGapΔ = (12 : ℝ) / 25 * φ ^ (-(32 : ℤ))) ∧
    (nu2Mass.val / nu3Mass.val = Real.sqrt (1 / 30)) ∧
    (0 < nu3Mass.val) ∧
    (nu3Mass.val < FUST.massGapΔ) :=
  ⟨nu3_electron_ratio, nu2_nu3_ratio, nu3Mass_pos, nu3_lt_electron⟩

end FUST.NeutrinoMass
