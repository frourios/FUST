import FUST.Physics.MassGap
import FUST.Physics.WeinbergAngle
import FUST.DimensionalAnalysis

/-!
# Neutrino Mass Structure from Fζ Channel Dimensions

All neutrino mass predictions from Fζ structure:
- 3 flavors from syWeight = 3
- Mass hierarchy from spinDegeneracy = 2 (SU(2) doublet)
- Δm²₂₁/Δm²₃₁ = 1/30 from spinDegeneracy × C(6,2)
- m_ν₃/m_e = Δ × φ^(-32) where 32 = spinDegeneracy^5
-/

namespace FUST.NeutrinoMass

open FUST.Dim FUST.WeinbergAngle

/-! ## Part 1: Neutrino Mass Squared Ratio

Δm²₂₁/Δm²₃₁ = 1/(spinDegeneracy × C(6,2)) = 1/30
where spinDegeneracy = 2 (SU(2) doublet) and C(6,2) = 15. -/

/-- Neutrino mass squared denominator: spinDegeneracy × C(6,2) = 2 × 15 = 30 -/
abbrev neutrinoMassSqDenom : ℕ := spinDegeneracy * Nat.choose 6 2

theorem neutrinoMassSqDenom_eq : neutrinoMassSqDenom = 30 := rfl

/-- Structural decomposition: 30 = spinDegeneracy × C(6,2) -/
theorem neutrinoMassSqDenom_structural :
    neutrinoMassSqDenom = spinDegeneracy * Nat.choose 6 2 ∧
    spinDegeneracy = 2 ∧ Nat.choose 6 2 = 15 := ⟨rfl, rfl, rfl⟩

/-- Neutrino mass squared ratio: Δm²₂₁/Δm²₃₁ = 1/30 -/
noncomputable abbrev neutrinoMassSqRatio : ℚ := 1 / neutrinoMassSqDenom

theorem neutrinoMassSqRatio_eq : neutrinoMassSqRatio = 1 / 30 := rfl

/-- Neutrino mass ratio m₂/m₃ = √(1/30) -/
noncomputable abbrev neutrinoMassRatio : ℝ := Real.sqrt (1 / 30)

/-! ## Part 2: Absolute Mass Scale

m_ν₃/m_e = Δ × φ^(-32) where:
- Δ = 12/25 (mass gap)
- 32 = 2⁵ = spinDegeneracy^5

The neutrino mass acquires a Δ suppression factor (seesaw-like). -/

/-- Neutrino mass suppression exponent: 2⁵ = spinDegeneracy^5 -/
abbrev neutrinoMassExponent : ℕ := spinDegeneracy ^ 5

theorem neutrinoMassExponent_eq : neutrinoMassExponent = 32 := rfl

theorem neutrinoMassExponent_structural :
    neutrinoMassExponent = spinDegeneracy ^ 5 ∧
    spinDegeneracy = 2 := ⟨rfl, rfl⟩

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
  unfold nu3ElectronRatio neutrinoMassExponent spinDegeneracy afWeight
  apply mul_pos (by norm_num : (0 : ℝ) < 12 / 25)
  exact zpow_pos phi_pos _

/-! ## Part 3: Dimensioned Neutrino Masses

Neutrinos have unique FDim in the D₆² sector:
m_ν₃ = Δ² × φ^(-32), m_ν₂ = m_ν₃ × √(1/30). -/

-- Neutrino FDim: D₆² sector
def dimNu3 : FDim := dimLagrangian * dimTimeD2 ^ (-(32 : ℤ))
def dimNu2 : FDim := dimNu3 * deriveFDim 2

/-- Neutrino mass squared ratio as RatioQ -/
def neutrinoMassSqRatio_dimQ : RatioQ :=
  ⟨1 / (spinDegeneracy * Nat.choose 6 2 : ℚ)⟩

theorem neutrinoMassSqRatio_dimQ_val :
    neutrinoMassSqRatio_dimQ.val = 1 / 30 := by
  simp only [neutrinoMassSqRatio_dimQ, spinDegeneracy, afWeight, Nat.choose]; norm_num

/-- m_ν₃ = Δ × Δ × φ^(-32) = Δ² × φ^(-2⁵) -/
noncomputable def nu3Mass : ScaleQ dimNu3 :=
  ⟨FUST.massScale * nu3ElectronRatio⟩

theorem nu3Mass_val :
    nu3Mass.val = (12 / 25) * ((12 : ℝ) / 25 * φ ^ (-(32 : ℤ))) := by
  simp only [nu3Mass, nu3ElectronRatio_eq, FUST.massScale_eq]

/-- m_ν₃ / m_e = Δ × φ^(-32) (where m_e = Δ = massScale) -/
theorem nu3_electron_ratio :
    nu3Mass.val / FUST.massScale =
    (12 : ℝ) / 25 * φ ^ (-(32 : ℤ)) := by
  simp only [nu3Mass_val, FUST.massScale_eq]
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
theorem nu3_lt_electron : nu3Mass.val < FUST.massScale := by
  rw [nu3Mass_val, FUST.massScale_eq]
  have hΔ : (12 : ℝ) / 25 < 1 := by norm_num
  have hΔ_pos : (0 : ℝ) < 12 / 25 := by norm_num
  have hφ32 : φ ^ (-(32 : ℤ)) < 1 :=
    zpow_lt_one_of_neg₀ (by linarith [φ_gt_one]) (by norm_num)
  have hφ32_pos : (0 : ℝ) < φ ^ (-(32 : ℤ)) := zpow_pos phi_pos _
  nlinarith [mul_lt_mul_of_pos_left hΔ hΔ_pos,
             mul_lt_mul_of_pos_left hφ32 hΔ_pos]

/-- Complete neutrino mass chain -/
theorem neutrino_mass_chain :
    (nu3Mass.val / FUST.massScale = (12 : ℝ) / 25 * φ ^ (-(32 : ℤ))) ∧
    (nu2Mass.val / nu3Mass.val = Real.sqrt (1 / 30)) ∧
    (0 < nu3Mass.val) ∧
    (nu3Mass.val < FUST.massScale) :=
  ⟨nu3_electron_ratio, nu2_nu3_ratio, nu3Mass_pos, nu3_lt_electron⟩

end FUST.NeutrinoMass
