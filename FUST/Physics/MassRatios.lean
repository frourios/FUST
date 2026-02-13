import FUST.Physics.QuarkMassRatios
import FUST.Physics.MassRatioDerivation
import FUST.Physics.MassRatioPredictions
import FUST.Physics.MassGap
import FUST.DimensionalAnalysis

namespace FUST.Dim

/-! ## Mass Ratio Exponents as CountQ

Mass ratios are φ^n where n comes from D-structure pair counts.
The exponents n are CountQ (structure-derived integers). -/

def msMdExponent : CountQ := ⟨FUST.QuarkMassRatios.triangular 3⟩
def mcMsValue : CountQ :=
  ⟨FUST.QuarkMassRatios.mc_ms_D5_component +
   FUST.QuarkMassRatios.mc_ms_isospin_component⟩
def mbMcValue : CountQ := ⟨Nat.choose 3 2⟩
def mtMbExpHigh : CountQ := ⟨FUST.QuarkMassRatios.mt_mb_exp_high⟩
def mtMbExpLow : CountQ := ⟨FUST.QuarkMassRatios.mt_mb_exp_low⟩

theorem msMdExponent_val : msMdExponent.val = 6 := rfl
theorem mcMsValue_val : mcMsValue.val = 12 := rfl
theorem mbMcValue_val : mbMcValue.val = 3 := rfl
theorem mtMbExpHigh_val : mtMbExpHigh.val = 7 := rfl
theorem mtMbExpLow_val : mtMbExpLow.val = 5 := rfl

/-! ## Mass Ratios as ScaleQ 1 (dimensionless ratios of masses) -/

noncomputable def msMdRatio : ScaleQ 1 :=
  ⟨FUST.QuarkMassRatios.ms_md_structural⟩

theorem msMdRatio_val : msMdRatio.val = φ ^ 6 := rfl

noncomputable def mtMbRatio : ScaleQ 1 :=
  ⟨FUST.QuarkMassRatios.mt_mb_structural⟩

theorem mtMbRatio_val : mtMbRatio.val = φ ^ 7 + φ ^ 5 := rfl

/-! ## Up/Down Ratio as RatioQ -/

def muMdRatio : RatioQ :=
  ⟨(Nat.choose 2 2 : ℚ) / 2⟩

theorem muMdRatio_val : muMdRatio.val = 1 / 2 := by
  simp only [muMdRatio, Nat.choose]; norm_num

/-! ## Mass Ratio Correction Exponents as CountQ -/

def tauMuExponent : CountQ :=
  ⟨FUST.MassRatioDerivation.triangular 3⟩
def muEExponent : CountQ :=
  ⟨(FUST.MassRatioDerivation.massExponent 4 3).toNat⟩

theorem tauMuExponent_val : tauMuExponent.val = 6 := rfl
theorem muEExponent_val : muEExponent.val = 11 := by decide

/-! ## Dark Matter Exponent as CountQ -/

def darkMatterExponent : CountQ := ⟨FUST.MassRatioPredictions.darkMatterExponent⟩

theorem darkMatterExponent_val : darkMatterExponent.val = 25 := rfl

theorem darkMatterExponent_from_pairs :
    darkMatterExponent.val = Nat.choose 5 2 + Nat.choose 6 2 := rfl

/-! ## Baryon Asymmetry Exponent as CountQ -/

def baryonExponent : CountQ := ⟨FUST.MassRatioPredictions.baryonExponent⟩

theorem baryonExponent_val : baryonExponent.val = 44 := rfl

/-! ## Higgs/W Ratio as ScaleQ (involves φ) -/

noncomputable def higgsWRatio : ScaleQ 1 :=
  ⟨FUST.MassRatioPredictions.higgsWRatio⟩

/-! ## Exponent consistency -/

theorem exponent_sum : tauMuExponent.val + muEExponent.val = 17 := rfl

theorem all_exponents_from_pair_counts :
    (msMdExponent.val = Nat.choose 4 2) ∧
    (mbMcValue.val = Nat.choose 3 2) ∧
    (mtMbExpHigh.val = Nat.choose 4 2 + Nat.choose 2 2) ∧
    (mtMbExpLow.val = Nat.choose 4 2 - Nat.choose 2 2) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## Dimensioned Masses: ScaleQ dimTime⁻¹

Mass in FUST has dimension dimTime⁻¹ = (-5, 1, -1), the D₆ output dimension.
The electron, as the lightest charged fermion, is identified with the mass gap
Δ = C₃/(√5)⁵ = 12/25. Neutrinos acquire mass via a different mechanism
(D₅ mixing perturbation from ker(D₆)) and are not bounded by Δ. -/

/-- Electron mass: m_e = Δ (lightest charged fermion = D₆ mass gap) -/
noncomputable def electronMass : ScaleQ dimTime⁻¹ := massGapΔ

theorem electronMass_val : electronMass.val = 12 / 25 := rfl

/-- Muon mass: m_μ = Δ × φ¹¹ -/
noncomputable def muonMass : ScaleQ dimTime⁻¹ :=
  ⟨FUST.massGapΔ * φ ^ (11 : ℤ)⟩

theorem muonMass_val : muonMass.val = 12 / 25 * φ ^ (11 : ℤ) := rfl

/-- Tau mass: m_τ = Δ × φ¹⁷ -/
noncomputable def tauMass : ScaleQ dimTime⁻¹ :=
  ⟨FUST.massGapΔ * φ ^ (17 : ℤ)⟩

theorem tauMass_val : tauMass.val = 12 / 25 * φ ^ (17 : ℤ) := rfl

/-- Proton mass: m_p = Δ × φ¹¹ × C(6,3)×C(4,2)/(C(3,2)+C(5,2)) -/
noncomputable def protonMass : ScaleQ dimTime⁻¹ :=
  ⟨FUST.massGapΔ * φ ^ (11 : ℤ) *
    (Nat.choose 6 3 * Nat.choose 4 2 : ℝ) /
    (Nat.choose 3 2 + Nat.choose 5 2 : ℝ)⟩

theorem protonMass_val :
    protonMass.val = 12 / 25 * φ ^ (11 : ℤ) * 120 / 13 := by
  unfold protonMass FUST.massGapΔ
  simp only [Nat.choose]
  norm_num

/-- m_e = Δ: lightest charged fermion is the D₆ mass gap -/
theorem electronMass_eq_massGap : electronMass = massGapΔ := rfl

/-- m_p / m_e = φ¹¹ × 120/13 -/
theorem protonElectronRatio_from_masses :
    protonMass.val / electronMass.val = φ ^ (11 : ℤ) * 120 / 13 := by
  simp only [protonMass_val, electronMass_val]
  field_simp

/-- Lepton mass ratios from dimensioned masses -/
theorem muon_electron_ratio_from_masses :
    muonMass.val / electronMass.val = φ ^ (11 : ℤ) := by
  simp only [muonMass_val, electronMass_val]
  field_simp

theorem tau_muon_ratio_from_masses :
    tauMass.val / muonMass.val = φ ^ (6 : ℤ) := by
  simp only [tauMass_val, muonMass_val]
  have hΔ : (12 : ℝ) / 25 ≠ 0 := by norm_num
  have hφ11 : φ ^ (11 : ℤ) ≠ 0 := zpow_ne_zero 11 (by linarith [φ_gt_one])
  field_simp

/-! ## Gauge Boson Masses: ScaleQ dimTime⁻¹

W/Z/Higgs masses derived from electron mass and D-structure pair counts.
m_W = m_e × φ^(C(5,2)+C(6,2)) × C(6,2)/(C(6,2)+C(2,2))
m_Z = m_W / cos(θ_W)  where sin²θ_W = C(3,2)/(C(3,2)+C(5,2))
m_H = m_W × (φ - 1/C(5,2))
-/

/-- W boson mass: m_W = Δ × φ^25 × 15/16 -/
noncomputable def wBosonMass : ScaleQ dimTime⁻¹ :=
  ⟨FUST.massGapΔ * FUST.MassRatioPredictions.WElectronRatio⟩

theorem wBosonMass_val :
    wBosonMass.val = 12 / 25 * (φ ^ 25 * (15 / 16)) := by
  simp only [wBosonMass, FUST.MassRatioPredictions.WElectronRatio_eq, FUST.massGapΔ]

/-- m_W / m_e = φ^25 × 15/16 -/
theorem wBoson_electron_ratio :
    wBosonMass.val / electronMass.val =
    φ ^ 25 * (15 / 16) := by
  simp only [wBosonMass_val, electronMass_val]
  field_simp

/-- Z boson mass: m_Z = m_W / √(10/13) -/
noncomputable def zBosonMass : ScaleQ dimTime⁻¹ :=
  ⟨wBosonMass.val / Real.sqrt ((Nat.choose 5 2 : ℝ) / (Nat.choose 3 2 + Nat.choose 5 2))⟩

theorem zBosonMass_val :
    zBosonMass.val = wBosonMass.val / Real.sqrt (10 / 13) := by
  simp only [zBosonMass, Nat.choose]; norm_num

/-- Higgs mass: m_H = m_W × (φ - 1/10) -/
noncomputable def higgsMass : ScaleQ dimTime⁻¹ :=
  ⟨wBosonMass.val * FUST.MassRatioPredictions.higgsWRatio⟩

theorem higgsMass_val :
    higgsMass.val = wBosonMass.val * (φ - 1 / 10) := by
  simp only [higgsMass, FUST.MassRatioPredictions.higgsWRatio_structure]

/-- W mass is positive -/
theorem wBosonMass_pos : 0 < wBosonMass.val := by
  rw [wBosonMass_val]
  apply mul_pos (by norm_num : (0 : ℝ) < 12 / 25)
  apply mul_pos (pow_pos phi_pos _)
  norm_num

/-- W > electron (massive gauge boson) -/
theorem wBoson_gt_electron : wBosonMass.val > electronMass.val := by
  rw [wBosonMass_val, electronMass_val]
  have hφ : φ > 1 := φ_gt_one
  have hφ2 : φ ^ 2 > 2 := by rw [golden_ratio_property]; linarith
  have h21 : φ ^ 21 > 1 := one_lt_pow₀ (by linarith : 1 < φ) (by norm_num)
  have hφ4 : φ ^ 4 > 4 := by nlinarith [sq_nonneg (φ ^ 2 - 2)]
  have hφ25 : φ ^ 25 > 4 := by
    have : φ ^ 25 = φ ^ 4 * φ ^ 21 := by ring
    nlinarith
  nlinarith

/-- Complete gauge boson mass chain from D-structure -/
theorem gauge_boson_chain :
    (wBosonMass.val / electronMass.val = φ ^ 25 * (15 / 16)) ∧
    (zBosonMass.val = wBosonMass.val / Real.sqrt (10 / 13)) ∧
    (higgsMass.val = wBosonMass.val * (φ - 1 / 10)) :=
  ⟨wBoson_electron_ratio, zBosonMass_val, higgsMass_val⟩

end FUST.Dim
