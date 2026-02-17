import FUST.Physics.QuarkMassRatios
import FUST.Physics.MassRatioDerivation
import FUST.Physics.MassRatioPredictions
import FUST.Physics.MassGap

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

/-! ## Particle FDim: each particle has a unique dimension

FDim = deriveFDim(6)^a × dimTimeD2^n: the sector exponent a and φ-power n
determine the physical properties. φ^n scaling changes the dimension. -/

def dimElectron : FDim := dimTime⁻¹
def dimMuon : FDim := dimTime⁻¹ * dimTimeD2 ^ (11 : ℤ)
def dimTau : FDim := dimTime⁻¹ * dimTimeD2 ^ (17 : ℤ)
def dimProton : FDim := dimTime⁻¹ * dimTimeD2 ^ (14 : ℤ)
def dimNeutron : FDim := dimProton * deriveFDim 2
def dimWBoson : FDim := dimTime⁻¹ * dimTimeD2 ^ (25 : ℤ)

/-! ## Dimensioned Masses: each with its unique FDim

Each particle has a unique dimension deriveFDim(6)^a × dimTimeD2^n.
The electron (n=0) is the D₆ mass gap Δ = 12/25. -/

/-- Electron mass: m_e = Δ (lightest charged fermion = D₆ mass gap) -/
noncomputable def electronMass : ScaleQ dimElectron := massGapΔ

theorem electronMass_val : electronMass.val = 12 / 25 := rfl

/-- Muon mass: m_μ = Δ × φ¹¹ -/
noncomputable def muonMass : ScaleQ dimMuon :=
  ⟨FUST.massGapΔ * φ ^ (11 : ℤ)⟩

theorem muonMass_val : muonMass.val = 12 / 25 * φ ^ (11 : ℤ) := rfl

/-- Tau mass: m_τ = Δ × φ¹⁷ -/
noncomputable def tauMass : ScaleQ dimTau :=
  ⟨FUST.massGapΔ * φ ^ (17 : ℤ)⟩

theorem tauMass_val : tauMass.val = 12 / 25 * φ ^ (17 : ℤ) := rfl

/-- Proton mass: m_p = Δ × φ¹¹ × C(6,3)×C(4,2)/(C(3,2)+C(5,2)) -/
noncomputable def protonMass : ScaleQ dimProton :=
  ⟨FUST.massGapΔ * φ ^ (11 : ℤ) *
    (Nat.choose 6 3 * Nat.choose 4 2 : ℝ) /
    (Nat.choose 3 2 + Nat.choose 5 2 : ℝ)⟩

theorem protonMass_val :
    protonMass.val = 12 / 25 * φ ^ (11 : ℤ) * 120 / 13 := by
  unfold protonMass FUST.massGapΔ
  simp only [Nat.choose]
  norm_num

/-- Neutron-proton ratio: multiplicative isospin correction.
dim(R) = deriveFDim(2) = (-1,1,1): u↔d swap is a D₂ operation.
R = (C(6,3)·C(4,2)·2·C(6,2)·φ⁹ + F₁₄) / (C(6,3)·C(4,2)·2·C(6,2)·φ⁹)
where F₁₄ = 377 = (C(3,2)+C(5,2))·(2·C(6,2)-C(2,2)) -/
noncomputable def neutronProtonRatio : ScaleQ (deriveFDim 2) :=
  ⟨((Nat.choose 6 3 * Nat.choose 4 2 * (2 * Nat.choose 6 2) : ℝ) * φ ^ 9 +
    (Nat.choose 3 2 + Nat.choose 5 2 : ℝ) * (2 * Nat.choose 6 2 - Nat.choose 2 2)) /
   ((Nat.choose 6 3 * Nat.choose 4 2 * (2 * Nat.choose 6 2) : ℝ) * φ ^ 9)⟩

theorem neutronProtonRatio_val :
    neutronProtonRatio.val = (3600 * φ ^ 9 + 377) / (3600 * φ ^ 9) := by
  simp only [neutronProtonRatio, Nat.choose]; norm_num

-- 377 = F₁₄ = (C(3,2)+C(5,2)) × (2·C(6,2)-C(2,2))
theorem fibonacci_14_decomposition :
    (Nat.choose 3 2 + Nat.choose 5 2) * (2 * Nat.choose 6 2 - Nat.choose 2 2) = 377 := by
  decide

-- 3600 = C(6,3)·C(4,2)·2·C(6,2)
theorem neutron_denom_decomposition :
    Nat.choose 6 3 * Nat.choose 4 2 * (2 * Nat.choose 6 2) = 3600 := by
  decide

/-- Neutron mass: m_n = m_p × R where R is the D₂ isospin correction.
dim(m_n) = dimProton × deriveFDim(2) = dimNeutron. -/
noncomputable def neutronMass : ScaleQ dimNeutron :=
  protonMass * neutronProtonRatio

theorem neutronMass_val :
    neutronMass.val = protonMass.val * neutronProtonRatio.val := rfl

-- R > 1: neutron heavier than proton
theorem neutronProtonRatio_gt_one : neutronProtonRatio.val > 1 := by
  rw [neutronProtonRatio_val]
  rw [gt_iff_lt, lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3600) (pow_pos phi_pos 9))]
  linarith

theorem neutron_gt_proton : neutronMass.val > protonMass.val := by
  rw [neutronMass_val]
  have hp : protonMass.val > 0 := by
    rw [protonMass_val]; apply div_pos
    · apply mul_pos (mul_pos (by norm_num : (0:ℝ) < 12/25) (zpow_pos phi_pos _)); norm_num
    · norm_num
  nlinarith [neutronProtonRatio_gt_one]

-- ℝ projection: m_n·val - m_p·val = m_e·val × φ² × 29/30
private theorem neutronMass_additive :
    neutronMass.val = protonMass.val + electronMass.val * φ ^ 2 * 29 / 30 := by
  simp only [neutronMass_val, neutronProtonRatio_val, protonMass_val, electronMass_val]
  field_simp
  ring

-- Nuclear.lean dependency: ℝ-projected splitting formula
theorem splitting_from_isospin :
    neutronMass.val - protonMass.val =
    electronMass.val * (φ + Nat.choose 2 2) * 29 / 30 := by
  have h : neutronMass.val - protonMass.val = electronMass.val * φ ^ 2 * 29 / 30 := by
    rw [neutronMass_additive]; ring
  rw [h, golden_ratio_property]; simp only [Nat.choose]; ring

-- β-decay: m_n > m_p + m_e
theorem beta_decay_possible :
    neutronMass.val > protonMass.val + electronMass.val := by
  have h := neutronMass_additive
  simp only [electronMass_val] at h ⊢
  rw [h]
  have hφ : φ > 1 := φ_gt_one
  have hφ2_bound : φ ^ 2 > 2 := by rw [golden_ratio_property]; linarith
  nlinarith

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

/-! ## Gauge Boson Masses

W boson: D₆ sector, ScaleQ dimWBoson.
Z boson: DimSum2 with two components from electroweak mixing.
Higgs: DimSum2 with φ vacuum + D₅ correction. -/

/-- W boson mass: m_W = Δ × φ^25 × 15/16. D₆ sector. -/
noncomputable def wBosonMass : ScaleQ dimWBoson :=
  ⟨FUST.massGapΔ * FUST.MassRatioPredictions.WElectronRatio⟩

theorem wBosonMass_val :
    wBosonMass.val = 12 / 25 * (φ ^ 25 * (15 / 16)) := by
  simp only [wBosonMass, FUST.MassRatioPredictions.WElectronRatio_eq, FUST.massGapΔ]

theorem wBoson_electron_ratio :
    wBosonMass.val / electronMass.val =
    φ ^ 25 * (15 / 16) := by
  simp only [wBosonMass_val, electronMass_val]
  field_simp

theorem wBosonMass_pos : 0 < wBosonMass.val := by
  rw [wBosonMass_val]
  apply mul_pos (by norm_num : (0 : ℝ) < 12 / 25)
  apply mul_pos (pow_pos phi_pos _)
  norm_num

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

-- Z boson m² components
def dimZSqComp1 : FDim := dimWBoson * dimWBoson
def dimZSqComp2 : FDim :=
  dimWBoson * dimWBoson * (deriveFDim 2 * deriveFDim 2 * (deriveFDim 3 * deriveFDim 3)⁻¹)

theorem dimZSqComp1_eq : dimZSqComp1 = ⟨40, -48, -52⟩ := by decide
theorem dimZSqComp2_eq : dimZSqComp2 = ⟨42, -46, -52⟩ := by decide

/-- Z boson mass squared as DimSum2: m_Z² = m_W² + m_W² × 3/10.
comp1 dim = dimZSqComp1 = dimWBoson², comp2 dim = dimZSqComp2. -/
noncomputable def zBosonMassSq : DimSum2 dimZSqComp1 dimZSqComp2 :=
  ⟨wBosonMass.sq, ⟨wBosonMass.val ^ 2 * (3 / 10)⟩⟩

theorem zBosonMassSq_eval :
    zBosonMassSq.eval = wBosonMass.val ^ 2 * (13 / 10) := by
  simp [zBosonMassSq, DimSum2.eval, ScaleQ.sq_val]
  ring

theorem zBosonMassSq_dims_ne : dimZSqComp1 ≠ dimZSqComp2 := by decide

-- Higgs components
def dimHiggsVacuum : FDim := dimWBoson * dimTimeD2
def dimHiggsCorrection : FDim := dimWBoson * (dimTimeD2 * dimTimeD2)⁻¹

theorem dimHiggsVacuum_eq : dimHiggsVacuum = ⟨21, -25, -27⟩ := by decide
theorem dimHiggsCorrection_eq : dimHiggsCorrection = ⟨18, -22, -24⟩ := by decide

/-- Higgs mass as DimSum2: m_H = m_W × φ + (-m_W / 10).
eval gives m_W × (φ - 1/10). -/
noncomputable def higgsMass : DimSum2 dimHiggsVacuum dimHiggsCorrection :=
  ⟨⟨wBosonMass.val * φ⟩, ⟨-(wBosonMass.val / 10)⟩⟩

theorem higgsMass_eval :
    higgsMass.eval = wBosonMass.val * (φ - 1 / 10) := by
  simp [higgsMass, DimSum2.eval]
  ring

theorem dimHiggsComp_ne : dimHiggsVacuum ≠ dimHiggsCorrection := by decide

/-- All boson dimension types are pairwise distinct. -/
theorem boson_dims_all_distinct :
    dimWBoson ≠ dimZSqComp1 ∧
    dimWBoson ≠ dimZSqComp2 ∧
    dimWBoson ≠ dimHiggsVacuum ∧
    dimWBoson ≠ dimHiggsCorrection ∧
    dimZSqComp1 ≠ dimHiggsVacuum ∧
    dimZSqComp1 ≠ dimHiggsCorrection ∧
    dimZSqComp2 ≠ dimHiggsVacuum ∧
    dimZSqComp2 ≠ dimHiggsCorrection ∧
    dimHiggsVacuum ≠ dimHiggsCorrection := by decide

/-- W/Z/H mass chain: ℝ projections match experimental ratios. -/
theorem gauge_boson_chain :
    (wBosonMass.val / electronMass.val = φ ^ 25 * (15 / 16)) ∧
    (zBosonMassSq.eval = wBosonMass.val ^ 2 * (13 / 10)) ∧
    (higgsMass.eval = wBosonMass.val * (φ - 1 / 10)) :=
  ⟨wBoson_electron_ratio, zBosonMassSq_eval, higgsMass_eval⟩

end FUST.Dim
