import FUST.Physics.QuarkMassRatios
import FUST.Physics.MassRatioDerivation
import FUST.Physics.MassRatioPredictions
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

/-! ## Neutrino Mass Squared Ratio as RatioQ -/

def neutrinoMassSqRatio : RatioQ :=
  ⟨1 / (2 * Nat.choose 6 2 : ℚ)⟩

theorem neutrinoMassSqRatio_val :
    neutrinoMassSqRatio.val = 1 / 30 := by
  simp only [neutrinoMassSqRatio, Nat.choose]; norm_num

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

end FUST.Dim
