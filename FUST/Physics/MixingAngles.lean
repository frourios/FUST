import FUST.Physics.PMNSMixingAngles
import FUST.Dimension

namespace FUST.Dim

/-! ## PMNS Mixing Angles

sin²θ₁₂ = 1/3 (RatioQ), sin²θ₁₃ and sin²θ₂₃ involve φ (ScaleQ). -/

def sin2Theta12 : RatioQ := ⟨FUST.PMNSMixingAngles.sin2_theta12⟩

theorem sin2Theta12_val : sin2Theta12.val = 1 / 3 := rfl

noncomputable def sin2Theta13 : ScaleQ 1 :=
  ⟨FUST.PMNSMixingAngles.sin2_theta13_new⟩

theorem sin2Theta13_val : sin2Theta13.val = φ ^ (-8 : ℤ) := rfl

noncomputable def sin2Theta23 : ScaleQ 1 :=
  ⟨FUST.PMNSMixingAngles.sin2_theta23⟩

theorem sin2Theta23_val : sin2Theta23.val = 1 / 2 + φ ^ (-5 : ℤ) / 2 := rfl

/-! ## CKM Scaling as ScaleQ -/

noncomputable def ckmScaling (genDiff : ℕ) : ScaleQ 1 :=
  ⟨FUST.PMNSMixingAngles.ckm_scaling genDiff⟩

theorem ckmScaling_val (n : ℕ) :
    (ckmScaling n).val = φ ^ (-(3 * n : ℤ)) := rfl

theorem ckm_hierarchy :
    (ckmScaling 3).val < (ckmScaling 2).val ∧
    (ckmScaling 2).val < (ckmScaling 1).val :=
  FUST.PMNSMixingAngles.ckm_hierarchy

/-! ## Cosmological Density Parameters as ScaleQ -/

noncomputable def omegaLambda : ScaleQ 1 :=
  ⟨FUST.PMNSMixingAngles.Omega_Lambda_golden⟩

noncomputable def omegaM : ScaleQ 1 :=
  ⟨FUST.PMNSMixingAngles.Omega_m_golden⟩

theorem density_sum : omegaLambda.val + omegaM.val = 1 :=
  FUST.PMNSMixingAngles.density_sum_one

theorem dark_energy_dominates : omegaLambda.val > omegaM.val :=
  FUST.PMNSMixingAngles.dark_energy_dominates

/-! ## Refined Density Parameters -/

noncomputable def omegaLambdaRefined : ScaleQ 1 :=
  ⟨FUST.PMNSMixingAngles.Omega_Lambda_refined⟩

noncomputable def omegaMRefined : ScaleQ 1 :=
  ⟨FUST.PMNSMixingAngles.Omega_m_refined⟩

theorem refined_density_sum : omegaLambdaRefined.val + omegaMRefined.val = 1 :=
  FUST.PMNSMixingAngles.refined_density_sum_one

/-! ## Type Classification Summary -/

theorem mixing_type_hierarchy :
    -- RatioQ: pure rational from symmetry
    (sin2Theta12.val = 1 / 3) ∧
    -- ScaleQ: involves φ (transcendental)
    (sin2Theta13.val = φ ^ (-8 : ℤ)) ∧
    (sin2Theta23.val = 1 / 2 + φ ^ (-5 : ℤ) / 2) :=
  ⟨rfl, rfl, rfl⟩

end FUST.Dim
