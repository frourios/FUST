import FUST.Physics.TimeStructure

namespace FUST.StateFunctions

open FUST.FζOperator FUST.DζOperator FUST.TimeStructure Complex

/-! ## Structural integers from ℤ[φ,ζ₆] -/

abbrev ζ₆Order : ℕ := 6
abbrev colorRank : ℕ := 3
abbrev kernelModeCount : ℕ := 4
abbrev stencilWidth : ℕ := 5
abbrev galoisOrder : ℕ := 2

/-! ## Massless gauge boson (mode 0)

The most primitive state: constant function f(z) = 1.
Fζ(1) = 0 gives zero eigenvalue → massless.
Photon (U(1), 1 copy) and gluons (SU(3) adjoint, 8 copies) share this state;
their distinction is channel multiplicity, not state function. -/

noncomputable def masslessGaugeState : ℂ → ℂ := fun _ => 1

theorem masslessGauge_kernel : IsInKerFζ masslessGaugeState := by
  intro z; change Fζ (fun _ => 1) z = 0
  have : (fun (_ : ℂ) => (1 : ℂ)) = fun w => w ^ 0 := by ext w; simp
  rw [this]; exact Fζ_vanish_mod6_0 0 z

abbrev photonMultiplicity : ℕ := 1
abbrev gluonMultiplicity : ℕ := colorRank ^ 2 - 1

/-! ## Higgs mechanism: mode 0 → mode 1

timeEvolution preserves the Fζ kernel, so massless gauge bosons cannot
acquire mass by φ-scaling alone. Mass requires coupling to the vacuum
active mode z (mode 1): masslessGaugeState(z) · z = 1 · z = z. -/

theorem masslessGauge_timeEvolution_kernel :
    ∀ k, IsInKerFζ (timeEvolution^[k] masslessGaugeState) := by
  intro k; induction k with
  | zero => simpa using masslessGauge_kernel
  | succ n ih =>
    rw [Function.iterate_succ']
    exact ker_Fζ_invariant _ ih

/-- The vacuum active mode: massless gauge coupled to z -/
noncomputable def electronState : ℂ → ℂ := fun z => masslessGaugeState z * z

theorem electronState_eq : electronState = fun z => z := by
  ext z; simp [electronState, masslessGaugeState]

/-! ## Massive gauge bosons

W, Z, Higgs have mode 1 (active) with mass coefficients from structural
integers. Each is electronState scaled by φ^k × rational correction. -/

/-- W exponent: C(stencilWidth,2) + C(ζ₆Order,2) = 25 -/
abbrev wBosonExponent : ℕ :=
  Nat.choose stencilWidth galoisOrder + Nat.choose ζ₆Order galoisOrder

/-- W degeneracy: C(ζ₆Order,2) = 15 -/
abbrev wBosonDegeneracy : ℕ := Nat.choose ζ₆Order galoisOrder

/-- W constraint: C(ζ₆Order,2) + C(galoisOrder,2) = 16 -/
abbrev wBosonConstraint : ℕ :=
  Nat.choose ζ₆Order galoisOrder + Nat.choose galoisOrder galoisOrder

noncomputable def wBosonMassCoeff : ℝ :=
  φ ^ wBosonExponent * (wBosonDegeneracy / wBosonConstraint : ℝ)

theorem wBosonMassCoeff_eq : wBosonMassCoeff = φ ^ 25 * (15 / 16) := by
  unfold wBosonMassCoeff wBosonExponent wBosonDegeneracy wBosonConstraint
  norm_num [stencilWidth, ζ₆Order, galoisOrder, Nat.choose]

/-- W boson: electronState scaled by wBosonMassCoeff -/
noncomputable def wBosonState : ℂ → ℂ :=
  fun z => (↑wBosonMassCoeff : ℂ) * electronState z

theorem Fζ_wBosonState (z : ℂ) :
    Fζ wBosonState z = (↑wBosonMassCoeff : ℂ) * Fζ electronState z := by
  unfold wBosonState; rw [electronState_eq]
  exact Fζ_const_smul _ _ z

/-- Higgs/W ratio: φ - 1/C(stencilWidth, galoisOrder) = φ - 1/10 -/
noncomputable def higgsWFactor : ℝ :=
  φ - 1 / Nat.choose stencilWidth galoisOrder

theorem higgsWFactor_eq : higgsWFactor = φ - 1 / 10 := by
  unfold higgsWFactor; norm_num [stencilWidth, galoisOrder, Nat.choose]

/-- Higgs: W boson scaled by (φ - 1/10) -/
noncomputable def higgsMassCoeff : ℝ := wBosonMassCoeff * higgsWFactor

noncomputable def higgsState : ℂ → ℂ :=
  fun z => (↑higgsMassCoeff : ℂ) * electronState z

theorem higgsMassCoeff_pos : higgsMassCoeff > 0 := by
  unfold higgsMassCoeff higgsWFactor
  apply mul_pos
  · rw [wBosonMassCoeff_eq]
    exact mul_pos (pow_pos phi_pos _) (by norm_num)
  · have hφ : φ > 1 := φ_gt_one
    have : (1 : ℝ) / Nat.choose stencilWidth galoisOrder < 1 := by
      norm_num [stencilWidth, galoisOrder, Nat.choose]
    linarith

/-- Z boson: W boson / cos θ_W where cos²θ_W = 3/4 from channel weights -/
noncomputable def zBosonMassCoeff : ℝ :=
  wBosonMassCoeff / Real.sqrt (3 / 4)

noncomputable def zBosonState : ℂ → ℂ :=
  fun z => (↑zBosonMassCoeff : ℂ) * electronState z

theorem zBosonMassCoeff_gt_wBosonMassCoeff :
    zBosonMassCoeff > wBosonMassCoeff := by
  unfold zBosonMassCoeff
  have hw : wBosonMassCoeff > 0 := by
    rw [wBosonMassCoeff_eq]
    exact mul_pos (pow_pos phi_pos _) (by norm_num)
  have hsqrt_pos : Real.sqrt (3 / 4) > 0 :=
    Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_lt : Real.sqrt (3 / 4) < 1 := by
    calc Real.sqrt (3 / 4) < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 1 := Real.sqrt_one
  rw [gt_iff_lt, lt_div_iff₀ hsqrt_pos]
  nlinarith

/-! ## Leptons: electronState × timeEvolution^k

The electron IS the Higgs-coupled vacuum mode. Higher generations arise
from timeEvolution^k, with k from Diff operator pair counts. -/

private theorem timeEvolution_iterate_id (k : ℕ) :
    (timeEvolution^[k]) (fun t => t) = fun z => (↑φ : ℂ) ^ k * z := by
  induction k with
  | zero => ext z; simp [Function.iterate_zero]
  | succ n ih =>
    ext z
    rw [Function.iterate_succ', Function.comp_def]
    simp only [timeEvolution, ih]; ring

noncomputable def muonState : ℂ → ℂ := fun z => (↑φ : ℂ) ^ 11 * z

noncomputable def tauState : ℂ → ℂ := fun z => (↑φ : ℂ) ^ 17 * z

theorem muonState_from_timeEvolution :
    muonState = (timeEvolution^[11]) electronState := by
  rw [electronState_eq]; rw [timeEvolution_iterate_id]; ext z; simp [muonState]

theorem tauState_from_timeEvolution :
    tauState = (timeEvolution^[17]) electronState := by
  rw [electronState_eq]; rw [timeEvolution_iterate_id]; ext z; simp [tauState]

noncomputable def positronState : ℂ → ℂ := fun z => z ^ 5

noncomputable def antimuonState : ℂ → ℂ := fun z => (↑φ : ℂ) ^ 11 * z ^ 5

/-! ## Fζ linearity and mass ratios -/

theorem Fζ_muonState (z : ℂ) :
    Fζ muonState z = (↑φ : ℂ) ^ 11 * Fζ electronState z := by
  unfold muonState; rw [electronState_eq]
  exact Fζ_const_smul _ _ z

theorem Fζ_tauState (z : ℂ) :
    Fζ tauState z = (↑φ : ℂ) ^ 17 * Fζ electronState z := by
  unfold tauState; rw [electronState_eq]
  exact Fζ_const_smul _ _ z

private theorem normSq_ofReal_pow (x : ℝ) (n : ℕ) :
    normSq ((↑x : ℂ) ^ n) = x ^ (2 * n) := by
  rw [map_pow, normSq_ofReal]
  rw [show x * x = x ^ 2 from (sq x).symm, ← pow_mul]

theorem muon_electron_massSq_ratio :
    normSq (Fζ muonState 1) = φ ^ 22 * normSq (Fζ electronState 1) := by
  rw [Fζ_muonState, map_mul, normSq_ofReal_pow, show 2 * 11 = 22 from rfl]

theorem tau_electron_massSq_ratio :
    normSq (Fζ tauState 1) = φ ^ 34 * normSq (Fζ electronState 1) := by
  rw [Fζ_tauState, map_mul, normSq_ofReal_pow, show 2 * 17 = 34 from rfl]

/-! ## Electron is lightest: Diff5/Diff6 kernel at mode 1

Mode 1 is the unique active mode in ker(Diff5) ∩ ker(Diff6). -/

theorem Diff5_kernel_at_mode1 :
    φ ^ 2 + φ - 4 + ψ + ψ ^ 2 = 0 := by
  have h := golden_ratio_property
  have hpsi : ψ = 1 - φ := by linarith [phi_add_psi]
  rw [hpsi]; nlinarith

theorem Diff6_kernel_at_mode1 :
    φ ^ 3 - 3 * φ ^ 2 + φ - ψ + 3 * ψ ^ 2 - ψ ^ 3 = 0 := by
  have h := golden_ratio_property
  have hpsi : ψ = 1 - φ := by linarith [phi_add_psi]
  rw [hpsi]; nlinarith

theorem Diff5_nonzero_at_mode5 :
    φ ^ 10 + φ ^ 5 - 4 + ψ ^ 5 + ψ ^ 10 > 0 := by
  have h := golden_ratio_property
  have hpsi : ψ = 1 - φ := by linarith [phi_add_psi]
  have hφ : φ > 1 := φ_gt_one
  rw [hpsi]
  have hφ2 : φ ^ 2 > 2 := by nlinarith
  have hφ4 : φ ^ 4 > 4 := by nlinarith [sq_nonneg (φ ^ 2 - 2)]
  have hφ5 : φ ^ 5 > 5 := by nlinarith
  have hφ10 : φ ^ 10 > 25 := by nlinarith [sq_nonneg (φ ^ 5 - 5)]
  nlinarith [sq_nonneg ((1 - φ) ^ 5)]

/-! ## Quarks: Fζ-kernel modes (confined) -/

noncomputable def upQuarkState : ℂ → ℂ := fun z => z ^ 2

noncomputable def downQuarkState : ℂ → ℂ := fun z => z ^ 3

noncomputable def strangeQuarkState : ℂ → ℂ := fun z => z ^ 4

theorem upQuark_confined : IsInKerFζ upQuarkState := by
  intro z; change Fζ (fun w => w ^ 2) z = 0
  have : (2 : ℕ) = 6 * 0 + 2 := by omega
  rw [this]; exact Fζ_vanish_mod6_2 0 z

theorem downQuark_confined : IsInKerFζ downQuarkState := by
  intro z; change Fζ (fun w => w ^ 3) z = 0
  have : (3 : ℕ) = 6 * 0 + 3 := by omega
  rw [this]; exact Fζ_vanish_mod6_3 0 z

theorem strangeQuark_confined : IsInKerFζ strangeQuarkState := by
  intro z; change Fζ (fun w => w ^ 4) z = 0
  have : (4 : ℕ) = 6 * 0 + 4 := by omega
  rw [this]; exact Fζ_vanish_mod6_4 0 z

/-! ## Neutrinos: seesaw-suppressed

Suppression factor 12/25 = afChannelWeight, exponent 2^5 = 32. -/

abbrev seesawExponent : ℕ := galoisOrder ^ stencilWidth

noncomputable def afChannelWeight : ℝ := Complex.normSq AF_coeff / 5 ^ 2

theorem afChannelWeight_eq : afChannelWeight = 12 / 25 := by
  simp only [afChannelWeight, AF_coeff_normSq]; norm_num

noncomputable def nu3State : ℂ → ℂ :=
  fun z => (↑(afChannelWeight * φ ^ (-(seesawExponent : ℤ))) : ℂ) * z

theorem nu3_coeff_pos : afChannelWeight * φ ^ (-(seesawExponent : ℤ)) > 0 := by
  rw [afChannelWeight_eq]; exact mul_pos (by norm_num) (zpow_pos phi_pos _)

theorem nu3_coeff_lt_one : afChannelWeight * φ ^ (-(seesawExponent : ℤ)) < 1 := by
  rw [afChannelWeight_eq]
  have hΔ : (12 : ℝ) / 25 < 1 := by norm_num
  have hφ32 : φ ^ (-(32 : ℤ)) < 1 :=
    zpow_lt_one_of_neg₀ (by linarith [φ_gt_one]) (by norm_num)
  calc (12 : ℝ) / 25 * φ ^ (-(32 : ℤ))
      < 1 * 1 := by apply mul_lt_mul hΔ (le_of_lt hφ32) (zpow_pos phi_pos _) (by norm_num)
    _ = 1 := one_mul 1

end FUST.StateFunctions
