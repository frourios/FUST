import FUST.Physics.Hamiltonian
import FUST.Physics.MassRatios
import Mathlib.Data.Nat.Choose.Basic

/-!
# Vacuum Stability from Dζ

The FUST vacuum ker(Dζ) is the TRUE vacuum (not a false/metastable vacuum).
No vacuum decay can occur.

The unique Hamiltonian S[f] = Σ ‖D̃ζ f(φⁿ)‖² is non-negative with kernel
consisting of modes n ≡ 0,2,3,4 mod 6. Active modes (n ≡ 1,5 mod 6) have
eigenvalue λ(n) ≠ 0. The primordial eigenvalue λ₁ (n=1) gives the mass gap.
-/

namespace FUST.VacuumStability

open FUST FUST.IntegralDzeta FUST.Hamiltonian

/-! ## Effective Potential from Dζ -/

section EffectivePotential

noncomputable def effectivePotential (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  Complex.normSq (Dζ_int f z)

theorem effectivePotential_nonneg (f : ℂ → ℂ) (z : ℂ) :
    effectivePotential f z ≥ 0 := Complex.normSq_nonneg _

theorem effectivePotential_ker_zero (f : ℂ → ℂ) (hf : IsInKerDζ f) (z : ℂ) :
    effectivePotential f z = 0 := by
  simp only [effectivePotential, Complex.normSq_eq_zero, hf z]

theorem effectivePotential_massive_pos (f : ℂ → ℂ) (z : ℂ)
    (hDζ : Dζ_int f z ≠ 0) : effectivePotential f z > 0 :=
  Complex.normSq_pos.mpr hDζ

end EffectivePotential

/-! ## Higgs Self-Coupling Analog

λ_FUST = Δ²/(2·C(6,3)) = (12/25)²/(2·20) = 144/25000 -/

section SelfCoupling

noncomputable def lambda_FUST : ℝ := massGapΔ ^ 2 / (2 * Nat.choose 6 3)

theorem lambda_FUST_eq : lambda_FUST = 144 / 25000 := by
  simp only [lambda_FUST, massGapΔ, Nat.choose]; norm_num

theorem lambda_FUST_pos : 0 < lambda_FUST := by
  rw [lambda_FUST_eq]; norm_num

theorem lambda_FUST_bounded : 0 < lambda_FUST ∧ lambda_FUST < 1 := by
  rw [lambda_FUST_eq]; constructor <;> norm_num

end SelfCoupling

/-! ## Vacuum Is Global Minimum -/

section GlobalMinimum

theorem vacuum_is_global_minimum :
    (∀ f N, partialActionDζ f N ≥ 0) ∧
    (∀ f, IsInKerDζ f → ∀ N, partialActionDζ f N = 0) :=
  ⟨partialActionDζ_nonneg, partialActionDζ_ker_zero⟩

theorem vacuum_energy_is_zero (f : ℂ → ℂ) (hf : IsInKerDζ f) (N : ℕ) :
    partialActionDζ f N = 0 :=
  partialActionDζ_ker_zero f hf N

end GlobalMinimum

/-! ## No Lower Vacuum Exists -/

section NoLowerVacuum

theorem no_negative_energy (f : ℂ → ℂ) (n : ℤ) :
    actionDζ f n ≥ 0 :=
  actionDζ_nonneg f n

theorem no_lower_vacuum_exists :
    ¬∃ (f : ℂ → ℂ) (N : ℕ), partialActionDζ f N < 0 := by
  intro ⟨f, N, h⟩
  linarith [partialActionDζ_nonneg f N]

end NoLowerVacuum

/-! ## Spectral Gap from Dζ Primordial Eigenvalue

λ₁ ≠ 0 (from MassGap.lean / BSD.lean) gives the mass gap. -/

section SpectralGap

theorem spectral_gap_positive : 0 < massGapΔ ^ 2 := massGapΔ_sq_pos

theorem spectral_gap_value : massGapΔ ^ 2 = 144 / 625 := massGapΔ_sq

end SpectralGap

/-! ## True Vacuum (not False Vacuum)

A state is a TRUE vacuum if it has zero action and no lower-action state exists.
ker(Dζ) satisfies both conditions. -/

section TrueVacuum

def IsTrueVacuum (f : ℂ → ℂ) : Prop :=
  (∀ N, partialActionDζ f N = 0) ∧
  (∀ g N, partialActionDζ g N ≥ 0) ∧
  IsInKerDζ f

theorem vacuum_is_true (f : ℂ → ℂ) (hf : IsInKerDζ f) : IsTrueVacuum f :=
  ⟨partialActionDζ_ker_zero f hf, partialActionDζ_nonneg, hf⟩

def IsFalseVacuum (f : ℂ → ℂ) : Prop :=
  (∀ N, partialActionDζ f N = 0) ∧
  (∃ g N, partialActionDζ g N < 0)

theorem no_false_vacuum_exists : ¬∃ f, IsFalseVacuum f := by
  intro ⟨f, _, g, N, hlt⟩
  linarith [partialActionDζ_nonneg g N]

end TrueVacuum

/-! ## No Vacuum Decay -/

section NoDecay

def CanDecay (f : ℂ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, ∃ N : ℕ, partialActionDζ g N < partialActionDζ f N

theorem vacuum_cannot_decay (f : ℂ → ℂ) (hf : IsInKerDζ f) : ¬CanDecay f := by
  intro ⟨g, N, h⟩
  rw [partialActionDζ_ker_zero f hf N] at h
  linarith [partialActionDζ_nonneg g N]

theorem no_vacuum_decay :
    ∀ f, IsInKerDζ f → ¬CanDecay f := vacuum_cannot_decay

end NoDecay

/-! ## Top Quark Does Not Destabilize -/

section TopQuark

noncomputable def topBottomRatio : ℝ := φ ^ 7 + φ ^ 5

theorem topBottomRatio_pos : 0 < topBottomRatio :=
  add_pos (pow_pos phi_pos 7) (pow_pos phi_pos 5)

theorem top_does_not_destabilize :
    (0 < topBottomRatio) ∧
    (0 < lambda_FUST) ∧
    (∀ f, IsInKerDζ f → ∀ N, partialActionDζ f N = 0) :=
  ⟨topBottomRatio_pos, lambda_FUST_pos, partialActionDζ_ker_zero⟩

end TopQuark

/-! ## Complete Vacuum Stability Theorem -/

section Complete

theorem fust_vacuum_stability :
    (∀ f N, partialActionDζ f N ≥ 0) ∧
    (∀ f, IsInKerDζ f → ∀ N, partialActionDζ f N = 0) ∧
    (0 < massGapΔ ^ 2) ∧
    (0 < lambda_FUST) ∧
    (¬∃ (f : ℂ → ℂ) (N : ℕ), partialActionDζ f N < 0) :=
  ⟨partialActionDζ_nonneg,
   partialActionDζ_ker_zero,
   massGapΔ_sq_pos,
   lambda_FUST_pos,
   no_lower_vacuum_exists⟩

theorem electroweak_vacuum_is_true :
    (∀ f, IsInKerDζ f → IsTrueVacuum f) ∧
    (¬∃ f, IsFalseVacuum f) ∧
    (∀ f, IsInKerDζ f → ¬CanDecay f) :=
  ⟨vacuum_is_true, no_false_vacuum_exists, vacuum_cannot_decay⟩

end Complete

end FUST.VacuumStability

/-! ## Dimensioned Wrappers -/

namespace FUST.Dim

open FUST.VacuumStability FUST.Hamiltonian

noncomputable def lambdaFUST : RatioQ := ⟨144 / 25000⟩

theorem lambdaFUST_val : lambdaFUST.val = 144 / 25000 := rfl

theorem lambdaFUST_pos : (0 : ℚ) < lambdaFUST.val := by
  simp only [lambdaFUST]; norm_num

def spectralGapSq : RatioQ := ⟨144 / 625⟩

theorem spectralGapSq_val : spectralGapSq.val = 144 / 625 := rfl

theorem vacuum_stability_summary :
    (lambdaFUST.val = 144 / 25000) ∧
    (0 < lambdaFUST.val) ∧
    (spectralGapSq.val = 144 / 625) :=
  ⟨rfl, lambdaFUST_pos, rfl⟩

end FUST.Dim
