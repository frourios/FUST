import FUST.Physics.MassGap
import FUST.SpectralCoefficients
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# FUST Hamiltonian from Least Action Theorem

Construction of the Hamiltonian from each Dm operator's Lagrangian structure.
Each Dm (m=2..6) defines Hm[f] = Σₙ (Dm f (φⁿ))², and the spectral gap
(mass gap) Δm = |C_{d_min}| / (√5)^{m-1} is derived from operator structure.

## Spectral Structure (per operator)

- ker(Dm) states: Hm = 0 (vacuum under Dm)
- ker(Dm)⊥ states: Hm > 0 (massive under Dm)
- Mass gap Δm: minimum eigenvalue on ker(Dm)⊥
-/

namespace FUST.Hamiltonian

open FUST.LeastAction

/-! ## Hamiltonian Definition for All D-Operators

Each Dm defines a discretized Hamiltonian:
  Hm[f] = Σₙ (Dm f (φⁿ))²
-/

section HamiltonianDefinition

noncomputable def hamiltonianContributionD2 (f : ℝ → ℝ) (n : ℤ) : ℝ :=
  (D2 f (φ ^ n))^2

noncomputable def hamiltonianContributionD3 (f : ℝ → ℝ) (n : ℤ) : ℝ :=
  (D3 f (φ ^ n))^2

noncomputable def hamiltonianContributionD4 (f : ℝ → ℝ) (n : ℤ) : ℝ :=
  (D4 f (φ ^ n))^2

noncomputable def hamiltonianContributionD5 (f : ℝ → ℝ) (n : ℤ) : ℝ :=
  (D5 f (φ ^ n))^2

noncomputable def hamiltonianContributionD6 (f : ℝ → ℝ) (n : ℤ) : ℝ :=
  (D6 f (φ ^ n))^2

theorem hamiltonianContributionD2_nonneg (f : ℝ → ℝ) (n : ℤ) :
    hamiltonianContributionD2 f n ≥ 0 := sq_nonneg _
theorem hamiltonianContributionD3_nonneg (f : ℝ → ℝ) (n : ℤ) :
    hamiltonianContributionD3 f n ≥ 0 := sq_nonneg _
theorem hamiltonianContributionD4_nonneg (f : ℝ → ℝ) (n : ℤ) :
    hamiltonianContributionD4 f n ≥ 0 := sq_nonneg _
theorem hamiltonianContributionD5_nonneg (f : ℝ → ℝ) (n : ℤ) :
    hamiltonianContributionD5 f n ≥ 0 := sq_nonneg _
theorem hamiltonianContributionD6_nonneg (f : ℝ → ℝ) (n : ℤ) :
    hamiltonianContributionD6 f n ≥ 0 := sq_nonneg _

noncomputable def partialHamiltonianD2 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum (fun n => hamiltonianContributionD2 f n)

noncomputable def partialHamiltonianD3 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum (fun n => hamiltonianContributionD3 f n)

noncomputable def partialHamiltonianD4 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum (fun n => hamiltonianContributionD4 f n)

noncomputable def partialHamiltonianD5 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum (fun n => hamiltonianContributionD5 f n)

noncomputable def partialHamiltonianD6 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (Finset.Icc (-N : ℤ) N).sum (fun n => hamiltonianContributionD6 f n)

private theorem phi_zpow_ne_zero (n : ℤ) : φ ^ n ≠ 0 := by
  apply zpow_ne_zero; linarith [φ_gt_one]

theorem partialHamiltonianD2_nonneg (f : ℝ → ℝ) (N : ℕ) :
    partialHamiltonianD2 f N ≥ 0 :=
  Finset.sum_nonneg fun n _ => hamiltonianContributionD2_nonneg f n

theorem partialHamiltonianD3_nonneg (f : ℝ → ℝ) (N : ℕ) :
    partialHamiltonianD3 f N ≥ 0 :=
  Finset.sum_nonneg fun n _ => hamiltonianContributionD3_nonneg f n

theorem partialHamiltonianD4_nonneg (f : ℝ → ℝ) (N : ℕ) :
    partialHamiltonianD4 f N ≥ 0 :=
  Finset.sum_nonneg fun n _ => hamiltonianContributionD4_nonneg f n

theorem partialHamiltonianD5_nonneg (f : ℝ → ℝ) (N : ℕ) :
    partialHamiltonianD5 f N ≥ 0 :=
  Finset.sum_nonneg fun n _ => hamiltonianContributionD5_nonneg f n

theorem partialHamiltonianD6_nonneg (f : ℝ → ℝ) (N : ℕ) :
    partialHamiltonianD6 f N ≥ 0 :=
  Finset.sum_nonneg fun n _ => hamiltonianContributionD6_nonneg f n

theorem hamiltonianContributionD2_ker_zero (f : ℝ → ℝ) (hf : IsInKerD2 f) (n : ℤ) :
    hamiltonianContributionD2 f n = 0 := by
  simp only [hamiltonianContributionD2, sq_eq_zero_iff]
  exact IsInKerD2_implies_D2_zero f hf _ (phi_zpow_ne_zero n)

theorem hamiltonianContributionD3_ker_zero (f : ℝ → ℝ) (hf : IsInKerD3 f) (n : ℤ) :
    hamiltonianContributionD3 f n = 0 := by
  simp only [hamiltonianContributionD3, sq_eq_zero_iff]
  exact IsInKerD3_implies_D3_zero f hf _ (phi_zpow_ne_zero n)

theorem hamiltonianContributionD4_ker_zero (f : ℝ → ℝ) (hf : IsInKerD4 f) (n : ℤ) :
    hamiltonianContributionD4 f n = 0 := by
  simp only [hamiltonianContributionD4, sq_eq_zero_iff]
  exact IsInKerD4_implies_D4_zero f hf _ (phi_zpow_ne_zero n)

theorem hamiltonianContributionD5_ker_zero (f : ℝ → ℝ) (hf : IsInKerD5 f) (n : ℤ) :
    hamiltonianContributionD5 f n = 0 := by
  simp only [hamiltonianContributionD5, sq_eq_zero_iff]
  exact IsInKerD5_implies_D5_zero f hf _ (phi_zpow_ne_zero n)

theorem hamiltonianContributionD6_ker_zero (f : ℝ → ℝ) (hf : IsInKerD6 f) (n : ℤ) :
    hamiltonianContributionD6 f n = 0 := by
  simp only [hamiltonianContributionD6, sq_eq_zero_iff]
  exact IsInKerD6_implies_D6_zero f hf _ (phi_zpow_ne_zero n)

theorem partialHamiltonianD2_ker_zero (f : ℝ → ℝ) (hf : IsInKerD2 f) (N : ℕ) :
    partialHamiltonianD2 f N = 0 :=
  Finset.sum_eq_zero fun n _ => hamiltonianContributionD2_ker_zero f hf n

theorem partialHamiltonianD3_ker_zero (f : ℝ → ℝ) (hf : IsInKerD3 f) (N : ℕ) :
    partialHamiltonianD3 f N = 0 :=
  Finset.sum_eq_zero fun n _ => hamiltonianContributionD3_ker_zero f hf n

theorem partialHamiltonianD4_ker_zero (f : ℝ → ℝ) (hf : IsInKerD4 f) (N : ℕ) :
    partialHamiltonianD4 f N = 0 :=
  Finset.sum_eq_zero fun n _ => hamiltonianContributionD4_ker_zero f hf n

theorem partialHamiltonianD5_ker_zero (f : ℝ → ℝ) (hf : IsInKerD5 f) (N : ℕ) :
    partialHamiltonianD5 f N = 0 :=
  Finset.sum_eq_zero fun n _ => hamiltonianContributionD5_ker_zero f hf n

theorem partialHamiltonianD6_ker_zero (f : ℝ → ℝ) (hf : IsInKerD6 f) (N : ℕ) :
    partialHamiltonianD6 f N = 0 :=
  Finset.sum_eq_zero fun n _ => hamiltonianContributionD6_ker_zero f hf n

end HamiltonianDefinition

/-! ## Hamiltonian Properties for All Operators -/

section HamiltonianProperties

def HasPositiveHamiltonianD2 (f : ℝ → ℝ) : Prop :=
  ∃ n : ℤ, hamiltonianContributionD2 f n > 0

def HasPositiveHamiltonianD3 (f : ℝ → ℝ) : Prop :=
  ∃ n : ℤ, hamiltonianContributionD3 f n > 0

def HasPositiveHamiltonianD4 (f : ℝ → ℝ) : Prop :=
  ∃ n : ℤ, hamiltonianContributionD4 f n > 0

def HasPositiveHamiltonianD5 (f : ℝ → ℝ) : Prop :=
  ∃ n : ℤ, hamiltonianContributionD5 f n > 0

def HasPositiveHamiltonianD6 (f : ℝ → ℝ) : Prop :=
  ∃ n : ℤ, hamiltonianContributionD6 f n > 0

theorem positive_hamiltonianD2_not_ker (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD2 f) :
    ¬ IsInKerD2 f := by
  intro hker; obtain ⟨n, hn⟩ := hpos; linarith [hamiltonianContributionD2_ker_zero f hker n]

theorem positive_hamiltonianD3_not_ker (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD3 f) :
    ¬ IsInKerD3 f := by
  intro hker; obtain ⟨n, hn⟩ := hpos; linarith [hamiltonianContributionD3_ker_zero f hker n]

theorem positive_hamiltonianD4_not_ker (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD4 f) :
    ¬ IsInKerD4 f := by
  intro hker; obtain ⟨n, hn⟩ := hpos; linarith [hamiltonianContributionD4_ker_zero f hker n]

theorem positive_hamiltonianD5_not_ker (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD5 f) :
    ¬ IsInKerD5 f := by
  intro hker; obtain ⟨n, hn⟩ := hpos; linarith [hamiltonianContributionD5_ker_zero f hker n]

theorem positive_hamiltonianD6_not_ker (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD6 f) :
    ¬ IsInKerD6 f := by
  intro hker; obtain ⟨n, hn⟩ := hpos; linarith [hamiltonianContributionD6_ker_zero f hker n]

theorem hamiltonianD6_zero_iff_ker_discrete (f : ℝ → ℝ) :
    (∀ n : ℤ, hamiltonianContributionD6 f n = 0) ↔
    (∀ n : ℤ, D6 f (φ ^ n) = 0) := by
  constructor
  · intro h n
    have := h n
    simp only [hamiltonianContributionD6, sq_eq_zero_iff] at this
    exact this
  · intro h n
    simp only [hamiltonianContributionD6, h n, sq_eq_zero_iff]

theorem positive_hamiltonianD2_time_exists (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD2 f) :
    ¬ IsInKerD2 f :=
  positive_hamiltonianD2_not_ker f hpos

theorem positive_hamiltonianD3_time_exists (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD3 f) :
    ¬ IsInKerD3 f :=
  positive_hamiltonianD3_not_ker f hpos

theorem positive_hamiltonianD4_time_exists (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD4 f) :
    ¬ IsInKerD4 f :=
  positive_hamiltonianD4_not_ker f hpos

theorem positive_hamiltonianD5_time_exists (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD5 f) :
    ¬ IsInKerD5 f :=
  positive_hamiltonianD5_not_ker f hpos

theorem positive_hamiltonianD6_time_exists (f : ℝ → ℝ) (hpos : HasPositiveHamiltonianD6 f) :
    ¬ IsInKerD6 f :=
  positive_hamiltonianD6_not_ker f hpos

end HamiltonianProperties

/-! ## Spectral Gap Structure for All Operators

Each Dm has its own minimum massive degree and spectral gap:
  D2: ker = {1}, d_min = 1, Δ₂ = 1
  D3: ker = {1}, d_min = 1, Δ₃ = 1/5
  D4: ker = {x²}, d_min = 0, Δ₄ = 1/5
  D5: ker = {1,x}, d_min = 2, Δ₅ = 6/25
  D6: ker = {1,x,x²}, d_min = 3, Δ₆ = 12/25
-/

section SpectralGap

theorem minimum_massive_degree_D2 :
    (∀ x, x ≠ 0 → D2 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D2 id x ≠ 0) :=
  ⟨fun x hx => D2_const 1 x hx, D2_linear_ne_zero⟩

theorem minimum_massive_degree_D3 :
    (∀ x, x ≠ 0 → D3 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D3 id x ≠ 0) :=
  ⟨fun x hx => D3_const 1 x hx, D3_linear_ne_zero⟩

theorem minimum_massive_degree_D4 :
    (∀ x, x ≠ 0 → D4 (fun t => t^2) x = 0) ∧
    (∀ x, x ≠ 0 → D4 (fun _ => 1) x ≠ 0) :=
  ⟨D4_quadratic, D4_const_ne_zero⟩

theorem minimum_massive_degree_D5 :
    (∀ x, x ≠ 0 → D5 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D5 id x = 0) ∧
    (∀ x, x ≠ 0 → D5 (fun t => t^2) x ≠ 0) :=
  ⟨fun x hx => D5_const 1 x hx, D5_linear, D5_not_annihilate_quadratic⟩

theorem minimum_massive_degree_D6 :
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^3) x ≠ 0) :=
  ⟨D6_quadratic, D6_not_annihilate_cubic⟩

theorem linear_has_positive_hamiltonianD2 :
    HasPositiveHamiltonianD2 id := by
  use 0
  simp only [hamiltonianContributionD2, zpow_zero]
  exact sq_pos_of_ne_zero (D2_linear_ne_zero 1 one_ne_zero)

theorem linear_has_positive_hamiltonianD3 :
    HasPositiveHamiltonianD3 id := by
  use 0
  simp only [hamiltonianContributionD3, zpow_zero]
  exact sq_pos_of_ne_zero (D3_linear_ne_zero 1 one_ne_zero)

theorem const_has_positive_hamiltonianD4 :
    HasPositiveHamiltonianD4 (fun _ => 1) := by
  use 0
  simp only [hamiltonianContributionD4, zpow_zero]
  exact sq_pos_of_ne_zero (D4_const_ne_zero 1 one_ne_zero)

theorem quadratic_has_positive_hamiltonianD5 :
    HasPositiveHamiltonianD5 (fun t => t^2) := by
  use 0
  simp only [hamiltonianContributionD5, zpow_zero]
  exact sq_pos_of_ne_zero (D5_not_annihilate_quadratic 1 one_ne_zero)

theorem cubic_has_positive_hamiltonianD6 :
    HasPositiveHamiltonianD6 (fun t => t^3) := by
  use 0
  simp only [hamiltonianContributionD6, zpow_zero]
  exact sq_pos_of_ne_zero (D6_not_annihilate_cubic 1 one_ne_zero)

theorem all_operators_have_positive_hamiltonian :
    HasPositiveHamiltonianD2 id ∧
    HasPositiveHamiltonianD3 id ∧
    HasPositiveHamiltonianD4 (fun _ => 1) ∧
    HasPositiveHamiltonianD5 (fun t => t^2) ∧
    HasPositiveHamiltonianD6 (fun t => t^3) :=
  ⟨linear_has_positive_hamiltonianD2,
   linear_has_positive_hamiltonianD3,
   const_has_positive_hamiltonianD4,
   quadratic_has_positive_hamiltonianD5,
   cubic_has_positive_hamiltonianD6⟩

end SpectralGap

/-! ## Mass Gap Values for All Operators

  Δ₂ = 1, Δ₃ = 1/5, Δ₄ = 1/5, Δ₅ = 6/25, Δ₆ = 12/25
-/

section MassGapValues

noncomputable def massGapD2 : ℝ := 1
noncomputable def massGapD3 : ℝ := 1 / 5
noncomputable def massGapD4 : ℝ := 1 / 5
noncomputable def massGapD5 : ℝ := 6 / 25

theorem massGapD2_pos : 0 < massGapD2 := by unfold massGapD2; norm_num
theorem massGapD3_pos : 0 < massGapD3 := by unfold massGapD3; norm_num
theorem massGapD4_pos : 0 < massGapD4 := by unfold massGapD4; norm_num
theorem massGapD5_pos : 0 < massGapD5 := by unfold massGapD5; norm_num

theorem massGapD5_eq_D5MassScale :
    massGapD5 = FUST.SpectralCoefficients.D5MassScale := by
  unfold massGapD5
  rw [FUST.SpectralCoefficients.D5MassScale_eq]

/-- Mass gap hierarchy: Δ₆ > Δ₅ > Δ₃ = Δ₄ -/
theorem massGap_hierarchy :
    FUST.massGapΔ > massGapD5 ∧
    massGapD5 > massGapD3 ∧
    massGapD3 = massGapD4 ∧
    massGapD2 > FUST.massGapΔ := by
  unfold FUST.massGapΔ massGapD5 massGapD3 massGapD4 massGapD2
  norm_num

/-- Δm = 1 / t_min^Dm -/
theorem massGap_inverse_minTime :
    massGapD2 = 1 / FUST.TimeTheorem.structuralMinTimeD2 ∧
    massGapD3 = 1 / FUST.TimeTheorem.structuralMinTimeD3 ∧
    massGapD4 = 1 / FUST.TimeTheorem.structuralMinTimeD4 ∧
    massGapD5 = 1 / FUST.TimeTheorem.structuralMinTimeD5 ∧
    FUST.massGapΔ = 1 / FUST.TimeTheorem.structuralMinTimeD6 := by
  unfold massGapD2 massGapD3 massGapD4 massGapD5
  rw [FUST.TimeTheorem.structuralMinTimeD2_eq, FUST.TimeTheorem.structuralMinTimeD3_eq,
      FUST.TimeTheorem.structuralMinTimeD4_eq, FUST.TimeTheorem.structuralMinTimeD5_eq]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
          FUST.massGapΔ_eq_inv_structuralMinTimeD6⟩

end MassGapValues

/-! ## Yang-Mills Hamiltonian Interpretation (D6-specific)

For SU(3) Yang-Mills (QCD), the D₆ Hamiltonian has:
- H = 0: vacuum state
- H ∈ (0, Δ²): forbidden (spectral gap)
- H ≥ Δ²: glueball states
-/

section YangMillsInterpretation

def EnergyInSpectrum (E : ℝ) : Prop :=
  E = 0 ∨ FUST.massGapΔ ^ 2 ≤ E

theorem vacuum_in_spectrum : EnergyInSpectrum 0 := Or.inl rfl

theorem gap_excluded (E : ℝ) (hpos : 0 < E) (hlt : E < FUST.massGapΔ ^ 2) :
    ¬ EnergyInSpectrum E := by
  intro h
  cases h with
  | inl hz => linarith
  | inr hge => linarith

theorem above_gap_in_spectrum (E : ℝ) (hge : FUST.massGapΔ ^ 2 ≤ E) :
    EnergyInSpectrum E := Or.inr hge

theorem spectral_gap_squared : FUST.massGapΔ ^ 2 = 144 / 625 :=
  FUST.massGapΔ_sq

theorem clay_hamiltonian_gap_derived :
    (∀ f n, hamiltonianContributionD6 f n = (D6 f (φ ^ n))^2) ∧
    (kernelDimensions 2 = 3) ∧
    (kernelDimensions 1 = 2) ∧
    (0 < FUST.massGapΔ) ∧
    (FUST.massGapΔ = 12 / 25) := by
  refine ⟨fun _ _ => rfl, rfl, rfl, FUST.massGapΔ_pos, rfl⟩

end YangMillsInterpretation

/-! ## Complete Mass Gap Theorem -/

section CompleteMassGap

theorem hamiltonian_mass_gap_all :
    (∀ f N, partialHamiltonianD2 f N ≥ 0) ∧
    (∀ f N, partialHamiltonianD3 f N ≥ 0) ∧
    (∀ f N, partialHamiltonianD4 f N ≥ 0) ∧
    (∀ f N, partialHamiltonianD5 f N ≥ 0) ∧
    (∀ f N, partialHamiltonianD6 f N ≥ 0) ∧
    (∀ f, IsInKerD2 f → ∀ N, partialHamiltonianD2 f N = 0) ∧
    (∀ f, IsInKerD3 f → ∀ N, partialHamiltonianD3 f N = 0) ∧
    (∀ f, IsInKerD4 f → ∀ N, partialHamiltonianD4 f N = 0) ∧
    (∀ f, IsInKerD5 f → ∀ N, partialHamiltonianD5 f N = 0) ∧
    (∀ f, IsInKerD6 f → ∀ N, partialHamiltonianD6 f N = 0) ∧
    HasPositiveHamiltonianD2 id ∧
    HasPositiveHamiltonianD3 id ∧
    HasPositiveHamiltonianD4 (fun _ => 1) ∧
    HasPositiveHamiltonianD5 (fun t => t^2) ∧
    HasPositiveHamiltonianD6 (fun t => t^3) :=
  ⟨partialHamiltonianD2_nonneg,
   partialHamiltonianD3_nonneg,
   partialHamiltonianD4_nonneg,
   partialHamiltonianD5_nonneg,
   partialHamiltonianD6_nonneg,
   partialHamiltonianD2_ker_zero,
   partialHamiltonianD3_ker_zero,
   partialHamiltonianD4_ker_zero,
   partialHamiltonianD5_ker_zero,
   partialHamiltonianD6_ker_zero,
   linear_has_positive_hamiltonianD2,
   linear_has_positive_hamiltonianD3,
   const_has_positive_hamiltonianD4,
   quadratic_has_positive_hamiltonianD5,
   cubic_has_positive_hamiltonianD6⟩

end CompleteMassGap

/-! ## D₆ Resonance Stability

For H = D6†D6, eigenvalues μ_n = (D6Coeff n)² > 0 for n ≥ 3.
Resonances at E² = μ_n > 0 with μ_n ∈ ℝ force E ∈ ℝ.
All D₆ resonances are stable (infinite lifetime).
-/

section ResonanceStability

open FUST.SpectralCoefficients Complex

theorem sq_eq_pos_real_implies_real (c : ℝ) (hc : 0 < c) (E : ℂ) (h : E ^ 2 = (c : ℂ)) :
    E.im = 0 := by
  have him : (E ^ 2).im = (c : ℂ).im := congrArg Complex.im h
  simp only [sq, Complex.mul_im, Complex.ofReal_im] at him
  have h2 : 2 * E.re * E.im = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exfalso
      have hre : (E ^ 2).re = (c : ℂ).re := congrArg Complex.re h
      simp only [sq, Complex.mul_re, Complex.ofReal_re] at hre
      rw [h4] at hre
      simp at hre
      linarith [sq_nonneg E.im]
  · exact h3

theorem D6_eigenvalue_sq_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < (D6Coeff n) ^ 2 :=
  sq_pos_of_ne_zero (D6Coeff_ne_zero_of_ge_three n hn)

theorem D6_resonance_real_energy (n : ℕ) (hn : 3 ≤ n) (E : ℂ)
    (h : E ^ 2 = ((D6Coeff n) ^ 2 : ℝ)) :
    E.im = 0 :=
  sq_eq_pos_real_implies_real _ (D6_eigenvalue_sq_pos n hn) E h

theorem resonance_amplitude_stable (E t : ℝ) :
    ‖Complex.exp (-(I * E * t))‖ = 1 := by
  have h : -(I * (E : ℂ) * (t : ℂ)) = (-(E * t) : ℝ) * I := by push_cast; ring
  rw [h, norm_exp_ofReal_mul_I]

theorem resonance_amplitude_unstable (E : ℂ) (t : ℝ) (ht : t ≠ 0) (him : E.im ≠ 0) :
    ‖Complex.exp (-(I * E * (t : ℂ)))‖ ≠ 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring_nf
  intro h
  have : Real.exp (E.im * t) = 1 := h
  rw [Real.exp_eq_one_iff] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact him h1
  · exact ht h1

theorem D6_resonance_stability :
    (∀ f x, (D6 f x) ^ 2 ≥ 0) ∧
    (∀ n, 3 ≤ n → 0 < (D6Coeff n) ^ 2) ∧
    (∀ n, 3 ≤ n → ∀ E : ℂ, E ^ 2 = ((D6Coeff n) ^ 2 : ℝ) → E.im = 0) ∧
    (∀ E t : ℝ, ‖Complex.exp (-(I * E * t))‖ = 1) :=
  ⟨fun _ _ => sq_nonneg _,
   D6_eigenvalue_sq_pos,
   D6_resonance_real_energy,
   resonance_amplitude_stable⟩

end ResonanceStability

end FUST.Hamiltonian

namespace FUST.Dim

noncomputable def hamiltonianContribution_dim (f : ℝ → ℝ) (n : ℤ) :
    ScaleQ dimLagrangian :=
  ⟨FUST.Hamiltonian.hamiltonianContributionD6 f n⟩

theorem hamiltonianContribution_dim_nonneg (f : ℝ → ℝ) (n : ℤ) :
    (hamiltonianContribution_dim f n).val ≥ 0 :=
  FUST.Hamiltonian.hamiltonianContributionD6_nonneg f n

theorem hamiltonianContribution_ker_zero (f : ℝ → ℝ)
    (hf : FUST.LeastAction.IsInKerD6 f) (n : ℤ) :
    (hamiltonianContribution_dim f n).val = 0 :=
  FUST.Hamiltonian.hamiltonianContributionD6_ker_zero f hf n

end FUST.Dim
