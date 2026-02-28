import FUST.Physics.TimeStructure
import FUST.Physics.Probability
import FUST.Physics.SchrodingerEquation
import FUST.Physics.MassGap

/-!
# FUST Thermodynamics: Three Laws from Fζ Structure

The three laws of thermodynamics derived from the unified operator Fζ = 5z·Dζ.

**Physical correspondence**:
- Entropy S(f)(z) := |Fζ f z|² measures departure from ker(Fζ)
- Time evolution f ↦ f(φ·) is identified with temporal direction via Poincaré I4
  decomposition (Gravity.lean: Φ_A_coeff built from φ,ψ with η(inr 0, inr 0) = -1)
- ker(Fζ) = thermal equilibrium = light cone (no proper time)
- ker(Fζ)⊥ = active states = massive particles (proper time > 0)

**Laws**:
- Zeroth: ker(Fζ) states share zero entropy (thermal equilibrium)
- First: FζLagrangian is φ-equivariant (energy conservation via Noether)
- Second: φ > 1 amplifies ker(Fζ)⊥ components (entropy increase)
- Third: f ∉ ker(Fζ) ⟹ ∃z, S(f)(z) > 0 (absolute zero unreachable)
-/

namespace FUST.Thermodynamics

open FUST FUST.TimeStructure FUST.FζOperator
open FUST.Probability FUST.SchrodingerEquation Complex

/-! ## Zeroth Law: Thermal Equilibrium as ker(Fζ)

Two systems in ker(Fζ) have identical entropy: S ≡ 0.
Same-degree scalar multiples have gauge-invariant entropy ratio. -/

section ZerothLaw

/-- ker(Fζ) states share zero entropy everywhere -/
theorem zeroth_law_kernel_equilibrium (f g : ℂ → ℂ)
    (hf : IsInKerFζ f) (hg : IsInKerFζ g) :
    ∀ z, entropyAtFζ f z = entropyAtFζ g z := by
  intro z
  rw [(entropyAtFζ_zero_iff f z).mpr (hf z), (entropyAtFζ_zero_iff g z).mpr (hg z)]

/-- Entropy ratio for same-degree states is gauge-invariant -/
theorem zeroth_law_same_degree_thermal (a b : ℂ) (f : ℂ → ℂ) (z : ℂ)
    (_hb : b ≠ 0) (hfz : Fζ f z ≠ 0) :
    entropyAtFζ (fun t => a * f t) z / entropyAtFζ (fun t => b * f t) z =
    normSq a / normSq b := by
  simp only [entropyAtFζ, FζLagrangian, Fζ_const_smul, normSq_mul]
  have hFζ : normSq (Fζ f z) ≠ 0 := normSq_pos.mpr hfz |>.ne'
  rw [mul_div_mul_right _ _ hFζ]

end ZerothLaw

/-! ## First Law: Energy Conservation

FζLagrangian is φ-equivariant: L[f(φ·)](z) = L[f](φz).
This is the FUST Noether current: φ-scale symmetry ⟹ energy conservation. -/

section FirstLaw

/-- φ-equivariance of Lagrangian = energy conservation -/
theorem first_law_equivariance (f : ℂ → ℂ) (z : ℂ) :
    FζLagrangian (timeEvolution f) z = FζLagrangian f ((↑φ : ℂ) * z) :=
  lagrangian_phi_equivariant f z

/-- Vacuum (ker) energy is zero -/
theorem first_law_vacuum_energy (f : ℂ → ℂ) (hf : IsInKerFζ f) (n : ℤ) :
    actionFζ f n = 0 :=
  actionFζ_ker_zero f hf n

/-- Action (energy) is non-negative -/
theorem first_law_energy_nonneg (f : ℂ → ℂ) (x₀ : ℝ) (N : ℕ) :
    FUST.Probability.discreteAction f x₀ N ≥ 0 :=
  FUST.Probability.discreteAction_nonneg f x₀ N

/-- Partial action is monotone: enlarging the scale window cannot decrease energy -/
theorem first_law_action_monotone (f : ℂ → ℂ) (N M : ℕ) (h : N ≤ M) :
    partialActionFζ f N ≤ partialActionFζ f M := by
  unfold partialActionFζ
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc (neg_le_neg (Int.ofNat_le.mpr h)) (Int.ofNat_le.mpr h)
  · intro i _ _; exact actionFζ_nonneg f i

end FirstLaw

/-! ## Second Law: Entropy Increase

φ-scaling (time evolution) amplifies ker(Fζ)⊥ components by φⁿ > 1.
Reversible processes remain in ker(Fζ); irreversible stay outside. -/

section SecondLaw

/-- Time evolution shifts entropy evaluation point by φ -/
theorem second_law_entropy_shift (f : ℂ → ℂ) (z : ℂ) :
    entropyAtFζ (timeEvolution f) z = entropyAtFζ f ((↑φ : ℂ) * z) :=
  lagrangian_phi_equivariant f z

/-- Monomial amplification: timeEvolution(tⁿ) = φⁿ·tⁿ -/
theorem second_law_monomial_amplification (n : ℕ) (t : ℂ) :
    timeEvolution (fun s => s ^ n) t = (↑φ : ℂ) ^ n * t ^ n :=
  monomial_amplification n t

/-- Reversible: ker(Fζ) is invariant under time evolution -/
theorem second_law_reversible (f : ℂ → ℂ) (hf : IsInKerFζ f) :
    IsInKerFζ (timeEvolution f) :=
  ker_Fζ_invariant f hf

/-- Irreversible: non-ker states remain non-ker -/
theorem second_law_irreversible (f : ℂ → ℂ) (hf : ¬IsInKerFζ f) :
    ¬IsInKerFζ (timeEvolution f) :=
  (timeEvolution_preserves_Fζ f).mp hf

/-- φⁿ > 1 for n ≥ 1: amplification factor exceeds unity -/
theorem second_law_amplification (n : ℕ) (hn : n ≥ 1) : φ ^ n > 1 :=
  phi_pow_gt_one n hn

end SecondLaw

/-! ## Third Law: Absolute Zero Unreachable

Active states (f ∉ ker(Fζ)) cannot reach absolute zero (S ≡ 0).
Finite iterations of time evolution preserve non-ker status. -/

section ThirdLaw

/-- Active states have positive entropy somewhere -/
theorem third_law_positive_entropy (f : ℂ → ℂ) (hf : ¬IsInKerFζ f) :
    ∃ z, entropyAtFζ f z > 0 :=
  third_law_Fζ f hf

/-- S ≡ 0 ⟺ f ∈ ker(Fζ) -/
theorem third_law_absolute_zero_iff (f : ℂ → ℂ) :
    (∀ z, entropyAtFζ f z = 0) ↔ IsInKerFζ f :=
  entropy_zero_iff_kerFζ f

/-- Finite time evolution cannot reach ker(Fζ) from outside -/
theorem third_law_finite_unreachable (f : ℂ → ℂ) (hf : ¬IsInKerFζ f) (n : ℕ) :
    ¬IsInKerFζ (timeEvolution^[n] f) := by
  induction n with
  | zero => simpa using hf
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact (timeEvolution_preserves_Fζ _).mp ih

/-- Mass gap: minimum energy of active states is positive -/
theorem third_law_mass_gap : massGapSq > 0 := massGapSq_pos

/-- ker states can reach zero entropy everywhere -/
theorem third_law_lightlike_zero (f : ℂ → ℂ) (hf : IsInKerFζ f) :
    ∀ z, entropyAtFζ f z = 0 :=
  (entropy_zero_iff_kerFζ f).mpr hf

end ThirdLaw

/-! ## Structural Properties of Entropy -/

section EntropyStructure

/-- Positive entropy ⟺ Fζ is active -/
theorem entropy_pos_iff_active (f : ℂ → ℂ) (z : ℂ) :
    entropyAtFζ f z > 0 ↔ Fζ f z ≠ 0 := by
  rw [show entropyAtFζ f z = normSq (Fζ f z) from rfl]
  exact ⟨fun h hzero => by rw [hzero, map_zero] at h; exact lt_irrefl 0 h,
         fun h => normSq_pos.mpr h⟩

/-- Entropy scales quadratically under scalar multiplication -/
theorem entropy_scalar_scaling (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    entropyAtFζ (fun t => c * f t) z = normSq c * entropyAtFζ f z := by
  simp only [entropyAtFζ, FζLagrangian, Fζ_const_smul, normSq_mul]

/-- Mass scale Δ = 12/25 > 0: thermal gap from Fζ structure -/
theorem thermal_gap : massScale > 0 := massScale_pos

end EntropyStructure

end FUST.Thermodynamics
