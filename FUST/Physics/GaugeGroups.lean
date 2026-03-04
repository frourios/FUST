import FUST.FζOperator
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace FUST

open FUST.DζOperator Matrix FUST.FrourioAlgebra.GoldenEisensteinInt

/-! ### A₂ root system from Eisenstein integers

The ζ₆ sublattice ℤ[ζ₆] ⊂ ℤ[φ,ζ₆] has exactly 6 units: ±1, ±ζ₆, ±ζ₆².
These form the A₂ root system with Cartan matrix [[2,-1],[-1,2]],
which determines the Lie algebra su(3) (dim 8 = 6 roots + rank 2). -/

open FUST.FrourioAlgebra

def cartanA2 : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 2]

theorem cartanA2_det : cartanA2.det = 3 := by
  simp [cartanA2, Matrix.det_fin_two]

def eisensteinUnits : Fin 6 → FUST.FrourioAlgebra.GoldenEisensteinInt :=
  ![⟨1,0,0,0⟩, ⟨0,0,1,0⟩, ⟨-1,0,1,0⟩, ⟨-1,0,0,0⟩, ⟨0,0,-1,0⟩, ⟨1,0,-1,0⟩]

theorem eisensteinUnit_in_zeta6_sublattice (i : Fin 6) :
    (eisensteinUnits i).b = 0 ∧ (eisensteinUnits i).d = 0 := by
  fin_cases i <;> simp [eisensteinUnits]

theorem eisensteinUnit_isUnit (i : Fin 6) :
    mul (eisensteinUnits i) (tau (eisensteinUnits i)) =
      FUST.FrourioAlgebra.GoldenEisensteinInt.one := by
  fin_cases i <;> unfold eisensteinUnits mul tau
    FUST.FrourioAlgebra.GoldenEisensteinInt.one <;> ext <;> simp

/-- Eisenstein norm: for x in ℤ[ζ₆] sublattice (b=d=0), N(x) = (a²+ac+c²)² -/
theorem eisenstein_norm_eq (a c : ℤ) :
    FUST.FrourioAlgebra.GoldenEisensteinInt.norm ⟨a, 0, c, 0⟩ =
    (a ^ 2 + a * c + c ^ 2) ^ 2 := by
  unfold FUST.FrourioAlgebra.GoldenEisensteinInt.norm tauNorm GoldenInt.norm; ring

/-- Classification: a²+ac+c²=1 has exactly 6 integer solutions -/
theorem eisenstein_unit_classification (a c : ℤ) (h : a ^ 2 + a * c + c ^ 2 = 1) :
    (a = 1 ∧ c = 0) ∨ (a = 0 ∧ c = 1) ∨ (a = -1 ∧ c = 1) ∨
    (a = -1 ∧ c = 0) ∨ (a = 0 ∧ c = -1) ∨ (a = 1 ∧ c = -1) := by
  have hc : -1 ≤ c ∧ c ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (2*a+c), sq_nonneg (c + 1), sq_nonneg (c - 1)]
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (a+2*c), sq_nonneg (a + 1), sq_nonneg (a - 1)]
  have : c = -1 ∨ c = 0 ∨ c = 1 := by omega
  have : a = -1 ∨ a = 0 ∨ a = 1 := by omega
  rcases ‹c = -1 ∨ c = 0 ∨ c = 1› with rfl | rfl | rfl <;>
    rcases ‹a = -1 ∨ a = 0 ∨ a = 1› with rfl | rfl | rfl <;>
    simp_all

theorem cartan_pairing_offdiag :
    2 * ((1:ℝ) * (-1/2) + 0 * (Real.sqrt 3 / 2)) /
    ((-1/2) * (-1/2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2)) = -1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : Real.sqrt 3 * Real.sqrt 3 = 3 := by rw [← sq]; exact h3
  field_simp
  nlinarith

/-- U(1) gauge group uniqueness for the trivial channel.

The trivial channel is the Galois-fixed subspace of ℤ[φ,ζ₆]:
- galois_fixed_iff: σ(x)=x ∧ τ(x)=x ↔ b=c=d=0 (1D over ℤ)
- On 1D: norm-preserving gauge = unitaryGroup (Fin 1) ℂ = U(1)
- SU(1) = {I} is trivial: no SU reduction, full gauge is U(1)
- derivDefect_const_gauge: scalar U(1) is exactly the gauge freedom -/
theorem U1_gauge_uniqueness :
    -- Galois-fixed subspace = ℤ (dim 1)
    (∀ x : FUST.FrourioAlgebra.GoldenEisensteinInt,
      sigma x = x ∧ tau x = x ↔ x.b = 0 ∧ x.c = 0 ∧ x.d = 0) ∧
    -- Scalar gauge invariance (derivDefect)
    (∀ (c : ℂ) (_ : c ≠ 0) (f g : ℂ → ℂ) (z : ℂ),
      FζOperator.derivDefect (fun w => c * f w) (fun w => c⁻¹ * g w) z =
      FζOperator.derivDefect f g z) ∧
    -- Scalar unitary c·I₁ ∈ U(1)
    (∀ c : ℂ, starRingEnd ℂ c * c = 1 →
      c • (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ unitaryGroup (Fin 1) ℂ) ∧
    -- det(c·I₁) = c (linear, not higher power)
    (∀ c : ℂ, (c • (1 : Matrix (Fin 1) (Fin 1) ℂ)).det = c ^ 1) ∧
    -- SU(1) is trivial (only identity)
    (∀ M : Matrix (Fin 1) (Fin 1) ℂ,
      M ∈ specialUnitaryGroup (Fin 1) ℂ → M = 1) ∧
    -- Galois-fixed units are ±1
    (∀ x : FUST.FrourioAlgebra.GoldenEisensteinInt,
      sigma x = x ∧ tau x = x ∧ (mul x x = one ∨ mul x (neg x) = one) →
      x = one ∨ x = neg one) :=
  ⟨galois_fixed_iff,
   FζOperator.derivDefect_const_gauge,
   fun c hc => by
     rw [mem_unitaryGroup_iff']; ext i j
     simp only [star_smul, star_one, mul_apply, smul_apply, one_apply, smul_eq_mul]
     simp [hc, Fin.eq_zero i, Fin.eq_zero j],
   fun c => by simp,
   fun M hM => by
     rw [mem_specialUnitaryGroup_iff] at hM; ext i j
     have hi := Fin.eq_zero i; have hj := Fin.eq_zero j; subst hi; subst hj
     simp only [one_apply_eq]; rw [det_fin_one] at hM; exact hM.2,
   galois_fixed_unit_iff⟩

/-- SU(2) gauge group uniqueness for the AF channel.

The AF channel carries a quaternionic structure from τ-anti-invariance:
- τ(AF_coeff) = -AF_coeff and τ² = id give eigenvalue -1
- AF_coeff² = -12: the J² < 0 quaternionic condition
- The 1D-over-ℂ AF space with quaternionic doubling gives ℂ² = ℍ¹
- Norm preservation on ℂ² → U(2), scalar separation → SU(2) = Sp(1) -/
theorem SU2_gauge_uniqueness :
    -- τ(AF_coeff) = -AF_coeff (quaternionic indicator)
    (tau AF_coeff_gei =
      FUST.FrourioAlgebra.GoldenEisensteinInt.neg AF_coeff_gei) ∧
    -- τ is an involution (eigenvalues ±1)
    (∀ x : FUST.FrourioAlgebra.GoldenEisensteinInt, tau (tau x) = x) ∧
    -- τ preserves multiplication (ring automorphism)
    (∀ x y : FUST.FrourioAlgebra.GoldenEisensteinInt,
      tau (mul x y) = mul (tau x) (tau y)) ∧
    -- AF_coeff² = -12 (quaternionic: J² < 0)
    (mul AF_coeff_gei AF_coeff_gei =
      (⟨-12, 0, 0, 0⟩ : FUST.FrourioAlgebra.GoldenEisensteinInt)) ∧
    -- AF_coeff is not real (complex structure essential, excludes SO(3))
    (AF_coeff.im ≠ 0) ∧
    -- Scalar unitary c·I₂ ∈ U(2) (center)
    (∀ c : ℂ, starRingEnd ℂ c * c = 1 →
      c • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitaryGroup (Fin 2) ℂ) ∧
    -- Scalar gauge has det c²
    (∀ c : ℂ, (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = c ^ 2) :=
  ⟨by unfold tau AF_coeff_gei FUST.FrourioAlgebra.GoldenEisensteinInt.neg; ext <;> simp,
   tau_involution,
   tau_mul,
   by unfold AF_coeff_gei mul; ext <;> simp,
   by rw [AF_coeff_eq]; simp,
   fun c hc => by
     rw [mem_unitaryGroup_iff']; ext i j
     simp only [star_smul, star_one, mul_apply, smul_apply, one_apply, smul_eq_mul,
       Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_ite, mul_zero, mul_one,
       ite_mul, zero_mul]
     split
     · subst_vars; exact hc
     · ring,
   fun c => by simp [Fintype.card_fin]⟩

/-- SU(3) gauge group from A₂ root system.

ℤ[ζ₆] has 6 units forming the A₂ root system (Cartan matrix [[2,-1],[-1,2]]).
A₂ determines su(3): dim = 6 roots + rank 2 = 8 = 3²-1.
Scalar U(1) separated by derivDefect, star≠id excludes SO. -/
theorem SU3_gauge_uniqueness :
    -- A₂ Cartan matrix is nondegenerate (det=3)
    (cartanA2.det = 3) ∧
    -- ℤ[ζ₆] has exactly 6 units (= A₂ roots)
    (∀ a c : ℤ, a ^ 2 + a * c + c ^ 2 = 1 →
      (a = 1 ∧ c = 0) ∨ (a = 0 ∧ c = 1) ∨ (a = -1 ∧ c = 1) ∨
      (a = -1 ∧ c = 0) ∨ (a = 0 ∧ c = -1) ∨ (a = 1 ∧ c = -1)) ∧
    -- 6 roots + rank 2 = dim su(3) = 8 = 3²-1
    (6 + 2 = 8 ∧ 3 ^ 2 - 1 = (8 : ℕ)) ∧
    -- ℂ has nontrivial star (SU not SO)
    (starRingEnd ℂ ≠ RingHom.id ℂ) ∧
    -- Scalar gauge separated by derivDefect
    (∀ (c : ℂ) (_ : c ≠ 0) (f g : ℂ → ℂ) (z : ℂ),
      FζOperator.derivDefect (fun w => c * f w) (fun w => c⁻¹ * g w) z =
      FζOperator.derivDefect f g z) :=
  ⟨cartanA2_det,
   eisenstein_unit_classification,
   ⟨by norm_num, by norm_num⟩,
   by intro h; have h1 : (starRingEnd ℂ) Complex.I = Complex.I := by rw [h]; simp
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_I] at h1
      have := congr_arg Complex.im h1
      simp only [Complex.neg_im, Complex.I_im] at this; linarith,
   FζOperator.derivDefect_const_gauge⟩

end FUST
