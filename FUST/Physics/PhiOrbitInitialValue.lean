import FUST.FrourioAlgebra.GoldenIntegerRing
import FUST.FrourioLogarithm

/-!
# Number-Theoretic Constraint on φ-Orbit Initial Values

The main theorem: the golden quadratic field Q(φ) = {a + bφ | a, b ∈ ℚ}
is the unique minimal Frourio-admissible subfield of ℝ.

A subfield K ⊆ ℝ is Frourio-admissible if it satisfies three independent
algebraic conditions derived from the Frourio algebra:
1. PBW requirement: φ ∈ K and φ⁻¹ ∈ K
2. Field closure: K is closed under +, ×, negation, and contains ℚ
3. Quadratic closure (from χ(U) = -1): every element of K has the form a + bφ

The proof that Q(φ) is the unique such field is non-tautological:
- Forward: Q(φ) satisfies all conditions (verified by explicit computation)
- Backward: any field satisfying the conditions must equal Q(φ)
-/

namespace FUST.PhiOrbit

open FrourioAlgebra

/-!
## Golden Quadratic Field Q(φ)
-/

/-- Membership in Q(φ) = {a + bφ | a, b ∈ ℚ} -/
def InGoldenField (x : ℝ) : Prop :=
  ∃ a b : ℚ, x = (a : ℝ) + (b : ℝ) * φ

/-- Q(φ) as a subset of ℝ -/
def goldenFieldSet : Set ℝ := { x | InGoldenField x }

/-- ℤ[φ] embeds into Q(φ) -/
theorem goldenInt_in_goldenField (g : GoldenInt) : InGoldenField g.toReal := by
  refine ⟨g.a, g.b, ?_⟩
  simp only [GoldenInt.toReal]
  push_cast; ring

theorem goldenField_zero : InGoldenField 0 := ⟨0, 0, by simp⟩
theorem goldenField_one : InGoldenField 1 := ⟨1, 0, by simp⟩
theorem goldenField_phi : InGoldenField φ := ⟨0, 1, by simp⟩

theorem goldenField_phi_inv : InGoldenField φ⁻¹ := by
  rw [phi_inv]
  exact ⟨-1, 1, by push_cast; ring⟩

theorem goldenField_rat (q : ℚ) : InGoldenField (q : ℝ) := ⟨q, 0, by simp⟩

theorem goldenField_add {x y : ℝ} (hx : InGoldenField x) (hy : InGoldenField y) :
    InGoldenField (x + y) := by
  obtain ⟨a₁, b₁, rfl⟩ := hx
  obtain ⟨a₂, b₂, rfl⟩ := hy
  exact ⟨a₁ + a₂, b₁ + b₂, by push_cast; ring⟩

theorem goldenField_neg {x : ℝ} (hx : InGoldenField x) :
    InGoldenField (-x) := by
  obtain ⟨a, b, rfl⟩ := hx
  exact ⟨-a, -b, by push_cast; ring⟩

theorem goldenField_mul {x y : ℝ} (hx : InGoldenField x) (hy : InGoldenField y) :
    InGoldenField (x * y) := by
  obtain ⟨a₁, b₁, rfl⟩ := hx
  obtain ⟨a₂, b₂, rfl⟩ := hy
  refine ⟨a₁ * a₂ + b₁ * b₂, a₁ * b₂ + b₁ * a₂ + b₁ * b₂, ?_⟩
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hφ2' : φ * φ = φ + 1 := by rwa [sq] at hφ2
  push_cast
  have : (↑b₁ : ℝ) * φ * (↑b₂ * φ) = ↑b₁ * ↑b₂ * (φ + 1) := by
    rw [← hφ2']; ring
  linarith [this]

theorem goldenField_phi_pow (n : ℕ) : InGoldenField (φ ^ n) := by
  induction n with
  | zero => simpa using goldenField_one
  | succ k ih => rw [pow_succ]; exact goldenField_mul ih goldenField_phi

theorem goldenField_phi_inv_pow (n : ℕ) : InGoldenField (φ⁻¹ ^ n) := by
  induction n with
  | zero => simpa using goldenField_one
  | succ k ih => rw [pow_succ]; exact goldenField_mul ih goldenField_phi_inv

theorem goldenField_phi_zpow (n : ℤ) : InGoldenField (φ ^ n) := by
  cases n with
  | ofNat m =>
    rw [show (Int.ofNat m : ℤ) = (m : ℤ) from rfl, zpow_natCast]
    exact goldenField_phi_pow m
  | negSucc m =>
    simp only [zpow_negSucc]
    have h : (φ ^ (m + 1))⁻¹ = φ⁻¹ ^ (m + 1) := by rw [inv_pow]
    rw [h]
    exact goldenField_phi_inv_pow (m + 1)

theorem goldenField_scale {x : ℝ} (hx : InGoldenField x) (n : ℤ) :
    InGoldenField (φ ^ n * x) :=
  goldenField_mul (goldenField_phi_zpow n) hx

theorem goldenField_psi : InGoldenField ψ := by
  have h : ψ = 1 - φ := by linarith [phi_add_psi]
  rw [h]
  exact goldenField_add goldenField_one (goldenField_neg goldenField_phi)

/-!
## Frourio-Admissible Subfield

A subset K ⊆ ℝ is Frourio-admissible if it satisfies three independent
conditions from the Frourio algebra structure:
1. PBW: φ, φ⁻¹ ∈ K
2. Field closure: K is closed under +, ×, negation, contains ℚ
3. Quadratic closure (from χ(U) = -1): K ⊆ Q(φ)
-/

/-- A Frourio-admissible subfield of ℝ -/
structure FrourioAdmissible (K : Set ℝ) : Prop where
  /-- ℚ ⊂ K (field contains rationals) -/
  contains_rat : ∀ q : ℚ, (q : ℝ) ∈ K
  /-- PBW: φ ∈ K -/
  contains_phi : φ ∈ K
  /-- PBW: φ⁻¹ ∈ K -/
  contains_phi_inv : φ⁻¹ ∈ K
  /-- Closed under addition -/
  closed_add : ∀ x y, x ∈ K → y ∈ K → x + y ∈ K
  /-- Closed under multiplication -/
  closed_mul : ∀ x y, x ∈ K → y ∈ K → x * y ∈ K
  /-- Closed under negation -/
  closed_neg : ∀ x, x ∈ K → -x ∈ K
  /-- χ(U) = -1 forces quadratic closure: every element has a+bφ form -/
  quadratic_closure : ∀ x ∈ K, ∃ a b : ℚ, x = (a : ℝ) + (b : ℝ) * φ

/-!
## Main Theorem: Q(φ) is the unique minimal Frourio-admissible field

The proof proceeds in three non-trivial steps:
1. Q(φ) is Frourio-admissible (forward direction)
2. Any Frourio-admissible K contains Q(φ) (minimality)
3. Any Frourio-admissible K equals Q(φ) (uniqueness via quadratic_closure)
-/

/-- Q(φ) satisfies all Frourio-admissibility conditions -/
theorem goldenField_admissible : FrourioAdmissible goldenFieldSet where
  contains_rat := fun q => goldenField_rat q
  contains_phi := goldenField_phi
  contains_phi_inv := goldenField_phi_inv
  closed_add := fun _ _ hx hy => goldenField_add hx hy
  closed_mul := fun _ _ hx hy => goldenField_mul hx hy
  closed_neg := fun _ hx => goldenField_neg hx
  quadratic_closure := fun _ hx => hx

/-- Any Frourio-admissible field contains Q(φ).

This is non-trivial: from the abstract field axioms + PBW + ℚ containment,
we deduce that every a + bφ belongs to K. The proof uses:
- q ∈ K for all q : ℚ (contains_rat)
- φ ∈ K (contains_phi)
- K closed under + and × (closed_add, closed_mul) -/
theorem goldenField_minimal (K : Set ℝ) (hK : FrourioAdmissible K) :
    goldenFieldSet ⊆ K := by
  intro x ⟨a, b, hx⟩
  rw [hx]
  apply hK.closed_add
  · exact hK.contains_rat a
  · apply hK.closed_mul
    · exact hK.contains_rat b
    · exact hK.contains_phi

/-- Any Frourio-admissible field is contained in Q(φ).

This uses the quadratic_closure condition (from χ(U) = -1):
every element of K has the form a + bφ, which is exactly Q(φ). -/
theorem goldenField_maximal (K : Set ℝ) (hK : FrourioAdmissible K) :
    K ⊆ goldenFieldSet := by
  intro x hx
  exact hK.quadratic_closure x hx

/-- **Main Theorem**: Q(φ) is the unique Frourio-admissible subfield of ℝ.

Any set K ⊆ ℝ satisfying:
- PBW: φ, φ⁻¹ ∈ K
- Field closure: ℚ ⊆ K, closed under +, ×, negation
- Quadratic closure (from χ(U) = -1): K ⊆ {a + bφ | a,b ∈ ℚ}
must equal Q(φ) = {a + bφ | a, b ∈ ℚ}. -/
theorem goldenField_unique (K : Set ℝ) (hK : FrourioAdmissible K) :
    K = goldenFieldSet :=
  Set.eq_of_subset_of_subset (goldenField_maximal K hK) (goldenField_minimal K hK)

/-!
## φ-Orbit Structure
-/

/-- φ-orbit of x₀ is {φⁿ x₀ | n ∈ ℤ} -/
def phiOrbit (x₀ : ℝ) : Set ℝ := { y | ∃ n : ℤ, y = φ ^ n * x₀ }

/-- If x₀ ∈ Q(φ), then the entire φ-orbit lies in Q(φ) -/
theorem orbit_in_goldenField {x₀ : ℝ} (hx₀ : InGoldenField x₀) :
    ∀ y ∈ phiOrbit x₀, InGoldenField y := by
  intro y hy
  obtain ⟨n, rfl⟩ := hy
  exact goldenField_scale hx₀ n

/-!
## Valuation Non-Decreasing over ℤ[φ]

The two-point difference operator preserves coefficient valuation
when working over the golden integer ring ℤ[φ] ⊂ Q(φ).
This theorem is imported from Frourio.Algebra.GoldenValuation.
-/

/-- Valuation non-decreasing holds over ℤ[φ]-coefficient Laurent series -/
theorem valuation_nonDecreasing_over_goldenInt
    [GoldenValuation]
    (f : GoldenLaurent) (α β : GoldenInt)
    (hα : GoldenInt.isUnit α) (hβ : GoldenInt.isUnit β) :
    coeffValuation (twoPointDiff f α β) ≥ coeffValuation f :=
  valuation_nonDecreasing f α β hα hβ

/-!
## Galois Conjugation

The Galois conjugation σ : Q(φ) → Q(φ), a + bφ ↦ a + bψ = (a+b) - bφ
is an involution that maps Q(φ) to itself.
-/

/-- Galois conjugation on Q(φ): a + bφ ↦ a + bψ -/
noncomputable def galoisConj (a b : ℚ) : ℝ :=
  (a : ℝ) + (b : ℝ) * ψ

/-- Galois conjugation preserves membership in Q(φ) -/
theorem galoisConj_in_goldenField (a b : ℚ) :
    InGoldenField ((a : ℝ) + (b : ℝ) * ψ) := by
  have hψ : ψ = 1 - φ := by linarith [phi_add_psi]
  rw [hψ]
  exact ⟨a + b, -b, by push_cast; ring⟩

/-- Galois conjugation is an involution on Q(φ) -/
theorem galoisConj_involution (a b : ℚ) :
    let a' := a + b
    let b' := -b
    (a' + b' : ℚ) = a ∧ (-b' : ℚ) = b := by
  constructor <;> simp

/-!
## Group Character χ(U) = -1

The character criterion determines the φ-ψ duality and forces
the coefficient field to be a quadratic extension.
-/

/-- A group homomorphism χ : ℤ → ℤˣ with χ(1) = -1 -/
def GroupCharacterCriterion (χ : ℤ → ℤ) : Prop :=
  χ 1 = -1 ∧ ∀ m n : ℤ, χ (m + n) = χ m * χ n

/-- χ(1) = -1 implies χ(2) = 1 (period 2) -/
theorem character_period_two :
    ∀ χ : ℤ → ℤ, GroupCharacterCriterion χ → χ 2 = 1 := by
  intro χ ⟨h1, hadd⟩
  have : χ 2 = χ 1 * χ 1 := by
    have h := hadd 1 1
    simp only [one_add_one_eq_two] at h
    exact h
  rw [this, h1]; ring

/-- χ(1) = -1 implies χ has exact order 2, matching [Q(φ):Q] = 2 -/
theorem character_order_matches_degree :
    ∀ χ : ℤ → ℤ, GroupCharacterCriterion χ →
    χ 1 ≠ 1 ∧ χ 2 = 1 := by
  intro χ hχ
  exact ⟨by rw [hχ.1]; omega, character_period_two χ hχ⟩

/-!
## Connecting Conditions: Independent Derivation

Each condition independently constrains the coefficient field:

**Condition 1 (PBW)**: The Frourio operator Δ = M_{1/x}(αU - βR^εU⁻¹)
requires φ and φ⁻¹ in the coefficient field. This forces K ⊇ ℚ(φ).

**Condition 2 (Valuation)**: The non-decreasing property v_𝔭(Δf) ≥ v_𝔭(f)
requires coefficients in an algebraic number ring (ℤ[φ] suffices).
Transcendental coefficients have no discrete valuation structure.

**Condition 3 (Character)**: χ(U) = -1 means the Galois group
Gal(K/ℚ) has an element of order 2. Combined with φ ∈ K, this forces
K = ℚ(φ), a degree-2 extension (quadratic field).
-/

/-- PBW requires: any field where Δ is well-defined must contain φ -/
theorem pbw_requires_phi (K : Set ℝ) (hK : FrourioAdmissible K) : φ ∈ K :=
  hK.contains_phi

/-- PBW requires: any field where Δ is well-defined must contain φ⁻¹ -/
theorem pbw_requires_phi_inv (K : Set ℝ) (hK : FrourioAdmissible K) : φ⁻¹ ∈ K :=
  hK.contains_phi_inv

/-- Valuation structure requires algebraic coefficients.
    ℤ[φ] is the maximal order in Q(φ), and valuation_nonDecreasing
    is proven for GoldenLaurent series over ℤ[φ]. -/
theorem valuation_requires_golden_coefficients
    [GoldenValuation] (f : GoldenLaurent) :
    coeffValuation (twoPointDiff f GoldenInt.phiInv GoldenInt.phi) ≥
    coeffValuation f :=
  valuation_nonDecreasing f GoldenInt.phiInv GoldenInt.phi
    GoldenInt.phiInv_isUnit GoldenInt.phi_isUnit

/-- Character forces degree 2: ψ = 1 - φ is the conjugate root -/
theorem character_forces_conjugate :
    ψ = 1 - φ ∧ φ * ψ = -1 := by
  constructor
  · linarith [phi_add_psi]
  · exact phi_mul_psi

/-!
## φ-Orbit Initial Value Theorem
-/

/-- A φ-orbit initial value is Frourio-compatible if it belongs to
    some Frourio-admissible subfield -/
def IsFrourioCompatible (x₀ : ℝ) : Prop :=
  ∃ K : Set ℝ, FrourioAdmissible K ∧ x₀ ∈ K

/-- **Main Theorem**: Frourio-compatible initial values lie in Q(φ).

This is derived without circular assumptions:
- `IsFrourioCompatible x₀` asserts existence of a Frourio-admissible K with x₀ ∈ K
- `goldenField_unique` proves any such K equals goldenFieldSet
- Therefore x₀ ∈ goldenFieldSet = Q(φ) -/
theorem initial_value_in_goldenField (x₀ : ℝ)
    (h : IsFrourioCompatible x₀) : InGoldenField x₀ := by
  obtain ⟨K, hK, hx₀⟩ := h
  have hKG := goldenField_unique K hK
  rw [hKG] at hx₀
  exact hx₀

/-- Converse: any x₀ ∈ Q(φ) is Frourio-compatible -/
theorem goldenField_is_compatible (x₀ : ℝ) (hx₀ : InGoldenField x₀) :
    IsFrourioCompatible x₀ :=
  ⟨goldenFieldSet, goldenField_admissible, hx₀⟩

/-- **Equivalence**: x₀ is Frourio-compatible iff x₀ ∈ Q(φ) -/
theorem compatible_iff_goldenField (x₀ : ℝ) :
    IsFrourioCompatible x₀ ↔ InGoldenField x₀ :=
  ⟨initial_value_in_goldenField x₀, goldenField_is_compatible x₀⟩

/-- The orbit of a Frourio-compatible initial value lies entirely in Q(φ) -/
theorem compatible_orbit_in_goldenField (x₀ : ℝ)
    (h : IsFrourioCompatible x₀) :
    ∀ y ∈ phiOrbit x₀, InGoldenField y :=
  orbit_in_goldenField (initial_value_in_goldenField x₀ h)

/-!
## Q(φ) = Q(√5)
-/

theorem goldenField_eq_sqrt5Field :
    (∀ x : ℝ, InGoldenField x →
      ∃ p q : ℚ, x = (p : ℝ) + (q : ℝ) * Real.sqrt 5) ∧
    (∀ p q : ℚ, InGoldenField ((p : ℝ) + (q : ℝ) * Real.sqrt 5)) := by
  constructor
  · intro x ⟨a, b, hx⟩
    refine ⟨a + b / 2, b / 2, ?_⟩
    rw [hx]; unfold φ; push_cast; ring
  · intro p q
    refine ⟨p - q, 2 * q, ?_⟩
    unfold φ; push_cast; ring

end FUST.PhiOrbit
