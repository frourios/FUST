/-
FζDim: Dimension system for Fζ output values on physically manifest state functions.

Fζ eigenvalue = α(n)·AF_coeff + β(n) where α,β ∈ ℤ[φ], AF_coeff = -2+4ζ₆.
This lives in ℤ[φ,ζ₆] = GoldenEisensteinInt (CommRing).

Composite states use ring multiplication.
Mass formula: |eigenvalue|² = β² + 12α² (AF_coeff = 2i√3).
Factorization non-uniqueness connects to LaplaceDemon's partition_choice_invisible.
-/
import FUST.FrourioAlgebra.GoldenEisensteinInt
import FUST.FrourioAlgebra.GoldenIntegerRing
import FUST.FζOperator

namespace FUST.FζDim

open FUST FUST.Zeta6 FUST.FrourioAlgebra FUST.FζOperator

/-! ## Channel decomposition: eigenvalue = α·AF_coeff + β

The 4 integers (α₀, α₁, β₀, β₁) satisfy:
  eigenvalue = (β₀ + β₁φ) + (α₀ + α₁φ)·(-2 + 4ζ₆)
             = (β₀ - 2α₀) + (β₁ - 2α₁)φ + 4α₀·ζ₆ + 4α₁·φζ₆  -/

/-- Construct ℤ[φ,ζ₆] element from AF/SY channels: α·AF_coeff + β -/
def fromChannels (α β : GoldenInt) : GoldenEisensteinInt :=
  GoldenEisensteinInt.add
    (GoldenEisensteinInt.ofGoldenInt β)
    (GoldenEisensteinInt.mul (GoldenEisensteinInt.ofGoldenInt α) GoldenEisensteinInt.AF_coeff_gei)

theorem fromChannels_eq (α β : GoldenInt) :
    fromChannels α β = ⟨β.a - 2 * α.a, β.b - 2 * α.b, 4 * α.a, 4 * α.b⟩ := by
  unfold fromChannels GoldenEisensteinInt.add GoldenEisensteinInt.mul
    GoldenEisensteinInt.ofGoldenInt GoldenEisensteinInt.AF_coeff_gei
  ext <;> simp <;> ring

theorem fromChannels_zero :
    fromChannels ⟨0, 0⟩ ⟨0, 0⟩ = GoldenEisensteinInt.zero := by
  rw [fromChannels_eq]; unfold GoldenEisensteinInt.zero; ext <;> simp

/-! ## Eigenvalue of Fζ on monomial z^n

For active mode n:
- Φ_A_eigen(n) ∈ ℤ[φ]: coefficient from AF channel
- Φ_S_eigen(n) ∈ ℤ[φ]: coefficient from SY channel
- eigenFζ(n) = fromChannels (5·Φ_A_eigen) (6·Φ_S_eigen) -/

/-- ψ^n in ℤ[φ] via Galois conjugation: ψ^n = conj(φ^n) -/
def psiPowNat (n : ℕ) : GoldenInt := GoldenInt.conj (GoldenInt.phiPowNat n)

/-- Φ_A eigenvalue on z^n in ℤ[φ]:
    φ^{3n} - 4φ^{2n} + (3+φ)φ^n - (4-φ)ψ^n + 4ψ^{2n} - ψ^{3n} -/
def phiA_goldenInt (n : ℕ) : GoldenInt :=
  let p3n := GoldenInt.phiPowNat (3 * n)
  let p2n := GoldenInt.phiPowNat (2 * n)
  let pn := GoldenInt.phiPowNat n
  let q_n := psiPowNat n
  let q2n := psiPowNat (2 * n)
  let q3n := psiPowNat (3 * n)
  p3n + (⟨-4, 0⟩ : GoldenInt) * p2n + ⟨3, 1⟩ * pn +
  (⟨-4, 1⟩ : GoldenInt) * q_n + ⟨4, 0⟩ * q2n + (⟨-1, 0⟩ : GoldenInt) * q3n

/-- Φ_S_int eigenvalue on z^n in ℤ[φ]:
    10φ^{2n} + (21-2φ)φ^n - 50 + (9+2φ)ψ^n + 10ψ^{2n} -/
def phiS_goldenInt (n : ℕ) : GoldenInt :=
  let p2n := GoldenInt.phiPowNat (2 * n)
  let pn := GoldenInt.phiPowNat n
  let q_n := psiPowNat n
  let q2n := psiPowNat (2 * n)
  ⟨10, 0⟩ * p2n + ⟨21, -2⟩ * pn + (⟨-50, 0⟩ : GoldenInt) +
  ⟨9, 2⟩ * q_n + ⟨10, 0⟩ * q2n

/-- Eigenvalue of Fζ on z^{6k+1} as ℤ[φ,ζ₆] element -/
def eigenFζ_mod1 (k : ℕ) : GoldenEisensteinInt :=
  let n := 6 * k + 1
  fromChannels (⟨5, 0⟩ * phiA_goldenInt n) (⟨6, 0⟩ * phiS_goldenInt n)

/-- Eigenvalue of Fζ on z^{6k+5}: AF sign flipped -/
def eigenFζ_mod5 (k : ℕ) : GoldenEisensteinInt :=
  let n := 6 * k + 5
  fromChannels (⟨-5, 0⟩ * phiA_goldenInt n) (⟨6, 0⟩ * phiS_goldenInt n)

/-! ## Verification: eigenFζ on z (n=1, k=0) -/

theorem phiA_goldenInt_one : phiA_goldenInt 1 = ⟨-2, 4⟩ := by decide

theorem phiS_goldenInt_one : phiS_goldenInt 1 = ⟨-15, 10⟩ := by decide

/-- eigenFζ(z) = [-70, 20, -40, 80] in basis {1, φ, ζ₆, φζ₆} -/
theorem eigenFζ_z : eigenFζ_mod1 0 = ⟨-70, 20, -40, 80⟩ := by decide

/-! ## Active/Kernel mode classification -/

def isActiveMode (n : ℕ) : Bool := n % 6 == 1 || n % 6 == 5

def isKernelMode (n : ℕ) : Bool := !isActiveMode n

/-! ## Composite state multiplication

Composite eigenvalue = ring multiplication in ℤ[φ,ζ₆].
In channel form: (α₁, β₁) × (α₂, β₂) → (α₁β₂+α₂β₁, β₁β₂-12α₁α₂)
since AF_coeff² = -12. -/

def compositeEigenvalue (x y : GoldenEisensteinInt) : GoldenEisensteinInt :=
  GoldenEisensteinInt.mul x y

/-- AF_coeff² = -12 in ℤ[ζ₆] ⊂ ℤ[φ,ζ₆] -/
theorem AF_coeff_sq :
    GoldenEisensteinInt.mul GoldenEisensteinInt.AF_coeff_gei
      GoldenEisensteinInt.AF_coeff_gei = ⟨-12, 0, 0, 0⟩ := by decide

/-- Channel decomposition of product -/
theorem composite_channels (a1 b1 a2 b2 : GoldenInt) :
    compositeEigenvalue (fromChannels a1 b1) (fromChannels a2 b2) =
    fromChannels (a1 * b2 + a2 * b1) (b1 * b2 + ⟨-12, 0⟩ * (a1 * a2)) := by
  rw [fromChannels_eq, fromChannels_eq, fromChannels_eq]
  obtain ⟨aa, ab⟩ := a1; obtain ⟨ba, bb⟩ := b1
  obtain ⟨ca, cb⟩ := a2; obtain ⟨da, db⟩ := b2
  simp only [compositeEigenvalue, GoldenEisensteinInt.mul,
    HMul.hMul, Mul.mul, HAdd.hAdd, Add.add, GoldenInt.mul, GoldenInt.add]
  simp only [(show Int.mul = (· * ·) from rfl), (show Int.add = (· + ·) from rfl)]
  ext <;> ring

/-! ## Product confinement: active × active → kernel

If a ≡ 1 or 5 and b ≡ 1 or 5 mod 6, then a+b ≡ 0,2,4 mod 6 (all kernel). -/

theorem active_product_kernel (a b : ℕ)
    (ha : isActiveMode a = true) (hb : isActiveMode b = true) :
    isKernelMode (a + b) = true := by
  simp only [isKernelMode, isActiveMode, Bool.not_eq_true',
    Bool.or_eq_true, beq_iff_eq, Bool.or_eq_false_iff] at *
  rw [Nat.add_mod]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-! ## Mass formula: |eigenvalue|² = β² + 12α²

Since AF_coeff = 2i√3, for eigenvalue = α·AF + β with α,β ∈ ℝ:
|eigenvalue|² = β² + 12α² -/

private theorem toComplex_ofGoldenInt (x : GoldenInt) :
    GoldenEisensteinInt.toComplex (GoldenEisensteinInt.ofGoldenInt x) =
    ↑(GoldenInt.toReal x) := by
  unfold GoldenEisensteinInt.toComplex GoldenEisensteinInt.ofGoldenInt GoldenInt.toReal
  push_cast; ring

noncomputable def massSq (x : GoldenEisensteinInt) : ℝ :=
  Complex.normSq (GoldenEisensteinInt.toComplex x)

theorem mass_formula (α β : GoldenInt) :
    massSq (fromChannels α β) =
    GoldenInt.toReal β ^ 2 + 12 * GoldenInt.toReal α ^ 2 := by
  unfold massSq fromChannels
  rw [GoldenEisensteinInt.toComplex_add, GoldenEisensteinInt.toComplex_mul,
      GoldenEisensteinInt.AF_coeff_gei_eq, toComplex_ofGoldenInt, toComplex_ofGoldenInt]
  rw [AF_coeff_eq]
  set a := GoldenInt.toReal α
  set b := GoldenInt.toReal β
  have heq : (↑b : ℂ) + ↑a * (⟨0, 2 * Real.sqrt 3⟩ : ℂ) = ⟨b, 2 * Real.sqrt 3 * a⟩ := by
    apply Complex.ext <;> simp [mul_comm]
  rw [heq, Complex.normSq_mk]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  nlinarith [h3, sq_nonneg a, sq_nonneg b]

/-! ## Factorization associativity and commutativity -/

theorem factorization_assoc (x y z : GoldenEisensteinInt) :
    compositeEigenvalue (compositeEigenvalue x y) z =
    compositeEigenvalue x (compositeEigenvalue y z) := by
  unfold compositeEigenvalue
  exact GoldenEisensteinInt.mul_assoc' x y z

theorem composite_comm (x y : GoldenEisensteinInt) :
    compositeEigenvalue x y = compositeEigenvalue y x := by
  unfold compositeEigenvalue
  exact GoldenEisensteinInt.mul_comm' x y

/-! ## Connection to FDim: Galois symmetry quotient

The FDim (p, δ) is a quotient of the ℤ[φ,ζ₆] ring structure.
σ (φ↦ψ) and τ (ζ₆↦1-ζ₆) determine the symmetry class. -/

theorem sigma_parity (x : GoldenEisensteinInt) :
    GoldenEisensteinInt.sigma x = x ↔ x.b = 0 ∧ x.d = 0 :=
  GoldenEisensteinInt.sigma_fixed_iff x

theorem tau_parity (x : GoldenEisensteinInt) :
    GoldenEisensteinInt.tau x = x ↔ x.c = 0 ∧ x.d = 0 :=
  GoldenEisensteinInt.tau_fixed_iff x

end FUST.FζDim
