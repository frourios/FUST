import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import FUST.FrourioAlgebra.GoldenEisensteinInt
import FUST.FrourioAlgebra.GoldenIntegerRing
import FUST.FζOperator

namespace FUST.Dim

open FUST.DζOperator FUST.FrourioAlgebra

/-- FUST dimension: (p, δ) where p = φ-power, δ = dissipation -/
structure FDim where
  p : ℤ
  delta : ℤ
  deriving DecidableEq, Repr

instance : One FDim where one := ⟨0, 0⟩

instance : Mul FDim where mul a b := ⟨a.p + b.p, a.delta + b.delta⟩

instance : Inv FDim where inv a := ⟨-a.p, -a.delta⟩

instance : Div FDim where div a b := a * b⁻¹

theorem one_p : (1 : FDim).p = 0 := rfl
theorem one_delta : (1 : FDim).delta = 0 := rfl
theorem mul_p (a b : FDim) : (a * b).p = a.p + b.p := rfl
theorem mul_delta (a b : FDim) : (a * b).delta = a.delta + b.delta := rfl
theorem inv_p (a : FDim) : a⁻¹.p = -a.p := rfl
theorem inv_delta (a : FDim) : a⁻¹.delta = -a.delta := rfl

theorem FDim.ext {a b : FDim} (hp : a.p = b.p) (hd : a.delta = b.delta) :
    a = b := by
  cases a; cases b; simp_all

instance : CommGroup FDim where
  mul_assoc a b c := FDim.ext (by simp [mul_p]; omega) (by simp [mul_delta]; omega)
  one_mul a := FDim.ext (by simp [one_p, mul_p]) (by simp [one_delta, mul_delta])
  mul_one a := FDim.ext (by simp [one_p, mul_p]) (by simp [one_delta, mul_delta])
  inv_mul_cancel a := FDim.ext (by simp [one_p, mul_p, inv_p])
    (by simp [one_delta, mul_delta, inv_delta])
  mul_comm a b := FDim.ext (by simp [mul_p]; omega) (by simp [mul_delta]; omega)

theorem npow_p (a : FDim) (n : ℕ) : (a ^ n).p = n * a.p := by
  induction n with
  | zero => simp [pow_zero, one_p]
  | succ k ih => simp [pow_succ, mul_p, ih]; ring

theorem npow_delta (a : FDim) (n : ℕ) : (a ^ n).delta = n * a.delta := by
  induction n with
  | zero => simp [pow_zero, one_delta]
  | succ k ih => simp [pow_succ, mul_delta, ih]; ring

theorem zpow_p (a : FDim) (n : ℤ) : (a ^ n).p = n * a.p := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp [npow_p, zpow_natCast]
  · simp [npow_p, zpow_neg, zpow_natCast, inv_p]

theorem zpow_delta (a : FDim) (n : ℤ) : (a ^ n).delta = n * a.delta := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp [npow_delta, zpow_natCast]
  · simp [npow_delta, zpow_neg, zpow_natCast, inv_delta]

section ScaleQuantity

/-- Dimensioned real quantity parameterized by FUST dimension -/
structure ScaleQ (d : FDim) where
  val : ℝ

instance (d : FDim) : Add (ScaleQ d) where add a b := ⟨a.val + b.val⟩
instance (d : FDim) : Sub (ScaleQ d) where sub a b := ⟨a.val - b.val⟩
instance (d : FDim) : Neg (ScaleQ d) where neg a := ⟨-a.val⟩
instance (d : FDim) : Zero (ScaleQ d) where zero := ⟨0⟩

noncomputable instance (d1 d2 : FDim) : HMul (ScaleQ d1) (ScaleQ d2) (ScaleQ (d1 * d2)) where
  hMul a b := ⟨a.val * b.val⟩

noncomputable instance (d1 d2 : FDim) : HDiv (ScaleQ d1) (ScaleQ d2) (ScaleQ (d1 * d2⁻¹)) where
  hDiv a b := ⟨a.val / b.val⟩

noncomputable instance (d : FDim) : HSMul ℝ (ScaleQ d) (ScaleQ d) where
  hSMul r a := ⟨r * a.val⟩

theorem ScaleQ.add_val {d : FDim} (a b : ScaleQ d) : (a + b).val = a.val + b.val := rfl
theorem ScaleQ.sub_val {d : FDim} (a b : ScaleQ d) : (a - b).val = a.val - b.val := rfl
theorem ScaleQ.neg_val {d : FDim} (a : ScaleQ d) : (-a).val = -a.val := rfl
theorem ScaleQ.zero_val {d : FDim} : (0 : ScaleQ d).val = 0 := rfl
theorem ScaleQ.mul_val {d1 d2 : FDim} (a : ScaleQ d1) (b : ScaleQ d2) :
    (a * b).val = a.val * b.val := rfl
theorem ScaleQ.div_val {d1 d2 : FDim} (a : ScaleQ d1) (b : ScaleQ d2) :
    (a / b).val = a.val / b.val := rfl
theorem ScaleQ.smul_val {d : FDim} (r : ℝ) (a : ScaleQ d) :
    (r • a).val = r * a.val := rfl

noncomputable def ScaleQ.sq {d : FDim} (a : ScaleQ d) : ScaleQ (d * d) := a * a

theorem ScaleQ.sq_val {d : FDim} (a : ScaleQ d) : a.sq.val = a.val * a.val := rfl

end ScaleQuantity

section CountQuantity

/-- Count quantity for kernel dimensions, pair counts, etc. -/
structure CountQ where
  val : ℕ
  deriving DecidableEq, Repr

instance : Add CountQ where add a b := ⟨a.val + b.val⟩
instance : Mul CountQ where mul a b := ⟨a.val * b.val⟩

noncomputable def CountQ.toReal (c : CountQ) : ℝ := c.val

end CountQuantity

section RatioQuantity

/-- Dimensionless ratio quantity -/
structure RatioQ where
  val : ℚ
  deriving DecidableEq, Repr

instance : Add RatioQ where add a b := ⟨a.val + b.val⟩
instance : Sub RatioQ where sub a b := ⟨a.val - b.val⟩
instance : Mul RatioQ where mul a b := ⟨a.val * b.val⟩
instance : Div RatioQ where div a b := ⟨a.val / b.val⟩

end RatioQuantity

section DimSum

/-- Formal sum of two quantities with different dimensions -/
structure DimSum2 (d1 d2 : FDim) where
  fst : ScaleQ d1
  snd : ScaleQ d2

noncomputable def DimSum2.eval {d1 d2 : FDim} (s : DimSum2 d1 d2) : ℝ :=
  s.fst.val + s.snd.val

theorem DimSum2.eval_mk {d1 d2 : FDim} (a : ScaleQ d1) (b : ScaleQ d2) :
    (DimSum2.mk a b).eval = a.val + b.val := rfl

def DimSum2.inl {d1 d2 : FDim} (a : ScaleQ d1) : DimSum2 d1 d2 := ⟨a, 0⟩
def DimSum2.inr {d1 d2 : FDim} (b : ScaleQ d2) : DimSum2 d1 d2 := ⟨0, b⟩

end DimSum

section DeriveFDim

/-! ## deriveFDim: derived from D operator kernel theorems

Each component of FDim is derived from algebraic properties of D_m:
- p = -(m-1): denominator power (φ-ψ)^(m-1) in D_m definition
- δ: φ↔ψ antisymmetry of the numerator N_m
-/

/-- Derive FDim from operator order m (for D_m):
  p = -(m-1), δ = 1 if m even else 0 -/
def deriveFDim (m : Nat) : FDim :=
  ⟨-((m - 1 : Nat) : ℤ),
   if m % 2 == 0 then 1 else 0⟩

def dimTime : FDim := (deriveFDim 6)⁻¹

theorem dimTime_eq : dimTime = ⟨5, -1⟩ := by decide

def dimLagrangian : FDim := deriveFDim 6 * deriveFDim 6

/-- Time dimension for each Dm: dimTimeDm = (deriveFDim m)⁻¹ -/
def dimTimeD2 : FDim := (deriveFDim 2)⁻¹

theorem dimTimeD2_eq : dimTimeD2 = ⟨1, -1⟩ := by decide

end DeriveFDim

section StateClassDecomposition

/-! ## FDim ↔ State Function Class correspondence -/

/-- Effective polynomial degree: d = -p - 2δ -/
def FDim.effectiveDegree (dim : FDim) : ℤ := -dim.p - 2 * dim.delta

/-- Sector power: a = (-p - δ) / 4 -/
def FDim.sectorPower (dim : FDim) : ℤ := (-dim.p - dim.delta) / 4

def FDim.detectionLevel (dim : FDim) : ℤ :=
  dim.effectiveDegree - 3 * dim.sectorPower

end StateClassDecomposition

/-! ## Eigenvalue dimension system in ℤ[φ,ζ₆]

Fζ eigenvalue = α(n)·AF_coeff + β(n) where α,β ∈ ℤ[φ], AF_coeff = -2+4ζ₆.
Mass formula: |eigenvalue|² = β² + 12α² (AF_coeff = 2i√3). -/

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

/-! ## Eigenvalue of Fζ on monomial z^n -/

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

theorem active_product_kernel (a b : ℕ)
    (ha : isActiveMode a = true) (hb : isActiveMode b = true) :
    isKernelMode (a + b) = true := by
  simp only [isKernelMode, isActiveMode, Bool.not_eq_true',
    Bool.or_eq_true, beq_iff_eq, Bool.or_eq_false_iff] at *
  rw [Nat.add_mod]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

/-! ## Mass formula: |eigenvalue|² = β² + 12α² -/

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

/-! ## Galois symmetry quotient: FζDim → FDim projection -/

theorem sigma_parity (x : GoldenEisensteinInt) :
    GoldenEisensteinInt.sigma x = x ↔ x.b = 0 ∧ x.d = 0 :=
  GoldenEisensteinInt.sigma_fixed_iff x

theorem tau_parity (x : GoldenEisensteinInt) :
    GoldenEisensteinInt.tau x = x ↔ x.c = 0 ∧ x.d = 0 :=
  GoldenEisensteinInt.tau_fixed_iff x

end FUST.Dim
