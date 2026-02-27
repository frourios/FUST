/-
Golden-Eisenstein integer ring ℤ[φ,ζ₆] = ring of integers of ℚ(√5,√(-3)).
Elements: a + bφ + cζ₆ + dφζ₆ with φ²=φ+1, ζ₆²=ζ₆-1. Class number h=1 (UFD).
-/
import FUST.FrourioAlgebra.GoldenIntegerRing
import FUST.DζOperator

namespace FUST.FrourioAlgebra

open FUST FUST.DζOperator

/-- ℤ[φ,ζ₆]: a + bφ + cζ₆ + dφζ₆ -/
@[ext]
structure GoldenEisensteinInt where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Repr

namespace GoldenEisensteinInt

def zero : GoldenEisensteinInt := ⟨0, 0, 0, 0⟩
def one : GoldenEisensteinInt := ⟨1, 0, 0, 0⟩

def add (x y : GoldenEisensteinInt) : GoldenEisensteinInt :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

def neg (x : GoldenEisensteinInt) : GoldenEisensteinInt :=
  ⟨-x.a, -x.b, -x.c, -x.d⟩

def sub (x y : GoldenEisensteinInt) : GoldenEisensteinInt := add x (neg y)

/-- Multiplication using φ²=φ+1, ζ₆²=ζ₆-1 -/
def mul (x y : GoldenEisensteinInt) : GoldenEisensteinInt :=
  ⟨x.a * y.a + x.b * y.b - x.c * y.c - x.d * y.d,
   x.a * y.b + x.b * y.a + x.b * y.b - x.c * y.d - x.d * y.c - x.d * y.d,
   x.a * y.c + x.b * y.d + x.c * y.a + x.c * y.c + x.d * y.b + x.d * y.d,
   x.a * y.d + x.b * y.c + x.b * y.d + x.c * y.b + x.c * y.d +
   x.d * y.a + x.d * y.b + x.d * y.c + x.d * y.d⟩

/-! ## Ring axioms -/

theorem add_comm' (x y : GoldenEisensteinInt) : add x y = add y x := by
  unfold add; ext <;> ring

theorem add_assoc' (x y z : GoldenEisensteinInt) :
    add (add x y) z = add x (add y z) := by
  unfold add; ext <;> ring

theorem zero_add' (x : GoldenEisensteinInt) : add zero x = x := by
  unfold add zero; ext <;> simp

theorem add_zero' (x : GoldenEisensteinInt) : add x zero = x := by
  unfold add zero; ext <;> simp

theorem neg_add_cancel' (x : GoldenEisensteinInt) : add (neg x) x = zero := by
  unfold add neg zero; ext <;> simp

theorem mul_comm' (x y : GoldenEisensteinInt) : mul x y = mul y x := by
  unfold mul; ext <;> ring

theorem mul_assoc' (x y z : GoldenEisensteinInt) :
    mul (mul x y) z = mul x (mul y z) := by
  unfold mul; ext <;> ring

theorem one_mul' (x : GoldenEisensteinInt) : mul one x = x := by
  unfold mul one; ext <;> simp

theorem mul_one' (x : GoldenEisensteinInt) : mul x one = x := by
  unfold mul one; ext <;> simp

theorem left_distrib' (x y z : GoldenEisensteinInt) :
    mul x (add y z) = add (mul x y) (mul x z) := by
  unfold mul add; ext <;> ring

theorem right_distrib' (x y z : GoldenEisensteinInt) :
    mul (add x y) z = add (mul x z) (mul y z) := by
  unfold mul add; ext <;> ring

theorem zero_mul' (x : GoldenEisensteinInt) : mul zero x = zero := by
  unfold mul zero; ext <;> simp

theorem mul_zero' (x : GoldenEisensteinInt) : mul x zero = zero := by
  unfold mul zero; ext <;> simp

/-! ## Scalar multiplication -/

def nsmul : ℕ → GoldenEisensteinInt → GoldenEisensteinInt
  | 0, _ => zero
  | n + 1, x => add (nsmul n x) x

def zsmul : ℤ → GoldenEisensteinInt → GoldenEisensteinInt
  | Int.ofNat n, x => nsmul n x
  | Int.negSucc n, x => neg (nsmul (n + 1) x)

def npow : ℕ → GoldenEisensteinInt → GoldenEisensteinInt
  | 0, _ => one
  | n + 1, x => mul (npow n x) x

def natCast : ℕ → GoldenEisensteinInt := fun n => ⟨n, 0, 0, 0⟩
def intCast : ℤ → GoldenEisensteinInt
  | Int.ofNat n => ⟨n, 0, 0, 0⟩
  | Int.negSucc n => ⟨-(n + 1 : ℤ), 0, 0, 0⟩

instance : NatCast GoldenEisensteinInt := ⟨natCast⟩
instance : IntCast GoldenEisensteinInt := ⟨intCast⟩

/-! ## CommRing instance -/

instance : CommRing GoldenEisensteinInt where
  add := add
  add_assoc := add_assoc'
  zero := zero
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmul
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  neg := neg
  zsmul := zsmul
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun n x => by
    change zsmul (Int.ofNat (n + 1)) x = add (zsmul (Int.ofNat n) x) x
    simp only [zsmul, nsmul]
  zsmul_neg' := fun n x => by
    change zsmul (Int.negSucc n) x = neg (zsmul (Int.ofNat (n + 1)) x)
    simp only [zsmul]
  neg_add_cancel := fun x => by
    change add (neg x) x = zero
    exact neg_add_cancel' x
  add_comm := add_comm'
  mul := mul
  mul_assoc := mul_assoc'
  one := one
  one_mul := one_mul'
  mul_one := mul_one'
  npow := npow
  npow_zero := fun _ => rfl
  npow_succ := fun _ _ => rfl
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  mul_comm := mul_comm'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  natCast := natCast
  natCast_zero := rfl
  natCast_succ := fun n => by
    change natCast (n + 1) = add (natCast n) one
    unfold natCast add one; ext <;> simp
  intCast := intCast
  intCast_ofNat := fun _ => rfl
  intCast_negSucc := fun _ => rfl

/-! ## Embedding into ℂ -/

noncomputable def toComplex (x : GoldenEisensteinInt) : ℂ :=
  ↑(x.a : ℤ) + ↑(x.b : ℤ) * (↑φ : ℂ) + ↑(x.c : ℤ) * ζ₆ + ↑(x.d : ℤ) * (↑φ : ℂ) * ζ₆

theorem toComplex_zero : toComplex zero = 0 := by
  unfold toComplex zero; push_cast; ring

theorem toComplex_one : toComplex one = 1 := by
  unfold toComplex one; push_cast; ring

theorem toComplex_add (x y : GoldenEisensteinInt) :
    toComplex (add x y) = toComplex x + toComplex y := by
  unfold toComplex add; push_cast; ring

theorem toComplex_neg (x : GoldenEisensteinInt) :
    toComplex (neg x) = -toComplex x := by
  unfold toComplex neg; push_cast; ring

private lemma phi_mul_phi : (↑φ : ℂ) * ↑φ = ↑φ + 1 := by
  have h := golden_ratio_property
  have : φ * φ = φ + 1 := by nlinarith [h]
  calc (↑φ : ℂ) * ↑φ = ↑(φ * φ) := by push_cast; ring
    _ = ↑(φ + 1) := congrArg _ this
    _ = ↑φ + 1 := by push_cast; ring

private lemma zeta6_mul_zeta6 : ζ₆ * ζ₆ = ζ₆ - 1 := by
  have := zeta6_sq; rw [sq] at this; exact this

theorem toComplex_mul (x y : GoldenEisensteinInt) :
    toComplex (mul x y) = toComplex x * toComplex y := by
  unfold toComplex mul
  set a := (↑x.a : ℂ); set b := (↑x.b : ℂ); set c := (↑x.c : ℂ); set d := (↑x.d : ℂ)
  set e := (↑y.a : ℂ); set f := (↑y.b : ℂ); set g := (↑y.c : ℂ); set h := (↑y.d : ℂ)
  set P := (↑φ : ℂ); set Z := ζ₆
  push_cast
  have hP : P * P = P + 1 := phi_mul_phi
  have hZ : Z * Z = Z - 1 := zeta6_mul_zeta6
  -- Rewrite all P² and Z² occurrences in expanded product
  have : (a + b * P + c * Z + d * P * Z) * (e + f * P + g * Z + h * P * Z) =
    a * e + a * f * P + a * g * Z + a * h * P * Z +
    b * e * P + b * f * (P * P) + b * g * P * Z + b * h * (P * P) * Z +
    c * e * Z + c * f * P * Z + c * g * (Z * Z) + c * h * P * (Z * Z) +
    d * e * P * Z + d * f * (P * P) * Z + d * g * P * (Z * Z) +
    d * h * (P * P) * (Z * Z) := by ring
  rw [this, hP, hZ]
  ring

/-! ## Galois automorphisms: Gal(ℚ(√5,√(-3))/ℚ) ≅ ℤ/2 × ℤ/2 -/

/-- σ: φ ↦ ψ (fixes ζ₆) -/
def sigma (x : GoldenEisensteinInt) : GoldenEisensteinInt :=
  ⟨x.a + x.b, -x.b, x.c + x.d, -x.d⟩

/-- τ: ζ₆ ↦ ζ₆' = 1-ζ₆ (fixes φ) -/
def tau (x : GoldenEisensteinInt) : GoldenEisensteinInt :=
  ⟨x.a + x.c, x.b + x.d, -x.c, -x.d⟩

theorem sigma_add (x y : GoldenEisensteinInt) :
    sigma (add x y) = add (sigma x) (sigma y) := by
  unfold sigma add; ext <;> ring

theorem sigma_mul (x y : GoldenEisensteinInt) :
    sigma (mul x y) = mul (sigma x) (sigma y) := by
  unfold sigma mul; ext <;> ring

theorem sigma_one : sigma one = one := by
  unfold sigma one; ext <;> simp

theorem sigma_involution (x : GoldenEisensteinInt) : sigma (sigma x) = x := by
  unfold sigma; ext <;> ring

theorem tau_add (x y : GoldenEisensteinInt) :
    tau (add x y) = add (tau x) (tau y) := by
  unfold tau add; ext <;> ring

theorem tau_mul (x y : GoldenEisensteinInt) :
    tau (mul x y) = mul (tau x) (tau y) := by
  unfold tau mul; ext <;> ring

theorem tau_one : tau one = one := by
  unfold tau one; ext <;> simp

theorem tau_involution (x : GoldenEisensteinInt) : tau (tau x) = x := by
  unfold tau; ext <;> ring

theorem sigma_tau_comm (x : GoldenEisensteinInt) :
    sigma (tau x) = tau (sigma x) := by
  unfold sigma tau; ext <;> ring

/-! ## τ-Norm: x·τ(x) ∈ ℤ[φ] -/

def tauProduct (x : GoldenEisensteinInt) : GoldenEisensteinInt := mul x (tau x)

theorem tauProduct_c_zero (x : GoldenEisensteinInt) : (tauProduct x).c = 0 := by
  unfold tauProduct mul tau; ring

theorem tauProduct_d_zero (x : GoldenEisensteinInt) : (tauProduct x).d = 0 := by
  unfold tauProduct mul tau; ring

/-- Project τ-product to ℤ[φ] -/
def tauNorm (x : GoldenEisensteinInt) : GoldenInt :=
  ⟨x.a * x.a + x.a * x.c + x.b * x.b + x.b * x.d + x.c * x.c + x.d * x.d,
   2 * x.a * x.b + x.a * x.d + x.b * x.b + x.b * x.c + x.b * x.d +
   2 * x.c * x.d + x.d * x.d⟩

/-- Full norm: N(x) = N_{ℤ[φ]}(x·τ(x)) -/
def norm (x : GoldenEisensteinInt) : ℤ := GoldenInt.norm (tauNorm x)

/-! ## Embedding from ℤ[φ] -/

def ofGoldenInt (x : GoldenInt) : GoldenEisensteinInt := ⟨x.a, x.b, 0, 0⟩

theorem ofGoldenInt_add (x y : GoldenInt) :
    ofGoldenInt (GoldenInt.add x y) = add (ofGoldenInt x) (ofGoldenInt y) := by
  unfold ofGoldenInt GoldenInt.add add; rfl

theorem ofGoldenInt_mul (x y : GoldenInt) :
    ofGoldenInt (GoldenInt.mul x y) = mul (ofGoldenInt x) (ofGoldenInt y) := by
  unfold ofGoldenInt GoldenInt.mul mul; ext <;> simp

theorem ofGoldenInt_one : ofGoldenInt GoldenInt.one = one := by
  unfold ofGoldenInt GoldenInt.one one; rfl

/-! ## Key constants in ℤ[φ,ζ₆] -/

/-- φ as element of ℤ[φ,ζ₆] -/
def phi_gei : GoldenEisensteinInt := ⟨0, 1, 0, 0⟩

/-- ζ₆ as element of ℤ[φ,ζ₆] -/
def zeta6_gei : GoldenEisensteinInt := ⟨0, 0, 1, 0⟩

/-- AF_coeff = 4ζ₆ - 2 ∈ ℤ[ζ₆] ⊂ ℤ[φ,ζ₆] -/
def AF_coeff_gei : GoldenEisensteinInt := ⟨-2, 0, 4, 0⟩

/-- 5μ = 6 - 2φ ∈ ℤ[φ] ⊂ ℤ[φ,ζ₆] -/
def five_mu_gei : GoldenEisensteinInt := ⟨6, -2, 0, 0⟩

/-- 5(3+μ) = 21 - 2φ -/
def five_three_plus_mu : GoldenEisensteinInt := ⟨21, -2, 0, 0⟩

/-- 5(3-μ) = 9 + 2φ -/
def five_three_minus_mu : GoldenEisensteinInt := ⟨9, 2, 0, 0⟩

/-! ## Units: φ, ζ₆, -1 generate ℤ[φ,ζ₆]× -/

/-- ζ₆' = 1 - ζ₆ is the inverse of ζ₆ (since ζ₆·ζ₆'=1) -/
def zeta6_bar : GoldenEisensteinInt := ⟨1, 0, -1, 0⟩

/-- ψ = 1 - φ as GEI element -/
def psi_gei : GoldenEisensteinInt := ⟨1, -1, 0, 0⟩

/-- -ψ is the inverse of φ (since φ·(-ψ) = -φψ = 1) -/
def neg_psi_gei : GoldenEisensteinInt := ⟨-1, 1, 0, 0⟩

theorem zeta6_mul_bar : mul zeta6_gei zeta6_bar = one := by
  unfold mul zeta6_gei zeta6_bar one; ext <;> simp

theorem phi_mul_neg_psi : mul phi_gei neg_psi_gei = one := by
  unfold mul phi_gei neg_psi_gei one; ext <;> simp

/-! ## Galois-fixed elements: σ(x)=x ∧ τ(x)=x ↔ x ∈ ℤ (b=c=d=0) -/

theorem sigma_fixed_iff (x : GoldenEisensteinInt) :
    sigma x = x ↔ x.b = 0 ∧ x.d = 0 := by
  constructor
  · intro h
    have hb : x.a + x.b = x.a := congr_arg GoldenEisensteinInt.a h
    have hd : x.c + x.d = x.c := congr_arg GoldenEisensteinInt.c h
    exact ⟨by linarith, by linarith⟩
  · intro ⟨hb, hd⟩
    unfold sigma; ext <;> simp [hb, hd]

theorem tau_fixed_iff (x : GoldenEisensteinInt) :
    tau x = x ↔ x.c = 0 ∧ x.d = 0 := by
  constructor
  · intro h
    have hc : x.a + x.c = x.a := congr_arg GoldenEisensteinInt.a h
    have hd : x.b + x.d = x.b := congr_arg GoldenEisensteinInt.b h
    exact ⟨by linarith, by linarith⟩
  · intro ⟨hc, hd⟩
    unfold tau; ext <;> simp [hc, hd]

/-- Galois-fixed elements are exactly ℤ ⊂ ℤ[φ,ζ₆] -/
theorem galois_fixed_iff (x : GoldenEisensteinInt) :
    sigma x = x ∧ tau x = x ↔ x.b = 0 ∧ x.c = 0 ∧ x.d = 0 := by
  rw [sigma_fixed_iff, tau_fixed_iff]
  constructor
  · intro ⟨⟨hb, hd⟩, ⟨hc, _⟩⟩; exact ⟨hb, hc, hd⟩
  · intro ⟨hb, hc, hd⟩; exact ⟨⟨hb, hd⟩, ⟨hc, hd⟩⟩

/-- The only Galois-fixed units are ±1 -/
theorem galois_fixed_unit_iff (x : GoldenEisensteinInt) :
    sigma x = x ∧ tau x = x ∧ (mul x x = one ∨ mul x (neg x) = one) →
    x = one ∨ x = neg one := by
  intro ⟨hs, ht, hu⟩
  have hf := (galois_fixed_iff x).mp ⟨hs, ht⟩
  obtain ⟨hb, hc, hd⟩ := hf
  cases hu with
  | inl h =>
    have ha : x.a * x.a + 0 - 0 - 0 = 1 := by
      have := congr_arg GoldenEisensteinInt.a h
      simp [mul, one, hb, hc, hd] at this; linarith
    have : x.a * x.a = 1 := by linarith
    have : x.a = 1 ∨ x.a = -1 := by
      have := Int.eq_one_or_neg_one_of_mul_eq_one' this
      rcases this with ⟨h1, _⟩ | ⟨h1, _⟩ <;> [left; right] <;> exact h1
    rcases this with ha | ha
    · left; ext <;> simp [one, hb, hc, hd, ha]
    · right; ext <;> simp [neg, one, hb, hc, hd, ha]
  | inr h =>
    have ha : x.a * (-x.a) + 0 + 0 + 0 = 1 := by
      have := congr_arg GoldenEisensteinInt.a h
      simp [mul, neg, one, hb, hc, hd] at this; linarith
    linarith [mul_self_nonneg x.a]

theorem AF_coeff_gei_eq :
    toComplex AF_coeff_gei = DζOperator.AF_coeff := by
  unfold toComplex AF_coeff_gei AF_coeff
  push_cast
  have h3 : ζ₆ ^ 3 = -1 := zeta6_cubed
  have h4 : ζ₆ ^ 4 = ζ₆ ^ 3 * ζ₆ := by ring
  have h5 : ζ₆ ^ 5 = ζ₆ ^ 3 * ζ₆ ^ 2 := by ring
  rw [h4, h5, h3, zeta6_sq]; ring

theorem five_mu_correct :
    (toComplex five_mu_gei : ℂ) * ((↑φ : ℂ) + 2) = 10 := by
  unfold toComplex five_mu_gei
  push_cast
  have hP : (↑φ : ℂ) * ↑φ = ↑φ + 1 := phi_mul_phi
  have : (6 + -2 * (↑φ : ℂ) + 0 * ζ₆ + 0 * ↑φ * ζ₆) * (↑φ + 2) =
    -2 * ((↑φ : ℂ) * ↑φ) + 2 * ↑φ + 12 := by ring
  rw [this, hP]; ring

end GoldenEisensteinInt

end FUST.FrourioAlgebra
