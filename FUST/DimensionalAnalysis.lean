import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import FUST.DifferenceOperators

namespace FUST.Dim

/-- FUST dimension: (p, δ) where p = φ-power, δ = dissipation -/
structure FDim where
  p : ℤ
  delta : ℤ
  deriving DecidableEq, Repr

instance : One FDim where one := ⟨0, 0⟩

instance : Mul FDim where mul a b := ⟨a.p + b.p, a.delta + b.delta⟩

instance : Inv FDim where inv a := ⟨-a.p, -a.delta⟩

instance : Div FDim where div a b := a * b⁻¹

@[simp] theorem one_p : (1 : FDim).p = 0 := rfl
@[simp] theorem one_delta : (1 : FDim).delta = 0 := rfl
@[simp] theorem mul_p (a b : FDim) : (a * b).p = a.p + b.p := rfl
@[simp] theorem mul_delta (a b : FDim) : (a * b).delta = a.delta + b.delta := rfl
@[simp] theorem inv_p (a : FDim) : a⁻¹.p = -a.p := rfl
@[simp] theorem inv_delta (a : FDim) : a⁻¹.delta = -a.delta := rfl

theorem FDim.ext {a b : FDim} (hp : a.p = b.p) (hd : a.delta = b.delta) :
    a = b := by
  cases a; cases b; simp_all

instance : CommGroup FDim where
  mul_assoc a b c := FDim.ext (by simp [mul_p]; omega) (by simp [mul_delta]; omega)
  one_mul a := FDim.ext (by simp) (by simp)
  mul_one a := FDim.ext (by simp) (by simp)
  inv_mul_cancel a := FDim.ext (by simp) (by simp)
  mul_comm a b := FDim.ext (by simp [mul_p]; omega) (by simp [mul_delta]; omega)

@[simp] theorem npow_p (a : FDim) (n : ℕ) : (a ^ n).p = n * a.p := by
  induction n with
  | zero => simp [pow_zero, one_p]
  | succ k ih => simp [pow_succ, mul_p, ih]; ring

@[simp] theorem npow_delta (a : FDim) (n : ℕ) : (a ^ n).delta = n * a.delta := by
  induction n with
  | zero => simp [pow_zero, one_delta]
  | succ k ih => simp [pow_succ, mul_delta, ih]; ring

@[simp] theorem zpow_p (a : FDim) (n : ℤ) : (a ^ n).p = n * a.p := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp [zpow_natCast]
  · simp [zpow_neg, zpow_natCast, inv_p]

@[simp] theorem zpow_delta (a : FDim) (n : ℤ) : (a ^ n).delta = n * a.delta := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · simp [zpow_natCast]
  · simp [zpow_neg, zpow_natCast, inv_delta]

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

@[simp] theorem ScaleQ.add_val {d : FDim} (a b : ScaleQ d) : (a + b).val = a.val + b.val := rfl
@[simp] theorem ScaleQ.sub_val {d : FDim} (a b : ScaleQ d) : (a - b).val = a.val - b.val := rfl
@[simp] theorem ScaleQ.neg_val {d : FDim} (a : ScaleQ d) : (-a).val = -a.val := rfl
@[simp] theorem ScaleQ.zero_val {d : FDim} : (0 : ScaleQ d).val = 0 := rfl
@[simp] theorem ScaleQ.mul_val {d1 d2 : FDim} (a : ScaleQ d1) (b : ScaleQ d2) :
    (a * b).val = a.val * b.val := rfl
@[simp] theorem ScaleQ.div_val {d1 d2 : FDim} (a : ScaleQ d1) (b : ScaleQ d2) :
    (a / b).val = a.val / b.val := rfl
@[simp] theorem ScaleQ.smul_val {d : FDim} (r : ℝ) (a : ScaleQ d) :
    (r • a).val = r * a.val := rfl

noncomputable def ScaleQ.sq {d : FDim} (a : ScaleQ d) : ScaleQ (d * d) := a * a

@[simp] theorem ScaleQ.sq_val {d : FDim} (a : ScaleQ d) : a.sq.val = a.val * a.val := rfl

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

@[simp] theorem DimSum2.eval_mk {d1 d2 : FDim} (a : ScaleQ d1) (b : ScaleQ d2) :
    (DimSum2.mk a b).eval = a.val + b.val := rfl

def DimSum2.inl {d1 d2 : FDim} (a : ScaleQ d1) : DimSum2 d1 d2 := ⟨a, 0⟩
def DimSum2.inr {d1 d2 : FDim} (b : ScaleQ d2) : DimSum2 d1 d2 := ⟨0, b⟩

end DimSum

section DeriveFDim

/-! ## operatorKerDim and deriveFDim: derived from D operator kernel theorems

Each component of FDim is derived from algebraic properties of D_m:
- p = -(m-1): denominator power (φ-ψ)^(m-1) in D_m definition
- δ: φ↔ψ antisymmetry of the numerator N_m
-/

/-- Kernel dimension of D_m (polynomial basis annihilation count).
    D4 is special: ker(D4) = {x²}, not contiguous from degree 0. -/
def operatorKerDim : Nat → Nat
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | _ => 0

/-- Derive FDim from operator order m (for D_m):
  p = -(m-1), δ = 1 if m even else 0 -/
def deriveFDim (m : Nat) : FDim :=
  ⟨-((m - 1 : Nat) : ℤ),
   if m % 2 == 0 then 1 else 0⟩

theorem deriveFDim_D2 : deriveFDim 2 = ⟨-1, 1⟩ := by decide
theorem deriveFDim_D3 : deriveFDim 3 = ⟨-2, 0⟩ := by decide
theorem deriveFDim_D4 : deriveFDim 4 = ⟨-3, 1⟩ := by decide
theorem deriveFDim_D5 : deriveFDim 5 = ⟨-4, 0⟩ := by decide
theorem deriveFDim_D6 : deriveFDim 6 = ⟨-5, 1⟩ := by decide

/-! ### operatorKerDim justification from kernel theorems

Each value is tied to annihilation/non-annihilation theorems proven in DifferenceOperators.lean.
Changing any operatorKerDim value breaks the corresponding `rfl` below. -/

theorem operatorKerDim_2_justified :
    operatorKerDim 2 = 1 ∧
    (∀ x, x ≠ 0 → D2 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D2 id x ≠ 0) :=
  ⟨rfl, fun x hx => D2_const 1 x hx, D2_linear_ne_zero⟩

theorem operatorKerDim_3_justified :
    operatorKerDim 3 = 1 ∧
    (∀ x, x ≠ 0 → D3 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D3 id x ≠ 0) :=
  ⟨rfl, fun x hx => D3_const 1 x hx, D3_linear_ne_zero⟩

theorem operatorKerDim_4_justified :
    operatorKerDim 4 = 1 ∧
    (∀ x, x ≠ 0 → D4 (fun _ => 1) x ≠ 0) ∧
    (∀ x, x ≠ 0 → D4 id x ≠ 0) ∧
    (∀ x, x ≠ 0 → D4 (fun t => t^2) x = 0) :=
  ⟨rfl, D4_const_ne_zero, D4_linear_ne_zero, D4_quadratic⟩

theorem operatorKerDim_5_justified :
    operatorKerDim 5 = 2 ∧
    (∀ x, x ≠ 0 → D5 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D5 id x = 0) ∧
    (∀ x, x ≠ 0 → D5 (fun t => t^2) x ≠ 0) :=
  ⟨rfl, fun x hx => D5_const 1 x hx, D5_linear, D5_not_annihilate_quadratic⟩

theorem operatorKerDim_6_justified :
    operatorKerDim 6 = 3 ∧
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^2) x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t^3) x ≠ 0) :=
  ⟨rfl, fun x hx => D6_const 1 x hx, D6_linear, D6_quadratic, D6_detects_cubic⟩

/-! ### D5half FDim: half-order operator between D₅ and D₆

D5half shares D₅'s denominator structure (φ-ψ)⁴ → p = -4,
is antisymmetric → δ = 0.
Justified by D5half_const, D5half_linear_ne_zero from DifferenceOperators.lean. -/

def deriveFDim_D5half : FDim := ⟨-4, 0⟩

theorem deriveFDim_D5half_justified :
    (∀ c x, x ≠ 0 → D5half (fun _ => c) x = 0) ∧
    (∀ x, x ≠ 0 → D5half id x ≠ 0) ∧
    deriveFDim_D5half.p = -4 ∧
    deriveFDim_D5half.delta = 0 :=
  ⟨D5half_const, D5half_linear_ne_zero, rfl, rfl⟩

-- D5half has same (p,δ) as D5 but different kerDim (1 vs 2)
theorem deriveFDim_D5half_eq_D5 : deriveFDim_D5half = deriveFDim 5 := by decide
theorem deriveFDim_D5half_ne_D6 : deriveFDim_D5half ≠ deriveFDim 6 := by decide

end DeriveFDim

section DerivedDimConstants

/-- Time dimension derived from D₆: dimTime = (D₆ output)⁻¹ -/
def dimTime : FDim := (deriveFDim 6)⁻¹

theorem dimTime_eq : dimTime = ⟨5, -1⟩ := by decide

/-- Lagrangian/Hamiltonian dimension: (D₆ output)² -/
def dimLagrangian : FDim := deriveFDim 6 * deriveFDim 6

theorem dimLagrangian_eq : dimLagrangian = ⟨-10, 2⟩ := by decide

/-- D₆ output = inverse time -/
theorem D6_output_is_inverse_time : deriveFDim 6 = dimTime⁻¹ := by decide

/-- Hamiltonian = (D₆)² -/
theorem dimLagrangian_from_D6 : dimLagrangian = deriveFDim 6 * deriveFDim 6 := rfl

end DerivedDimConstants

section DerivedDimPerOperator

/-- Time dimension for each Dm: dimTimeDm = (deriveFDim m)⁻¹ -/
def dimTimeD2 : FDim := (deriveFDim 2)⁻¹

theorem dimTimeD2_eq : dimTimeD2 = ⟨1, -1⟩ := by decide

end DerivedDimPerOperator

section DimensionedOperators

/-- D₂ output with derived dimension (-1, 1) -/
noncomputable def D2_dim (f : ℂ → ℂ) (z : ℂ) : ScaleQ (deriveFDim 2) := ⟨(D2 f z).re⟩

theorem D2_dim_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) :
    (D2_dim (fun _ => c) z).val = 0 := by simp [D2_dim, D2_const c z hz]

/-- D₃ output with derived dimension (-2, 0) -/
noncomputable def D3_dim (f : ℂ → ℂ) (z : ℂ) : ScaleQ (deriveFDim 3) := ⟨(D3 f z).re⟩

theorem D3_dim_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) :
    (D3_dim (fun _ => c) z).val = 0 := by simp [D3_dim, D3_const c z hz]

/-- D₄ output with derived dimension (-3, 1) -/
noncomputable def D4_dim (f : ℂ → ℂ) (z : ℂ) : ScaleQ (deriveFDim 4) := ⟨(D4 f z).re⟩

theorem D4_dim_quadratic (z : ℂ) (hz : z ≠ 0) :
    (D4_dim (fun t => t^2) z).val = 0 := by simp [D4_dim, D4_quadratic z hz]

/-- D₅ output with derived dimension (-4, 0) -/
noncomputable def D5_dim (f : ℂ → ℂ) (z : ℂ) : ScaleQ (deriveFDim 5) := ⟨(D5 f z).re⟩

theorem D5_dim_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) :
    (D5_dim (fun _ => c) z).val = 0 := by simp [D5_dim, D5_const c z hz]

theorem D5_dim_linear (z : ℂ) (hz : z ≠ 0) :
    (D5_dim id z).val = 0 := by simp [D5_dim, D5_linear z hz]

/-- D₆ output with derived dimension (-5, 1) -/
noncomputable def D6_dim (f : ℂ → ℂ) (z : ℂ) : ScaleQ (deriveFDim 6) := ⟨(D6 f z).re⟩

theorem D6_dim_const (c : ℂ) (z : ℂ) (hz : z ≠ 0) :
    (D6_dim (fun _ => c) z).val = 0 := by simp [D6_dim, D6_const c z hz]

theorem D6_dim_linear (z : ℂ) (hz : z ≠ 0) :
    (D6_dim id z).val = 0 := by simp [D6_dim, D6_linear z hz]

theorem D6_dim_quadratic (z : ℂ) (hz : z ≠ 0) :
    (D6_dim (fun t => t^2) z).val = 0 := by simp [D6_dim, D6_quadratic z hz]

end DimensionedOperators

section StateClassDecomposition

/-! ## FDim ↔ State Function Class correspondence

Every FDim decomposes as deriveFDim(6)^a × dimTimeD2^n with (a,n) ∈ ℤ²:
- sectorPower a = (-p - δ) / 4: which D₆^a detects it
- effectiveDegree d = -p - 2δ: polynomial degree of state function representative
- detectionLevel n = d - 3a: D₂ iterations beyond D₆^a baseline -/

/-- Effective polynomial degree: d = -p - 2δ -/
def FDim.effectiveDegree (dim : FDim) : ℤ := -dim.p - 2 * dim.delta

/-- Sector power: a = (-p - δ) / 4 (D₆ exponent) -/
def FDim.sectorPower (dim : FDim) : ℤ := (-dim.p - dim.delta) / 4

/-- Detection level beyond D₆^a baseline -/
def FDim.detectionLevel (dim : FDim) : ℤ :=
  dim.effectiveDegree - 3 * dim.sectorPower

/-- Forward map: FDim → (sectorPower, detectionLevel) -/
def FDim.toSectorLevel (dim : FDim) : ℤ × ℤ :=
  (dim.sectorPower, dim.detectionLevel)

/-- Inverse map: (sectorPower a, detectionLevel n) → FDim -/
def FDim.fromSectorLevel (a n : ℤ) : FDim :=
  deriveFDim 6 ^ a * dimTimeD2 ^ n

-- effectiveDegree verified on known particles
theorem effectiveDegree_electron : dimTime⁻¹.effectiveDegree = 3 := by decide
theorem effectiveDegree_muon : (dimTime⁻¹ * dimTimeD2 ^ (11 : ℤ)).effectiveDegree = 14 := by
  decide
theorem effectiveDegree_proton : (dimTime⁻¹ * dimTimeD2 ^ (14 : ℤ)).effectiveDegree = 17 := by
  decide
theorem effectiveDegree_tau : (dimTime⁻¹ * dimTimeD2 ^ (17 : ℤ)).effectiveDegree = 20 := by
  decide
theorem effectiveDegree_W : (dimTime⁻¹ * dimTimeD2 ^ (25 : ℤ)).effectiveDegree = 28 := by decide
theorem effectiveDegree_nu3 :
    (dimLagrangian * dimTimeD2 ^ (-(32 : ℤ))).effectiveDegree = -26 := by decide

-- sectorPower verified
theorem sectorPower_D6 : (deriveFDim 6).sectorPower = 1 := by decide
theorem sectorPower_D6sq : (deriveFDim 6 * deriveFDim 6).sectorPower = 2 := by decide

-- Inverse map produces correct FDim
theorem fromSectorLevel_one_zero : FDim.fromSectorLevel 1 0 = deriveFDim 6 := by
  unfold FDim.fromSectorLevel; decide
theorem fromSectorLevel_one_11 :
    FDim.fromSectorLevel 1 11 = dimTime⁻¹ * dimTimeD2 ^ (11 : ℤ) := by
  unfold FDim.fromSectorLevel dimTime dimTimeD2; decide
theorem fromSectorLevel_one_14 :
    FDim.fromSectorLevel 1 14 = dimTime⁻¹ * dimTimeD2 ^ (14 : ℤ) := by
  unfold FDim.fromSectorLevel dimTime dimTimeD2; decide
theorem fromSectorLevel_two_neg32 :
    FDim.fromSectorLevel 2 (-32) = dimLagrangian * dimTimeD2 ^ (-(32 : ℤ)) := by
  unfold FDim.fromSectorLevel dimLagrangian dimTimeD2; decide

-- Roundtrip: toSectorLevel ∘ fromSectorLevel = id (verified on concrete values)
theorem roundtrip_electron :
    FDim.toSectorLevel (FDim.fromSectorLevel 1 0) = (1, 0) := by
  unfold FDim.toSectorLevel FDim.fromSectorLevel FDim.sectorPower
    FDim.detectionLevel FDim.effectiveDegree; decide
theorem roundtrip_muon :
    FDim.toSectorLevel (FDim.fromSectorLevel 1 11) = (1, 11) := by
  unfold FDim.toSectorLevel FDim.fromSectorLevel FDim.sectorPower
    FDim.detectionLevel FDim.effectiveDegree; decide
theorem roundtrip_proton :
    FDim.toSectorLevel (FDim.fromSectorLevel 1 14) = (1, 14) := by
  unfold FDim.toSectorLevel FDim.fromSectorLevel FDim.sectorPower
    FDim.detectionLevel FDim.effectiveDegree; decide
theorem roundtrip_nu3 :
    FDim.toSectorLevel (FDim.fromSectorLevel 2 (-32)) = (2, -32) := by
  unfold FDim.toSectorLevel FDim.fromSectorLevel FDim.sectorPower
    FDim.detectionLevel FDim.effectiveDegree; decide

end StateClassDecomposition

end FUST.Dim
