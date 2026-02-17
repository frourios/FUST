import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import FUST.DifferenceOperators

namespace FUST.Dim

/-- FUST dimension: (p, δ, τ) where p = φ-power, δ = dissipation, τ = time -/
structure FDim where
  p : ℤ
  delta : ℤ
  tau : ℤ
  deriving DecidableEq, Repr

instance : One FDim where one := ⟨0, 0, 0⟩

instance : Mul FDim where mul a b := ⟨a.p + b.p, a.delta + b.delta, a.tau + b.tau⟩

instance : Inv FDim where inv a := ⟨-a.p, -a.delta, -a.tau⟩

instance : Div FDim where div a b := a * b⁻¹

@[simp] theorem one_p : (1 : FDim).p = 0 := rfl
@[simp] theorem one_delta : (1 : FDim).delta = 0 := rfl
@[simp] theorem one_tau : (1 : FDim).tau = 0 := rfl
@[simp] theorem mul_p (a b : FDim) : (a * b).p = a.p + b.p := rfl
@[simp] theorem mul_delta (a b : FDim) : (a * b).delta = a.delta + b.delta := rfl
@[simp] theorem mul_tau (a b : FDim) : (a * b).tau = a.tau + b.tau := rfl
@[simp] theorem inv_p (a : FDim) : a⁻¹.p = -a.p := rfl
@[simp] theorem inv_delta (a : FDim) : a⁻¹.delta = -a.delta := rfl
@[simp] theorem inv_tau (a : FDim) : a⁻¹.tau = -a.tau := rfl

theorem FDim.ext {a b : FDim} (hp : a.p = b.p) (hd : a.delta = b.delta) (ht : a.tau = b.tau) :
    a = b := by
  cases a; cases b; simp_all

instance : CommGroup FDim where
  mul_assoc a b c := FDim.ext (by simp [mul_p]; omega) (by simp [mul_delta]; omega)
    (by simp [mul_tau]; omega)
  one_mul a := FDim.ext (by simp) (by simp) (by simp)
  mul_one a := FDim.ext (by simp) (by simp) (by simp)
  inv_mul_cancel a := FDim.ext (by simp) (by simp) (by simp)
  mul_comm a b := FDim.ext (by simp [mul_p]; omega) (by simp [mul_delta]; omega)
    (by simp [mul_tau]; omega)

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
- τ: 2 minus the kernel dimension of D_m on polynomial basis
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
  p = -(m-1), δ = 1 if m even else 0, τ = 2 - kerDim(D_m) -/
def deriveFDim (m : Nat) : FDim :=
  ⟨-((m - 1 : Nat) : ℤ),
   if m % 2 == 0 then 1 else 0,
   2 - (operatorKerDim m : ℤ)⟩

theorem deriveFDim_D2 : deriveFDim 2 = ⟨-1, 1, 1⟩ := by decide
theorem deriveFDim_D3 : deriveFDim 3 = ⟨-2, 0, 1⟩ := by decide
theorem deriveFDim_D4 : deriveFDim 4 = ⟨-3, 1, 1⟩ := by decide
theorem deriveFDim_D5 : deriveFDim 5 = ⟨-4, 0, 0⟩ := by decide
theorem deriveFDim_D6 : deriveFDim 6 = ⟨-5, 1, -1⟩ := by decide

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
is antisymmetric → δ = 0, and has kerDim = 1 → τ = 2-1 = 1.
Justified by D5half_const, D5half_linear_ne_zero from DifferenceOperators.lean. -/

def deriveFDim_D5half : FDim := ⟨-4, 0, 1⟩

theorem deriveFDim_D5half_justified :
    -- kerDim = 1: annihilates constants but not linear
    (∀ c x, x ≠ 0 → D5half (fun _ => c) x = 0) ∧
    (∀ x, x ≠ 0 → D5half id x ≠ 0) ∧
    -- p = -4: same denominator order as D₅
    deriveFDim_D5half.p = -4 ∧
    -- δ = 0: antisymmetric (odd-type)
    deriveFDim_D5half.delta = 0 ∧
    -- τ = 1: kerDim = 1
    deriveFDim_D5half.tau = 1 :=
  ⟨D5half_const, D5half_linear_ne_zero, rfl, rfl, rfl⟩

theorem deriveFDim_D5half_ne_D5 : deriveFDim_D5half ≠ deriveFDim 5 := by decide
theorem deriveFDim_D5half_ne_D6 : deriveFDim_D5half ≠ deriveFDim 6 := by decide

end DeriveFDim

section DerivedDimConstants

/-- Spatial projection: drop τ component (ker(D₆) = spatial subspace) -/
def FDim.spatial (d : FDim) : FDim := ⟨d.p, d.delta, 0⟩

/-- Time dimension derived from D₆: dimTime = (D₆ output)⁻¹ -/
def dimTime : FDim := (deriveFDim 6)⁻¹

theorem dimTime_eq : dimTime = ⟨5, -1, 1⟩ := by decide

/-- Length dimension: spatial projection of time -/
def dimLength : FDim := dimTime.spatial

theorem dimLength_eq : dimLength = ⟨5, -1, 0⟩ := by decide

/-- Light speed: c = l/t, derived from length and time -/
def dimLightSpeed : FDim := dimLength * dimTime⁻¹

theorem dimLightSpeed_eq : dimLightSpeed = ⟨0, 0, -1⟩ := by decide

/-- Lagrangian/Hamiltonian dimension: (D₆ output)² -/
def dimLagrangian : FDim := deriveFDim 6 * deriveFDim 6

theorem dimLagrangian_eq : dimLagrangian = ⟨-10, 2, -2⟩ := by decide

/-- D₆ output = inverse time -/
theorem D6_output_is_inverse_time : deriveFDim 6 = dimTime⁻¹ := by decide

/-- l = c · t at the dimension level -/
theorem dimLength_eq_speed_times_time : dimLength = dimLightSpeed * dimTime := by decide

/-- Hamiltonian = (D₆)² -/
theorem dimLagrangian_from_D6 : dimLagrangian = deriveFDim 6 * deriveFDim 6 := rfl

/-- Existing dimTime/dimLength/dimLightSpeed are D6-specific aliases -/
theorem dimTime_eq_dimTimeD6 : dimTime = (deriveFDim 6)⁻¹ := rfl
theorem dimLength_eq_dimLengthD6 : dimLength = ((deriveFDim 6)⁻¹).spatial := rfl

end DerivedDimConstants

section DerivedDimPerOperator

/-- Time dimension for each Dm: dimTimeDm = (deriveFDim m)⁻¹ -/
def dimTimeD2 : FDim := (deriveFDim 2)⁻¹
def dimTimeD3 : FDim := (deriveFDim 3)⁻¹
def dimTimeD4 : FDim := (deriveFDim 4)⁻¹
def dimTimeD5 : FDim := (deriveFDim 5)⁻¹

theorem dimTimeD2_eq : dimTimeD2 = ⟨1, -1, -1⟩ := by decide
theorem dimTimeD3_eq : dimTimeD3 = ⟨2, 0, -1⟩ := by decide
theorem dimTimeD4_eq : dimTimeD4 = ⟨3, -1, -1⟩ := by decide
theorem dimTimeD5_eq : dimTimeD5 = ⟨4, 0, 0⟩ := by decide

/-- Length dimension for each Dm: spatial projection of time -/
def dimLengthD2 : FDim := dimTimeD2.spatial
def dimLengthD3 : FDim := dimTimeD3.spatial
def dimLengthD4 : FDim := dimTimeD4.spatial
def dimLengthD5 : FDim := dimTimeD5.spatial

theorem dimLengthD2_eq : dimLengthD2 = ⟨1, -1, 0⟩ := by decide
theorem dimLengthD3_eq : dimLengthD3 = ⟨2, 0, 0⟩ := by decide
theorem dimLengthD4_eq : dimLengthD4 = ⟨3, -1, 0⟩ := by decide
theorem dimLengthD5_eq : dimLengthD5 = ⟨4, 0, 0⟩ := by decide

/-- Light speed for each Dm: c_m = l_m / t_m -/
def dimLightSpeedD2 : FDim := dimLengthD2 * dimTimeD2⁻¹
def dimLightSpeedD3 : FDim := dimLengthD3 * dimTimeD3⁻¹
def dimLightSpeedD4 : FDim := dimLengthD4 * dimTimeD4⁻¹
def dimLightSpeedD5 : FDim := dimLengthD5 * dimTimeD5⁻¹

theorem dimLightSpeedD2_eq : dimLightSpeedD2 = ⟨0, 0, 1⟩ := by decide
theorem dimLightSpeedD3_eq : dimLightSpeedD3 = ⟨0, 0, 1⟩ := by decide
theorem dimLightSpeedD4_eq : dimLightSpeedD4 = ⟨0, 0, 1⟩ := by decide
theorem dimLightSpeedD5_eq : dimLightSpeedD5 = ⟨0, 0, 0⟩ := by decide

/-- Dm output = inverse time for each sector -/
theorem D2_output_is_inverse_time : deriveFDim 2 = dimTimeD2⁻¹ := by decide
theorem D3_output_is_inverse_time : deriveFDim 3 = dimTimeD3⁻¹ := by decide
theorem D4_output_is_inverse_time : deriveFDim 4 = dimTimeD4⁻¹ := by decide
theorem D5_output_is_inverse_time : deriveFDim 5 = dimTimeD5⁻¹ := by decide

/-- l = c · t holds for every sector -/
theorem dimLengthD2_eq_speed_times_time : dimLengthD2 = dimLightSpeedD2 * dimTimeD2 := by decide
theorem dimLengthD3_eq_speed_times_time : dimLengthD3 = dimLightSpeedD3 * dimTimeD3 := by decide
theorem dimLengthD4_eq_speed_times_time : dimLengthD4 = dimLightSpeedD4 * dimTimeD4 := by decide
theorem dimLengthD5_eq_speed_times_time : dimLengthD5 = dimLightSpeedD5 * dimTimeD5 := by decide

end DerivedDimPerOperator

section DimensionedOperators

/-- D₂ output with derived dimension (-1, 1, 1) -/
noncomputable def D2_dim (f : ℝ → ℝ) (x : ℝ) : ScaleQ (deriveFDim 2) := ⟨D2 f x⟩

theorem D2_dim_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) :
    (D2_dim (fun _ => c) x).val = 0 := D2_const c x hx

/-- D₃ output with derived dimension (-2, 0, 1) -/
noncomputable def D3_dim (f : ℝ → ℝ) (x : ℝ) : ScaleQ (deriveFDim 3) := ⟨D3 f x⟩

theorem D3_dim_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) :
    (D3_dim (fun _ => c) x).val = 0 := D3_const c x hx

/-- D₄ output with derived dimension (-3, 1, 1) -/
noncomputable def D4_dim (f : ℝ → ℝ) (x : ℝ) : ScaleQ (deriveFDim 4) := ⟨D4 f x⟩

theorem D4_dim_quadratic (x : ℝ) (hx : x ≠ 0) :
    (D4_dim (fun t => t^2) x).val = 0 := D4_quadratic x hx

/-- D₅ output with derived dimension (-4, 0, 0) -/
noncomputable def D5_dim (f : ℝ → ℝ) (x : ℝ) : ScaleQ (deriveFDim 5) := ⟨D5 f x⟩

theorem D5_dim_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) :
    (D5_dim (fun _ => c) x).val = 0 := D5_const c x hx

theorem D5_dim_linear (x : ℝ) (hx : x ≠ 0) :
    (D5_dim id x).val = 0 := D5_linear x hx

/-- D₆ output with derived dimension (-5, 1, -1) -/
noncomputable def D6_dim (f : ℝ → ℝ) (x : ℝ) : ScaleQ (deriveFDim 6) := ⟨D6 f x⟩

theorem D6_dim_const (c : ℝ) (x : ℝ) (hx : x ≠ 0) :
    (D6_dim (fun _ => c) x).val = 0 := D6_const c x hx

theorem D6_dim_linear (x : ℝ) (hx : x ≠ 0) :
    (D6_dim id x).val = 0 := D6_linear x hx

theorem D6_dim_quadratic (x : ℝ) (hx : x ≠ 0) :
    (D6_dim (fun t => t^2) x).val = 0 := D6_quadratic x hx

end DimensionedOperators

section DimLagrangians

/-- Lagrangian dimension for each Dm: (Dm output)² -/
def dimLagrangianD2 : FDim := deriveFDim 2 * deriveFDim 2
def dimLagrangianD3 : FDim := deriveFDim 3 * deriveFDim 3
def dimLagrangianD4 : FDim := deriveFDim 4 * deriveFDim 4
def dimLagrangianD5 : FDim := deriveFDim 5 * deriveFDim 5

theorem dimLagrangianD2_eq : dimLagrangianD2 = ⟨-2, 2, 2⟩ := by decide
theorem dimLagrangianD3_eq : dimLagrangianD3 = ⟨-4, 0, 2⟩ := by decide
theorem dimLagrangianD4_eq : dimLagrangianD4 = ⟨-6, 2, 2⟩ := by decide
theorem dimLagrangianD5_eq : dimLagrangianD5 = ⟨-8, 0, 0⟩ := by decide

end DimLagrangians

section DimStructuralComparison

/-- D5 time = D5 length: τ = 0 collapses time-space distinction -/
theorem dimTimeD5_eq_dimLengthD5 : dimTimeD5 = dimLengthD5 := by decide

/-- D5 light speed is dimensionless (⟨0,0,0⟩ = 1) -/
theorem dimLightSpeedD5_eq_one : dimLightSpeedD5 = 1 := by decide

/-- D2,D3,D4 share τ = -1 in time dimension -/
theorem dimTimeD2_tau : dimTimeD2.tau = -1 := by decide
theorem dimTimeD3_tau : dimTimeD3.tau = -1 := by decide
theorem dimTimeD4_tau : dimTimeD4.tau = -1 := by decide

/-- D6 has τ = 1, opposite to D2,D3,D4 -/
theorem dimTime_tau : dimTime.tau = 1 := by decide

/-- D5 has τ = 0: no time direction -/
theorem dimTimeD5_tau : dimTimeD5.tau = 0 := by decide

/-- All dimTimeDm are distinct -/
theorem dimTime_all_distinct :
    dimTimeD2 ≠ dimTimeD3 ∧ dimTimeD2 ≠ dimTimeD4 ∧ dimTimeD2 ≠ dimTimeD5 ∧
    dimTimeD2 ≠ dimTime ∧ dimTimeD3 ≠ dimTimeD4 ∧ dimTimeD3 ≠ dimTimeD5 ∧
    dimTimeD3 ≠ dimTime ∧ dimTimeD4 ≠ dimTimeD5 ∧ dimTimeD4 ≠ dimTime ∧
    dimTimeD5 ≠ dimTime := by decide

/-- D2,D3,D4 light speeds are equal (⟨0,0,1⟩) but differ from D5 and D6 -/
theorem dimLightSpeed_D234_agree :
    dimLightSpeedD2 = dimLightSpeedD3 ∧
    dimLightSpeedD3 = dimLightSpeedD4 := by decide

theorem dimLightSpeed_D234_ne_D5 : dimLightSpeedD2 ≠ dimLightSpeedD5 := by decide
theorem dimLightSpeed_D234_ne_D6 : dimLightSpeedD2 ≠ dimLightSpeed := by decide
theorem dimLightSpeed_D5_ne_D6 : dimLightSpeedD5 ≠ dimLightSpeed := by decide

/-- D2,D3,D4 light speed τ = 1, D6 light speed τ = -1: opposite sign -/
theorem dimLightSpeed_tau_opposite :
    dimLightSpeedD2.tau = -dimLightSpeed.tau := by decide

end DimStructuralComparison

end FUST.Dim
