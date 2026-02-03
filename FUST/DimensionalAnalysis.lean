import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs

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

section DeriveFDim

/-- Derive FDim from operator order m (for D_m):
  p = -(m-1): denominator power of (φ-ψ)
  δ = 1 if m even (antisymmetric coefficients), 0 if odd (symmetric)
  τ = -1 if m = 6 (terminal: ker saturated), 0 otherwise -/
def deriveFDim (m : Nat) : FDim :=
  ⟨-((m - 1 : Nat) : ℤ),
   if m % 2 == 0 then 1 else 0,
   if m == 6 then -1 else 0⟩

theorem deriveFDim_D2 : deriveFDim 2 = ⟨-1, 1, 0⟩ := by decide
theorem deriveFDim_D3 : deriveFDim 3 = ⟨-2, 0, 0⟩ := by decide
theorem deriveFDim_D4 : deriveFDim 4 = ⟨-3, 1, 0⟩ := by decide
theorem deriveFDim_D5 : deriveFDim 5 = ⟨-4, 0, 0⟩ := by decide
theorem deriveFDim_D6 : deriveFDim 6 = ⟨-5, 1, -1⟩ := by decide

end DeriveFDim

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

/-- Dimensionless ratio quantity (§4.3: coupling constants as Count/Count) -/
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

section DerivedDimConstants

/-- Spatial projection: drop τ component (ker(D₆) = spatial subspace) -/
def FDim.spatial (d : FDim) : FDim := ⟨d.p, d.delta, 0⟩

/-- Time dimension derived from D₆: dimTime = (D₆ output)⁻¹ -/
def dimTime : FDim := (deriveFDim 6)⁻¹

theorem dimTime_eq : dimTime = ⟨5, -1, 1⟩ := by decide

/-- Length dimension: spatial projection of time (§5: l = (√5)⁵/C₃, τ=0) -/
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

end DerivedDimConstants

end FUST.Dim
