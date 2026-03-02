import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

theorem one_p : (1 : FDim).p = 0 := rfl
theorem one_delta : (1 : FDim).delta = 0 := rfl
theorem mul_p (a b : FDim) : (a * b).p = a.p + b.p := rfl
theorem mul_delta (a b : FDim) : (a * b).delta = a.delta + b.delta := rfl
theorem inv_p (a : FDim) : a⁻¹.p = -a.p := rfl
theorem inv_delta (a : FDim) : a⁻¹.delta = -a.delta := rfl

theorem FDim.ext {a b : FDim} (hp : a.p = b.p) (hd : a.delta = b.delta) :
    a = b := by
  cases a; cases b; simp_all

/-- Effective polynomial degree: d = -p - 2δ -/
def FDim.effectiveDegree (dim : FDim) : ℤ := -dim.p - 2 * dim.delta

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

/-! ## Backward compatibility aliases -/

abbrev deriveFDim (m : Nat) : FDim :=
  ⟨-((m - 1 : Nat) : ℤ),
   if m % 2 == 0 then 1 else 0⟩

/-! ## Sector and scale dimensions

Every particle FDim decomposes as dimSector^a × dimScale^n.
- dimSector ⟨-5, 1⟩: particle sector classifier (Fζ eigenvalue class)
- dimScale ⟨1, -1⟩: φ-power scale modulation -/

/-- Particle sector classifier: ⟨-5, 1⟩ -/
def dimSector : FDim := deriveFDim 6

/-- Scale modulation: ⟨1, -1⟩ -/
def dimScale : FDim := ⟨1, -1⟩

end FUST.Dim
