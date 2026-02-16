/-
Discrete Dimensional Analysis — Core Types and Constants

DTag/DTagged: phantom-typed ℕ wrapper preventing cross-kind arithmetic.
Only imports Physics.Nuclear (no Chemistry dependency) so every Chemistry
file can import this without circular dependencies.
-/

import FUST.Physics.Nuclear
import FUST.DimensionalAnalysis

namespace FUST.DiscreteTag

open FUST FUST.Dim

/-! ## DTag and DTagged -/

inductive DTag where
  | protonNum    -- Z (proton count)
  | neutronNum   -- N (neutron count)
  | degree       -- deg = Z + N + e
  | kerDim       -- dim ker(D_m)
  | count        -- discrete counting quantity
  | deltaDeg     -- degree difference
  deriving DecidableEq, Repr

structure DTagged (tag : DTag) where
  val : ℕ
  deriving DecidableEq, Repr

instance (t : DTag) : Add (DTagged t) where add a b := ⟨a.val + b.val⟩
instance (t : DTag) : Sub (DTagged t) where sub a b := ⟨a.val - b.val⟩
instance (t : DTag) : LE (DTagged t) where le a b := a.val ≤ b.val
instance (t : DTag) : LT (DTagged t) where lt a b := a.val < b.val

@[simp] theorem DTagged.add_val {t : DTag} (a b : DTagged t) :
    (a + b).val = a.val + b.val := rfl
@[simp] theorem DTagged.sub_val {t : DTag} (a b : DTagged t) :
    (a - b).val = a.val - b.val := rfl

/-! ## Cross-Tag Conversion Functions -/

def mkDegree (z : DTagged .protonNum) (n : DTagged .neutronNum)
    (e : DTagged .protonNum) : DTagged .degree :=
  ⟨z.val + n.val + e.val⟩

def kerToCount (k : DTagged .kerDim) : DTagged .count := ⟨k.val⟩
def countMul (a b : DTagged .count) : DTagged .count := ⟨a.val * b.val⟩
def countPow (base exp : DTagged .count) : DTagged .count := ⟨base.val ^ exp.val⟩
def degDiff (a b : DTagged .degree) : DTagged .deltaDeg := ⟨a.val - b.val⟩
def scaleZ (n : ℕ) (z : DTagged .protonNum) : DTagged .protonNum := ⟨n * z.val⟩
def scaleN (n : ℕ) (z : DTagged .neutronNum) : DTagged .neutronNum := ⟨n * z.val⟩

/-! ## Kernel Dimension Constants (from D-operator kernel structure) -/

def spinDeg_t : DTagged .kerDim := ⟨Nuclear.spinDegeneracy⟩
def spatialDim_t : DTagged .kerDim := ⟨WaveEquation.spatialDim⟩

theorem spinDeg_t_val : spinDeg_t.val = 2 := rfl
theorem spatialDim_t_val : spatialDim_t.val = 3 := rfl

/-! ## Literal Atomic Constants (Chemistry-independent) -/

def hydrogenZ_t : DTagged .protonNum := ⟨1⟩
def heliumZ_t : DTagged .protonNum := ⟨2⟩

theorem hydrogenZ_t_val : hydrogenZ_t.val = 1 := rfl
theorem heliumZ_t_val : heliumZ_t.val = 2 := rfl

/-! ## Counting Quantities (derived from kernel dimensions) -/

def baseCount_t : DTagged .count := countPow ⟨2⟩ (kerToCount spinDeg_t)
def codonLength_t : DTagged .count := kerToCount spatialDim_t
def codonCount_t : DTagged .count := countPow baseCount_t codonLength_t
def aminoAcidCount_t : DTagged .count := ⟨Nuclear.nuclearMagic 2⟩
def stopCodonCount_t : DTagged .count := kerToCount spatialDim_t
def senseCodonCount_t : DTagged .count := codonCount_t - stopCodonCount_t

theorem baseCount_t_val : baseCount_t.val = 4 := rfl
theorem codonLength_t_val : codonLength_t.val = 3 := rfl
theorem codonCount_t_val : codonCount_t.val = 64 := rfl
theorem aminoAcidCount_t_val : aminoAcidCount_t.val = 20 := rfl
theorem stopCodonCount_t_val : stopCodonCount_t.val = 3 := rfl
theorem senseCodonCount_t_val : senseCodonCount_t.val = 61 := rfl

/-! ## H-bond Counts -/

def AT_hbonds_t : DTagged .count := kerToCount spinDeg_t
def GC_hbonds_t : DTagged .count := kerToCount spatialDim_t

theorem AT_hbonds_t_val : AT_hbonds_t.val = 2 := rfl
theorem GC_hbonds_t_val : GC_hbonds_t.val = 3 := rfl

/-! ## He = nuclearMagic(0) -/

theorem heliumZ_eq_magic0 :
    heliumZ_t = ⟨Nuclear.nuclearMagic 0⟩ := rfl

/-! ## FDim–DTag Coherence

FDim.tau encodes kernel dimensions: τ(D_m) = 2 - operatorKerDim(m).
DTag.kerDim values are extracted from FDim via: kerDim = 2 - τ. -/

theorem spinDeg_from_FDim :
    spinDeg_t.val = (2 - (deriveFDim 5).tau).toNat := by decide

theorem spatialDim_from_FDim :
    spatialDim_t.val = (2 - (deriveFDim 6).tau).toNat := by decide

theorem kerDim_eq_operatorKerDim :
    spinDeg_t.val = operatorKerDim 5 ∧
    spatialDim_t.val = operatorKerDim 6 := ⟨rfl, rfl⟩

/-! ## Reduction to Three Axioms (Basic constants only)

Every discrete constant reduces to:
  1. operatorKerDim(5) = 2, 2. operatorKerDim(6) = 3, 3. hydrogenZ = 1. -/

theorem reduce_baseCount :
    baseCount_t.val = 2 ^ Dim.operatorKerDim 5 := rfl

theorem reduce_codonCount :
    codonCount_t.val =
    2 ^ (Dim.operatorKerDim 5 * Dim.operatorKerDim 6) := rfl

theorem reduce_aminoAcidCount :
    aminoAcidCount_t.val = Nuclear.nuclearMagic 2 := rfl

/-! ## CountQ Embedding

CountQ (from DimensionalAnalysis.lean) is an untagged ℕ wrapper.
DTagged refines it: every CountQ embeds into DTagged .count. -/

def fromCountQ (c : Dim.CountQ) : DTagged .count := ⟨c.val⟩
def toCountQ (d : DTagged .count) : Dim.CountQ := ⟨d.val⟩

theorem countQ_roundtrip (c : Dim.CountQ) :
    (toCountQ (fromCountQ c)).val = c.val := rfl

theorem dtagged_roundtrip (d : DTagged .count) :
    (fromCountQ (toCountQ d)).val = d.val := rfl

theorem countQ_add_compat (a b : Dim.CountQ) :
    fromCountQ (a + b) = fromCountQ a + fromCountQ b := rfl

/-! ## Summary -/

theorem discrete_tag_coherence :
    spinDeg_t.val = Dim.operatorKerDim 5 ∧
    spatialDim_t.val = Dim.operatorKerDim 6 ∧
    baseCount_t.val = 2 ^ Dim.operatorKerDim 5 ∧
    codonCount_t.val = 2 ^ (Dim.operatorKerDim 5 * Dim.operatorKerDim 6) ∧
    aminoAcidCount_t.val = Nuclear.nuclearMagic 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end FUST.DiscreteTag
