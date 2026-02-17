import FUST.Physics.ParticleSpectrum
import FUST.Physics.MassRatios
import FUST.DifferenceOperators
import FUST.DimensionalAnalysis
import Mathlib.Data.Nat.Choose.Basic

/-!
# Nuclear and Atomic Structure from D-operators

Derives shell structure, quark charges, and magic numbers
from ker(D₅) = 2 (spin degeneracy) and ker(D₆) = 3 (spatial dimension).
-/

namespace FUST.Nuclear

open FUST FUST.Dim

/-! ## Section 1: Kernel Dimensions from D-operators -/

-- dim ker(D₅) = 2: D5 annihilates {1, x} but not x²
abbrev spinDegeneracy : ℕ := operatorKerDim 5

theorem spinDegeneracy_eq : spinDegeneracy = 2 := rfl

theorem spinDegeneracy_justified :
    spinDegeneracy = 2 ∧
    (∀ x, x ≠ 0 → D5 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D5 id x = 0) ∧
    (∀ x, x ≠ 0 → D5 (fun t => t ^ 2) x ≠ 0) :=
  operatorKerDim_5_justified

-- dim ker(D₆) = 3 = spatialDim: D6 annihilates {1, x, x²} but not x³
theorem spatialDim_from_kerD6 :
    WaveEquation.spatialDim = operatorKerDim 6 := rfl

theorem spatialDim_justified :
    WaveEquation.spatialDim = 3 ∧
    (∀ x, x ≠ 0 → D6 (fun _ => 1) x = 0) ∧
    (∀ x, x ≠ 0 → D6 id x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t ^ 2) x = 0) ∧
    (∀ x, x ≠ 0 → D6 (fun t => t ^ 3) x ≠ 0) :=
  ⟨rfl, (operatorKerDim_6_justified).2.1,
   (operatorKerDim_6_justified).2.2.1,
   (operatorKerDim_6_justified).2.2.2.1,
   (operatorKerDim_6_justified).2.2.2.2⟩

/-! ## Section 2: Harmonic Polynomial Dimensions

In d dimensions, spherical harmonics of degree l have dimension
C(l+d-1, d-1) - C(l+d-3, d-1). For d = spatialDim = 3, this simplifies to 2l+1.
-/

-- d=3 specialization: harmonicDim(l) = 2l+1
abbrev harmonicDim (l : ℕ) : ℕ := 2 * l + 1

-- C(l+2, 2) = (2l+1) + C(l, 2): spherical harmonic count in d=3
theorem binomial_harmonicDim (l : ℕ) :
    Nat.choose (l + 2) 2 = 2 * l + 1 + Nat.choose l 2 := by
  induction l with
  | zero => decide
  | succ k ih =>
    have step1 : Nat.choose (k + 3) 2 = Nat.choose (k + 2) 1 + Nat.choose (k + 2) 2 := by
      rw [show (k + 3) = (k + 2).succ from rfl, show (2 : ℕ) = 1 + 1 from rfl]
      exact Nat.choose_succ_succ (k + 2) 1
    have step2 : Nat.choose (k + 2) 1 = k + 2 := Nat.choose_one_right (k + 2)
    have step3 : Nat.choose (k + 1) 2 = k + Nat.choose k 2 := by
      rw [show (k + 1) = k.succ from rfl, show (2 : ℕ) = 1 + 1 from rfl]
      rw [Nat.choose_succ_succ k 1, Nat.choose_one_right]
    rw [show k + 1 + 2 = k + 3 from by ring] at *
    omega

-- Σ_{l=0}^{n-1} (2l+1) = n²
theorem harmonicDim_sum (n : ℕ) :
    (Finset.range n).sum harmonicDim = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [harmonicDim]
    ring

/-! ## Section 3: Subshell Structure -/

structure Subshell where
  n : ℕ
  l : ℕ
  deriving DecidableEq, Repr, BEq

-- Max electrons per subshell = spinDegeneracy × harmonicDim(l) = 2(2l+1)
def Subshell.maxElectrons (sh : Subshell) : ℕ := spinDegeneracy * harmonicDim sh.l

theorem subshell_capacity_values :
  Subshell.maxElectrons ⟨1, 0⟩ = 2 ∧
  Subshell.maxElectrons ⟨2, 1⟩ = 6 ∧
  Subshell.maxElectrons ⟨3, 2⟩ = 10 ∧
  Subshell.maxElectrons ⟨4, 3⟩ = 14 := ⟨rfl, rfl, rfl, rfl⟩

-- Shell capacity = spinDegeneracy × n² = 2n²
def shellCapacity (n : ℕ) : ℕ := spinDegeneracy * n ^ 2

theorem shellCapacity_eq_sum (n : ℕ) :
    shellCapacity n = spinDegeneracy * (Finset.range n).sum harmonicDim := by
  simp [shellCapacity, harmonicDim_sum]

theorem shellCapacity_values :
  shellCapacity 1 = 2 ∧ shellCapacity 2 = 8 ∧
  shellCapacity 3 = 18 ∧ shellCapacity 4 = 32 := ⟨rfl, rfl, rfl, rfl⟩

/-! ## Section 4: Period Structure

Madelung (n+l) rule: periods pair up as shellCapacity(⌈p/2⌉).
This is an empirical ordering rule, not derived from D-structure.
-/

def periodLength (p : ℕ) : ℕ := shellCapacity ((p + 2) / 2)

theorem periodLength_values :
  periodLength 1 = 2 ∧ periodLength 2 = 8 ∧ periodLength 3 = 8 ∧
  periodLength 4 = 18 ∧ periodLength 5 = 18 ∧
  periodLength 6 = 32 ∧ periodLength 7 = 32 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem total_elements_118 :
  periodLength 1 + periodLength 2 + periodLength 3 + periodLength 4 +
  periodLength 5 + periodLength 6 + periodLength 7 = 118 := rfl

/-! ## Section 5: Quark Charge from D₃ Structure -/

-- Charge denominator = C(spatialDim, 2) from D₃ structure
abbrev chargeDenom : ℕ := Nat.choose WaveEquation.spatialDim 2

theorem chargeDenom_eq : chargeDenom = 3 := rfl

inductive QuarkFlavor where | up | down
  deriving DecidableEq, Repr

def QuarkFlavor.chargeNum : QuarkFlavor → ℤ
  | .up => 2
  | .down => -1

theorem quark_charge_gap :
  QuarkFlavor.chargeNum .up - QuarkFlavor.chargeNum .down = chargeDenom := rfl

-- chargeNum is uniquely determined by proton=chargeDenom, neutron=0, 3 quarks each
theorem chargeNum_unique (u d : ℤ) (hp : 2 * u + d = chargeDenom) (hn : u + 2 * d = 0) :
    u = QuarkFlavor.chargeNum .up ∧ d = QuarkFlavor.chargeNum .down := by
  have : (chargeDenom : ℤ) = 3 := by decide
  simp only [QuarkFlavor.chargeNum, this] at *
  constructor <;> omega

theorem up_charge_allowed :
  QuarkFlavor.chargeNum .up ∈ ParticleSpectrum.allowedChargeNumerators := by decide
theorem down_charge_allowed :
  QuarkFlavor.chargeNum .down ∈ ParticleSpectrum.allowedChargeNumerators := by decide

def baryonCharge (quarks : List QuarkFlavor) : ℤ :=
  quarks.foldl (fun acc q => acc + q.chargeNum) 0

def protonQuarks : List QuarkFlavor := [.up, .up, .down]
def neutronQuarks : List QuarkFlavor := [.up, .down, .down]

theorem proton_quark_count : protonQuarks.length = WaveEquation.spatialDim := rfl
theorem neutron_quark_count : neutronQuarks.length = WaveEquation.spatialDim := rfl
theorem proton_charge : baryonCharge protonQuarks = chargeDenom := rfl
theorem neutron_charge : baryonCharge neutronQuarks = 0 := rfl

theorem proton_composition_unique (n_up n_down : ℕ)
    (hcount : n_up + n_down = WaveEquation.spatialDim)
    (hcharge : n_up * (QuarkFlavor.chargeNum .up) + n_down * (QuarkFlavor.chargeNum .down) =
      chargeDenom) :
    n_up = 2 ∧ n_down = 1 := by
  have hd : (chargeDenom : ℤ) = 3 := by decide
  simp only [WaveEquation.spatialDim, QuarkFlavor.chargeNum, hd] at *; omega

theorem neutron_composition_unique (n_up n_down : ℕ)
    (hcount : n_up + n_down = WaveEquation.spatialDim)
    (hcharge : n_up * (QuarkFlavor.chargeNum .up) + n_down * (QuarkFlavor.chargeNum .down) = 0) :
    n_up = 1 ∧ n_down = 2 := by
  simp only [WaveEquation.spatialDim, QuarkFlavor.chargeNum] at *
  omega

/-! ## Section 5b: Connection to Mass Derivations

chargeDenom = C(3,2) appears in protonMass normalization C(3,2)+C(5,2) = 13.
m_u/m_d = C(2,2)/2 = 1/2 (from QuarkMassRatios) determines the isospin splitting.
-/

-- C(3,2) in protonMass denominator is the charge denominator
theorem chargeDenom_in_baryon_normalization :
    (chargeDenom : ℕ) + Nat.choose 5 2 = 13 := rfl

-- Neutron has one extra down quark → m_n - m_p ∝ m_d - m_u
theorem neutron_down_excess :
    neutronQuarks.count .down - protonQuarks.count .down = 1 ∧
    protonQuarks.count .up - neutronQuarks.count .up = 1 := by decide

-- m_u/m_d = 1/2 from MassRatios (D₂ isospin)
theorem quark_mass_ratio_from_isospin :
    muMdRatio.val = 1 / 2 := muMdRatio_val

-- Splitting connects to isospin: φ² = φ + C(2,2) where C(2,2) = m_u/m_d numerator
theorem splitting_isospin_connection :
    neutronMass.val - protonMass.val =
    electronMass.val * (φ + Nat.choose 2 2) * 29 / 30 :=
  splitting_from_isospin

-- β-decay: neutron → proton + electron + ν̄ₑ is kinematically allowed
theorem beta_decay_from_quark_structure :
    neutronMass.val > protonMass.val + electronMass.val :=
  beta_decay_possible

/-! ## Section 6: Nuclear Shell Model

Nuclei are identified by (Z, N) via DTagged .protonNum / .neutronNum
in DiscreteTag.lean. No separate Nucleus structure needed.
Mass number A = Z + N = atomDegree Z N 0 (ion degree, defined in OxygenIsotopes). -/

-- 3D harmonic oscillator degeneracy: C(N + spatialDim - 1, spatialDim - 1)
def hoDegeneracy (N : ℕ) : ℕ :=
  Nat.choose (N + WaveEquation.spatialDim - 1) (WaveEquation.spatialDim - 1)

theorem hoDeg_formula (N : ℕ) : hoDegeneracy N = Nat.choose (N + 2) 2 := rfl

theorem hoDeg_values :
  hoDegeneracy 0 = 1 ∧ hoDegeneracy 1 = 3 ∧
  hoDegeneracy 2 = 6 ∧ hoDegeneracy 3 = 10 ∧
  hoDegeneracy 4 = 15 ∧ hoDegeneracy 5 = 21 := by decide

def hoLevelCapacity (N : ℕ) : ℕ := spinDegeneracy * hoDegeneracy N

theorem hoCapacity_values :
  hoLevelCapacity 0 = 2 ∧ hoLevelCapacity 1 = 6 ∧
  hoLevelCapacity 2 = 12 ∧ hoLevelCapacity 3 = 20 ∧
  hoLevelCapacity 4 = 30 ∧ hoLevelCapacity 5 = 42 := by decide

-- Cumulative: spinDegeneracy × C(N + spatialDim, spatialDim)
def hoMagic (N : ℕ) : ℕ :=
  spinDegeneracy * Nat.choose (N + WaveEquation.spatialDim) WaveEquation.spatialDim

theorem hoMagic_values :
  hoMagic 0 = 2 ∧ hoMagic 1 = 8 ∧ hoMagic 2 = 20 ∧
  hoMagic 3 = 40 ∧ hoMagic 4 = 70 ∧ hoMagic 5 = 112 := by decide

theorem hoMagic_cumulative :
  hoMagic 0 = hoLevelCapacity 0 ∧
  hoMagic 1 = hoLevelCapacity 0 + hoLevelCapacity 1 ∧
  hoMagic 2 = hoLevelCapacity 0 + hoLevelCapacity 1 + hoLevelCapacity 2 ∧
  hoMagic 3 = hoLevelCapacity 0 + hoLevelCapacity 1 + hoLevelCapacity 2 +
    hoLevelCapacity 3 := by decide

/-! ## Section 7: Intruder State Correction

Spin-orbit coupling promotes the j = l + 1/2 stretched state from shell N (l = N)
into the gap below. Degeneracy = 2j + 1 = spinDegeneracy × (N + 1).
This is empirical: the spin-orbit strength ordering is not derived from D-structure.
-/

def intruderDeg (N : ℕ) : ℕ := spinDegeneracy * (N + 1)

theorem intruderDeg_eq_harmonicDim_succ (N : ℕ) :
    intruderDeg N = harmonicDim N + 1 := by
  simp [intruderDeg, harmonicDim, spinDegeneracy, operatorKerDim]; ring

theorem intruderDeg_values :
  intruderDeg 0 = 2 ∧ intruderDeg 1 = 4 ∧ intruderDeg 2 = 6 ∧
  intruderDeg 3 = 8 ∧ intruderDeg 4 = 10 ∧ intruderDeg 5 = 12 ∧
  intruderDeg 6 = 14 := by decide

-- N ≤ 2: pure harmonic oscillator; N ≥ 3: spin-orbit intruder correction (empirical)
def nuclearMagic : ℕ → ℕ
  | 0 => hoMagic 0
  | 1 => hoMagic 1
  | 2 => hoMagic 2
  | n + 3 => hoMagic (n + 2) + intruderDeg (n + 3)

theorem nuclearMagic_values :
  nuclearMagic 0 = 2 ∧ nuclearMagic 1 = 8 ∧ nuclearMagic 2 = 20 ∧
  nuclearMagic 3 = 28 ∧ nuclearMagic 4 = 50 ∧ nuclearMagic 5 = 82 ∧
  nuclearMagic 6 = 126 := by decide

-- N ≤ 2 magic numbers are pure harmonic oscillator (no empirical input)
theorem low_magic_from_ho :
  nuclearMagic 0 = hoMagic 0 ∧
  nuclearMagic 1 = hoMagic 1 ∧
  nuclearMagic 2 = hoMagic 2 := ⟨rfl, rfl, rfl⟩

theorem magic_even : ∀ n, n < 7 → nuclearMagic n % 2 = 0 := by decide

-- Predicate: n is a magic number
def IsMagic (n : ℕ) : Prop := ∃ i, i < 7 ∧ nuclearMagic i = n

-- Double-magic: both Z and N are magic numbers
def IsDoubleMagic (Z N : ℕ) : Prop := IsMagic Z ∧ IsMagic N

theorem He4_double_magic : IsDoubleMagic 2 2 :=
  ⟨⟨0, by omega, rfl⟩, ⟨0, by omega, rfl⟩⟩
theorem O16_double_magic : IsDoubleMagic 8 8 :=
  ⟨⟨1, by omega, rfl⟩, ⟨1, by omega, rfl⟩⟩
theorem Ca40_double_magic : IsDoubleMagic 20 20 :=
  ⟨⟨2, by omega, rfl⟩, ⟨2, by omega, rfl⟩⟩
theorem Ca48_double_magic : IsDoubleMagic 20 28 :=
  ⟨⟨2, by omega, rfl⟩, ⟨3, by omega, rfl⟩⟩
theorem Ni78_double_magic : IsDoubleMagic 28 50 :=
  ⟨⟨3, by omega, rfl⟩, ⟨4, by omega, rfl⟩⟩
theorem Sn132_double_magic : IsDoubleMagic 50 82 :=
  ⟨⟨4, by omega, rfl⟩, ⟨5, by omega, rfl⟩⟩
theorem Pb208_double_magic : IsDoubleMagic 82 126 :=
  ⟨⟨5, by omega, rfl⟩, ⟨6, by omega, rfl⟩⟩

theorem He4_mass_number : 2 + 2 = 4 := rfl
theorem Pb208_mass_number : 82 + 126 = 208 := rfl
theorem iron_peak_near_magic : nuclearMagic 3 = 28 := rfl

/-! ## Section 8: Summary -/

theorem nuclear_structure_from_D_operators :
  -- Derived from D-operators
  spinDegeneracy = operatorKerDim 5 ∧
  WaveEquation.spatialDim = operatorKerDim 6 ∧
  -- Subshell capacities: spinDeg × harmonicDim
  Subshell.maxElectrons ⟨1, 0⟩ = 2 ∧
  Subshell.maxElectrons ⟨2, 1⟩ = 6 ∧
  Subshell.maxElectrons ⟨3, 2⟩ = 10 ∧
  Subshell.maxElectrons ⟨4, 3⟩ = 14 ∧
  -- 7 periods = 118 elements (Madelung ordering is empirical)
  periodLength 1 + periodLength 2 + periodLength 3 + periodLength 4 +
  periodLength 5 + periodLength 6 + periodLength 7 = 118 ∧
  -- Pure harmonic oscillator magic numbers (derived)
  hoMagic 0 = 2 ∧ hoMagic 1 = 8 ∧ hoMagic 2 = 20 ∧
  -- Quark charge denominator = C(spatialDim, 2)
  chargeDenom = Nat.choose WaveEquation.spatialDim 2 := by decide

end FUST.Nuclear
