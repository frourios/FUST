/-
Atomic FDim and State Function

dimAtom(Z, N, e) = dimProton^Z × dimNeutron^N × dimElectron^e × dimTimeD2^(-(Z+N+e-1))
atomStateFn(Z, N, e, x) = x^Z · (1+x)^N · (1+ψx)^e

General theorems for ALL (Z, N, e):
- effectiveDegree = 16Z + 15N + 2e + 1
- isPureSector (universally true)
- merge: dimAtom(A) * dimAtom(B) = dimAtom(A+B) * dimTimeD2
-/

import FUST.Chemistry.HydrogenIsotopes
import FUST.Physics.ParticleSpectrum

namespace FUST.Chemistry

open FUST FUST.Dim

/-! ## Polynomial State Function

g(x) = x^Z · (1+x)^N · (1+ψx)^e where ψ = (1-√5)/2.
Roots at {0, -1, φ} encode proton, neutron, electron factors. -/

noncomputable def atomStateFn (Z N e : ℕ) (x : ℝ) : ℝ :=
  x ^ Z * (1 + x) ^ N * (1 + ψ * x) ^ e

theorem atomStateFn_vanishes_at_zero (Z N e : ℕ) (hZ : Z ≥ 1) :
    atomStateFn Z N e 0 = 0 := by
  unfold atomStateFn; simp [zero_pow (by omega : Z ≠ 0)]

theorem atomStateFn_vanishes_at_neg_one (Z N e : ℕ) (hN : N ≥ 1) :
    atomStateFn Z N e (-1) = 0 := by
  unfold atomStateFn; simp [zero_pow (by omega : N ≠ 0)]

theorem atomStateFn_vanishes_at_phi (Z N e : ℕ) (he : e ≥ 1) :
    atomStateFn Z N e φ = 0 := by
  unfold atomStateFn
  have : 1 + ψ * φ = 0 := by linarith [phi_mul_psi]
  simp [this, zero_pow (by omega : e ≠ 0)]

-- Product of state functions = state function of merged species
theorem atomStateFn_mul (Z₁ N₁ e₁ Z₂ N₂ e₂ : ℕ) (x : ℝ) :
    atomStateFn Z₁ N₁ e₁ x * atomStateFn Z₂ N₂ e₂ x =
    atomStateFn (Z₁ + Z₂) (N₁ + N₂) (e₁ + e₂) x := by
  unfold atomStateFn; rw [pow_add, pow_add, pow_add]; ring

/-! ## FDim Constructor -/

def dimAtom (Z N e : ℕ) : FDim :=
  dimProton ^ (Z : ℤ) * dimNeutron ^ (N : ℤ) *
  dimElectron ^ (e : ℤ) * dimTimeD2 ^ (-(↑Z + ↑N + ↑e - 1 : ℤ))

def dimNucleus (Z N : ℕ) : FDim := dimAtom Z N 0

/-! ## Section 1: Consistency with HydrogenIsotopes -/

theorem dimAtom_eq_hydrogenIon : dimAtom 1 0 0 = dimHydrogenIon := by decide
theorem dimAtom_eq_hydrogenAtom : dimAtom 1 0 1 = dimHydrogenAtom := by decide
theorem dimAtom_eq_hydrideAnion : dimAtom 1 0 2 = dimHydrideAnion := by decide
theorem dimAtom_eq_deuteronIon : dimAtom 1 1 0 = dimDeuteronIon := by decide
theorem dimAtom_eq_deuteriumAtom : dimAtom 1 1 1 = dimDeuteriumAtom := by decide
theorem dimAtom_eq_tritonIon : dimAtom 1 2 0 = dimTritonIon := by decide
theorem dimAtom_eq_tritiumAtom : dimAtom 1 2 1 = dimTritiumAtom := by decide

/-! ## Section 2: General Effective Degree

effectiveDegree = 16Z + 15N + 2e + 1 for all (Z, N, e). -/

theorem dimAtom_effectiveDegree (Z N e : ℕ) :
    (dimAtom Z N e).effectiveDegree = 16 * Z + 15 * N + 2 * e + 1 := by
  unfold dimAtom FDim.effectiveDegree
  simp only [mul_delta, mul_tau, zpow_delta, zpow_tau]
  rw [dimProton_eq, dimNeutron_eq, dimElectron_eq, dimTimeD2_eq]
  push_cast; ring

/-! ## Section 3: Universal Pure Sector

All dimAtom lie on p + 3δ - 2τ = 0. -/

theorem dimAtom_isPureSector (Z N e : ℕ) :
    (dimAtom Z N e).isPureSector := by
  unfold dimAtom FDim.isPureSector
  simp only [mul_p, mul_delta, mul_tau, zpow_p, zpow_delta, zpow_tau]
  rw [dimProton_eq, dimNeutron_eq, dimElectron_eq, dimTimeD2_eq]
  push_cast; ring

/-! ## Section 4: Merge

Two species merging releases one dimTimeD2 binding defect. -/

theorem dimAtom_merge (Z₁ N₁ e₁ Z₂ N₂ e₂ : ℕ) :
    dimAtom Z₁ N₁ e₁ * dimAtom Z₂ N₂ e₂ =
    dimAtom (Z₁ + Z₂) (N₁ + N₂) (e₁ + e₂) * dimTimeD2 := by
  unfold dimAtom
  rw [dimTimeD2_eq]
  apply FDim.ext <;>
    simp only [mul_p, mul_delta, mul_tau, zpow_p, zpow_delta, zpow_tau] <;>
    push_cast <;> ring

end FUST.Chemistry
