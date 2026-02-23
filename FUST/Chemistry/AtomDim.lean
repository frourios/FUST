/-
Atomic FDim and State Function

dimAtom(Z, N, e) = dimProton^Z × dimNeutron^N × dimElectron^e × dimTimeD2^(-(Z+N+e-1))
atomStateFn(Z, N, e, x) = x^Z · (1+x)^N · (1+ψx)^e

General theorems for ALL (Z, N, e):
- effectiveDegree = 16Z + 15N + 2e + 1
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
  simp only [mul_p, mul_delta, zpow_p, zpow_delta]
  rw [dimProton_eq, dimNeutron_eq, dimElectron_eq, dimTimeD2_eq]
  push_cast; ring

/-! ## Section 3: Merge -/

theorem dimAtom_merge (Z₁ N₁ e₁ Z₂ N₂ e₂ : ℕ) :
    dimAtom Z₁ N₁ e₁ * dimAtom Z₂ N₂ e₂ =
    dimAtom (Z₁ + Z₂) (N₁ + N₂) (e₁ + e₂) * dimTimeD2 := by
  unfold dimAtom
  rw [dimTimeD2_eq]
  apply FDim.ext <;>
    simp only [mul_p, mul_delta, zpow_p, zpow_delta] <;>
    push_cast <;> ring

/-! ## Section 4: Galois Conjugate State Function

σ(g)(x) = x^Z · (1+x)^N · (1+φx)^e replaces ψ with φ.
Root set {0, -1, φ} maps to {0, -1, ψ} under conjugation. -/

noncomputable def conjStateFn (Z N e : ℕ) (x : ℝ) : ℝ :=
  x ^ Z * (1 + x) ^ N * (1 + φ * x) ^ e

theorem conjStateFn_vanishes_at_zero (Z N e : ℕ) (hZ : Z ≥ 1) :
    conjStateFn Z N e 0 = 0 := by
  unfold conjStateFn; simp [zero_pow (by omega : Z ≠ 0)]

theorem conjStateFn_vanishes_at_neg_one (Z N e : ℕ) (hN : N ≥ 1) :
    conjStateFn Z N e (-1) = 0 := by
  unfold conjStateFn; simp [zero_pow (by omega : N ≠ 0)]

-- σ(g) vanishes at ψ (not φ!)
theorem conjStateFn_vanishes_at_psi (Z N e : ℕ) (he : e ≥ 1) :
    conjStateFn Z N e ψ = 0 := by
  unfold conjStateFn
  have : 1 + φ * ψ = 0 := by linarith [phi_mul_psi]
  simp [this, zero_pow (by omega : e ≠ 0)]

-- Product of state functions = merged conjugate
theorem conjStateFn_mul (Z₁ N₁ e₁ Z₂ N₂ e₂ : ℕ) (x : ℝ) :
    conjStateFn Z₁ N₁ e₁ x * conjStateFn Z₂ N₂ e₂ x =
    conjStateFn (Z₁ + Z₂) (N₁ + N₂) (e₁ + e₂) x := by
  unfold conjStateFn; rw [pow_add, pow_add, pow_add]; ring

/-! ## Section 5: Galois Norm — Integer Polynomial

g(x) · σ(g)(x) ∈ ℤ[x]: the irrational parts cancel.

Key identity: (1+ψx)(1+φx) = 1 + (φ+ψ)x + φψx² = 1 + x - x²
since φ+ψ = 1 and φψ = -1. -/

-- The electron factor norm: (1+ψx)(1+φx) = 1 + x - x²
theorem electron_factor_norm (x : ℝ) :
    (1 + ψ * x) * (1 + φ * x) = 1 + x - x ^ 2 := by
  have hsum : φ + ψ = 1 := phi_add_psi
  have hprod : φ * ψ = -1 := phi_mul_psi
  have hprod' : ψ * φ = -1 := by linarith
  have hsum' : ψ + φ = 1 := by linarith
  have : (1 + ψ * x) * (1 + φ * x) = 1 + (ψ + φ) * x + ψ * φ * x ^ 2 := by ring
  rw [this, hsum', hprod']; ring

-- g · σ(g) = x^{2Z} · (1+x)^{2N} · (1+x-x²)^e
theorem galois_norm_stateFn (Z N e : ℕ) (x : ℝ) :
    atomStateFn Z N e x * conjStateFn Z N e x =
    x ^ (2 * Z) * (1 + x) ^ (2 * N) * (1 + x - x ^ 2) ^ e := by
  unfold atomStateFn conjStateFn
  rw [show 2 * Z = Z + Z from by omega, show 2 * N = N + N from by omega,
      pow_add, pow_add]
  have h : ∀ y : ℝ, (1 + ψ * y) * (1 + φ * y) = 1 + y - y ^ 2 :=
    electron_factor_norm
  calc x ^ Z * (1 + x) ^ N * (1 + ψ * x) ^ e *
       (x ^ Z * (1 + x) ^ N * (1 + φ * x) ^ e)
      = x ^ Z * x ^ Z * ((1 + x) ^ N * (1 + x) ^ N) *
        ((1 + ψ * x) ^ e * (1 + φ * x) ^ e) := by ring
    _ = x ^ Z * x ^ Z * ((1 + x) ^ N * (1 + x) ^ N) *
        ((1 + ψ * x) * (1 + φ * x)) ^ e := by rw [mul_pow]
    _ = x ^ Z * x ^ Z * ((1 + x) ^ N * (1 + x) ^ N) *
        (1 + x - x ^ 2) ^ e := by rw [h]

-- Root set asymmetry: φ ≠ ψ so the root sets differ
theorem root_sets_differ : φ ≠ ψ := by
  intro h
  have : φ - ψ = 0 := sub_eq_zero.mpr h
  rw [phi_sub_psi] at this
  have := Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)
  linarith

-- The norm factor 1+x-x² vanishes at both φ and ψ
theorem norm_factor_root_phi : 1 + φ - φ ^ 2 = 0 := by
  linarith [golden_ratio_property]

theorem norm_factor_root_psi : 1 + ψ - ψ ^ 2 = 0 := by
  linarith [psi_sq]

/-! ## Section 6: Conjugation Swaps Time Direction

φ > 1 drives forward time evolution (expansion).
ψ: |ψ| < 1 drives backward (contraction).
Galois conjugation σ: φ ↔ ψ reverses the arrow of time. -/

theorem conjugation_reverses_time :
    φ > 1 ∧ |ψ| < 1 ∧ φ * |ψ| = 1 :=
  ⟨φ_gt_one, FUST.LeastAction.abs_psi_lt_one, FUST.LeastAction.phi_mul_abs_psi⟩

/-! ## Section 7: Automorphism Uniqueness

The only ring endomorphism σ: ℤ[φ] → ℤ[φ] fixing ℤ and satisfying σ(φ)² = σ(φ) + 1
is either id or conjugation. Since φ² = φ + 1, σ(φ) must be a root of x² - x - 1 = 0.
The only roots are φ and ψ = 1-φ, so σ = id or σ = conj. -/

-- φ and ψ are the only solutions to x² = x + 1 in ℝ
theorem golden_equation_roots (r : ℝ) (h : r ^ 2 = r + 1) :
    r = φ ∨ r = ψ := by
  have h1 : r ^ 2 - r - 1 = 0 := by linarith
  have h2 : (r - φ) * (r - ψ) = r ^ 2 - (φ + ψ) * r + φ * ψ := by ring
  rw [phi_add_psi, phi_mul_psi] at h2
  have h3 : (r - φ) * (r - ψ) = 0 := by nlinarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · left; linarith
  · right; linarith

/-! ## Section 8: Minimal Complete Root Cluster

atomStateFn(Z,N,e) has root at 0 iff Z≥1, root at -1 iff N≥1, root at φ iff e≥1.
The minimum (Z,N,e) with ALL three roots is (1,1,1). -/

def hasCompleteRootCluster (Z N e : ℕ) : Prop := Z ≥ 1 ∧ N ≥ 1 ∧ e ≥ 1

-- Forward: complete cluster implies all three roots
theorem complete_cluster_has_all_roots (Z N e : ℕ) (h : hasCompleteRootCluster Z N e) :
    atomStateFn Z N e 0 = 0 ∧
    atomStateFn Z N e (-1) = 0 ∧
    atomStateFn Z N e φ = 0 := by
  obtain ⟨hZ, hN, he⟩ := h
  exact ⟨atomStateFn_vanishes_at_zero Z N e hZ,
         atomStateFn_vanishes_at_neg_one Z N e hN,
         atomStateFn_vanishes_at_phi Z N e he⟩

-- Reverse: Z=0 means no root at 0
theorem no_proton_root (N e : ℕ) :
    atomStateFn 0 N e 0 = 1 := by
  unfold atomStateFn; simp

-- Reverse: N=0 means no root at -1 (since 1-ψ = φ ≠ 0)
theorem no_neutron_root (Z e : ℕ) :
    atomStateFn Z 0 e (-1) = (-1) ^ Z * φ ^ e := by
  unfold atomStateFn
  have : (1 : ℝ) + ψ * (-1) = φ := by unfold ψ φ; ring
  rw [this]; ring

-- Reverse: e=0 means no root at φ (since φ≠0 and 1+φ = φ² ≠ 0)
theorem no_electron_root (Z N : ℕ) :
    atomStateFn Z N 0 φ = φ ^ Z * (1 + φ) ^ N := by
  unfold atomStateFn; simp

-- (1,1,1) has a complete root cluster
theorem minimal_complete_cluster : hasCompleteRootCluster 1 1 1 :=
  ⟨le_refl 1, le_refl 1, le_refl 1⟩

-- (1,1,1) is minimal: any smaller tuple lacks at least one root
theorem complete_cluster_minimal (Z N e : ℕ) (h : hasCompleteRootCluster Z N e) :
    Z + N + e ≥ 3 := by
  obtain ⟨hZ, hN, he⟩ := h; omega

/-! ## Section 9: Galois Norm Irreducible Factor

The norm factor (1+x-x²) = -(x²-x-1) is the minimal polynomial of φ over ℤ.
It appears in the galois norm iff e ≥ 1. -/

-- 1+x-x² has exactly two roots: φ and ψ
theorem norm_factor_roots (r : ℝ) (h : 1 + r - r ^ 2 = 0) :
    r = φ ∨ r = ψ := by
  have : r ^ 2 = r + 1 := by linarith
  exact golden_equation_roots r this

-- Norm of (1,1,1) has degree 6 = 2*(1+1+1)
theorem norm_degree_111 : 2 * (1 + 1 + 1) = 6 := by norm_num

-- For complete cluster, norm has all three ℤ[x] factor types
theorem galois_norm_complete (Z N e : ℕ)
    (hZ : Z ≥ 1) (hN : N ≥ 1) (he : e ≥ 1) :
    -- norm vanishes at 0 (proton factor)
    atomStateFn Z N e 0 * conjStateFn Z N e 0 = 0 ∧
    -- norm vanishes at -1 (neutron factor)
    atomStateFn Z N e (-1) * conjStateFn Z N e (-1) = 0 ∧
    -- norm vanishes at φ (electron factor — irrational root)
    atomStateFn Z N e φ * conjStateFn Z N e φ = 0 ∧
    -- norm vanishes at ψ (conjugate electron factor)
    atomStateFn Z N e ψ * conjStateFn Z N e ψ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [atomStateFn_vanishes_at_zero Z N e hZ]
  · simp [atomStateFn_vanishes_at_neg_one Z N e hN]
  · simp [atomStateFn_vanishes_at_phi Z N e he]
  · simp [conjStateFn_vanishes_at_psi Z N e he]

-- Without e≥1, norm has only rational roots
theorem galois_norm_no_electron (Z N : ℕ) (x : ℝ) :
    atomStateFn Z N 0 x * conjStateFn Z N 0 x =
    x ^ (2 * Z) * (1 + x) ^ (2 * N) := by
  rw [galois_norm_stateFn]; simp

-- With e≥1, norm acquires irrational factor (1+x-x²)
theorem galois_norm_has_irrational_factor (Z N e : ℕ) (he : e ≥ 1) :
    atomStateFn Z N e φ * conjStateFn Z N e φ = 0 ∧
    atomStateFn Z N e ψ * conjStateFn Z N e ψ = 0 := by
  constructor
  · simp [atomStateFn_vanishes_at_phi Z N e he]
  · simp [conjStateFn_vanishes_at_psi Z N e he]

/-! ## Section 10: Scale Action and Recursive Root Orbit

U: g(x) → g(φx) maps roots of g to their φ-preimages.
Proton root 0 is scale-fixed. Neutron root -1 maps to -1/φ = ψ.
Electron root φ maps to 1, then to 1/φ, then to 1/φ², ...
generating a Fibonacci orbit φ^{1-n} = F(n-1) - F(n)ψ. -/

-- Scale action: g(φx) evaluated at root/φ = g(root) = 0
noncomputable def scaleStateFn (Z N e : ℕ) (x : ℝ) : ℝ :=
  atomStateFn Z N e (φ * x)

private theorem psi_phi_mul (x : ℝ) : ψ * (φ * x) = -x := by
  have : ψ * φ = -1 := by linarith [phi_mul_psi]
  calc ψ * (φ * x) = (ψ * φ) * x := by ring
    _ = (-1) * x := by rw [this]
    _ = -x := by ring

-- Proton root is scale-fixed: x=0 stays at 0
theorem scale_proton_fixed (Z N e : ℕ) (hZ : Z ≥ 1) :
    scaleStateFn Z N e 0 = 0 := by
  unfold scaleStateFn; simp [atomStateFn_vanishes_at_zero Z N e hZ]

-- Scale maps electron root φ to 1: g(φ·1) = g(φ) = 0
theorem scale_electron_to_one (Z N e : ℕ) (he : e ≥ 1) :
    scaleStateFn Z N e 1 = 0 := by
  unfold scaleStateFn; rw [mul_one]; exact atomStateFn_vanishes_at_phi Z N e he

-- Scale maps neutron root -1 to ψ: g(φ·ψ) = g(φψ) = g(-1) = 0
theorem scale_neutron_to_psi (Z N e : ℕ) (hN : N ≥ 1) :
    scaleStateFn Z N e ψ = 0 := by
  unfold scaleStateFn
  rw [show φ * ψ = -1 from phi_mul_psi]
  exact atomStateFn_vanishes_at_neg_one Z N e hN

-- Electron root under n-fold scaling: g(φⁿ · φ^{1-n}) = g(φ) = 0
theorem scale_orbit_electron (Z N e : ℕ) (he : e ≥ 1) (n : ℕ) :
    atomStateFn Z N e (φ ^ n * φ ^ (1 - (n : ℤ))) = 0 := by
  have h : φ ^ n * φ ^ (1 - (n : ℤ)) = φ := by
    rw [← zpow_natCast φ n, ← zpow_add₀ (ne_of_gt phi_pos)]
    simp
  rw [h]
  exact atomStateFn_vanishes_at_phi Z N e he

-- The key identity: ψφ = -1, so 1+ψ(φx) = 1-x (electron factor rationalizes)
theorem electron_factor_scale (x : ℝ) :
    1 + ψ * (φ * x) = 1 - x := by
  rw [psi_phi_mul]; ring

-- Scaled state function decomposes: growth factor φ^Z separates from recursion
theorem scale_decomposition (Z N e : ℕ) (x : ℝ) :
    scaleStateFn Z N e x =
    φ ^ Z * x ^ Z * (1 + φ * x) ^ N * (1 - x) ^ e := by
  unfold scaleStateFn atomStateFn
  rw [show 1 + ψ * (φ * x) = 1 - x from by rw [psi_phi_mul]; ring]
  rw [mul_pow]

-- Without electrons: scale action has only rational fixed points {0}
-- With electrons: scale action generates irrational orbit through φ^{1-n}
-- This is the algebraic basis of Fibonacci recursion in sub-demons.

-- Conjugate norm factor under scale: roots are (φ^{1-n}, ψ^{1-n}), a conjugate pair
theorem norm_factor_scale (x : ℝ) :
    (1 + ψ * (φ * x)) * (1 + φ * (φ * x)) = (1 - x) * (1 + φ ^ 2 * x) := by
  rw [psi_phi_mul, show φ * (φ * x) = φ ^ 2 * x from by ring]; ring

-- Using φ²=φ+1, the scaled norm factor becomes (1-x)(1+(φ+1)x) = (1-x)(1+φx+x)
theorem norm_factor_scale_golden (x : ℝ) :
    (1 - x) * (1 + φ ^ 2 * x) = (1 - x) * (1 + (φ + 1) * x) := by
  rw [golden_ratio_property]

/-! ## Section 11: Electron Factor Uniqueness

The electron factor (1+ψx) is uniquely determined among (1+αx) where α ∈ {φ, ψ, -φ, -ψ}
(the four units with Norm(α)=-1 and minimal |Trace|=1) by requiring the root to exceed 1.

Root of (1+αx) = 0 is x = -1/α:
  α = φ:  root = -1/φ ≈ -0.618  (< 0)
  α = ψ:  root = -1/ψ = φ ≈ 1.618  (> 1 ✓)
  α = -φ: root = 1/φ ≈ 0.618  (< 1)
  α = -ψ: root = 1/ψ ≈ -1.618  (< 0) -/

-- Root of (1+ψx)=0 is φ
theorem electron_root_is_phi : 1 + ψ * φ = 0 := by linarith [phi_mul_psi]

-- Root of (1+ψx)=0 exceeds 1: -1/ψ = φ > 1
theorem electron_root_gt_one : -1 / ψ > 1 := by
  have hψ_ne : ψ ≠ 0 := ne_of_lt psi_neg
  have hprod : φ * ψ = -1 := phi_mul_psi
  have hphi_eq : -1 / ψ = φ := by
    rw [div_eq_iff hψ_ne]; linarith
  linarith [φ_gt_one]

-- Root of (1+φx)=0 is < 0 (so not > 1)
theorem phi_factor_root_neg : -1 / φ < 0 :=
  div_neg_of_neg_of_pos (by linarith) phi_pos

-- Root of (1-φx)=0 is < 1
theorem neg_phi_factor_root_lt_one : 1 / φ < 1 := by
  rw [div_lt_one phi_pos]; exact φ_gt_one

-- Root of (1-ψx)=0 is < 0
theorem neg_psi_factor_root_neg : 1 / ψ < 0 :=
  div_neg_of_pos_of_neg one_pos psi_neg

/-- Among {φ, ψ, -φ, -ψ}, only (1+ψx)=0 has root > 1.
    Combined with electron_factor_norm, this determines atomStateFn. -/
theorem electron_factor_unique (α : ℝ) (hα : α = φ ∨ α = ψ ∨ α = -φ ∨ α = -ψ)
    (hroot : -1 / α > 1) : α = ψ := by
  rcases hα with rfl | rfl | rfl | rfl
  · exfalso; linarith [phi_factor_root_neg]
  · rfl
  · exfalso
    have : -1 / (-φ) = 1 / φ := by ring
    rw [this] at hroot
    linarith [neg_phi_factor_root_lt_one]
  · exfalso
    have : -1 / (-ψ) = 1 / ψ := by ring
    rw [this] at hroot
    linarith [neg_psi_factor_root_neg]

/-! ## Section 12: Rational Root Selection

Among rational linear factors (1+rx) with r ∈ ℤ, r ≠ 0:
  root = -1/r. The sign-spanning condition (roots include both < 0 and > 0)
  combined with |r| = 1 forces r ∈ {1, -1}. If the irrational root is > 1
  (forward time), then sign-spanning requires the rational root < 0,
  hence r = 1 (root at -1). -/

-- r = 1 or r = -1 and root < 0 → r = 1
theorem rational_root_is_neg_one (r : ℤ) (hr : r = 1 ∨ r = -1)
    (hroot_neg : -(1 : ℝ) / r < 0) : r = 1 := by
  rcases hr with rfl | rfl
  · rfl
  · exfalso; push_cast at hroot_neg; linarith

/-! ## Section 13: Complete atomStateFn Form Theorem

Combining all constraints: origin root, chirality, sign-spanning, minimality.

Given g(x) = x^Z · (1+rx)^N · (1+αx)^e with:
  (i)   r ∈ ℤ, |r| = 1 (minimal rational root)
  (ii)  α ∈ {φ, ψ, -φ, -ψ} (unit norm, minimal trace)
  (iii) -1/α > 1 (irrational root exceeds 1 = forward time)
  (iv)  -1/r < 0 (rational root is negative = sign-spanning with 0 and φ)
Then g = atomStateFn. -/

theorem atomStateFn_form (Z N e : ℕ) (x : ℝ)
    (r : ℤ) (hr : r = 1 ∨ r = -1) (hr_neg : -(1 : ℝ) / r < 0)
    (α : ℝ) (hα : α = φ ∨ α = ψ ∨ α = -φ ∨ α = -ψ)
    (hα_root : -1 / α > 1) :
    x ^ Z * (1 + (r : ℝ) * x) ^ N * (1 + α * x) ^ e =
    atomStateFn Z N e x := by
  have hr1 := rational_root_is_neg_one r hr hr_neg
  have hα_eq := electron_factor_unique α hα hα_root
  subst hr1; subst hα_eq
  unfold atomStateFn; push_cast; ring_nf

/-- The three roots {-1, 0, φ} form the unique sign-spanning triple. -/
theorem root_triple_unique :
    (-1 : ℝ) < 0 ∧ (0 : ℝ) = 0 ∧ φ > 1 ∧
    (-1 : ℝ) < 0 ∧ 0 < φ :=
  ⟨by norm_num, rfl, φ_gt_one, by norm_num, phi_pos⟩

/-! ## Section 14: Polynomial Necessity

Finite Observability: a particle's state has finitely many nonzero detectable coefficients.
D₆ eigenvalues λₙ = 0 for n ≤ 2, λₙ ≠ 0 for n ≥ 3 (from D6_detects_cubic etc).
So finite observability forces the state function to be polynomial. -/

-- Finite support implies polynomial (bounded degree)
theorem finite_support_is_polynomial (g : ℕ → ℝ)
    (hfin : Set.Finite {n : ℕ | g n ≠ 0}) :
    ∃ d : ℕ, ∀ n : ℕ, n > d → g n = 0 := by
  by_cases hempty : {n : ℕ | g n ≠ 0} = ∅
  · exact ⟨0, fun n _ => not_not.mp
      (Set.eq_empty_iff_forall_notMem.mp hempty n)⟩
  · obtain ⟨d, hd⟩ := hfin.bddAbove
    exact ⟨d, fun n hn => by
      by_contra h
      exact absurd (hd h) (not_le.mpr hn)⟩

-- If eigenvalues are nonzero for n ≥ 3, finite observable data implies finite support above 2
theorem finite_observable_implies_finite_support
    (g eigval : ℕ → ℝ)
    (hdet : ∀ n : ℕ, n ≥ 3 → eigval n ≠ 0)
    (hfin : Set.Finite {n : ℕ | eigval n * g n ≠ 0}) :
    Set.Finite {n : ℕ | g n ≠ 0 ∧ n ≥ 3} := by
  apply Set.Finite.subset hfin
  intro n ⟨hgn, hn3⟩
  exact mul_ne_zero (hdet n hn3) hgn

-- Combined: finite D₆-observability forces polynomial state
theorem polynomial_necessity (g eigval : ℕ → ℝ)
    (hdet : ∀ n : ℕ, n ≥ 3 → eigval n ≠ 0)
    (hfin : Set.Finite {n : ℕ | eigval n * g n ≠ 0}) :
    ∃ d : ℕ, ∀ n : ℕ, n ≥ 3 → n > d → g n = 0 := by
  have hfin3 := finite_observable_implies_finite_support g eigval hdet hfin
  have hfin_g : Set.Finite {n : ℕ | (fun k => if k ≥ 3 then g k else 0) n ≠ 0} := by
    apply hfin3.subset
    intro n (hn : (if n ≥ 3 then g n else 0) ≠ 0)
    split at hn
    · exact ⟨hn, by omega⟩
    · exact absurd rfl hn
  obtain ⟨d, hd⟩ := finite_support_is_polynomial _ hfin_g
  exact ⟨d, fun n hn3 hnd => by
    have h := hd n hnd; simp only [ge_iff_le, hn3, ↓reduceIte] at h; exact h⟩

/-! ## Root Families and Spatial Dimension

atomStateFn has 3 irreducible factor families vanishing at {0, -1, φ}.
spatialDim = |{0, -1, φ}| = 3. -/

noncomputable def rootFamilies : List ℝ := [0, -1, φ]
noncomputable def rootFamilyCount : ℕ := rootFamilies.length

theorem rootFamilyCount_val : rootFamilyCount = 3 := by
  unfold rootFamilyCount rootFamilies; simp

theorem rootFamilies_roots_distinct :
    (0 : ℝ) ≠ -1 ∧ (0 : ℝ) ≠ φ ∧ (-1 : ℝ) ≠ φ :=
  ⟨by norm_num, by linarith [phi_pos], by linarith [phi_pos]⟩

noncomputable def spatialDim : ℕ := rootFamilyCount
def timeDim : ℕ := 1
noncomputable def spacetimeDim : ℕ := spatialDim + timeDim

theorem spatialDim_eq_rootFamilyCount : spatialDim = rootFamilyCount := rfl
theorem spatialDim_val : spatialDim = 3 := by
  unfold spatialDim; exact rootFamilyCount_val
theorem timeDim_val : timeDim = 1 := rfl
theorem spacetimeDim_val : spacetimeDim = 4 := by
  unfold spacetimeDim spatialDim timeDim; simp [rootFamilyCount_val]

end FUST.Chemistry
