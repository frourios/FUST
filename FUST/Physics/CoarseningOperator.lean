import FUST.Physics.MassGap

/-!
# Galois Coarsening: Canonical Projections from ℤ[φ,ζ₆]

Fζ eigenvalues live in ℤ[φ,ζ₆] with Galois group Gal(ℚ(√5,√-3)/ℚ) ≅ (ℤ/2)².
The three nontrivial Galois elements define canonical coarsening projections
with NO free parameters:

- N_σ: ℤ[φ,ζ₆] → ℤ[ζ₆]  (remove scale φ, keep gauge ζ₆)
- N_τ: ℤ[φ,ζ₆] → ℤ[φ]   (remove gauge ζ₆, keep scale φ)
- N:   ℤ[φ,ζ₆] → ℤ       (remove both)

These are the UNIQUE coarsenings determined by the algebraic structure itself.
-/

namespace FUST.Coarsening

open FUST FUST.FζOperator FUST.DζOperator FUST.FrourioAlgebra

/-! ## Eigenvalue dimension system in ℤ[φ,ζ₆]

Fζ eigenvalue = α(n)·AF_coeff + β(n) where α,β ∈ ℤ[φ], AF_coeff = -2+4ζ₆.
Mass formula: |eigenvalue|² = β² + 12α² (AF_coeff = 2i√3). -/

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

/-- ψ^n in ℤ[φ] via Galois conjugation: ψ^n = conj(φ^n) -/
def psiPowNat (n : ℕ) : GoldenInt := GoldenInt.conj (GoldenInt.phiPowNat n)

/-- psiPowNat n corresponds to ψ^n in ℝ -/
theorem psiPowNat_toReal (n : ℕ) : GoldenInt.toReal (psiPowNat n) = ψ ^ n := by
  induction n with
  | zero =>
    simp only [psiPowNat, GoldenInt.phiPowNat, pow_zero]
    rw [conj_one]; exact toReal_one
  | succ n ih =>
    simp only [psiPowNat] at ih ⊢
    have : GoldenInt.phiPowNat (n + 1) =
        GoldenInt.mul GoldenInt.phi (GoldenInt.phiPowNat n) := rfl
    rw [this, FrourioAlgebra.conj_mul, toReal_mul,
      conj_phi_toReal, ih, pow_succ, mul_comm]

/-- Φ_A eigenvalue on z^n in ℤ[φ] -/
def phiA_goldenInt (n : ℕ) : GoldenInt :=
  let p3n := GoldenInt.phiPowNat (3 * n)
  let p2n := GoldenInt.phiPowNat (2 * n)
  let pn := GoldenInt.phiPowNat n
  let q_n := psiPowNat n
  let q2n := psiPowNat (2 * n)
  let q3n := psiPowNat (3 * n)
  p3n + (⟨-4, 0⟩ : GoldenInt) * p2n + ⟨3, 1⟩ * pn +
  (⟨-4, 1⟩ : GoldenInt) * q_n + ⟨4, 0⟩ * q2n + (⟨-1, 0⟩ : GoldenInt) * q3n

/-- Φ_S_int eigenvalue on z^n in ℤ[φ] -/
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

/-! ## Active/Kernel mode classification -/

def isActiveMode (n : ℕ) : Bool := n % 6 == 1 || n % 6 == 5

def isKernelMode (n : ℕ) : Bool := !isActiveMode n

/-! ## Composite state multiplication -/

def compositeEigenvalue (x y : GoldenEisensteinInt) : GoldenEisensteinInt :=
  GoldenEisensteinInt.mul x y

/-- AF_coeff² = -12 in ℤ[ζ₆] ⊂ ℤ[φ,ζ₆] -/
theorem AF_coeff_sq :
    GoldenEisensteinInt.mul GoldenEisensteinInt.AF_coeff_gei
      GoldenEisensteinInt.AF_coeff_gei = ⟨-12, 0, 0, 0⟩ := by decide

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

/-! ## Bridge: Fζ evaluation ↔ GEI eigenvalue ↔ massSq -/

private theorem toReal_hadd (x y : GoldenInt) :
    GoldenInt.toReal (x + y) =
    GoldenInt.toReal x + GoldenInt.toReal y :=
  toReal_add x y

private theorem toReal_hmul (x y : GoldenInt) :
    GoldenInt.toReal (x * y) =
    GoldenInt.toReal x * GoldenInt.toReal y :=
  toReal_mul x y

theorem phiA_goldenInt_toReal (n : ℕ) :
    GoldenInt.toReal (phiA_goldenInt n) =
    φ ^ (3 * n) - 4 * φ ^ (2 * n) + (3 + φ) * φ ^ n -
    (4 - φ) * ψ ^ n + 4 * ψ ^ (2 * n) -
    ψ ^ (3 * n) := by
  simp only [phiA_goldenInt]
  simp only [toReal_hadd, toReal_hmul,
    phiPowNat_toReal, psiPowNat_toReal]
  simp only [GoldenInt.toReal]
  push_cast; ring

theorem phiS_goldenInt_toReal (n : ℕ) :
    GoldenInt.toReal (phiS_goldenInt n) =
    10 * φ ^ (2 * n) + (21 - 2 * φ) * φ ^ n - 50 +
    (9 + 2 * φ) * ψ ^ n + 10 * ψ ^ (2 * n) := by
  simp only [phiS_goldenInt]
  simp only [toReal_hadd, toReal_hmul,
    phiPowNat_toReal, psiPowNat_toReal]
  simp only [GoldenInt.toReal]
  push_cast; ring

/-- Fζ(z^{6k+1})(1) = toComplex(eigenFζ_mod1 k) -/
theorem Fζ_eigenvalue_bridge_mod1 (k : ℕ) :
    FζOperator.Fζ (fun w => w ^ (6 * k + 1)) 1 =
    GoldenEisensteinInt.toComplex (eigenFζ_mod1 k) := by
  rw [FζOperator.Fζ_eigenvalue_mod6_1]
  simp only [one_pow, mul_one]
  simp only [eigenFζ_mod1, fromChannels]
  rw [GoldenEisensteinInt.toComplex_add,
    GoldenEisensteinInt.toComplex_mul,
    GoldenEisensteinInt.AF_coeff_gei_eq,
    toComplex_ofGoldenInt, toComplex_ofGoldenInt]
  rw [toReal_hmul, toReal_hmul,
    phiA_goldenInt_toReal, phiS_goldenInt_toReal]
  simp only [GoldenInt.toReal]
  push_cast
  have hψc : (↑ψ : ℂ) = 1 - ↑φ := by
    linear_combination phi_add_psi_complex
  rw [hψc]; ring

/-- Fζ(z^{6k+5})(1) = toComplex(eigenFζ_mod5 k) -/
theorem Fζ_eigenvalue_bridge_mod5 (k : ℕ) :
    FζOperator.Fζ (fun w => w ^ (6 * k + 5)) 1 =
    GoldenEisensteinInt.toComplex (eigenFζ_mod5 k) := by
  rw [FζOperator.Fζ_eigenvalue_mod6_5]
  simp only [one_pow, mul_one]
  simp only [eigenFζ_mod5, fromChannels]
  rw [GoldenEisensteinInt.toComplex_add,
    GoldenEisensteinInt.toComplex_mul,
    GoldenEisensteinInt.AF_coeff_gei_eq,
    toComplex_ofGoldenInt, toComplex_ofGoldenInt]
  rw [toReal_hmul, toReal_hmul,
    phiA_goldenInt_toReal, phiS_goldenInt_toReal]
  simp only [GoldenInt.toReal]
  push_cast
  have hψc : (↑ψ : ℂ) = 1 - ↑φ := by
    linear_combination phi_add_psi_complex
  rw [hψc]; ring

/-- |Fζ(z^{6k+1})(1)|² = massSq(eigenFζ_mod1 k) -/
theorem Fζ_normSq_eq_massSq_mod1 (k : ℕ) :
    Complex.normSq
      (FζOperator.Fζ (fun w => w ^ (6 * k + 1)) 1) =
    massSq (eigenFζ_mod1 k) := by
  rw [Fζ_eigenvalue_bridge_mod1]; rfl

/-- |Fζ(z^{6k+5})(1)|² = massSq(eigenFζ_mod5 k) -/
theorem Fζ_normSq_eq_massSq_mod5 (k : ℕ) :
    Complex.normSq
      (FζOperator.Fζ (fun w => w ^ (6 * k + 5)) 1) =
    massSq (eigenFζ_mod5 k) := by
  rw [Fζ_eigenvalue_bridge_mod5]; rfl

/-- |δ(z^{6j+3}, z^{6k+4})(1)|² = massSq (matter emergence) -/
theorem emergence_massSq_matter (j k : ℕ) :
    Complex.normSq
      (FζOperator.derivDefect (fun w => w ^ (6 * j + 3))
        (fun w => w ^ (6 * k + 4)) 1) =
    massSq (eigenFζ_mod1 (j + k + 1)) := by
  rw [FζOperator.emergence_normSq_matter,
    show 6 * j + 3 + (6 * k + 4) = 6 * (j + k + 1) + 1
      from by omega,
    Fζ_normSq_eq_massSq_mod1]

/-- |δ(z^{6j+2}, z^{6k+3})(1)|² = massSq (antimatter emergence) -/
theorem emergence_massSq_antimatter (j k : ℕ) :
    Complex.normSq
      (FζOperator.derivDefect (fun w => w ^ (6 * j + 2))
        (fun w => w ^ (6 * k + 3)) 1) =
    massSq (eigenFζ_mod5 (j + k)) := by
  rw [FζOperator.emergence_normSq_antimatter,
    show 6 * j + 2 + (6 * k + 3) = 6 * (j + k) + 5
      from by omega,
    Fζ_normSq_eq_massSq_mod5]

theorem factorization_assoc (x y z : GoldenEisensteinInt) :
    compositeEigenvalue (compositeEigenvalue x y) z =
    compositeEigenvalue x (compositeEigenvalue y z) := by
  unfold compositeEigenvalue
  exact GoldenEisensteinInt.mul_assoc' x y z

theorem composite_comm (x y : GoldenEisensteinInt) :
    compositeEigenvalue x y = compositeEigenvalue y x := by
  unfold compositeEigenvalue
  exact GoldenEisensteinInt.mul_comm' x y

/-! ## Eigenvalue for each active mode as ℤ[φ,ζ₆] element -/

/-- Fζ eigenvalue for active mode n -/
def eigenGEI (n : ℕ) : GoldenEisensteinInt :=
  if n % 6 = 1 then eigenFζ_mod1 (n / 6)
  else if n % 6 = 5 then eigenFζ_mod5 (n / 6)
  else GoldenEisensteinInt.zero

theorem eigenGEI_kernel {n : ℕ} (h1 : n % 6 ≠ 1) (h5 : n % 6 ≠ 5) :
    eigenGEI n = GoldenEisensteinInt.zero := by
  unfold eigenGEI; simp [h1, h5]

/-! ## N_τ projection: ℤ[φ,ζ₆] → ℤ[φ] (remove gauge, keep scale) -/

/-- τ-coarsening of mode n: eigenvalue projected to ℤ[φ] -/
def tauCoarsen (n : ℕ) : GoldenInt :=
  GoldenEisensteinInt.tauNorm (eigenGEI n)

theorem tauCoarsen_kernel {n : ℕ} (h1 : n % 6 ≠ 1) (h5 : n % 6 ≠ 5) :
    tauCoarsen n = ⟨0, 0⟩ := by
  unfold tauCoarsen
  rw [eigenGEI_kernel h1 h5]
  unfold GoldenEisensteinInt.tauNorm GoldenEisensteinInt.zero; simp

/-! ## N_σ projection: ℤ[φ,ζ₆] → ℤ[ζ₆] (remove scale, keep gauge) -/

/-- σ-coarsening of mode n: eigenvalue projected to ℤ[ζ₆] as (p, q) = p + q·ζ₆ -/
def sigmaCoarsen (n : ℕ) : ℤ × ℤ :=
  GoldenEisensteinInt.sigmaNorm (eigenGEI n)

theorem sigmaCoarsen_kernel {n : ℕ} (h1 : n % 6 ≠ 1) (h5 : n % 6 ≠ 5) :
    sigmaCoarsen n = (0, 0) := by
  unfold sigmaCoarsen
  rw [eigenGEI_kernel h1 h5]
  unfold GoldenEisensteinInt.sigmaNorm GoldenEisensteinInt.zero; simp

/-! ## Full norm N: ℤ[φ,ζ₆] → ℤ (remove all structure) -/

/-- Full Galois norm of mode n -/
def fullNorm (n : ℕ) : ℤ :=
  GoldenEisensteinInt.norm (eigenGEI n)

theorem fullNorm_kernel {n : ℕ} (h1 : n % 6 ≠ 1) (h5 : n % 6 ≠ 5) :
    fullNorm n = 0 := by
  unfold fullNorm
  rw [eigenGEI_kernel h1 h5]
  unfold GoldenEisensteinInt.norm GoldenEisensteinInt.tauNorm
    GoldenEisensteinInt.zero GoldenInt.norm; simp

/-! ## N_τ preserves mass formula: |λ|² = toReal(N_τ(λ)) -/

noncomputable def eigenNormSq (n : ℕ) : ℝ :=
  if n % 6 = 1 then massSq (eigenFζ_mod1 (n / 6))
  else if n % 6 = 5 then massSq (eigenFζ_mod5 (n / 6))
  else 0

theorem eigenNormSq_nonneg (n : ℕ) : 0 ≤ eigenNormSq n := by
  unfold eigenNormSq
  split
  · exact Complex.normSq_nonneg _
  · split
    · exact Complex.normSq_nonneg _
    · exact le_refl _

/-! ## Coarsening on spectral coefficients -/

/-- Apply τ-coarsening to spectrum: project each eigenvalue to ℤ[φ] -/
noncomputable def coarsenTau (c : ℕ → ℂ) : ℕ → ℂ :=
  fun n =>
    if isActiveMode n then c n * ↑(GoldenInt.toReal (tauCoarsen n))
    else 0

/-- Apply σ-coarsening to spectrum: project each eigenvalue to ℤ[ζ₆] -/
noncomputable def coarsenSigma (c : ℕ → ℂ) : ℕ → ℂ :=
  fun n =>
    if isActiveMode n then
      let sc := sigmaCoarsen n
      c n * (↑sc.1 + ↑sc.2 * GoldenEisensteinInt.toComplex GoldenEisensteinInt.zeta6_gei)
    else 0

/-- Apply full norm coarsening: project each eigenvalue to ℤ -/
def coarsenFull (c : ℕ → ℂ) : ℕ → ℂ :=
  fun n =>
    if isActiveMode n then c n * ↑(fullNorm n)
    else 0

/-! ## Kernel preservation -/

theorem coarsenTau_kernel (c : ℕ → ℂ) {n : ℕ}
    (h : isActiveMode n = false) : coarsenTau c n = 0 := by
  simp [coarsenTau, h]

theorem coarsenFull_kernel (c : ℕ → ℂ) {n : ℕ}
    (h : isActiveMode n = false) : coarsenFull c n = 0 := by
  simp [coarsenFull, h]

/-! ## Linearity -/

theorem coarsenTau_add (c₁ c₂ : ℕ → ℂ) :
    coarsenTau (fun n => c₁ n + c₂ n) =
    fun n => coarsenTau c₁ n + coarsenTau c₂ n := by
  funext n; simp [coarsenTau]; split <;> ring

theorem coarsenFull_add (c₁ c₂ : ℕ → ℂ) :
    coarsenFull (fun n => c₁ n + c₂ n) =
    fun n => coarsenFull c₁ n + coarsenFull c₂ n := by
  funext n; simp [coarsenFull]; split <;> ring

theorem coarsenTau_smul (a : ℂ) (c : ℕ → ℂ) :
    coarsenTau (fun n => a * c n) = fun n => a * coarsenTau c n := by
  funext n; simp [coarsenTau]; split <;> ring

theorem coarsenFull_smul (a : ℂ) (c : ℕ → ℂ) :
    coarsenFull (fun n => a * c n) = fun n => a * coarsenFull c n := by
  funext n; simp [coarsenFull]; split <;> ring

/-! ## Galois coarsening hierarchy

The three projections form a commutative diagram:
  ℤ[φ,ζ₆] --N_σ--> ℤ[ζ₆]
     |                  |
    N_τ              N_{ℤ[ζ₆]}
     |                  |
     v                  v
   ℤ[φ]  --N_{ℤ[φ]}--> ℤ
-/

theorem fullNorm_factors (n : ℕ) :
    fullNorm n = GoldenInt.norm (tauCoarsen n) := rfl

end FUST.Coarsening
