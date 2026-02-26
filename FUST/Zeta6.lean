/-
ζ₆-based difference operator for Dynamics.
ζ₆ = e^{iπ/3}: compact (|ζ₆|=1, ζ₆·ζ₆'=+1), contrasting FUST's φψ=-1.
ζ₆_N6 has ker = {1, z, z²} and detects z³, same as FUST D₆ but via rotation.
-/
import FUST.DifferenceOperators
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace FUST.Zeta6

open Complex FUST

attribute [local ext] Complex.ext

/-! ## ζ₆ definition and basic properties -/

/-- ζ₆ = e^{iπ/3} = (1 + i√3)/2 -/
noncomputable def ζ₆ : ℂ := ⟨1/2, Real.sqrt 3 / 2⟩

/-- ζ₆' = e^{-iπ/3} = (1 - i√3)/2 -/
noncomputable def ζ₆' : ℂ := ⟨1/2, -(Real.sqrt 3 / 2)⟩

lemma sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- ζ₆ + ζ₆' = 1 (same trace as φ + ψ = 1) -/
theorem zeta6_add_conj : ζ₆ + ζ₆' = 1 := by ext <;> simp [ζ₆, ζ₆']; ring

/-- ζ₆ · ζ₆' = +1 (contrast with φψ = -1) -/
theorem zeta6_mul_conj : ζ₆ * ζ₆' = 1 := by
  ext <;> simp [ζ₆, ζ₆', mul_re, mul_im]
  · have h := sqrt3_sq; nlinarith
  · ring

/-- ζ₆² = ζ₆ - 1 (contrast with φ² = φ + 1) -/
theorem zeta6_sq : ζ₆ ^ 2 = ζ₆ - 1 := by
  ext <;> simp [ζ₆, sq, mul_re, mul_im]
  · have h := sqrt3_sq; nlinarith
  · ring

/-- ζ₆³ = -1 -/
theorem zeta6_cubed : ζ₆ ^ 3 = -1 := by
  have : ζ₆ ^ 3 = ζ₆ ^ 2 * ζ₆ := by ring
  rw [this, zeta6_sq]
  ext <;> simp [ζ₆, mul_re, mul_im]
  · have h := sqrt3_sq; nlinarith
  · ring

/-- ζ₆⁶ = 1 -/
theorem zeta6_pow_six : ζ₆ ^ 6 = 1 := by
  have : ζ₆ ^ 6 = (ζ₆ ^ 3) ^ 2 := by ring
  rw [this, zeta6_cubed]; norm_num

/-- |ζ₆| = 1 (compact: isometric action) -/
theorem norm_zeta6 : ‖ζ₆‖ = 1 :=
  norm_eq_one_of_pow_eq_one zeta6_pow_six (by norm_num)

/-- ζ₆ ≠ 0 -/
theorem zeta6_ne_zero : ζ₆ ≠ 0 := by
  intro h
  have h1 : ‖ζ₆‖ = 0 := by rw [h, norm_zero]
  linarith [norm_zeta6]

/-- ζ₆⁴ = -ζ₆ -/
private theorem zeta6_pow_four : ζ₆ ^ 4 = -ζ₆ := by
  have : ζ₆ ^ 4 = ζ₆ ^ 3 * ζ₆ := by ring
  rw [this, zeta6_cubed]; ring

/-- ζ₆⁵ = 1 - ζ₆ -/
private theorem zeta6_pow_five : ζ₆ ^ 5 = 1 - ζ₆ := by
  have : ζ₆ ^ 5 = ζ₆ ^ 3 * ζ₆ ^ 2 := by ring
  rw [this, zeta6_cubed, zeta6_sq]; ring

/-! ## ζ₆_N6: DFT mode-3 projection -/

/-- ζ₆_N6 numerator: Σ_{k=0}^{5} (-1)^k f(ζ₆^k · z) -/
noncomputable def ζ₆_N6 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z - f (ζ₆ * z) + f (ζ₆ ^ 2 * z) - f (ζ₆ ^ 3 * z) +
  f (ζ₆ ^ 4 * z) - f (ζ₆ ^ 5 * z)

/-- ζ₆_D6: normalized DFT projection -/
noncomputable def ζ₆_D6 (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ζ₆_N6 f z / 6

/-! ## Kernel: {1, z, z²} -/

/-- Alternating sum of 6th roots of unity vanishes -/
theorem alternating_root_sum :
    (1 : ℂ) - ζ₆ + ζ₆ ^ 2 - ζ₆ ^ 3 + ζ₆ ^ 4 - ζ₆ ^ 5 = 0 := by
  rw [zeta6_cubed, zeta6_sq, zeta6_pow_four, zeta6_pow_five]; ring

/-- ζ₆_N6 annihilates constants -/
theorem ζ₆_N6_const (c : ℂ) (z : ℂ) : ζ₆_N6 (fun _ => c) z = 0 := by
  unfold ζ₆_N6; ring

/-- ζ₆_N6 annihilates z -/
theorem ζ₆_N6_linear (z : ℂ) : ζ₆_N6 id z = 0 := by
  simp only [ζ₆_N6, id_eq]
  have : z - ζ₆ * z + ζ₆ ^ 2 * z - ζ₆ ^ 3 * z + ζ₆ ^ 4 * z - ζ₆ ^ 5 * z =
    (1 - ζ₆ + ζ₆ ^ 2 - ζ₆ ^ 3 + ζ₆ ^ 4 - ζ₆ ^ 5) * z := by ring
  rw [this, alternating_root_sum, zero_mul]

/-- Alternating sum of squared 6th roots vanishes -/
private theorem alternating_sq_root_sum :
    (1 : ℂ) - ζ₆ ^ 2 + ζ₆ ^ 4 - ζ₆ ^ 6 + ζ₆ ^ 8 - ζ₆ ^ 10 = 0 := by
  have h6 := zeta6_pow_six
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    have : ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    rw [this, h6, one_mul]
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    have : ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    rw [this, h6, one_mul]
  rw [h6, h8, h10]; ring

/-- ζ₆_N6 annihilates z² -/
theorem ζ₆_N6_quadratic (z : ℂ) : ζ₆_N6 (fun w => w ^ 2) z = 0 := by
  simp only [ζ₆_N6]
  have : z ^ 2 - (ζ₆ * z) ^ 2 + (ζ₆ ^ 2 * z) ^ 2 - (ζ₆ ^ 3 * z) ^ 2 +
    (ζ₆ ^ 4 * z) ^ 2 - (ζ₆ ^ 5 * z) ^ 2 =
    (1 - ζ₆ ^ 2 + ζ₆ ^ 4 - ζ₆ ^ 6 + ζ₆ ^ 8 - ζ₆ ^ 10) * z ^ 2 := by ring
  rw [this, alternating_sq_root_sum, zero_mul]

/-! ## Detection: z³ -/

/-- Alternating sum of cubed 6th roots = 6 -/
private theorem alternating_cube_root_sum :
    (1 : ℂ) - ζ₆ ^ 3 + ζ₆ ^ 6 - ζ₆ ^ 9 + ζ₆ ^ 12 - ζ₆ ^ 15 = 6 := by
  have h3 := zeta6_cubed
  have h6 := zeta6_pow_six
  have h9 : ζ₆ ^ 9 = -1 := by
    have : ζ₆ ^ 9 = ζ₆ ^ 6 * ζ₆ ^ 3 := by ring
    rw [this, h6, one_mul, h3]
  have h12 : ζ₆ ^ 12 = 1 := by
    have : ζ₆ ^ 12 = (ζ₆ ^ 6) ^ 2 := by ring
    rw [this, h6]; norm_num
  have h15 : ζ₆ ^ 15 = -1 := by
    have : ζ₆ ^ 15 = ζ₆ ^ 12 * ζ₆ ^ 3 := by ring
    rw [this, h12, one_mul, h3]
  rw [h3, h6, h9, h12, h15]; norm_num

/-- ζ₆_N6[z³] = 6z³ -/
theorem ζ₆_N6_cubic (z : ℂ) : ζ₆_N6 (fun w => w ^ 3) z = 6 * z ^ 3 := by
  simp only [ζ₆_N6]
  have : z ^ 3 - (ζ₆ * z) ^ 3 + (ζ₆ ^ 2 * z) ^ 3 - (ζ₆ ^ 3 * z) ^ 3 +
    (ζ₆ ^ 4 * z) ^ 3 - (ζ₆ ^ 5 * z) ^ 3 =
    (1 - ζ₆ ^ 3 + ζ₆ ^ 6 - ζ₆ ^ 9 + ζ₆ ^ 12 - ζ₆ ^ 15) * z ^ 3 := by ring
  rw [this, alternating_cube_root_sum]

/-- ζ₆_D6[z³] = z³ -/
theorem ζ₆_D6_cubic (z : ℂ) : ζ₆_D6 (fun w => w ^ 3) z = z ^ 3 := by
  simp only [ζ₆_D6, ζ₆_N6_cubic]; field_simp

/-- ζ₆_D6 detects z³ -/
theorem ζ₆_D6_detects_cubic (z : ℂ) (hz : z ≠ 0) :
    ζ₆_D6 (fun w => w ^ 3) z ≠ 0 := by
  rw [ζ₆_D6_cubic]; exact pow_ne_zero 3 hz

/-! ## Kernel dimension = 3 -/

/-- ker(ζ₆_N6) ⊇ {1, z, z²} -/
theorem ζ₆_N6_kernel :
    (∀ c z, ζ₆_N6 (fun _ => c) z = 0) ∧
    (∀ z, ζ₆_N6 id z = 0) ∧
    (∀ z, ζ₆_N6 (fun w => w ^ 2) z = 0) :=
  ⟨ζ₆_N6_const, ζ₆_N6_linear, ζ₆_N6_quadratic⟩

/-! ## ζ₆ - ζ₆' properties -/

/-- ζ₆ - ζ₆' = i√3 -/
theorem zeta6_sub_conj : ζ₆ - ζ₆' = ⟨0, Real.sqrt 3⟩ := by
  ext <;> simp [ζ₆, ζ₆']

/-- ζ₆ - ζ₆' ≠ 0 -/
theorem zeta6_sub_conj_ne_zero : ζ₆ - ζ₆' ≠ 0 := by
  rw [zeta6_sub_conj]
  intro h
  have him := congr_arg Complex.im h
  simp at him

/-- ζ₆' ≠ 0 -/
theorem zeta6'_ne_zero : ζ₆' ≠ 0 := by
  intro h; have := congr_arg Complex.re h
  simp [ζ₆'] at this

/-- ζ₆' = ζ₆⁻¹ -/
theorem conj_eq_inv : ζ₆' = ζ₆⁻¹ :=
  eq_inv_of_mul_eq_one_right zeta6_mul_conj

/-- |ζ₆'| = 1 -/
theorem norm_zeta6' : ‖ζ₆'‖ = 1 := by
  rw [conj_eq_inv, norm_inv, norm_zeta6, inv_one]

/-- ζ₆' = starRingEnd ℂ ζ₆ (complex conjugate) -/
theorem conj_eq_starRingEnd : ζ₆' = starRingEnd ℂ ζ₆ := by
  ext <;> simp [ζ₆, ζ₆']

/-- (ζ₆ - ζ₆')² = -3 (discriminant of t² - t + 1) -/
theorem zeta6_sub_conj_sq : (ζ₆ - ζ₆') ^ 2 = -3 := by
  rw [zeta6_sub_conj]
  have : (⟨0, Real.sqrt 3⟩ : ℂ) ^ 2 = ⟨-(Real.sqrt 3 ^ 2), 0⟩ := by
    ext <;> simp [sq, mul_re, mul_im]
  rw [this, sqrt3_sq]; ext <;> simp

/-- ζ₆² - ζ₆ + 1 = 0 (6th cyclotomic polynomial) -/
theorem zeta6_minimal_poly : ζ₆ ^ 2 - ζ₆ + 1 = 0 := by
  have h := zeta6_sq
  have : ζ₆ ^ 2 - ζ₆ + 1 = (ζ₆ - 1) - ζ₆ + 1 := by rw [h]
  rw [this]; ring

/-! ## ζ₆ convolution filters: AFNum and SymNum

Anti-Fibonacci sequence: C_n = C_{n-1} - C_{n-2}, C_0=0, C_1=1.
Period 6: [0, 1, 1, 0, -1, -1]. Recurrence mirrors ζ₆²=ζ₆-1.

AFNum: antisymmetric filter with coefficients C_k = [0,1,1,0,-1,-1]
SymNum: symmetric filter with coefficients 2Re(ζ₆^k) = [2,1,-1,-2,-1,1]

For s ≡ 1 mod 6: AFNum selects AF_coeff = 2i√3, SymNum selects 6.
For s ≡ 5 mod 6: AFNum selects -AF_coeff, SymNum selects 6.
For s ≡ 0,2,3,4 mod 6: both filters annihilate. -/

/-- Anti-Fibonacci numerator: Σ C_k · g(ζ₆^k · z) for C_k = [0,1,1,0,-1,-1] -/
noncomputable def AFNum (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  g (ζ₆ * z) + g (ζ₆ ^ 2 * z) - g (ζ₆ ^ 4 * z) - g (ζ₆ ^ 5 * z)

/-- Symmetric 6-point: Σ 2Re(ζ₆^k) · g(ζ₆^k · z), coefficients [2,1,-1,-2,-1,1] -/
noncomputable def SymNum (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  2 * g z + g (ζ₆ * z) - g (ζ₆ ^ 2 * z) - 2 * g (ζ₆ ^ 3 * z) -
  g (ζ₆ ^ 4 * z) + g (ζ₆ ^ 5 * z)

private lemma zeta6k_mul_ne (k : ℕ) (z : ℂ) (hz : z ≠ 0) : ζ₆ ^ k * z ≠ 0 := by
  apply mul_ne_zero _ hz
  exact pow_ne_zero k zeta6_ne_zero

private lemma zeta6_mul_ne (z : ℂ) (hz : z ≠ 0) : ζ₆ * z ≠ 0 :=
  mul_ne_zero zeta6_ne_zero hz

/-- AFNum annihilates constant functions -/
theorem AFNum_const (c : ℂ) (z : ℂ) : AFNum (fun _ => c) z = 0 := by
  unfold AFNum; ring

/-- SymNum annihilates constant functions -/
theorem SymNum_const (c : ℂ) (z : ℂ) : SymNum (fun _ => c) z = 0 := by
  unfold SymNum; ring

/-- AFNum is additive: AFNum(f+g) = AFNum(f) + AFNum(g) -/
theorem AFNum_add (f g : ℂ → ℂ) (z : ℂ) :
    AFNum (fun w => f w + g w) z = AFNum f z + AFNum g z := by
  unfold AFNum; ring

/-- SymNum is additive: SymNum(f+g) = SymNum(f) + SymNum(g) -/
theorem SymNum_add (f g : ℂ → ℂ) (z : ℂ) :
    SymNum (fun w => f w + g w) z = SymNum f z + SymNum g z := by
  unfold SymNum; ring

/-- AFNum is ℂ-homogeneous: AFNum(c·f) = c·AFNum(f) -/
theorem AFNum_smul (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    AFNum (fun w => c * f w) z = c * AFNum f z := by
  unfold AFNum; ring

/-- SymNum is ℂ-homogeneous: SymNum(c·f) = c·SymNum(f) -/
theorem SymNum_smul (c : ℂ) (f : ℂ → ℂ) (z : ℂ) :
    SymNum (fun w => c * f w) z = c * SymNum f z := by
  unfold SymNum; ring

/-! ## Unified Dζ operator

Rank-2 operator on ⟨φ,ζ₆⟩ ≅ ℤ × ℤ/6ℤ.
C(a,k) = AF_k·Φ_A(a) + SY_k·Φ_S(a) where:
  Φ_A = N6 + N2 - N4: antisymmetric channel
  Φ_S = 2·N5 + N3 + μ·N2: symmetric channel, μ = 2/(φ+2)
Half-period: C(a, k+3) = -C(a, k) from AF/SY anti-periodicity. -/

/-- Φ_A: φ-numerator = N6 + N2 - N4, all 6 ops AF channel -/
noncomputable def Φ_A (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f ((↑φ : ℂ) ^ 3 * z) - 4 * f ((↑φ : ℂ) ^ 2 * z) +
  (3 + (↑φ : ℂ)) * f (↑φ * z) - (3 + (↑ψ : ℂ)) * f (↑ψ * z) +
  4 * f ((↑ψ : ℂ) ^ 2 * z) - f ((↑ψ : ℂ) ^ 3 * z)

/-- Φ_S: φ-numerator = 2·N5 + N3 + μ·N2, all 6 ops SY channel -/
noncomputable def Φ_S (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let μ : ℂ := 2 / ((↑φ : ℂ) + 2)
  2 * N5 f z + N3 f z + μ * N2 f z

/-- Unified Dζ: rank-2 on lattice ⟨φ,ζ₆⟩, encoding all 6 operators -/
noncomputable def Dζ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (AFNum (Φ_A f) z + SymNum (Φ_S f) z) / z

private lemma phi_plus_two_ne : (↑φ : ℂ) + 2 ≠ 0 := by
  rw [ne_eq, ← ofReal_ofNat, ← ofReal_add, ofReal_eq_zero]
  linarith [phi_pos]

/-- Φ_A on constants: Σ = 1-4+(3+φ)-(3+ψ)+4-1 = φ-ψ (not zero, but AFNum kills it) -/
theorem Φ_A_const (c : ℂ) (z : ℂ) :
    Φ_A (fun _ => c) z = ((↑φ : ℂ) - ↑ψ) * c := by
  unfold Φ_A; ring

/-- Φ_S annihilates constants: 2+(3+μ)-10+(3-μ)+2 = 0 -/
theorem Φ_S_const (c : ℂ) (z : ℂ) : Φ_S (fun _ => c) z = 0 := by
  simp only [Φ_S, N5, N3, N2]
  have hφ2 : (↑φ : ℂ) + 2 ≠ 0 := phi_plus_two_ne
  field_simp; ring

/-- Unified Dζ annihilates constants (Φ_A gives const, AFNum kills it) -/
theorem Dζ_const (z : ℂ) : Dζ (fun _ => 1) z = 0 := by
  simp only [Dζ]
  have hA : ∀ w, Φ_A (fun _ => (1 : ℂ)) w = ((↑φ : ℂ) - ↑ψ) * 1 :=
    fun w => Φ_A_const 1 w
  have hS : ∀ w, Φ_S (fun _ => (1 : ℂ)) w = 0 := fun w => Φ_S_const 1 w
  simp only [AFNum, hA, SymNum, hS, mul_one]
  simp [sub_self]

/-- Decomposition: Φ_A = N6 + N2 - N4 -/
theorem Φ_A_decompose (f : ℂ → ℂ) (z : ℂ) :
    Φ_A f z = N6 f z + N2 f z - N4 f z := by
  unfold Φ_A N6 N2 N4
  have hφ2 : (↑φ : ℂ) ^ 2 = ↑φ + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ) ^ 2 = ↑ψ + 1 := psi_sq_complex
  rw [hφ2, hψ2]; ring

/-! ## Fourier coefficients: AF = 2i√3, SY = 6

For f = w^s with s coprime to 6, the ζ₆ Fourier coefficients are:
  AFNum factor = ζ₆^s + ζ₆^{2s} - ζ₆^{4s} - ζ₆^{5s}
  SymNum factor = 2 + ζ₆^s - ζ₆^{2s} - 2ζ₆^{3s} - ζ₆^{4s} + ζ₆^{5s}
For s ≡ 1 mod 6: AF = 2i√3, SY = 6.  For s ≡ 5 mod 6: AF = -2i√3, SY = 6. -/

/-- AF_coeff = ζ₆+ζ₆²-ζ₆⁴-ζ₆⁵ = (ζ₆-ζ₆⁵)+(ζ₆²-ζ₆⁴) -/
noncomputable def AF_coeff : ℂ := ζ₆ + ζ₆ ^ 2 - ζ₆ ^ 4 - ζ₆ ^ 5

/-- AF_coeff = 2i√3 -/
theorem AF_coeff_eq : AF_coeff = ⟨0, 2 * Real.sqrt 3⟩ := by
  unfold AF_coeff; rw [zeta6_sq, zeta6_pow_four, zeta6_pow_five]
  ext <;> simp [ζ₆] <;> ring

/-- 2+ζ₆-ζ₆²-2ζ₆³-ζ₆⁴+ζ₆⁵ = 6 -/
theorem SY_coeff_val :
    (2 : ℂ) + ζ₆ - ζ₆ ^ 2 - 2 * ζ₆ ^ 3 - ζ₆ ^ 4 + ζ₆ ^ 5 = 6 := by
  rw [zeta6_sq, zeta6_cubed, zeta6_pow_four, zeta6_pow_five]
  ext <;> simp [ζ₆]; ring

/-! ## Monomial mode selection: (ζ₆^j)^{6k+r} = ζ₆^{jr} -/

private theorem zeta6_pow_pow_6k1 (j k : ℕ) : (ζ₆ ^ j) ^ (6 * k + 1) = ζ₆ ^ j := by
  rw [← pow_mul, show j * (6 * k + 1) = 6 * (j * k) + j from by ring,
      pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

private theorem zeta6_pow_6k1 (k : ℕ) : ζ₆ ^ (6 * k + 1) = ζ₆ := by
  rw [pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul, pow_one]

private theorem zeta6_pow_pow_6k5 (j k : ℕ) : (ζ₆ ^ j) ^ (6 * k + 5) = ζ₆ ^ (5 * j) := by
  rw [← pow_mul, show j * (6 * k + 5) = 6 * (j * k) + 5 * j from by ring,
      pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

private theorem zeta6_pow_6k5 (k : ℕ) : ζ₆ ^ (6 * k + 5) = ζ₆ ^ 5 := by
  rw [pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

/-- AFNum on w^{6k+1} = AF_coeff · z^{6k+1} -/
theorem AFNum_pow_mod6_1 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 1)) z = z ^ (6 * k + 1) * AF_coeff := by
  simp only [AFNum, AF_coeff, mul_pow, zeta6_pow_6k1,
    zeta6_pow_pow_6k1 2, zeta6_pow_pow_6k1 4, zeta6_pow_pow_6k1 5]
  ring

/-- SymNum on w^{6k+1} = 6 · z^{6k+1} -/
theorem SymNum_pow_mod6_1 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 1)) z = 6 * z ^ (6 * k + 1) := by
  simp only [SymNum, mul_pow, zeta6_pow_6k1,
    zeta6_pow_pow_6k1 2, zeta6_pow_pow_6k1 3, zeta6_pow_pow_6k1 4, zeta6_pow_pow_6k1 5]
  have key : (2 : ℂ) * z ^ (6 * k + 1) + ζ₆ * z ^ (6 * k + 1) - ζ₆ ^ 2 * z ^ (6 * k + 1) -
    2 * (ζ₆ ^ 3 * z ^ (6 * k + 1)) - ζ₆ ^ 4 * z ^ (6 * k + 1) +
    ζ₆ ^ 5 * z ^ (6 * k + 1) =
    (2 + ζ₆ - ζ₆ ^ 2 - 2 * ζ₆ ^ 3 - ζ₆ ^ 4 + ζ₆ ^ 5) * z ^ (6 * k + 1) := by ring
  rw [key, SY_coeff_val]

private theorem AF_coeff_mod5 :
    ζ₆ ^ 5 + ζ₆ ^ 10 - ζ₆ ^ 20 - ζ₆ ^ 25 = -AF_coeff := by
  unfold AF_coeff
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_mul]
  have h20 : ζ₆ ^ 20 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 20 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_pow, one_mul]
  have h25 : ζ₆ ^ 25 = ζ₆ := by
    calc ζ₆ ^ 25 = (ζ₆ ^ 6) ^ 4 * ζ₆ := by ring
    _ = ζ₆ := by rw [zeta6_pow_six, one_pow, one_mul]
  rw [h10, h20, h25]; ring

/-- AFNum on w^{6k+5} = -AF_coeff · z^{6k+5} -/
theorem AFNum_pow_mod6_5 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 5)) z = -(z ^ (6 * k + 5) * AF_coeff) := by
  simp only [AFNum, mul_pow, zeta6_pow_6k5,
    zeta6_pow_pow_6k5 2, zeta6_pow_pow_6k5 4, zeta6_pow_pow_6k5 5]
  simp only [show 5 * 2 = 10 from by ring,
             show 5 * 4 = 20 from by ring, show 5 * 5 = 25 from by ring]
  have key : ζ₆ ^ 5 * z ^ (6 * k + 5) + ζ₆ ^ 10 * z ^ (6 * k + 5) -
    ζ₆ ^ 20 * z ^ (6 * k + 5) - ζ₆ ^ 25 * z ^ (6 * k + 5) =
    (ζ₆ ^ 5 + ζ₆ ^ 10 - ζ₆ ^ 20 - ζ₆ ^ 25) * z ^ (6 * k + 5) := by ring
  rw [key, AF_coeff_mod5]; ring

private theorem SY_coeff_mod5 :
    (2 : ℂ) + ζ₆ ^ 5 - ζ₆ ^ 10 - 2 * ζ₆ ^ 15 - ζ₆ ^ 20 + ζ₆ ^ 25 = 6 := by
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_mul]
  have h15 : ζ₆ ^ 15 = -1 := by
    calc ζ₆ ^ 15 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 3 := by ring
    _ = ζ₆ ^ 3 := by rw [zeta6_pow_six, one_pow, one_mul]
    _ = -1 := zeta6_cubed
  have h20 : ζ₆ ^ 20 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 20 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_pow, one_mul]
  have h25 : ζ₆ ^ 25 = ζ₆ := by
    calc ζ₆ ^ 25 = (ζ₆ ^ 6) ^ 4 * ζ₆ := by ring
    _ = ζ₆ := by rw [zeta6_pow_six, one_pow, one_mul]
  rw [h10, h15, h20, h25, zeta6_pow_four, zeta6_pow_five, zeta6_sq]
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  ext
  · simp [ζ₆]; nlinarith
  · simp [ζ₆]

/-- SymNum on w^{6k+5} = 6 · z^{6k+5} -/
theorem SymNum_pow_mod6_5 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 5)) z = 6 * z ^ (6 * k + 5) := by
  simp only [SymNum, mul_pow, zeta6_pow_6k5,
    zeta6_pow_pow_6k5 2, zeta6_pow_pow_6k5 3, zeta6_pow_pow_6k5 4, zeta6_pow_pow_6k5 5]
  simp only [show 5 * 2 = 10 from by ring, show 5 * 3 = 15 from by ring,
             show 5 * 4 = 20 from by ring, show 5 * 5 = 25 from by ring]
  have key : (2 : ℂ) * z ^ (6 * k + 5) + ζ₆ ^ 5 * z ^ (6 * k + 5) -
    ζ₆ ^ 10 * z ^ (6 * k + 5) - 2 * (ζ₆ ^ 15 * z ^ (6 * k + 5)) -
    ζ₆ ^ 20 * z ^ (6 * k + 5) + ζ₆ ^ 25 * z ^ (6 * k + 5) =
    (2 + ζ₆ ^ 5 - ζ₆ ^ 10 - 2 * ζ₆ ^ 15 - ζ₆ ^ 20 + ζ₆ ^ 25) * z ^ (6 * k + 5) := by ring
  rw [key, SY_coeff_mod5]

/-! ## Mod 6 vanishing: AFNum and SymNum kill w^n for gcd(n,6) > 1

For n ≡ 0,2,3,4 mod 6, the ζ₆-multiplexing sums vanish:
  AF_n := ζ₆ⁿ + ζ₆²ⁿ - ζ₆⁴ⁿ - ζ₆⁵ⁿ = 0
  SY_n := 2 + ζ₆ⁿ - ζ₆²ⁿ - 2ζ₆³ⁿ - ζ₆⁴ⁿ + ζ₆⁵ⁿ = 0 -/

private theorem zeta6_pow_6kr (k r : ℕ) : ζ₆ ^ (6 * k + r) = ζ₆ ^ r := by
  rw [pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

private theorem zeta6_pow_pow_6k (j k r : ℕ) :
    (ζ₆ ^ j) ^ (6 * k + r) = ζ₆ ^ (j * r) := by
  rw [← pow_mul, show j * (6 * k + r) = 6 * (j * k) + j * r from by ring,
      pow_add, pow_mul, zeta6_pow_six, one_pow, one_mul]

/-- AFNum on w^{6k} = 0 -/
theorem AFNum_pow_mod6_0 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k)) z = 0 := by
  simp only [AFNum, mul_pow]
  have h1 : ζ₆ ^ (6 * k) = 1 := by rw [pow_mul, zeta6_pow_six, one_pow]
  have h2 : (ζ₆ ^ 2) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 2*(6*k) = 6*(2*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h4 : (ζ₆ ^ 4) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 4*(6*k) = 6*(4*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h5 : (ζ₆ ^ 5) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 5*(6*k) = 6*(5*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  rw [h1, h2, h4, h5]; ring

/-- SymNum on w^{6k} = 0 -/
theorem SymNum_pow_mod6_0 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k)) z = 0 := by
  simp only [SymNum, mul_pow]
  have h1 : ζ₆ ^ (6 * k) = 1 := by rw [pow_mul, zeta6_pow_six, one_pow]
  have h2 : (ζ₆ ^ 2) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 2*(6*k) = 6*(2*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h3 : (ζ₆ ^ 3) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 3*(6*k) = 6*(3*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h4 : (ζ₆ ^ 4) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 4*(6*k) = 6*(4*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  have h5 : (ζ₆ ^ 5) ^ (6 * k) = 1 := by
    rw [← pow_mul, show 5*(6*k) = 6*(5*k) from by ring, pow_mul, zeta6_pow_six, one_pow]
  rw [h1, h2, h3, h4, h5]; ring

private theorem zeta6_pow_red (n r : ℕ) (h : n = 6 * (n / 6) + r) : ζ₆ ^ n = ζ₆ ^ r := by
  rw [h, zeta6_pow_6kr]

/-- AFNum on w^{6k+2} = 0 (ζ₆²+ζ₆⁴-ζ₆⁸-ζ₆¹⁰ = 0) -/
theorem AFNum_pow_mod6_2 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 2)) z = 0 := by
  simp only [AFNum, mul_pow]
  rw [zeta6_pow_6kr k 2,
      zeta6_pow_pow_6k 2 k 2, show 2 * 2 = 4 from by ring,
      zeta6_pow_pow_6k 4 k 2, show 4 * 2 = 8 from by ring,
      zeta6_pow_pow_6k 5 k 2, show 5 * 2 = 10 from by ring]
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_mul]
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_mul]
  rw [h8, h10]; ring

/-- SymNum on w^{6k+2} = 0 -/
theorem SymNum_pow_mod6_2 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 2)) z = 0 := by
  simp only [SymNum, mul_pow]
  rw [zeta6_pow_6kr k 2,
      zeta6_pow_pow_6k 2 k 2, show 2 * 2 = 4 from by ring,
      zeta6_pow_pow_6k 3 k 2, show 3 * 2 = 6 from by ring,
      zeta6_pow_pow_6k 4 k 2, show 4 * 2 = 8 from by ring,
      zeta6_pow_pow_6k 5 k 2, show 5 * 2 = 10 from by ring]
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_mul]
  have h10 : ζ₆ ^ 10 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 10 = ζ₆ ^ 6 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_mul]
  rw [zeta6_pow_six, h8, h10]; ring

/-- AFNum on w^{6k+3} = 0 (ζ₆³=-1 cancellation) -/
theorem AFNum_pow_mod6_3 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 3)) z = 0 := by
  simp only [AFNum, mul_pow]
  rw [zeta6_pow_6kr k 3,
      zeta6_pow_pow_6k 2 k 3, show 2 * 3 = 6 from by ring,
      zeta6_pow_pow_6k 4 k 3, show 4 * 3 = 12 from by ring,
      zeta6_pow_pow_6k 5 k 3, show 5 * 3 = 15 from by ring]
  have h12 : ζ₆ ^ 12 = 1 := by
    calc ζ₆ ^ 12 = (ζ₆ ^ 6) ^ 2 := by ring
    _ = 1 := by rw [zeta6_pow_six, one_pow]
  have h15 : ζ₆ ^ 15 = -1 := by
    calc ζ₆ ^ 15 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 3 := by ring
    _ = ζ₆ ^ 3 := by rw [zeta6_pow_six, one_pow, one_mul]
    _ = -1 := zeta6_cubed
  rw [zeta6_cubed, zeta6_pow_six, h12, h15]; ring

/-- SymNum on w^{6k+3} = 0 -/
theorem SymNum_pow_mod6_3 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 3)) z = 0 := by
  simp only [SymNum, mul_pow]
  rw [zeta6_pow_6kr k 3,
      zeta6_pow_pow_6k 2 k 3, show 2 * 3 = 6 from by ring,
      zeta6_pow_pow_6k 3 k 3, show 3 * 3 = 9 from by ring,
      zeta6_pow_pow_6k 4 k 3, show 4 * 3 = 12 from by ring,
      zeta6_pow_pow_6k 5 k 3, show 5 * 3 = 15 from by ring]
  have h9 : ζ₆ ^ 9 = -1 := by
    calc ζ₆ ^ 9 = ζ₆ ^ 6 * ζ₆ ^ 3 := by ring
    _ = ζ₆ ^ 3 := by rw [zeta6_pow_six, one_mul]
    _ = -1 := zeta6_cubed
  have h12 : ζ₆ ^ 12 = 1 := by
    calc ζ₆ ^ 12 = (ζ₆ ^ 6) ^ 2 := by ring
    _ = 1 := by rw [zeta6_pow_six, one_pow]
  have h15 : ζ₆ ^ 15 = -1 := by
    calc ζ₆ ^ 15 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 3 := by ring
    _ = ζ₆ ^ 3 := by rw [zeta6_pow_six, one_pow, one_mul]
    _ = -1 := zeta6_cubed
  rw [zeta6_cubed, zeta6_pow_six, h9, h12, h15]; ring

/-- AFNum on w^{6k+4} = 0 (ζ₆⁴=-ζ₆ cancellation) -/
theorem AFNum_pow_mod6_4 (k : ℕ) (z : ℂ) :
    AFNum (fun w => w ^ (6 * k + 4)) z = 0 := by
  simp only [AFNum, mul_pow]
  rw [zeta6_pow_6kr k 4,
      zeta6_pow_pow_6k 2 k 4, show 2 * 4 = 8 from by ring,
      zeta6_pow_pow_6k 4 k 4, show 4 * 4 = 16 from by ring,
      zeta6_pow_pow_6k 5 k 4, show 5 * 4 = 20 from by ring]
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_mul]
  have h16 : ζ₆ ^ 16 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 16 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_pow, one_mul]
  have h20 : ζ₆ ^ 20 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 20 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_pow, one_mul]
  rw [h8, h16, h20]; ring

/-- SymNum on w^{6k+4} = 0 -/
theorem SymNum_pow_mod6_4 (k : ℕ) (z : ℂ) :
    SymNum (fun w => w ^ (6 * k + 4)) z = 0 := by
  simp only [SymNum, mul_pow]
  rw [zeta6_pow_6kr k 4,
      zeta6_pow_pow_6k 2 k 4, show 2 * 4 = 8 from by ring,
      zeta6_pow_pow_6k 3 k 4, show 3 * 4 = 12 from by ring,
      zeta6_pow_pow_6k 4 k 4, show 4 * 4 = 16 from by ring,
      zeta6_pow_pow_6k 5 k 4, show 5 * 4 = 20 from by ring]
  have h8 : ζ₆ ^ 8 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 8 = ζ₆ ^ 6 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_mul]
  have h12 : ζ₆ ^ 12 = 1 := by
    calc ζ₆ ^ 12 = (ζ₆ ^ 6) ^ 2 := by ring
    _ = 1 := by rw [zeta6_pow_six, one_pow]
  have h16 : ζ₆ ^ 16 = ζ₆ ^ 4 := by
    calc ζ₆ ^ 16 = (ζ₆ ^ 6) ^ 2 * ζ₆ ^ 4 := by ring
    _ = ζ₆ ^ 4 := by rw [zeta6_pow_six, one_pow, one_mul]
  have h20 : ζ₆ ^ 20 = ζ₆ ^ 2 := by
    calc ζ₆ ^ 20 = (ζ₆ ^ 6) ^ 3 * ζ₆ ^ 2 := by ring
    _ = ζ₆ ^ 2 := by rw [zeta6_pow_six, one_pow, one_mul]
  rw [h8, h12, h16, h20]
  simp only [zeta6_pow_four]; ring

/-! ## Norm squared decomposition: |6a + 2i√3·b|² = 12(3a² + b²)

The unified Dζ output for monomial z^s decomposes as:
  Re(Dζ) = 6·Φ_S (symmetric/rotation channel, weight 3)
  Im(Dζ) = ±2√3·Φ_A (antisymmetric/boost channel, weight 1)
The 3:1 weight ratio in |Dζ|² encodes I4 = Fin 3 ⊕ Fin 1. -/

/-- |6a + AF_coeff·b|² = 12(3a² + b²) for real a, b -/
theorem Dζ_normSq_decomposition (a b : ℝ) :
    Complex.normSq (6 * (a : ℂ) + AF_coeff * b) = 12 * (3 * a ^ 2 + b ^ 2) := by
  rw [AF_coeff_eq]
  have heq : 6 * (a : ℂ) + (⟨0, 2 * Real.sqrt 3⟩ : ℂ) * (b : ℂ) =
    ⟨6 * a, 2 * Real.sqrt 3 * b⟩ := by ext <;> simp
  rw [heq, normSq_mk]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)
  nlinarith

/-- |AF_coeff|² = 12 -/
theorem AF_coeff_normSq : Complex.normSq AF_coeff = 12 := by
  have h := Dζ_normSq_decomposition 0 1
  simp only [ofReal_zero, mul_zero, zero_add, ofReal_one, mul_one] at h
  linarith

/-! ## Φ_S 3-component decomposition: N5 + N3 + μ·N2

Φ_S decomposes into 3 independent sub-operators (Dn numerators N2/N3/N5).
For monomials z^s, the coefficients σ_Nn(s) = Nn(z^s)/z^s form
rank-3 vectors across s=1,5,7, proving Φ_S carries Fin 3 of information. -/

/-- Φ_S = 2·N5 + N3 + μ·N2 -/
theorem Φ_S_decompose (f : ℂ → ℂ) (z : ℂ) :
    Φ_S f z = 2 * FUST.N5 f z + FUST.N3 f z +
    (2 / ((↑φ : ℂ) + 2)) * FUST.N2 f z := by
  unfold Φ_S FUST.N5 FUST.N3 FUST.N2; ring

/-- Nn on w^s: monomial coefficients -/
theorem N2_pow (s : ℕ) (z : ℂ) :
    FUST.N2 (fun w => w ^ s) z = ((↑φ : ℂ) ^ s - (↑ψ : ℂ) ^ s) * z ^ s := by
  unfold FUST.N2; simp only [mul_pow]; ring

theorem N3_pow (s : ℕ) (z : ℂ) :
    FUST.N3 (fun w => w ^ s) z = ((↑φ : ℂ) ^ s - 2 + (↑ψ : ℂ) ^ s) * z ^ s := by
  unfold FUST.N3; simp only [mul_pow]; ring

theorem N5_pow (s : ℕ) (z : ℂ) :
    FUST.N5 (fun w => w ^ s) z =
    ((↑φ : ℂ) ^ (2 * s) + (↑φ : ℂ) ^ s - 4 + (↑ψ : ℂ) ^ s + (↑ψ : ℂ) ^ (2 * s)) * z ^ s := by
  unfold FUST.N5; simp only [mul_pow, ← pow_mul]; ring

/-- Φ_S on w^s via sub-operator coefficients -/
theorem Φ_S_pow_via_sub (s : ℕ) (z : ℂ) :
    Φ_S (fun w => w ^ s) z =
    (2 * ((↑φ : ℂ) ^ (2 * s) + (↑φ : ℂ) ^ s - 4 + (↑ψ : ℂ) ^ s + (↑ψ : ℂ) ^ (2 * s)) +
     ((↑φ : ℂ) ^ s - 2 + (↑ψ : ℂ) ^ s) +
     (2 / ((↑φ : ℂ) + 2)) * ((↑φ : ℂ) ^ s - (↑ψ : ℂ) ^ s)) * z ^ s := by
  unfold Φ_S FUST.N5 FUST.N3 FUST.N2; simp only [mul_pow, ← pow_mul]; ring

/-! ### Golden ratio powers as F_n·φ + F_{n-1} -/

private lemma psi_eq_c : (↑ψ : ℂ) = 1 - ↑φ := by
  have h : φ + ψ = 1 := phi_add_psi
  have : (↑ψ : ℂ) = ↑(1 - φ) := by rw [show 1 - φ = ψ from by linarith]
  rw [this, ofReal_sub, ofReal_one]

private lemma phi_sq_c : (↑φ : ℂ) ^ 2 = ↑φ + 1 := by
  have h := golden_ratio_property
  have : (↑(φ ^ 2) : ℂ) = ↑(φ + 1) := congrArg _ h
  simp only [ofReal_pow, ofReal_add, ofReal_one] at this; exact this

private lemma phi_pow3_c : (↑φ : ℂ) ^ 3 = 2 * ↑φ + 1 := by
  calc (↑φ : ℂ) ^ 3 = (↑φ : ℂ) ^ 2 * ↑φ := by ring
    _ = ((↑φ : ℂ) + 1) * ↑φ := by rw [phi_sq_c]
    _ = (↑φ : ℂ) ^ 2 + ↑φ := by ring
    _ = (↑φ : ℂ) + 1 + ↑φ := by rw [phi_sq_c]
    _ = 2 * ↑φ + 1 := by ring

private lemma phi_pow4_c : (↑φ : ℂ) ^ 4 = 3 * ↑φ + 2 := by
  calc (↑φ : ℂ) ^ 4 = (↑φ : ℂ) ^ 3 * ↑φ := by ring
    _ = (2 * ↑φ + 1) * ↑φ := by rw [phi_pow3_c]
    _ = 2 * (↑φ : ℂ) ^ 2 + ↑φ := by ring
    _ = 2 * ((↑φ : ℂ) + 1) + ↑φ := by rw [phi_sq_c]
    _ = 3 * ↑φ + 2 := by ring

private lemma phi_pow5_c : (↑φ : ℂ) ^ 5 = 5 * ↑φ + 3 := by
  calc (↑φ : ℂ) ^ 5 = (↑φ : ℂ) ^ 3 * (↑φ : ℂ) ^ 2 := by ring
    _ = (2 * ↑φ + 1) * ((↑φ : ℂ) + 1) := by rw [phi_pow3_c, phi_sq_c]
    _ = 2 * (↑φ : ℂ) ^ 2 + 3 * ↑φ + 1 := by ring
    _ = 2 * ((↑φ : ℂ) + 1) + 3 * ↑φ + 1 := by rw [phi_sq_c]
    _ = 5 * ↑φ + 3 := by ring

private lemma phi_pow7_c : (↑φ : ℂ) ^ 7 = 13 * ↑φ + 8 := by
  calc (↑φ : ℂ) ^ 7 = (↑φ : ℂ) ^ 5 * (↑φ : ℂ) ^ 2 := by ring
    _ = (5 * ↑φ + 3) * ((↑φ : ℂ) + 1) := by rw [phi_pow5_c, phi_sq_c]
    _ = 5 * (↑φ : ℂ) ^ 2 + 8 * ↑φ + 3 := by ring
    _ = 5 * ((↑φ : ℂ) + 1) + 8 * ↑φ + 3 := by rw [phi_sq_c]
    _ = 13 * ↑φ + 8 := by ring

private lemma phi_pow10_c : (↑φ : ℂ) ^ 10 = 55 * ↑φ + 34 := by
  calc (↑φ : ℂ) ^ 10 = ((↑φ : ℂ) ^ 5) ^ 2 := by ring
    _ = (5 * ↑φ + 3) ^ 2 := by rw [phi_pow5_c]
    _ = 25 * (↑φ : ℂ) ^ 2 + 30 * ↑φ + 9 := by ring
    _ = 25 * ((↑φ : ℂ) + 1) + 30 * ↑φ + 9 := by rw [phi_sq_c]
    _ = 55 * ↑φ + 34 := by ring

private lemma phi_pow14_c : (↑φ : ℂ) ^ 14 = 377 * ↑φ + 233 := by
  calc (↑φ : ℂ) ^ 14 = ((↑φ : ℂ) ^ 7) ^ 2 := by ring
    _ = (13 * ↑φ + 8) ^ 2 := by rw [phi_pow7_c]
    _ = 169 * (↑φ : ℂ) ^ 2 + 208 * ↑φ + 64 := by ring
    _ = 169 * ((↑φ : ℂ) + 1) + 208 * ↑φ + 64 := by rw [phi_sq_c]
    _ = 377 * ↑φ + 233 := by ring

private lemma one_sub_phi_pow5 : (1 - (↑φ : ℂ)) ^ 5 = -(5 * ↑φ) + 8 := by
  have : (1 - (↑φ : ℂ)) ^ 5 =
    1 - 5 * ↑φ + 10 * (↑φ : ℂ) ^ 2 - 10 * (↑φ : ℂ) ^ 3 +
    5 * (↑φ : ℂ) ^ 4 - (↑φ : ℂ) ^ 5 := by ring
  rw [this, phi_sq_c, phi_pow3_c, phi_pow4_c, phi_pow5_c]; ring

private lemma one_sub_phi_pow7 : (1 - (↑φ : ℂ)) ^ 7 = -(13 * ↑φ) + 21 := by
  have h2 : (1 - (↑φ : ℂ)) ^ 2 = 2 - ↑φ := by
    have : (1 - (↑φ : ℂ)) ^ 2 = (↑φ : ℂ) ^ 2 - 2 * ↑φ + 1 := by ring
    rw [this, phi_sq_c]; ring
  calc (1 - (↑φ : ℂ)) ^ 7 = (1 - (↑φ : ℂ)) ^ 5 * (1 - (↑φ : ℂ)) ^ 2 := by ring
    _ = (-(5 * ↑φ) + 8) * (2 - ↑φ) := by rw [one_sub_phi_pow5, h2]
    _ = 5 * (↑φ : ℂ) ^ 2 - 18 * ↑φ + 16 := by ring
    _ = 5 * ((↑φ : ℂ) + 1) - 18 * ↑φ + 16 := by rw [phi_sq_c]
    _ = -(13 * ↑φ) + 21 := by ring

private lemma one_sub_phi_pow10 : (1 - (↑φ : ℂ)) ^ 10 = -(55 * ↑φ) + 89 := by
  calc (1 - (↑φ : ℂ)) ^ 10 = ((1 - (↑φ : ℂ)) ^ 5) ^ 2 := by ring
    _ = (-(5 * ↑φ) + 8) ^ 2 := by rw [one_sub_phi_pow5]
    _ = 25 * (↑φ : ℂ) ^ 2 - 80 * ↑φ + 64 := by ring
    _ = 25 * ((↑φ : ℂ) + 1) - 80 * ↑φ + 64 := by rw [phi_sq_c]
    _ = -(55 * ↑φ) + 89 := by ring

private lemma one_sub_phi_pow14 : (1 - (↑φ : ℂ)) ^ 14 = -(377 * ↑φ) + 610 := by
  calc (1 - (↑φ : ℂ)) ^ 14 = ((1 - (↑φ : ℂ)) ^ 7) ^ 2 := by ring
    _ = (-(13 * ↑φ) + 21) ^ 2 := by rw [one_sub_phi_pow7]
    _ = 169 * (↑φ : ℂ) ^ 2 - 546 * ↑φ + 441 := by ring
    _ = 169 * ((↑φ : ℂ) + 1) - 546 * ↑φ + 441 := by rw [phi_sq_c]
    _ = -(377 * ↑φ) + 610 := by ring

/-! ### Sub-operator coefficient values -/

/-- σ_N5(s) = L_{2s} + L_s - 4, σ_N3(s) = L_s - 2, σ_N2(s) = √5·F_s -/
noncomputable def σ_N5 (s : ℕ) : ℂ :=
  (↑φ : ℂ) ^ (2 * s) + (↑φ : ℂ) ^ s - 4 + (↑ψ : ℂ) ^ s + (↑ψ : ℂ) ^ (2 * s)

noncomputable def σ_N3 (s : ℕ) : ℂ := (↑φ : ℂ) ^ s - 2 + (↑ψ : ℂ) ^ s

noncomputable def σ_N2 (s : ℕ) : ℂ := (↑φ : ℂ) ^ s - (↑ψ : ℂ) ^ s

-- s = 1
theorem σ_N5_one : σ_N5 1 = 0 := by
  simp only [σ_N5, Nat.mul_one, pow_one, phi_sq_c, psi_eq_c]
  have : (1 - (↑φ : ℂ)) ^ 2 = (↑φ : ℂ) ^ 2 - 2 * ↑φ + 1 := by ring
  rw [this, phi_sq_c]; ring

theorem σ_N3_one : σ_N3 1 = -1 := by
  simp only [σ_N3, pow_one, psi_eq_c]; ring

theorem σ_N2_one : σ_N2 1 = (↑φ : ℂ) - ↑ψ := by
  simp only [σ_N2, pow_one]

-- s = 5
theorem σ_N5_five : σ_N5 5 = 130 := by
  simp only [σ_N5, show 2 * 5 = 10 from by ring, psi_eq_c]
  rw [phi_pow10_c, phi_pow5_c, one_sub_phi_pow5, one_sub_phi_pow10]; ring

theorem σ_N3_five : σ_N3 5 = 9 := by
  simp only [σ_N3, psi_eq_c]; rw [phi_pow5_c, one_sub_phi_pow5]; ring

theorem σ_N2_five : σ_N2 5 = 5 * ((↑φ : ℂ) - ↑ψ) := by
  simp only [σ_N2, psi_eq_c]; rw [phi_pow5_c, one_sub_phi_pow5]; ring

-- s = 7
theorem σ_N5_seven : σ_N5 7 = 868 := by
  simp only [σ_N5, show 2 * 7 = 14 from by ring, psi_eq_c]
  rw [phi_pow14_c, phi_pow7_c, one_sub_phi_pow7, one_sub_phi_pow14]; ring

theorem σ_N3_seven : σ_N3 7 = 27 := by
  simp only [σ_N3, psi_eq_c]; rw [phi_pow7_c, one_sub_phi_pow7]; ring

theorem σ_N2_seven : σ_N2 7 = 13 * ((↑φ : ℂ) - ↑ψ) := by
  simp only [σ_N2, psi_eq_c]; rw [phi_pow7_c, one_sub_phi_pow7]; ring

private lemma phi_sub_psi_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := by
  rw [← ofReal_sub, ne_eq, ofReal_eq_zero, sub_eq_zero]
  intro h; linarith [phi_pos, psi_neg]

/-- The 3×3 det of [σ_N5, σ_N3, σ_N2] at s=1,5,7 is -6952(φ-ψ) ≠ 0: rank 3.
    This proves Φ_S carries Fin 3 worth of independent information. -/
theorem Φ_S_rank_three :
    σ_N5 1 * (σ_N3 5 * σ_N2 7 - σ_N2 5 * σ_N3 7) -
    σ_N3 1 * (σ_N5 5 * σ_N2 7 - σ_N2 5 * σ_N5 7) +
    σ_N2 1 * (σ_N5 5 * σ_N3 7 - σ_N3 5 * σ_N5 7) ≠ 0 := by
  rw [σ_N5_one, σ_N3_one, σ_N2_one,
      σ_N5_five, σ_N3_five, σ_N2_five,
      σ_N5_seven, σ_N3_seven, σ_N2_seven]
  have hne := phi_sub_psi_ne
  intro h; apply hne
  have : (0 : ℂ) * (9 * (13 * ((↑φ : ℂ) - ↑ψ)) - 5 * ((↑φ : ℂ) - ↑ψ) * 27) -
    (-1 : ℂ) * ((130 : ℂ) * (13 * ((↑φ : ℂ) - ↑ψ)) - 5 * ((↑φ : ℂ) - ↑ψ) * 868) +
    ((↑φ : ℂ) - ↑ψ) * ((130 : ℂ) * 27 - 9 * 868) = -6952 * ((↑φ : ℂ) - ↑ψ) := by ring
  rw [this] at h
  by_contra hc
  exact absurd (mul_ne_zero (by norm_num : (-6952 : ℂ) ≠ 0) hc) (not_not.mpr h)

/-! ## Dζ Gauge Covariance

Dζ(f(c·))(z) = c · Dζ(f)(c·z) for any c ≠ 0.
"Continuity without limits": every observer at scale φⁿ sees identical
algebraic structure. A continuous-parameter limit (D_t → θ) would only
parametrize the φ-direction and cannot extend to full Dζ, because
the ζ₆-direction is compact-discrete (ℤ/6ℤ, period 6). -/

section GaugeCovariance

private lemma mul_comm_assoc' (c a z : ℂ) : c * (a * z) = a * (c * z) := by ring

/-- Φ_A is translation-equivariant: Φ_A(f(c·))(z) = Φ_A(f)(cz) -/
theorem Φ_A_translate (f : ℂ → ℂ) (c z : ℂ) :
    Φ_A (fun t => f (c * t)) z = Φ_A f (c * z) := by
  simp only [Φ_A, mul_comm_assoc']

/-- Φ_S is translation-equivariant: Φ_S(f(c·))(z) = Φ_S(f)(cz) -/
theorem Φ_S_translate (f : ℂ → ℂ) (c z : ℂ) :
    Φ_S (fun t => f (c * t)) z = Φ_S f (c * z) := by
  simp only [Φ_S, N5, N3, N2, mul_comm_assoc']

/-- AFNum is translation-equivariant: AFNum(g(c·))(z) = AFNum(g)(cz) -/
theorem AFNum_translate (g : ℂ → ℂ) (c z : ℂ) :
    AFNum (fun w => g (c * w)) z = AFNum g (c * z) := by
  simp only [AFNum, mul_comm_assoc']

/-- SymNum is translation-equivariant: SymNum(g(c·))(z) = SymNum(g)(cz) -/
theorem SymNum_translate (g : ℂ → ℂ) (c z : ℂ) :
    SymNum (fun w => g (c * w)) z = SymNum g (c * z) := by
  simp only [SymNum, mul_comm_assoc']

private lemma Φ_A_translate_fun (f : ℂ → ℂ) (c : ℂ) :
    Φ_A (fun t => f (c * t)) = fun w => Φ_A f (c * w) := by
  funext z; exact Φ_A_translate f c z

private lemma Φ_S_translate_fun (f : ℂ → ℂ) (c : ℂ) :
    Φ_S (fun t => f (c * t)) = fun w => Φ_S f (c * w) := by
  funext z; exact Φ_S_translate f c z

/-- Dζ gauge covariance: Dζ(f(c·))(z) = c · Dζ(f)(cz) -/
theorem Dζ_gauge_covariance (f : ℂ → ℂ) (c z : ℂ) (hc : c ≠ 0) (hz : z ≠ 0) :
    Dζ (fun t => f (c * t)) z = c * Dζ f (c * z) := by
  have hcz : c * z ≠ 0 := mul_ne_zero hc hz
  simp only [Dζ]
  rw [Φ_A_translate_fun f c, Φ_S_translate_fun f c]
  rw [show AFNum (fun w => Φ_A f (c * w)) z = AFNum (Φ_A f) (c * z)
      from AFNum_translate (Φ_A f) c z]
  rw [show SymNum (fun w => Φ_S f (c * w)) z = SymNum (Φ_S f) (c * z)
      from SymNum_translate (Φ_S f) c z]
  field_simp

/-- φ-gauge covariance: Dζ(f(φ·))(z) = φ · Dζ(f)(φz) -/
theorem Dζ_phi_covariance (f : ℂ → ℂ) (z : ℂ) (hz : z ≠ 0) :
    Dζ (fun t => f ((↑φ : ℂ) * t)) z =
    (↑φ : ℂ) * Dζ f ((↑φ : ℂ) * z) :=
  Dζ_gauge_covariance f _ z (ofReal_ne_zero.mpr (ne_of_gt phi_pos)) hz

/-- Iterated φ-scaling: Dζ(f(φⁿ·))(z) = φⁿ · Dζ(f)(φⁿz) -/
theorem Dζ_self_similar (f : ℂ → ℂ) (n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    Dζ (fun t => f ((↑φ : ℂ) ^ n * t)) z =
    (↑φ : ℂ) ^ n * Dζ f ((↑φ : ℂ) ^ n * z) :=
  Dζ_gauge_covariance f _ z
    (pow_ne_zero n (ofReal_ne_zero.mpr (ne_of_gt phi_pos))) hz

/-- Observer scale independence: no internal measurement distinguishes absolute scale -/
theorem observer_scale_independence (f : ℂ → ℂ) (n : ℤ)
    (z : ℂ) (hz : z ≠ 0) :
    Dζ (fun t => f ((↑φ : ℂ) ^ n * t)) z =
    (↑φ : ℂ) ^ n * Dζ f ((↑φ : ℂ) ^ n * z) :=
  Dζ_gauge_covariance f _ z
    (zpow_ne_zero n (ofReal_ne_zero.mpr (ne_of_gt phi_pos))) hz

end GaugeCovariance

/-! ## Channel Decomposition Theorem

Dζ decomposes into AF (antisymmetric) and SY (symmetric) channels:
  Dζ = (AFNum(Φ_A) + SymNum(Φ_S)) / z
where Φ_A = N6 + N2 - N4 and Φ_S = 2N5 + N3 + μN2 with μ = 2/(φ+2).

The AF channel carries N6, N4, N2 (odd-rank) and the SY channel carries N5, N3 (even-rank). -/

section ChannelDecomposition

/-- AF channel linearity: AFNum distributes over Φ_A = N6 + N2 - N4 -/
theorem AFNum_Φ_A_decompose (f : ℂ → ℂ) (z : ℂ) :
    AFNum (Φ_A f) z = AFNum (N6 f) z + AFNum (N2 f) z - AFNum (N4 f) z := by
  conv_lhs => rw [show Φ_A f = fun w => N6 f w + N2 f w - N4 f w from funext (Φ_A_decompose f)]
  simp only [AFNum]; ring

/-- SY channel linearity: SymNum distributes over Φ_S = 2N5 + N3 + μN2 -/
theorem SymNum_Φ_S_decompose (f : ℂ → ℂ) (z : ℂ) :
    SymNum (Φ_S f) z =
    2 * SymNum (N5 f) z + SymNum (N3 f) z +
    (2 / ((↑φ : ℂ) + 2)) * SymNum (N2 f) z := by
  conv_lhs =>
    rw [show Φ_S f = fun w => 2 * N5 f w + N3 f w + (2 / ((↑φ : ℂ) + 2)) * N2 f w
        from funext (fun w => by simp only [Φ_S])]
  simp only [SymNum]; ring

/-- Dζ channel decomposition: Dζ splits into Nn components via Φ_A and Φ_S -/
theorem Dζ_channel_decompose (f : ℂ → ℂ) (z : ℂ) :
    Dζ f z =
    (AFNum (fun w => N6 f w + N2 f w - N4 f w) z +
     SymNum (fun w => 2 * N5 f w + N3 f w + (2 / ((↑φ : ℂ) + 2)) * N2 f w) z) / z := by
  simp only [Dζ, show Φ_A f = fun w => N6 f w + N2 f w - N4 f w
    from funext (Φ_A_decompose f), show Φ_S f = fun w => 2 * N5 f w + N3 f w +
    (2 / ((↑φ : ℂ) + 2)) * N2 f w from funext (fun w => by simp only [Φ_S])]

/-- AF channel of Dζ: carries N6, N2, N4 (odd-rank operators D6, D4, D2) -/
theorem Dζ_AF_channel (f : ℂ → ℂ) (z : ℂ) :
    AFNum (Φ_A f) z / z =
    (AFNum (N6 f) z + AFNum (N2 f) z - AFNum (N4 f) z) / z := by
  rw [AFNum_Φ_A_decompose]

/-- SY channel of Dζ: carries N5, N3, N2 (even-rank operators D5, D3) -/
theorem Dζ_SY_channel (f : ℂ → ℂ) (z : ℂ) :
    SymNum (Φ_S f) z / z =
    (2 * SymNum (N5 f) z + SymNum (N3 f) z +
     (2 / ((↑φ : ℂ) + 2)) * SymNum (N2 f) z) / z := by
  rw [SymNum_Φ_S_decompose]

end ChannelDecomposition

end FUST.Zeta6
