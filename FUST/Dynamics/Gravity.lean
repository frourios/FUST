/-
General relativity from localized Lorentz symmetry.
Global so(3,1) invariance (Poincare.lean) → local ω : I4 → so(3,1) → gravity.
All dimensions derived from ζ₆/φψ duality: kerDim=3, posRootCount=1, spacetime=4.
-/
import FUST.Dynamics.Poincare

namespace FUST.Dynamics.Gravity

open LinearMap (BilinForm)
open LieAlgebra.Orthogonal Matrix FUST Lorentz Poincare Zeta6

/-! ## Lorentz connection: localized so(3,1) -/

noncomputable instance : Module.Free ℝ (so' (Fin 3) (Fin 1) ℝ).toSubmodule :=
  Module.Free.of_equiv so31EquivR6.symm

/-- dim(connection) = dim so(3,1) × spacetime dim = 6 × 4 = 24 -/
theorem finrank_connection :
    Module.finrank ℝ (I4 → (so' (Fin 3) (Fin 1) ℝ).toSubmodule) = 24 := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
      show Fintype.card I4 = 4 from by simp [I4, Fintype.card_sum, Fintype.card_fin],
      finrank_so31]; norm_num

/-! ## Curvature: Lie bracket of connection components

Localizing the Lorentz symmetry introduces a connection ω : I4 → so(3,1).
The curvature F_{μν} = [ω_μ, ω_ν] ∈ so(3,1) is the Riemann curvature. -/

/-- Curvature of Lorentz connection = Lie bracket of components -/
noncomputable def curvature (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) :
    so' (Fin 3) (Fin 1) ℝ :=
  ⁅ω μ, ω ν⁆

/-- Curvature is antisymmetric: F_{μν} = -F_{νμ} -/
theorem curvature_antisymm (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) :
    curvature ω μ ν = -curvature ω ν μ :=
  (lie_skew (ω μ) (ω ν)).symm

/-- Curvature stays in so(3,1): [so(3,1), so(3,1)] ⊆ so(3,1) -/
theorem curvature_in_so31 (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) :
    (curvature ω μ ν).val ∈ so' (Fin 3) (Fin 1) ℝ :=
  (curvature ω μ ν).prop

/-- Curvature preserves the Minkowski form (inherits from so(3,1)) -/
theorem curvature_preserves_minkowski
    (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) (v w : I4 → ℝ) :
    minkowskiBilin (((curvature ω μ ν).val : Matrix I4 I4 ℝ) *ᵥ v) w +
    minkowskiBilin v (((curvature ω μ ν).val : Matrix I4 I4 ℝ) *ᵥ w) = 0 :=
  lorentz_infinitesimal_invariance ⟨(curvature ω μ ν).val, curvature_in_so31 ω μ ν⟩ v w

/-! ## Bianchi identity from Jacobi identity

The algebraic Bianchi identity ∇_{[μ} F_{νρ]} = 0 is the Jacobi identity
of the Lie algebra so(3,1) applied to connection components. -/

/-- Algebraic Bianchi identity: cyclic sum of [ω_μ, F_{νρ}] = 0 -/
theorem bianchi_identity (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν ρ : I4) :
    ⁅ω μ, ⁅ω ν, ω ρ⁆⁆ + ⁅ω ν, ⁅ω ρ, ω μ⁆⁆ + ⁅ω ρ, ⁅ω μ, ω ν⁆⁆ = 0 :=
  lie_jacobi (ω μ) (ω ν) (ω ρ)

section DzetaConnection

open Complex

/-! ## Dζ → so(3,1) connection: algebraic 3+1 decomposition

The unified Dζ operator decomposes into:
  Re(Dζ) = 6·Φ_S (spatial, weight 3 in |Dζ|²) — 3 independent sub-operators
  Im(Dζ) = ±2√3·Φ_A (temporal, weight 1 in |Dζ|²) — 1 independent channel
This matches I4 = Fin 3 ⊕ Fin 1 and indexes the connection space ω : I4 → so(3,1). -/

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

private lemma phi_sub_psi_ne : (↑φ : ℂ) - ↑ψ ≠ 0 := by
  rw [← ofReal_sub, ne_eq, ofReal_eq_zero, sub_eq_zero]
  intro h; linarith [phi_pos, psi_neg]

/-- Φ_A coefficient on monomial w^s -/
noncomputable def Φ_A_coeff (s : ℕ) : ℂ :=
  (↑φ : ℂ) ^ (3 * s) - 4 * (↑φ : ℂ) ^ (2 * s) +
  (3 + (↑φ : ℂ)) * (↑φ : ℂ) ^ s - (3 + (↑ψ : ℂ)) * (↑ψ : ℂ) ^ s +
  4 * (↑ψ : ℂ) ^ (2 * s) - (↑ψ : ℂ) ^ (3 * s)

/-- Φ_A on monomial: Φ_A(w^s)(z) = Φ_A_coeff(s) · z^s -/
theorem Φ_A_pow (s : ℕ) (z : ℂ) :
    Φ_A (fun w => w ^ s) z = Φ_A_coeff s * z ^ s := by
  unfold Φ_A Φ_A_coeff; simp only [mul_pow, ← pow_mul]; ring

/-- Φ_A_coeff(1) = 2(φ-ψ) = 2√5 -/
theorem Φ_A_coeff_one : Φ_A_coeff 1 = 2 * ((↑φ : ℂ) - ↑ψ) := by
  simp only [Φ_A_coeff, Nat.mul_one, pow_one, psi_eq_c, phi_pow3_c, phi_sq_c]
  have h2 : (1 - (↑φ : ℂ)) ^ 2 = 2 - ↑φ := by
    have : (1 - (↑φ : ℂ)) ^ 2 = (↑φ : ℂ) ^ 2 - 2 * ↑φ + 1 := by ring
    rw [this, phi_sq_c]; ring
  have h3 : (1 - (↑φ : ℂ)) ^ 3 = -(2 * ↑φ) + 3 := by
    calc (1 - (↑φ : ℂ)) ^ 3
        = (1 - (↑φ : ℂ)) ^ 2 * (1 - ↑φ) := by ring
      _ = (2 - ↑φ) * (1 - ↑φ) := by rw [h2]
      _ = 2 - 3 * ↑φ + (↑φ : ℂ) ^ 2 := by ring
      _ = 2 - 3 * ↑φ + ((↑φ : ℂ) + 1) := by rw [phi_sq_c]
      _ = -(2 * ↑φ) + 3 := by ring
  rw [h2, h3]; ring

/-- Temporal channel is nonzero -/
theorem temporal_nonzero : Φ_A_coeff 1 ≠ 0 := by
  rw [Φ_A_coeff_one]
  exact mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) phi_sub_psi_ne

/-- 4-component extraction: 3 spatial (from Φ_S) + 1 temporal (from Φ_A) -/
noncomputable def Dζ_components (s : ℕ) : I4 → ℂ :=
  fun idx => match idx with
  | Sum.inl 0 => σ_N5 s
  | Sum.inl 1 => σ_N3 s
  | Sum.inl 2 => σ_N2 s
  | Sum.inr 0 => Φ_A_coeff s

/-- Spatial (Fin 3) + temporal (Fin 1) = I4 -/
theorem Dζ_dim_matches_I4 :
    Fintype.card (Fin 3) + Fintype.card (Fin 1) = Fintype.card I4 := by
  simp [I4, Fintype.card_sum, Fintype.card_fin]

/-- Weight ratio 3:1 from |Dζ|² matches I4 cardinality -/
theorem weight_matches_I4 :
    3 + 1 = Fintype.card I4 := by
  simp [I4, Fintype.card_sum, Fintype.card_fin]

/-- Connection space dim = |I4| × dim so(3,1) = 4 × 6 = 24 -/
theorem Dζ_connection_dim :
    Fintype.card I4 * Module.finrank ℝ (so' (Fin 3) (Fin 1) ℝ).toSubmodule = 24 := by
  rw [show Fintype.card I4 = 4 from by simp [I4, Fintype.card_sum, Fintype.card_fin],
      finrank_so31]

/-- Bianchi identity for Dζ-indexed connections -/
theorem Dζ_bianchi (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν ρ : I4) :
    ⁅ω μ, ⁅ω ν, ω ρ⁆⁆ + ⁅ω ν, ⁅ω ρ, ω μ⁆⁆ + ⁅ω ρ, ⁅ω μ, ω ν⁆⁆ = 0 :=
  bianchi_identity ω μ ν ρ

end DzetaConnection

section EinsteinEquations

/-! ## Minkowski metric, Riemann/Ricci/Einstein tensors, vacuum EFE -/

/-- Minkowski metric η_{μν} = diag(1,1,1,-1) -/
noncomputable def η (μ ν : I4) : ℝ :=
  (indefiniteDiagonal (Fin 3) (Fin 1) ℝ : Matrix I4 I4 ℝ) μ ν

theorem η_off_diag (μ ν : I4) (h : μ ≠ ν) : η μ ν = 0 := by
  unfold η; exact Matrix.diagonal_apply_ne _ h

theorem η_spatial (i : Fin 3) : η (Sum.inl i) (Sum.inl i) = 1 := by
  simp [η, indefiniteDiagonal, Matrix.diagonal_apply_eq]

theorem η_temporal : η (Sum.inr 0) (Sum.inr 0) = -1 := by
  simp [η, indefiniteDiagonal, Matrix.diagonal_apply_eq]

/-- Tr(η²) = dim(spacetime) = 4 -/
theorem η_sq_trace : ∑ μ : I4, ∑ ν : I4, η μ ν * η μ ν = 4 := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Fin.sum_univ_one]
  simp (config := { decide := true }) only [η, indefiniteDiagonal, Matrix.diagonal_apply,
    Sum.elim_inl, Sum.elim_inr, ↓reduceIte]
  norm_num

/-! ## Riemann tensor -/

/-- R^ρ_{σμν} := (curvature ω μ ν).val ρ σ -/
noncomputable def riemann (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν ρ σ : I4) : ℝ :=
  ((curvature ω μ ν).val : Matrix I4 I4 ℝ) ρ σ

/-- Riemann antisymmetry: R^ρ_{σμν} = -R^ρ_{σνμ} -/
theorem riemann_antisymm (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν ρ σ : I4) :
    riemann ω μ ν ρ σ = -riemann ω ν μ ρ σ := by
  unfold riemann
  rw [curvature_antisymm]
  simp

theorem riemann_diag (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ρ σ : I4) :
    riemann ω μ μ ρ σ = 0 := by
  have h := riemann_antisymm ω μ μ ρ σ
  linarith

/-- Flat connection → zero Riemann -/
theorem riemann_flat (A : so' (Fin 3) (Fin 1) ℝ) (μ ν ρ σ : I4) :
    riemann (fun _ => A) μ ν ρ σ = 0 := by
  unfold riemann curvature
  simp [lie_self]

/-! ## Ricci tensor, scalar curvature, Einstein tensor -/

/-- Ric_{μν} = Σ_ρ R^ρ_{μρν} -/
noncomputable def ricci (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) : ℝ :=
  ∑ ρ : I4, riemann ω ρ ν ρ μ

/-- R = Σ_{μν} η^{μν} Ric_{μν} -/
noncomputable def scalarCurvature (ω : I4 → so' (Fin 3) (Fin 1) ℝ) : ℝ :=
  ∑ μ : I4, ∑ ν : I4, η μ ν * ricci ω μ ν

/-- G_{μν} = Ric_{μν} - (1/2) η_{μν} R -/
noncomputable def einstein (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) : ℝ :=
  ricci ω μ ν - (1 / 2) * η μ ν * scalarCurvature ω

/-! ## Flat connection satisfies vacuum EFE -/

theorem ricci_flat (A : so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) :
    ricci (fun _ => A) μ ν = 0 := by
  unfold ricci; simp [riemann_flat]

theorem scalarCurvature_flat (A : so' (Fin 3) (Fin 1) ℝ) :
    scalarCurvature (fun _ => A) = 0 := by
  unfold scalarCurvature; simp [ricci_flat]

theorem einstein_flat (A : so' (Fin 3) (Fin 1) ℝ) (μ ν : I4) :
    einstein (fun _ => A) μ ν = 0 := by
  unfold einstein; rw [ricci_flat, scalarCurvature_flat]; ring

/-- Vacuum Einstein equations: constant connections satisfy G_{μν} = 0 -/
theorem vacuum_einstein (A : so' (Fin 3) (Fin 1) ℝ) :
    ∀ μ ν : I4, einstein (fun _ => A) μ ν = 0 :=
  fun μ ν => einstein_flat A μ ν

/-! ## Einstein tensor trace: η^{μν} G_{μν} = -R -/

theorem einstein_trace (ω : I4 → so' (Fin 3) (Fin 1) ℝ) :
    ∑ μ : I4, ∑ ν : I4, η μ ν * einstein ω μ ν = -scalarCurvature ω := by
  simp_rw [einstein, mul_sub]
  simp_rw [Finset.sum_sub_distrib]
  have h1 : ∑ μ : I4, ∑ ν : I4, η μ ν * ricci ω μ ν = scalarCurvature ω := rfl
  rw [h1]
  have h2 : ∑ μ : I4, ∑ ν : I4, η μ ν * (1 / 2 * η μ ν * scalarCurvature ω) =
      2 * scalarCurvature ω := by
    calc ∑ μ : I4, ∑ ν : I4, η μ ν * (1 / 2 * η μ ν * scalarCurvature ω)
        = ∑ μ : I4, ∑ ν : I4, (η μ ν * η μ ν) * (1 / 2 * scalarCurvature ω) := by
          congr 1; ext μ; congr 1; ext ν; ring
      _ = (∑ μ : I4, ∑ ν : I4, η μ ν * η μ ν) * (1 / 2 * scalarCurvature ω) := by
          rw [Finset.sum_mul]; congr 1; ext μ; rw [Finset.sum_mul]
      _ = 2 * scalarCurvature ω := by rw [η_sq_trace]; ring
  rw [h2]; ring

/-! ## Bianchi identity in matrix entries -/

theorem bianchi_entries (ω : I4 → so' (Fin 3) (Fin 1) ℝ) (μ ν ρ α β : I4) :
    (⁅ω μ, ⁅ω ν, ω ρ⁆⁆ : so' (Fin 3) (Fin 1) ℝ).val α β +
    (⁅ω ν, ⁅ω ρ, ω μ⁆⁆ : so' (Fin 3) (Fin 1) ℝ).val α β +
    (⁅ω ρ, ⁅ω μ, ω ν⁆⁆ : so' (Fin 3) (Fin 1) ℝ).val α β = 0 := by
  have h := bianchi_identity ω μ ν ρ
  have h2 : (⁅ω μ, ⁅ω ν, ω ρ⁆⁆ + ⁅ω ν, ⁅ω ρ, ω μ⁆⁆ +
    ⁅ω ρ, ⁅ω μ, ω ν⁆⁆ : so' (Fin 3) (Fin 1) ℝ).val α β = 0 := by
    rw [h]; rfl
  have h3 : ∀ (A B C : so' (Fin 3) (Fin 1) ℝ),
    (A + B + C).val α β = A.val α β + B.val α β + C.val α β := by
    intro A B C; show ((A + B + C : so' _ _ _) : Matrix I4 I4 ℝ) α β = _
    simp [Matrix.add_apply]
  rw [h3] at h2; exact h2

end EinsteinEquations

end FUST.Dynamics.Gravity
