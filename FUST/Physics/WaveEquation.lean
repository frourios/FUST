import FUST.Physics.LeastAction

/-!
# FUST Wave Equation

Concrete witness for variational structure: Fζ(id)(z) ≠ 0 for z ≠ 0.
Variational framework (linearity, perturbation, parametric critical point)
is in LeastAction.lean.
-/

namespace FUST.WaveEquation

open FUST.LeastAction FUST.FζOperator FUST.DζOperator Complex

/-! ## Critical Point: Fζ f = 0

Fζ(id)(z) = eigenCoeff·z where eigenCoeff.re = 60φ-90 > 0.
Hence Fζ(id)(z) ≠ 0 for z ≠ 0, providing a test variation. -/

private noncomputable def phiA_id : ℂ :=
  (↑φ : ℂ)^3 - 4*(↑φ : ℂ)^2 + (3+(↑φ : ℂ))*(↑φ : ℂ) -
  (3+(↑ψ : ℂ))*(↑ψ : ℂ) + 4*(↑ψ : ℂ)^2 - (↑ψ : ℂ)^3

private theorem phiA_id_eq (w : ℂ) : Φ_A (fun t => t) w = phiA_id * w := by
  unfold Φ_A phiA_id; ring

private noncomputable def phiS_id : ℂ :=
  10*(↑φ : ℂ)^2 + (21 - 2*(↑φ : ℂ))*(↑φ : ℂ) - 50 +
  (9 + 2*(↑φ : ℂ))*(↑ψ : ℂ) + 10*(↑ψ : ℂ)^2

private theorem phiS_id_eq (w : ℂ) : Φ_S_int (fun t => t) w = phiS_id * w := by
  unfold Φ_S_int phiS_id; ring

private theorem afnum_linear (c z : ℂ) :
    AFNum (fun w => c * w) z = c * AF_coeff * z := by
  unfold AFNum AF_coeff; ring

private theorem symnum_linear (c z : ℂ) :
    SymNum (fun w => c * w) z =
    c * (2 + ζ₆ - ζ₆^2 - 2*ζ₆^3 - ζ₆^4 + ζ₆^5) * z := by
  unfold SymNum; ring

private noncomputable def eigenCoeff : ℂ :=
  5 * phiA_id * AF_coeff + phiS_id * 6

private theorem fzeta_id_eq (z : ℂ) : Fζ (fun t => t) z = eigenCoeff * z := by
  unfold Fζ eigenCoeff
  rw [show (fun w => 5 * Φ_A (fun t => t) w) = (fun w => (5 * phiA_id) * w) from by
    ext w; rw [phiA_id_eq]; ring]
  rw [show Φ_S_int (fun t => t) = (fun w => phiS_id * w) from by
    ext w; rw [phiS_id_eq]]
  rw [afnum_linear, symnum_linear, SY_coeff_val]; ring

private theorem phiA_id_real : phiA_id = ↑(2 * Real.sqrt 5) := by
  unfold phiA_id
  have hφ2 : (↑φ : ℂ)^2 = (↑φ : ℂ) + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ)^2 = (↑ψ : ℂ) + 1 := psi_sq_complex
  rw [phi_cubed_complex, psi_cubed_complex, hφ2, hψ2]
  ring_nf; rw [hφ2, hψ2]
  rw [show (↑φ : ℂ) + ((↑φ : ℂ) + 1) + (-(↑ψ : ℂ) - ((↑ψ : ℂ) + 1)) =
      ↑(2 * (φ - ψ)) from by push_cast; ring]
  congr 1; rw [phi_sub_psi]; ring

private theorem phiS_id_real : phiS_id = ↑(10 * φ - 15) := by
  unfold phiS_id
  have hφ2 : (↑φ : ℂ)^2 = (↑φ : ℂ) + 1 := golden_ratio_property_complex
  have hψ2 : (↑ψ : ℂ)^2 = (↑ψ : ℂ) + 1 := psi_sq_complex
  have hφψ : (↑φ : ℂ) + (↑ψ : ℂ) = 1 := phi_add_psi_complex
  rw [hφ2, hψ2]; ring_nf; rw [phi_mul_psi_complex, hφ2]
  rw [show (↑ψ : ℂ) = 1 - (↑φ : ℂ) from by linear_combination hφψ]
  push_cast; ring

private theorem eigenCoeff_re_pos : eigenCoeff.re > 0 := by
  change (5 * phiA_id * AF_coeff + phiS_id * 6).re > 0
  rw [phiA_id_real, phiS_id_real, AF_coeff_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  -- 60φ - 90 > 0, i.e. φ > 3/2, i.e. √5 > 2
  have : Real.sqrt 5 > 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) from (Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith [show φ = (1 + Real.sqrt 5) / 2 from rfl]

private theorem eigenCoeff_ne_zero : eigenCoeff ≠ 0 := by
  intro h; have := eigenCoeff_re_pos; rw [h] at this; simp at this

theorem Fζ_detects_active (z : ℂ) (hz : z ≠ 0) :
    Fζ (fun t => t) z ≠ 0 := by
  rw [fzeta_id_eq]; exact mul_ne_zero eigenCoeff_ne_zero hz

theorem critical_point_condition (f : ℂ → ℂ) (z : ℂ) (hz : z ≠ 0) :
    (∀ η : ℂ → ℂ, Fζ f z * Fζ η z = 0) → Fζ f z = 0 :=
  critical_point_of_witness f z ⟨fun t => t, Fζ_detects_active z hz⟩

end FUST.WaveEquation
