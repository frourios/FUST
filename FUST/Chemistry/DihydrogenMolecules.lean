/-
Dihydrogen Molecules from the Multiplicative State Function Model

Molecular state function g(x) = x^Z · (1+x)^N · (1+ψx)^e
where Z, N, e are total proton, neutron, electron counts.

H₂ isotopologues: H₂, HD, HT, D₂, DT, T₂ and their ions.
-/

import FUST.DifferenceOperators
import FUST.Chemistry.OxygenIsotopes

namespace FUST.Chemistry.Dihydrogen

open FUST FUST.Chemistry.Oxygen

/-! ## Section 1: H₂ Isotopologue Parameters

Atomic parameters: H(Z=1,N=0), D(Z=1,N=1), T(Z=1,N=2).
Molecular Z = sum of atomic Z, N = sum of atomic N.
-/

-- Hydrogen isotope atomic parameters
abbrev hydrogenZ : ℕ := 1
def protium_N : ℕ := 0
def deuterium_N : ℕ := 1
def tritium_N : ℕ := 2

-- Dihydrogen molecular Z = 2 × hydrogenZ
abbrev dihydrogenZ : ℕ := hydrogenZ + hydrogenZ

theorem dihydrogenZ_eq : dihydrogenZ = 2 := rfl

-- Molecular neutron counts from atomic composition
def neutrons_H2 : ℕ := protium_N + protium_N
def neutrons_HD : ℕ := protium_N + deuterium_N
def neutrons_HT : ℕ := protium_N + tritium_N
def neutrons_D2 : ℕ := deuterium_N + deuterium_N
def neutrons_DT : ℕ := deuterium_N + tritium_N
def neutrons_T2 : ℕ := tritium_N + tritium_N

theorem neutrons_H2_eq : neutrons_H2 = 0 := rfl
theorem neutrons_HD_eq : neutrons_HD = 1 := rfl
theorem neutrons_HT_eq : neutrons_HT = 2 := rfl
theorem neutrons_D2_eq : neutrons_D2 = 2 := rfl
theorem neutrons_DT_eq : neutrons_DT = 3 := rfl
theorem neutrons_T2_eq : neutrons_T2 = 4 := rfl

-- HT and D₂ have the same N because H.N + T.N = D.N + D.N
theorem HT_D2_same_neutrons : neutrons_HT = neutrons_D2 := rfl

/-! ## Section 2: Neutral Molecule State Functions -/

noncomputable def H2 (x : ℝ) : ℝ := atomStateFn 2 0 2 x
noncomputable def HD (x : ℝ) : ℝ := atomStateFn 2 1 2 x
noncomputable def HT (x : ℝ) : ℝ := atomStateFn 2 2 2 x
noncomputable def D2 (x : ℝ) : ℝ := atomStateFn 2 2 2 x
noncomputable def DT (x : ℝ) : ℝ := atomStateFn 2 3 2 x
noncomputable def T2 (x : ℝ) : ℝ := atomStateFn 2 4 2 x

-- HT and D₂ are isodegree: both have Z=2, N=2, e=2
theorem HT_eq_D2 : HT = D2 := rfl

/-! ## Section 3: Molecular Ions -/

-- H₂⁺ (dihydrogen cation): 2 protons, 0 neutrons, 1 electron
noncomputable def H2_cation (x : ℝ) : ℝ := atomStateFn 2 0 1 x

-- H₂⁻ (dihydrogen anion): 2 protons, 0 neutrons, 3 electrons
noncomputable def H2_anion (x : ℝ) : ℝ := atomStateFn 2 0 3 x

-- D₂⁺
noncomputable def D2_cation (x : ℝ) : ℝ := atomStateFn 2 2 1 x

-- H₃⁺ (trihydrogen cation): 3 protons, 0 neutrons, 2 electrons
noncomputable def H3_cation (x : ℝ) : ℝ := atomStateFn 3 0 2 x

/-! ## Section 4: Factored Form Identities -/

private lemma psi_eq : ψ = 1 - φ := by linarith [phi_add_psi]

theorem H2_eq (x : ℝ) : H2 x = x ^ 2 * (1 + ψ * x) ^ 2 := by
  unfold H2 atomStateFn; simp [pow_zero, mul_one]

theorem HD_eq (x : ℝ) : HD x = x ^ 2 * (1 + x) * (1 + ψ * x) ^ 2 := by
  unfold HD atomStateFn; ring

theorem D2_eq (x : ℝ) : D2 x = x ^ 2 * (1 + x) ^ 2 * (1 + ψ * x) ^ 2 := rfl

theorem H2_cation_eq (x : ℝ) : H2_cation x = x ^ 2 * (1 + ψ * x) := by
  unfold H2_cation atomStateFn; simp [pow_zero, mul_one, pow_one]

theorem H3_cation_eq (x : ℝ) : H3_cation x = x ^ 3 * (1 + ψ * x) ^ 2 := by
  unfold H3_cation atomStateFn; simp [pow_zero, mul_one]

/-! ## Section 5: Polynomial Expansions -/

theorem H2_expand (x : ℝ) : H2 x = x ^ 2 + 2 * ψ * x ^ 3 + ψ ^ 2 * x ^ 4 := by
  rw [H2_eq]; ring

theorem H2_cation_expand (x : ℝ) : H2_cation x = x ^ 2 + ψ * x ^ 3 := by
  rw [H2_cation_eq]; ring

theorem HD_expand (x : ℝ) :
    HD x = x ^ 2 + (1 + 2 * ψ) * x ^ 3 + (2 * ψ + ψ ^ 2) * x ^ 4 + ψ ^ 2 * x ^ 5 := by
  unfold HD atomStateFn; ring

/-! ## Section 6: Degree Structure -/

theorem degree_H2 : atomDegree 2 0 2 = 4 := rfl
theorem degree_HD : atomDegree 2 1 2 = 5 := rfl
theorem degree_HT : atomDegree 2 2 2 = 6 := rfl
theorem degree_D2 : atomDegree 2 2 2 = 6 := rfl
theorem degree_DT : atomDegree 2 3 2 = 7 := rfl
theorem degree_T2 : atomDegree 2 4 2 = 8 := rfl

theorem degree_H2_cation : atomDegree 2 0 1 = 3 := rfl
theorem degree_H2_anion : atomDegree 2 0 3 = 5 := rfl
theorem degree_D2_cation : atomDegree 2 2 1 = 5 := rfl
theorem degree_H3_cation : atomDegree 3 0 2 = 5 := rfl

-- All dihydrogen species exceed ker(D6) threshold
theorem dihydrogen_degree_exceeds_kerD6 (N e : ℕ) (he : e ≥ 1) :
    atomDegree 2 N e > 2 := by
  unfold atomDegree; omega

/-! ## Section 7: D6 Non-Kernel Classification

All dihydrogen molecules have degree ≥ 3, hence none are in ker(D6).
The minimum-degree species is H₂⁺ with deg=3.
-/

theorem H2_cation_is_minimal_dihydrogen :
    atomDegree 2 0 1 = 3 ∧
    ∀ N e, e ≥ 1 → atomDegree 2 N e ≥ 3 := by
  constructor
  · rfl
  · intro N e he; unfold atomDegree; omega

-- D6(H₂⁺) ≠ 0: the simplest dihydrogen species is already outside ker(D6)
theorem H2_cation_not_in_kerD6 (x : ℝ) (hx : x ≠ 0) :
    D6 H2_cation x ≠ 0 := by
  have heq : H2_cation = fun t => t ^ 2 + ψ * t ^ 3 := by
    ext t; rw [H2_cation_expand]
  rw [heq]
  simp only [D6, N6, hx, ↓reduceIte]
  have hφ2 : φ ^ 2 = φ + 1 := golden_ratio_property
  have hψ2 : ψ ^ 2 = ψ + 1 := psi_sq
  have hφ3 : φ ^ 3 = 2 * φ + 1 := phi_cubed
  have hψ3 : ψ ^ 3 = 2 * ψ + 1 := by
    calc ψ ^ 3 = ψ ^ 2 * ψ := by ring
      _ = (ψ + 1) * ψ := by rw [hψ2]
      _ = ψ ^ 2 + ψ := by ring
      _ = 2 * ψ + 1 := by rw [hψ2]; ring
  have hφ4 : φ ^ 4 = 3 * φ + 2 := by nlinarith [hφ2]
  have hψ4 : ψ ^ 4 = 3 * ψ + 2 := by nlinarith [hψ2]
  have hφ6 : φ ^ 6 = 8 * φ + 5 := by
    calc φ ^ 6 = (φ ^ 4) * (φ ^ 2) := by ring
      _ = (3 * φ + 2) * (φ + 1) := by rw [hφ4, hφ2]
      _ = 3 * φ ^ 2 + 5 * φ + 2 := by ring
      _ = 8 * φ + 5 := by rw [hφ2]; ring
  have hψ6 : ψ ^ 6 = 8 * ψ + 5 := by
    calc ψ ^ 6 = (ψ ^ 4) * (ψ ^ 2) := by ring
      _ = (3 * ψ + 2) * (ψ + 1) := by rw [hψ4, hψ2]
      _ = 3 * ψ ^ 2 + 5 * ψ + 2 := by ring
      _ = 8 * ψ + 5 := by rw [hψ2]; ring
  have hφ9 : φ ^ 9 = 34 * φ + 21 := by
    calc φ ^ 9 = (φ ^ 6) * (φ ^ 3) := by ring
      _ = (8 * φ + 5) * (2 * φ + 1) := by rw [hφ6, hφ3]
      _ = 16 * φ ^ 2 + 18 * φ + 5 := by ring
      _ = 34 * φ + 21 := by rw [hφ2]; ring
  have hψ9 : ψ ^ 9 = 34 * ψ + 21 := by
    calc ψ ^ 9 = (ψ ^ 6) * (ψ ^ 3) := by ring
      _ = (8 * ψ + 5) * (2 * ψ + 1) := by rw [hψ6, hψ3]
      _ = 16 * ψ ^ 2 + 18 * ψ + 5 := by ring
      _ = 34 * ψ + 21 := by rw [hψ2]; ring
  have hsum : φ + ψ = 1 := phi_add_psi
  -- f(t) = t² + ψt³. N6(f) = N6(t²) + ψ·N6(t³)
  -- N6(t²) = 0 (in ker), N6(t³) = D6Coeff(3)·x³ where D6Coeff(3) = 12(φ-ψ) ≠ 0
  have hcoef3 : φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9 =
      12 * (φ - ψ) := by
    rw [hφ9, hφ6, hφ3, hψ3, hψ6, hψ9]; linarith
  have hc_sq : φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6 = 0 := by
    rw [hφ6, hφ4, hφ2, hψ2, hψ4, hψ6]; linarith
  have hnum : (φ ^ 3 * x) ^ 2 + ψ * (φ ^ 3 * x) ^ 3 -
      3 * ((φ ^ 2 * x) ^ 2 + ψ * (φ ^ 2 * x) ^ 3) +
      ((φ * x) ^ 2 + ψ * (φ * x) ^ 3) -
      ((ψ * x) ^ 2 + ψ * (ψ * x) ^ 3) +
      3 * ((ψ ^ 2 * x) ^ 2 + ψ * (ψ ^ 2 * x) ^ 3) -
      ((ψ ^ 3 * x) ^ 2 + ψ * (ψ ^ 3 * x) ^ 3) =
      12 * ψ * (φ - ψ) * x ^ 3 := by
    have := calc (φ ^ 3 * x) ^ 2 + ψ * (φ ^ 3 * x) ^ 3 -
        3 * ((φ ^ 2 * x) ^ 2 + ψ * (φ ^ 2 * x) ^ 3) +
        ((φ * x) ^ 2 + ψ * (φ * x) ^ 3) -
        ((ψ * x) ^ 2 + ψ * (ψ * x) ^ 3) +
        3 * ((ψ ^ 2 * x) ^ 2 + ψ * (ψ ^ 2 * x) ^ 3) -
        ((ψ ^ 3 * x) ^ 2 + ψ * (ψ ^ 3 * x) ^ 3)
        = (φ ^ 6 - 3 * φ ^ 4 + φ ^ 2 - ψ ^ 2 + 3 * ψ ^ 4 - ψ ^ 6) * x ^ 2 +
          ψ * (φ ^ 9 - 3 * φ ^ 6 + φ ^ 3 - ψ ^ 3 + 3 * ψ ^ 6 - ψ ^ 9) * x ^ 3 := by ring
      _ = 0 * x ^ 2 + ψ * (12 * (φ - ψ)) * x ^ 3 := by rw [hc_sq, hcoef3]
      _ = 12 * ψ * (φ - ψ) * x ^ 3 := by ring
    linarith
  rw [hnum]
  have hφψ : φ - ψ = Real.sqrt 5 := phi_sub_psi
  have hφψ_ne : φ - ψ ≠ 0 := by rw [hφψ]; exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hψ_ne : ψ ≠ 0 := by
    intro h; have : φ * ψ = -1 := phi_mul_psi; rw [h, mul_zero] at this; linarith
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hψ_ne) hφψ_ne) (pow_ne_zero 3 hx)
  · exact mul_ne_zero (pow_ne_zero 5 hφψ_ne) hx

/-! ## Section 8: Isotopologue Degeneracy

HT and D₂ share the same (Z, N, e) = (2, 2, 2), hence the same state function.
This is the simplest example of isotopologue degeneracy.
-/

theorem isotopologue_degeneracy_HT_D2 :
    atomDegree 2 neutrons_HT 2 = atomDegree 2 neutrons_D2 2 := rfl

/-! ## Section 9: Summary -/

theorem dihydrogen_classification :
    -- H₂⁺ is minimum-degree dihydrogen (deg=3, first outside ker(D6))
    atomDegree 2 0 1 = 3 ∧
    -- Neutral molecule degrees
    atomDegree 2 0 2 = 4 ∧  -- H₂
    atomDegree 2 1 2 = 5 ∧  -- HD
    atomDegree 2 2 2 = 6 ∧  -- D₂ = HT
    atomDegree 2 3 2 = 7 ∧  -- DT
    atomDegree 2 4 2 = 8 ∧  -- T₂
    -- All exceed ker(D6) threshold
    (∀ N e, e ≥ 1 → atomDegree 2 N e > 2) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro N e he; unfold atomDegree; omega

end FUST.Chemistry.Dihydrogen

namespace FUST.DiscreteTag
open FUST.Chemistry.Dihydrogen

def protiumN_t : DTagged .neutronNum := ⟨protium_N⟩
def deuteriumN_t : DTagged .neutronNum := ⟨deuterium_N⟩
def tritiumN_t : DTagged .neutronNum := ⟨tritium_N⟩
def dihydrogenZ_t : DTagged .protonNum := scaleZ 2 hydrogenZ_t
def H2Deg_t : DTagged .degree := mkDegree dihydrogenZ_t protiumN_t dihydrogenZ_t

theorem protiumN_t_val : protiumN_t.val = 0 := rfl
theorem deuteriumN_t_val : deuteriumN_t.val = 1 := rfl
theorem tritiumN_t_val : tritiumN_t.val = 2 := rfl
theorem dihydrogenZ_t_val : dihydrogenZ_t.val = 2 := rfl
theorem H2Deg_t_val : H2Deg_t.val = 4 := rfl

-- HT and D₂ have same total neutrons
theorem HT_D2_neutrons_tagged :
    protiumN_t + tritiumN_t = deuteriumN_t + deuteriumN_t := rfl

-- Degree construction consistency
theorem H2_deg_consistency :
    mkDegree dihydrogenZ_t protiumN_t dihydrogenZ_t = H2Deg_t := rfl

end FUST.DiscreteTag
