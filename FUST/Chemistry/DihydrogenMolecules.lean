/-
Dihydrogen Molecules from the Multiplicative State Function Model

Molecular state function g(x) = x^Z · (1+x)^N · (1+ψx)^e
where Z, N, e are total proton, neutron, electron counts.

H₂ isotopologues: H₂, HD, HT, D₂, DT, T₂ and their ions.
-/
import FUST.Chemistry.OxygenIsotopes

namespace FUST.Chemistry.Dihydrogen

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen

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

theorem degree_H2 : (dimAtom 2 0 2).effectiveDegree = 37 := by decide
theorem degree_HD : (dimAtom 2 1 2).effectiveDegree = 52 := by decide
theorem degree_HT : (dimAtom 2 2 2).effectiveDegree = 67 := by decide
theorem degree_D2 : (dimAtom 2 2 2).effectiveDegree = 67 := by decide
theorem degree_DT : (dimAtom 2 3 2).effectiveDegree = 82 := by decide
theorem degree_T2 : (dimAtom 2 4 2).effectiveDegree = 97 := by decide

theorem degree_H2_cation : (dimAtom 2 0 1).effectiveDegree = 35 := by decide
theorem degree_H2_anion : (dimAtom 2 0 3).effectiveDegree = 39 := by decide
theorem degree_D2_cation : (dimAtom 2 2 1).effectiveDegree = 65 := by decide
theorem degree_H3_cation : (dimAtom 3 0 2).effectiveDegree = 53 := by decide

/-! ## Section 7: Isotopologue Degeneracy

HT and D₂ share the same (Z, N, e) = (2, 2, 2), hence the same state function.
This is the simplest example of isotopologue degeneracy.
-/

-- HT and D₂ share the same FDim: both (Z=2, N=2, e=2)
theorem isotopologue_degeneracy_HT_D2 :
    dimAtom 2 2 2 = dimAtom 2 2 2 := rfl

/-! ## Section 8: Summary -/

theorem dihydrogen_classification :
    -- H₂⁺ effectiveDegree
    (dimAtom 2 0 1).effectiveDegree = 35 ∧
    -- Neutral molecule effectiveDegrees
    (dimAtom 2 0 2).effectiveDegree = 37 ∧  -- H₂
    (dimAtom 2 1 2).effectiveDegree = 52 ∧  -- HD
    (dimAtom 2 2 2).effectiveDegree = 67 ∧  -- D₂ = HT
    (dimAtom 2 3 2).effectiveDegree = 82 ∧  -- DT
    (dimAtom 2 4 2).effectiveDegree = 97 := by decide  -- T₂

end FUST.Chemistry.Dihydrogen
