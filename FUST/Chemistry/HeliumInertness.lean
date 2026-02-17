/-
Helium State Functions and Algebraic Inertness

Key result: He is chemically inert because e = shellCapacity(1) = 2,
meaning its electron shell is exactly filled with zero vacancies.
This is derived purely from D-operator kernel dimensions.
-/

import FUST.Chemistry.OxygenIsotopes

namespace FUST.Chemistry.Helium

open FUST FUST.Chemistry.Oxygen

/-! ## Section 1: Helium Species State Functions -/

-- He-4 (alpha particle core): Z=2, N=2
noncomputable def He4Ion (x : ℝ) : ℝ := atomStateFn 2 2 0 x
noncomputable def He4Cation (x : ℝ) : ℝ := atomStateFn 2 2 1 x
noncomputable def He4Atom (x : ℝ) : ℝ := atomStateFn 2 2 2 x
noncomputable def He4Anion (x : ℝ) : ℝ := atomStateFn 2 2 3 x

-- He-3: Z=2, N=1
noncomputable def He3Ion (x : ℝ) : ℝ := atomStateFn 2 1 0 x
noncomputable def He3Cation (x : ℝ) : ℝ := atomStateFn 2 1 1 x
noncomputable def He3Atom (x : ℝ) : ℝ := atomStateFn 2 1 2 x

/-! ## Section 2: Factored Form Identities -/

theorem He4Ion_eq (x : ℝ) : He4Ion x = x ^ 2 * (1 + x) ^ 2 := by
  unfold He4Ion atomStateFn; simp [pow_zero, mul_one]

theorem He4Atom_eq (x : ℝ) :
    He4Atom x = x ^ 2 * (1 + x) ^ 2 * (1 + ψ * x) ^ 2 := rfl

-- He neutral = (unit cell)² where unit cell = x(1+x)(1+ψx)
noncomputable def unitCell (x : ℝ) : ℝ := x * (1 + x) * (1 + ψ * x)

theorem He4Atom_eq_unitCell_sq (x : ℝ) :
    He4Atom x = unitCell x ^ 2 := by
  unfold He4Atom atomStateFn unitCell; ring

theorem He3Atom_eq (x : ℝ) :
    He3Atom x = x ^ 2 * (1 + x) * (1 + ψ * x) ^ 2 := by
  unfold He3Atom atomStateFn; ring

/-! ## Section 3: Degree Structure -/

theorem degree_He4Ion : atomDegree 2 2 0 = 4 := rfl
theorem degree_He4Cation : atomDegree 2 2 1 = 5 := rfl
theorem degree_He4Atom : atomDegree 2 2 2 = 6 := rfl
theorem degree_He4Anion : atomDegree 2 2 3 = 7 := rfl
theorem degree_He3Ion : atomDegree 2 1 0 = 3 := rfl
theorem degree_He3Cation : atomDegree 2 1 1 = 4 := rfl
theorem degree_He3Atom : atomDegree 2 1 2 = 5 := rfl

-- He-4 nucleus is doubly magic (Z=2, N=2)
theorem He4_proton_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = 2 :=
  ⟨0, by omega, rfl⟩

theorem He4_neutron_magic : ∃ i, i < 7 ∧ Nuclear.nuclearMagic i = 2 :=
  ⟨0, by omega, rfl⟩

/-! ## Section 4: Pairwise Particle Factors and ker(D6)

The three particle factors: proton=x, neutron=(1+x), electron=(1+ψx).
All pairwise products have deg ≤ 2, so they lie in ker(D6).
The triple product (unit cell) has deg = 3, exiting ker(D6).
-/

theorem pn_pair_degree : atomDegree 1 1 0 = 2 := rfl
theorem pe_pair_degree : atomDegree 1 0 1 = 2 := rfl
theorem ne_pair_degree : atomDegree 0 1 1 = 2 := rfl
theorem unitCell_degree : atomDegree 1 1 1 = 3 := rfl

theorem pairs_in_kerD6 :
    atomDegree 1 1 0 ≤ 2 ∧
    atomDegree 1 0 1 ≤ 2 ∧
    atomDegree 0 1 1 ≤ 2 ∧
    atomDegree 1 1 1 > 2 := by
  unfold atomDegree; omega

/-! ## Section 5: Closed Shell Electron Count

closedShellElectronCount(n) = Σ_{k=1}^n shellCapacity(k) = Σ_{k=1}^n 2k²
-/

def closedShellElectronCount (n : ℕ) : ℕ :=
  (Finset.range n).sum (fun k => Nuclear.shellCapacity (k + 1))

theorem closedShellElectronCount_zero : closedShellElectronCount 0 = 0 := rfl

theorem closedShellElectronCount_succ (n : ℕ) :
    closedShellElectronCount (n + 1) =
    closedShellElectronCount n + Nuclear.shellCapacity (n + 1) := by
  unfold closedShellElectronCount
  rw [Finset.sum_range_succ]

theorem closedShell_1 : closedShellElectronCount 1 = 2 := by decide
theorem closedShell_2 : closedShellElectronCount 2 = 10 := by decide

private theorem shellCapacity_ge_two (n : ℕ) (hn : n ≥ 1) :
    Nuclear.shellCapacity n ≥ 2 := by
  unfold Nuclear.shellCapacity
  have h2 : Nuclear.spinDegeneracy = 2 := Nuclear.spinDegeneracy_eq
  rw [h2]
  nlinarith [Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0)]

-- closedShellElectronCount is strictly increasing for n ≥ 1
theorem closedShellElectronCount_strict_mono (n : ℕ) (hn : n ≥ 1) :
    closedShellElectronCount n < closedShellElectronCount (n + 1) := by
  rw [closedShellElectronCount_succ]
  have := shellCapacity_ge_two (n + 1) (by omega)
  omega

/-! ## Section 6: Helium Closed Shell Property -/

def isClosedShell (e : ℕ) : Prop :=
  ∃ n, n ≥ 1 ∧ closedShellElectronCount n = e

theorem helium_is_closed_shell : isClosedShell 2 :=
  ⟨1, by omega, by decide⟩

theorem neon_is_closed_shell : isClosedShell 10 :=
  ⟨2, by omega, by decide⟩

theorem helium_closed_shell_eq :
    closedShellElectronCount 1 = Nuclear.shellCapacity 1 := by decide

-- shellCapacity(1) = spinDegeneracy = dim(ker(D5)) = 2
theorem shell1_eq_spinDeg : Nuclear.shellCapacity 1 = Nuclear.spinDegeneracy := by
  unfold Nuclear.shellCapacity; ring

/-! ## Section 7: Hydrogen and Oxygen Have Vacancies -/

theorem hydrogen_has_vacancy :
    (1 : ℕ) < closedShellElectronCount 1 := by decide

theorem oxygen_has_vacancy :
    (8 : ℕ) < closedShellElectronCount 2 := by decide

theorem hydrogen_vacancy_count :
    closedShellElectronCount 1 - 1 = 1 := by decide

theorem oxygen_vacancy_count :
    closedShellElectronCount 2 - 8 = 2 := by decide

/-! ## Section 8: Non-Closed Shell Proofs

Key: closedShellElectronCount(1) = 2, closedShellElectronCount(2) = 10,
and the sequence is strictly increasing, so values between 2 and 10 (exclusive)
and below 2 cannot be closed shell values.
-/

private theorem closedShell_ge_10_of_ge_2 (n : ℕ) (hn : n ≥ 2) :
    closedShellElectronCount n ≥ 10 := by
  have hmono : ∀ m, m ≥ 1 →
      closedShellElectronCount m < closedShellElectronCount (m + 1) :=
    closedShellElectronCount_strict_mono
  have h2 : closedShellElectronCount 2 = 10 := by decide
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k + 1 = 2
    · rw [hk, h2]
    · have hk2 : k ≥ 2 := by omega
      have ihk := ih hk2
      have := hmono k (by omega)
      omega

theorem hydrogen_not_closed_shell : ¬ isClosedShell 1 := by
  intro ⟨n, hn, heq⟩
  by_cases h1 : n = 1
  · subst h1; simp [closedShell_1] at heq
  · have hn2 : n ≥ 2 := by omega
    have := closedShell_ge_10_of_ge_2 n hn2
    omega

theorem oxygen_not_closed_shell : ¬ isClosedShell 8 := by
  intro ⟨n, hn, heq⟩
  by_cases h1 : n = 1
  · subst h1; simp [closedShell_1] at heq
  · have hn2 : n ≥ 2 := by omega
    have := closedShell_ge_10_of_ge_2 n hn2
    omega

theorem HeH_not_closed_shell : ¬ isClosedShell 3 := by
  intro ⟨n, hn, heq⟩
  by_cases h1 : n = 1
  · subst h1; simp [closedShell_1] at heq
  · have hn2 : n ≥ 2 := by omega
    have := closedShell_ge_10_of_ge_2 n hn2
    omega

theorem He2_not_closed_shell : ¬ isClosedShell 4 := by
  intro ⟨n, hn, heq⟩
  by_cases h1 : n = 1
  · subst h1; simp [closedShell_1] at heq
  · have hn2 : n ≥ 2 := by omega
    have := closedShell_ge_10_of_ge_2 n hn2
    omega

/-! ## Section 9: Shell Transition Cost -/

-- After shell 1 (He), the next shell needs 8 electrons
theorem shell_transition_cost_1 :
    Nuclear.shellCapacity 2 = 8 := rfl

-- One electron beyond He creates 7 vacancies in shell 2
theorem beyond_He_vacancy :
    Nuclear.shellCapacity 2 - 1 = 7 := rfl

-- After shell 2 (Ne), the next shell needs 18 electrons
theorem shell_transition_cost_2 :
    Nuclear.shellCapacity 3 = 18 := rfl

theorem beyond_Ne_vacancy :
    Nuclear.shellCapacity 3 - 1 = 17 := rfl

-- HeH degree
theorem degree_HeH : atomDegree 3 2 3 = 8 := rfl

-- He₂ (hypothetical dihelium): Z=4, N=4, e=4
theorem degree_He2 : atomDegree 4 4 4 = 12 := rfl

/-! ## Section 10: Summary -/

theorem helium_inertness_algebraic :
    -- He-4 is doubly magic
    (∃ i, i < 7 ∧ Nuclear.nuclearMagic i = 2) ∧
    -- He electron count = shellCapacity(1) = spinDegeneracy
    Nuclear.shellCapacity 1 = 2 ∧
    -- He is closed shell
    isClosedShell 2 ∧
    -- H and O are not closed shell
    ¬ isClosedShell 1 ∧ ¬ isClosedShell 8 ∧
    -- Hypothetical He compounds are not closed shell
    ¬ isClosedShell 3 ∧ ¬ isClosedShell 4 ∧
    -- All He species have deg > 2 (outside ker(D6))
    (∀ e, e ≥ 1 → atomDegree 2 2 e > 2) := by
  refine ⟨⟨0, by omega, rfl⟩, rfl, helium_is_closed_shell,
    hydrogen_not_closed_shell, oxygen_not_closed_shell,
    HeH_not_closed_shell, He2_not_closed_shell, ?_⟩
  intro e he; unfold atomDegree; omega

end FUST.Chemistry.Helium
