import FUST.Physics.MassGap
import FUST.Physics.StateFunctions
import Mathlib.Data.Finsupp.Defs

/-!
# Field Quantization: Fock Space from Fζ Mode Structure

Fζ eigenvalue structure (mod 6 selection) defines a natural Fock space:
- Active modes n ≡ 1,5 (mod 6): propagating quanta
- Kernel modes n ≡ 0,2,3,4 (mod 6): gauge degrees of freedom
- Hamiltonian H = Σ_m E_m · N_m with E_m = casimirMassSq(m)
- Particles = single-mode excitations of the Fock vacuum
-/

namespace FUST.FieldQuantization

open FUST FUST.FζOperator FUST.DζOperator FUST.TimeStructure

/-! ## Layer 1: Mode Space

Fζ(z^n) = 0 iff n ≡ 0,2,3,4 (mod 6). Active modes: n ≡ 1,5 (mod 6). -/

section ModeSpace

def IsActiveMode (n : ℕ) : Prop := n % 6 = 1 ∨ n % 6 = 5

def IsKernelMode (n : ℕ) : Prop := n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4

instance : DecidablePred IsActiveMode := fun _ => inferInstanceAs (Decidable (_ ∨ _))

instance : DecidablePred IsKernelMode := fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

theorem mode_dichotomy (n : ℕ) : IsActiveMode n ∨ IsKernelMode n := by
  unfold IsActiveMode IsKernelMode; omega

theorem mode_exclusive (n : ℕ) : ¬(IsActiveMode n ∧ IsKernelMode n) := by
  unfold IsActiveMode IsKernelMode; omega

theorem active_mode_form (n : ℕ) (h : IsActiveMode n) :
    ∃ k, n = 6 * k + 1 ∨ n = 6 * k + 5 := by
  unfold IsActiveMode at h
  exact ⟨n / 6, by omega⟩

/-- Active modes are Fζ-nontrivial (eigenvalue ≠ 0 established elsewhere) -/
theorem active_mode_nonkernel (n : ℕ) (h : IsActiveMode n) :
    ¬ IsKernelMode n :=
  fun hk => mode_exclusive n ⟨h, hk⟩

/-- Kernel modes are Fζ-trivial -/
theorem kernel_mode_fzeta_zero (n : ℕ) (h : IsKernelMode n) (z : ℂ) :
    Fζ (fun w => w ^ n) z = 0 := by
  unfold IsKernelMode at h
  have hk : n / 6 = n / 6 := rfl
  rcases h with h0 | h2 | h3 | h4
  · have : n = 6 * (n / 6) := by omega
    rw [this]; exact Fζ_vanish_mod6_0 _ z
  · have : n = 6 * (n / 6) + 2 := by omega
    rw [this]; exact Fζ_vanish_mod6_2 _ z
  · have : n = 6 * (n / 6) + 3 := by omega
    rw [this]; exact Fζ_vanish_mod6_3 _ z
  · have : n = 6 * (n / 6) + 4 := by omega
    rw [this]; exact Fζ_vanish_mod6_4 _ z

end ModeSpace

/-! ## Layer 2: Fock Space via Occupation Numbers

Each active mode can be occupied by finitely many quanta.
FockState = ActiveMode →₀ ℕ (finitely supported functions). -/

section FockSpace

abbrev ActiveMode := {n : ℕ // IsActiveMode n}

abbrev FockState := ActiveMode →₀ ℕ

def vacuum : FockState := 0

noncomputable def singleParticle (m : ActiveMode) : FockState :=
  Finsupp.single m 1

def particleNumber (occ : FockState) : ℕ :=
  occ.sum (fun _ n => n)

theorem vacuum_particle_number : particleNumber vacuum = 0 := by
  simp [particleNumber, vacuum, Finsupp.sum]

theorem single_particle_number (m : ActiveMode) :
    particleNumber (singleParticle m) = 1 := by
  simp [particleNumber, singleParticle, Finsupp.sum_single_index]

end FockSpace

/-! ## Layer 3: Hamiltonian from Casimir Invariant

Energy of mode m = casimirMassSq(m), the Poincaré Casimir invariant.
Fock Hamiltonian = Σ_m E_m · N_m (diagonal in mode basis). -/

section Hamiltonian

noncomputable def modeEnergy (m : ActiveMode) : ℝ :=
  casimirMassSq m.val

noncomputable def fockHamiltonian (occ : FockState) : ℝ :=
  occ.sum (fun m n => modeEnergy m * ↑n)

theorem vacuum_energy : fockHamiltonian vacuum = 0 := by
  simp [fockHamiltonian, vacuum, Finsupp.sum]

theorem electron_energy_pos : fockHamiltonian (singleParticle ⟨1, Or.inl rfl⟩) > 0 := by
  unfold fockHamiltonian singleParticle
  rw [Finsupp.sum_single_index (by simp [modeEnergy])]
  simp only [modeEnergy, Nat.cast_one, mul_one]
  exact massGapSq_pos

end Hamiltonian

/-! ## Layer 4: Particle Derivation

Elementary particles = single-mode Fock excitations. -/

section Particles

def electronMode : ActiveMode := ⟨1, Or.inl rfl⟩

def positronMode : ActiveMode := ⟨5, Or.inr rfl⟩

noncomputable def electronFock : FockState := singleParticle electronMode

noncomputable def positronFock : FockState := singleParticle positronMode

theorem electron_energy :
    fockHamiltonian electronFock = casimirMassSq 1 := by
  unfold fockHamiltonian electronFock singleParticle electronMode
  rw [Finsupp.sum_single_index (by simp [modeEnergy])]
  simp [modeEnergy]

theorem electron_is_lightest :
    fockHamiltonian electronFock = massGapSq := by
  rw [electron_energy]; rfl

/-- Photon: kernel mode 0 (gauge boson, not in Fock space of active modes) -/
theorem photon_is_kernel : IsKernelMode 0 := Or.inl rfl

theorem quark_modes_kernel : IsKernelMode 3 ∧ IsKernelMode 4 :=
  ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl))⟩

/-- Interaction vertex: kernel modes combine to create active modes.
    z³ ∈ ker, z⁴ ∈ ker, z⁷ ∈ active (7 ≡ 1 mod 6). -/
theorem interaction_creates_particle :
    IsKernelMode 3 ∧ IsKernelMode 4 ∧ IsActiveMode 7 :=
  ⟨Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr rfl)), Or.inl rfl⟩

/-- Antimatter channel: z² ∈ ker, z³ ∈ ker, z⁵ ∈ active (5 ≡ 5 mod 6). -/
theorem antimatter_creates_particle :
    IsKernelMode 2 ∧ IsKernelMode 3 ∧ IsActiveMode 5 :=
  ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)), Or.inr rfl⟩

/-- Active modes are discrete: exactly n ≡ 1,5 (mod 6) -/
theorem spectrum_discrete (n : ℕ) (h : IsActiveMode n) :
    ∃ k, n = 6 * k + 1 ∨ n = 6 * k + 5 :=
  active_mode_form n h

/-- Electron state function (StateFunctions.electronState) is mode 1 -/
theorem electron_mode_is_one : electronMode.val = 1 := rfl

/-- Positron state function (StateFunctions.positronState) is mode 5 -/
theorem positron_mode_is_five : positronMode.val = 5 := rfl

/-- Combinatorial identity: 11 = C(5,2) + C(2,2) -/
theorem generation_exponent_11 : 11 = Nat.choose 5 2 + Nat.choose 2 2 := by decide

/-- Combinatorial identity: 17 = C(5,2) + C(2,2) + C(4,2) -/
theorem generation_exponent_17 : 17 = Nat.choose 5 2 + Nat.choose 2 2 + Nat.choose 4 2 := by
  decide

/-- Total particle count: 24 fermions + 13 bosons = 37 (from ParticleSpectrum) -/
theorem sm_particle_count :
    2 * 3 + 2 * 3 * 3 + (1 + 3 + (3 ^ 2 - 1) + 1) = 37 := by decide

end Particles

/-! ## Connection to Existing Theory

The derivation defect (FζOperator.derivDefect) provides the interaction vertex:
δ(z^{6j+3}, z^{6k+4}) = Fζ(z^{6(j+k)+7}) (matter emergence)
δ(z^{6j+2}, z^{6k+3}) = Fζ(z^{6(j+k)+5}) (antimatter emergence)
These are already proven in FζOperator.lean. -/

section Connection

/-- Matter emergence mode is always active -/
theorem matter_emergence_active (j k : ℕ) :
    IsActiveMode (6 * j + 3 + (6 * k + 4)) := by
  change (6 * j + 3 + (6 * k + 4)) % 6 = 1 ∨ _; left; omega

/-- Antimatter emergence mode is always active -/
theorem antimatter_emergence_active (j k : ℕ) :
    IsActiveMode (6 * j + 2 + (6 * k + 3)) := by
  change (6 * j + 2 + (6 * k + 3)) % 6 = 1 ∨ _; right; omega

end Connection

end FUST.FieldQuantization
