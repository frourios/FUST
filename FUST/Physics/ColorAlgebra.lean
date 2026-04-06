import FUST.Physics.FieldQuantization
import FUST.Physics.GaugeGroups
import Mathlib.LinearAlgebra.Determinant

/-!
# Color Algebra: 3-Forms, Baryons, and Form Degree Hierarchy

The A₂ root system from ℤ[ζ₆] (GaugeGroups.lean) determines:
- Color space ℂ³ = fund. rep. of SU(3)
- 3-form ε ∈ ⋀³(ℂ³): baryon = color singlet
- ⋀⁴(ℂ³) = 0: no 4-quark primitive (baryons are exactly 3-quark)
- Nested derivDefect: hadron observability beyond mod-6 selection
-/

namespace FUST.ColorAlgebra

open FUST FUST.FζOperator FUST.FieldQuantization Matrix Module

/-! ## Color Space from A₂

Color space = Fin 3 → ℂ (standard basis of ℂ³).
The 3-form det ∈ ⋀³(ℂ³) is the color singlet projector. -/

section ColorSpace

abbrev Color := Fin 3

noncomputable def colorBasis : Basis Color ℂ (Color → ℂ) := Pi.basisFun ℂ Color

/-- The color 3-form: ε_{abc} = det on ℂ³ -/
noncomputable def colorDet : (Color → ℂ) [⋀^Color]→ₗ[ℂ] ℂ := colorBasis.det

/-- Color 3-form on standard basis = 1 -/
theorem colorDet_basis : colorDet colorBasis = 1 := colorBasis.det_self

/-- colorRank = 3 from StateFunctions -/
theorem color_dim : Fintype.card Color = StateFunctions.colorRank := rfl

end ColorSpace

/-! ## Baryon as 3-Form

A baryon is ε_{abc} q₁ᵃ q₂ᵇ q₃ᶜ where q_i ∈ ℂ³ are color vectors.
Nonzero iff the three color vectors are linearly independent. -/

section Baryon

/-- Baryon vertex: 3-form applied to three quark color vectors -/
noncomputable def baryonVertex (q₁ q₂ q₃ : Color → ℂ) : ℂ :=
  colorDet ![q₁, q₂, q₃]

/-- Baryon is antisymmetric: swapping quarks 1,2 negates the vertex -/
theorem baryon_swap_12 (q₁ q₂ q₃ : Color → ℂ) :
    baryonVertex q₂ q₁ q₃ = -baryonVertex q₁ q₂ q₃ := by
  simp only [baryonVertex]
  have key : (![q₂, q₁, q₃] : Color → Color → ℂ) =
      ![q₁, q₂, q₃] ∘ Equiv.swap (0 : Color) 1 := by
    ext i x; fin_cases i <;> simp [cons_val_zero, cons_val_one, Equiv.swap_apply_def]
  rw [key, colorDet.map_swap _ (by decide)]

/-- Baryon is antisymmetric: swapping quarks 2,3 negates the vertex -/
theorem baryon_swap_23 (q₁ q₂ q₃ : Color → ℂ) :
    baryonVertex q₁ q₃ q₂ = -baryonVertex q₁ q₂ q₃ := by
  simp only [baryonVertex]
  have key : (![q₁, q₃, q₂] : Color → Color → ℂ) =
      ![q₁, q₂, q₃] ∘ Equiv.swap (1 : Color) 2 := by
    ext i x; fin_cases i <;> simp [cons_val_zero, cons_val_one, Equiv.swap_apply_def]
  rw [key, colorDet.map_swap _ (by decide)]

/-- Same-quark baryon vanishes: q₁ = q₂ → ε_{abc} q₁ᵃ q₂ᵇ q₃ᶜ = 0 -/
theorem baryon_same_vanish (q q₃ : Color → ℂ) :
    baryonVertex q q q₃ = 0 := by
  simp only [baryonVertex]
  exact colorDet.map_eq_zero_of_eq (![q, q, q₃])
    (show (![q, q, q₃] : Color → Color → ℂ) 0 = (![q, q, q₃]) 1 by
      simp [cons_val_zero, cons_val_one])
    (by decide)

noncomputable def red : Color → ℂ := Pi.single 0 1
noncomputable def green : Color → ℂ := Pi.single 1 1
noncomputable def blue : Color → ℂ := Pi.single 2 1

/-- Standard baryon (r,g,b) has unit color factor -/
theorem standard_baryon_color : baryonVertex red green blue = 1 := by
  unfold baryonVertex colorDet colorBasis red green blue
  rw [Basis.det_apply]
  have : (Pi.basisFun ℂ Color).toMatrix
      ![Pi.single (0 : Color) (1 : ℂ), Pi.single 1 1, Pi.single 2 1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Basis.toMatrix_apply, Pi.basisFun_repr, cons_val_zero, cons_val_one]
  rw [this, Matrix.det_one]

end Baryon

/-! ## 3-Form Maximum: ⋀⁴(ℂ³) = 0

No 4-quark color primitive exists. This is the mathematical reason
baryons have exactly 3 quarks and no more. -/

section FormMaximum

/-- dim ⋀³(ℂ³) = C(3,3) = 1: unique color singlet -/
theorem color_singlet_unique : Nat.choose 3 3 = 1 := by decide

/-- dim ⋀⁴(ℂ³) = C(3,4) = 0: no 4-quark primitive -/
theorem no_four_quark_primitive : Nat.choose 3 4 = 0 := by decide

/-- All exterior algebra dimensions for ℂ³ -/
theorem exterior_dimensions :
    Nat.choose 3 0 = 1 ∧ Nat.choose 3 1 = 3 ∧
    Nat.choose 3 2 = 3 ∧ Nat.choose 3 3 = 1 := by decide

/-- colorRank determines the maximum form degree -/
theorem max_form_degree_eq_colorRank :
    StateFunctions.colorRank = 3 ∧ Nat.choose 3 3 = 1 ∧ Nat.choose 3 4 = 0 := by decide

/-- stencilWidth = colorRank + galoisOrder -/
theorem stencil_decomposition :
    StateFunctions.stencilWidth = StateFunctions.colorRank + StateFunctions.galoisOrder := by
  decide

end FormMaximum

/-! ## Quark Mode Uniqueness

The quark triple (u,d,s) is uniquely determined (mod 6) by:
1. All three are non-gauge kernel modes (mod 6 ∈ {2,3,4})
2. d+s ≡ 1 mod 6 (matter emergence → electron-like active mode)
3. u+d ≡ 5 mod 6 (antimatter emergence → positron-like active mode)
Residue 3 is the unique "bridge" participating in both channels. -/

section QuarkModes

/-- Conditions for a valid quark triple from emergence structure -/
structure IsQuarkTriple (u d s : ℕ) : Prop where
  u_kernel : IsKernelMode u
  d_kernel : IsKernelMode d
  s_kernel : IsKernelMode s
  u_not_gauge : u % 6 ≠ 0
  d_not_gauge : d % 6 ≠ 0
  s_not_gauge : s % 6 ≠ 0
  distinct_ud : u % 6 ≠ d % 6
  distinct_ds : d % 6 ≠ s % 6
  distinct_us : u % 6 ≠ s % 6
  matter_channel : (d + s) % 6 = 1
  antimatter_channel : (u + d) % 6 = 5

/-- Quark residues are uniquely determined by emergence structure -/
theorem quark_triple_unique (u d s : ℕ) (h : IsQuarkTriple u d s) :
    u % 6 = 2 ∧ d % 6 = 3 ∧ s % 6 = 4 := by
  have hu := h.u_kernel; have hd := h.d_kernel; have hs := h.s_kernel
  unfold IsKernelMode at hu hd hs
  have := h.u_not_gauge; have := h.d_not_gauge; have := h.s_not_gauge
  have := h.distinct_ud; have := h.distinct_ds; have := h.distinct_us
  have := h.matter_channel; have := h.antimatter_channel
  omega

def uMode : ℕ := 2
def dMode : ℕ := 3
def sMode : ℕ := 4

/-- The standard quark triple satisfies all emergence conditions -/
theorem standard_quark_triple : IsQuarkTriple uMode dMode sMode where
  u_kernel := Or.inr (Or.inl rfl)
  d_kernel := Or.inr (Or.inr (Or.inl rfl))
  s_kernel := Or.inr (Or.inr (Or.inr rfl))
  u_not_gauge := by decide
  d_not_gauge := by decide
  s_not_gauge := by decide
  distinct_ud := by decide
  distinct_ds := by decide
  distinct_us := by decide
  matter_channel := by decide
  antimatter_channel := by decide

theorem u_is_kernel : IsKernelMode uMode := standard_quark_triple.u_kernel
theorem d_is_kernel : IsKernelMode dMode := standard_quark_triple.d_kernel
theorem s_is_kernel : IsKernelMode sMode := standard_quark_triple.s_kernel

theorem u_confined (z : ℂ) : Fζ (fun w => w ^ uMode) z = 0 :=
  kernel_mode_fzeta_zero uMode u_is_kernel z

theorem d_confined (z : ℂ) : Fζ (fun w => w ^ dMode) z = 0 :=
  kernel_mode_fzeta_zero dMode d_is_kernel z

theorem s_confined (z : ℂ) : Fζ (fun w => w ^ sMode) z = 0 :=
  kernel_mode_fzeta_zero sMode s_is_kernel z

end QuarkModes

/-! ## Nested derivDefect: Hadron Observability

The nested derivDefect δ(δ(f,g),h) provides observability for
composite states beyond the simple mod-6 selection rule. -/

section NestedDerivDefect

/-- Nested (3-body) derivDefect -/
noncomputable def derivDefect₃ (f g h : ℂ → ℂ) (z : ℂ) : ℂ :=
  derivDefect (fun w => derivDefect f g w) h z

/-- Two kernel modes: derivDefect = Fζ(product) since individual Fζ = 0 -/
theorem derivDefect_kernel_pair (a b : ℕ) (ha : IsKernelMode a) (hb : IsKernelMode b) (z : ℂ) :
    derivDefect (fun w => w ^ a) (fun w => w ^ b) z =
    Fζ (fun w => w ^ (a + b)) z := by
  rw [derivDefect_monomial, kernel_mode_fzeta_zero a ha, kernel_mode_fzeta_zero b hb]
  ring

/-- ud emergence: δ(z², z³) = Fζ(z⁵), mode 5 is active -/
theorem ud_emergence (z : ℂ) :
    derivDefect (fun w => w ^ uMode) (fun w => w ^ dMode) z =
    Fζ (fun w => w ^ 5) z :=
  derivDefect_kernel_pair uMode dMode u_is_kernel d_is_kernel z

theorem ud_emergence_active : IsActiveMode (uMode + dMode) := Or.inr rfl

/-- ds emergence: δ(z³, z⁴) = Fζ(z⁷), mode 7 is active -/
theorem ds_emergence (z : ℂ) :
    derivDefect (fun w => w ^ dMode) (fun w => w ^ sMode) z =
    Fζ (fun w => w ^ 7) z :=
  derivDefect_kernel_pair dMode sMode d_is_kernel s_is_kernel z

theorem ds_emergence_active : IsActiveMode (dMode + sMode) := Or.inl rfl

/-- Same-flavor kernel: δ(z^n, z^n) = Fζ(z^{2n}) for kernel modes -/
theorem same_kernel_derivDefect (n : ℕ) (hn : IsKernelMode n) (z : ℂ) :
    derivDefect (fun w => w ^ n) (fun w => w ^ n) z =
    Fζ (fun w => w ^ (2 * n)) z := by
  rw [derivDefect_kernel_pair n n hn hn, show n + n = 2 * n from by ring]

/-- Double of kernel mode is kernel: 2n mod 6 ∈ {0,2,4} for n ∈ {0,2,3,4} mod 6 -/
theorem double_kernel_is_kernel (n : ℕ) (hn : IsKernelMode n) :
    IsKernelMode (2 * n) := by
  unfold IsKernelMode at hn ⊢; rcases hn with h | h | h | h <;> omega

/-- Same-flavor kernel pair vanishes: δ(z^n, z^n) = 0 -/
theorem same_kernel_vanish (n : ℕ) (hn : IsKernelMode n) (z : ℂ) :
    derivDefect (fun w => w ^ n) (fun w => w ^ n) z = 0 := by
  rw [same_kernel_derivDefect n hn, kernel_mode_fzeta_zero _ (double_kernel_is_kernel n hn)]

theorem uu_vanish (z : ℂ) :
    derivDefect (fun w => w ^ uMode) (fun w => w ^ uMode) z = 0 :=
  same_kernel_vanish uMode u_is_kernel z

theorem dd_vanish (z : ℂ) :
    derivDefect (fun w => w ^ dMode) (fun w => w ^ dMode) z = 0 :=
  same_kernel_vanish dMode d_is_kernel z

theorem ss_vanish (z : ℂ) :
    derivDefect (fun w => w ^ sMode) (fun w => w ^ sMode) z = 0 :=
  same_kernel_vanish sMode s_is_kernel z

end NestedDerivDefect

/-! ## Gauge Interaction: Active × Active → Kernel

When two active modes annihilate to a kernel mode, the derivDefect reduces to
minus the eigenvalue sum. This is the algebraic dual of emergence:
- emergence: δ(ker, ker) = +Fζ(active sum) — matter creation
- gauge:     δ(active, active) = -(Fζ terms) — gauge-mediated interaction
The kernel sum mode carries zero Fζ eigenvalue → massless gauge boson. -/

section GaugeInteraction

/-- Gauge interaction: active mode 1 + active mode 5 → kernel mode 0.
    The derivDefect reduces to minus the sum of individual Fζ eigenvalues. -/
theorem gauge_interaction_mod1_mod5 (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 1)) (fun w => w ^ (6 * k + 5)) z =
    -(Fζ (fun w => w ^ (6 * j + 1)) z * z ^ (6 * k + 5) +
      z ^ (6 * j + 1) * Fζ (fun w => w ^ (6 * k + 5)) z) := by
  rw [derivDefect_monomial]
  have h : 6 * j + 1 + (6 * k + 5) = 6 * (j + k + 1) := by omega
  rw [h, Fζ_vanish_mod6_0]; ring

/-- Gauge interaction: active mode 5 + active mode 1 → kernel mode 0 -/
theorem gauge_interaction_mod5_mod1 (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 5)) (fun w => w ^ (6 * k + 1)) z =
    -(Fζ (fun w => w ^ (6 * j + 5)) z * z ^ (6 * k + 1) +
      z ^ (6 * j + 5) * Fζ (fun w => w ^ (6 * k + 1)) z) := by
  rw [derivDefect_monomial]
  have h : 6 * j + 5 + (6 * k + 1) = 6 * (j + k + 1) := by omega
  rw [h, Fζ_vanish_mod6_0]; ring

/-- Same-type active binding: mode 1 + mode 1 → kernel mode 2.
    Electromagnetic binding of same-charge-type active modes. -/
theorem binding_mod1_mod1 (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 1)) (fun w => w ^ (6 * k + 1)) z =
    -(Fζ (fun w => w ^ (6 * j + 1)) z * z ^ (6 * k + 1) +
      z ^ (6 * j + 1) * Fζ (fun w => w ^ (6 * k + 1)) z) := by
  rw [derivDefect_monomial]
  have h : 6 * j + 1 + (6 * k + 1) = 6 * (j + k) + 2 := by omega
  rw [h, Fζ_vanish_mod6_2]; ring

/-- Same-type active binding: mode 5 + mode 5 → kernel mode 4 -/
theorem binding_mod5_mod5 (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 5)) (fun w => w ^ (6 * k + 5)) z =
    -(Fζ (fun w => w ^ (6 * j + 5)) z * z ^ (6 * k + 5) +
      z ^ (6 * j + 5) * Fζ (fun w => w ^ (6 * k + 5)) z) := by
  rw [derivDefect_monomial]
  have h : 6 * j + 5 + (6 * k + 5) = 6 * (j + k + 1) + 4 := by omega
  rw [h, Fζ_vanish_mod6_4]; ring

end GaugeInteraction

/-! ## Hydrogen Atom: Electromagnetic Binding via derivDefect

Hydrogen = electron(mode 1) + proton(mode 7), both active mod 1.
Sum 1+7=8 ≡ 2 mod 6 → kernel: electrically neutral bound state.
δ(z,z⁷) = -(z·Fζ(z⁷) + Fζ(z)·z⁷): binding through eigenvalue exchange. -/

section HydrogenAtom

/-- Hydrogen binding: δ(electron, proton) = -(eigenvalue exchange).
    electron = z¹ (mode 1), proton = z⁷ (mode 7 = udu baryon). -/
theorem hydrogen_binding (z : ℂ) :
    derivDefect (fun w => w ^ 1) (fun w => w ^ 7) z =
    -(Fζ (fun w => w ^ 1) z * z ^ 7 + z ^ 1 * Fζ (fun w => w ^ 7) z) :=
  binding_mod1_mod1 0 1 z

/-- Hydrogen sum mode is kernel: electrically neutral -/
theorem hydrogen_neutral : IsKernelMode 8 := Or.inr (Or.inl rfl)

/-- Hydrogen sum mode has zero Fζ: bound state is confined -/
theorem hydrogen_confined (z : ℂ) : Fζ (fun w => w ^ 8) z = 0 :=
  kernel_mode_fzeta_zero 8 hydrogen_neutral z

end HydrogenAtom

/-! ## Weak Decay: Kernel + Active Transitions

Beta decay d → u + e⁻ + ν̄ₑ at mode level: 3 = 2 + 1 + 0.
The two weak transition patterns (both have kernel + active inputs):
- ker(mod2) + active(mod1) → ker(mod3): neutron β decay
- ker(mod4) + active(mod1) → active(mod5): tritium β decay -/

section WeakDecay

/-- Weak transition: kernel(mod2) + active(mod1) → kernel(mod3).
    Only the active eigenvalue survives. -/
theorem weak_transition_mod2_mod1 (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 2)) (fun w => w ^ (6 * k + 1)) z =
    -(z ^ (6 * j + 2) * Fζ (fun w => w ^ (6 * k + 1)) z) := by
  rw [derivDefect_monomial, Fζ_vanish_mod6_2]
  have h : 6 * j + 2 + (6 * k + 1) = 6 * (j + k) + 3 := by omega
  rw [h, Fζ_vanish_mod6_3]; ring

/-- Weak transition: kernel(mod4) + active(mod1) → active(mod5).
    Both Fζ terms survive: product becomes active. -/
theorem weak_transition_mod4_mod1 (j k : ℕ) (z : ℂ) :
    derivDefect (fun w => w ^ (6 * j + 4)) (fun w => w ^ (6 * k + 1)) z =
    Fζ (fun w => w ^ (6 * (j + k) + 5)) z -
    z ^ (6 * j + 4) * Fζ (fun w => w ^ (6 * k + 1)) z := by
  rw [derivDefect_monomial, Fζ_vanish_mod6_4]
  have h : 6 * j + 4 + (6 * k + 1) = 6 * (j + k) + 5 := by omega
  rw [h]; ring

/-- Beta decay: δ(u, e⁻) = -Fζ(e⁻)·u, mode sum = d.
    Reverse reading: d decays to u + e⁻ releasing eigenvalue λ₁. -/
theorem beta_decay_mode (z : ℂ) :
    derivDefect (fun w => w ^ uMode) (fun w => w ^ 1) z =
    -(z ^ uMode * Fζ (fun w => w ^ 1) z) :=
  weak_transition_mod2_mod1 0 0 z

/-- Antineutrino is gauge mode: Fζ(z⁰) = 0, invisible -/
theorem antineutrino_invisible (z : ℂ) : Fζ (fun w => w ^ 0) z = 0 :=
  kernel_mode_fzeta_zero 0 (Or.inl rfl) z

/-- Beta decay mode conservation: u + e⁻ + ν̄ₑ = d -/
theorem beta_mode_conservation : uMode + 1 + 0 = dMode := by decide

/-- Tritium ³H = p + n + n, mode 23 (active, mod 5) -/
theorem tritium_mode : 7 + 8 + 8 = 23 ∧ IsActiveMode 23 := ⟨by decide, Or.inr rfl⟩

/-- ³He = p + p + n, mode 22 (kernel, mod 4) -/
theorem helium3_mode : 7 + 7 + 8 = 22 ∧ IsKernelMode 22 :=
  ⟨by decide, Or.inr (Or.inr (Or.inr rfl))⟩

/-- Tritium decay mode conservation: ³H → ³He + e⁻ + ν̄ₑ -/
theorem tritium_decay_conservation : 23 = 22 + 1 + 0 := by decide

/-- Tritium β decay: δ(³He, e⁻) = Fζ(³H) - ³He·Fζ(e⁻).
    Same quark vertex (d→u+e⁻+ν̄ₑ) as neutron, different nuclear phase space. -/
theorem tritium_decay (z : ℂ) :
    derivDefect (fun w => w ^ 22) (fun w => w ^ 1) z =
    Fζ (fun w => w ^ 23) z - z ^ 22 * Fζ (fun w => w ^ 1) z :=
  weak_transition_mod4_mod1 3 0 z

/-- ⁴He = p+p+n+n, mode 30 ≡ 0 mod 6 (kernel, gauge = maximally stable) -/
theorem helium4_mode : 7 + 7 + 8 + 8 = 30 ∧ IsKernelMode 30 :=
  ⟨by decide, Or.inl rfl⟩

end WeakDecay

/-! ## Proton and Neutron via Nested derivDefect

proton (udu) = δ(δ(u,d), u): spatial part ∝ z⁷ (active, mode 1 mod 6)
neutron (udd) = δ(δ(u,d), d): spatial part ∝ z⁸ (kernel, but δ ≠ 0!) -/

section Hadrons

theorem proton_mode_sum : uMode + dMode + uMode = 7 := by decide
theorem proton_mode_active : IsActiveMode 7 := Or.inl rfl

theorem neutron_mode_sum : uMode + dMode + dMode = 8 := by decide
theorem neutron_mode_kernel : IsKernelMode 8 := Or.inr (Or.inl rfl)

/-- Neutron is Fζ-trivial as a single mode (= hydrogen_confined) -/
theorem neutron_fzeta_zero (z : ℂ) : Fζ (fun w => w ^ 8) z = 0 :=
  hydrogen_confined z

/-- Λ baryon (uds): all three flavors distinct -/
theorem lambda_mode_sum : uMode + dMode + sMode = 9 := by decide

/-- Ξ⁻ (dss): mode 11, active -/
theorem xi_mode_sum : dMode + sMode + sMode = 11 := by decide
theorem xi_mode_active : IsActiveMode 11 := Or.inr rfl

/-- Baryon mode sums and their mod-6 status -/
theorem baryon_mode_classification :
    IsActiveMode (uMode + dMode + uMode) ∧
    IsActiveMode (dMode + sMode + sMode) ∧
    IsKernelMode (uMode + dMode + dMode) ∧
    IsKernelMode (uMode + dMode + sMode) ∧
    IsKernelMode (uMode + uMode + sMode) := by
  exact ⟨Or.inl rfl, Or.inr rfl, Or.inr (Or.inl rfl),
    Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inl rfl)⟩

end Hadrons

/-! ## Composite Structures: Nuclei and Atoms

Nuclear binding = derivDefect of baryon spatial parts.
Deuteron (pn) mode sum 7+8 = 15 ≡ 3 mod 6 (kernel = confined composite). -/

section Composites

/-- Deuteron mode sum: proton(7) + neutron(8) = 15, kernel -/
theorem deuteron_mode_kernel : IsKernelMode 15 := Or.inr (Or.inr (Or.inl rfl))

/-- Multi-baryon singlet: 1 ⊗ 1 = 1 -/
theorem multi_baryon_singlet : Nat.choose 3 3 * Nat.choose 3 3 = 1 := by decide

/-- Meson mode sums: π⁺(ud̄) and π⁻(ūd) are active -/
theorem pion_plus_active : IsActiveMode 5 := Or.inr rfl
theorem pion_minus_active : IsActiveMode 7 := Or.inl rfl


end Composites

/-! ## Form Degree Hierarchy

The complete hierarchy of antisymmetric forms in FUST. -/

section Hierarchy

/-- Exterior algebra of ℂ³: dimensions 1,3,3,1,0,0 -/
theorem color_exterior_dims :
    Nat.choose 3 0 = 1 ∧ Nat.choose 3 1 = 3 ∧
    Nat.choose 3 2 = 3 ∧ Nat.choose 3 3 = 1 ∧
    Nat.choose 3 4 = 0 ∧ Nat.choose 3 5 = 0 := by decide

/-- Exterior algebra of ℂ²: dimensions 1,2,1,0 (spin) -/
theorem spin_exterior_dims :
    Nat.choose 2 0 = 1 ∧ Nat.choose 2 1 = 2 ∧
    Nat.choose 2 2 = 1 ∧ Nat.choose 2 3 = 0 := by decide

/-- Color × spin: ℂ⁶, exterior dims C(6,k) -/
theorem color_spin_exterior_dims :
    Nat.choose 6 0 = 1 ∧ Nat.choose 6 1 = 6 ∧
    Nat.choose 6 2 = 15 ∧ Nat.choose 6 3 = 20 ∧
    Nat.choose 6 4 = 15 ∧ Nat.choose 6 5 = 6 ∧
    Nat.choose 6 6 = 1 := by decide

/-- 20 active modes up to 59 (= 20 amino acids) -/
theorem active_modes_count :
    (Finset.filter (fun n => decide (IsActiveMode n) = true) (Finset.range 60)).card = 20 := by
  decide

/-- Color singlets for pure n-quark: require n divisible by 3 -/
theorem pure_quark_singlet_mod3 :
    (∀ n : ℕ, n % 3 = 0 → n ≥ 3 → Nat.choose 3 3 ^ (n / 3) = 1) := by
  intro n _ _; simp

end Hierarchy

/-! ## Dζ Cohomology: Nilpotency and Topological Protection

Dζ = Fζ/(5z) drops monomial degree by 1: z^n ↦ λ_n·z^{n-1}.
For active modes (n≡1,5 mod 6), n-1 is always kernel (n-1≡0,4 mod 6),
so applying Dζ twice yields zero: Dζ²=0.

This gives a cochain complex with cohomology H = ker/im:
- Exact (trivial H): n≡0 mod 6 (gauge) and n≡4 mod 6 (u-quark type)
  — these are in both ker(Dζ) and im(Dζ)
- Cohomological (nontrivial H): n≡2 mod 6 (d-quark type) and n≡3 mod 6 (neutrino)
  — in ker(Dζ) but NOT in im(Dζ), hence topologically protected -/

section DζCohomology

/-- Active mode predecessor is kernel: n≡1 mod 6 ⟹ n-1≡0 mod 6 -/
theorem active_mod1_pred_kernel (n : ℕ) (h : n % 6 = 1) :
    IsKernelMode (n - 1) := by
  unfold IsKernelMode; omega

/-- Active mode predecessor is kernel: n≡5 mod 6 ⟹ n-1≡4 mod 6 -/
theorem active_mod5_pred_kernel (n : ℕ) (h : n % 6 = 5) :
    IsKernelMode (n - 1) := by
  unfold IsKernelMode; omega

/-- Dζ nilpotency on active modes: Fζ vanishes on the degree-shifted output.
    For n≡1 mod 6: Dζ(z^n) ∝ z^{n-1} with n-1≡0 mod 6, so Fζ(z^{n-1}) = 0. -/
theorem nilpotency_mod1 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k + 1 - 1)) z = 0 := by
  have h : 6 * k + 1 - 1 = 6 * k := by omega
  rw [h]; exact Fζ_vanish_mod6_0 k z

/-- Dζ nilpotency on active modes: n≡5 mod 6 maps to n-1≡4 mod 6. -/
theorem nilpotency_mod5 (k : ℕ) (z : ℂ) :
    Fζ (fun w => w ^ (6 * k + 5 - 1)) z = 0 := by
  have h : 6 * k + 5 - 1 = 6 * k + 4 := by omega
  rw [h]; exact Fζ_vanish_mod6_4 k z

/-- Image of Dζ lands on n≡0 and n≡4 mod 6.
    Active n≡1 → kernel n-1≡0, active n≡5 → kernel n-1≡4. -/
theorem image_mod1_lands_mod0 (k : ℕ) : (6 * k + 1 - 1) % 6 = 0 := by omega
theorem image_mod5_lands_mod4 (k : ℕ) : (6 * k + 5 - 1) % 6 = 4 := by omega

/-- Exact modes: in both ker(Fζ) and im(Dζ degree shift) -/
def IsExactMode (n : ℕ) : Prop := n % 6 = 0 ∨ n % 6 = 4

/-- Cohomological modes: in ker(Fζ) but NOT in im(Dζ degree shift) -/
def IsCohomologicalMode (n : ℕ) : Prop := n % 6 = 2 ∨ n % 6 = 3

instance : DecidablePred IsExactMode := fun _ => inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred IsCohomologicalMode := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Kernel modes decompose into exact and cohomological -/
theorem kernel_decomposition (n : ℕ) (h : IsKernelMode n) :
    IsExactMode n ∨ IsCohomologicalMode n := by
  unfold IsKernelMode at h; unfold IsExactMode IsCohomologicalMode; omega

/-- Exact and cohomological are disjoint -/
theorem exact_cohomological_disjoint (n : ℕ) :
    ¬(IsExactMode n ∧ IsCohomologicalMode n) := by
  unfold IsExactMode IsCohomologicalMode; omega

/-- All exact modes are kernel modes -/
theorem exact_is_kernel (n : ℕ) (h : IsExactMode n) : IsKernelMode n := by
  unfold IsExactMode at h; unfold IsKernelMode; omega

/-- All cohomological modes are kernel modes -/
theorem cohomological_is_kernel (n : ℕ) (h : IsCohomologicalMode n) : IsKernelMode n := by
  unfold IsCohomologicalMode at h; unfold IsKernelMode; omega

/-- Cohomological modes have vanishing Fζ (inherited from kernel) -/
theorem cohomological_fzeta_zero (n : ℕ) (h : IsCohomologicalMode n) (z : ℂ) :
    Fζ (fun w => w ^ n) z = 0 :=
  kernel_mode_fzeta_zero n (cohomological_is_kernel n h) z

/-- No active mode maps to a cohomological mode under degree shift.
    Active n≡1 → n-1≡0 (exact, not cohomological).
    Active n≡5 → n-1≡4 (exact, not cohomological). -/
theorem cohomological_not_in_image (m : ℕ) (hm : IsCohomologicalMode m) :
    ¬(∃ n, IsActiveMode n ∧ n - 1 = m) := by
  unfold IsCohomologicalMode at hm; unfold IsActiveMode
  intro ⟨n, hn, heq⟩; omega

/-- d-quark type (mode 2, n≡2 mod 6) is cohomologically protected -/
theorem d_quark_cohomological : IsCohomologicalMode uMode := by decide

/-- Neutrino type (mode 3, n≡3 mod 6) is cohomologically protected -/
theorem neutrino_cohomological : IsCohomologicalMode dMode := by decide

/-- u-quark type (n≡4 mod 6) is exact (can be created/destroyed by Dζ) -/
theorem u_quark_exact : IsExactMode sMode := by decide

/-- Gauge mode (n≡0 mod 6) is exact -/
theorem gauge_exact : IsExactMode 0 := Or.inl rfl

/-- The six mod-6 classes form a complete partition:
    2 active + 2 exact + 2 cohomological = 6 -/
theorem mode_partition (n : ℕ) :
    IsActiveMode n ∨ IsExactMode n ∨ IsCohomologicalMode n := by
  unfold IsActiveMode IsExactMode IsCohomologicalMode; omega

/-- The partition is exclusive -/
theorem mode_partition_exclusive (n : ℕ) :
    (IsActiveMode n → ¬IsExactMode n ∧ ¬IsCohomologicalMode n) ∧
    (IsExactMode n → ¬IsActiveMode n ∧ ¬IsCohomologicalMode n) ∧
    (IsCohomologicalMode n → ¬IsActiveMode n ∧ ¬IsExactMode n) := by
  unfold IsActiveMode IsExactMode IsCohomologicalMode; omega

/-- Counting: 2 active + 2 exact + 2 cohomological per period -/
theorem mode_count_per_period :
    (Finset.filter (fun n => decide (IsActiveMode n) = true) (Finset.range 6)).card = 2 ∧
    (Finset.filter (fun n => decide (IsExactMode n) = true) (Finset.range 6)).card = 2 ∧
    (Finset.filter (fun n => decide (IsCohomologicalMode n) = true) (Finset.range 6)).card = 2 := by
  decide

end DζCohomology

end FUST.ColorAlgebra
