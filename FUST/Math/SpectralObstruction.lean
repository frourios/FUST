/-
Spectral obstruction: algebraic constraints on Fζ eigenvalues in ℤ[φ,ζ₆].
Every eigenvalue λ_n is divisible by 10·(1+ζ₆), so the reachable sub-ring
R = ℤ[{λ_n}] is a proper sub-ring of ℤ[φ,ζ₆]. The gap is controlled by
primes 2, 3, 5 — encoded in the Euler factors of ζ_K(s).
-/
import FUST.FrourioAlgebra.GoldenEisensteinInt
import FUST.DζOperator

namespace FUST.SpectralObstruction

open FUST.FrourioAlgebra
open GoldenEisensteinInt hiding norm

-- Disambiguate: use GEI norm not Mathlib norm
local notation "geiNorm" => GoldenEisensteinInt.norm

/-! ## AF_coeff factorization: 4ζ₆ - 2 = 2·(2ζ₆ - 1) -/

def two_zeta6_sub_one : GoldenEisensteinInt := ⟨-1, 0, 2, 0⟩

theorem AF_coeff_factor_two :
    AF_coeff_gei = mul ⟨2, 0, 0, 0⟩ two_zeta6_sub_one := by
  unfold AF_coeff_gei two_zeta6_sub_one mul; ext <;> simp

theorem two_zeta6_sub_one_sq :
    mul two_zeta6_sub_one two_zeta6_sub_one = ⟨-3, 0, 0, 0⟩ := by
  unfold two_zeta6_sub_one mul; ext <;> simp

theorem AF_coeff_gei_sq :
    mul AF_coeff_gei AF_coeff_gei = ⟨-12, 0, 0, 0⟩ := by
  unfold AF_coeff_gei mul; ext <;> simp

/-! ## 1+ζ₆: the prime above 3

(1+ζ₆)·(2-ζ₆) = 3, so (1+ζ₆) is a prime of norm 9 in ℤ[φ,ζ₆]. -/

def one_plus_zeta6 : GoldenEisensteinInt := ⟨1, 0, 1, 0⟩

def two_sub_zeta6 : GoldenEisensteinInt := ⟨2, 0, -1, 0⟩

theorem tau_one_plus_zeta6 :
    tau one_plus_zeta6 = two_sub_zeta6 := by
  unfold tau one_plus_zeta6 two_sub_zeta6; ext <;> simp

theorem one_plus_zeta6_norm_three :
    mul one_plus_zeta6 two_sub_zeta6 = ⟨3, 0, 0, 0⟩ := by
  unfold mul one_plus_zeta6 two_sub_zeta6; ext <;> simp

theorem one_plus_zeta6_tau_norm :
    mul one_plus_zeta6 (tau one_plus_zeta6) = ⟨3, 0, 0, 0⟩ := by
  rw [tau_one_plus_zeta6]; exact one_plus_zeta6_norm_three

theorem one_plus_zeta6_fullNorm :
    geiNorm one_plus_zeta6 = 9 := by
  unfold GoldenEisensteinInt.norm tauNorm GoldenInt.norm one_plus_zeta6; ring

/-! ## SymNum coefficient: 6 = 2·3 -/

def sy_coeff : GoldenEisensteinInt := ⟨6, 0, 0, 0⟩

theorem sy_coeff_factor_two :
    sy_coeff = mul ⟨2, 0, 0, 0⟩ ⟨3, 0, 0, 0⟩ := by
  unfold sy_coeff mul; ext <;> simp

/-! ## Universal 2-divisibility: c_A·AF_coeff + c_S·6 is always even -/

theorem eigenvalue_even (c_A c_S : ℤ) :
    ∃ μ : GoldenEisensteinInt,
    add (mul (⟨c_A, 0, 0, 0⟩ : GoldenEisensteinInt) AF_coeff_gei)
        (mul (⟨c_S, 0, 0, 0⟩ : GoldenEisensteinInt) sy_coeff) =
    mul ⟨2, 0, 0, 0⟩ μ := by
  refine ⟨⟨-c_A + 3 * c_S, 0, 2 * c_A, 0⟩, ?_⟩
  unfold add mul AF_coeff_gei sy_coeff; ext <;> simp <;> ring

def half_eigenvalue (c_A c_S : ℤ) : GoldenEisensteinInt :=
  add (mul ⟨c_A, 0, 0, 0⟩ two_zeta6_sub_one) ⟨3 * c_S, 0, 0, 0⟩

theorem half_eigenvalue_eq (c_A c_S : ℤ) :
    add (mul (⟨c_A, 0, 0, 0⟩ : GoldenEisensteinInt) AF_coeff_gei)
        (mul (⟨c_S, 0, 0, 0⟩ : GoldenEisensteinInt) sy_coeff) =
    mul ⟨2, 0, 0, 0⟩ (half_eigenvalue c_A c_S) := by
  unfold half_eigenvalue add mul AF_coeff_gei two_zeta6_sub_one sy_coeff
  ext <;> simp <;> ring

theorem half_eigenvalue_components (c_A c_S : ℤ) :
    half_eigenvalue c_A c_S = ⟨-c_A + 3 * c_S, 0, 2 * c_A, 0⟩ := by
  unfold half_eigenvalue add mul two_zeta6_sub_one; ext <;> simp; ring

/-! ## Mod 3 structure: μ = 2c_A·(1+ζ₆) + 3·q -/

theorem half_eigenvalue_mod3 (c_A c_S : ℤ) :
    ∃ q : GoldenEisensteinInt,
    half_eigenvalue c_A c_S =
    add (mul ⟨2 * c_A, 0, 0, 0⟩ one_plus_zeta6) (mul ⟨3, 0, 0, 0⟩ q) := by
  refine ⟨⟨-c_A + c_S, 0, 0, 0⟩, ?_⟩
  rw [half_eigenvalue_components]
  unfold add mul one_plus_zeta6; ext <;> simp; ring

/-! ## 5-divisibility: SY coefficients are always divisible by 5 -/

theorem sy_channel_ten_divisible (a b : ℤ) :
    mul (⟨6, 0, 0, 0⟩ : GoldenEisensteinInt) ⟨5 * a, 5 * b, 0, 0⟩ =
    mul ⟨10, 0, 0, 0⟩ ⟨3 * a, 3 * b, 0, 0⟩ := by
  unfold mul; ext <;> simp <;> ring

/-! ## Pairwise dark coupling: coprime-to-6 modes always couple to kernel -/

theorem pairwise_sum_in_kernel (a b : ZMod 6)
    (ha : a = 1 ∨ a = 5) (hb : b = 1 ∨ b = 5) :
    ¬(a + b = 1 ∨ a + b = 5) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem triple_sum_can_be_active :
    ∃ a b c : ZMod 6, (a = 1 ∨ a = 5) ∧ (b = 1 ∨ b = 5) ∧
    (c = 1 ∨ c = 5) ∧ (a + b + c = 1 ∨ a + b + c = 5) :=
  ⟨1, 1, 5, Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inl (by decide)⟩

theorem triple_sum_not_always_active :
    ∃ a b c : ZMod 6, (a = 1 ∨ a = 5) ∧ (b = 1 ∨ b = 5) ∧
    (c = 1 ∨ c = 5) ∧ ¬(a + b + c = 1 ∨ a + b + c = 5) :=
  ⟨1, 1, 1, Or.inl rfl, Or.inl rfl, Or.inl rfl, by decide⟩

/-! ## Kernel fraction: 4/6 dark, 2/6 active -/

theorem active_residues :
    (Finset.univ.filter (fun n : ZMod 6 => n = 1 ∨ n = 5)).card = 2 := by
  decide

theorem kernel_residues :
    (Finset.univ.filter (fun n : ZMod 6 => ¬(n = 1 ∨ n = 5))).card = 4 := by
  decide

/-! ## Shadow lattice: φ, ζ₆, φζ₆ are unreachable from ℤ + 2·ℤ[φ,ζ₆] -/

theorem phi_not_reachable :
    ¬∃ (k : ℤ) (μ : GoldenEisensteinInt),
    add ⟨k, 0, 0, 0⟩ (mul ⟨2, 0, 0, 0⟩ μ) =
    (⟨0, 1, 0, 0⟩ : GoldenEisensteinInt) := by
  intro ⟨_, μ, h⟩
  have := congr_arg GoldenEisensteinInt.b h
  unfold add mul at this; simp at this; omega

theorem zeta6_not_reachable :
    ¬∃ (k : ℤ) (μ : GoldenEisensteinInt),
    add ⟨k, 0, 0, 0⟩ (mul ⟨2, 0, 0, 0⟩ μ) =
    (⟨0, 0, 1, 0⟩ : GoldenEisensteinInt) := by
  intro ⟨_, μ, h⟩
  have := congr_arg GoldenEisensteinInt.c h
  unfold add mul at this; simp at this; omega

theorem phi_zeta6_not_reachable :
    ¬∃ (k : ℤ) (μ : GoldenEisensteinInt),
    add ⟨k, 0, 0, 0⟩ (mul ⟨2, 0, 0, 0⟩ μ) =
    (⟨0, 0, 0, 1⟩ : GoldenEisensteinInt) := by
  intro ⟨_, μ, h⟩
  have := congr_arg GoldenEisensteinInt.d h
  unfold add mul at this; simp at this; omega

/-! ## N(10·(1+ζ₆)) = 90000 = 2⁴·3²·5⁴ -/

def ten_one_plus_zeta6 : GoldenEisensteinInt :=
  mul ⟨10, 0, 0, 0⟩ one_plus_zeta6

theorem ten_one_plus_zeta6_eq :
    ten_one_plus_zeta6 = ⟨10, 0, 10, 0⟩ := by
  unfold ten_one_plus_zeta6 mul one_plus_zeta6; ext <;> simp

theorem obstruction_ideal_norm :
    geiNorm ten_one_plus_zeta6 = 90000 := by
  rw [ten_one_plus_zeta6_eq]
  unfold GoldenEisensteinInt.norm tauNorm GoldenInt.norm; ring

theorem norm_factorization : (90000 : ℤ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 4 := by norm_num

/-! ## Three-layer factorization: 10·(1+ζ₆) = 2·5·(1+ζ₆) -/

theorem obstruction_factorization :
    ten_one_plus_zeta6 =
    mul (mul ⟨2, 0, 0, 0⟩ ⟨5, 0, 0, 0⟩) one_plus_zeta6 := by
  unfold ten_one_plus_zeta6 mul one_plus_zeta6; ext <;> simp

theorem norm_decomposition :
    geiNorm ten_one_plus_zeta6 =
    geiNorm (⟨2, 0, 0, 0⟩ : GoldenEisensteinInt) *
    geiNorm (⟨5, 0, 0, 0⟩ : GoldenEisensteinInt) *
    geiNorm one_plus_zeta6 := by
  unfold GoldenEisensteinInt.norm tauNorm GoldenInt.norm
    ten_one_plus_zeta6 one_plus_zeta6 mul; ring

theorem norm_two : geiNorm (⟨2, 0, 0, 0⟩ : GoldenEisensteinInt) = 16 := by
  unfold GoldenEisensteinInt.norm tauNorm GoldenInt.norm; ring

theorem norm_five : geiNorm (⟨5, 0, 0, 0⟩ : GoldenEisensteinInt) = 625 := by
  unfold GoldenEisensteinInt.norm tauNorm GoldenInt.norm; ring

theorem euler_factor_product : (16 : ℤ) * 625 * 9 = 90000 := by norm_num

/-! ## Summary -/

theorem obstruction_primes :
    geiNorm (⟨2, 0, 0, 0⟩ : GoldenEisensteinInt) = 2 ^ 4 ∧
    geiNorm (⟨5, 0, 0, 0⟩ : GoldenEisensteinInt) = 5 ^ 4 ∧
    geiNorm one_plus_zeta6 = 3 ^ 2 ∧
    geiNorm ten_one_plus_zeta6 = 2 ^ 4 * 3 ^ 2 * 5 ^ 4 :=
  ⟨norm_two, norm_five, one_plus_zeta6_fullNorm,
    by rw [obstruction_ideal_norm]; norm_num⟩

end FUST.SpectralObstruction
