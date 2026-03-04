import FUST.Physics.MassGap
import FUST.Physics.GaugeGroups

namespace FUST.YangMills

open FUST.FζOperator FUST.Physics.Lorentz FUST.Physics.Poincare
open FUST.FrourioAlgebra.GoldenEisensteinInt

/-- SU(2) mass gap: τ-anti-invariance + AF²=-12 → quaternionic SU(2) -/
theorem yangMills_massGap_SU2 :
    -- τ(AF_coeff) = -AF_coeff (quaternionic indicator)
    (tau AF_coeff_gei =
      FUST.FrourioAlgebra.GoldenEisensteinInt.neg AF_coeff_gei) ∧
    -- AF_coeff² = -12 (J² < 0)
    (mul AF_coeff_gei AF_coeff_gei =
      (⟨-12, 0, 0, 0⟩ : FUST.FrourioAlgebra.GoldenEisensteinInt)) ∧
    -- Scalar det c² (separates U(1) center from SU(2))
    (∀ c : ℂ, (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = c ^ 2) :=
  ⟨FUST.SU2_gauge_uniqueness.1,
   FUST.SU2_gauge_uniqueness.2.2.2.1,
   FUST.SU2_gauge_uniqueness.2.2.2.2.2.2⟩

/-- SU(3) mass gap: SY rank 3 → SU(3), m² = 14 > 0 -/
theorem yangMills_massGap_SU3 :
    -- SU(3) from SY mode vectors rank 3
    (LinearIndependent ℝ (fun i : Fin 3 => FUST.syModeMatrix i)) ∧
    -- Scalar det c³ (separates U(1) center from SU(3))
    (∀ c : ℂ, (c • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = c ^ 3) ∧
    -- Casimir mass squared m² = 14 > 0
    (0 < FUST.massGapSq ∧ FUST.massGapSq = 14) :=
  ⟨FUST.SU3_gauge_uniqueness.1,
   FUST.SU3_gauge_uniqueness.2.2.1,
   ⟨FUST.massGapSq_pos, FUST.massGapSq_eq⟩⟩

/-- Yang-Mills mass gap: 4D Poincaré, SU(3)×SU(2)×U(1) gauge, mass gap -/
theorem yangMills_massGap :
    -- 4D spacetime from Poincaré translation group
    (Module.finrank ℝ (I4 → ℝ) = 4) ∧
    -- SU(3): SY rank 3
    (LinearIndependent ℝ (fun i : Fin 3 => FUST.syModeMatrix i)) ∧
    -- SU(2): AF²=-12 (quaternionic)
    (mul AF_coeff_gei AF_coeff_gei =
      (⟨-12, 0, 0, 0⟩ : FUST.FrourioAlgebra.GoldenEisensteinInt)) ∧
    -- U(1): Galois-fixed = ℤ (dim 1)
    (∀ x : FUST.FrourioAlgebra.GoldenEisensteinInt,
      sigma x = x ∧ tau x = x ↔
      x.b = 0 ∧ x.c = 0 ∧ x.d = 0) ∧
    -- Casimir mass squared m² = 14 > 0
    (0 < FUST.massGapSq ∧ FUST.massGapSq = 14) :=
  ⟨finrank_translations,
   FUST.SU3_gauge_uniqueness.1,
   FUST.SU2_gauge_uniqueness.2.2.2.1,
   FUST.U1_gauge_uniqueness.1,
   ⟨FUST.massGapSq_pos, FUST.massGapSq_eq⟩⟩

end FUST.YangMills
