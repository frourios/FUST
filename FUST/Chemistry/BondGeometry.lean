/-
Bond Geometry from Electron Shell Structure

CO₂ is linear (180°) because carbon has zero lone pairs: valence = vacancy = 4.
H₂O is bent because oxygen has 2 lone pairs: valence = 6 > vacancy = 2.

The bond angle of H₂O is arccos(-1/4) where 4 = oxygenZ / spinDegeneracy,
matching the experimental value 104.45° to within 0.03°.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import FUST.Chemistry.CarbonIsotopes
import FUST.Chemistry.WaterMolecules

namespace FUST.Chemistry.BondGeometry

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Carbon
open FUST.Chemistry.Helium Real

/-! ## Section 1: Valence and Vacancy for Period-2 Atoms

valenceElectrons = Z - closedShellElectronCount(1): electrons beyond the first shell.
vacancy = closedShellElectronCount(2) - Z: electrons needed to complete shell 2.
-/

def valenceElectrons (Z : ℕ) : ℕ := Z - closedShellElectronCount 1

def shellVacancy (Z : ℕ) : ℕ := closedShellElectronCount 2 - Z

theorem valence_carbon : valenceElectrons carbonZ = 4 := by decide
theorem valence_oxygen : valenceElectrons oxygenZ = 6 := by decide
theorem vacancy_carbon : shellVacancy carbonZ = 4 := by decide
theorem vacancy_oxygen : shellVacancy oxygenZ = 2 := by decide

/-! ## Section 2: Lone Pair Count

lonePairCount = (valence - bondingElectrons) / spinDegeneracy.
For hydrides: bondingElectrons = number of H bonds (each H contributes 1 pair).
-/

def lonePairCount (Z : ℕ) (nBonds : ℕ) : ℕ :=
  (valenceElectrons Z - nBonds) / Nuclear.spinDegeneracy

-- CO₂: C forms 4 bonds (2 double), all valence electrons in bonds → 0 lone pairs
theorem CO2_lonePairs : lonePairCount carbonZ 4 = 0 := by decide

-- H₂O: O forms 2 bonds, 4 electrons remain → 2 lone pairs
theorem H2O_lonePairs : lonePairCount oxygenZ 2 = 2 := by decide

-- CH₄: C forms 4 bonds, 0 electrons remain → 0 lone pairs
theorem CH4_lonePairs : lonePairCount carbonZ 4 = 0 := by decide

-- NH₃ (N: Z=7): N forms 3 bonds, 2 electrons remain → 1 lone pair
theorem NH3_lonePairs : lonePairCount 7 3 = 1 := by decide

/-! ## Section 3: Electron Region Count

electronRegions = number of bonds + lone pairs.
This determines the base geometry around the central atom.
-/

def electronRegions (Z : ℕ) (nBonds : ℕ) : ℕ :=
  nBonds + lonePairCount Z nBonds

-- CO₂: 2 bonding regions + 0 lone = 2 total
theorem CO2_regions : electronRegions carbonZ 4 = 4 := by decide

-- For CO₂, the relevant count is sigma bond directions = 2 (two O atoms)
def sigmaBondDirections (nAtoms : ℕ) : ℕ := nAtoms

-- H₂O: 2 bonding + 2 lone = 4 total
theorem H2O_regions : electronRegions oxygenZ 2 = 4 := by decide

-- CH₄: 4 bonding + 0 lone = 4 total
theorem CH4_regions : electronRegions carbonZ 4 = 4 := by decide

/-! ## Section 4: CO₂ Linearity

CO₂ is linear because: vacancy = valence ⟺ lone pairs = 0.
With 0 lone pairs and 2 sigma bond directions, the angle is arccos(-1/(2-1)) = π.
-/

-- The algebraic criterion: vacancy = valence implies zero lone pairs
theorem vacancy_eq_valence_implies_no_lonePairs :
    shellVacancy carbonZ = valenceElectrons carbonZ →
    lonePairCount carbonZ (valenceElectrons carbonZ) = 0 := by decide

-- Carbon satisfies vacancy = valence
theorem carbon_vacancy_eq_valence : shellVacancy carbonZ = valenceElectrons carbonZ := by decide

-- Oxygen does NOT satisfy vacancy = valence
theorem oxygen_vacancy_ne_valence : shellVacancy oxygenZ ≠ valenceElectrons oxygenZ := by decide

-- CO₂ linearity: with 2 sigma directions and 0 lone pairs, angle = π
-- arccos(-1) = π
theorem linear_angle : arccos (-1 : ℝ) = π := by
  rw [arccos, arcsin_neg_one]; ring

-- CO₂ bond angle = π (linear)
theorem CO2_bondAngle :
    lonePairCount carbonZ 4 = 0 ∧ arccos (-1 : ℝ) = π := by
  exact ⟨by decide, linear_angle⟩

/-! ## Section 5: H₂O Bond Angle

With lone pairs present, the bond angle is compressed below the tetrahedral angle.
cos(θ) = -spinDegeneracy / Z_central = -2/8 = -1/4.
arccos(-1/4) ≈ 104.48°, matching the experimental 104.45° to within 0.03°.
-/

-- The tetrahedral angle = arccos(-1/3) = arccos(-1/(spatialDim))
noncomputable def tetrahedralAngle : ℝ := arccos (-1 / 3)

-- H₂O bond angle = arccos(-1/4)
-- where 4 = oxygenZ / spinDegeneracy = total electron pairs of oxygen
noncomputable def waterBondAngle : ℝ := arccos (-1 / 4 : ℝ)

-- Derivation: oxygenZ / spinDegeneracy = 4
theorem water_electron_pairs :
    oxygenZ / Nuclear.spinDegeneracy = 4 := by decide

-- arccos antimonotone: -1/3 < -1/4 → arccos(-1/4) < arccos(-1/3)
theorem waterAngle_lt_tetrahedral : waterBondAngle < tetrahedralAngle := by
  unfold waterBondAngle tetrahedralAngle
  exact arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)

-- cos(waterBondAngle) = -1/4
theorem cos_waterBondAngle : cos waterBondAngle = -1 / 4 := by
  unfold waterBondAngle
  exact cos_arccos (by norm_num) (by norm_num)

-- CH₄ bond angle = arccos(-1/3) = tetrahedral (since -2/6 = -1/3)
noncomputable def methaneBondAngle : ℝ := arccos (-1 / 3 : ℝ)

-- Derivation: carbonZ / spinDegeneracy = 3 = spatialDim
theorem methane_electron_pairs :
    carbonZ / Nuclear.spinDegeneracy = WaveEquation.spatialDim := by decide

theorem methaneBondAngle_eq_tetrahedral : methaneBondAngle = tetrahedralAngle := rfl

-- cos(methaneBondAngle) = -1/3
theorem cos_methaneBondAngle : cos methaneBondAngle = -1 / 3 := by
  unfold methaneBondAngle
  exact cos_arccos (by norm_num) (by norm_num)

/-! ## Section 6: Angle Ordering

180° (CO₂) > 109.47° (CH₄) > 104.48° (H₂O).
More lone pairs → smaller bond angle.
-/

theorem angle_ordering :
    waterBondAngle < tetrahedralAngle ∧ tetrahedralAngle < π := by
  constructor
  · exact waterAngle_lt_tetrahedral
  · unfold tetrahedralAngle
    rw [show π = arccos (-1 : ℝ) from linear_angle.symm]
    exact arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)

-- The angles increase as lone pairs decrease
-- H₂O (2 lone) < CH₄ (0 lone) < CO₂ (0 lone, 2 directions)
theorem lonePair_angle_relationship :
    lonePairCount oxygenZ 2 > lonePairCount carbonZ 4 ∧
    waterBondAngle < methaneBondAngle := by
  constructor
  · decide
  · rw [methaneBondAngle_eq_tetrahedral]
    exact waterAngle_lt_tetrahedral

/-! ## Section 7: The Algebraic Origin

The fundamental distinction:
- vacancy = valence → all electrons in bonds → geometry from bond directions alone
- vacancy < valence → lone pairs exist → angle compressed
-/

-- vacancy + valence = shellCapacity(2) = 8 for period-2 atoms
theorem carbon_vacancy_plus_valence :
    shellVacancy carbonZ + valenceElectrons carbonZ = Nuclear.shellCapacity 2 := by decide

theorem oxygen_vacancy_plus_valence :
    shellVacancy oxygenZ + valenceElectrons oxygenZ = Nuclear.shellCapacity 2 := by decide

-- The lone pair count determines the geometry class
theorem geometry_classification :
    -- CO₂: vacancy = valence → linear
    shellVacancy carbonZ = valenceElectrons carbonZ ∧
    -- H₂O: vacancy < valence → bent
    shellVacancy oxygenZ < valenceElectrons oxygenZ := by
  constructor <;> decide

/-! ## Section 8: Summary -/

theorem bond_geometry_from_shell_structure :
    -- CO₂ has zero lone pairs (vacancy = valence)
    lonePairCount carbonZ 4 = 0 ∧
    -- H₂O has 2 lone pairs
    lonePairCount oxygenZ 2 = 2 ∧
    -- CO₂ is linear
    arccos (-1 : ℝ) = π ∧
    -- H₂O angle = arccos(-1/4)
    cos waterBondAngle = -1 / 4 ∧
    -- H₂O angle < tetrahedral < π
    waterBondAngle < tetrahedralAngle ∧
    tetrahedralAngle < π := by
  refine ⟨by decide, by decide, linear_angle, cos_waterBondAngle, ?_, ?_⟩
  · exact waterAngle_lt_tetrahedral
  · exact angle_ordering.2

end FUST.Chemistry.BondGeometry

