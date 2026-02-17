/-
20 Standard Amino Acids from FDim Structure

Each amino acid has (Z, N, e=Z) from its molecular formula.
FDim = dimAtom Z N Z, effectiveDegree = 18Z + 15N + 1.
Count 20 = nuclearMagic(2) = hoMagic(2).
Leu/Ile isomers share the same FDim.
Peptide bond = condensation releasing H₂O.
-/

import FUST.Chemistry.SulfurAtom
import FUST.Chemistry.Nucleotides

namespace FUST.Chemistry.AminoAcid

open FUST FUST.Dim FUST.Chemistry FUST.Chemistry.Oxygen
open FUST.Chemistry.Dihydrogen
open FUST.Chemistry.Carbon FUST.Chemistry.Nitrogen
open FUST.Chemistry.Sulfur FUST.Chemistry.Nucleotide

set_option maxRecDepth 8192

/-! ## Section 1: Amino Acid Parameters

Each amino acid as (Z, N) pair. Neutral molecules: e = Z.
-/

-- Nonpolar, aliphatic
abbrev glyZ : ℕ := 40
abbrev glyN : ℕ := 35   -- C₂H₅NO₂
abbrev alaZ : ℕ := 48
abbrev alaN : ℕ := 41   -- C₃H₇NO₂
abbrev valZ : ℕ := 64
abbrev valN : ℕ := 53   -- C₅H₁₁NO₂
abbrev leuZ : ℕ := 72
abbrev leuN : ℕ := 59   -- C₆H₁₃NO₂
abbrev ileZ : ℕ := 72
abbrev ileN : ℕ := 59   -- C₆H₁₃NO₂
abbrev proZ : ℕ := 62
abbrev proN : ℕ := 53   -- C₅H₉NO₂

-- Aromatic
abbrev pheZ : ℕ := 88
abbrev pheN : ℕ := 77   -- C₉H₁₁NO₂
abbrev trpZ : ℕ := 108
abbrev trpN : ℕ := 96   -- C₁₁H₁₂N₂O₂
abbrev tyrZ : ℕ := 96
abbrev tyrN : ℕ := 85   -- C₉H₁₁NO₃

-- Sulfur-containing
abbrev metZ : ℕ := 80
abbrev metN : ℕ := 69   -- C₅H₁₁NO₂S
abbrev cysZ : ℕ := 64
abbrev cysN : ℕ := 57   -- C₃H₇NO₂S

-- Polar, uncharged
abbrev serZ : ℕ := 56
abbrev serN : ℕ := 49   -- C₃H₇NO₃
abbrev thrZ : ℕ := 64
abbrev thrN : ℕ := 55   -- C₄H₉NO₃
abbrev asnZ : ℕ := 70
abbrev asnN : ℕ := 62   -- C₄H₈N₂O₃
abbrev glnZ : ℕ := 78
abbrev glnN : ℕ := 68   -- C₅H₁₀N₂O₃

-- Positively charged
abbrev lysZ : ℕ := 80
abbrev lysN : ℕ := 66   -- C₆H₁₄N₂O₂
abbrev argZ : ℕ := 94
abbrev argN : ℕ := 80   -- C₆H₁₄N₄O₂
abbrev hisZ : ℕ := 82
abbrev hisN : ℕ := 73   -- C₆H₉N₃O₂

-- Negatively charged
abbrev aspZ : ℕ := 70
abbrev aspN : ℕ := 63   -- C₄H₇NO₄
abbrev gluZ : ℕ := 78
abbrev gluN : ℕ := 69   -- C₅H₉NO₄

/-! ## Section 2: Z Derivation from Atomic Composition -/

theorem gly_Z_eq :
    2 * carbonZ + 5 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = glyZ := rfl
theorem ala_Z_eq :
    3 * carbonZ + 7 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = alaZ := rfl
theorem val_Z_eq :
    5 * carbonZ + 11 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = valZ := rfl
theorem leu_Z_eq :
    6 * carbonZ + 13 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = leuZ := rfl
theorem phe_Z_eq :
    9 * carbonZ + 11 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = pheZ := rfl
theorem trp_Z_eq :
    11 * carbonZ + 12 * hydrogenZ + 2 * nitrogenZ + 2 * oxygenZ = trpZ := rfl
theorem tyr_Z_eq :
    9 * carbonZ + 11 * hydrogenZ + 1 * nitrogenZ + 3 * oxygenZ = tyrZ := rfl
theorem met_Z_eq :
    5 * carbonZ + 11 * hydrogenZ + 1 * nitrogenZ
      + 2 * oxygenZ + 1 * sulfurZ = metZ := rfl
theorem cys_Z_eq :
    3 * carbonZ + 7 * hydrogenZ + 1 * nitrogenZ
      + 2 * oxygenZ + 1 * sulfurZ = cysZ := rfl
theorem ser_Z_eq :
    3 * carbonZ + 7 * hydrogenZ + 1 * nitrogenZ + 3 * oxygenZ = serZ := rfl
theorem asp_Z_eq :
    4 * carbonZ + 7 * hydrogenZ + 1 * nitrogenZ + 4 * oxygenZ = aspZ := rfl
theorem glu_Z_eq :
    5 * carbonZ + 9 * hydrogenZ + 1 * nitrogenZ + 4 * oxygenZ = gluZ := rfl

/-! ## Section 3: effectiveDegree Values -/

theorem gly_effDeg :
    (dimAtom glyZ glyN glyZ).effectiveDegree = 1246 := by decide
theorem ala_effDeg :
    (dimAtom alaZ alaN alaZ).effectiveDegree = 1480 := by decide
theorem val_effDeg :
    (dimAtom valZ valN valZ).effectiveDegree = 1948 := by decide
theorem leu_effDeg :
    (dimAtom leuZ leuN leuZ).effectiveDegree = 2182 := by decide
theorem ile_effDeg :
    (dimAtom ileZ ileN ileZ).effectiveDegree = 2182 := by decide
theorem pro_effDeg :
    (dimAtom proZ proN proZ).effectiveDegree = 1912 := by decide
theorem phe_effDeg :
    (dimAtom pheZ pheN pheZ).effectiveDegree = 2740 := by decide
theorem trp_effDeg :
    (dimAtom trpZ trpN trpZ).effectiveDegree = 3385 := by decide
theorem tyr_effDeg :
    (dimAtom tyrZ tyrN tyrZ).effectiveDegree = 3004 := by decide
theorem met_effDeg :
    (dimAtom metZ metN metZ).effectiveDegree = 2476 := by decide
theorem cys_effDeg :
    (dimAtom cysZ cysN cysZ).effectiveDegree = 2008 := by decide
theorem ser_effDeg :
    (dimAtom serZ serN serZ).effectiveDegree = 1744 := by decide
theorem thr_effDeg :
    (dimAtom thrZ thrN thrZ).effectiveDegree = 1978 := by decide
theorem asn_effDeg :
    (dimAtom asnZ asnN asnZ).effectiveDegree = 2191 := by decide
theorem gln_effDeg :
    (dimAtom glnZ glnN glnZ).effectiveDegree = 2425 := by decide
theorem lys_effDeg :
    (dimAtom lysZ lysN lysZ).effectiveDegree = 2431 := by decide
theorem arg_effDeg :
    (dimAtom argZ argN argZ).effectiveDegree = 2893 := by decide
theorem his_effDeg :
    (dimAtom hisZ hisN hisZ).effectiveDegree = 2572 := by decide
theorem asp_effDeg :
    (dimAtom aspZ aspN aspZ).effectiveDegree = 2206 := by decide
theorem glu_effDeg :
    (dimAtom gluZ gluN gluZ).effectiveDegree = 2440 := by decide

/-! ## Section 4: Structural Isomers

Leucine and isoleucine have identical molecular formula C₆H₁₃NO₂,
so they have the same (Z,N) and FDim.
-/

theorem leu_ile_isomers : leuZ = ileZ ∧ leuN = ileN := ⟨rfl, rfl⟩

theorem leu_ile_same_FDim :
    dimAtom leuZ leuN leuZ = dimAtom ileZ ileN ileZ := rfl

-- Glu and Gln have the same Z
theorem glu_gln_Z_same : gluZ = glnZ := rfl

/-! ## Section 5: Peptide Bond

Peptide bond: AA₁ + AA₂ → dipeptide + H₂O.
H₂O: Z=10, N=8, effDeg=301.
dipeptide effDeg = effDeg(AA1) + effDeg(AA2) - 301.
-/

theorem h2oEffDeg :
    (dimAtom 10 8 10).effectiveDegree = 301 := by decide

/-! ## Section 6: Count = nuclearMagic(2) -/

-- 20 standard amino acids = nuclearMagic(2) = 20
def allAAZ : List ℕ := [glyZ, alaZ, valZ, leuZ, ileZ, proZ, pheZ, trpZ,
  tyrZ, metZ, cysZ, serZ, thrZ, asnZ, glnZ, lysZ, argZ, hisZ, aspZ, gluZ]

theorem aa_count : allAAZ.length = Nuclear.nuclearMagic 2 := rfl

-- Z range: smallest Gly(40) to largest Trp(108)
theorem aa_Z_range : glyZ = 40 ∧ trpZ = 108 := ⟨rfl, rfl⟩

/-! ## Section 7: Sickle Cell Disease

β-globin position 6: Glu(E) → Val(V) mutation (GAG → GTG).
-/

theorem sickle_cell_Z_change : valZ + gluZ = 142 := rfl
theorem sickle_cell_Z_drop : gluZ - valZ = 14 := rfl

/-! ## Section 8: Disulfide Bond

2 Cys → Cys-S-S-Cys + H₂.
Disulfide bond removes 2 hydrogen atoms.
-/

theorem disulfide_Z_change : 2 * hydrogenZ = 2 := rfl

/-! ## Section 9: Summary -/

theorem amino_acid_classification :
    allAAZ.length = 20 ∧
    allAAZ.length = Nuclear.nuclearMagic 2 ∧
    leuZ = ileZ ∧
    gluZ = glnZ ∧
    gluZ - valZ = 14 ∧
    glyZ = 40 ∧ trpZ = 108 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.AminoAcid
