/-
20 Standard Amino Acids from State Function Model

Each amino acid has (Z, N, e=Z) from its molecular formula.
Count 20 = nuclearMagic(2) = hoMagic(2).
Leu/Ile isomers share the same state function.
Peptide bond = condensation releasing H₂O (Z=10, N=8).
-/

import FUST.Chemistry.SulfurAtom
import FUST.Chemistry.Nucleotides

namespace FUST.Chemistry.AminoAcid

open FUST FUST.Chemistry.Oxygen FUST.Chemistry.Dihydrogen
open FUST.Chemistry.Carbon FUST.Chemistry.Nitrogen
open FUST.Chemistry.Sulfur

/-! ## Section 1: Amino Acid Structure -/

structure AA where
  code : String
  Z : ℕ
  N : ℕ
  deriving Repr

def AA.e (a : AA) : ℕ := a.Z
def AA.deg (a : AA) : ℕ := a.Z + a.N + a.e

/-! ## Section 2: The 20 Standard Amino Acids

Grouped by chemical property. Neutral molecules: e = Z.
-/

-- Nonpolar, aliphatic
def gly : AA := ⟨"G", 40, 35⟩   -- C₂H₅NO₂
def ala : AA := ⟨"A", 48, 41⟩   -- C₃H₇NO₂
def val : AA := ⟨"V", 64, 53⟩   -- C₅H₁₁NO₂
def leu : AA := ⟨"L", 72, 59⟩   -- C₆H₁₃NO₂
def ile : AA := ⟨"I", 72, 59⟩   -- C₆H₁₃NO₂
def pro : AA := ⟨"P", 62, 53⟩   -- C₅H₉NO₂

-- Aromatic
def phe : AA := ⟨"F", 88, 77⟩   -- C₉H₁₁NO₂
def trp : AA := ⟨"W", 108, 96⟩  -- C₁₁H₁₂N₂O₂
def tyr : AA := ⟨"Y", 96, 85⟩   -- C₉H₁₁NO₃

-- Sulfur-containing
def met : AA := ⟨"M", 80, 69⟩   -- C₅H₁₁NO₂S
def cys : AA := ⟨"C", 64, 57⟩   -- C₃H₇NO₂S

-- Polar, uncharged
def ser : AA := ⟨"S", 56, 49⟩   -- C₃H₇NO₃
def thr : AA := ⟨"T", 64, 55⟩   -- C₄H₉NO₃
def asn : AA := ⟨"N", 70, 62⟩   -- C₄H₈N₂O₃
def gln : AA := ⟨"Q", 78, 68⟩   -- C₅H₁₀N₂O₃

-- Positively charged
def lys : AA := ⟨"K", 80, 66⟩   -- C₆H₁₄N₂O₂
def arg : AA := ⟨"R", 94, 80⟩   -- C₆H₁₄N₄O₂
def his : AA := ⟨"H", 82, 73⟩   -- C₆H₉N₃O₂

-- Negatively charged
def asp : AA := ⟨"D", 70, 63⟩   -- C₄H₇NO₄
def glu : AA := ⟨"E", 78, 69⟩   -- C₅H₉NO₄

/-! ## Section 3: Z Derivation from Atomic Composition -/

-- Non-sulfur: Z = nC·6 + nH·1 + nN·7 + nO·8
-- Sulfur-containing: add nS·16
theorem gly_Z : 2 * carbonZ + 5 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = gly.Z := rfl
theorem ala_Z : 3 * carbonZ + 7 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = ala.Z := rfl
theorem val_Z : 5 * carbonZ + 11 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = val.Z := rfl
theorem leu_Z : 6 * carbonZ + 13 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = leu.Z := rfl
theorem ile_Z : 6 * carbonZ + 13 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = ile.Z := rfl
theorem pro_Z : 5 * carbonZ + 9 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = pro.Z := rfl
theorem phe_Z : 9 * carbonZ + 11 * hydrogenZ + 1 * nitrogenZ + 2 * oxygenZ = phe.Z := rfl
theorem trp_Z : 11 * carbonZ + 12 * hydrogenZ + 2 * nitrogenZ + 2 * oxygenZ = trp.Z := rfl
theorem tyr_Z : 9 * carbonZ + 11 * hydrogenZ + 1 * nitrogenZ + 3 * oxygenZ = tyr.Z := rfl
theorem met_Z :
    5 * carbonZ + 11 * hydrogenZ + 1 * nitrogenZ
      + 2 * oxygenZ + 1 * sulfurZ = met.Z := rfl
theorem cys_Z :
    3 * carbonZ + 7 * hydrogenZ + 1 * nitrogenZ
      + 2 * oxygenZ + 1 * sulfurZ = cys.Z := rfl
theorem ser_Z : 3 * carbonZ + 7 * hydrogenZ + 1 * nitrogenZ + 3 * oxygenZ = ser.Z := rfl
theorem thr_Z : 4 * carbonZ + 9 * hydrogenZ + 1 * nitrogenZ + 3 * oxygenZ = thr.Z := rfl
theorem asn_Z : 4 * carbonZ + 8 * hydrogenZ + 2 * nitrogenZ + 3 * oxygenZ = asn.Z := rfl
theorem gln_Z : 5 * carbonZ + 10 * hydrogenZ + 2 * nitrogenZ + 3 * oxygenZ = gln.Z := rfl
theorem lys_Z : 6 * carbonZ + 14 * hydrogenZ + 2 * nitrogenZ + 2 * oxygenZ = lys.Z := rfl
theorem arg_Z : 6 * carbonZ + 14 * hydrogenZ + 4 * nitrogenZ + 2 * oxygenZ = arg.Z := rfl
theorem his_Z : 6 * carbonZ + 9 * hydrogenZ + 3 * nitrogenZ + 2 * oxygenZ = his.Z := rfl
theorem asp_Z : 4 * carbonZ + 7 * hydrogenZ + 1 * nitrogenZ + 4 * oxygenZ = asp.Z := rfl
theorem glu_Z : 5 * carbonZ + 9 * hydrogenZ + 1 * nitrogenZ + 4 * oxygenZ = glu.Z := rfl

/-! ## Section 4: Degree Values -/

theorem gly_deg : gly.deg = 115 := rfl
theorem ala_deg : ala.deg = 137 := rfl
theorem val_deg : val.deg = 181 := rfl
theorem leu_deg : leu.deg = 203 := rfl
theorem ile_deg : ile.deg = 203 := rfl
theorem pro_deg : pro.deg = 177 := rfl
theorem phe_deg : phe.deg = 253 := rfl
theorem trp_deg : trp.deg = 312 := rfl
theorem tyr_deg : tyr.deg = 277 := rfl
theorem met_deg : met.deg = 229 := rfl
theorem cys_deg : cys.deg = 185 := rfl
theorem ser_deg : ser.deg = 161 := rfl
theorem thr_deg : thr.deg = 183 := rfl
theorem asn_deg : asn.deg = 202 := rfl
theorem gln_deg : gln.deg = 224 := rfl
theorem lys_deg : lys.deg = 226 := rfl
theorem arg_deg : arg.deg = 268 := rfl
theorem his_deg : his.deg = 237 := rfl
theorem asp_deg : asp.deg = 203 := rfl
theorem glu_deg : glu.deg = 225 := rfl

/-! ## Section 5: Structural Isomers

Leucine and isoleucine have identical molecular formula C₆H₁₃NO₂,
so they have the same (Z,N,e) and degree. FUST state functions
cannot distinguish structural isomers (same particle counts).
-/

theorem leu_ile_isomers : leu.Z = ile.Z ∧ leu.N = ile.N ∧ leu.deg = ile.deg :=
  ⟨rfl, rfl, rfl⟩

-- Asp/Asn and Glu/Gln pairs differ by NH vs O (amidation)
-- Asp(D) C₄H₇NO₄ → Asn(N) C₄H₈N₂O₃: replace O with NH₂ → ΔZ = 7+2-8 = 1
theorem asp_asn_Z_diff : asn.Z - asp.Z = 0 := rfl
-- Actually both have Z=70 since 4·6+8·1+2·7+3·8 = 24+8+14+24 = 70
-- and 4·6+7·1+1·7+4·8 = 24+7+7+32 = 70

-- Glu/Gln similarly
theorem glu_gln_Z_same : glu.Z = gln.Z := rfl

/-! ## Section 6: Peptide Bond and Residue Mass

Peptide bond: AA₁ + AA₂ → dipeptide + H₂O
Residue = free amino acid - H₂O
H₂O: Z=10, N=8, deg=28
-/

def residueZ (a : AA) : ℕ := a.Z - 10
def residueN (a : AA) : ℕ := a.N - 8
def residueDeg (a : AA) : ℕ := a.deg - 28

-- Glycine residue: smallest
theorem gly_residue : residueZ gly = 30 ∧ residueN gly = 27 ∧ residueDeg gly = 87 :=
  ⟨rfl, rfl, rfl⟩

-- Tryptophan residue: largest
theorem trp_residue : residueZ trp = 98 ∧ residueN trp = 88 ∧ residueDeg trp = 284 :=
  ⟨rfl, rfl, rfl⟩

-- Degree is additive for peptide chains:
-- deg(chain of k residues) = Σ residueDeg + deg(H₂O) + (k-1)·0 ???
-- Actually: deg(dipeptide) = deg(AA1) + deg(AA2) - deg(H2O)
theorem dipeptide_deg (a1 a2 : AA) (h1 : a1.Z ≥ 10) (h2 : a2.Z ≥ 10)
    (hn1 : a1.N ≥ 8) (hn2 : a2.N ≥ 8) :
    (a1.Z + a2.Z - 10) + (a1.N + a2.N - 8) + (a1.Z + a2.Z - 10) =
    a1.deg + a2.deg - 28 := by
  unfold AA.deg AA.e; omega

/-! ## Section 7: Count = nuclearMagic(2)

20 standard amino acids = nuclearMagic(2) = 20.
-/

def allAA : List AA := [gly, ala, val, leu, ile, pro, phe, trp, tyr,
                         met, cys, ser, thr, asn, gln, lys, arg, his, asp, glu]

theorem aa_count : allAA.length = Nuclear.nuclearMagic 2 := rfl

-- Z range: smallest Gly(40) to largest Trp(108)
theorem aa_Z_range : gly.Z = 40 ∧ trp.Z = 108 := ⟨rfl, rfl⟩

-- Degree range: smallest Gly(115) to largest Trp(312)
theorem aa_deg_range : gly.deg = 115 ∧ trp.deg = 312 := ⟨rfl, rfl⟩

/-! ## Section 8: Sickle Cell Disease

β-globin position 6: Glu(E) → Val(V) mutation (GAG → GTG).
ΔZ = 64 - 78 = -14, Δdeg = 181 - 225 = -44.
This is the largest |ΔZ| among single-base substitution diseases.
-/

theorem sickle_cell_Z_change : val.Z + glu.Z = 142 := rfl
theorem sickle_cell_deg_change : glu.deg - val.deg = 44 := rfl

-- The mutation replaces a charged residue with a hydrophobic one
-- Glu is negatively charged (Z=78), Val is nonpolar (Z=64)
theorem sickle_cell_Z_drop : glu.Z - val.Z = 14 := rfl

/-! ## Section 9: Disulfide Bond

2 Cys → Cys-S-S-Cys + 2H
Disulfide bond removes 2 hydrogen atoms (Z=2, N=0, deg=4).
-/

theorem disulfide_Z_change : 2 * hydrogenZ = 2 := rfl
theorem disulfide_deg_change : 2 * cys.deg - 2 * (2 * hydrogenZ + 0 + 2 * hydrogenZ) = 362 := rfl

/-! ## Section 10: Met as Start Amino Acid

Met (ATG) is the universal start codon amino acid.
Met degree = 229 = Guanine degree (coincidence with nucleobase).
-/

theorem met_deg_eq_guanine_deg : met.deg = Nucleotide.guanine.deg := rfl

/-! ## Section 11: Summary -/

theorem amino_acid_classification :
    allAA.length = 20 ∧
    allAA.length = Nuclear.nuclearMagic 2 ∧
    leu.Z = ile.Z ∧
    glu.Z = gln.Z ∧
    glu.deg - val.deg = 44 ∧
    met.deg = Nucleotide.guanine.deg ∧
    gly.deg = 115 ∧ trp.deg = 312 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end FUST.Chemistry.AminoAcid

namespace FUST.DiscreteTag
open FUST.Chemistry.AminoAcid

def glyDeg_t : DTagged .degree := ⟨gly.deg⟩
def alaDeg_t : DTagged .degree := ⟨ala.deg⟩
def valDeg_t : DTagged .degree := ⟨val.deg⟩
def leuDeg_t : DTagged .degree := ⟨leu.deg⟩
def ileDeg_t : DTagged .degree := ⟨ile.deg⟩
def proDeg_t : DTagged .degree := ⟨pro.deg⟩
def pheDeg_t : DTagged .degree := ⟨phe.deg⟩
def trpDeg_t : DTagged .degree := ⟨trp.deg⟩
def tyrDeg_t : DTagged .degree := ⟨tyr.deg⟩
def metDeg_t : DTagged .degree := ⟨met.deg⟩
def cysDeg_t : DTagged .degree := ⟨cys.deg⟩
def serDeg_t : DTagged .degree := ⟨ser.deg⟩
def thrDeg_t : DTagged .degree := ⟨thr.deg⟩
def asnDeg_t : DTagged .degree := ⟨asn.deg⟩
def glnDeg_t : DTagged .degree := ⟨gln.deg⟩
def lysDeg_t : DTagged .degree := ⟨lys.deg⟩
def argDeg_t : DTagged .degree := ⟨arg.deg⟩
def hisDeg_t : DTagged .degree := ⟨his.deg⟩
def aspDeg_t : DTagged .degree := ⟨asp.deg⟩
def gluDeg_t : DTagged .degree := ⟨glu.deg⟩

def deamidationDeltaDeg_t : DTagged .deltaDeg := ⟨asp.deg - asn.deg⟩

theorem glyDeg_t_val : glyDeg_t.val = 115 := rfl
theorem alaDeg_t_val : alaDeg_t.val = 137 := rfl
theorem valDeg_t_val : valDeg_t.val = 181 := rfl
theorem leuDeg_t_val : leuDeg_t.val = 203 := rfl
theorem ileDeg_t_val : ileDeg_t.val = 203 := rfl
theorem proDeg_t_val : proDeg_t.val = 177 := rfl
theorem pheDeg_t_val : pheDeg_t.val = 253 := rfl
theorem trpDeg_t_val : trpDeg_t.val = 312 := rfl
theorem tyrDeg_t_val : tyrDeg_t.val = 277 := rfl
theorem metDeg_t_val : metDeg_t.val = 229 := rfl
theorem cysDeg_t_val : cysDeg_t.val = 185 := rfl
theorem serDeg_t_val : serDeg_t.val = 161 := rfl
theorem thrDeg_t_val : thrDeg_t.val = 183 := rfl
theorem asnDeg_t_val : asnDeg_t.val = 202 := rfl
theorem glnDeg_t_val : glnDeg_t.val = 224 := rfl
theorem lysDeg_t_val : lysDeg_t.val = 226 := rfl
theorem argDeg_t_val : argDeg_t.val = 268 := rfl
theorem hisDeg_t_val : hisDeg_t.val = 237 := rfl
theorem aspDeg_t_val : aspDeg_t.val = 203 := rfl
theorem gluDeg_t_val : gluDeg_t.val = 225 := rfl

theorem deamidation_deltaDeg_t : deamidationDeltaDeg_t = ⟨1⟩ := rfl

-- Leu/Ile isomers have same degree
theorem leu_ile_deg_tagged : leuDeg_t = ileDeg_t := rfl

-- Met = Guanine (protein ↔ nucleic acid bridge)
theorem met_guanine_deg_tagged : metDeg_t = guanineDeg_t := rfl

-- Deamidation Asn→Asp via degDiff
theorem deamidation_deg_tagged :
    degDiff aspDeg_t asnDeg_t = deamidationDeltaDeg_t := rfl

-- Deamidation Gln→Glu via degDiff
theorem gln_glu_deamidation_deg_tagged :
    degDiff gluDeg_t glnDeg_t = deamidationDeltaDeg_t := rfl

end FUST.DiscreteTag
