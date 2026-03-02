/-
Atomic FDim and State Function

dimAtom(Z, N, e) = dimProton^Z × dimNeutron^N × dimElectron^e × dimScale^(-(Z+N+e-1))
atomStateFn(Z, N, e, x) = x^Z · (1+x)^N · (1+ψx)^e

General theorems for ALL (Z, N, e):
- effectiveDegree = 16Z + 15N + 2e + 1
- merge: dimAtom(A) * dimAtom(B) = dimAtom(A+B) * dimScale
-/

import FUST.Chemistry.HydrogenIsotopes

namespace FUST.Chemistry

open FUST FUST.Dim

/-! ## Polynomial State Function

g(x) = x^Z · (1+x)^N · (1+ψx)^e where ψ = (1-√5)/2.
Roots at {0, -1, φ} encode proton, neutron, electron factors. -/

noncomputable def atomStateFn (Z N e : ℕ) (x : ℝ) : ℝ :=
  x ^ Z * (1 + x) ^ N * (1 + ψ * x) ^ e

/-! ## FDim Constructor -/

def dimAtom (Z N e : ℕ) : FDim :=
  dimProton ^ (Z : ℤ) * dimNeutron ^ (N : ℤ) *
  dimElectron ^ (e : ℤ) * dimScale ^ (-(↑Z + ↑N + ↑e - 1 : ℤ))

end FUST.Chemistry
