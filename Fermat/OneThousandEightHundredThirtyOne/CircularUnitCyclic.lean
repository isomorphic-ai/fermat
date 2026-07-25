import Fermat.Irregular.CyclicDifferenceMatrix

/-!
# Cyclic compression for the exponent-1831 circular-unit matrix

This is the exponent-specific interface to the generic reduced-difference
matrix construction. The real residue group has order
`(1831 - 1) / 2 = 915`; deleting its zero coordinate leaves the
`914 × 914` matrix used by the circular-unit certificate.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic

open scoped BigOperators Matrix

open Fermat.Irregular.CyclicDifferenceMatrix

/-- The real residue group has order `915`. -/
abbrev Cyc := Fermat.Irregular.CyclicDifferenceMatrix.Cyc 914

/-- Enumeration of the nonzero elements of `ZMod 915`. -/
def coord (i : Fin 914) : Cyc :=
  Fermat.Irregular.CyclicDifferenceMatrix.coord 914 i

/-- The reduced difference matrix attached to a cyclic function. -/
def differenceMatrix (h : Cyc → ZMod 1831) :
    Matrix (Fin 914) (Fin 914) (ZMod 1831) :=
  Fermat.Irregular.CyclicDifferenceMatrix.differenceMatrix 914 h

/-- A cyclic correlation inverse induces an inverse for the reduced
difference matrices. -/
theorem differenceMatrix_mul_eq_one
    (f g : Cyc → ZMod 1831)
    (hcorr : ∀ d : Cyc,
      (∑ u : Cyc, f u * g (u + d)) = if d = 0 then 1 else 0) :
    differenceMatrix f * differenceMatrix g = 1 :=
  Fermat.Irregular.CyclicDifferenceMatrix.differenceMatrix_mul_eq_one
    f g hcorr

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
