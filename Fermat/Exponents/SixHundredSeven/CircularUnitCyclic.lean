import Fermat.Descent.Irregular.CyclicDifferenceMatrix

/-!
# Cyclic compression for the exponent-607 circular-unit matrix

This is the exponent-specific interface to the generic reduced-difference
matrix construction. The real residue group has order
`(607 - 1) / 2 = 303`; deleting its zero coordinate leaves the
`302 × 302` matrix used by the circular-unit certificate.
-/

namespace Fermat.SixHundredSeven.CircularUnitCyclic

open scoped BigOperators Matrix

open Fermat.Irregular.CyclicDifferenceMatrix

/-- The real residue group has order `303`. -/
abbrev Cyc := Fermat.Irregular.CyclicDifferenceMatrix.Cyc 302

/-- Enumeration of the nonzero elements of `ZMod 303`. -/
def coord (i : Fin 302) : Cyc :=
  Fermat.Irregular.CyclicDifferenceMatrix.coord 302 i

/-- The reduced difference matrix attached to a cyclic function. -/
def differenceMatrix (h : Cyc → ZMod 607) :
    Matrix (Fin 302) (Fin 302) (ZMod 607) :=
  Fermat.Irregular.CyclicDifferenceMatrix.differenceMatrix 302 h

/-- A cyclic correlation inverse induces an inverse for the reduced
difference matrices. -/
theorem differenceMatrix_mul_eq_one
    (f g : Cyc → ZMod 607)
    (hcorr : ∀ d : Cyc,
      (∑ u : Cyc, f u * g (u + d)) = if d = 0 then 1 else 0) :
    differenceMatrix f * differenceMatrix g = 1 :=
  Fermat.Irregular.CyclicDifferenceMatrix.differenceMatrix_mul_eq_one
    f g hcorr

end Fermat.SixHundredSeven.CircularUnitCyclic
