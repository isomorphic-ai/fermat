import Fermat.Descent.Irregular.CyclicDifferenceMatrix

/-!
# Cyclic compression for the exponent-1381 circular-unit matrix

This is the exponent-specific interface to the generic reduced-difference
matrix construction. The real residue group has order
`(1381 - 1) / 2 = 690`; deleting its zero coordinate leaves the
`689 × 689` matrix used by the circular-unit certificate.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic

open scoped BigOperators Matrix

open Fermat.Irregular.CyclicDifferenceMatrix

/-- The real residue group has order `690`. -/
abbrev Cyc := Fermat.Irregular.CyclicDifferenceMatrix.Cyc 689

/-- Enumeration of the nonzero elements of `ZMod 690`. -/
def coord (i : Fin 689) : Cyc :=
  Fermat.Irregular.CyclicDifferenceMatrix.coord 689 i

/-- The reduced difference matrix attached to a cyclic function. -/
def differenceMatrix (h : Cyc → ZMod 1381) :
    Matrix (Fin 689) (Fin 689) (ZMod 1381) :=
  Fermat.Irregular.CyclicDifferenceMatrix.differenceMatrix 689 h

/-- A cyclic correlation inverse induces an inverse for the reduced
difference matrices. -/
theorem differenceMatrix_mul_eq_one
    (f g : Cyc → ZMod 1381)
    (hcorr : ∀ d : Cyc,
      (∑ u : Cyc, f u * g (u + d)) = if d = 0 then 1 else 0) :
    differenceMatrix f * differenceMatrix g = 1 :=
  Fermat.Irregular.CyclicDifferenceMatrix.differenceMatrix_mul_eq_one
    f g hcorr

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
