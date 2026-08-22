import Fermat.Descent.Irregular.CyclicDifferenceMatrix

/-!
# Cyclic compression of the exponent-587 circular-unit matrix

This compatibility wrapper specializes the generic cyclic-difference-matrix
theory to the real residue cycle of order `293`. It preserves the original
public API used by the exponent-587 circular-unit certificate.
-/

namespace Fermat.FiveHundredEightySeven.CircularUnitCyclic

open scoped BigOperators Matrix
open Fermat.Irregular

/-- The cyclic group of order `(587 - 1) / 2 = 293`. -/
abbrev Cyc := CyclicDifferenceMatrix.Cyc 292

/-- Enumeration of the nonzero elements of `ZMod 293`. -/
abbrev coord (i : Fin 292) : Cyc :=
  CyclicDifferenceMatrix.coord 292 i

/-- The reduced difference matrix attached to a cyclic function. -/
abbrev differenceMatrix (h : Cyc → ZMod 587) :
    Matrix (Fin 292) (Fin 292) (ZMod 587) :=
  CyclicDifferenceMatrix.differenceMatrix 292 h

/-- The nonzero-coordinate enumeration is injective. -/
theorem coord_injective : Function.Injective coord := by
  simpa only [coord] using
    CyclicDifferenceMatrix.coord_injective 292

/-- Every enumerated coordinate is nonzero. -/
theorem coord_ne_zero (i : Fin 292) : coord i ≠ 0 := by
  simpa only [coord] using
    CyclicDifferenceMatrix.coord_ne_zero 292 i

/-- Split a cyclic sum into its zero term and its 292 nonzero terms. -/
theorem sum_cyc_eq_zero_add_coord (F : Cyc → ZMod 587) :
    (∑ u : Cyc, F u) = F 0 + ∑ i : Fin 292, F (coord i) := by
  simpa only [coord] using
    (CyclicDifferenceMatrix.sum_cyc_eq_zero_add_coord (n := 292) F)

/-- A sum over the nonzero coordinates can be extended to the whole cycle
when its zero summand vanishes. -/
theorem sum_coord_eq_sum_cyc_of_zero
    (F : Cyc → ZMod 587) (hF : F 0 = 0) :
    (∑ i : Fin 292, F (coord i)) = ∑ u : Cyc, F u := by
  simpa only [coord] using
    (CyclicDifferenceMatrix.sum_coord_eq_sum_cyc_of_zero
      (n := 292) F hF)

/-- Cyclic translation does not change a finite sum. -/
theorem sum_add_right (F : Cyc → ZMod 587) (a : Cyc) :
    (∑ u : Cyc, F (u + a)) = ∑ u : Cyc, F u :=
  CyclicDifferenceMatrix.sum_add_right F a

/-- Reindex a shifted product by the translation `v ↦ x + v`. -/
theorem sum_shifted_product (f g : Cyc → ZMod 587) (x z : Cyc) :
    (∑ v : Cyc, f (x + v) * g (v + z)) =
      ∑ u : Cyc, f u * g (u + (z - x)) :=
  CyclicDifferenceMatrix.sum_shifted_product f g x z

/-- A product of finite differences is a difference of correlations. -/
theorem sum_difference_products (f g : Cyc → ZMod 587) (x z : Cyc) :
    (∑ v : Cyc, (f (x + v) - f x) * (g (v + z) - g v)) =
      (∑ u : Cyc, f u * g (u + (z - x))) -
        ∑ u : Cyc, f u * g (u + (-x)) :=
  CyclicDifferenceMatrix.sum_difference_products f g x z

/-- A cyclic correlation inverse induces an inverse for the reduced
difference matrices. -/
theorem differenceMatrix_mul_eq_one
    (f g : Cyc → ZMod 587)
    (hcorr : ∀ d : Cyc,
      (∑ u : Cyc, f u * g (u + d)) = if d = 0 then 1 else 0) :
    differenceMatrix f * differenceMatrix g = 1 := by
  simpa only [differenceMatrix] using
    (CyclicDifferenceMatrix.differenceMatrix_mul_eq_one f g hcorr)

end Fermat.FiveHundredEightySeven.CircularUnitCyclic
