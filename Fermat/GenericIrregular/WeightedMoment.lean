import Mathlib.LinearAlgebra.Vandermonde

/-!
# Structure-preserving compression by weighted moments

For finitely many distinct levels `x i` and weights `c i`, the weighted
moment matrix is

`W = Vᵀ * diagonal c * V`,

where `V` is the Vandermonde evaluation matrix.  Its determinant is the
product of all weights times the square of the Vandermonde determinant.
Consequently, once the levels are distinct, one nonzero determinant is
equivalent to simultaneous nonvanishing of every weight.

The number of channels is an arbitrary parameter.  No case split on that
number occurs in this module.
-/

open scoped BigOperators

namespace Fermat.GenericIrregular.WeightedMoment

variable {F : Type*} [Field F] {N : ℕ}

/-- The Gram matrix of weighted evaluation at the levels `x`. -/
def weightedMoment (x c : Fin N → F) : Matrix (Fin N) (Fin N) F :=
  (Matrix.vandermonde x).transpose * Matrix.diagonal c *
    Matrix.vandermonde x

/-- The determinant separates into the product of the weights and the
square of the Vandermonde determinant. -/
theorem det_weightedMoment (x c : Fin N → F) :
    (weightedMoment x c).det =
      (∏ i, c i) * (Matrix.vandermonde x).det ^ 2 := by
  simp only [weightedMoment, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  ring

/-- Expanded determinant formula in terms of pairwise level differences. -/
theorem det_weightedMoment_eq_vandermondeProduct
    (x c : Fin N → F) :
    (weightedMoment x c).det =
      (∏ i, c i) *
        (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (x j - x i)) ^ 2 := by
  rw [det_weightedMoment, Matrix.det_vandermonde]

/-- For distinct levels, nondegeneracy of the single moment matrix is
equivalent to simultaneous nonvanishing of every channel weight. -/
theorem det_weightedMoment_ne_zero_iff
    {x c : Fin N → F} (hx : Function.Injective x) :
    (weightedMoment x c).det ≠ 0 ↔ ∀ i, c i ≠ 0 := by
  rw [det_weightedMoment]
  have hV : (Matrix.vandermonde x).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hx
  simp [hV, Finset.prod_ne_zero_iff]

/-- Axis-8 elimination: one nonzero weighted-moment determinant closes
every channel at once. -/
theorem weight_ne_zero_of_det_weightedMoment_ne_zero
    {x c : Fin N → F} (hx : Function.Injective x)
    (hdet : (weightedMoment x c).det ≠ 0) (i : Fin N) :
    c i ≠ 0 :=
  (det_weightedMoment_ne_zero_iff hx).mp hdet i

/-- Conversely, nonzero weights at distinct levels make the compressed
moment object nondegenerate. -/
theorem det_weightedMoment_ne_zero
    {x c : Fin N → F} (hx : Function.Injective x)
    (hc : ∀ i, c i ≠ 0) :
    (weightedMoment x c).det ≠ 0 :=
  (det_weightedMoment_ne_zero_iff hx).mpr hc

end Fermat.GenericIrregular.WeightedMoment
