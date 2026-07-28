/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# FLT(4): the conservation spine over the integers

The exponent-four drain is native to `ℤ`. Its stronger state equation is

`x⁴ + y⁴ = z²`,

and its charge is `|z|`. The drain engine is the exponent-two balance law:
the square legs `(x², y²)` and hypotenuse `z` form a right triangle.
Mathlib's Pythagorean parametrization realizes the coupling-free
decomposition

`(m² - n², 2mn, m² + n²)`,

while `Fermat.Two.PythagorasConservation` supplies its conservation
interpretation: an empty coupling channel makes the squared-charge ledger
close. Thus the n=2 balance rung is used as the transformation that powers
the n=4 drain rung.

The bounded import roles are:

* `Fermat.Conservation.Floor` supplies the shared well-founded floor;
* `Fermat.Two.PythagorasConservation` supplies the n=2 balance
  interpretation;
* `NumberTheory.PythagoreanTriples` supplies only the integer
  parametrization of coupling-free right triangles;
* `Tactic.LinearCombination` verifies polynomial ledger equalities.

No fixed-exponent FLT theorem is imported.
-/
import Fermat.Conservation.Floor
import Fermat.Two.PythagorasConservation
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.LinearCombination

namespace Fermat.Four.Conservation

/-- A nontrivial solution of Fermat's stronger exponent-four equation
`x⁴ + y⁴ = z²`. -/
def StrongerSolution (x y z : ℤ) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ x ^ 4 + y ^ 4 = z ^ 2

/-- The integer drain charge of the stronger equation: the absolute
hypotenuse `|z|`. -/
def charge (z : ℤ) : ℕ :=
  z.natAbs

/-- A primitive stronger solution: its two nonzero legs are coprime.
Orientation and hypotenuse sign are deliberately absent; the charged
transformer normalizes them internally without changing charge. -/
structure PrimitiveSolution where
  x : ℤ
  y : ℤ
  z : ℤ
  solution : StrongerSolution x y z
  coprime : IsCoprime x y

/-- The charge carried by a normalized descent state. -/
def PrimitiveSolution.stateCharge (S : PrimitiveSolution) : ℕ :=
  charge S.z

/-- **Balance powers drain.** The stronger exponent-four equation is exactly
the closed n=2 ledger on the square legs `(x², y²)`. This is the formal seam
where the coupling-free Pythagorean decomposition from the balance rung
becomes the transformation engine for the drain rung. -/
theorem pythagorean_balance_engine {x y z : ℤ}
    (h : StrongerSolution x y z) :
    PythagoreanTriple (x ^ 2) (y ^ 2) z := by
  delta PythagoreanTriple
  linear_combination h.2.2

/-- A nontrivial stronger solution has nonzero hypotenuse, so its natural
charge lies strictly above the conservation floor. -/
theorem StrongerSolution.charge_pos {x y z : ℤ}
    (h : StrongerSolution x y z) :
    0 < charge z := by
  apply Int.natAbs_pos.mpr
  apply ne_zero_pow two_ne_zero
  apply ne_of_gt
  rw [← h.2.2,
    (by ring : x ^ 4 + y ^ 4 = (x ^ 2) ^ 2 + (y ^ 2) ^ 2)]
  exact
    add_pos
      (sq_pos_of_ne_zero (pow_ne_zero 2 h.1))
      (sq_pos_of_ne_zero (pow_ne_zero 2 h.2.1))

/-- Every primitive descent state carries positive charge. -/
theorem PrimitiveSolution.stateCharge_pos (S : PrimitiveSolution) :
    0 < S.stateCharge :=
  S.solution.charge_pos

end Fermat.Four.Conservation
