/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# FLT(6): the native conservation spine

The sixth cyclotomic field is the Eisenstein field, but its native generator
has minimal polynomial `X² - X + 1`.  Accordingly, the degree-six norm ledger
uses the positive form

`N(x + yζ₆) = x² + xy + y²`

and the Fermat equation factors as

`a⁶ + b⁶ = (a² + b²) N(a² - b²ζ₆)`.

The same equation is also a closed exponent-two balance ledger on the cube
legs `(a³, b³)` and cube hypotenuse `c³`.  Both views are stated here before
the descent chooses its arithmetic coordinates.

The bounded import roles are:

* `Fermat.Conservation.Floor` supplies the shared well-founded floor;
* `QuadraticAlgebra.Basic` supplies the coordinate ring and norm;
* `PythagoreanTriples` supplies only the right-triangle predicate;
* `NormNum` and `Ring` verify explicit integer polynomial identities.

No fixed-exponent theorem, exponent transport, Ladder module, or
`Fermat.Three` module is imported.
-/
import Fermat.Conservation.Floor
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Fermat.Six.Conservation

/-- The integral sixth-cyclotomic order
`ℤ[ζ₆] = ℤ[X] / (X² - X + 1)`. -/
abbrev SixthCyclotomicInt := QuadraticAlgebra ℤ (-1) 1

/-- The distinguished primitive sixth root, represented by `X`. -/
def zetaSix : SixthCyclotomicInt := QuadraticAlgebra.omega

/-- The sixth-cyclotomic integer `x + yζ₆`. -/
def ofCoeffs (x y : ℤ) : SixthCyclotomicInt := ⟨x, y⟩

/-- The signed algebraic norm charge on `ℤ[ζ₆]`. -/
def charge (z : SixthCyclotomicInt) : ℤ :=
  QuadraticAlgebra.norm z

/-- In native sixth-root coordinates,
`N(x + yζ₆) = x² + xy + y²`. -/
theorem charge_formula (x y : ℤ) :
    charge (ofCoeffs x y) = x ^ 2 + x * y + y ^ 2 := by
  simp [charge, ofCoeffs, QuadraticAlgebra.norm_def]
  ring

/-- **Multiplicative conservation.** Sixth-cyclotomic multiplication
preserves the norm ledger. -/
theorem charge_mul (u v : SixthCyclotomicInt) :
    charge (u * v) = charge u * charge v := by
  exact map_mul QuadraticAlgebra.norm u v

/-- The native norm factor in the degree-six ledger. -/
def cofactorElement (a b : ℤ) : SixthCyclotomicInt :=
  ofCoeffs (a ^ 2) (-(b ^ 2))

/-- The native norm factor is the quartic cyclotomic cofactor. -/
theorem cofactor_charge (a b : ℤ) :
    charge (cofactorElement a b) =
      a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4 := by
  rw [cofactorElement, charge_formula]
  ring

/-- **The degree-six ledger.** The sum channel and the native
sixth-cyclotomic charge account for the whole sixth-power equation. -/
theorem sixth_ledger (a b : ℤ) :
    a ^ 6 + b ^ 6 =
      (a ^ 2 + b ^ 2) * charge (cofactorElement a b) := by
  rw [cofactor_charge]
  ring

/-- **Balance at the top.** A sixth-power equation is a coupling-free
Pythagorean ledger whose two legs and hypotenuse are cubes. -/
theorem pythagorean_cube_balance {a b c : ℤ}
    (h : a ^ 6 + b ^ 6 = c ^ 6) :
    PythagoreanTriple (a ^ 3) (b ^ 3) (c ^ 3) := by
  simpa only [PythagoreanTriple, ← pow_two, ← pow_mul,
    Nat.reduceMul] using h

/-- The ramified drain quantum in sixth-root coordinates. -/
def drainUnit : SixthCyclotomicInt :=
  1 + zetaSix

/-- The ramified quantum has norm charge three. -/
theorem drainUnit_charge :
    charge drainUnit = 3 := by
  have hunit : drainUnit = ofCoeffs 1 1 := rfl
  rw [hunit, charge_formula]
  norm_num

/-- Conservation iterated through powers. -/
theorem charge_pow (u : SixthCyclotomicInt) (n : ℕ) :
    charge (u ^ n) = charge u ^ n := by
  exact map_pow QuadraticAlgebra.norm u n

/-- The positive native norm charge stored in `n` ramified quanta. -/
def drainCharge (n : ℕ) : ℕ :=
  (charge (drainUnit ^ n)).natAbs

/-- `n` ramified quanta carry native degree-six charge `3ⁿ`. -/
theorem drainCharge_eq (n : ℕ) :
    drainCharge n = 3 ^ n := by
  simp [drainCharge, charge_pow, drainUnit_charge]

/-- Removing ramified multiplicity strictly lowers the native charge. -/
theorem drainCharge_lt {m n : ℕ} (h : m < n) :
    drainCharge m < drainCharge n := by
  rw [drainCharge_eq, drainCharge_eq]
  exact Nat.pow_lt_pow_right (by norm_num) h

end Fermat.Six.Conservation
