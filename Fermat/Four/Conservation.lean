/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# FLT(4), strictly through conservation

This is the public exponent-four conservation rung. `Spine` defines the
integer hypotenuse charge and exposes the stronger equation as an n=2
closed ledger. `Descent` uses that balance parametrization twice to construct
a strictly lower-charge primitive state. The shared conservation floor turns
that perpetual drain into impossible debt.

The bounded import roles are:

* `Fermat.Statement` supplies only the project statement `Fermat.HoldsAt`;
* `Fermat.Four.Conservation.Descent` supplies the provenance-clean stronger
  theorem and charged double descent.

No fixed-exponent FLT theorem is imported.
-/
import Fermat.Statement
import Fermat.Four.Conservation.Descent

namespace Fermat.Four

/-- Fermat's Last Theorem for exponent four, proved through the stronger
integer equation `x⁴ + y⁴ = z²`, the n=2 balance engine, strict hypotenuse
charge drain, and the shared well-founded conservation floor. -/
theorem holdsAt_four_conservation : Fermat.HoldsAt 4 := by
  change FermatLastTheoremFor 4
  rw [fermatLastTheoremFor_iff_int]
  intro x y z hx hy _ heq
  apply
    @Conservation.not_stronger_solution_conservation
      x y (z ^ 2) hx hy
  rw [heq]
  ring

end Fermat.Four
