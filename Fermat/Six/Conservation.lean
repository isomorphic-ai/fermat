/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# FLT(6), directly through conservation

This is the public exponent-six conservation rung.  A primitive
sixth-power solution first closes both native ledgers: the sixth-cyclotomic
norm factorization and the Pythagorean balance on cube coordinates.  Its
modulo-nine allocation then seeds the ramified charged state directly.
Strict loss of native norm charge closes through the shared conservation
floor.

The bounded import roles are:

* `Fermat.Statement.Basic` supplies only the proposition
  `Fermat.HoldsAt`, with no repository exponent-transport theorem;
* `Fermat.Six.Conservation.Descent` supplies the native primitive entry,
  direct charged seed, strict transformer, and floor closure.

No fixed exponent-three statement, repository exponent-three module,
divisibility fold, or Ladder transport enters this cone.
-/
import Fermat.Statement.Basic
import Fermat.Six.Conservation.Descent

namespace Fermat.Six

/-- Fermat's Last Theorem for exponent six, proved by seeding the ramified
sixth-cyclotomic charge directly from primitive degree-six data and draining
that charge through the shared conservation floor. -/
theorem holdsAt_six_conservation : Fermat.HoldsAt 6 := by
  change FermatLastTheoremFor 6
  rw [fermatLastTheoremFor_iff_int]
  refine
    fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
      (fun a b c ha hb hc hprimitive equation ↦ ?_)
  let initial : Conservation.PrimitiveSolution :=
    { a := a
      b := b
      c := c
      a_ne_zero := ha
      b_ne_zero := hb
      c_ne_zero := hc
      equation := equation
      primitive := hprimitive }
  exact
    Conservation.PrimitiveSolution.impossible_conservation initial

end Fermat.Six
