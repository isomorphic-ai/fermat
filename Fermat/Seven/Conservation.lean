/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Fermat's Last Theorem at seven by conservation

This is the public boundary of the strict exponent-seven conservation cone.
It combines the local class-number-one certificate, the full rank-two unit
gauge and septic norm ledger, and the credited reconstruction of Lebesgue's
corrected descent.  No declaration from the repository's earlier
`Fermat.Seven.Lebesgue` implementation is imported.
-/
import Fermat.Seven.Conservation.ClassNumber
import Fermat.Seven.Conservation.Reconstruction.Lebesgue.TheoremTwo
import Fermat.Seven.Conservation.Spine

namespace Fermat.Seven

/-- Fermat's Last Theorem for exponent seven, proved through the septic
norm ledger, the full rank-two cyclotomic unit gauge, the norm-seven
ramified quantum, and the shared strict conservation floor. -/
theorem holdsAt_seven_conservation : Fermat.HoldsAt 7 :=
  Conservation.Reconstruction.Lebesgue.holdsAt_seven_lebesgue

end Fermat.Seven
