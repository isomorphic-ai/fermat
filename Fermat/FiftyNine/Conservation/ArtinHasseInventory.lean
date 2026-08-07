/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conductor-59 Artin--Hasse generator inventory

This file records the Stage-3 formula-budget decision.  It contains no wild
symbol and asserts no Artin--Hasse special value.

Three generator kinds have explicit cyclotomic provenance in the selected
cone:

* `StateFactorPair.zetaUnit` is the chosen root of unity;
* `StateFactorPair.fixedDenominator` is `zeta - 1`, hence an associate of
  `1 - zeta`; and
* `Credit.generatedUnit` is generated from geometric cyclotomic units.

The two values actually supplied to the wild pairing do not presently carry
such a decomposition.  The statewise value is obtained through
`CommonActionStage.allocatedSelmerObstruction`, whose underlying
`ExactFilteredPair.liftClassPair` is a chosen preimage of the class
projection.  The detector value is the unrestricted
`TateBridge.TransverseDetector.detector`.  In the seated realization both
are Kummer classes; `SelmerEigenspace.quotientRepresentative` chooses a
representative and proves only the Selmer valuation receipt, not membership
in the cyclotomic-unit subgroup.

Accordingly, `needsVostokov` below means that the currently available
decomposition evidence does not reduce every actual input to the two special
Artin--Hasse families.  It is deliberately not a theorem that a future
explicit representative cannot lie in that subgroup: supplying the two
missing decompositions would justify revisiting the budget.
-/

namespace Fermat.FiftyNine.Conservation.ArtinHasseInventory

/-- Provenance classes relevant to the conductor-59 wild-symbol budget. -/
inductive WildClassKind
  | rootOfUnity
  | oneSubRoot
  | cyclotomicUnit
  | statewiseSelmerLift
  | transverseDetectorComponent
  deriving DecidableEq, Repr

/-- Whether the selected cone currently exposes the advertised
Artin--Hasse-generator decomposition for this kind of input. -/
def hasArtinHasseDecomposition : WildClassKind → Bool
  | .rootOfUnity => true
  | .oneSubRoot => true
  | .cyclotomicUnit => true
  | .statewiseSelmerLift => false
  | .transverseDetectorComponent => false

/-- The two possible budgets named by the Stage-3 fork check. -/
inductive WildFormulaBudget
  | ahSuffices
  | needsVostokov
  deriving DecidableEq, Repr

/-- Special formulas suffice exactly when every inventoried input comes with
the corresponding generator decomposition in the current cone. -/
def formulaBudget (inventory : List WildClassKind) : WildFormulaBudget :=
  if inventory.all hasArtinHasseDecomposition then
    .ahSuffices
  else
    .needsVostokov

/-- The complete selected inventory: the three advertised generators and
the two opaque values actually entering the wild pairing. -/
def campaignInventory : List WildClassKind :=
  [.rootOfUnity, .oneSubRoot, .cyclotomicUnit,
    .statewiseSelmerLift, .transverseDetectorComponent]

/-- **Stage-3 fork verdict: `NEEDS-VOSTOKOV`.**  The verdict is a coverage
audit of available decompositions, not an invented non-membership theorem. -/
theorem campaign_formulaBudget_eq_needsVostokov :
    formulaBudget campaignInventory = .needsVostokov := by
  rfl

end Fermat.FiftyNine.Conservation.ArtinHasseInventory
