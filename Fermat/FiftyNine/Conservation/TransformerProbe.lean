/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Probe: the post-repayment stock/credit seam

This scratch file asks only what the current clean conservation cone can
compose after repayment.  A primitive second-case exponent-59 solution is
given its literal hypotenuse charge.  A genuine transformer must return
another primitive second-case solution with strictly smaller charge.

The generic floor consumes exactly that transformer.  The selected fold now
derives Vandiver's (7d) from conjugation acting as ledger transpose (the
literal relative-norm product is proved generically) and principalizes the
allocated ledger once the state also supplies (7a).
The guarded examples record the remaining producers: stock torsion does not
itself derive (7a), selected repayment is an equality in the real-unit group
rather than a successor solution, and the strict drain compares ramified
norm charges rather than the hypotenuse charges of two integral solutions.
-/
import Fermat.Conservation.KummerDrain
import Fermat.FiftyNine.Conservation.Fold
import Fermat.FiftyNine.Conservation.GaugeQuotient

open scoped NumberField

namespace Fermat.FiftyNine.Conservation.TransformerProbe

noncomputable section

/-- A primitive nonzero integral second-case solution at the campaign
exponent. -/
structure PrimitiveSecondCaseSolution where
  x : ℤ
  y : ℤ
  z : ℤ
  x_ne_zero : x ≠ 0
  y_ne_zero : y ≠ 0
  z_ne_zero : z ≠ 0
  primitive : ({x, y, z} : Finset ℤ).gcd id = 1
  equation : x ^ 59 + y ^ 59 = z ^ 59
  secondCase : (59 : ℤ) ∣ x * y * z

/-- The smallest stock charge available directly on an integral solution. -/
def PrimitiveSecondCaseSolution.charge
    (S : PrimitiveSecondCaseSolution) : ℕ :=
  S.z.natAbs

theorem PrimitiveSecondCaseSolution.charge_pos
    (S : PrimitiveSecondCaseSolution) :
    0 < S.charge :=
  Int.natAbs_pos.mpr S.z_ne_zero

/-- The exact strict-successor output required by the shared floor. -/
def StrictSuccessor (S : PrimitiveSecondCaseSolution) : Prop :=
  ∃ next : PrimitiveSecondCaseSolution, next.charge < S.charge

/-- Seam 4, stated without hiding its conclusion in a provider record. -/
def StockCreditTransformer : Prop :=
  ∀ S : PrimitiveSecondCaseSolution, StrictSuccessor S

/-- Once the transformer exists, the shared floor excludes every primitive
solution.  No further credit theorem is needed by the floor. -/
theorem false_of_stockCreditTransformer
    (htransform : StockCreditTransformer)
    (start : PrimitiveSecondCaseSolution) :
    False :=
  Fermat.Conservation.impossible_of_strict_charge_drain
    start PrimitiveSecondCaseSolution.charge
      PrimitiveSecondCaseSolution.charge_pos htransform

section GenericPrincipalization

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The generic typed hole closes as soon as the state supplies Vandiver's
two relations for every relevant pair. -/
example {ι : Type*}
    (ledger :
      Fermat.Conservation.KummerDrain.AllocatedFactorLedger
        (p := p) (K := K) ι)
    (hodd : Odd p)
    (sevenA : ∀ i j, ledger.VandiverSevenA i j)
    (sevenD : ∀ i j, ledger.VandiverSevenD i j) :
    Fermat.Conservation.KummerDrain.FactorPrincipalizationPermit
      ledger := by
  exact
    Fermat.Conservation.KummerDrain.factorPrincipalizationPermit_of_vandiver_relations
      ledger hodd sevenA sevenD

/--
error: Type mismatch
  Conservation.KummerDrain.AllocatedFactorLedger.rootClass_torsion ledger j
has type
  p • ledger.rootClass j = 0
but is expected to have type
  ledger.VandiverSevenA i j
-/
#guard_msgs in
example {ι : Type*}
    (ledger :
      Fermat.Conservation.KummerDrain.AllocatedFactorLedger
        (p := p) (K := K) ι)
    (i j : ι) :
    ledger.VandiverSevenA i j := by
  exact ledger.rootClass_torsion j

end GenericPrincipalization

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

/-
The original principalization hole is now an actual composition once
the two-node state supplies Vandiver's remaining (7a) relation and its
conjugation-transpose identity.
-/
example
    (ledger :
      Fermat.Conservation.KummerDrain.AllocatedFactorLedger
        (p := 59) (K := K) (Fin 2))
    (sevenA : ledger.VandiverSevenA 0 1)
    (htranspose :
      ledger.rootIdeal 1 =
        Ideal.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K)
          (ledger.rootIdeal 0)) :
    Fermat.Conservation.KummerDrain.FactorPrincipalizationPermit
      ledger := by
  exact
    Fermat.FiftyNine.Conservation.Fold.factorPrincipalizationPermit_of_sevenA_and_conjugationTranspose
      ledger sevenA htranspose

variable {ζ : K}
variable (hζ : IsPrimitiveRoot ζ 59)
  {u : NumberField.IsCMField.realUnits K}
  (S : PrimitiveSecondCaseSolution)

/--
error: Type mismatch
  hrepaid
has type
  Conservation.Credit.Repayment.IsRepaid 59 u
but is expected to have type
  StrictSuccessor S
-/
#guard_msgs in
example
    (hrepaid :
      Fermat.Conservation.Credit.Repayment.IsRepaid 59 u) :
    StrictSuccessor S := by
  exact hrepaid

/--
error: Type mismatch
  drainCharge_step hζ n
has type
  drainCharge hζ n < drainCharge hζ (n + 1)
but is expected to have type
  next.charge < S.charge
-/
#guard_msgs in
example (next : PrimitiveSecondCaseSolution) (n : ℕ) :
    next.charge < S.charge := by
  exact drainCharge_step hζ n

end

end Fermat.FiftyNine.Conservation.TransformerProbe
