/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# Probe: the post-repayment stock/credit seam

This scratch file asks only what the current clean conservation cone can
compose after repayment.  A primitive second-case exponent-59 solution now
produces its selected ideal pair directly.  A genuine transformer must
principalize that pair and then return another primitive second-case
solution with strictly smaller charge.

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
import Fermat.Conservation.AreaTransfer
import Fermat.FiftyNine.Conservation.Fold
import Fermat.FiftyNine.Conservation.GaugeQuotient
import Fermat.FiftyNine.Conservation.StateFactorConjugation
import Fermat.FiftyNine.Conservation.StateFactorPair

open scoped NumberField

namespace Fermat.FiftyNine.Conservation.TransformerProbe

noncomputable section

open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.StateFactorPair

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
The allocation and conjugation sides of the original principalization hole
are now actual state-produced terms.  The only remaining input is
Vandiver's Lemma-I relation (7a) for that canonical pair; its relative-norm
fold (7d) is derived internally.
-/
example
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution)
    (hz : (59 : ℤ) ∣ S.z)
    (sevenA :
      (allocatedPair hζ S hz).ledger.VandiverSevenA 0 1) :
    Fermat.Conservation.KummerDrain.FactorPrincipalizationPermit
      (allocatedPair hζ S hz).ledger := by
  exact
    Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.factorPrincipalizationPermit_of_sevenA
      (allocatedPair hζ S hz) sevenA

/-! The exact-cancellation equation exported by `Heis` is an integer
payload fact.  It cannot fill the class-group relation required by the
inherited abelian transaction. -/

/--
error: Type mismatch
  hcancel
has type
  word.c = -c
but is expected to have type
  (allocatedPair hζ S hz).ledger.VandiverSevenA 0 1
-/
#guard_msgs in
example
    {ζ : K} (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution)
    (hz : (59 : ℤ) ∣ S.z)
    (word : Fermat.Conservation.Heis ℤ) (c : ℤ)
    (hcancel : word.c = -c) :
    (allocatedPair hζ S hz).ledger.VandiverSevenA 0 1 := by
  exact hcancel

variable {ζ : K}
variable (hζ : IsPrimitiveRoot ζ 59)
  {u : NumberField.IsCMField.realUnits K}
  (S : PrimitiveSecondCaseSolution)

/--
error: Type mismatch
  (allocatedPair hζ S hz).ledger.rootQuotient 0 1
has type
  FractionalIdeal (nonZeroDivisors (𝓞 K)) K
but is expected to have type
  ↥(NumberField.IsCMField.realUnits K)
-/
#guard_msgs in
example (hz : (59 : ℤ) ∣ S.z) :
    NumberField.IsCMField.realUnits K := by
  exact (allocatedPair hζ S hz).ledger.rootQuotient 0 1

/--
error: Type mismatch
  Instance.repayment_of_capacity_and_flow hζ hdeep
has type
  Conservation.Credit.Repayment.IsRepaid 59 u
but is expected to have type
  (allocatedPair hζ S hz).ledger.VandiverSevenA 0 1
-/
#guard_msgs in
example (hz : (59 : ℤ) ∣ S.z)
    (hdeep :
      Fermat.FiftyNine.Conservation.Instance.IsDeeplyRepayable hζ u) :
    (allocatedPair hζ S hz).ledger.VandiverSevenA 0 1 := by
  exact
    Fermat.FiftyNine.Conservation.Instance.repayment_of_capacity_and_flow
      hζ hdeep

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
