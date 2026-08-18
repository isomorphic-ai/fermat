/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The Fermat-factor Selmer difference is Vandiver's gauge

The two normalized Fermat factors now exist as literal empty-support Selmer
classes, and their class-group obstructions are the two allocated ideal
classes.  This file takes their additive difference and identifies its class
obstruction with Vandiver's relation-(7a) word.

Consequently, (7a) is exactly the assertion that this genuine
solution-dependent Selmer difference lies in the unit leg of the canonical
unit--Selmer--class exact sequence.  No character projector, local readout,
or extra arithmetic input is used in this identification.
-/
import Fermat.FiftyNine.Conservation.CommonActionStage
import Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

namespace Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CommonActionStage
open Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.StateFactorPair

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {ζ : K} {hζ : IsPrimitiveRoot ζ 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-- The actual Selmer-class difference selected by the two normalized
Fermat factors. -/
noncomputable def fermatFactorSelmerDifference59
    (pair : StateLinkedIdealPair hζ S hz) :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 :=
  fermatPlusStrictSelmer59 pair - fermatMinusStrictSelmer59 pair

/-- Its class obstruction is literally the difference of the two allocated
ideal classes. -/
theorem fermatFactorSelmerDifference59_idealClass_difference
    (pair : StateLinkedIdealPair hζ S hz) :
    strictSelmerIdealClass59 (K := K)
        (fermatFactorSelmerDifference59 pair) =
      pair.ledger.rootClass 0 - pair.ledger.rootClass 1 := by
  rw [fermatFactorSelmerDifference59, map_sub,
    fermatPlusStrictSelmer59_idealClass,
    fermatMinusStrictSelmer59_idealClass]

/-- Using only the already-earned `59`-torsion receipt, the same obstruction
is exactly Vandiver's relation-(7a) gauge word. -/
theorem fermatFactorSelmerDifference59_idealClass
    (pair : StateLinkedIdealPair hζ S hz) :
    strictSelmerIdealClass59 (K := K)
        (fermatFactorSelmerDifference59 pair) =
      pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1 := by
  rw [fermatFactorSelmerDifference59_idealClass_difference]
  exact StateLinkedIdealPair.differenceGauge_reading pair

/-- Vanishing of the genuine Selmer difference's class obstruction is
precisely Vandiver's still-visible relation (7a). -/
theorem fermatFactorSelmerDifference59_idealClass_eq_zero_iff
    (pair : StateLinkedIdealPair hζ S hz) :
    strictSelmerIdealClass59 (K := K)
          (fermatFactorSelmerDifference59 pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  rw [fermatFactorSelmerDifference59_idealClass]
  rfl

/-- Exact-sequence form of the same boundary: Vandiver (7a) holds exactly
when the plus/minus Fermat-factor difference comes from a global unit class. -/
theorem fermatFactorSelmerDifference59_mem_unitRange_iff
    (pair : StateLinkedIdealPair hζ S hz) :
    fermatFactorSelmerDifference59 pair ∈
        Set.range (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) ↔
      pair.ledger.VandiverSevenA 0 1 := by
  rw [(selmerClassSequenceRealization
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)).exact_at_selmer]
  constructor
  · intro hzero
    apply
      (fermatFactorSelmerDifference59_idealClass_eq_zero_iff pair).mp
    exact congrArg Subtype.val hzero
  · intro hsevenA
    apply Subtype.ext
    exact
      (fermatFactorSelmerDifference59_idealClass_eq_zero_iff pair).mpr
        hsevenA

end Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
