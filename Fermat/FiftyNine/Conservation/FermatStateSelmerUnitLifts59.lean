/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Unit lifts for the two allocated Fermat factors

Takagi principalization kills both ideal-class obstructions attached to the
literal normalized Fermat factors.  Exactness of the global
unit--Selmer--class sequence therefore supplies honest global-unit lifts of
both strict Selmer sources.  This is stronger than lifting only their
difference and keeps the two factor coordinates separately available for the
later descent.
-/
import Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
import Fermat.FiftyNine.Conservation.FermatStateTakagiSevenA59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.FermatStateSelmerUnitLifts59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.FermatStateTakagiSevenA59
open Fermat.FiftyNine.Conservation.StateFactorPair

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-- The actual plus-factor strict Selmer source comes from a global unit
class once its Takagi ideal class has been killed. -/
theorem fermatPlusStrictSelmer59_mem_unitRange_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    fermatPlusStrictSelmer59 pair ∈
      Set.range (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) := by
  rw [(selmerClassSequenceRealization
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)).exact_at_selmer]
  apply Subtype.ext
  change strictSelmerIdealClass59 (K := K)
      (fermatPlusStrictSelmer59 pair) = 0
  rw [fermatPlusStrictSelmer59_idealClass,
    (rootClasses_eq_zero_takagi pair).1]

/-- The actual minus-factor strict Selmer source likewise comes from a
global unit class. -/
theorem fermatMinusStrictSelmer59_mem_unitRange_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    fermatMinusStrictSelmer59 pair ∈
      Set.range (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) := by
  rw [(selmerClassSequenceRealization
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)).exact_at_selmer]
  apply Subtype.ext
  change strictSelmerIdealClass59 (K := K)
      (fermatMinusStrictSelmer59 pair) = 0
  rw [fermatMinusStrictSelmer59_idealClass,
    (rootClasses_eq_zero_takagi pair).2]

/-- Relation (7a), now proved for the actual Fermat state, puts the genuine
plus/minus Selmer difference in the global-unit range. -/
theorem fermatFactorSelmerDifference59_mem_unitRange_takagi
    (pair : StateLinkedIdealPair hZeta S hz) :
    fermatFactorSelmerDifference59 pair ∈
      Set.range (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) :=
  (fermatFactorSelmerDifference59_mem_unitRange_iff pair).2
    (vandiverSevenA_takagi pair)

/-- An explicit existential readback of the plus global-unit lift. -/
theorem exists_unitLift_fermatPlusStrictSelmer59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ u : UnitModP (NumberField.RingOfIntegers K) 59,
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u =
        fermatPlusStrictSelmer59 pair :=
  fermatPlusStrictSelmer59_mem_unitRange_takagi pair

/-- An explicit existential readback of the minus global-unit lift. -/
theorem exists_unitLift_fermatMinusStrictSelmer59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ∃ u : UnitModP (NumberField.RingOfIntegers K) 59,
      unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u =
        fermatMinusStrictSelmer59 pair :=
  fermatMinusStrictSelmer59_mem_unitRange_takagi pair

end Fermat.FiftyNine.Conservation.FermatStateSelmerUnitLifts59
