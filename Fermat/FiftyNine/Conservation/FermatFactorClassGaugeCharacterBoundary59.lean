/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Character-seating boundary for the Fermat-factor class gauge

The selected relation-`(7a)` class is the class-map image of the literal,
unprojected plus-minus Fermat-factor Selmer difference.  Strong naturality
identifies its class-group character projection with the class-map image of
the corresponding Selmer projection.

Consequently, fixedness of the selected class under the canonical irregular
projector is equivalent to one exact missing receipt: projecting the Selmer
difference must not change its class obstruction.  Exactness of the genuine
unit--Selmer--class sequence expresses the same boundary as membership of
`q - P_chi(q)` in the actual global-unit range.

No Takagi theorem, relation `(7a)`, Artin map, class-group dimension claim,
or injectivity assertion is imported or used here.
-/
import Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

namespace Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

/-- Projecting the selected class gauge is exactly the class obstruction of
the projected genuine Fermat-factor Selmer difference.  This is the strongest
unconditional character-seating identity currently supplied by the existing
projector and class-map naturality receipts. -/
theorem cyclotomicClassProjector59_selectedClassGauge59_eq_projectedSelmerClass
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassProjector59 K irregularCharacter59
        (selectedClassGauge59 pair) =
      strictSelmerClassLinearMap59 K
        ((characterProjectorAt
          (cyclotomicStrictSelmerRepresentation59 K)
          irregularCharacter59
          (fermatFactorSelmerDifference59 pair)).1) := by
  rw [strictSelmerClassLinearMap59_characterProjector]
  apply congrArg (cyclotomicClassProjector59 K irregularCharacter59)
  exact (fermatFactorClassGaugeSeating59 pair).gauge_at_fermat.symm

/-- Thus fixedness of the selected class is precisely equality of the class
obstructions before and after projecting the genuine Selmer difference. -/
theorem selectedClassGauge59_projector_fixed_iff_projectedClass_eq_class
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassProjector59 K irregularCharacter59
        (selectedClassGauge59 pair) = selectedClassGauge59 pair ↔
      strictSelmerClassLinearMap59 K
          ((characterProjectorAt
            (cyclotomicStrictSelmerRepresentation59 K)
            irregularCharacter59
            (fermatFactorSelmerDifference59 pair)).1) =
        strictSelmerClassLinearMap59 K
          (fermatFactorSelmerDifference59 pair) := by
  rw [cyclotomicClassProjector59_selectedClassGauge59_eq_projectedSelmerClass]
  rw [← (fermatFactorClassGaugeSeating59 pair).gauge_at_fermat]
  rfl

/-- The same missing receipt in exact-sequence form: the unprojected Selmer
difference and its irregular projection have the same class obstruction
exactly when their difference is represented by a genuine global unit. -/
theorem selectedClassGauge59_projector_fixed_iff_difference_mem_unitRange
    (pair : StateLinkedIdealPair hZeta S hz) :
    cyclotomicClassProjector59 K irregularCharacter59
        (selectedClassGauge59 pair) = selectedClassGauge59 pair ↔
      fermatFactorSelmerDifference59 pair -
          (characterProjectorAt
            (cyclotomicStrictSelmerRepresentation59 K)
            irregularCharacter59
            (fermatFactorSelmerDifference59 pair)).1 ∈
        Set.range (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) := by
  rw [selectedClassGauge59_projector_fixed_iff_projectedClass_eq_class]
  let q := fermatFactorSelmerDifference59 pair
  let projected :=
    (characterProjectorAt
      (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 q).1
  change strictSelmerClassLinearMap59 K projected =
      strictSelmerClassLinearMap59 K q ↔
    q - projected ∈ Set.range (unitInclusion
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59))
  rw [← fermatFactorClassGaugeMap59_eq_zero_iff_mem_unitRange]
  rw [map_sub, fermatFactorClassGaugeMap59_apply,
    fermatFactorClassGaugeMap59_apply]
  exact eq_comm.trans sub_eq_zero.symm

end Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59
