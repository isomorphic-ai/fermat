/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conductor-59 state on the common-action stage

The actual normalized Fermat pair supplies two allocated ideals and the
proved relative-norm fold.  This module lifts both roots into non-lossy
`ClassCarrier` states, threads the fold receipt through them, and retains the
statewise class obstruction.  Transport of that receipt to the strict-route
Selmer corner is deliberately stopped at the named arithmetic-representation
target.
-/
import Fermat.Conservation.CommonActionStage
import Fermat.FiftyNine.Conservation.StateFactorConjugation

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.CommonActionStage

open Fermat.FiftyNine.Conservation.FermatState
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.StateFactorConjugation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.LinkingInterfaces

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {ζ : K} {hζ : IsPrimitiveRoot ζ 59}
  {S : PrimitiveSecondCaseSolution} {hz : (59 : ℤ) ∣ S.z}

/-- The two allocated Fermat classes, before the missing character
allocation. -/
def StateLinkedIdealPair.classObstruction
    (pair : StateLinkedIdealPair hζ S hz) :
    AllocatedClass K × AllocatedClass K :=
  allocatedClassObstruction pair.ledger 0 1

/-- The original accounted relative-norm fold receipt. -/
def StateLinkedIdealPair.reflectionFoldTransfer
    (pair : StateLinkedIdealPair hζ S hz) :
    Fermat.Conservation.Transfer (AllocatedClass K) :=
  Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenDFoldToVacuumTransfer
    pair

/-- The proved (7d) fold re-expressed as the class-shadow corner relation
`1 + classSwap` acting on the retained statewise obstruction. -/
def StateLinkedIdealPair.sevenDClassReceipt
    (pair : StateLinkedIdealPair hζ S hz) :
    Fermat.Conservation.ClassCarrier.AnnihilatorReceipt
      (Module.End ℤ (AllocatedClass K × AllocatedClass K))
      (AllocatedClass K × AllocatedClass K) :=
  allocatedSevenDClassReceipt pair.ledger 0 1
    (Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD
      pair)

/-- The plus root above its lossy class, with beta and the fold receipt. -/
def StateLinkedIdealPair.plusClassCarrierState
    (pair : StateLinkedIdealPair hζ S hz) :=
  allocatedSevenDReceiptedRootState
    pair.ledger 0 1 0
      (Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD
        pair)

/-- The reflected minus root above its lossy class, independently receipted;
it is not obtained by swapping the plus carrier. -/
def StateLinkedIdealPair.minusClassCarrierState
    (pair : StateLinkedIdealPair hζ S hz) :=
  allocatedSevenDReceiptedRootState
    pair.ledger 0 1 1
      (Fermat.FiftyNine.Conservation.StateFactorConjugation.StateLinkedIdealPair.vandiverSevenD
        pair)

@[simp]
theorem StateLinkedIdealPair.plusClassCarrierState_receipt
    (pair : StateLinkedIdealPair hζ S hz) :
    (StateLinkedIdealPair.plusClassCarrierState pair).annihilatorReceipts =
      [StateLinkedIdealPair.sevenDClassReceipt pair] :=
  rfl

@[simp]
theorem StateLinkedIdealPair.minusClassCarrierState_receipt
    (pair : StateLinkedIdealPair hζ S hz) :
    (StateLinkedIdealPair.minusClassCarrierState pair).annihilatorReceipts =
      [StateLinkedIdealPair.sevenDClassReceipt pair] :=
  rfl

/-- The plus `ClassCarrier` projects to the allocated plus class. -/
theorem StateLinkedIdealPair.plusClassCarrierState_class
    (pair : StateLinkedIdealPair hζ S hz) :
    Additive.ofMul
        (Fermat.Conservation.ClassCarrier.idealClassProjection
          (StateLinkedIdealPair.plusClassCarrierState pair)) =
      pair.ledger.rootClass 0 :=
  allocatedRootState_class pair.ledger 0 _

/-- The minus `ClassCarrier` projects to the allocated minus class. -/
theorem StateLinkedIdealPair.minusClassCarrierState_class
    (pair : StateLinkedIdealPair hζ S hz) :
    Additive.ofMul
        (Fermat.Conservation.ClassCarrier.idealClassProjection
          (StateLinkedIdealPair.minusClassCarrierState pair)) =
      pair.ledger.rootClass 1 :=
  allocatedRootState_class pair.ledger 1 _

/-- Reading the plus beta reconstructs the original allocated ideal. -/
theorem StateLinkedIdealPair.plusClassCarrierState_source_eq
    (pair : StateLinkedIdealPair hζ S hz) :
    allocatedRootSource pair.ledger 0 =
      toPrincipalIdeal (NumberField.RingOfIntegers K) K
          (StateLinkedIdealPair.plusClassCarrierState pair).beta *
        (StateLinkedIdealPair.plusClassCarrierState pair).reduced :=
  allocatedRootState_source_eq pair.ledger 0 _

/-- Reading the minus beta reconstructs the independently retained source. -/
theorem StateLinkedIdealPair.minusClassCarrierState_source_eq
    (pair : StateLinkedIdealPair hζ S hz) :
    allocatedRootSource pair.ledger 1 =
      toPrincipalIdeal (NumberField.RingOfIntegers K) K
          (StateLinkedIdealPair.minusClassCarrierState pair).beta *
        (StateLinkedIdealPair.minusClassCarrierState pair).reduced :=
  allocatedRootState_source_eq pair.ledger 1 _

/-- The (7d) class-shadow receipt carries exactly the statewise Fermat
obstruction. -/
theorem StateLinkedIdealPair.sevenDClassReceipt_payload
    (pair : StateLinkedIdealPair hζ S hz) :
    (StateLinkedIdealPair.sevenDClassReceipt pair).payload =
      StateLinkedIdealPair.classObstruction pair :=
  rfl

/-- The canonical allocated pair selected by `StateFactorPair`, now retained
as the requested statewise obstruction. -/
def canonicalClassObstruction
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :
    AllocatedClass K × AllocatedClass K :=
  StateLinkedIdealPair.classObstruction (allocatedPair hζ S hz)

/-- The canonical pair's compiled (7d) class-shadow receipt. -/
def canonicalSevenDClassReceipt
    (hζ : IsPrimitiveRoot ζ 59)
    (S : PrimitiveSecondCaseSolution) (hz : (59 : ℤ) ∣ S.z) :=
  StateLinkedIdealPair.sevenDClassReceipt (allocatedPair hζ S hz)

/-- The exact first missing selected-instance seam.  The state and fold
receipt exist, while Mathlib still withholds the class projection/exactness
needed to realize the concrete Selmer lift. -/
def StateLinkedIdealPair.selmerClassExactnessWall
    (pair : StateLinkedIdealPair hζ S hz) :
    Outcome.LocalizedWall
      (StateLinkedIdealPair.classObstruction pair) where
  obstruction := StateLinkedIdealPair.classObstruction pair
  obstruction_eq := rfl
  address := Outcome.WallAddress.selmerClassExactness
  target := WithheldSelmerClassSequenceRealization
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)

/-- Evidence that every seam before the strict-route representation has
actually been crossed on this selected state.  It binds the actual Kummer
sequence, the omega-twisted character dual, both integral guards, the
allocated `p`-torsion class lift, and both ClassCarrier beta values into one
paired carrier. -/
structure StateLinkedIdealPair.StrictRouteBoundary
    {Delta : Type*} [CommGroup Delta] [Fintype Delta]
    [Invertible (Fintype.card Delta : PadicInt 59)]
    {UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual : Type*}
    [AddCommGroup UChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UChi]
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
    [Module (PadicInt 59) SelmerChi]
    [AddCommGroup ClassChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassChi]
    [AddCommGroup UStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UStar]
    [AddCommGroup SelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChiStar]
    [AddCommGroup ClassStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassStar]
    [AddCommGroup UDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UDual]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
    [Module (PadicInt 59) DOmegaSelmerChiStar]
    [AddCommGroup ClassDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassDual]
    (pair : StateLinkedIdealPair hζ S hz)
    (omega :
      Fermat.Conservation.InvolutiveBase.Character (PadicInt 59) Delta) where
  sequence : SelmerClassSequenceRealization
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
  guarded : GuardedPairedCarrier 59 Delta omega
    UChi SelmerChi ClassChi UDual DOmegaSelmerChiStar ClassDual
    Kˣ (FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)ˣ
    (toPrincipalIdeal (NumberField.RingOfIntegers K) K)
  reflectedPair : ReflectedExactFilteredPair 59
    (IntegralPadicGroupAlgebra 59 Delta)
    UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
    UDual DOmegaSelmerChiStar ClassDual
    (Fermat.Conservation.InvolutiveBase.hash omega)
  exactPair_eq : reflectedPair.pair = guarded.exactPair
  kummerBinding : KummerPairedBinding sequence reflectedPair
  classAllocation : CharacterClassAllocation
    (p := 59) (K := K) (ClassChi := ClassChi) (ClassDual := ClassDual)
  selmerObstruction : SelmerChi × DOmegaSelmerChiStar
  selmerObstruction_eq :
    selmerObstruction = allocatedSelmerObstruction guarded.exactPair
      classAllocation pair.ledger 0 1
  theta : guarded.integral.source.ideal
  plusBetaCompatibility : StateConversionCompatibility
    (StateLinkedIdealPair.plusClassCarrierState pair) guarded.chi theta
      selmerObstruction.1
  minusBetaCompatibility : StateConversionCompatibility
    (StateLinkedIdealPair.minusClassCarrierState pair) guarded.reflectedDual
      (guarded.integral.sharpTransport theta) selmerObstruction.2

/-- Once a `StrictRouteBoundary` supplies every earlier receipt, the next
wall is exactly the existing missing strict-route representation.  Its
obstruction is now the actual paired Selmer lift, not the raw class pair. -/
def StateLinkedIdealPair.strictRouteRhoWall
    {Delta : Type*} [CommGroup Delta] [Fintype Delta]
    [Invertible (Fintype.card Delta : PadicInt 59)]
    {UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual : Type*}
    [AddCommGroup UChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UChi]
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
    [Module (PadicInt 59) SelmerChi]
    [AddCommGroup ClassChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassChi]
    [AddCommGroup UStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UStar]
    [AddCommGroup SelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChiStar]
    [AddCommGroup ClassStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassStar]
    [AddCommGroup UDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UDual]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
    [Module (PadicInt 59) DOmegaSelmerChiStar]
    [AddCommGroup ClassDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassDual]
    (pair : StateLinkedIdealPair hζ S hz)
    (omega chi :
      Fermat.Conservation.InvolutiveBase.Character (PadicInt 59) Delta)
    (boundary : StateLinkedIdealPair.StrictRouteBoundary pair omega
      (UChi := UChi) (SelmerChi := SelmerChi) (ClassChi := ClassChi)
      (UStar := UStar) (SelmerChiStar := SelmerChiStar)
      (ClassStar := ClassStar) (UDual := UDual)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      (ClassDual := ClassDual)) :
    Outcome.LocalizedWall boundary.selmerObstruction where
  obstruction := boundary.selmerObstruction
  obstruction_eq := rfl
  address := Outcome.WallAddress.strictRouteRho
  target :=
    Fermat.Conservation.LinkingInterfaces.ReflectedSelmerArithmeticRepresentationTarget
      (SelmerChi := SelmerChi)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar) omega chi

theorem StateLinkedIdealPair.strictRouteRhoWall_target
    {Delta : Type*} [CommGroup Delta] [Fintype Delta]
    [Invertible (Fintype.card Delta : PadicInt 59)]
    {UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual : Type*}
    [AddCommGroup UChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UChi]
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
    [Module (PadicInt 59) SelmerChi]
    [AddCommGroup ClassChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassChi]
    [AddCommGroup UStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UStar]
    [AddCommGroup SelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChiStar]
    [AddCommGroup ClassStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassStar]
    [AddCommGroup UDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) UDual]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
    [Module (PadicInt 59) DOmegaSelmerChiStar]
    [AddCommGroup ClassDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassDual]
    (pair : StateLinkedIdealPair hζ S hz)
    (omega chi :
      Fermat.Conservation.InvolutiveBase.Character (PadicInt 59) Delta)
    (boundary : StateLinkedIdealPair.StrictRouteBoundary pair omega
      (UChi := UChi) (SelmerChi := SelmerChi) (ClassChi := ClassChi)
      (UStar := UStar) (SelmerChiStar := SelmerChiStar)
      (ClassStar := ClassStar) (UDual := UDual)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      (ClassDual := ClassDual)) :
    (StateLinkedIdealPair.strictRouteRhoWall pair omega chi boundary).target =
      Fermat.Conservation.LinkingInterfaces.ReflectedSelmerArithmeticRepresentationTarget
        (SelmerChi := SelmerChi)
        (DOmegaSelmerChiStar := DOmegaSelmerChiStar) omega chi :=
  rfl

/-- The unconditional selected-stage result stops at the first missing
class-projection/exactness theorem.  Later route data is not accepted here,
so this value cannot skip directly to the representation wall. -/
def StateLinkedIdealPair.typedLocalizedResult
    (pair : StateLinkedIdealPair hζ S hz)
    (transverse :
      Module.End ℤ (AllocatedClass K × AllocatedClass K)) :
    Outcome.TypedResult
      (cycle := sevenDClassOperator (AllocatedClass K))
      (transverse := transverse)
      (m := StateLinkedIdealPair.classObstruction pair)
      (differenceGauge (AllocatedClass K)) :=
  .localizedWall
    (StateLinkedIdealPair.selmerClassExactnessWall pair)

end Fermat.FiftyNine.Conservation.CommonActionStage
