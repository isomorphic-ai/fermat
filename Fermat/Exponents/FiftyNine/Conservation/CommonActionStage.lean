/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# The conductor-59 state on the common-action stage

The actual normalized Fermat pair supplies two allocated ideals and the
proved relative-norm fold.  This module lifts both roots into non-lossy
`ClassCarrier` states, threads the fold receipt through them, and retains the
statewise class obstruction.  The vendored Selmer class sequence now supplies
the formerly missing exactness canonically.  Conditional on a supplied
reflected exact pair, which already carries the omega-dual laws, the selected
stage stops next at its missing character allocations.  Only a boundary also
carrying the integral data and both beta compatibilities may advance to the
strict-route arithmetic-representation target.
-/
import Fermat.Experiments.Conservation.CommonActionStage
import Fermat.Exponents.FiftyNine.Conservation.StateFactorConjugation

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

/-- The selected difference gauge is exactly the relation-(7a) word.  The
rewrite from subtraction uses only the already-earned `59`-torsion receipt;
it does not assert that the reading vanishes. -/
theorem StateLinkedIdealPair.differenceGauge_reading
    (pair : StateLinkedIdealPair hζ S hz) :
    differenceGauge (AllocatedClass K)
        (StateLinkedIdealPair.classObstruction pair) =
      pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1 := by
  change pair.ledger.rootClass 0 - pair.ledger.rootClass 1 =
    pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1
  rw [sub_eq_add_neg]
  congr 1
  have htorsion := pair.ledger.rootClass_torsion 1
  have hsplit :
      58 • pair.ledger.rootClass 1 + pair.ledger.rootClass 1 = 0 := by
    calc
      58 • pair.ledger.rootClass 1 + pair.ledger.rootClass 1 =
          58 • pair.ledger.rootClass 1 + 1 • pair.ledger.rootClass 1 := by
            rw [one_nsmul]
      _ = (58 + 1) • pair.ledger.rootClass 1 := by rw [add_nsmul]
      _ = 59 • pair.ledger.rootClass 1 := by norm_num
      _ = 0 := htorsion
  exact (eq_neg_of_add_eq_zero_left hsplit).symm

/-- Vanishing of the selected difference gauge is precisely the still-open
Vandiver relation (7a), rather than a newly proved unit-ideal reading. -/
theorem StateLinkedIdealPair.differenceGauge_eq_zero_iff_vandiverSevenA
    (pair : StateLinkedIdealPair hζ S hz) :
    differenceGauge (AllocatedClass K)
          (StateLinkedIdealPair.classObstruction pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  rw [StateLinkedIdealPair.differenceGauge_reading]
  rfl

/-- The first missing stage service after the now-canonical Selmer class
sequence, conditional on one supplied reflected exact pair.  The pair already
supplies the omega-dual laws; the target asks only for both commuting Kummer
character allocations and the separately directed allocation into the
reflected-dual class leg.  Readback maps retain the actual allocated roots on
all three class views, so zero maps cannot fake the service unless the
corresponding retained root itself vanishes. -/
def StateLinkedIdealPair.CharacterDualAllocationTarget
    {Delta : Type*} [CommGroup Delta] [Fintype Delta]
    [Invertible (Fintype.card Delta : PadicInt 59)]
    {UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual : Type*}
    [AddCommGroup UChi] [Module (IntegralPadicGroupAlgebra 59 Delta) UChi]
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
    [AddCommGroup ClassChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassChi]
    [AddCommGroup UStar] [Module (IntegralPadicGroupAlgebra 59 Delta) UStar]
    [AddCommGroup SelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChiStar]
    [AddCommGroup ClassStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassStar]
    [AddCommGroup UDual] [Module (IntegralPadicGroupAlgebra 59 Delta) UDual]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
    [AddCommGroup ClassDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassDual]
    (pair : StateLinkedIdealPair hζ S hz)
    (omega : Fermat.Conservation.InvolutiveBase.Character (PadicInt 59) Delta)
    (reflectedPair : ReflectedExactFilteredPair 59
      (IntegralPadicGroupAlgebra 59 Delta)
      UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual
      (Fermat.Conservation.InvolutiveBase.hash omega)) : Prop :=
  ∃ (binding : KummerPairedBinding
        (selmerClassSequenceRealization
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59))
        reflectedPair)
      (allocation : CharacterClassAllocation
        (p := 59) (K := K) (ClassChi := ClassChi) (ClassDual := ClassDual))
      (chiReadback : ClassChi →+
        ClassPTorsion (NumberField.RingOfIntegers K) 59)
      (chiStarReadback : ClassStar →+
        ClassPTorsion (NumberField.RingOfIntegers K) 59)
      (reflectedDualReadback : ClassDual →+
        ClassPTorsion (NumberField.RingOfIntegers K) 59),
      allocation.chi = binding.chi.classAllocation ∧
      chiReadback
          (allocation.chi (allocatedRootClassPTorsion pair.ledger 0)) =
        allocatedRootClassPTorsion pair.ledger 0 ∧
      chiStarReadback
          (binding.chiStar.classAllocation
            (allocatedRootClassPTorsion pair.ledger 1)) =
        allocatedRootClassPTorsion pair.ledger 1 ∧
      reflectedDualReadback
          (allocation.reflectedDual
            (allocatedRootClassPTorsion pair.ledger 1)) =
        allocatedRootClassPTorsion pair.ledger 1

/-- Conditional on one supplied reflected exact pair, the selected stage now
stops at character allocation.  The pair already supplies the omega-dual laws,
while the class obstruction and its difference gauge remain retained and
exactness is provided by the vendored sequence. -/
def StateLinkedIdealPair.characterDualAllocationWall
    {Delta : Type*} [CommGroup Delta] [Fintype Delta]
    [Invertible (Fintype.card Delta : PadicInt 59)]
    {UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual : Type*}
    [AddCommGroup UChi] [Module (IntegralPadicGroupAlgebra 59 Delta) UChi]
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
    [AddCommGroup ClassChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassChi]
    [AddCommGroup UStar] [Module (IntegralPadicGroupAlgebra 59 Delta) UStar]
    [AddCommGroup SelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChiStar]
    [AddCommGroup ClassStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassStar]
    [AddCommGroup UDual] [Module (IntegralPadicGroupAlgebra 59 Delta) UDual]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
    [AddCommGroup ClassDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassDual]
    (pair : StateLinkedIdealPair hζ S hz)
    (omega : Fermat.Conservation.InvolutiveBase.Character (PadicInt 59) Delta)
    (reflectedPair : ReflectedExactFilteredPair 59
      (IntegralPadicGroupAlgebra 59 Delta)
      UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual
      (Fermat.Conservation.InvolutiveBase.hash omega)) :
    Outcome.LocalizedWall
      (StateLinkedIdealPair.classObstruction pair) where
  obstruction := StateLinkedIdealPair.classObstruction pair
  obstruction_eq := rfl
  address := Outcome.WallAddress.characterDualAllocation
  target := StateLinkedIdealPair.CharacterDualAllocationTarget
    pair omega reflectedPair

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
  kummerBinding : KummerPairedBinding
    (selmerClassSequenceRealization
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59))
    reflectedPair
  classAllocation : CharacterClassAllocation
    (p := 59) (K := K) (ClassChi := ClassChi) (ClassDual := ClassDual)
  classAllocation_chi_eq :
    classAllocation.chi = kummerBinding.chi.classAllocation
  chiClassReadback :
    ClassChi →+ ClassPTorsion (NumberField.RingOfIntegers K) 59
  chiClassReadback_root_zero :
    chiClassReadback
        (classAllocation.chi (allocatedRootClassPTorsion pair.ledger 0)) =
      allocatedRootClassPTorsion pair.ledger 0
  chiStarClassReadback :
    ClassStar →+ ClassPTorsion (NumberField.RingOfIntegers K) 59
  chiStarClassReadback_root_one :
    chiStarClassReadback
        (kummerBinding.chiStar.classAllocation
          (allocatedRootClassPTorsion pair.ledger 1)) =
      allocatedRootClassPTorsion pair.ledger 1
  reflectedDualClassReadback :
    ClassDual →+ ClassPTorsion (NumberField.RingOfIntegers K) 59
  reflectedDualClassReadback_root_one :
    reflectedDualClassReadback
        (classAllocation.reflectedDual
          (allocatedRootClassPTorsion pair.ledger 1)) =
      allocatedRootClassPTorsion pair.ledger 1
  theta : guarded.integral.source.ideal
  plusBetaCompatibility : StateConversionCompatibility
    (StateLinkedIdealPair.plusClassCarrierState pair) guarded.chi theta
      (allocatedSelmerObstruction guarded.exactPair
        classAllocation pair.ledger 0 1).1
  minusBetaCompatibility : StateConversionCompatibility
    (StateLinkedIdealPair.minusClassCarrierState pair) guarded.reflectedDual
      (guarded.integral.sharpTransport theta)
      (allocatedSelmerObstruction guarded.exactPair
        classAllocation pair.ledger 0 1).2

/-- The paired Selmer obstruction is determined by the paired exact carrier,
the two directional class allocations, and the allocated Fermat roots.  It is
not separately stored in `StrictRouteBoundary`. -/
def StateLinkedIdealPair.StrictRouteBoundary.selmerObstruction
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
    {pair : StateLinkedIdealPair hζ S hz}
    {omega :
      Fermat.Conservation.InvolutiveBase.Character (PadicInt 59) Delta}
    (boundary : StateLinkedIdealPair.StrictRouteBoundary pair omega
      (UChi := UChi) (SelmerChi := SelmerChi) (ClassChi := ClassChi)
      (UStar := UStar) (SelmerChiStar := SelmerChiStar)
      (ClassStar := ClassStar) (UDual := UDual)
      (DOmegaSelmerChiStar := DOmegaSelmerChiStar)
      (ClassDual := ClassDual)) :
    SelmerChi × DOmegaSelmerChiStar :=
  allocatedSelmerObstruction boundary.guarded.exactPair
    boundary.classAllocation pair.ledger 0 1

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
      (R := NumberField.RingOfIntegers K) (K := K)
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
        (R := NumberField.RingOfIntegers K) (K := K)
        (SelmerChi := SelmerChi)
        (DOmegaSelmerChiStar := DOmegaSelmerChiStar) omega chi :=
  rfl

/-- Conditional on one supplied reflected exact pair, the selected-stage
result stops at the first missing character-allocation service.  The pair
already supplies the omega-dual laws; later integral, beta, and route data is
not accepted here, so this value cannot skip directly to the representation
wall. -/
def StateLinkedIdealPair.typedLocalizedResult
    {Delta : Type*} [CommGroup Delta] [Fintype Delta]
    [Invertible (Fintype.card Delta : PadicInt 59)]
    {UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual : Type*}
    [AddCommGroup UChi] [Module (IntegralPadicGroupAlgebra 59 Delta) UChi]
    [AddCommGroup SelmerChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChi]
    [AddCommGroup ClassChi]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassChi]
    [AddCommGroup UStar] [Module (IntegralPadicGroupAlgebra 59 Delta) UStar]
    [AddCommGroup SelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) SelmerChiStar]
    [AddCommGroup ClassStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassStar]
    [AddCommGroup UDual] [Module (IntegralPadicGroupAlgebra 59 Delta) UDual]
    [AddCommGroup DOmegaSelmerChiStar]
    [Module (IntegralPadicGroupAlgebra 59 Delta) DOmegaSelmerChiStar]
    [AddCommGroup ClassDual]
    [Module (IntegralPadicGroupAlgebra 59 Delta) ClassDual]
    (pair : StateLinkedIdealPair hζ S hz)
    (omega : Fermat.Conservation.InvolutiveBase.Character (PadicInt 59) Delta)
    (reflectedPair : ReflectedExactFilteredPair 59
      (IntegralPadicGroupAlgebra 59 Delta)
      UChi SelmerChi ClassChi UStar SelmerChiStar ClassStar
      UDual DOmegaSelmerChiStar ClassDual
      (Fermat.Conservation.InvolutiveBase.hash omega))
    (transverse :
      Module.End ℤ (AllocatedClass K × AllocatedClass K)) :
    Outcome.TypedResult
      (cycle := sevenDClassOperator (AllocatedClass K))
      (transverse := transverse)
      (m := StateLinkedIdealPair.classObstruction pair)
      (differenceGauge (AllocatedClass K)) :=
  .localizedWall
    (StateLinkedIdealPair.characterDualAllocationWall
      pair omega reflectedPair)

end Fermat.FiftyNine.Conservation.CommonActionStage
