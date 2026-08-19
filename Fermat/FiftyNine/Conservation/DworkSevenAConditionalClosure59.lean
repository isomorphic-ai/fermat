/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Conditional relation-7A closure at the projected Fermat test

The exact Dwork--Artin balance lives on the genuine irregular primal test
space.  This file places the concrete plus-minus Fermat-factor Selmer
difference into that space by the actual chi=15 character projector, then
computes its class-gauge value through strong projector naturality.

Under the still-explicit arithmetic inputs predicted by the Kummer--Artin
route--a supplied normalized Dwork lift, global reciprocity, chi=15 seating
of the selected class, rank one of the actual class-character line, and
nonvanishing of the canonical readout on that line--the Dwork boundary at
this projected Fermat test vanishes exactly when Vandiver's relation `(7a)`
holds.

No lift, seating theorem, rank statement, or nonvanishing witness is chosen
or manufactured here.
-/
import Fermat.FiftyNine.Conservation.CanonicalModeFortyFourCharacterLine827
import Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Fermat.FiftyNine.Conservation.DworkSevenAConditionalClosure59

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalModeFortyFourCharacterLine827
open Fermat.FiftyNine.Conservation.CanonicalModeFortyFourClassFactorization827
open Fermat.FiftyNine.Conservation.CharacterLinePointwiseFaithfulness59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.DworkSeatedLambdaMeter59
open Fermat.FiftyNine.Conservation.DworkSevenAArtinBalance59
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeCharacterBoundary59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
open Fermat.FiftyNine.Conservation.IrregularPrimalClassGaugeBridge827
open Fermat.FiftyNine.Conservation.LambdaMeterPointedPoitouTate827
open Fermat.FiftyNine.Conservation.PointedTateIncidence
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.UlamReadout827
open Fermat.FiftyNine.Conservation.VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

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

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
private theorem irregularOldPrimal59_nsmul_eq_zero
    (x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) :
    59 • x = 0 := by
  apply Subtype.ext
  exact p_nsmul_eq_zero x.1

noncomputable local instance instIrregularOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  AddCommGroup.zmodModule irregularOldPrimal59_nsmul_eq_zero

noncomputable local instance instQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)

/-! ## The genuine projected Fermat test -/

/-- The literal plus-minus Fermat-factor Selmer difference, projected into
the actual chi=15 irregular primal Poitou--Tate test space. -/
noncomputable def projectedFermatPrimalTest59
    (pair : StateLinkedIdealPair hZeta S hz) :
    OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59 :=
  characterProjectorAt
    (cyclotomicStrictSelmerRepresentation59 K)
    irregularCharacter59
    (fermatFactorSelmerDifference59 pair)

@[simp]
theorem projectedFermatPrimalTest59_coe
    (pair : StateLinkedIdealPair hZeta S hz) :
    (projectedFermatPrimalTest59 (K := K) pair).1 =
      (characterProjectorAt
        (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59
        (fermatFactorSelmerDifference59 pair)).1 :=
  rfl

/-! ## Its exact class-gauge value -/

/-- Strong class-map naturality computes the projected Fermat test's
genuine irregular primal class gauge as the chi=15 projection of the
selected relation-7A class. -/
theorem irregularPrimalClassGauge59_projectedFermatPrimalTest59
    (pair : StateLinkedIdealPair hZeta S hz) :
    irregularPrimalClassGauge59 K
        (projectedFermatPrimalTest59 (K := K) pair) =
      cyclotomicClassProjector59 K irregularCharacter59
        (selectedClassGauge59 pair) := by
  rw [irregularPrimalClassGauge59_apply]
  exact
    (cyclotomicClassProjector59_selectedClassGauge59_eq_projectedSelmerClass
      (K := K) pair).symm

/-- Under the explicit chi=15 class-seating premise, the projected test's
class-gauge value is the selected relation-7A class itself. -/
theorem irregularPrimalClassGauge59_projectedFermatPrimalTest59_eq_selected
    (pair : StateLinkedIdealPair hZeta S hz)
    (seated :
      cyclotomicClassProjector59 K irregularCharacter59
          (selectedClassGauge59 pair) = selectedClassGauge59 pair) :
    irregularPrimalClassGauge59 K
        (projectedFermatPrimalTest59 (K := K) pair) =
      selectedClassGauge59 pair := by
  rw [irregularPrimalClassGauge59_projectedFermatPrimalTest59 pair,
    seated]

/-! ## Conditional relation-7A closure -/

/-- With every remaining arithmetic input visible, the concrete Dwork
boundary at the genuine projected Fermat test vanishes exactly when
Vandiver's relation `(7a)` holds. -/
theorem dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA
    (lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K))
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (pair : StateLinkedIdealPair hZeta S hz)
    (seated :
      cyclotomicClassProjector59 K irregularCharacter59
          (selectedClassGauge59 pair) = selectedClassGauge59 pair)
    (rank_one : Module.finrank (ZMod 59)
      (irregularClassCharacterLine59 K) = 1)
    (readout_ne_zero :
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0) :
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K)
        (projectedFermatPrimalTest59 (K := K) pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  have pointwise :=
    dworkLambdaBoundary_apply_eq_zero_iff_classGaugeReadout_apply_eq_zero
      (K := K) lift reciprocity
        (projectedFermatPrimalTest59 (K := K) pair)
  constructor
  · intro boundary_zero
    have readout_zero := pointwise.mp boundary_zero
    rw [irregularPrimalClassGauge59_projectedFermatPrimalTest59_eq_selected
      pair seated] at readout_zero
    apply (selectedClassGauge59_eq_zero_iff_vandiverSevenA pair).1
    exact
      selectedClassGauge59_eq_zero_of_canonicalModeFortyFourReadout_eq_zero
        K pair seated rank_one readout_ne_zero readout_zero
  · intro sevenA
    apply pointwise.mpr
    rw [irregularPrimalClassGauge59_projectedFermatPrimalTest59_eq_selected
      pair seated]
    rw [(selectedClassGauge59_eq_zero_iff_vandiverSevenA pair).2 sevenA,
      map_zero]

/-! ## Kernel-trust and route-separation audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAConditionalClosure59.irregularPrimalClassGauge59_projectedFermatPrimalTest59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms irregularPrimalClassGauge59_projectedFermatPrimalTest59

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAConditionalClosure59.irregularPrimalClassGauge59_projectedFermatPrimalTest59_eq_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms irregularPrimalClassGauge59_projectedFermatPrimalTest59_eq_selected

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAConditionalClosure59.dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA

/- The projected gauge computation must consume the proved naturality of
the strict Selmer class map under the actual chi=15 projector. -/
#guard_depends_on
  irregularPrimalClassGauge59_projectedFermatPrimalTest59,
  FermatFactorClassGaugeCharacterBoundary59.cyclotomicClassProjector59_selectedClassGauge59_eq_projectedSelmerClass

/- Explicit class seating is the only step identifying the projected class
with the selected relation-7A class. -/
#guard_depends_on
  irregularPrimalClassGauge59_projectedFermatPrimalTest59_eq_selected,
  irregularPrimalClassGauge59_projectedFermatPrimalTest59

/- The endpoint crosses the exact Dwork--Artin balance proved upstream. -/
#guard_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA,
  DworkSevenAArtinBalance59.dworkLambdaBoundary_apply_eq_zero_iff_classGaugeReadout_apply_eq_zero

/- Pointwise faithfulness on the actual rank-one irregular class line is
the visible route from zero readout back to zero selected class. -/
#guard_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA,
  CanonicalModeFortyFourCharacterLine827.selectedClassGauge59_eq_zero_of_canonicalModeFortyFourReadout_eq_zero

/- The final relation-7A conversion is the already proved selected-class
endpoint, not an independently reconstructed Vandiver argument. -/
#guard_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA,
  UlamReadout827.selectedClassGauge59_eq_zero_iff_vandiverSevenA

/- This conditional theorem accepts its Dwork lift explicitly; it does not
select one through the existential Poitou--Tate/unit-comparison constructor. -/
#guard_not_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA,
  DworkSeatedLambdaMeter59.nonempty_dworkSeatedLambdaLift827_of_pt_and_unitComparison

/- The endpoint does not detour through the later Fourier-character-line
relation-7A closure. -/
#guard_not_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA,
  CanonicalModeFortyFourCharacterLine827.fourierCoefficient_fermatFactor_eq_zero_iff_vandiverSevenA_of_canonicalCharacterLine

/- Nor does it close through the older strict-tame Artin endpoint. -/
#guard_not_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA,
  SevenAArtinPartialClosure59.strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA

end Fermat.FiftyNine.Conservation.DworkSevenAConditionalClosure59
