/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The exact Dwork globalization obstruction for relation 7A

This file specializes the meter-parametric affine cokernel criterion to the
actual projected depth-44 Dwork meter.  The remaining global lifting input is
now one literal quotient class: at a fixed unit scale, a normalized Dwork
lift exists if and only if that class vanishes.

The conditional relation-7A closure is then restated with this obstruction
vanishing in place of a supplied lift or the much stronger full reverse
Poitou--Tate inclusion.  The normalized 827 point remains public, while the
constructed lift is consumed under an existential eliminator.
-/
import Fermat.Experiments.Conservation.GuardDependsOn
import Fermat.Exponents.FiftyNine.Conservation.DworkSevenAConditionalClosure59
import Fermat.Exponents.FiftyNine.Conservation.LambdaMeterAffineUnitOrbit827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Fermat.FiftyNine.Conservation.DworkSevenAAffineObstruction59

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TatePairing
open CanonicalFullOrbitLocalPairing827
open CanonicalIrregularMode827
open CanonicalModeFortyFourCharacterLine827
open CanonicalModeFortyFourClassFactorization827
open CharacterLinePointwiseFaithfulness59
open CyclotomicSelmerAction59
open CyclotomicSelmerClassNaturality59
open DetectorWitness827
open DworkSeatedLambdaMeter59
open DworkSevenAConditionalClosure59
open ExplicitTameOrbitReciprocity827
open LambdaMeterAffineCokernel827
open LambdaMeterAffineUnitOrbit827
open LambdaMeterPointedPoitouTate827
open LambdaOrbitAffineCokernel827
open PointedTateIncidence
open SplitPrimeFourier827
open StateFactorPair
open UlamReadout827

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

/-! ## The literal Dwork obstruction -/

/-- The affine cokernel obstruction for the actual seated depth-44 Dwork
meter at one retained unit scale. -/
noncomputable def dworkScaledLambdaObstructionClass827
    (scale : ZMod 59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    W1LambdaCokernel827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  scaledLambdaMeterObstructionClass827 (K := K)
    (dworkSeatedLambdaMeterFortyFour59 (K := K)) scale y₀

/-- The Dwork obstruction inherits the proved independence of the retained
normalized 827 basepoint. -/
theorem dworkScaledLambdaObstructionClass827_eq
    (scale : ZMod 59)
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    dworkScaledLambdaObstructionClass827 (K := K) scale y₀ =
      dworkScaledLambdaObstructionClass827 (K := K) scale y₁ :=
  scaledLambdaMeterObstructionClass827_eq
    (dworkSeatedLambdaMeterFortyFour59 (K := K)) scale y₀ y₁

/-- **Exact fixed-scale Dwork globalization criterion.**  An actual
normalized Dwork lift with prescribed unit scale exists precisely when the
corresponding quotient obstruction vanishes. -/
theorem exists_dworkSeatedLambdaLift827_with_scale_iff
    (scale : (ZMod 59)ˣ)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    (∃ lift : DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K),
        lift.wildScale = scale) ↔
      dworkScaledLambdaObstructionClass827 (K := K)
        (scale : ZMod 59) y₀ = 0 :=
  exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff
    (dworkSeatedLambdaMeterFortyFour59 (K := K)) scale y₀

/-- With the unit normalization allowed to vary, nonemptiness of the actual
Dwork lift fiber is exactly existence of one vanishing scaled obstruction. -/
theorem nonempty_dworkSeatedLambdaLift827_iff_exists_scale_obstruction_eq_zero
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)) ↔
      ∃ scale : (ZMod 59)ˣ,
        dworkScaledLambdaObstructionClass827 (K := K)
          (scale : ZMod 59) y₀ = 0 :=
  nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_exists_scale
    (dworkSeatedLambdaMeterFortyFour59 (K := K)) y₀

/-! ## The same obstruction as one unit-orbit equation -/

/-- The actual depth-44 Dwork meter retained in the exact W1 lambda
cokernel. -/
noncomputable def dworkLambdaMeterCokernelClass827 :
    W1LambdaCokernel827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  lambdaMeterCokernelClass827 (K := K)
    (dworkSeatedLambdaMeterFortyFour59 (K := K))

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The Dwork obstruction is literally the difference between the scaled
Dwork meter coset and the normalized complete-`827` coset. -/
theorem dworkScaledLambdaObstructionClass827_eq_smul_sub_normalized
    (scale : ZMod 59)
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    dworkScaledLambdaObstructionClass827 (K := K) scale y₀ =
      scale • dworkLambdaMeterCokernelClass827 (K := K) -
        normalizedW3LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀ := by
  exact
    scaledLambdaMeterObstructionClass827_eq_smul_sub_normalized
      (dworkSeatedLambdaMeterFortyFour59 (K := K)) scale y₀

/-- The concrete normalized Dwork lift fiber is nonempty exactly when the
normalized `827` coset is in the unit orbit of the depth-44 Dwork meter
coset.  This exposes the note's single retained normalization freedom. -/
theorem nonempty_dworkSeatedLambdaLift827_iff_unitOrbit
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    Nonempty (DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)) ↔
      ∃ scale : (ZMod 59)ˣ,
        (scale : ZMod 59) •
            dworkLambdaMeterCokernelClass827 (K := K) =
          normalizedW3LambdaCoset827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59 y₀ := by
  exact
    nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit
      (dworkSeatedLambdaMeterFortyFour59 (K := K)) y₀

/-- A one-dimensional W1 lambda cokernel closes the Dwork globalization
problem as soon as the concrete Dwork-meter and normalized-827 cosets are
both nonzero. -/
theorem nonempty_dworkSeatedLambdaLift827_of_cokernel_finrank_one
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (hfinrank : Module.finrank (ZMod 59)
      (W1LambdaCokernel827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59) = 1)
    (hmeter : dworkLambdaMeterCokernelClass827 (K := K) ≠ 0)
    (hnormalized : normalizedW3LambdaCoset827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 y₀ ≠ 0) :
    Nonempty (DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)) := by
  exact
    nonempty_normalizedOrbitScaledLambdaMeterLift827_of_finrank_one
      (dworkSeatedLambdaMeterFortyFour59 (K := K)) y₀
      hfinrank hmeter hnormalized

/-! ## Relation-7A closure through the affine obstruction -/

/-- The projected Fermat test closes conditionally from the exact affine
globalization obstruction.  Compared with the previous endpoint, neither a
chosen Dwork lift nor full reverse PT exactness is an input. -/
theorem dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_affine
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (globalizes : ∃ scale : (ZMod 59)ˣ,
      dworkScaledLambdaObstructionClass827 (K := K)
        (scale : ZMod 59) y₀ = 0)
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
  have lift_nonempty :
      Nonempty (DworkSeatedNormalizedOrbitScaledLambdaLift827 (K := K)) :=
    (nonempty_dworkSeatedLambdaLift827_iff_exists_scale_obstruction_eq_zero
      (K := K) y₀).2 globalizes
  rcases lift_nonempty with ⟨lift⟩
  exact
    dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA
      (K := K) lift reciprocity pair seated rank_one readout_ne_zero

/-- The same conditional relation-7A closure with globalization stated in
its sharp unit-orbit form. -/
theorem dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_unitOrbit
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (globalizes : ∃ scale : (ZMod 59)ˣ,
      (scale : ZMod 59) • dworkLambdaMeterCokernelClass827 (K := K) =
        normalizedW3LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀)
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
  refine
    dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_affine
      (K := K) y₀ ?_ reciprocity pair seated rank_one readout_ne_zero
  obtain ⟨scale, hscale⟩ := globalizes
  refine ⟨scale, ?_⟩
  exact
    (scaledLambdaMeterObstructionClass827_eq_zero_iff_smul_eq_normalized
      (dworkSeatedLambdaMeterFortyFour59 (K := K))
      (scale : ZMod 59) y₀).2 hscale

/-- Under the note's one-dimensional-line hypotheses, the affine lift is
constructed internally and the projected Fermat test reaches relation 7A.
All remaining arithmetic inputs stay explicit. -/
theorem dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_cokernel_finrank_one
    (y₀ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (cokernel_rank_one : Module.finrank (ZMod 59)
      (W1LambdaCokernel827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59) = 1)
    (meter_ne_zero : dworkLambdaMeterCokernelClass827 (K := K) ≠ 0)
    (normalized_ne_zero : normalizedW3LambdaCoset827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 y₀ ≠ 0)
    (reciprocity : GlobalReciprocityLaw
      (canonicalFullOrbitLocalPairing827 K
        canonicalTeichmullerCharacter59 irregularCharacter59))
    (pair : StateLinkedIdealPair hZeta S hz)
    (seated :
      cyclotomicClassProjector59 K irregularCharacter59
          (selectedClassGauge59 pair) = selectedClassGauge59 pair)
    (class_rank_one : Module.finrank (ZMod 59)
      (irregularClassCharacterLine59 K) = 1)
    (readout_ne_zero :
      (canonicalModeFortyFourClassReadout827 K).comp
          (irregularClassCharacterLine59 K).subtype ≠ 0) :
    dworkSeatedLambdaPrimalBoundaryFunctional827 (K := K)
        (projectedFermatPrimalTest59 (K := K) pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  apply
    dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_unitOrbit
      (K := K) y₀
  · obtain ⟨scale, hscale, _⟩ :=
      existsUnique_unit_smul_lambdaMeterCokernelClass827_eq_normalized
        (dworkSeatedLambdaMeterFortyFour59 (K := K)) y₀
        cokernel_rank_one meter_ne_zero normalized_ne_zero
    exact ⟨scale, hscale⟩
  · exact reciprocity
  · exact seated
  · exact class_rank_one
  · exact readout_ne_zero

/-! ## Kernel-trust and route-separation audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAAffineObstruction59.exists_dworkSeatedLambdaLift827_with_scale_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exists_dworkSeatedLambdaLift827_with_scale_iff

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAAffineObstruction59.nonempty_dworkSeatedLambdaLift827_iff_exists_scale_obstruction_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms nonempty_dworkSeatedLambdaLift827_iff_exists_scale_obstruction_eq_zero

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAAffineObstruction59.dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_affine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_affine

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAAffineObstruction59.dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_unitOrbit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_unitOrbit

/--
info: 'Fermat.FiftyNine.Conservation.DworkSevenAAffineObstruction59.dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_cokernel_finrank_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_cokernel_finrank_one

#guard_depends_on
  exists_dworkSeatedLambdaLift827_with_scale_iff,
  LambdaMeterAffineCokernel827.exists_normalizedOrbitScaledLambdaMeterLift827_with_scale_iff

#guard_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_affine,
  nonempty_dworkSeatedLambdaLift827_iff_exists_scale_obstruction_eq_zero

#guard_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_affine,
  DworkSevenAConditionalClosure59.dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA

#guard_depends_on
  nonempty_dworkSeatedLambdaLift827_iff_unitOrbit,
  LambdaMeterAffineUnitOrbit827.nonempty_normalizedOrbitScaledLambdaMeterLift827_iff_unitOrbit

#guard_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_unitOrbit,
  LambdaMeterAffineUnitOrbit827.scaledLambdaMeterObstructionClass827_eq_zero_iff_smul_eq_normalized

#guard_depends_on
  nonempty_dworkSeatedLambdaLift827_of_cokernel_finrank_one,
  LambdaMeterAffineUnitOrbit827.nonempty_normalizedOrbitScaledLambdaMeterLift827_of_finrank_one

#guard_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_cokernel_finrank_one,
  LambdaMeterAffineUnitOrbit827.existsUnique_unit_smul_lambdaMeterCokernelClass827_eq_normalized

#guard_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_cokernel_finrank_one,
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_unitOrbit

/- The affine closure consumes neither the former full reverse-PT inclusion
nor its conditional lift constructor. -/
#guard_not_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_affine,
  LambdaMeterPointedPoitouTate827.lambdaMeterPointedLocalization827_range_eq_ker_iff_kernel_lifts

#guard_not_depends_on
  dworkLambdaBoundary_projectedFermatTest_eq_zero_iff_vandiverSevenA_of_affine,
  DworkSeatedLambdaMeter59.nonempty_dworkSeatedLambdaLift827_of_pt_and_unitComparison

end Fermat.FiftyNine.Conservation.DworkSevenAAffineObstruction59
