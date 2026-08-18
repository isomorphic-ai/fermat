/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Continuous Kummer--Tate structural verification

This non-imported audit leaf checks the public construction receipts exposed
by the continuous Kummer map, its primitive-root orientation, the raw
Alexander--Whitney cup, its two-sided descent to genuine continuous
cohomology, and the typed coefficient algebra.

The endpoint deliberately remains `H^2`-valued.  The generic cup is now
constructed internally rather than supplied by a caller.  This file still
does not assert the normalized local `H^2` readout, a Hilbert-symbol
comparison, Tate-duality theorem, or global reflected lift.
-/
import Fermat.Conservation.ContinuousKummerTateAlgebra
import Fermat.Conservation.ContinuousKummerTateCup

/-! ## Genuine continuous Kummer `H^1` -/

#check Fermat.Conservation.ContinuousKummerH1.ContinuousCrossedHom
#check Fermat.Conservation.ContinuousKummerH1.homogeneousOneCochain_isCycle
#check Fermat.Conservation.ContinuousKummerH1.ContinuousCrossedHom.homogeneousOneClass_eq_zero_of_principal
#check Fermat.Conservation.ContinuousKummerH1.homogeneousOneClass_add
#check Fermat.Conservation.ContinuousKummerH1.homogeneousOneClass_sub
#check Fermat.Conservation.ContinuousKummerH1.continuousClassOfUnit_one
#check Fermat.Conservation.ContinuousKummerH1.continuousClassOfUnit_mul
#check Fermat.Conservation.ContinuousKummerH1.continuousClassOfUnit_pow_n
#check Fermat.Conservation.ContinuousKummerH1.continuousMap
#check Fermat.Conservation.ContinuousKummerH1.continuousMap_classOfUnit

/-! ## Primitive-root orientation with distinct left and right seats -/

#check Fermat.Conservation.ContinuousKummerOrientation.trivialTopLine
#check Fermat.Conservation.ContinuousKummerOrientation.coordinateContinuousLinearEquiv
#check Fermat.Conservation.ContinuousKummerOrientation.rootsTopRepresentationEquivTrivial
#check Fermat.Conservation.ContinuousKummerOrientation.OrientedContinuousH1
#check Fermat.Conservation.ContinuousKummerOrientation.OrientedContinuousH2
#check Fermat.Conservation.ContinuousKummerOrientation.orientH1
#check Fermat.Conservation.ContinuousKummerOrientation.orientH1Equiv
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2Equiv
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2Equiv_apply
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv_apply
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv_symm_apply
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv_apply
#check Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv_symm_apply
#check Fermat.Conservation.ContinuousKummerOrientation.rightKummerMap
#check Fermat.Conservation.ContinuousKummerOrientation.rightKummerMap_classOfUnit
#check Fermat.Conservation.ContinuousKummerOrientation.leftKummerMap
#check Fermat.Conservation.ContinuousKummerOrientation.leftKummerMap_classOfUnit

/-! ## Raw continuous Alexander--Whitney cup -/

#check Fermat.Conservation.ContinuousKummerTateCupRaw.ContinuousEquivariantPairing
#check Fermat.Conservation.ContinuousKummerTateCupRaw.rawCup
#check Fermat.Conservation.ContinuousKummerTateCupRaw.rawCup_apply
#check Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain
#check Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_apply
#check Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_isCycle
#check Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochainLinear
#check Fermat.Conservation.ContinuousKummerTateCupRaw.cupZeroOne
#check Fermat.Conservation.ContinuousKummerTateCupRaw.cupOneZeroNegative
#check Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_zeroBoundary_left
#check Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_zeroBoundary_right

/-! ## Genuine categorical cycles -/

#check Fermat.Conservation.ContinuousKummerTateCup.cokernelProjection_surjective
#check Fermat.Conservation.ContinuousKummerTateCup.cokernelProjection_eq_zero_iff
#check Fermat.Conservation.ContinuousKummerTateCup.homologyProjection_surjective
#check Fermat.Conservation.ContinuousKummerTateCup.homologyProjection_eq_zero_iff_range_toCycles
#check Fermat.Conservation.ContinuousKummerTateCup.cyclesInclusion_injective
#check Fermat.Conservation.ContinuousKummerTateCup.concreteKernelToCycles
#check Fermat.Conservation.ContinuousKummerTateCup.concreteKernelToCycles_i
#check Fermat.Conservation.ContinuousKummerTateCup.oneCycleCochain
#check Fermat.Conservation.ContinuousKummerTateCup.oneCycleCochain_isCycle
#check Fermat.Conservation.ContinuousKummerTateCup.oneCycleCochain_toCycles
#check Fermat.Conservation.ContinuousKummerTateCup.cupKernel
#check Fermat.Conservation.ContinuousKummerTateCup.twoKernelToCycles
#check Fermat.Conservation.ContinuousKummerTateCup.cupCycle

/-! ## Nominal two-sided descent and genuine continuous cohomology -/

#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.Cochain
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.Cycle
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.cycleConcreteLinearEquiv
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.Homology
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.homologyLinearEquiv
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.h1Projection
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.h1Projection_surjective
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.h1Projection_eq_zero_iff
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.h2Projection_eq_zero_iff
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCycleCupToH2
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCycleCupToH2_kills_left
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCycleCupToH2_kills_right
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCupH1
#check Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCupH1_projection
#check Fermat.Conservation.ContinuousKummerTateCup.transportBilinear
#check Fermat.Conservation.ContinuousKummerTateCup.cupH1
#check Fermat.Conservation.ContinuousKummerTateCup.cupH1_homologyLinearEquiv
#check Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection

/-! ## Typed coefficient algebra and retained `H^2` output -/

#check Fermat.Conservation.ContinuousKummerTateAlgebra.scalarTimesRootPairing
#check Fermat.Conservation.ContinuousKummerTateAlgebra.scalarTimesRootPairing_apply
#check Fermat.Conservation.ContinuousKummerTateAlgebra.ContinuousKummerCohomologyTwo
#check Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairingFromCup
#check Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairingFromCup_apply
#check Fermat.Conservation.ContinuousKummerTateAlgebra.kummerCupH1
#check Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairing
#check Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairing_apply

/-! ## Axiom budgets

The representative public receipts below may use quotient soundness,
propositional extensionality, and classical choice through Mathlib's
categorical homology construction.  The guarded output prevents any new
mathematical axiom from entering this layer unnoticed.
-/

/--
info: 'Fermat.Conservation.ContinuousKummerH1.ContinuousCrossedHom.homogeneousOneClass_eq_zero_of_principal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerH1.ContinuousCrossedHom.homogeneousOneClass_eq_zero_of_principal

/--
info: 'Fermat.Conservation.ContinuousKummerH1.continuousClassOfUnit_pow_n' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerH1.continuousClassOfUnit_pow_n

/--
info: 'Fermat.Conservation.ContinuousKummerH1.continuousMap_classOfUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerH1.continuousMap_classOfUnit

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.orientH2Equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.orientH2Equiv

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.orientH2Equiv_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.orientH2Equiv_apply

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv_apply

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv_symm_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.orientH2ReadoutEquiv_symm_apply

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv_apply

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv_symm_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.orientH2ContinuousReadoutEquiv_symm_apply

/--
info: 'Fermat.Conservation.ContinuousKummerOrientation.leftKummerMap_classOfUnit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerOrientation.leftKummerMap_classOfUnit

/--
info: 'Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_isCycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_isCycle

/--
info: 'Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_zeroBoundary_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_zeroBoundary_left

/--
info: 'Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_zeroBoundary_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCupRaw.cupCochain_zeroBoundary_right

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.concreteKernelToCycles_i' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.concreteKernelToCycles_i

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.oneCycleCochain_toCycles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.oneCycleCochain_toCycles

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.cupCycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.cupCycle

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCycleCupToH2_kills_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCycleCupToH2_kills_left

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCycleCupToH2_kills_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCycleCupToH2_kills_right

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCupH1_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.Nominal.nominalCupH1_projection

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.cupH1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.cupH1

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.cupH1_homologyLinearEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.cupH1_homologyLinearEquiv

/--
info: 'Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection

/--
info: 'Fermat.Conservation.ContinuousKummerTateAlgebra.scalarTimesRootPairing_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateAlgebra.scalarTimesRootPairing_apply

/--
info: 'Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairingFromCup_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairingFromCup_apply

/--
info: 'Fermat.Conservation.ContinuousKummerTateAlgebra.kummerCupH1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateAlgebra.kummerCupH1

/--
info: 'Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairing

/--
info: 'Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairing_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairing_apply
