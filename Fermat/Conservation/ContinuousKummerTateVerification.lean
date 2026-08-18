/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Continuous Kummer--Tate structural verification

This non-imported audit leaf checks the public construction receipts exposed
by the continuous Kummer map, its primitive-root orientation, the raw
Alexander--Whitney cup, the passage to genuine categorical cycles, and the
typed coefficient algebra.

The endpoint deliberately remains an `H^2`-valued adapter taking a descended
cup product as an input.  This file does not assert a local invariant,
Hilbert-symbol comparison, Tate-duality theorem, or global reflected lift.
-/
import Fermat.Conservation.ContinuousKummerTateAlgebra
import Fermat.Conservation.ContinuousKummerTateCupCycles

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

/-! ## Typed coefficient algebra and retained `H^2` output -/

#check Fermat.Conservation.ContinuousKummerTateAlgebra.scalarTimesRootPairing
#check Fermat.Conservation.ContinuousKummerTateAlgebra.scalarTimesRootPairing_apply
#check Fermat.Conservation.ContinuousKummerTateAlgebra.ContinuousKummerCohomologyTwo
#check Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairingFromCup
#check Fermat.Conservation.ContinuousKummerTateAlgebra.kummerPairingFromCup_apply

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
