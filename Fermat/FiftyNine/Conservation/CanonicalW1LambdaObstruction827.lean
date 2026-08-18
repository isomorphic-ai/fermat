/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The point-free canonical W1 lambda obstruction

The canonical `(59, 44)` normalized W3 fiber is already known to be
nonempty.  We use that theorem once, privately, to choose a basepoint.  The
basepoint-independence theorem for the affine cokernel then exposes a named
obstruction class whose public type and exact vanishing criterion contain no
chosen point.

This module does not prove that the obstruction vanishes and does not assert
a Poitou--Tate lift.
-/
import Fermat.FiftyNine.Conservation.LambdaOrbitAffineCokernel827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.CanonicalW1LambdaObstruction827

open Fermat.Conservation
open CanonicalConjugatePairIncidence827
open CanonicalIrregularMode827
open CyclotomicSelmerAction59
open DetectorWitness827
open ExplicitTameOrbitReciprocity827
open LambdaOrbitAffineCokernel827
open LambdaOrbitAffineKernelCriterion827
open LambdaOrbitLocalizationFiber827
open PointedTateIncidence
open SplitPrimeFourier827
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

noncomputable local instance instCanonicalQRelaxedReflectedDual827ModuleZMod :
    Module (ZMod 59)
      (QRelaxedReflectedDual827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59) :=
  AddCommGroup.zmodModule
    (qRelaxedReflectedDual827_nsmul_eq_zero
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59)

/-- A private implementation basepoint.  No public statement below depends
on which witness `Classical.choice` returns. -/
private noncomputable def chosenCanonicalNormalizedW3Point827 :
    NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)) :=
  Classical.choice
    (canonicalConjugatePairNormalizedReflectedFiber827_nonempty (K := K))

/-- The canonical normalized-W3 lambda coset.  Its implementation uses the
private point above, while the theorem below identifies it with the coset of
every normalized W3 point. -/
noncomputable def canonicalNormalizedW3LambdaCoset827 :
    W1LambdaCokernel827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  normalizedW3LambdaCoset827 (K := K)
    canonicalTeichmullerCharacter59 irregularCharacter59
    (chosenCanonicalNormalizedW3Point827 (K := K))

/-- The canonical W1 lambda obstruction in the literal cokernel of lambda
localization restricted to the full-orbit kernel.  No basepoint occurs in
its public type. -/
noncomputable def canonicalW1LambdaObstruction827 :
    W1LambdaCokernel827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  w1LambdaObstructionClass827 (K := K)
    canonicalTeichmullerCharacter59 irregularCharacter59
    (chosenCanonicalNormalizedW3Point827 (K := K))

/-- The named normalized W3 coset agrees with the coset computed from every
actual normalized W3 point. -/
theorem canonicalNormalizedW3LambdaCoset827_eq
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    canonicalNormalizedW3LambdaCoset827 (K := K) =
      normalizedW3LambdaCoset827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y := by
  exact normalizedW3LambdaCoset827_eq
    canonicalTeichmullerCharacter59 irregularCharacter59
    (chosenCanonicalNormalizedW3Point827 (K := K)) y

/-- The point-free canonical obstruction agrees with the obstruction
computed from every actual normalized W3 point. -/
theorem canonicalW1LambdaObstruction827_eq
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    canonicalW1LambdaObstruction827 (K := K) =
      w1LambdaObstructionClass827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y := by
  exact w1LambdaObstructionClass827_eq
    canonicalTeichmullerCharacter59 irregularCharacter59
    (chosenCanonicalNormalizedW3Point827 (K := K)) y

/-- The canonical obstruction is exactly the difference between W1's
prescribed quotient class and the point-free normalized W3 coset. -/
theorem canonicalW1LambdaObstruction827_eq_prescribed_sub_normalized :
    canonicalW1LambdaObstruction827 (K := K) =
      prescribedW1LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 -
        canonicalNormalizedW3LambdaCoset827 (K := K) := by
  exact w1LambdaObstructionClass827_eq_prescribed_sub_normalized
    canonicalTeichmullerCharacter59 irregularCharacter59
    (chosenCanonicalNormalizedW3Point827 (K := K))

/-- Point-free quotient formulation of the unresolved equality. -/
theorem prescribedW1LambdaCoset827_eq_canonicalNormalized_iff_obstruction_eq_zero :
    prescribedW1LambdaCoset827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 =
        canonicalNormalizedW3LambdaCoset827 (K := K) ↔
      canonicalW1LambdaObstruction827 (K := K) = 0 := by
  rw [canonicalW1LambdaObstruction827_eq_prescribed_sub_normalized]
  exact sub_eq_zero.symm

/-- The exact point-free W2 obstruction theorem.  The compatible fiber is
inhabited precisely when the canonical cokernel class vanishes; this theorem
does not establish either side. -/
theorem w1w3CompatibleFiber827_nonempty_iff_canonicalObstruction_eq_zero :
    Nonempty (W1W3CompatibleFiber827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59) ↔
      canonicalW1LambdaObstruction827 (K := K) = 0 := by
  exact w1w3CompatibleFiber827_nonempty_iff_obstruction_eq_zero
    canonicalTeichmullerCharacter59 irregularCharacter59
    (chosenCanonicalNormalizedW3Point827 (K := K))

/-- The same exact criterion stated as equality of the two intrinsic
cokernel cosets. -/
theorem w1w3CompatibleFiber827_nonempty_iff_prescribed_eq_canonicalNormalized :
    Nonempty (W1W3CompatibleFiber827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59) ↔
      prescribedW1LambdaCoset827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 =
        canonicalNormalizedW3LambdaCoset827 (K := K) := by
  rw [w1w3CompatibleFiber827_nonempty_iff_canonicalObstruction_eq_zero]
  exact
    prescribedW1LambdaCoset827_eq_canonicalNormalized_iff_obstruction_eq_zero.symm

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1LambdaObstruction827.canonicalW1LambdaObstruction827_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms canonicalW1LambdaObstruction827_eq

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1LambdaObstruction827.w1w3CompatibleFiber827_nonempty_iff_canonicalObstruction_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  w1w3CompatibleFiber827_nonempty_iff_canonicalObstruction_eq_zero

end Fermat.FiftyNine.Conservation.CanonicalW1LambdaObstruction827
