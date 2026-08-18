/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The dual boundary of the canonical W1 lambda obstruction

The remaining W2 cokernel class can be read by every linear functional that
annihilates the lambda image of full-orbit-invisible adjustments.  This file
packages all such readings as one point-free canonical boundary functional.

Mathlib's dual-annihilator separation theorem proves that this entire
boundary vanishes exactly when the canonical cokernel obstruction vanishes.
No vanishing, lift, or Poitou--Tate assertion is added.
-/
import Fermat.FiftyNine.Conservation.CanonicalW1LambdaObstruction827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Fermat.FiftyNine.Conservation.CanonicalW1LambdaBoundary827

open Fermat.Conservation
open CanonicalConjugatePairIncidence827
open CanonicalIrregularMode827
open CanonicalW1LambdaObstruction827
open ContinuousKummerTateLocalization59
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

/-- The complete test space: all linear functionals on the lambda-local
`H¹` seat which annihilate the lambda image of every full-orbit-invisible
adjustment. -/
abbrev CanonicalW1LambdaBoundaryTestSpace827 :=
  (LinearMap.range
    (lambdaOnFullOrbitKernel827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59)).dualAnnihilator

/-- Evaluation of every lawful boundary test on the W1-minus-W3 correction
computed from one normalized W3 point. -/
def w1LambdaBoundaryAt827
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    Module.Dual (ZMod 59)
      (CanonicalW1LambdaBoundaryTestSpace827 (K := K)) where
  toFun phi := phi.1
    (w1LambdaCorrection827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 y)
  map_add' phi psi := by simp
  map_smul' a phi := by simp

@[simp]
theorem w1LambdaBoundaryAt827_apply
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (phi : CanonicalW1LambdaBoundaryTestSpace827 (K := K)) :
    w1LambdaBoundaryAt827 (K := K) y phi =
      phi.1 (w1LambdaCorrection827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y) :=
  rfl

/-- The full dual boundary is independent of the normalized W3 point used
to compute the affine correction. -/
theorem w1LambdaBoundaryAt827_eq
    (y₀ y₁ : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    w1LambdaBoundaryAt827 (K := K) y₀ =
      w1LambdaBoundaryAt827 (K := K) y₁ := by
  apply LinearMap.ext
  intro phi
  have hquotient :
      w1LambdaObstructionClass827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀ =
        w1LambdaObstructionClass827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₁ :=
    w1LambdaObstructionClass827_eq
      canonicalTeichmullerCharacter59 irregularCharacter59 y₀ y₁
  have hmem :
      w1LambdaCorrection827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₀ -
        w1LambdaCorrection827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59 y₁ ∈
        LinearMap.range
          (lambdaOnFullOrbitKernel827 (K := K)
            canonicalTeichmullerCharacter59 irregularCharacter59) := by
    exact (Submodule.Quotient.eq
      (LinearMap.range
        (lambdaOnFullOrbitKernel827 (K := K)
          canonicalTeichmullerCharacter59 irregularCharacter59))).mp
      hquotient
  have hzero :=
    (Submodule.mem_dualAnnihilator phi.1).mp phi.2 _ hmem
  change
    phi.1 (w1LambdaCorrection827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y₀) =
      phi.1 (w1LambdaCorrection827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y₁)
  rw [← sub_eq_zero, ← map_sub]
  exact hzero

/-- A private implementation point used only to define the point-free
boundary below.  Basepoint independence makes the choice observationally
irrelevant. -/
private noncomputable def chosenCanonicalBoundaryBasepoint827 :
    NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)) :=
  Classical.choice
    (canonicalConjugatePairNormalizedReflectedFiber827_nonempty (K := K))

/-- The point-free canonical boundary functional: every annihilating test
is evaluated on the retained W1-minus-W3 correction. -/
noncomputable def canonicalW1LambdaBoundary827 :
    Module.Dual (ZMod 59)
      (CanonicalW1LambdaBoundaryTestSpace827 (K := K)) :=
  w1LambdaBoundaryAt827 (K := K)
    (chosenCanonicalBoundaryBasepoint827 (K := K))

/-- The point-free boundary can be read using every actual normalized W3
point, without exposing the private implementation choice. -/
theorem canonicalW1LambdaBoundary827_eq
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K))) :
    canonicalW1LambdaBoundary827 (K := K) =
      w1LambdaBoundaryAt827 (K := K) y := by
  exact w1LambdaBoundaryAt827_eq
    (chosenCanonicalBoundaryBasepoint827 (K := K)) y

@[simp]
theorem canonicalW1LambdaBoundary827_apply
    (y : NormalizedReflectedFiber827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)))
    (phi : CanonicalW1LambdaBoundaryTestSpace827 (K := K)) :
    canonicalW1LambdaBoundary827 (K := K) phi =
      phi.1 (w1LambdaCorrection827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 y) := by
  rw [canonicalW1LambdaBoundary827_eq y]
  rfl

/-- Dual-annihilator separation: the point-free cokernel obstruction
vanishes exactly when every lawful scalar boundary test vanishes. -/
theorem canonicalW1LambdaObstruction827_eq_zero_iff_boundary_eq_zero :
    canonicalW1LambdaObstruction827 (K := K) = 0 ↔
      canonicalW1LambdaBoundary827 (K := K) = 0 := by
  let y := chosenCanonicalBoundaryBasepoint827 (K := K)
  rw [canonicalW1LambdaObstruction827_eq y,
    w1LambdaObstructionClass827_eq_zero_iff_mem_range]
  let W : Subspace (ZMod 59) (LambdaRootsContinuousH1 K) :=
    LinearMap.range
      (lambdaOnFullOrbitKernel827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59)
  let c : LambdaRootsContinuousH1 K :=
    w1LambdaCorrection827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59 y
  constructor
  · intro hc
    apply LinearMap.ext
    intro phi
    change phi.1 c = 0
    exact (Submodule.mem_dualAnnihilator phi.1).mp phi.2 c hc
  · intro hboundary
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W c).mp
    intro phi hphi
    have hvalue := LinearMap.congr_fun hboundary
      (⟨phi, hphi⟩ : W.dualAnnihilator)
    change phi c = 0
    exact hvalue

/-- The exact dual W2 boundary criterion.  The compatible fiber is inhabited
if and only if every functional annihilating the restricted lambda image
also annihilates the canonical W1-minus-W3 correction. -/
theorem w1w3CompatibleFiber827_nonempty_iff_canonicalBoundary_eq_zero :
    Nonempty (W1W3CompatibleFiber827 (K := K)
      canonicalTeichmullerCharacter59 irregularCharacter59) ↔
      canonicalW1LambdaBoundary827 (K := K) = 0 := by
  rw [w1w3CompatibleFiber827_nonempty_iff_canonicalObstruction_eq_zero,
    canonicalW1LambdaObstruction827_eq_zero_iff_boundary_eq_zero]

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1LambdaBoundary827.w1LambdaBoundaryAt827_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms w1LambdaBoundaryAt827_eq

/--
info: 'Fermat.FiftyNine.Conservation.CanonicalW1LambdaBoundary827.canonicalW1LambdaObstruction827_eq_zero_iff_boundary_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  canonicalW1LambdaObstruction827_eq_zero_iff_boundary_eq_zero

end Fermat.FiftyNine.Conservation.CanonicalW1LambdaBoundary827
