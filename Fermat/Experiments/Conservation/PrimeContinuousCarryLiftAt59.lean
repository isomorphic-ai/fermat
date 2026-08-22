/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The prime-parametric pullback and carry-lift stack specializes at 59

The existing `59`-specific low-degree pullback, cyclic-square extension,
pulled carry class, and explicit lift primitives are definitionally the
`p = 59` specialization of the generic construction.  This file records
that compatibility without changing the original modules.
-/
import Fermat.Experiments.Conservation.PrimeContinuousCarryLift
import Fermat.Experiments.Conservation.ContinuousCarryH2LiftCriterion59

noncomputable section

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.PrimeContinuousCarryLiftAt59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable {G H : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem coefficients_eq_59 :
    PrimeContinuousHomogeneousPullback.coefficients 59 G =
      ContinuousHomogeneousPullback59.coefficients G := rfl

theorem pullbackOne_eq_59 (phi : G →ₜ* H) :
    PrimeContinuousHomogeneousPullback.pullbackOne 59 phi =
      ContinuousHomogeneousPullback59.pullbackOne phi := rfl

theorem pullbackTwo_eq_59 (phi : G →ₜ* H) :
    PrimeContinuousHomogeneousPullback.pullbackTwo 59 phi =
      ContinuousHomogeneousPullback59.pullbackTwo phi := rfl

theorem pullbackCycleTwo_eq_59 (phi : G →ₜ* H) :
    PrimeContinuousHomogeneousPullback.pullbackCycleTwo 59 phi =
      ContinuousHomogeneousPullback59.pullbackCycleTwo phi := rfl

theorem reduction_eq_59 :
    PrimeCyclicExtension.reduction 59 =
      ContinuousCarryLiftObstruction59.reduction59 := rfl

theorem standardSection_eq_59 :
    PrimeCyclicExtension.standardSection 59 =
      ContinuousCarryLiftObstruction59.standardSection59 := rfl

theorem kernelEmbed_eq_59 :
    PrimeCyclicExtension.kernelEmbed 59 =
      ContinuousCarryLiftObstruction59.kernelEmbed59 := rfl

theorem pulledCarryCycle_eq_59
    (chi : G →ₜ* PrimeCyclicExtension.CyclicGroup 59) :
    PrimeContinuousCarryLift.pulledCarryCycle chi =
      ContinuousCarryLiftObstruction59.pulledCarryCycle59 chi := rfl

omit [IsTopologicalGroup G] in
theorem noContinuousLift_eq_59
    (chi : G →ₜ* PrimeCyclicExtension.CyclicGroup 59) :
    PrimeContinuousCarryLift.NoContinuousLift chi =
      ContinuousCarryLiftObstruction59.NoContinuousLift chi := rfl

theorem pulledCarryH2Class_eq_59
    (chi : G →ₜ* PrimeCyclicExtension.CyclicGroup 59) :
    PrimeContinuousCarryLift.pulledCarryH2Class chi =
      ContinuousCarryLiftObstruction59.pulledCarryH2Class59 chi := rfl

omit [IsTopologicalGroup G] in
theorem liftCorrection_eq_59
    (chi : G →ₜ* PrimeCyclicExtension.CyclicGroup 59)
    (psi : G →ₜ* PrimeCyclicExtension.CyclicGroupSquared 59) :
    PrimeContinuousCarryLift.liftCorrection chi psi =
      ContinuousCarryLiftObstruction59.liftCorrection59 chi psi := rfl

theorem liftPrimitive_eq_59
    (chi : G →ₜ* PrimeCyclicExtension.CyclicGroup 59)
    (psi : G →ₜ* PrimeCyclicExtension.CyclicGroupSquared 59) :
    PrimeContinuousCarryLift.liftPrimitive chi psi =
      ContinuousCarryLiftObstruction59.liftPrimitive59 chi psi := rfl

/-- The old actual-`H²` criterion is directly the generic theorem at 59. -/
theorem pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift
    (chi : G →ₜ* PrimeCyclicExtension.CyclicGroup 59) :
    ContinuousCarryLiftObstruction59.pulledCarryH2Class59 chi = 0 ↔
      ∃ psi : G →ₜ* PrimeCyclicExtension.CyclicGroupSquared 59,
        ContinuousCarryLiftObstruction59.reduction59.comp psi = chi :=
  PrimeContinuousCarryLift.pulledCarryH2Class_eq_zero_iff_exists_continuous_lift
    chi

end Fermat.Conservation.PrimeContinuousCarryLiftAt59
