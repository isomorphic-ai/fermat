/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Actual continuous H² pullback at 59

The low-degree cochain layer already precomposes continuous homogeneous
cochains along a continuous group homomorphism.  This module proves that the
cycle map kills the kernel of the honest homology projection and therefore
descends it to Mathlib's actual continuous second cohomology.

For a cyclic character `chi : G → C_59`, the resulting map sends the
normalized finite carry class literally to the existing pulled carry class.
Consequently a target readout is normalized on that class as soon as its
composition with this genuine pullback equals the canonical finite-cyclic
readout.  This states the exact naturality equation required of a future
local invariant without postulating or supplying such an invariant.
-/
import Fermat.Experiments.Conservation.ContinuousCyclicH2Readout59
import Fermat.Experiments.Conservation.ContinuousCarryLiftObstruction59

noncomputable section

open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.ContinuousH2Pullback59

open Fermat.Conservation.ContinuousHomogeneousPullback59
open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.ContinuousCyclicH2Readout59
open Fermat.Conservation.CyclicCarryH2Class59
open Fermat.Conservation.FiniteCyclicH2Generator59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable {G H : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Simultaneous precomposition of continuous homogeneous two-cycles,
bundled as a linear map. -/
def pullbackCycleTwoLinear (phi : G →ₜ* H) :
    Cycle (coefficients H) 2 3 →ₗ[ZMod 59]
      Cycle (coefficients G) 2 3 where
  toFun := pullbackCycleTwo phi
  map_add' x y := by
    apply Cycle.ext
    apply Cochain.ext
    rfl
  map_smul' a x := by
    apply Cycle.ext
    apply Cochain.ext
    rfl

/-- Pull a source cycle back and project the result to honest target
continuous homology. -/
def pullbackCycleToH2 (phi : G →ₜ* H) :
    Cycle (coefficients H) 2 3 →ₗ[ZMod 59]
      Homology (coefficients G) 2 :=
  (h2Projection (coefficients G)).comp (pullbackCycleTwoLinear phi)

/-- A source homology-zero cycle remains zero after pullback. -/
theorem pullbackCycleToH2_eq_zero_of_h2Projection_eq_zero
    (phi : G →ₜ* H) (z : Cycle (coefficients H) 2 3)
    (hz : h2Projection (coefficients H) z = 0) :
    pullbackCycleToH2 phi z = 0 := by
  obtain ⟨b, hb⟩ := (h2Projection_eq_zero_iff (coefficients H) z).mp hz
  apply (h2Projection_eq_zero_iff
    (coefficients G) (pullbackCycleTwo phi z)).mpr
  exact pullbackCycleTwo_of_boundary phi z ⟨b, hb⟩

theorem ker_h2Projection_le_ker_pullbackCycleToH2 (phi : G →ₜ* H) :
    LinearMap.ker (h2Projection (coefficients H)) ≤
      LinearMap.ker (pullbackCycleToH2 phi) := by
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  exact pullbackCycleToH2_eq_zero_of_h2Projection_eq_zero phi z hz

theorem sourceH2Projection_surjective :
    Function.Surjective (h2Projection (coefficients H)) :=
  cycleToHomology_surjective (coefficients H) 2 3
    ((ComplexShape.up ℕ).next_eq' (by simp))

/-- The cochain pullback descended through the genuine source homology
quotient. -/
noncomputable def pullbackHomologyTwo (phi : G →ₜ* H) :
    Homology (coefficients H) 2 →ₗ[ZMod 59]
      Homology (coefficients G) 2 :=
  ((LinearMap.ker (h2Projection (coefficients H))).liftQ
      (pullbackCycleToH2 phi)
      (ker_h2Projection_le_ker_pullbackCycleToH2 phi)).comp
    ((h2Projection (coefficients H)).quotKerEquivOfSurjective
      sourceH2Projection_surjective).symm.toLinearMap

/-- The descended map is computed by literal cochain pullback on every
closed representative. -/
@[simp]
theorem pullbackHomologyTwo_h2Projection
    (phi : G →ₜ* H) (z : Cycle (coefficients H) 2 3) :
    pullbackHomologyTwo phi (h2Projection (coefficients H) z) =
      h2Projection (coefficients G) (pullbackCycleTwo phi z) := by
  change ((LinearMap.ker (h2Projection (coefficients H))).liftQ
      (pullbackCycleToH2 phi)
      (ker_h2Projection_le_ker_pullbackCycleToH2 phi))
    (((h2Projection (coefficients H)).quotKerEquivOfSurjective
      sourceH2Projection_surjective).symm
        (h2Projection (coefficients H) z)) = _
  rw [(h2Projection (coefficients H)).quotKerEquivOfSurjective_symm_apply]
  exact Submodule.liftQ_apply _ _ _

/-- Actual contravariant pullback on Mathlib's exposed continuous
second-cohomology objects with trivial `F_59` coefficients. -/
noncomputable def pullbackActualContinuousH2 (phi : G →ₜ* H) :
    (continuousCohomology (ZMod 59) H 2).obj (coefficients H) →ₗ[ZMod 59]
      (continuousCohomology (ZMod 59) G 2).obj (coefficients G) :=
  (homologyLinearEquiv (coefficients G) 2).toLinearMap.comp
    ((pullbackHomologyTwo phi).comp
      (homologyLinearEquiv (coefficients H) 2).symm.toLinearMap)

@[simp]
theorem pullbackActualContinuousH2_cycle
    (phi : G →ₜ* H) (z : Cycle (coefficients H) 2 3) :
    pullbackActualContinuousH2 phi
        (homologyLinearEquiv (coefficients H) 2
          (h2Projection (coefficients H) z)) =
      homologyLinearEquiv (coefficients G) 2
        (h2Projection (coefficients G) (pullbackCycleTwo phi z)) := by
  change homologyLinearEquiv (coefficients G) 2
      (pullbackHomologyTwo phi (h2Projection (coefficients H) z)) = _
  rw [pullbackHomologyTwo_h2Projection]

/-- The actual pulled carry class is literally the pullback of the normalized
finite cyclic carry class. -/
@[simp]
theorem pullbackActualContinuousH2_continuousCarryH2Class59
    (chi : G →ₜ* CyclicGroup59) :
    pullbackActualContinuousH2 chi continuousCarryH2Class59 =
      pulledCarryH2Class59 chi := by
  exact pullbackActualContinuousH2_cycle chi continuousCarryCycle59

/-- Any scalar readout on the target which restricts along pullback to the
normalized finite-cyclic readout necessarily assigns value one to the
pulled carry class.  This is the exact naturality equation a local invariant
comparison must prove. -/
theorem readout_pulledCarryH2Class59_eq_one_of_normalized_pullback
    (chi : G →ₜ* CyclicGroup59)
    (readout :
      (continuousCohomology (ZMod 59) G 2).obj (coefficients G) →ₗ[ZMod 59]
        ZMod 59)
    (hnormalized :
      readout.comp (pullbackActualContinuousH2 chi) =
        actualContinuousCyclicH2Readout59) :
    readout (pulledCarryH2Class59 chi) = 1 := by
  rw [← pullbackActualContinuousH2_continuousCarryH2Class59 chi]
  change (readout.comp (pullbackActualContinuousH2 chi))
      continuousCarryH2Class59 = 1
  rw [hnormalized]
  exact actualContinuousCyclicH2Readout59_continuousCarryH2Class59

end Fermat.Conservation.ContinuousH2Pullback59
