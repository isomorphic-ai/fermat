/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Functoriality of actual continuous H² pullback at 59

The descended low-degree pullback is contravariantly functorial: pullback
along the identity is the identity, and pullback along a composite is the
composite of pullbacks in reverse order.  The proof uses the surjectivity of
the honest cycle-to-homology projection, so these are equalities on all of
Mathlib's actual continuous second cohomology, not only on selected cycle
representatives.
-/
import Fermat.Experiments.Conservation.ContinuousH2Pullback59

noncomputable section

open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.ContinuousH2PullbackFunctorial59

open Fermat.Conservation.ContinuousHomogeneousPullback59
open Fermat.Conservation.ContinuousH2Pullback59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable {G H J : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]

theorem pullbackCycleTwo_id (z : Cycle (coefficients G) 2 3) :
    pullbackCycleTwo (ContinuousMonoidHom.id G) z = z := by
  apply Cycle.ext
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  rfl

theorem pullbackCycleTwo_comp
    (phi : G →ₜ* H) (psi : H →ₜ* J)
    (z : Cycle (coefficients J) 2 3) :
    pullbackCycleTwo (psi.comp phi) z =
      pullbackCycleTwo phi (pullbackCycleTwo psi z) := by
  apply Cycle.ext
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  rfl

/-- Every actual continuous `H²` class has a nominal closed representative. -/
theorem exists_cycle_representation
    (x : (continuousCohomology (ZMod 59) G 2).obj (coefficients G)) :
    ∃ z : Cycle (coefficients G) 2 3,
      homologyLinearEquiv (coefficients G) 2
        (h2Projection (coefficients G) z) = x := by
  obtain ⟨z, hz⟩ := sourceH2Projection_surjective
    ((homologyLinearEquiv (coefficients G) 2).symm x)
  refine ⟨z, ?_⟩
  rw [hz]
  simp

/-- Pullback along the identity is the identity on actual continuous
second cohomology. -/
theorem pullbackActualContinuousH2_id :
    pullbackActualContinuousH2 (ContinuousMonoidHom.id G) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := exists_cycle_representation x
  rw [pullbackActualContinuousH2_cycle, pullbackCycleTwo_id]
  rfl

/-- Contravariant composition law for actual continuous `H²` pullback. -/
theorem pullbackActualContinuousH2_comp
    (phi : G →ₜ* H) (psi : H →ₜ* J) :
    pullbackActualContinuousH2 (psi.comp phi) =
      (pullbackActualContinuousH2 phi).comp
        (pullbackActualContinuousH2 psi) := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := exists_cycle_representation x
  rw [pullbackActualContinuousH2_cycle]
  rw [LinearMap.comp_apply]
  rw [pullbackActualContinuousH2_cycle]
  rw [pullbackActualContinuousH2_cycle]
  rw [pullbackCycleTwo_comp]

end Fermat.Conservation.ContinuousH2PullbackFunctorial59
