/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Vanishing of the continuous carry class is exactly cyclic liftability

The explicit pulled carry cycle was already proved to be a boundary exactly
when its quotient character lifts through `C_(59^2)`.  This module carries
that statement through Mathlib's actual continuous-homology quotient.  Thus
the retained continuous `H²` class vanishes exactly when the lift exists.

This is an unconditional cohomological criterion.  It neither constructs a
local invariant nor identifies this class with a Hilbert-symbol scalar.
-/
import Fermat.Experiments.Conservation.ContinuousCarryLiftObstruction59

noncomputable section

namespace Fermat.Conservation.ContinuousCarryH2LiftCriterion59

open ContinuousCohomology
open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.ContinuousHomogeneousPullback59
open Fermat.Conservation.ContinuousKummerTateCup.Nominal
open Fermat.Conservation.FiniteCyclicH2Generator59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual pulled continuous carry class vanishes exactly when its
character admits a continuous lift from `C_59` to `C_(59²)`. -/
theorem pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift
    (chi : G →ₜ* CyclicGroup59) :
    pulledCarryH2Class59 chi = 0 ↔
      ∃ psi : G →ₜ* CyclicGroup59Squared,
        reduction59.comp psi = chi := by
  rw [← pulledCarryCycle59_boundary_iff_exists_continuous_lift chi]
  constructor
  · intro hzero
    have hprojection :
        h2Projection (coefficients G) (pulledCarryCycle59 chi) = 0 := by
      let e := homologyLinearEquiv (coefficients G) 2
      change e (h2Projection (coefficients G) (pulledCarryCycle59 chi)) = 0
        at hzero
      exact e.injective (hzero.trans e.map_zero.symm)
    exact (h2Projection_eq_zero_iff (coefficients G)
      (pulledCarryCycle59 chi)).mp hprojection
  · intro hboundary
    unfold pulledCarryH2Class59
    rw [(h2Projection_eq_zero_iff (coefficients G)
      (pulledCarryCycle59 chi)).mpr hboundary]
    exact map_zero _

/-- Negating the vanishing criterion identifies nonzero carry classes with
the genuine obstruction to a continuous `C_(59²)` lift. -/
theorem pulledCarryH2Class59_ne_zero_iff_noContinuousLift
    (chi : G →ₜ* CyclicGroup59) :
    pulledCarryH2Class59 chi ≠ 0 ↔ NoContinuousLift chi := by
  simpa [NoContinuousLift] using
    not_congr (pulledCarryH2Class59_eq_zero_iff_exists_continuous_lift chi)

end Fermat.Conservation.ContinuousCarryH2LiftCriterion59
