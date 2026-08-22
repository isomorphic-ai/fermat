/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Nonboundary witnesses for continuous second cohomology

This file isolates the smallest honest producer of a nonzero class in
Mathlib's actual continuous `H²`: an explicit closed homogeneous two-cochain
together with a proof that it is not a degree-one boundary.

It does not construct that arithmetic nonboundary witness, identify the
result with a local fundamental class, or assert a local invariant or
duality theorem.
-/
import Fermat.Experiments.Conservation.ContinuousKummerTateCupNominal

noncomputable section

namespace Fermat.Conservation.ContinuousH2Nonboundary

open CategoryTheory
open ContinuousCohomology
open ContinuousKummerTateCup.Nominal

universe u

variable {R G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (A : Action (TopModuleCat R) G)

/-- An explicit nominal continuous two-cycle which is not the differential
of any nominal degree-one cochain gives a nonzero class in Mathlib's actual
continuous second cohomology. -/
theorem exists_nonzero_actualContinuousH2_of_cycle_not_boundary
    (z : Cycle A 2 3)
    (hz : ¬ ∃ x : Cochain A 1,
      differential A 1 2 x = cycleCochain A 2 3 z) :
    ∃ c : (continuousCohomology R G 2).obj A, c ≠ 0 := by
  have hprojection : h2Projection A z ≠ 0 := by
    intro hzero
    exact hz ((h2Projection_eq_zero_iff A z).mp hzero)
  refine ⟨homologyLinearEquiv A 2 (h2Projection A z), ?_⟩
  intro hzero
  apply hprojection
  have hback := congrArg (fun q => (homologyLinearEquiv A 2).symm q) hzero
  exact hback.trans (homologyLinearEquiv A 2).symm.map_zero

end Fermat.Conservation.ContinuousH2Nonboundary
