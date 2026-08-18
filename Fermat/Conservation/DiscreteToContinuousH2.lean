/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# From discrete group cohomology to continuous `H²`

For a discrete group and a discrete commutative coefficient ring with the
trivial action, every inhomogeneous cochain is continuous.  This file gives
the degree-two comparison needed by the conservation route explicitly:

* an inhomogeneous discrete two-cocycle `c` is sent to the homogeneous
  continuous cocycle `(x,y,z) ↦ c(x⁻¹y,y⁻¹z)`;
* if the resulting homogeneous cocycle were a continuous boundary, evaluating
  its primitive at `(1,g)` would make `c` a discrete boundary;
* consequently, any nonzero discrete `H²` class produces a nonzero class in
  Mathlib's actual continuous `H²`.

This is intentionally a trivial-coefficient, discrete-topology comparison.
It is not an inflation map along a group quotient.  For a nontrivial action,
the homogeneous formula needs an additional coefficient-action factor.
-/
import Fermat.Conservation.ContinuousH2Nonboundary
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

noncomputable section

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.DiscreteToContinuousH2

universe u

variable {R G : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- The trivial continuous `G`-action on the coefficient ring. -/
def trivialAction : Action (TopModuleCat R) G where
  V := TopModuleCat.of R R
  ρ := 1

omit [TopologicalSpace G] [DiscreteTopology G] in
@[simp]
theorem trivialAction_action (g : G) (x : R) :
    ((trivialAction (R := R) (G := G)).ρ g).hom x = x :=
  rfl

/-- The matching trivial representation used by discrete group cohomology. -/
abbrev discreteTrivial : Rep R G := Rep.trivial R G R

/-- The standard homogeneous degree-two cochain attached to an
inhomogeneous degree-two cochain.  Discreteness makes each nested function
continuous. -/
def rawHomogeneousTwo (c : G × G → R) : C(G, C(G, C(G, R))) :=
  ⟨fun x =>
    ⟨fun y =>
      ⟨fun z => c (x⁻¹ * y, y⁻¹ * z), continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩

/-- Bundle the standard homogeneous cochain and prove its diagonal
invariance. -/
def homogeneousTwoOfDiscrete
    (c : groupCohomology.cocycles₂ (discreteTrivial (R := R) (G := G))) :
    ((homogeneousCochains R G).obj
      (trivialAction (R := R) (G := G))).X 2 := by
  refine ⟨rawHomogeneousTwo c, ?_⟩
  intro a
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change c ((a⁻¹ * x)⁻¹ * (a⁻¹ * y), (a⁻¹ * y)⁻¹ * (a⁻¹ * z)) =
    c (x⁻¹ * y, y⁻¹ * z)
  apply congrArg c
  apply Prod.ext <;> dsimp <;> group

@[simp]
theorem homogeneousTwoOfDiscrete_apply
    (c : groupCohomology.cocycles₂ (discreteTrivial (R := R) (G := G)))
    (x y z : G) :
    twoValue (homogeneousTwoOfDiscrete c) x y z =
      c (x⁻¹ * y, y⁻¹ * z) :=
  rfl

/-- The homogeneous cochain attached to a discrete two-cocycle is closed in
Mathlib's continuous homogeneous complex. -/
theorem homogeneousTwoOfDiscrete_isCycle
    (c : groupCohomology.cocycles₂ (discreteTrivial (R := R) (G := G))) :
    (((homogeneousCochains R G).obj
      (trivialAction (R := R) (G := G))).d 2 3).hom
        (homogeneousTwoOfDiscrete c) = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change
    c (x⁻¹ * y, y⁻¹ * z) -
      (c (w⁻¹ * y, y⁻¹ * z) -
        (c (w⁻¹ * x, x⁻¹ * z) - c (w⁻¹ * x, x⁻¹ * y))) = 0
  have hc := (groupCohomology.mem_cocycles₂_def c).1 c.2
    (w⁻¹ * x) (x⁻¹ * y) (y⁻¹ * z)
  change
    c (x⁻¹ * y, y⁻¹ * z) -
      c ((w⁻¹ * x) * (x⁻¹ * y), y⁻¹ * z) +
      c (w⁻¹ * x, (x⁻¹ * y) * (y⁻¹ * z)) -
      c (w⁻¹ * x, x⁻¹ * y) = 0 at hc
  rw [show w⁻¹ * y = (w⁻¹ * x) * (x⁻¹ * y) by group,
    show x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) by group]
  linear_combination hc

/-- The cocycle-to-cycle transfer into the nominal continuous complex. -/
def continuousCycleOfDiscrete
    (c : groupCohomology.cocycles₂ (discreteTrivial (R := R) (G := G))) :
    Cycle (trivialAction (R := R) (G := G)) 2 3 :=
  ⟨⟨homogeneousTwoOfDiscrete c⟩, by
    apply Cochain.ext
    exact homogeneousTwoOfDiscrete_isCycle c⟩

/-- Evaluate a homogeneous continuous degree-one cochain at `(1,g)` to
recover an inhomogeneous degree-one cochain. -/
def inhomogeneousOneOfContinuous
    (b : Cochain (trivialAction (R := R) (G := G)) 1) : G → R :=
  fun g => oneValue b.val 1 g

@[simp]
theorem continuousOneDifferential_apply
    (b : Cochain (trivialAction (R := R) (G := G)) 1) (w x y : G) :
    twoValue
      ((((homogeneousCochains R G).obj
        (trivialAction (R := R) (G := G))).d 1 2).hom b.val)
      w x y =
      oneValue b.val x y - (oneValue b.val w y - oneValue b.val w x) :=
  rfl

/-- Boundary reflection: if the transferred homogeneous cocycle has a
continuous primitive, then evaluating that primitive at `(1,g)` exhibits the
original discrete cocycle as a discrete coboundary. -/
theorem mem_discreteCoboundaries_of_continuousBoundary
    (c : groupCohomology.cocycles₂ (discreteTrivial (R := R) (G := G)))
    (b : Cochain (trivialAction (R := R) (G := G)) 1)
    (hb : differential (trivialAction (R := R) (G := G)) 1 2 b =
      cycleCochain (trivialAction (R := R) (G := G)) 2 3
        (continuousCycleOfDiscrete c)) :
    ⇑c ∈ groupCohomology.coboundaries₂
      (discreteTrivial (R := R) (G := G)) := by
  refine ⟨inhomogeneousOneOfContinuous b, ?_⟩
  funext gh
  rcases gh with ⟨g, h⟩
  have hpoint := congrArg
    (fun q : Cochain (trivialAction (R := R) (G := G)) 2 =>
      twoValue q.val 1 g (g * h)) hb
  rw [differential_val, cycleCochain_val] at hpoint
  rw [continuousOneDifferential_apply] at hpoint
  change
    oneValue b.val g (g * h) -
      (oneValue b.val 1 (g * h) - oneValue b.val 1 g) =
        twoValue (homogeneousTwoOfDiscrete c) 1 g (g * h) at hpoint
  rw [homogeneousTwoOfDiscrete_apply] at hpoint
  have hpoint' :
      oneValue b.val g (g * h) -
        (oneValue b.val 1 (g * h) - oneValue b.val 1 g) =
          (show R from c (g, h)) := by
    simpa using hpoint
  have hinv := oneValue_invariant b.val g g (g * h)
  have hinv' : oneValue b.val 1 h = oneValue b.val g (g * h) := by
    simpa using hinv
  change
    oneValue b.val 1 h - oneValue b.val 1 (g * h) + oneValue b.val 1 g = c (g, h)
  rw [hinv']
  calc
    (oneValue b.val g (g * h) - oneValue b.val 1 (g * h) +
        oneValue b.val 1 g : R) =
      oneValue b.val g (g * h) -
        (oneValue b.val 1 (g * h) - oneValue b.val 1 g) := by abel
    _ = (show R from c (g, h)) := hpoint'

/-- A discrete nonboundary stays a nonboundary after transfer to the
continuous homogeneous complex. -/
theorem continuousCycleOfDiscrete_not_boundary
    (c : groupCohomology.cocycles₂ (discreteTrivial (R := R) (G := G)))
    (hc : ⇑c ∉ groupCohomology.coboundaries₂
      (discreteTrivial (R := R) (G := G))) :
    ¬ ∃ b : Cochain (trivialAction (R := R) (G := G)) 1,
      differential (trivialAction (R := R) (G := G)) 1 2 b =
        cycleCochain (trivialAction (R := R) (G := G)) 2 3
          (continuousCycleOfDiscrete c) := by
  rintro ⟨b, hb⟩
  exact hc (mem_discreteCoboundaries_of_continuousBoundary c b hb)

/-- A nonzero abstract discrete `H²` class has a representative whose
continuous transfer is not a boundary. -/
theorem exists_continuous_cycle_not_boundary_of_discreteH2
    (x : groupCohomology (discreteTrivial (R := R) (G := G)) 2)
    (hx : x ≠ 0) :
    ∃ z : Cycle (trivialAction (R := R) (G := G)) 2 3,
      ¬ ∃ b : Cochain (trivialAction (R := R) (G := G)) 1,
        differential (trivialAction (R := R) (G := G)) 1 2 b =
          cycleCochain (trivialAction (R := R) (G := G)) 2 3 z := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
      refine ⟨continuousCycleOfDiscrete c,
        continuousCycleOfDiscrete_not_boundary c ?_⟩
      intro hc
      apply hx
      exact (groupCohomology.H2π_eq_zero_iff c).2 hc

/-- Any nonzero discrete `H²(G,R)` class, for trivial coefficients and
discrete topologies, produces a nonzero class in Mathlib's actual continuous
`H²(G,R)`. -/
theorem exists_nonzero_actualContinuousH2_of_discreteH2
    (x : groupCohomology (discreteTrivial (R := R) (G := G)) 2)
    (hx : x ≠ 0) :
    ∃ c : (continuousCohomology R G 2).obj
      (trivialAction (R := R) (G := G)), c ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_continuous_cycle_not_boundary_of_discreteH2 x hx
  exact
    ContinuousH2Nonboundary.exists_nonzero_actualContinuousH2_of_cycle_not_boundary
      (trivialAction (R := R) (G := G)) z hz

end Fermat.Conservation.DiscreteToContinuousH2
