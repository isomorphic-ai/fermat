/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Low-degree continuous homogeneous pullback at 59

This file constructs the low-degree group-variable pullback which Mathlib's
continuous-cohomology API does not yet expose.  For a continuous homomorphism
`φ : G →ₜ* H` and trivial `ZMod 59` coefficients, simultaneous
precomposition in every homogeneous argument gives maps in degrees one,
two, and three.  The maps commute with `d¹` and `d²`, hence pull degree-two
cycles back and send source boundaries to target boundaries.

The direction of the last statement matters.  This module does **not** prove
that pullback is injective, does **not** prove that a nonboundary remains a
nonboundary, and does **not** claim that a nonzero finite-cyclic `H²` class
survives inflation to an absolute Galois group.  Those remain separate
arithmetic/cohomological obligations.
-/
import Fermat.Experiments.Conservation.ContinuousKummerTateCupNominal
import Mathlib.Topology.Instances.ZMod

noncomputable section

namespace Fermat.Conservation.ContinuousHomogeneousPullback59

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

local instance zmodContinuousSMul : ContinuousSMul (ZMod 59) (ZMod 59) :=
  ⟨continuous_of_discreteTopology⟩

/-- The trivial topological coefficient line at `59`. -/
def coefficients (G : Type) [Group G] :
    Action (TopModuleCat (ZMod 59)) G where
  V := TopModuleCat.of (ZMod 59) (ZMod 59)
  ρ := 1

@[simp]
theorem coefficients_action {G : Type} [Group G] (g : G) (x : ZMod 59) :
    ((coefficients G).ρ g).hom x = x :=
  rfl

variable {G H : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
@[simp]
lemma map_inv_mul (φ : G →ₜ* H) (a x : G) :
    φ (a⁻¹ * x) = (φ a)⁻¹ * φ x := by
  simp

/-- Precomposition on one nested continuous-map argument. -/
def precompose₁ (φ : G →ₜ* H) : C(C(H, ZMod 59), C(G, ZMod 59)) :=
  ContinuousMap.compRightContinuousMap (ZMod 59) φ.toContinuousMap

/-- Simultaneous precomposition on two nested continuous-map arguments. -/
def precompose₂ (φ : G →ₜ* H) :
    C(C(H, C(H, ZMod 59)), C(G, C(G, ZMod 59))) where
  toFun f := (precompose₁ φ).comp (f.comp φ.toContinuousMap)
  continuous_toFun :=
    (ContinuousMap.continuous_postcomp (precompose₁ φ)).comp
      (ContinuousMap.continuous_precomp φ.toContinuousMap)

/-- Simultaneous precomposition on three nested continuous-map arguments. -/
def precompose₃ (φ : G →ₜ* H) :
    C(C(H, C(H, C(H, ZMod 59))), C(G, C(G, C(G, ZMod 59)))) where
  toFun f := (precompose₂ φ).comp (f.comp φ.toContinuousMap)
  continuous_toFun :=
    (ContinuousMap.continuous_postcomp (precompose₂ φ)).comp
      (ContinuousMap.continuous_precomp φ.toContinuousMap)

/-- Simultaneous precomposition on four nested continuous-map arguments. -/
def precompose₄ (φ : G →ₜ* H) :
    C(C(H, C(H, C(H, C(H, ZMod 59)))),
      C(G, C(G, C(G, C(G, ZMod 59))))) where
  toFun f := (precompose₃ φ).comp (f.comp φ.toContinuousMap)
  continuous_toFun :=
    (ContinuousMap.continuous_postcomp (precompose₃ φ)).comp
      (ContinuousMap.continuous_precomp φ.toContinuousMap)

/-- The nested continuous map underlying a homogeneous degree-three cochain. -/
def threeValue
    (f : ((homogeneousCochains (ZMod 59) H).obj (coefficients H)).X 3) :
    C(H, C(H, C(H, C(H, ZMod 59)))) := by
  change {x : C(H, C(H, C(H, C(H, ZMod 59)))) // ∀ g : H, _} at f
  exact f.1

/-- Diagonal invariance of a homogeneous degree-two cochain, evaluated at
three arguments. -/
theorem twoValue_invariant
    (f : ((homogeneousCochains (ZMod 59) H).obj (coefficients H)).X 2)
    (a x y z : H) :
    ((coefficients H).ρ a).hom
        (Fermat.Conservation.ContinuousKummerTateCupRaw.twoValue f
          (a⁻¹ * x) (a⁻¹ * y) (a⁻¹ * z)) =
      Fermat.Conservation.ContinuousKummerTateCupRaw.twoValue f x y z := by
  change {q : C(H, C(H, C(H, ZMod 59))) // ∀ g : H, _} at f
  exact congrArg (fun q : C(H, C(H, C(H, ZMod 59))) => q x y z) (f.2 a)

/-- Diagonal invariance of a homogeneous degree-three cochain, evaluated at
four arguments. -/
theorem threeValue_invariant
    (f : ((homogeneousCochains (ZMod 59) H).obj (coefficients H)).X 3)
    (a w x y z : H) :
    ((coefficients H).ρ a).hom
        (threeValue f (a⁻¹ * w) (a⁻¹ * x) (a⁻¹ * y) (a⁻¹ * z)) =
      threeValue f w x y z := by
  change {q : C(H, C(H, C(H, C(H, ZMod 59)))) // ∀ g : H, _} at f
  exact congrArg (fun q : C(H, C(H, C(H, C(H, ZMod 59)))) => q w x y z) (f.2 a)

/-- Pull a nominal continuous homogeneous degree-one cochain back along
`φ`. -/
def pullbackOne (φ : G →ₜ* H) :
    Cochain (coefficients H) 1 → Cochain (coefficients G) 1 := fun f => by
  refine ⟨⟨precompose₂ φ
    (Fermat.Conservation.ContinuousKummerTateCupRaw.oneValue f.val), ?_⟩⟩
  intro a
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change Fermat.Conservation.ContinuousKummerTateCupRaw.oneValue f.val
      (φ (a⁻¹ * x)) (φ (a⁻¹ * y)) =
    Fermat.Conservation.ContinuousKummerTateCupRaw.oneValue f.val (φ x) (φ y)
  rw [map_inv_mul φ, map_inv_mul φ]
  simpa only [coefficients_action] using
    (Fermat.Conservation.ContinuousKummerTateCupRaw.oneValue_invariant
      f.val (φ a) (φ x) (φ y))

/-- Pull a nominal continuous homogeneous degree-two cochain back along
`φ`. -/
def pullbackTwo (φ : G →ₜ* H) :
    Cochain (coefficients H) 2 → Cochain (coefficients G) 2 := fun f => by
  refine ⟨⟨precompose₃ φ
    (Fermat.Conservation.ContinuousKummerTateCupRaw.twoValue f.val), ?_⟩⟩
  intro a
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change Fermat.Conservation.ContinuousKummerTateCupRaw.twoValue f.val
      (φ (a⁻¹ * x)) (φ (a⁻¹ * y)) (φ (a⁻¹ * z)) =
    Fermat.Conservation.ContinuousKummerTateCupRaw.twoValue f.val (φ x) (φ y) (φ z)
  rw [map_inv_mul φ, map_inv_mul φ, map_inv_mul φ]
  simpa only [coefficients_action] using
    (twoValue_invariant f.val (φ a) (φ x) (φ y) (φ z))

/-- Pull a nominal continuous homogeneous degree-three cochain back along
`φ`. -/
def pullbackThree (φ : G →ₜ* H) :
    Cochain (coefficients H) 3 → Cochain (coefficients G) 3 := fun f => by
  refine ⟨⟨precompose₄ φ (threeValue f.val), ?_⟩⟩
  intro a
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change threeValue f.val (φ (a⁻¹ * w)) (φ (a⁻¹ * x))
      (φ (a⁻¹ * y)) (φ (a⁻¹ * z)) =
    threeValue f.val (φ w) (φ x) (φ y) (φ z)
  rw [map_inv_mul φ, map_inv_mul φ, map_inv_mul φ, map_inv_mul φ]
  have h := threeValue_invariant f.val (φ a) (φ w) (φ x) (φ y) (φ z)
  rw [coefficients_action] at h
  change threeValue f.val ((φ a)⁻¹ * φ w) ((φ a)⁻¹ * φ x)
      ((φ a)⁻¹ * φ y) ((φ a)⁻¹ * φ z) =
    threeValue f.val (φ w) (φ x) (φ y) (φ z) at h
  exact h

/-- Pullback commutes with the degree-one-to-degree-two homogeneous
differential. -/
theorem pullback_differential_one_two (φ : G →ₜ* H)
    (f : Cochain (coefficients H) 1) :
    pullbackTwo φ (differential (coefficients H) 1 2 f) =
      differential (coefficients G) 1 2 (pullbackOne φ f) := by
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  rfl

/-- Pullback commutes with the degree-two-to-degree-three homogeneous
differential. -/
theorem pullback_differential_two_three (φ : G →ₜ* H)
    (f : Cochain (coefficients H) 2) :
    pullbackThree φ (differential (coefficients H) 2 3 f) =
      differential (coefficients G) 2 3 (pullbackTwo φ f) := by
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro v
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  rfl

/-- Pull a nominal continuous homogeneous degree-two cycle back along
`φ`. -/
def pullbackCycleTwo (φ : G →ₜ* H) :
    Cycle (coefficients H) 2 3 → Cycle (coefficients G) 2 3 := fun z =>
  ⟨pullbackTwo φ z.cochain, by
    rw [← pullback_differential_two_three]
    rw [z.isCycle]
    rfl⟩

/-- A source boundary pulls back to a target boundary.  The converse is
intentionally not asserted: this theorem supplies no injectivity or
nonvanishing result for pullback on `H²`. -/
theorem pullbackCycleTwo_of_boundary (φ : G →ₜ* H)
    (z : Cycle (coefficients H) 2 3)
    (hz : ∃ x : Cochain (coefficients H) 1,
      differential (coefficients H) 1 2 x =
        cycleCochain (coefficients H) 2 3 z) :
    ∃ x : Cochain (coefficients G) 1,
      differential (coefficients G) 1 2 x =
        cycleCochain (coefficients G) 2 3 (pullbackCycleTwo φ z) := by
  obtain ⟨x, hx⟩ := hz
  refine ⟨pullbackOne φ x, ?_⟩
  rw [← pullback_differential_one_two, hx]
  rfl

end Fermat.Conservation.ContinuousHomogeneousPullback59
