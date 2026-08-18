/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Prime-parametric low-degree continuous homogeneous pullback

For every prime `p`, simultaneous precomposition along a continuous group
homomorphism gives pullback maps in homogeneous degrees one, two, and three
with trivial `ZMod p` coefficients.  The maps commute with both low-degree
differentials, pull degree-two cycles back, and preserve boundaries.

No injectivity or survival-under-inflation statement is asserted.
-/
import Fermat.Conservation.PrimeCyclicH2
import Mathlib.Topology.Instances.ZMod

noncomputable section

namespace Fermat.Conservation.PrimeContinuousHomogeneousPullback

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

variable (p : ℕ) [Fact p.Prime]

local instance zmodContinuousSMul : ContinuousSMul (ZMod p) (ZMod p) :=
  ⟨continuous_of_discreteTopology⟩

/-- The trivial topological coefficient line at `p`. -/
def coefficients (G : Type) [Group G] :
    Action (TopModuleCat (ZMod p)) G where
  V := TopModuleCat.of (ZMod p) (ZMod p)
  ρ := 1

@[simp]
theorem coefficients_action {G : Type} [Group G] (g : G) (x : ZMod p) :
    ((coefficients p G).ρ g).hom x = x :=
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
def precompose₁ (φ : G →ₜ* H) : C(C(H, ZMod p), C(G, ZMod p)) :=
  ContinuousMap.compRightContinuousMap (ZMod p) φ.toContinuousMap

/-- Simultaneous precomposition on two nested continuous-map arguments. -/
def precompose₂ (φ : G →ₜ* H) :
    C(C(H, C(H, ZMod p)), C(G, C(G, ZMod p))) where
  toFun f := (precompose₁ p φ).comp (f.comp φ.toContinuousMap)
  continuous_toFun :=
    (ContinuousMap.continuous_postcomp (precompose₁ p φ)).comp
      (ContinuousMap.continuous_precomp φ.toContinuousMap)

/-- Simultaneous precomposition on three nested continuous-map arguments. -/
def precompose₃ (φ : G →ₜ* H) :
    C(C(H, C(H, C(H, ZMod p))), C(G, C(G, C(G, ZMod p)))) where
  toFun f := (precompose₂ p φ).comp (f.comp φ.toContinuousMap)
  continuous_toFun :=
    (ContinuousMap.continuous_postcomp (precompose₂ p φ)).comp
      (ContinuousMap.continuous_precomp φ.toContinuousMap)

/-- Simultaneous precomposition on four nested continuous-map arguments. -/
def precompose₄ (φ : G →ₜ* H) :
    C(C(H, C(H, C(H, C(H, ZMod p)))),
      C(G, C(G, C(G, C(G, ZMod p))))) where
  toFun f := (precompose₃ p φ).comp (f.comp φ.toContinuousMap)
  continuous_toFun :=
    (ContinuousMap.continuous_postcomp (precompose₃ p φ)).comp
      (ContinuousMap.continuous_precomp φ.toContinuousMap)

/-- The nested continuous map underlying a homogeneous degree-three cochain. -/
def threeValue
    (f : ((homogeneousCochains (ZMod p) H).obj (coefficients p H)).X 3) :
    C(H, C(H, C(H, C(H, ZMod p)))) := by
  change {x : C(H, C(H, C(H, C(H, ZMod p)))) // ∀ g : H, _} at f
  exact f.1

/-- Diagonal invariance of a homogeneous degree-two cochain, evaluated at
three arguments. -/
theorem twoValue_invariant
    (f : ((homogeneousCochains (ZMod p) H).obj (coefficients p H)).X 2)
    (a x y z : H) :
    ((coefficients p H).ρ a).hom
        (Fermat.Conservation.ContinuousKummerTateCupRaw.twoValue f
          (a⁻¹ * x) (a⁻¹ * y) (a⁻¹ * z)) =
      Fermat.Conservation.ContinuousKummerTateCupRaw.twoValue f x y z := by
  change {q : C(H, C(H, C(H, ZMod p))) // ∀ g : H, _} at f
  exact congrArg (fun q : C(H, C(H, C(H, ZMod p))) => q x y z) (f.2 a)

/-- Diagonal invariance of a homogeneous degree-three cochain, evaluated at
four arguments. -/
theorem threeValue_invariant
    (f : ((homogeneousCochains (ZMod p) H).obj (coefficients p H)).X 3)
    (a w x y z : H) :
    ((coefficients p H).ρ a).hom
        (threeValue p f (a⁻¹ * w) (a⁻¹ * x) (a⁻¹ * y) (a⁻¹ * z)) =
      threeValue p f w x y z := by
  change {q : C(H, C(H, C(H, C(H, ZMod p)))) // ∀ g : H, _} at f
  exact congrArg (fun q : C(H, C(H, C(H, C(H, ZMod p)))) => q w x y z) (f.2 a)

/-- Pull a nominal continuous homogeneous degree-one cochain back along
`φ`. -/
def pullbackOne (φ : G →ₜ* H) :
    Cochain (coefficients p H) 1 → Cochain (coefficients p G) 1 := fun f => by
  refine ⟨⟨precompose₂ p φ
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
    Cochain (coefficients p H) 2 → Cochain (coefficients p G) 2 := fun f => by
  refine ⟨⟨precompose₃ p φ
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
    (twoValue_invariant p f.val (φ a) (φ x) (φ y) (φ z))

/-- Pull a nominal continuous homogeneous degree-three cochain back along
`φ`. -/
def pullbackThree (φ : G →ₜ* H) :
    Cochain (coefficients p H) 3 → Cochain (coefficients p G) 3 := fun f => by
  refine ⟨⟨precompose₄ p φ (threeValue p f.val), ?_⟩⟩
  intro a
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change threeValue p f.val (φ (a⁻¹ * w)) (φ (a⁻¹ * x))
      (φ (a⁻¹ * y)) (φ (a⁻¹ * z)) =
    threeValue p f.val (φ w) (φ x) (φ y) (φ z)
  rw [map_inv_mul φ, map_inv_mul φ, map_inv_mul φ, map_inv_mul φ]
  have h := threeValue_invariant p f.val (φ a) (φ w) (φ x) (φ y) (φ z)
  rw [coefficients_action] at h
  change threeValue p f.val ((φ a)⁻¹ * φ w) ((φ a)⁻¹ * φ x)
      ((φ a)⁻¹ * φ y) ((φ a)⁻¹ * φ z) =
    threeValue p f.val (φ w) (φ x) (φ y) (φ z) at h
  exact h

/-- Pullback commutes with the degree-one-to-degree-two homogeneous
differential. -/
theorem pullback_differential_one_two (φ : G →ₜ* H)
    (f : Cochain (coefficients p H) 1) :
    pullbackTwo p φ (differential (coefficients p H) 1 2 f) =
      differential (coefficients p G) 1 2 (pullbackOne p φ f) := by
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
    (f : Cochain (coefficients p H) 2) :
    pullbackThree p φ (differential (coefficients p H) 2 3 f) =
      differential (coefficients p G) 2 3 (pullbackTwo p φ f) := by
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
    Cycle (coefficients p H) 2 3 → Cycle (coefficients p G) 2 3 := fun z =>
  ⟨pullbackTwo p φ z.cochain, by
    rw [← pullback_differential_two_three]
    rw [z.isCycle]
    rfl⟩

/-- A source boundary pulls back to a target boundary.  The converse is
intentionally not asserted: this theorem supplies no injectivity or
nonvanishing result for pullback on `H²`. -/
theorem pullbackCycleTwo_of_boundary (φ : G →ₜ* H)
    (z : Cycle (coefficients p H) 2 3)
    (hz : ∃ x : Cochain (coefficients p H) 1,
      differential (coefficients p H) 1 2 x =
        cycleCochain (coefficients p H) 2 3 z) :
    ∃ x : Cochain (coefficients p G) 1,
      differential (coefficients p G) 1 2 x =
        cycleCochain (coefficients p G) 2 3 (pullbackCycleTwo p φ z) := by
  obtain ⟨x, hx⟩ := hz
  refine ⟨pullbackOne p φ x, ?_⟩
  rw [← pullback_differential_one_two, hx]
  rfl

end Fermat.Conservation.PrimeContinuousHomogeneousPullback
