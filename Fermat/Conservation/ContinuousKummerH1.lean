/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The continuous absolute-Galois Kummer class in degree one

This file places the concrete chosen-root Kummer cocycle from
`LocalKummerH1` inside Mathlib's homogeneous continuous-cohomology complex.
The passage from an inhomogeneous crossed homomorphism `c` to a homogeneous
cochain is the standard formula

`(g, h) ↦ c(h) - c(g)`.

The construction below proves that this cochain is invariant and killed by
the degree-one differential.  It then uses the actual cycles object and
homology projection of `ContinuousCohomology.homogeneousCochains` to produce
a genuine continuous `H¹` class for each representative unit.

The deliberate boundaries are:

* no multiplicativity in the representative unit is asserted;
* no descent through `Kˣ / (Kˣ)^n` is asserted;
* no comparison with the discrete class in `LocalKummerH1` is asserted.
* no continuous cup product, `H²` class, local invariant, Hilbert-symbol
  readout, or global reflected lift is asserted.

Those require further compatibility with continuous coboundaries.  In
particular, `continuousClassOfUnit` is not advertised as a Kummer map on the
quotient.
-/
import Fermat.Conservation.LocalKummerH1
import Mathlib.Algebra.Category.ContinuousCohomology.Basic
import Mathlib.Topology.Instances.ZMod

noncomputable section

namespace Fermat.Conservation.ContinuousKummerH1

open CategoryTheory
open groupCohomology
open Fermat.Conservation.LocalKummerH1

open scoped LocalKummerH1.KummerRootsDiscrete

/-! ## Generic passage from crossed homomorphisms to homogeneous cochains -/

section Generic

variable {G M : Type*} [TopologicalSpace G]
  [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M]

/-- Homogenize a continuous inhomogeneous one-cochain by the formula
`(g, h) ↦ c(h) - c(g)`.

Writing the inner function as a translated copy of `c` proves continuity
directly in Mathlib's iterated-continuous-map model; no local compactness
hypothesis is needed. -/
def homogenize (c : C(G, M)) : C(G, C(G, M)) where
  toFun g := c - ContinuousMap.const G (c g)
  continuous_toFun :=
    continuous_const.sub
      ((ContinuousLinearMap.const ℤ G).continuous.comp c.continuous)

@[simp]
theorem homogenize_apply (c : C(G, M)) (g h : G) :
    homogenize c g h = c h - c g :=
  rfl

end Generic

section Homogeneous

variable {R G : Type*} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Action (TopModuleCat R) G)

/-- An invariant homogeneous degree-one cochain obtained from a continuous
crossed homomorphism.

The crossed law uses the action bundled in `A`; this is what supplies the
invariance condition imposed by the homogeneous complex. -/
def homogeneousOneCochain
    (c : C(G, A.V))
    (hc : ∀ g h : G, c (g * h) = c g + (A.ρ g).hom (c h)) :
    ((ContinuousCohomology.homogeneousCochains R G).obj A).X 1 := by
  refine ⟨homogenize c, ?_⟩
  intro a
  apply ContinuousMap.ext
  intro g
  apply ContinuousMap.ext
  intro h
  change (A.ρ a).hom (c (a⁻¹ * h) - c (a⁻¹ * g)) = c h - c g
  rw [map_sub]
  have hh := hc a (a⁻¹ * h)
  have hg := hc a (a⁻¹ * g)
  simp only [mul_inv_cancel_left] at hh hg
  rw [hh, hg]
  abel

@[simp]
theorem homogeneousOneCochain_val
    (c : C(G, A.V))
    (hc : ∀ g h : G, c (g * h) = c g + (A.ρ g).hom (c h)) :
    (homogeneousOneCochain A c hc).1 = homogenize c :=
  rfl

/-- The homogeneous cochain associated to a crossed homomorphism is killed
by the degree-one differential. -/
theorem homogeneousOneCochain_isCycle
    (c : C(G, A.V))
    (hc : ∀ g h : G, c (g * h) = c g + (A.ρ g).hom (c h)) :
    (((ContinuousCohomology.homogeneousCochains R G).obj A).d 1 2).hom
      (homogeneousOneCochain A c hc) = 0 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  apply ContinuousMap.ext
  intro h
  apply ContinuousMap.ext
  intro k
  change (c k - c h) - ((c k - c g) - (c h - c g)) = 0
  abel

/-- The homogeneous one-cochain, bundled in the concrete kernel of the
degree-one differential. -/
def homogeneousOneKernel
    (c : C(G, A.V))
    (hc : ∀ g h : G, c (g * h) = c g + (A.ρ g).hom (c h)) :
    TopModuleCat.ker
      (((ContinuousCohomology.homogeneousCochains R G).obj A).d 1 2) :=
  ⟨homogeneousOneCochain A c hc, homogeneousOneCochain_isCycle A c hc⟩

/- The same cochain in Mathlib's categorical cycles object.

`TopModuleCat.kerι` is the concrete kernel inclusion.  The categorical
`liftCycles` identifies that kernel with the cycles object used by homology. -/
set_option maxHeartbeats 800000 in
noncomputable def homogeneousOneCycle
    (c : C(G, A.V))
    (hc : ∀ g h : G, c (g * h) = c g + (A.ρ g).hom (c h)) :
    ((ContinuousCohomology.homogeneousCochains R G).obj A).cycles 1 :=
  let C := (ContinuousCohomology.homogeneousCochains R G).obj A
  (C.liftCycles (TopModuleCat.kerι (C.d 1 2)) 2
      ((ComplexShape.up ℕ).next_eq' (by simp)) (by simp)).hom
    (homogeneousOneKernel A c hc)

/-- The genuine continuous-cohomology class represented by a continuous
crossed homomorphism. -/
noncomputable def homogeneousOneClass
    (c : C(G, A.V))
    (hc : ∀ g h : G, c (g * h) = c g + (A.ρ g).hom (c h)) :
    (continuousCohomology R G 1).obj A :=
  let C := (ContinuousCohomology.homogeneousCochains R G).obj A
  (C.homologyπ 1).hom (homogeneousOneCycle A c hc)

end Homogeneous

/-! ## The absolute-Galois roots-of-unity representation -/

variable (n : ℕ) (K : Type) [Field K] [NeZero n]

/- The roots module and `ZMod n` both carry their canonical discrete
topologies.  This local instance records the resulting joint continuity of
scalar multiplication without exporting another topology or global
instance. -/
local instance rootsContinuousSMul :
    ContinuousSMul (ZMod n) (Additive (KummerRoots n K)) :=
  ⟨continuous_of_discreteTopology⟩

/-- The natural absolute-Galois action on `μ_n`, promoted from the discrete
linear representation to an action in topological `ZMod n`-modules. -/
def rootsTopRepresentation :
    Action (TopModuleCat (ZMod n)) (AbsoluteGalois K) where
  V := TopModuleCat.of (ZMod n) (Additive (KummerRoots n K))
  ρ :=
    { toFun := fun σ => TopModuleCat.ofHom
        { toFun := fun x => σ • x
          map_add' := smul_add σ
          map_smul' := fun c x => smul_comm σ c x
          cont := continuous_of_discreteTopology }
      map_one' := by
        apply ConcreteCategory.ext
        apply ContinuousLinearMap.ext
        intro x
        exact one_smul (AbsoluteGalois K) x
      map_mul' := by
        intro σ τ
        apply ConcreteCategory.ext
        apply ContinuousLinearMap.ext
        intro x
        exact mul_smul σ τ x }

/-! ## The concrete continuous Kummer cocycle and class -/

/-- The chosen-root Kummer cocycle as a continuous map into the additively
written roots of unity. -/
def continuousCocycleValue (a : Kˣ) :
    C(AbsoluteGalois K, Additive (KummerRoots n K)) :=
  ⟨fun σ => Additive.ofMul (LocalKummerH1.cocycleValue n K a σ),
    LocalKummerH1.continuous_cocycleValue n K a⟩

@[simp]
theorem continuousCocycleValue_apply (a : Kˣ) (σ : AbsoluteGalois K) :
    continuousCocycleValue n K a σ =
      Additive.ofMul (LocalKummerH1.cocycleValue n K a σ) :=
  rfl

/-- The usual inhomogeneous one-cocycle identity, read from the already
proved discrete cocycle membership. -/
theorem continuousCocycleValue_mul (a : Kˣ) (σ τ : AbsoluteGalois K) :
    continuousCocycleValue n K a (σ * τ) =
      σ • continuousCocycleValue n K a τ +
        continuousCocycleValue n K a σ := by
  exact isCocycle₁_of_mem_cocycles₁
    (fun g => Additive.ofMul (LocalKummerH1.cocycleValue n K a g))
    (LocalKummerH1.cocycle n K a).2 σ τ

/-- The crossed law in the exact orientation expected by
`homogeneousOneCochain`. -/
theorem continuousCocycleValue_crossed (a : Kˣ)
    (σ τ : AbsoluteGalois K) :
    continuousCocycleValue n K a (σ * τ) =
      continuousCocycleValue n K a σ +
        σ • continuousCocycleValue n K a τ := by
  rw [continuousCocycleValue_mul]
  exact add_comm _ _

/-- The continuous Kummer cocycle with its codomain presented as the
underlying module of the topological representation. -/
def continuousCocycle (a : Kˣ) :
    C(AbsoluteGalois K, (rootsTopRepresentation n K).V) :=
  continuousCocycleValue n K a

@[simp]
theorem continuousCocycle_apply (a : Kˣ) (σ : AbsoluteGalois K) :
    continuousCocycle n K a σ = continuousCocycleValue n K a σ :=
  rfl

/-- The same crossed law, now typed entirely in the topological
representation used by the homogeneous complex. -/
theorem continuousCocycle_crossed (a : Kˣ) (σ τ : AbsoluteGalois K) :
    continuousCocycle n K a (σ * τ) =
      continuousCocycle n K a σ +
        ((rootsTopRepresentation n K).ρ σ).hom
          (continuousCocycle n K a τ) := by
  change continuousCocycleValue n K a (σ * τ) =
    continuousCocycleValue n K a σ +
      σ • continuousCocycleValue n K a τ
  exact continuousCocycleValue_crossed n K a σ τ

/-- Degree-one cochains in the homogeneous continuous Kummer complex. -/
abbrev ContinuousKummerCochainsOne :=
  ((ContinuousCohomology.homogeneousCochains (ZMod n)
    (AbsoluteGalois K)).obj (rootsTopRepresentation n K)).X 1

/-- The concrete Kummer cocycle, now seated as an invariant homogeneous
degree-one continuous cochain. -/
def kummerHomogeneousOneCochain (a : Kˣ) :
    ContinuousKummerCochainsOne n K :=
  homogeneousOneCochain (rootsTopRepresentation n K)
    (continuousCocycle n K a)
    (continuousCocycle_crossed n K a)

@[simp]
theorem kummerHomogeneousOneCochain_val (a : Kˣ) :
    (kummerHomogeneousOneCochain n K a).1 =
      homogenize (continuousCocycle n K a) :=
  rfl

/-- The concrete homogeneous Kummer cochain is a cycle. -/
theorem kummerHomogeneousOneCochain_isCycle (a : Kˣ) :
    (((ContinuousCohomology.homogeneousCochains (ZMod n)
      (AbsoluteGalois K)).obj (rootsTopRepresentation n K)).d 1 2).hom
        (kummerHomogeneousOneCochain n K a) = 0 :=
  homogeneousOneCochain_isCycle (rootsTopRepresentation n K)
    (continuousCocycle n K a)
    (continuousCocycle_crossed n K a)

/-- The cycles object containing the continuous Kummer cocycle. -/
abbrev ContinuousKummerCyclesOne :=
  ((ContinuousCohomology.homogeneousCochains (ZMod n)
    (AbsoluteGalois K)).obj (rootsTopRepresentation n K)).cycles 1

/-- The concrete Kummer cocycle bundled in Mathlib's degree-one cycles
object. -/
noncomputable def kummerHomogeneousOneCycle (a : Kˣ) :
    ContinuousKummerCyclesOne n K :=
  homogeneousOneCycle (rootsTopRepresentation n K)
    (continuousCocycle n K a)
    (continuousCocycle_crossed n K a)

/-- Genuine degree-one continuous cohomology for the topological
roots-of-unity representation. -/
abbrev ContinuousKummerCohomologyOne :=
  (continuousCohomology (ZMod n) (AbsoluteGalois K) 1).obj
    (rootsTopRepresentation n K)

/-- The continuous cohomology class of the chosen-root Kummer cocycle.

This is a genuine class in Mathlib's homogeneous continuous complex, but it
is only attached to a representative unit here.  No quotient descent or
comparison theorem is part of this declaration. -/
noncomputable def continuousClassOfUnit (a : Kˣ) :
    ContinuousKummerCohomologyOne n K :=
  homogeneousOneClass (rootsTopRepresentation n K)
    (continuousCocycle n K a)
    (continuousCocycle_crossed n K a)

end Fermat.Conservation.ContinuousKummerH1
