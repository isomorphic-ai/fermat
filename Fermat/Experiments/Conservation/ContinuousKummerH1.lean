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

Compatibility with continuous principal boundaries proves multiplicativity
of the resulting class and descends it through `Kˣ / (Kˣ)^n` to the
genuine continuous Kummer map.  The deliberate remaining boundaries are:

* no comparison with the discrete class in `LocalKummerH1` is asserted.
* no continuous cup product, `H²` class, local invariant, Hilbert-symbol
  readout, or global reflected lift is asserted.

Those require additional constructions beyond the degree-one quotient
descent in this file.
-/
import Fermat.Experiments.Conservation.LocalKummerH1
import Mathlib.Algebra.Category.ContinuousCohomology.Basic
import Mathlib.Topology.Instances.ZMod

noncomputable section

namespace Fermat.Conservation.ContinuousKummerH1

open CategoryTheory
open CategoryTheory.Limits
open groupCohomology
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.TameSymbol

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

/-! ## Linear infrastructure for continuous crossed homomorphisms -/

section CrossedHomLinear

variable (R G : Type*) [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Action (TopModuleCat R) G)

/-- Continuous crossed homomorphisms for the action `A`, as a submodule of
continuous maps.  Bundling the crossed law this way makes the passage to
continuous `H¹` visibly additive and `R`-linear. -/
def ContinuousCrossedHom : Submodule R C(G, A.V) where
  carrier := { c | ∀ g h, c (g * h) = c g + (A.ρ g).hom (c h) }
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd g h
    change ∀ g h, c (g * h) = c g + (A.ρ g).hom (c h) at hc
    change ∀ g h, d (g * h) = d g + (A.ρ g).hom (d h) at hd
    rw [ContinuousMap.add_apply, ContinuousMap.add_apply,
      ContinuousMap.add_apply, hc, hd, map_add]
    abel
  smul_mem' := by
    intro r c hc g h
    change ∀ g h, c (g * h) = c g + (A.ρ g).hom (c h) at hc
    rw [ContinuousMap.smul_apply, ContinuousMap.smul_apply,
      ContinuousMap.smul_apply, hc, map_smul, smul_add]

namespace ContinuousCrossedHom

/-- Homogenization is linear on continuous crossed homomorphisms. -/
def homogeneousOneLinear :
    ContinuousCrossedHom R G A →ₗ[R]
      ((ContinuousCohomology.homogeneousCochains R G).obj A).X 1 where
  toFun c := homogeneousOneCochain A c.1 c.2
  map_add' c d := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    change (c.1 h + d.1 h) - (c.1 g + d.1 g) =
      (c.1 h - c.1 g) + (d.1 h - d.1 g)
    abel
  map_smul' r c := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    change r • c.1 h - r • c.1 g = r • (c.1 h - c.1 g)
    rw [smul_sub]

/-- The linear homogenization map, with its image bundled in the concrete
kernel of the degree-one differential. -/
def homogeneousOneKernelLinear :
    ContinuousCrossedHom R G A →ₗ[R]
      ((((ContinuousCohomology.homogeneousCochains R G).obj A).d 1 2).hom.ker) where
  toFun c :=
    ⟨homogeneousOneCochain A c.1 c.2,
      homogeneousOneCochain_isCycle A c.1 c.2⟩
  map_add' c d := by
    apply Subtype.ext
    exact (homogeneousOneLinear R G A).map_add c d
  map_smul' r c := by
    apply Subtype.ext
    exact (homogeneousOneLinear R G A).map_smul r c

/-! ## Principal crossed homomorphisms are homogeneous boundaries -/

/-- If a continuous crossed homomorphism is pointwise principal, adding its
principal witness produces the corresponding continuous homogeneous
zero-cochain.  In particular, continuity of the orbit map is derived from
the already-continuous crossed homomorphism rather than assumed separately. -/
def principalZeroCochain
    (c : ContinuousCrossedHom R G A) (m : A.V)
    (hc : ∀ g, c.1 g = (A.ρ g).hom m - m) :
    ((ContinuousCohomology.homogeneousCochains R G).obj A).X 0 := by
  let f : C(G, A.V) := c.1 + ContinuousMap.const G m
  refine ⟨f, ?_⟩
  intro k
  change ((ContinuousCohomology.Iobj (R := R) (G := G) A).ρ k).hom f = f
  apply ContinuousMap.ext
  intro g
  change (A.ρ k).hom (f (k⁻¹ * g)) = f g
  have hf (x : G) : f x = (A.ρ x).hom m := by
    change c.1 x + m = (A.ρ x).hom m
    rw [hc]
    abel
  rw [hf, hf, ← ConcreteCategory.comp_apply]
  change (ConcreteCategory.hom (A.ρ k * A.ρ (k⁻¹ * g))) m =
    (A.ρ g).hom m
  rw [← A.ρ.map_mul]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem principalZeroCochain_apply
    (c : ContinuousCrossedHom R G A) (m : A.V)
    (hc : ∀ g, c.1 g = (A.ρ g).hom m - m) (g : G) :
    DFunLike.coe (F := C(G, _))
      (principalZeroCochain R G A c m hc).1 g = c.1 g + m := by
  change c.1 g + m = c.1 g + m
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Readback of Mathlib's degree-zero homogeneous differential.  The sign
convention is `(d⁰ f)(g,h) = f(h) - f(g)`. -/
theorem homogeneousDifferentialZero_apply
    (f : ((ContinuousCohomology.homogeneousCochains R G).obj A).X 0)
    (g h : G) :
    DFunLike.coe (F := C(G, _))
      (DFunLike.coe (F := C(G, _))
        ((((ContinuousCohomology.homogeneousCochains R G).obj A).d 0 1).hom f).1 g) h =
      DFunLike.coe (F := C(G, _)) f.1 h -
        DFunLike.coe (F := C(G, _)) f.1 g :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise readback that the homogeneous cochain attached to a principal
crossed homomorphism is exactly the positive-sign degree-zero boundary. -/
theorem homogeneousOneCochain_eq_d_principalZeroCochain_apply
    (c : ContinuousCrossedHom R G A) (m : A.V)
    (hc : ∀ g, c.1 g = (A.ρ g).hom m - m) (g h : G) :
    DFunLike.coe (F := C(G, _))
      (DFunLike.coe (F := C(G, _))
        (homogeneousOneCochain A c.1 c.2).1 g) h =
    DFunLike.coe (F := C(G, _))
      (DFunLike.coe (F := C(G, _))
        ((((ContinuousCohomology.homogeneousCochains R G).obj A).d 0 1).hom
          (principalZeroCochain R G A c m hc)).1 g) h := by
  change c.1 h - c.1 g =
    DFunLike.coe (F := C(G, _))
      (DFunLike.coe (F := C(G, _))
        ((((ContinuousCohomology.homogeneousCochains R G).obj A).d 0 1).hom
          (principalZeroCochain R G A c m hc)).1 g) h
  rw [homogeneousDifferentialZero_apply, principalZeroCochain_apply,
    principalZeroCochain_apply]
  abel

/-- A principal continuous crossed homomorphism homogenizes to an actual
degree-zero boundary, with no sign correction. -/
theorem homogeneousOneCochain_eq_d_principalZeroCochain
    (c : ContinuousCrossedHom R G A) (m : A.V)
    (hc : ∀ g, c.1 g = (A.ρ g).hom m - m) :
    @Eq (((ContinuousCohomology.homogeneousCochains R G).obj A).X 1)
      (homogeneousOneCochain A c.1 c.2)
      (((((ContinuousCohomology.homogeneousCochains R G).obj A).d 0 1).hom
        (principalZeroCochain R G A c m hc))) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  apply ContinuousMap.ext
  intro h
  exact homogeneousOneCochain_eq_d_principalZeroCochain_apply R G A c m hc g h

/- Mathlib's cycles object is categorical rather than definitionally the
concrete kernel.  Comparing the two kernel limit cones gives a small,
stable injectivity receipt for reading equality back through `iCycles`.
Keeping this theorem separate avoids unfolding the full homogeneous
complex in every later boundary calculation. -/
set_option maxHeartbeats 800000 in
theorem homogeneousOneICycles_injective :
    Function.Injective
      (((((ContinuousCohomology.homogeneousCochains R G).obj A).iCycles 1).hom)) := by
  let C := (ContinuousCohomology.homogeneousCochains R G).obj A
  let d := C.d 1 2
  let e : TopModuleCat.ker d ≅ C.cycles 1 :=
    IsLimit.conePointUniqueUpToIso
      (TopModuleCat.isLimitKer d) (C.cyclesIsKernel 1 2 (by simp))
  have he : e.inv ≫ TopModuleCat.kerι d = C.iCycles 1 := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp _ _
      WalkingParallelPair.zero
  intro x y hxy
  have hxy' : e.inv.hom x = e.inv.hom y := by
    apply Subtype.ext
    have hmap :
        (TopModuleCat.kerι d).hom (e.inv.hom x) =
          (TopModuleCat.kerι d).hom (e.inv.hom y) := by
      simpa only [← ConcreteCategory.comp_apply, he] using hxy
    exact hmap
  have h := congrArg e.hom.hom hxy'
  simpa [← ConcreteCategory.comp_apply] using h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The categorical cycle associated to a principal crossed homomorphism
is exactly the cycle induced by its degree-zero boundary. -/
theorem homogeneousOneCycle_eq_toCycles_principal
    (c : ContinuousCrossedHom R G A) (m : A.V)
    (hc : ∀ g, c.1 g = (A.ρ g).hom m - m) :
    homogeneousOneCycle A c.1 c.2 =
      ((((ContinuousCohomology.homogeneousCochains R G).obj A).toCycles 0 1).hom
        (principalZeroCochain R G A c m hc)) := by
  let C := (ContinuousCohomology.homogeneousCochains R G).obj A
  apply homogeneousOneICycles_injective R G A
  rw [← ConcreteCategory.comp_apply, C.toCycles_i 0 1]
  simp only [homogeneousOneCycle, ← ConcreteCategory.comp_apply,
    HomologicalComplex.liftCycles_i]
  exact homogeneousOneCochain_eq_d_principalZeroCochain R G A c m hc

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Principal continuous crossed homomorphisms represent zero in genuine
continuous degree-one cohomology. -/
theorem homogeneousOneClass_eq_zero_of_principal
    (c : ContinuousCrossedHom R G A) (m : A.V)
    (hc : ∀ g, c.1 g = (A.ρ g).hom m - m) :
    homogeneousOneClass A c.1 c.2 = 0 := by
  let C := (ContinuousCohomology.homogeneousCochains R G).obj A
  unfold homogeneousOneClass
  rw [homogeneousOneCycle_eq_toCycles_principal R G A c m hc]
  rw [← ConcreteCategory.comp_apply, C.toCycles_comp_homologyπ 0 1]
  rfl

end ContinuousCrossedHom

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Addition of continuous crossed homomorphisms is preserved in the
categorical degree-one cycles object. -/
theorem homogeneousOneCycle_add
    (c d : ContinuousCrossedHom R G A) :
    homogeneousOneCycle A (c + d).1 (c + d).2 =
      homogeneousOneCycle A c.1 c.2 + homogeneousOneCycle A d.1 d.2 := by
  apply ContinuousCrossedHom.homogeneousOneICycles_injective R G A
  simp only [homogeneousOneCycle, ← ConcreteCategory.comp_apply,
    HomologicalComplex.liftCycles_i, map_add]
  exact (ContinuousCrossedHom.homogeneousOneLinear R G A).map_add c d

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Addition of continuous crossed homomorphisms is preserved after passage
to genuine continuous degree-one cohomology. -/
theorem homogeneousOneClass_add
    (c d : ContinuousCrossedHom R G A) :
    homogeneousOneClass A (c + d).1 (c + d).2 =
      homogeneousOneClass A c.1 c.2 + homogeneousOneClass A d.1 d.2 := by
  unfold homogeneousOneClass
  rw [homogeneousOneCycle_add (R := R) (G := G) A c d, map_add]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Subtraction of continuous crossed homomorphisms is preserved in the
categorical degree-one cycles object. -/
theorem homogeneousOneCycle_sub
    (c d : ContinuousCrossedHom R G A) :
    homogeneousOneCycle A (c - d).1 (c - d).2 =
      homogeneousOneCycle A c.1 c.2 - homogeneousOneCycle A d.1 d.2 := by
  apply ContinuousCrossedHom.homogeneousOneICycles_injective R G A
  simp only [homogeneousOneCycle, ← ConcreteCategory.comp_apply,
    HomologicalComplex.liftCycles_i, map_sub]
  exact (ContinuousCrossedHom.homogeneousOneLinear R G A).map_sub c d

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Subtraction of continuous crossed homomorphisms is preserved after
passage to genuine continuous degree-one cohomology. -/
theorem homogeneousOneClass_sub
    (c d : ContinuousCrossedHom R G A) :
    homogeneousOneClass A (c - d).1 (c - d).2 =
      homogeneousOneClass A c.1 c.2 - homogeneousOneClass A d.1 d.2 := by
  unfold homogeneousOneClass
  rw [homogeneousOneCycle_sub (R := R) (G := G) A c d, map_sub]

end CrossedHomLinear

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

/-- The concrete continuous Kummer cocycle, bundled with its crossed law.

This retains the complete roots-of-unity-valued Kummer state; it does not
split the class into valuation, torsion, and logarithmic coordinates. -/
def kummerCrossedHom (a : Kˣ) :
    ContinuousCrossedHom (ZMod n) (AbsoluteGalois K)
      (rootsTopRepresentation n K) :=
  ⟨continuousCocycle n K a, continuousCocycle_crossed n K a⟩

@[simp]
theorem kummerCrossedHom_apply (a : Kˣ) (σ : AbsoluteGalois K) :
    (kummerCrossedHom n K a).1 σ = continuousCocycle n K a σ :=
  rfl

/-- The cocycle of the unit representative `1` is principal.

The witness is extracted from the already proved discrete Kummer
coboundary theorem.  No private chosen root is exposed. -/
theorem exists_principalWitness_one :
    ∃ m : (rootsTopRepresentation n K).V,
      ∀ σ : AbsoluteGalois K,
        (kummerCrossedHom n K 1).1 σ =
          ((rootsTopRepresentation n K).ρ σ).hom m - m := by
  have hmem :
      (⇑(LocalKummerH1.cocycle n K 1) :
          AbsoluteGalois K → Additive (KummerRoots n K)) ∈
        coboundaries₁ (LocalKummerH1.rootsRepresentation n K) :=
    (H1π_eq_zero_iff (LocalKummerH1.cocycle n K 1)).1 <| by
      simpa [LocalKummerH1.classOfUnit] using
        LocalKummerH1.classOfUnit_one n K
  obtain ⟨m, hm⟩ := isCoboundary₁_of_mem_coboundaries₁ _ hmem
  refine ⟨m, ?_⟩
  intro σ
  exact (hm σ).symm

/-- The failure of the chosen-root cocycle to preserve multiplication on
the nose is a principal continuous crossed homomorphism.

This extracts the witness from the public discrete multiplicativity proof;
the private explicit multiplication defect therefore need not become part
of the public API. -/
theorem exists_principalWitness_mul_defect (a b : Kˣ) :
    ∃ m : (rootsTopRepresentation n K).V,
      ∀ σ : AbsoluteGalois K,
        (kummerCrossedHom n K (a * b) -
            (kummerCrossedHom n K a + kummerCrossedHom n K b)).1 σ =
          ((rootsTopRepresentation n K).ρ σ).hom m - m := by
  let cab := LocalKummerH1.cocycle n K (a * b)
  let csum := LocalKummerH1.cocycle n K a +
    LocalKummerH1.cocycle n K b
  have heq : H1π (LocalKummerH1.rootsRepresentation n K) cab =
      H1π (LocalKummerH1.rootsRepresentation n K) csum := by
    simpa [cab, csum, LocalKummerH1.classOfUnit] using
      LocalKummerH1.classOfUnit_mul n K a b
  have hmem :
      (⇑cab - ⇑csum :
          AbsoluteGalois K → Additive (KummerRoots n K)) ∈
        coboundaries₁ (LocalKummerH1.rootsRepresentation n K) :=
    (H1π_eq_iff cab csum).1 heq
  obtain ⟨m, hm⟩ := isCoboundary₁_of_mem_coboundaries₁ _ hmem
  refine ⟨m, ?_⟩
  intro σ
  exact (hm σ).symm

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

This is a genuine class in Mathlib's homogeneous continuous complex.  The
theorems below prove its representative compatibility and descend it to the
Kummer quotient. -/
noncomputable def continuousClassOfUnit (a : Kˣ) :
    ContinuousKummerCohomologyOne n K :=
  homogeneousOneClass (rootsTopRepresentation n K)
    (continuousCocycle n K a)
    (continuousCocycle_crossed n K a)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
@[simp]
theorem continuousClassOfUnit_one :
    continuousClassOfUnit n K 1 = 0 := by
  obtain ⟨m, hm⟩ := exists_principalWitness_one n K
  exact ContinuousCrossedHom.homogeneousOneClass_eq_zero_of_principal
    (ZMod n) (AbsoluteGalois K) (rootsTopRepresentation n K)
    (kummerCrossedHom n K 1) m hm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Multiplication of field units becomes addition of their genuine
continuous Kummer classes. -/
theorem continuousClassOfUnit_mul (a b : Kˣ) :
    continuousClassOfUnit n K (a * b) =
      continuousClassOfUnit n K a + continuousClassOfUnit n K b := by
  let defect := kummerCrossedHom n K (a * b) -
    (kummerCrossedHom n K a + kummerCrossedHom n K b)
  obtain ⟨m, hm⟩ := exists_principalWitness_mul_defect n K a b
  have hz : homogeneousOneClass (rootsTopRepresentation n K)
      defect.1 defect.2 = 0 :=
    ContinuousCrossedHom.homogeneousOneClass_eq_zero_of_principal
      (ZMod n) (AbsoluteGalois K) (rootsTopRepresentation n K)
      defect m hm
  rw [show homogeneousOneClass (rootsTopRepresentation n K)
      defect.1 defect.2 =
        continuousClassOfUnit n K (a * b) -
          (continuousClassOfUnit n K a + continuousClassOfUnit n K b) by
      dsimp only [defect, continuousClassOfUnit]
      rw [homogeneousOneClass_sub, homogeneousOneClass_add]
      rfl] at hz
  exact sub_eq_zero.mp hz

/-- Every class in continuous `H¹(G_K, μ_n)` is killed by `n`. -/
theorem nsmul_continuousKummerH1_eq_zero
    (x : ContinuousKummerCohomologyOne n K) :
    n • x = 0 :=
  ZModModule.char_nsmul_eq_zero n x

/-- The representative continuous Kummer map, on multiplicatively written
units presented additively. -/
noncomputable def continuousRepresentativeMap :
    Additive Kˣ →+ ContinuousKummerCohomologyOne n K where
  toFun a := continuousClassOfUnit n K a.toMul
  map_zero' := continuousClassOfUnit_one n K
  map_add' a b := continuousClassOfUnit_mul n K a.toMul b.toMul

/-- The continuous Kummer class of an `n`-th power vanishes. -/
theorem continuousClassOfUnit_pow_n (a : Kˣ) :
    continuousClassOfUnit n K (a ^ n) = 0 := by
  change continuousRepresentativeMap n K
    (Additive.ofMul (a ^ n)) = 0
  rw [ofMul_pow, map_nsmul,
    nsmul_continuousKummerH1_eq_zero]

private noncomputable def continuousRepresentativeMonoidHom :
    Kˣ →* Multiplicative (ContinuousKummerCohomologyOne n K) :=
  AddMonoidHom.toMultiplicative (continuousRepresentativeMap n K)

/-- The continuous absolute-Galois Kummer map, descended through `n`-th
powers. -/
noncomputable def continuousMap :
    KummerClass n K →+ ContinuousKummerCohomologyOne n K :=
  MonoidHom.toAdditive <|
    QuotientGroup.lift (powMonoidHom n : Kˣ →* Kˣ).range
      (continuousRepresentativeMonoidHom n K) fun x hx ↦ by
        obtain ⟨y, rfl⟩ := hx
        change Multiplicative.ofAdd
          (continuousRepresentativeMap n K
            (n • Additive.ofMul y)) = 1
        rw [map_nsmul, nsmul_continuousKummerH1_eq_zero]
        rfl

@[simp]
theorem continuousMap_classOfUnit (a : Kˣ) :
    continuousMap n K (Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a)) =
      continuousClassOfUnit n K a := by
  rfl

end Fermat.Conservation.ContinuousKummerH1
