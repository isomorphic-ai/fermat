/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The raw continuous Kummer--Tate cup product

This file constructs the degree-`(1,1)` Alexander--Whitney cup product in
Mathlib's homogeneous continuous-cochain complex.  The two degree-one
cochains may have different coefficient representations.  Their values are
combined by a jointly continuous, equivariant bilinear pairing

`A.V × B.V → C.V`.

For homogeneous cochains `f` and `g`, the cup cochain is

`(x,y,z) ↦ β (f(x,y)) (g(y,z))`.

The construction proves directly that cups of one-cocycles are two-cocycles,
is bilinear, and sends a boundary in either input to an explicit boundary.
It deliberately stops before descending through the categorical homology
quotients.  No local invariant, Tate-duality theorem, Kummer map, or
discrete-to-continuous comparison is asserted here.
-/
import Mathlib.Algebra.Category.ContinuousCohomology.Basic

noncomputable section

namespace Fermat.Conservation.ContinuousKummerTateCupRaw

open CategoryTheory
open ContinuousCohomology

universe u

variable {R G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A jointly continuous, bilinear coefficient pairing which intertwines the
three `G`-actions.

This is the concrete adapter needed when two differently typed coefficient
representations have tensor product landing in an oriented output line. -/
structure ContinuousEquivariantPairing
    (A B C : Action (TopModuleCat R) G) where
  toLinearMap : A.V →ₗ[R] B.V →ₗ[R] C.V
  continuous_uncurry :
    Continuous (fun x : A.V × B.V => toLinearMap x.1 x.2)
  equivariant : ∀ (g : G) (a : A.V) (b : B.V),
    toLinearMap ((A.ρ g).hom a) ((B.ρ g).hom b) =
      (C.ρ g).hom (toLinearMap a b)

variable {A B C : Action (TopModuleCat R) G}

/-! ## Pointwise readback of low-degree homogeneous cochains -/

/-- The nested continuous map underlying a homogeneous degree-one cochain. -/
def oneValue
    (f : ((homogeneousCochains R G).obj A).X 1) :
    C(G, C(G, A.V)) := by
  change {x : C(G, C(G, A.V)) // ∀ g : G, _} at f
  exact f.1

/-- Invariance of a homogeneous degree-one cochain, evaluated at two
arguments. -/
theorem oneValue_invariant
    (f : ((homogeneousCochains R G).obj A).X 1) (a x y : G) :
    (A.ρ a).hom (oneValue f (a⁻¹ * x) (a⁻¹ * y)) =
      oneValue f x y := by
  change {x : C(G, C(G, A.V)) // ∀ g : G, _} at f
  exact congrArg (fun q : C(G, C(G, A.V)) => q x y) (f.2 a)

/-- The nested continuous map underlying a homogeneous degree-two cochain. -/
def twoValue
    (h : ((homogeneousCochains R G).obj A).X 2) :
    C(G, C(G, C(G, A.V))) := by
  change {x : C(G, C(G, C(G, A.V))) // ∀ g : G, _} at h
  exact h.1

/-- Pointwise form of the degree-one cocycle equation in Mathlib's
homogeneous complex. -/
theorem oneCycle_identity
    (f : ((homogeneousCochains R G).obj A).X 1)
    (hf : (((homogeneousCochains R G).obj A).d 1 2).hom f = 0)
    (w x y : G) :
    oneValue f x y - (oneValue f w y - oneValue f w x) = 0 := by
  have h := congrArg
    (fun q : ((homogeneousCochains R G).obj A).X 2 => twoValue q w x y) hf
  exact h

/-- The continuous map underlying a homogeneous degree-zero cochain. -/
def zeroValue
    (a : ((homogeneousCochains R G).obj A).X 0) : C(G, A.V) := by
  change {x : C(G, A.V) // ∀ g : G, _} at a
  exact a.1

/-- Invariance of a homogeneous degree-zero cochain, evaluated at one
argument. -/
theorem zeroValue_invariant
    (a : ((homogeneousCochains R G).obj A).X 0) (q x : G) :
    (A.ρ q).hom (zeroValue a (q⁻¹ * x)) = zeroValue a x := by
  change {x : C(G, A.V) // ∀ g : G, _} at a
  exact congrArg (fun f : C(G, A.V) => f x) (a.2 q)

/-- Mathlib's degree-zero homogeneous differential has the expected
pointwise formula `a(y) - a(x)`. -/
@[simp]
theorem zeroBoundary_apply
    (a : ((homogeneousCochains R G).obj A).X 0) (x y : G) :
    oneValue ((((homogeneousCochains R G).obj A).d 0 1).hom a) x y =
      zeroValue a y - zeroValue a x :=
  rfl

/-! ## The raw degree-`(1,1)` cup -/

section LocallyCompact

variable [LocallyCompactSpace G]

/-- The unbundled value of the Alexander--Whitney degree-`(1,1)` cup.

Local compactness is used only to un-curry arbitrary nested continuous maps
and hence prove joint continuity of their evaluation. -/
def rawCup
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).X 1)
    (g : ((homogeneousCochains R G).obj B).X 1) :
    C(G, C(G, C(G, C.V))) := by
  let F : C((G × G) × G, C.V) :=
    ⟨fun xyz => p.toLinearMap
        (oneValue f xyz.1.1 xyz.1.2) (oneValue g xyz.1.2 xyz.2), by
      have hf : Continuous (fun xy : G × G => oneValue f xy.1 xy.2) :=
        ContinuousMap.continuous_uncurry_of_continuous (oneValue f)
      have hg : Continuous (fun xy : G × G => oneValue g xy.1 xy.2) :=
        ContinuousMap.continuous_uncurry_of_continuous (oneValue g)
      exact p.continuous_uncurry.comp
        (Continuous.prodMk (hf.comp continuous_fst)
          (hg.comp
            (Continuous.prodMk (continuous_snd.comp continuous_fst)
              continuous_snd)))⟩
  exact ContinuousMap.curry (ContinuousMap.curry F)

@[simp]
theorem rawCup_apply
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).X 1)
    (g : ((homogeneousCochains R G).obj B).X 1)
    (x y z : G) :
    rawCup p f g x y z =
      p.toLinearMap (oneValue f x y) (oneValue g y z) :=
  rfl

/-- The raw cup bundled as an invariant homogeneous degree-two cochain. -/
def cupCochain
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).X 1)
    (g : ((homogeneousCochains R G).obj B).X 1) :
    ((homogeneousCochains R G).obj C).X 2 := by
  refine ⟨rawCup p f g, ?_⟩
  intro a
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.ext
  intro z
  change (C.ρ a).hom
      (p.toLinearMap (oneValue f (a⁻¹ * x) (a⁻¹ * y))
        (oneValue g (a⁻¹ * y) (a⁻¹ * z))) =
    p.toLinearMap (oneValue f x y) (oneValue g y z)
  rw [← p.equivariant, oneValue_invariant f, oneValue_invariant g]

@[simp]
theorem cupCochain_apply
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).X 1)
    (g : ((homogeneousCochains R G).obj B).X 1)
    (x y z : G) :
    twoValue (cupCochain p f g) x y z =
      p.toLinearMap (oneValue f x y) (oneValue g y z) :=
  rfl

/-- The cup of two homogeneous one-cocycles is a homogeneous two-cocycle. -/
theorem cupCochain_isCycle
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).X 1)
    (g : ((homogeneousCochains R G).obj B).X 1)
    (hf : (((homogeneousCochains R G).obj A).d 1 2).hom f = 0)
    (hg : (((homogeneousCochains R G).obj B).d 1 2).hom g = 0) :
    (((homogeneousCochains R G).obj C).d 2 3).hom
      (cupCochain p f g) = 0 := by
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
    p.toLinearMap (oneValue f x y) (oneValue g y z) -
        (p.toLinearMap (oneValue f w y) (oneValue g y z) -
          (p.toLinearMap (oneValue f w x) (oneValue g x z) -
            p.toLinearMap (oneValue f w x) (oneValue g x y))) = 0
  have hf' := oneCycle_identity f hf w x y
  have hg' := oneCycle_identity g hg x y z
  apply sub_eq_zero.mpr
  rw [sub_eq_iff_eq_add] at hf'
  rw [sub_eq_iff_eq_add] at hg'
  simp only [zero_add] at hf' hg'
  rw [hf', hg']
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- The raw cup is bilinear on degree-one homogeneous cochains. -/
def cupCochainLinear
    (p : ContinuousEquivariantPairing A B C) :
    (((homogeneousCochains R G).obj A).X 1) →ₗ[R]
      (((homogeneousCochains R G).obj B).X 1) →ₗ[R]
        (((homogeneousCochains R G).obj C).X 2) :=
  LinearMap.mk₂ R (cupCochain p)
    (by
      intro f₁ f₂ g
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      apply ContinuousMap.ext
      intro y
      apply ContinuousMap.ext
      intro z
      change p.toLinearMap
          (oneValue f₁ x y + oneValue f₂ x y) (oneValue g y z) =
        p.toLinearMap (oneValue f₁ x y) (oneValue g y z) +
          p.toLinearMap (oneValue f₂ x y) (oneValue g y z)
      exact LinearMap.congr_fun
        (p.toLinearMap.map_add (oneValue f₁ x y) (oneValue f₂ x y))
        (oneValue g y z))
    (by
      intro r f g
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      apply ContinuousMap.ext
      intro y
      apply ContinuousMap.ext
      intro z
      change p.toLinearMap (r • oneValue f x y) (oneValue g y z) =
        r • p.toLinearMap (oneValue f x y) (oneValue g y z)
      exact LinearMap.congr_fun
        (p.toLinearMap.map_smul r (oneValue f x y)) (oneValue g y z))
    (by
      intro f g₁ g₂
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      apply ContinuousMap.ext
      intro y
      apply ContinuousMap.ext
      intro z
      change p.toLinearMap (oneValue f x y)
          (oneValue g₁ y z + oneValue g₂ y z) =
        p.toLinearMap (oneValue f x y) (oneValue g₁ y z) +
          p.toLinearMap (oneValue f x y) (oneValue g₂ y z)
      exact (p.toLinearMap (oneValue f x y)).map_add _ _)
    (by
      intro r f g
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      apply ContinuousMap.ext
      intro y
      apply ContinuousMap.ext
      intro z
      change p.toLinearMap (oneValue f x y) (r • oneValue g y z) =
        r • p.toLinearMap (oneValue f x y) (oneValue g y z)
      exact (p.toLinearMap (oneValue f x y)).map_smul r (oneValue g y z))

/-! ## Explicit primitives for cups with degree-one boundaries -/

/-- The degree-one primitive `β(a(x),g(x,y))` used when the left input is a
degree-zero boundary. -/
def cupZeroOne
    (p : ContinuousEquivariantPairing A B C)
    (a : ((homogeneousCochains R G).obj A).X 0)
    (g : ((homogeneousCochains R G).obj B).X 1) :
    ((homogeneousCochains R G).obj C).X 1 := by
  let F : C(G × G, C.V) :=
    ⟨fun xy => p.toLinearMap (zeroValue a xy.1) (oneValue g xy.1 xy.2), by
      have hg : Continuous (fun xy : G × G => oneValue g xy.1 xy.2) :=
        ContinuousMap.continuous_uncurry_of_continuous (oneValue g)
      exact p.continuous_uncurry.comp
        (Continuous.prodMk ((zeroValue a).continuous.comp continuous_fst) hg)⟩
  refine ⟨ContinuousMap.curry F, ?_⟩
  intro q
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change (C.ρ q).hom
      (p.toLinearMap (zeroValue a (q⁻¹ * x))
        (oneValue g (q⁻¹ * x) (q⁻¹ * y))) =
    p.toLinearMap (zeroValue a x) (oneValue g x y)
  rw [← p.equivariant, zeroValue_invariant a, oneValue_invariant g]

@[simp]
theorem cupZeroOne_apply
    (p : ContinuousEquivariantPairing A B C)
    (a : ((homogeneousCochains R G).obj A).X 0)
    (g : ((homogeneousCochains R G).obj B).X 1) (x y : G) :
    oneValue (cupZeroOne p a g) x y =
      p.toLinearMap (zeroValue a x) (oneValue g x y) :=
  rfl

/-- The signed degree-one primitive `-β(f(x,y),b(y))` used when the right
input is a degree-zero boundary.

It is constructed pointwise instead of by negating the entire bundled
cochain; this keeps elaboration of the nested continuous-map type tractable. -/
def cupOneZeroNegative
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).X 1)
    (b : ((homogeneousCochains R G).obj B).X 0) :
    ((homogeneousCochains R G).obj C).X 1 := by
  let F : C(G × G, C.V) :=
    ⟨fun xy =>
        -(p.toLinearMap (oneValue f xy.1 xy.2) (zeroValue b xy.2)), by
      have hf : Continuous (fun xy : G × G => oneValue f xy.1 xy.2) :=
        ContinuousMap.continuous_uncurry_of_continuous (oneValue f)
      exact (p.continuous_uncurry.comp
        (Continuous.prodMk hf
          ((zeroValue b).continuous.comp continuous_snd))).neg⟩
  refine ⟨ContinuousMap.curry F, ?_⟩
  intro q
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change (C.ρ q).hom
      (-(p.toLinearMap (oneValue f (q⁻¹ * x) (q⁻¹ * y))
        (zeroValue b (q⁻¹ * y)))) =
    -(p.toLinearMap (oneValue f x y) (zeroValue b y))
  rw [map_neg, ← p.equivariant, oneValue_invariant f,
    zeroValue_invariant b]

@[simp]
theorem cupOneZeroNegative_apply
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).X 1)
    (b : ((homogeneousCochains R G).obj B).X 0) (x y : G) :
    oneValue (cupOneZeroNegative p f b) x y =
      -(p.toLinearMap (oneValue f x y) (zeroValue b y)) :=
  rfl

/-- Cup with a left degree-zero boundary is the boundary of the explicit
`cupZeroOne` primitive. -/
theorem cupCochain_zeroBoundary_left
    (p : ContinuousEquivariantPairing A B C)
    (a : ((homogeneousCochains R G).obj A).X 0)
    (g : ((homogeneousCochains R G).obj B).X 1)
    (hg : (((homogeneousCochains R G).obj B).d 1 2).hom g = 0) :
    @Eq (((homogeneousCochains R G).obj C).X 2)
      (cupCochain p
        ((((homogeneousCochains R G).obj A).d 0 1).hom a) g)
      ((((homogeneousCochains R G).obj C).d 1 2).hom
        (cupZeroOne p a g)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change p.toLinearMap (zeroValue a x - zeroValue a w) (oneValue g x y) =
    p.toLinearMap (zeroValue a x) (oneValue g x y) -
      (p.toLinearMap (zeroValue a w) (oneValue g w y) -
        p.toLinearMap (zeroValue a w) (oneValue g w x))
  have hg' := sub_eq_zero.mp (oneCycle_identity g hg w x y)
  have hg'' : oneValue g w y = oneValue g x y + oneValue g w x :=
    ((eq_sub_iff_add_eq).mp hg').symm
  rw [hg'']
  simp only [map_sub, map_add, LinearMap.sub_apply]
  abel

/-- Cup with a right degree-zero boundary is the boundary of the explicit
signed `cupOneZeroNegative` primitive. -/
theorem cupCochain_zeroBoundary_right
    (p : ContinuousEquivariantPairing A B C)
    (f : ((homogeneousCochains R G).obj A).X 1)
    (hf : (((homogeneousCochains R G).obj A).d 1 2).hom f = 0)
    (b : ((homogeneousCochains R G).obj B).X 0) :
    @Eq (((homogeneousCochains R G).obj C).X 2)
      (cupCochain p f
        ((((homogeneousCochains R G).obj B).d 0 1).hom b))
      ((((homogeneousCochains R G).obj C).d 1 2).hom
        (cupOneZeroNegative p f b)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change p.toLinearMap (oneValue f w x) (zeroValue b y - zeroValue b x) =
    -(p.toLinearMap (oneValue f x y) (zeroValue b y)) -
      (-(p.toLinearMap (oneValue f w y) (zeroValue b y)) -
        (-(p.toLinearMap (oneValue f w x) (zeroValue b x))))
  have hf' := sub_eq_zero.mp (oneCycle_identity f hf w x y)
  rw [hf']
  simp only [map_sub, LinearMap.sub_apply]
  abel

end LocallyCompact

end Fermat.Conservation.ContinuousKummerTateCupRaw
