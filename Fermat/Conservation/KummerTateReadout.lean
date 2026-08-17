/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The oriented Kummer--Tate scalar readout

The low-degree cup product retains the interaction of two degree-one classes
as a class in `H²`.  A local invariant followed by an oriented discrete
logarithm is linear, so composing it with that cup product gives the scalar
pairing

`(Additive G →+ k) →ₗ[k] H¹(G,A) →ₗ[k] k`.

The local invariant is supplied as actual data.  This file neither postulates
one nor assigns it fabricated values; constructing and calibrating the
arithmetic local invariant remains a separate theorem-level obligation.
-/
import Fermat.Conservation.KummerTateCup

noncomputable section

namespace Fermat.Conservation.KummerTateReadout

open groupCohomology
open KummerTateCup

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G)

/-- For a fixed oriented left character, compose cup product with the supplied
linear local invariant to obtain a scalar readout on right `H¹` classes. -/
def orientedReadoutRight
    (localInvariant : H2 A →ₗ[k] k) (f : Additive G →+ k) :
    H1 A →ₗ[k] k :=
  localInvariant.comp (orientedCupH1 A f)

@[simp]
theorem orientedReadoutRight_apply
    (localInvariant : H2 A →ₗ[k] k) (f : Additive G →+ k) (x : H1 A) :
    orientedReadoutRight A localInvariant f x =
      localInvariant (orientedCupH1 A f x) :=
  rfl

/-- The oriented cup/invariant construction as an honest bilinear scalar
pairing. -/
def orientedReadout (localInvariant : H2 A →ₗ[k] k) :
    (Additive G →+ k) →ₗ[k] H1 A →ₗ[k] k where
  toFun := orientedReadoutRight A localInvariant
  map_add' f₁ f₂ := by
    ext x
    change localInvariant (orientedCupH1 A (f₁ + f₂) x) =
      localInvariant (orientedCupH1 A f₁ x) +
        localInvariant (orientedCupH1 A f₂ x)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' c f := by
    ext x
    change localInvariant (orientedCupH1 A (c • f) x) =
      c • localInvariant (orientedCupH1 A f x)
    rw [map_smul, LinearMap.smul_apply, map_smul]

@[simp]
theorem orientedReadout_apply
    (localInvariant : H2 A →ₗ[k] k) (f : Additive G →+ k) (x : H1 A) :
    orientedReadout A localInvariant f x =
      localInvariant (orientedCupH1 A f x) :=
  rfl

/-- Concrete readback on a right one-cocycle: cup first, pass to `H²`, and
only then apply the supplied local invariant. -/
@[simp]
theorem orientedReadout_H1π
    (localInvariant : H2 A →ₗ[k] k)
    (f : Additive G →+ k) (g : cocycles₁ A) :
    orientedReadout A localInvariant f (H1π A g) =
      localInvariant (H2π A (orientedCupCocycle A f g)) := by
  rw [orientedReadout_apply, orientedCupH1_apply_H1π]

@[simp]
theorem orientedReadout_zero_invariant :
    orientedReadout A (0 : H2 A →ₗ[k] k) = 0 := by
  ext f x
  rfl

theorem orientedReadout_add_invariant
    (localInvariant₁ localInvariant₂ : H2 A →ₗ[k] k) :
    orientedReadout A (localInvariant₁ + localInvariant₂) =
      orientedReadout A localInvariant₁ + orientedReadout A localInvariant₂ := by
  ext f x
  rfl

theorem orientedReadout_smul_invariant
    (c : k) (localInvariant : H2 A →ₗ[k] k) :
    orientedReadout A (c • localInvariant) =
      c • orientedReadout A localInvariant := by
  ext f x
  rfl

/-- Postprocessing the local invariant is the same as postprocessing every
scalar pairing value. -/
theorem orientedReadout_postcomp
    (post : k →ₗ[k] k) (localInvariant : H2 A →ₗ[k] k)
    (f : Additive G →+ k) (x : H1 A) :
    orientedReadout A (post.comp localInvariant) f x =
      post (orientedReadout A localInvariant f x) :=
  rfl

/-- The scalar readout with both probe and meter presented as genuine `H¹`
classes.  The left trivial-coefficient class is converted through Mathlib's
canonical `H¹ ≅ Hom` isomorphism before applying the oriented cup product. -/
def orientedReadoutClasses (localInvariant : H2 A →ₗ[k] k) :
    H1 (KummerTateCup.trivialLine (k := k) (G := G)) →ₗ[k]
      H1 A →ₗ[k] k :=
  (orientedReadout A localInvariant).comp
    (H1IsoOfIsTrivial
      (KummerTateCup.trivialLine (k := k) (G := G))).hom.hom

@[simp]
theorem orientedReadoutClasses_apply
    (localInvariant : H2 A →ₗ[k] k)
    (left : H1 (KummerTateCup.trivialLine (k := k) (G := G)))
    (right : H1 A) :
    orientedReadoutClasses A localInvariant left right =
      localInvariant (KummerTateCup.orientedCupH1Classes A left right) :=
  rfl

end Fermat.Conservation.KummerTateReadout
