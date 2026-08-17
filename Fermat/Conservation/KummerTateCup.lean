/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The oriented low-degree Kummer--Tate cup product

This file constructs the concrete inhomogeneous-cochain cup product needed
by the local Kummer--Tate route.  The left degree-one class has trivial
coefficients, hence is represented canonically by an additive character
`Additive G →+ k`.  The right degree-one class has coefficients in an
arbitrary `k`-linear representation `A`.

For cocycles `f` and `g`, the oriented cup cocycle is

`(sigma, tau) ↦ f(sigma) • sigma(g(tau))`.

The construction below proves directly that this is a two-cocycle and that
changing the right cocycle by a coboundary changes the cup by a
coboundary.  It therefore descends to an honest linear map

`H¹(G, A) → H²(G, A)`

for each oriented left character.  No local invariant, Kummer map, or
Tate-duality theorem is assumed here.
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

noncomputable section

namespace Fermat.Conservation.KummerTateCup

open CategoryTheory
open groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G)

/-- The inhomogeneous degree-two cup cochain
`(sigma,tau) ↦ f(sigma) • sigma(g(tau))`. -/
def orientedCupCochain
    (f : Additive G →+ k) (g : cocycles₁ A) : G × G → A :=
  fun st ↦ f (Additive.ofMul st.1) • A.ρ st.1 (g st.2)

/-- The oriented cup cochain of two one-cocycles is a two-cocycle. -/
theorem orientedCupCochain_mem_cocycles₂
    (f : Additive G →+ k) (g : cocycles₁ A) :
    orientedCupCochain A f g ∈ cocycles₂ A := by
  rw [mem_cocycles₂_iff]
  intro sigma tau upsilon
  change
    f (Additive.ofMul (sigma * tau)) •
          A.ρ (sigma * tau) (g upsilon) +
        f (Additive.ofMul sigma) • A.ρ sigma (g tau) =
      A.ρ sigma
          (f (Additive.ofMul tau) • A.ρ tau (g upsilon)) +
        f (Additive.ofMul sigma) • A.ρ sigma (g (tau * upsilon))
  rw [show f (Additive.ofMul (sigma * tau)) =
      f (Additive.ofMul sigma) + f (Additive.ofMul tau) by
        simp]
  rw [(mem_cocycles₁_iff g).mp g.property tau upsilon]
  simp only [add_smul, map_add, map_smul, map_mul, Module.End.mul_apply]
  module

/-- The bundled oriented cup two-cocycle. -/
def orientedCupCocycle
    (f : Additive G →+ k) (g : cocycles₁ A) : cocycles₂ A :=
  ⟨orientedCupCochain A f g, orientedCupCochain_mem_cocycles₂ A f g⟩

@[simp]
theorem orientedCupCocycle_apply
    (f : Additive G →+ k) (g : cocycles₁ A) (sigma tau : G) :
    orientedCupCocycle A f g (sigma, tau) =
      f (Additive.ofMul sigma) • A.ρ sigma (g tau) :=
  rfl

/-- For a fixed oriented left character, cup product is linear on right
one-cocycles. -/
def orientedCupCocyclesRight (f : Additive G →+ k) :
    cocycles₁ A →ₗ[k] cocycles₂ A where
  toFun := orientedCupCocycle A f
  map_add' g₁ g₂ := by
    ext sigma tau
    change f (Additive.ofMul sigma) •
        A.ρ sigma (g₁ tau + g₂ tau) =
      f (Additive.ofMul sigma) • A.ρ sigma (g₁ tau) +
        f (Additive.ofMul sigma) • A.ρ sigma (g₂ tau)
    rw [map_add, smul_add]
  map_smul' c g := by
    ext sigma tau
    change f (Additive.ofMul sigma) • A.ρ sigma (c • g tau) =
      c • (f (Additive.ofMul sigma) • A.ρ sigma (g tau))
    rw [map_smul, smul_smul, smul_smul, mul_comm]

/-- The explicit one-cochain whose coboundary is the cup with a right
one-coboundary.  The sign matches Mathlib's inhomogeneous differential. -/
def orientedCupCoboundaryPrimitive
    (f : Additive G →+ k) (m : A) : G → A :=
  fun sigma ↦ -(f (Additive.ofMul sigma) • A.ρ sigma m)

/-- Cup with the principal one-cocycle `d₀m` is the explicit coboundary of
`orientedCupCoboundaryPrimitive`. -/
theorem orientedCupCochain_d₀₁
    (f : Additive G →+ k) (m : A) :
    orientedCupCochain A f
        ⟨d₀₁ A m, d₀₁_apply_mem_cocycles₁ m⟩ =
      d₁₂ A (orientedCupCoboundaryPrimitive A f m) := by
  funext st
  rcases st with ⟨sigma, tau⟩
  change f (Additive.ofMul sigma) •
      A.ρ sigma (A.ρ tau m - m) =
    A.ρ sigma
        (-(f (Additive.ofMul tau) • A.ρ tau m)) -
      (-(f (Additive.ofMul (sigma * tau)) •
        A.ρ (sigma * tau) m)) +
      (-(f (Additive.ofMul sigma) • A.ρ sigma m))
  rw [show f (Additive.ofMul (sigma * tau)) =
      f (Additive.ofMul sigma) + f (Additive.ofMul tau) by
        simp]
  simp only [map_sub, smul_sub, map_neg, map_smul, map_mul,
    Module.End.mul_apply, add_smul]
  module

/-- A right one-coboundary cups to a two-coboundary. -/
theorem orientedCupCocycle_mem_coboundaries₂_of_mem_coboundaries₁
    (f : Additive G →+ k) (g : cocycles₁ A)
    (hg : (g : G → A) ∈ coboundaries₁ A) :
    (orientedCupCocycle A f g : G × G → A) ∈ coboundaries₂ A := by
  rw [coboundaries₁] at hg
  obtain ⟨m, hm⟩ := hg
  rw [coboundaries₂]
  refine ⟨orientedCupCoboundaryPrimitive A f m, ?_⟩
  rw [← orientedCupCochain_d₀₁ A f m]
  apply funext
  intro st
  change orientedCupCochain A f
      ⟨d₀₁ A m, d₀₁_apply_mem_cocycles₁ m⟩ st =
    orientedCupCochain A f g st
  rw [orientedCupCochain]
  congr 2
  exact congrFun hm st.2

/-- Project the oriented cup cocycle to second cohomology. -/
def orientedCupToH2 (f : Additive G →+ k) :
    cocycles₁ A →ₗ[k] H2 A :=
  (H2π A).hom.comp (orientedCupCocyclesRight A f)

@[simp]
theorem orientedCupToH2_apply
    (f : Additive G →+ k) (g : cocycles₁ A) :
    orientedCupToH2 A f g = H2π A (orientedCupCocycle A f g) :=
  rfl

/-- The projection to `H²` kills every right one-coboundary. -/
theorem orientedCupToH2_eq_zero_of_mem_coboundaries₁
    (f : Additive G →+ k) (g : cocycles₁ A)
    (hg : (g : G → A) ∈ coboundaries₁ A) :
    orientedCupToH2 A f g = 0 := by
  rw [orientedCupToH2_apply]
  exact (H2π_eq_zero_iff _).2
    (orientedCupCocycle_mem_coboundaries₂_of_mem_coboundaries₁ A f g hg)

/-- The kernel of the `H¹` quotient map is killed by cup product. -/
theorem ker_H1π_le_ker_orientedCupToH2 (f : Additive G →+ k) :
    LinearMap.ker (H1π A).hom ≤ LinearMap.ker (orientedCupToH2 A f) := by
  intro g hg
  rw [LinearMap.mem_ker] at hg ⊢
  exact orientedCupToH2_eq_zero_of_mem_coboundaries₁ A f g
    ((H1π_eq_zero_iff g).1 hg)

/-- The concrete cocycle projection onto `H¹` is surjective. -/
theorem H1π_hom_surjective : Function.Surjective (H1π A).hom :=
  (ModuleCat.epi_iff_surjective (H1π A)).1 inferInstance

/-- The oriented cup product descends from right one-cocycles to an honest
linear map `H¹(G,A) → H²(G,A)`. -/
noncomputable def orientedCupH1Right (f : Additive G →+ k) :
    H1 A →ₗ[k] H2 A :=
  ((LinearMap.ker (H1π A).hom).liftQ
      (orientedCupToH2 A f)
      (ker_H1π_le_ker_orientedCupToH2 A f)).comp
    (((H1π A).hom.quotKerEquivOfSurjective
      (H1π_hom_surjective A)).symm.toLinearMap)

/-- Readback of the descended cup product on a concrete cocycle. -/
@[simp]
theorem orientedCupH1Right_H1π
    (f : Additive G →+ k) (g : cocycles₁ A) :
    orientedCupH1Right A f (H1π A g) =
      H2π A (orientedCupCocycle A f g) := by
  simp [orientedCupH1Right, orientedCupToH2]
  rfl

@[simp]
theorem orientedCupCocycle_add_left
    (f₁ f₂ : Additive G →+ k) (g : cocycles₁ A) :
    orientedCupCocycle A (f₁ + f₂) g =
      orientedCupCocycle A f₁ g + orientedCupCocycle A f₂ g := by
  ext sigma tau
  change (f₁ (Additive.ofMul sigma) + f₂ (Additive.ofMul sigma)) •
      A.ρ sigma (g tau) =
    f₁ (Additive.ofMul sigma) • A.ρ sigma (g tau) +
      f₂ (Additive.ofMul sigma) • A.ρ sigma (g tau)
  rw [add_smul]

@[simp]
theorem orientedCupCocycle_smul_left
    (c : k) (f : Additive G →+ k) (g : cocycles₁ A) :
    orientedCupCocycle A (c • f) g =
      c • orientedCupCocycle A f g := by
  ext sigma tau
  change (c * f (Additive.ofMul sigma)) • A.ρ sigma (g tau) =
    c • (f (Additive.ofMul sigma) • A.ρ sigma (g tau))
  rw [smul_smul]

/-- The complete oriented low-degree cup product.  Its left input is the
canonical concrete model of `H¹` with trivial coefficients; its right input
is an arbitrary `H¹(G,A)` class. -/
noncomputable def orientedCupH1 :
    (Additive G →+ k) →ₗ[k] H1 A →ₗ[k] H2 A where
  toFun := orientedCupH1Right A
  map_add' f₁ f₂ := by
    ext x
    induction x using H1_induction_on with
    | _ g =>
      change orientedCupH1Right A (f₁ + f₂) (H1π A g) =
        orientedCupH1Right A f₁ (H1π A g) +
          orientedCupH1Right A f₂ (H1π A g)
      rw [orientedCupH1Right_H1π A (f₁ + f₂) g,
        orientedCupH1Right_H1π A f₁ g,
        orientedCupH1Right_H1π A f₂ g,
        orientedCupCocycle_add_left, map_add]
  map_smul' c f := by
    ext x
    induction x using H1_induction_on with
    | _ g =>
      change orientedCupH1Right A (c • f) (H1π A g) =
        c • orientedCupH1Right A f (H1π A g)
      rw [orientedCupH1Right_H1π A (c • f) g,
        orientedCupH1Right_H1π A f g,
        orientedCupCocycle_smul_left, map_smul]

/-- Concrete readback of the bilinear cup product. -/
@[simp]
theorem orientedCupH1_apply_H1π
    (f : Additive G →+ k) (g : cocycles₁ A) :
    orientedCupH1 A f (H1π A g) =
      H2π A (orientedCupCocycle A f g) :=
  orientedCupH1Right_H1π A f g

/-- The trivial coefficient line used for the oriented left `H¹` input. -/
abbrev trivialLine : Rep k G := Rep.trivial k G k

/-- The same cup product with both inputs presented as genuine cohomology
classes.  Mathlib canonically identifies `H¹` of the trivial coefficient line
with additive characters of `G`; no choice or quotient representative is
introduced here. -/
noncomputable def orientedCupH1Classes :
    H1 (trivialLine (k := k) (G := G)) →ₗ[k] H1 A →ₗ[k] H2 A :=
  (orientedCupH1 A).comp
    (H1IsoOfIsTrivial (trivialLine (k := k) (G := G))).hom.hom

@[simp]
theorem orientedCupH1Classes_apply
    (left : H1 (trivialLine (k := k) (G := G))) (right : H1 A) :
    orientedCupH1Classes A left right =
      orientedCupH1 A
        ((H1IsoOfIsTrivial (trivialLine (k := k) (G := G))).hom left)
        right :=
  rfl

end Fermat.Conservation.KummerTateCup
