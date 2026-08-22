/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Orienting the Kummer roots by a chosen primitive root

If a field `F` contains a chosen primitive `n`-th root of unity, its absolute
Galois group fixes every `n`-th root of unity.  The chosen root consequently
identifies the roots-of-unity representation with the trivial `ZMod n` line.

This file constructs that identification from the primitive root itself and
uses functoriality of group cohomology to turn the ordinary Kummer class in
`H¹(G_F, μ_n)` into the oriented left class in `H¹(G_F, ZMod n)` needed by
the Kummer--Tate cup product.  No coordinate or pairing value is chosen beyond
the explicitly supplied primitive root.
-/
import Fermat.Experiments.Conservation.LocalKummerH1
import Fermat.Experiments.Conservation.KummerTateCup
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

noncomputable section

namespace Fermat.Conservation.KummerOrientation

open CategoryTheory
open groupCohomology

open Fermat.Conservation
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.TameSymbol

variable (n : ℕ) (F : Type) [Field F] [NeZero n]

/-- The chosen primitive root, bundled as a unit of the base field. -/
def primitiveUnit (zeta : F) (hzeta : IsPrimitiveRoot zeta n) : Fˣ :=
  (hzeta.isUnit (NeZero.ne n)).unit

/-- The chosen primitive root after embedding it into the fixed algebraic
closure used by `LocalKummerH1`. -/
def algebraicPrimitiveUnit (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    (AlgebraicClosure F)ˣ :=
  Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom
    (primitiveUnit n F zeta hzeta)

/-- Primitivity is preserved by the algebraic-closure embedding. -/
theorem algebraicPrimitiveUnit_isPrimitive
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    IsPrimitiveRoot (algebraicPrimitiveUnit n F zeta hzeta) n := by
  exact (hzeta.isUnit_unit (NeZero.ne n)).map_of_injective
    (Units.map_injective (algebraMap F (AlgebraicClosure F)).injective)

/-- All algebraic-closure `n`-th roots of unity, identified with powers of the
chosen embedded primitive root. -/
def rootsEquivZPowers
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    KummerRoots n F ≃* Subgroup.zpowers
      (algebraicPrimitiveUnit n F zeta hzeta) :=
  MulEquiv.subgroupCongr
    (algebraicPrimitiveUnit_isPrimitive n F zeta hzeta).zpowers_eq.symm

/-- Additive primitive-root coordinates on all `n`-th roots of unity. -/
def coordinateAddEquiv
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    Additive (KummerRoots n F) ≃+ ZMod n :=
  (MulEquiv.toAdditive (rootsEquivZPowers n F zeta hzeta)).trans
    (algebraicPrimitiveUnit_isPrimitive n F zeta hzeta).zmodEquivZPowers.symm

/-- The primitive-root coordinates are automatically `ZMod n`-linear, since
both module structures are the canonical ones on groups killed by `n`. -/
def coordinateLinearEquiv
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    Additive (KummerRoots n F) ≃ₗ[ZMod n] ZMod n :=
  LinearEquiv.ofBijective
    ((coordinateAddEquiv n F zeta hzeta).toAddMonoidHom.toZModLinearMap n)
    (coordinateAddEquiv n F zeta hzeta).bijective

/-- Because the primitive root lies in the base field, the absolute Galois
group fixes every `n`-th root of unity in the algebraic closure. -/
theorem absoluteGalois_smul_root_eq
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (sigma : AbsoluteGalois F) (eta : Additive (KummerRoots n F)) :
    sigma • eta = eta := by
  apply Additive.toMul.injective
  apply Subtype.ext
  have heta : (eta.toMul : (AlgebraicClosure F)ˣ) ∈
      Subgroup.zpowers (algebraicPrimitiveUnit n F zeta hzeta) := by
    rw [(algebraicPrimitiveUnit_isPrimitive n F zeta hzeta).zpowers_eq]
    exact eta.toMul.property
  obtain ⟨i, hi⟩ := heta
  change sigma • (eta.toMul : (AlgebraicClosure F)ˣ) = eta.toMul
  rw [← hi, smul_zpow']
  congr 1
  apply Units.ext
  exact sigma.commutes ((primitiveUnit n F zeta hzeta : F))

/-- The chosen root gives an equivariant linear equivalence between the
roots-of-unity representation and the trivial coefficient line. -/
def rootsRepresentationEquivTrivial
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    rootsRepresentation n F ≅
      KummerTateCup.trivialLine
        (k := ZMod n) (G := AbsoluteGalois F) :=
  Rep.mkIso <| Representation.Equiv.mk
    (coordinateLinearEquiv n F zeta hzeta) <| by
      intro sigma
      ext eta
      change coordinateLinearEquiv n F zeta hzeta (sigma • eta) =
        coordinateLinearEquiv n F zeta hzeta eta
      rw [absoluteGalois_smul_root_eq n F zeta hzeta]

/-- Functoriality of group cohomology transports a Kummer `H¹` class through
the chosen-root orientation into the trivial coefficient line. -/
def orientH1
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    DiscreteKummerH1 n F →ₗ[ZMod n]
      H1 (KummerTateCup.trivialLine
        (k := ZMod n) (G := AbsoluteGalois F)) :=
  (groupCohomology.map (MonoidHom.id (AbsoluteGalois F))
      (rootsRepresentationEquivTrivial n F zeta hzeta).hom 1).hom

/-- Readback of the oriented cohomology map on a concrete Kummer cocycle. -/
@[simp]
theorem orientH1_H1pi
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (c : cocycles₁ (rootsRepresentation n F)) :
    orientH1 n F zeta hzeta (H1π (rootsRepresentation n F) c) =
      H1π (KummerTateCup.trivialLine
          (k := ZMod n) (G := AbsoluteGalois F))
        (groupCohomology.mapCocycles₁
          (MonoidHom.id (AbsoluteGalois F))
          (rootsRepresentationEquivTrivial n F zeta hzeta).hom c) := by
  change
    (groupCohomology.map (MonoidHom.id (AbsoluteGalois F))
        (rootsRepresentationEquivTrivial n F zeta hzeta).hom 1)
          (H1π (rootsRepresentation n F) c) = _
  rw [groupCohomology.H1π_comp_map_apply]

/-- Functoriality in the coefficient representation transports degree-two
cohomology through the same chosen-root orientation.  This only removes the
`mu_n`/`ZMod n` coordinate bookkeeping: it does not construct or normalize a
local invariant on `H²`. -/
def orientH2
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    H2 (rootsRepresentation n F) →ₗ[ZMod n]
      H2 (KummerTateCup.trivialLine
        (k := ZMod n) (G := AbsoluteGalois F)) :=
  (groupCohomology.map (MonoidHom.id (AbsoluteGalois F))
      (rootsRepresentationEquivTrivial n F zeta hzeta).hom 2).hom

/-- Readback of the degree-two orientation on a concrete two-cocycle. -/
@[simp]
theorem orientH2_H2pi
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (c : cocycles₂ (rootsRepresentation n F)) :
    orientH2 n F zeta hzeta (H2π (rootsRepresentation n F) c) =
      H2π (KummerTateCup.trivialLine
          (k := ZMod n) (G := AbsoluteGalois F))
        (groupCohomology.mapCocycles₂
          (MonoidHom.id (AbsoluteGalois F))
          (rootsRepresentationEquivTrivial n F zeta hzeta).hom c) := by
  change
    (groupCohomology.map (MonoidHom.id (AbsoluteGalois F))
        (rootsRepresentationEquivTrivial n F zeta hzeta).hom 2)
          (H2π (rootsRepresentation n F) c) = _
  rw [groupCohomology.H2π_comp_map_apply]

/-- The ordinary Kummer map followed by the honest chosen-root orientation.
This is the additive left Kummer map used by the oriented cup product. -/
def leftKummerMap
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    KummerClass n F →+
      H1 (KummerTateCup.trivialLine
        (k := ZMod n) (G := AbsoluteGalois F)) :=
  (orientH1 n F zeta hzeta).toAddMonoidHom.comp (LocalKummerH1.map n F)

/-- Readback of the left Kummer map on a nonzero field representative. -/
@[simp]
theorem leftKummerMap_classOfUnit
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) (a : Fˣ) :
    leftKummerMap n F zeta hzeta
        (Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom n : Fˣ →* Fˣ).range a)) =
      orientH1 n F zeta hzeta (LocalKummerH1.classOfUnit n F a) := by
  rfl

end Fermat.Conservation.KummerOrientation
