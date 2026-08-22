/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Orienting the continuous Kummer class

A chosen primitive `n`-th root in the base field continuously identifies the
roots-of-unity coefficient representation with the trivial topological
`ZMod n` line.  Continuous-cohomology functoriality then transports the
genuine continuous Kummer class into oriented coordinates.

This file only changes coefficients.  It does not compare continuous and
discrete cohomology, construct a cup product or local invariant, or identify
the un-oriented right Kummer class with the oriented left class.
-/
import Fermat.Experiments.Conservation.ContinuousKummerH1
import Fermat.Experiments.Conservation.KummerOrientation

noncomputable section

namespace Fermat.Conservation.ContinuousKummerOrientation

open CategoryTheory
open Fermat.Conservation.KummerOrientation
open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.TameSymbol

open scoped LocalKummerH1.KummerRootsDiscrete

variable (n : ℕ) (F : Type) [Field F] [NeZero n]

/- The coefficient line has its canonical discrete topology.  Recording
joint continuity locally keeps this file independent of any exported
topology choice. -/
local instance zmodContinuousSMul : ContinuousSMul (ZMod n) (ZMod n) :=
  ⟨continuous_of_discreteTopology⟩

/-- The topological `ZMod n` line with trivial absolute-Galois action. -/
def trivialTopLine :
    Action (TopModuleCat (ZMod n)) (AbsoluteGalois F) :=
  Action.trivial (AbsoluteGalois F) (TopModuleCat.of (ZMod n) (ZMod n))

/-- Primitive-root coordinates, upgraded to a continuous linear
equivalence.  Both coefficient modules carry their canonical discrete
topologies, so the algebraic coordinate equivalence and its inverse are
automatically continuous. -/
def coordinateContinuousLinearEquiv
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    (rootsTopRepresentation n F).V ≃L[ZMod n] (trivialTopLine n F).V := by
  change Additive (KummerRoots n F) ≃L[ZMod n] ZMod n
  exact
    { __ := coordinateLinearEquiv n F zeta hzeta
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The primitive root gives an equivariant coefficient isomorphism from
the continuous roots-of-unity representation to the trivial topological
line. -/
def rootsTopRepresentationEquivTrivial
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    rootsTopRepresentation n F ≅ trivialTopLine n F :=
  Action.mkIso
    (TopModuleCat.ofIso (coordinateContinuousLinearEquiv n F zeta hzeta)) <| by
      intro sigma
      apply ConcreteCategory.ext
      apply ContinuousLinearMap.ext
      intro eta
      have hfix := absoluteGalois_smul_root_eq n F zeta hzeta sigma
        (show Additive (KummerRoots n F) from eta)
      exact congrArg (coordinateLinearEquiv n F zeta hzeta) hfix

/-- Genuine continuous degree-one cohomology with trivial oriented
coefficients. -/
abbrev OrientedContinuousH1 :=
  (continuousCohomology (ZMod n) (AbsoluteGalois F) 1).obj
    (trivialTopLine n F)

/-- Genuine continuous degree-two cohomology with trivial oriented
coefficients.  This is only a coefficient target; no local invariant is
installed here. -/
abbrev OrientedContinuousH2 :=
  (continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
    (trivialTopLine n F)

/-- Continuous-cohomology functoriality transports degree-one classes
through the chosen primitive-root coordinates. -/
def orientH1
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    ContinuousKummerCohomologyOne n F →L[ZMod n]
      OrientedContinuousH1 n F :=
  ((continuousCohomology (ZMod n) (AbsoluteGalois F) 1).map
    (rootsTopRepresentationEquivTrivial n F zeta hzeta).hom).hom

/-- The degree-one orientation is itself a continuous linear
equivalence. -/
def orientH1Equiv
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    ContinuousKummerCohomologyOne n F ≃L[ZMod n]
      OrientedContinuousH1 n F :=
  ((continuousCohomology (ZMod n) (AbsoluteGalois F) 1).mapIso
    (rootsTopRepresentationEquivTrivial n F zeta hzeta)).toContinuousLinearEquiv

/-- Continuous-cohomology functoriality transports degree-two classes
through the same coefficient orientation. -/
def orientH2
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
        (rootsTopRepresentation n F)) →L[ZMod n]
      OrientedContinuousH2 n F :=
  ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).map
    (rootsTopRepresentationEquivTrivial n F zeta hzeta).hom).hom

/-- The degree-two coefficient orientation is itself a continuous linear
equivalence.  This changes coordinates without scalarizing the retained
cohomology class. -/
def orientH2Equiv
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
        (rootsTopRepresentation n F)) ≃L[ZMod n]
      OrientedContinuousH2 n F :=
  ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).mapIso
    (rootsTopRepresentationEquivTrivial n F zeta hzeta)).toContinuousLinearEquiv

/-- Readback of the degree-two orientation equivalence through the existing
continuous linear map. -/
@[simp]
theorem orientH2Equiv_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (x : ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
      (rootsTopRepresentation n F))) :
    orientH2Equiv n F zeta hzeta x = orientH2 n F zeta hzeta x :=
  rfl

/-- Scalar readouts in oriented coordinates are linearly equivalent to
scalar readouts on roots-valued degree-two cohomology.  This only transports
supplied maps through `orientH2Equiv`; it does not construct a readout. -/
def orientH2ReadoutEquiv
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    (OrientedContinuousH2 n F →ₗ[ZMod n] ZMod n) ≃ₗ[ZMod n]
      (((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
        (rootsTopRepresentation n F)) →ₗ[ZMod n] ZMod n) :=
  (orientH2Equiv n F zeta hzeta).symm.toLinearEquiv.arrowCongr
    (LinearEquiv.refl (ZMod n) (ZMod n))

/-- Applying the transported linear readout means orienting the retained
degree-two class first. -/
@[simp]
theorem orientH2ReadoutEquiv_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (readout : OrientedContinuousH2 n F →ₗ[ZMod n] ZMod n)
    (x : ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
      (rootsTopRepresentation n F))) :
    orientH2ReadoutEquiv n F zeta hzeta readout x =
      readout (orientH2Equiv n F zeta hzeta x) :=
  rfl

/-- The inverse transport evaluates a roots-valued readout after applying
the inverse degree-two orientation. -/
@[simp]
theorem orientH2ReadoutEquiv_symm_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (readout :
      ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
        (rootsTopRepresentation n F)) →ₗ[ZMod n] ZMod n)
    (x : OrientedContinuousH2 n F) :
    (orientH2ReadoutEquiv n F zeta hzeta).symm readout x =
      readout ((orientH2Equiv n F zeta hzeta).symm x) :=
  rfl

/-- The same lossless transport for topology-preserving scalar readouts.
The equivalence itself is linear on the two spaces of continuous linear maps;
it still supplies no distinguished element of either space. -/
def orientH2ContinuousReadoutEquiv
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    (OrientedContinuousH2 n F →L[ZMod n] ZMod n) ≃ₗ[ZMod n]
      (((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
        (rootsTopRepresentation n F)) →L[ZMod n] ZMod n) :=
  (orientH2Equiv n F zeta hzeta).symm.arrowCongrEquivₛₗ
    (ContinuousLinearEquiv.refl (ZMod n) (ZMod n))

/-- Application of the transported topology-preserving readout. -/
@[simp]
theorem orientH2ContinuousReadoutEquiv_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (readout : OrientedContinuousH2 n F →L[ZMod n] ZMod n)
    (x : ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
      (rootsTopRepresentation n F))) :
    orientH2ContinuousReadoutEquiv n F zeta hzeta readout x =
      readout (orientH2Equiv n F zeta hzeta x) :=
  rfl

/-- Inverse application of the transported topology-preserving readout. -/
@[simp]
theorem orientH2ContinuousReadoutEquiv_symm_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (readout :
      ((continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
        (rootsTopRepresentation n F)) →L[ZMod n] ZMod n)
    (x : OrientedContinuousH2 n F) :
    (orientH2ContinuousReadoutEquiv n F zeta hzeta).symm readout x =
      readout ((orientH2Equiv n F zeta hzeta).symm x) :=
  rfl

/-- The un-oriented right Kummer map.  Its coefficient object remains
`mu_n`; it is deliberately not identified with the oriented left target. -/
def rightKummerMap :
    KummerClass n F →+ ContinuousKummerCohomologyOne n F :=
  ContinuousKummerH1.continuousMap n F

/-- Readback of the un-oriented right Kummer map. -/
@[simp]
theorem rightKummerMap_classOfUnit (a : Fˣ) :
    rightKummerMap n F
        (Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom n : Fˣ →* Fˣ).range a)) =
      ContinuousKummerH1.continuousClassOfUnit n F a := by
  rfl

/-- The ordinary genuine continuous Kummer map followed by the chosen-root
orientation.  This is the oriented left Kummer map; the original
`ContinuousKummerH1.continuousMap` remains the separate, un-oriented right
Kummer map. -/
def leftKummerMap
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    KummerClass n F →+ OrientedContinuousH1 n F :=
  (orientH1 n F zeta hzeta).toLinearMap.toAddMonoidHom.comp
    (rightKummerMap n F)

/-- Readback of the oriented left Kummer map on a nonzero field
representative. -/
@[simp]
theorem leftKummerMap_classOfUnit
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) (a : Fˣ) :
    leftKummerMap n F zeta hzeta
        (Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom n : Fˣ →* Fˣ).range a)) =
      orientH1 n F zeta hzeta
        (ContinuousKummerH1.continuousClassOfUnit n F a) := by
  rfl

end Fermat.Conservation.ContinuousKummerOrientation
