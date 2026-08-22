/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The coefficient algebra for the continuous Kummer--Tate pairing

A chosen primitive root orients the left Kummer class into the trivial
`ZMod n` line.  Scalar multiplication then gives the jointly continuous,
equivariant coefficient pairing

`ZMod n x mu_n -> mu_n`.

This file packages that coefficient algebra and the final specialization
adapter from any descended continuous `H^1 x H^1 -> H^2` cup product to
Kummer classes.  The output deliberately retains its roots-of-unity-valued
degree-two cohomology type.  No local invariant, Tate-duality theorem,
Hilbert-symbol comparison, or global lifting theorem is asserted here.
-/
import Fermat.Experiments.Conservation.ContinuousKummerOrientation
import Fermat.Experiments.Conservation.ContinuousKummerTateCup
import Mathlib.FieldTheory.Galois.Profinite

noncomputable section

namespace Fermat.Conservation.ContinuousKummerTateAlgebra

open CategoryTheory
open ContinuousKummerH1
open ContinuousKummerOrientation
open ContinuousKummerTateCupRaw
open LocalKummerH1
open TameSymbol

open scoped LocalKummerH1.KummerRootsDiscrete

variable (n : ℕ) (F : Type) [Field F] [NeZero n]

/- Mathlib equips the absolute Galois group in characteristic zero with its
profinite topology.  Exposing compactness and separation under the concrete
automorphism-group presentation supplies the exact local-compactness input
needed by the continuous cup construction. -/
local instance absoluteGaloisCompactSpace [CharZero F] :
    CompactSpace (AbsoluteGalois F) := by
  change CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  infer_instance

local instance absoluteGaloisT2Space [CharZero F] :
    T2Space (AbsoluteGalois F) := by
  change T2Space (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  infer_instance

local instance rootsContinuousSMul :
    ContinuousSMul (ZMod n) (Additive (KummerRoots n F)) :=
  ⟨continuous_of_discreteTopology⟩

/-- Scalar multiplication of roots, typed as a jointly continuous,
equivariant pairing from the oriented line and the un-oriented roots module
back to the roots module. -/
def scalarTimesRootPairing :
    ContinuousEquivariantPairing
      (trivialTopLine n F) (rootsTopRepresentation n F)
      (rootsTopRepresentation n F) := by
  refine
    { toLinearMap := ?_
      continuous_uncurry := ?_
      equivariant := ?_ }
  · change ZMod n →ₗ[ZMod n]
      Additive (KummerRoots n F) →ₗ[ZMod n]
        Additive (KummerRoots n F)
    exact LinearMap.lsmul (ZMod n) (Additive (KummerRoots n F))
  · change Continuous
      (fun x : ZMod n × Additive (KummerRoots n F) => x.1 • x.2)
    exact continuous_smul
  · intro sigma a b
    have h := smul_comm sigma (show ZMod n from a)
      (show Additive (KummerRoots n F) from b)
    exact h.symm

@[simp]
theorem scalarTimesRootPairing_apply
    (a : (trivialTopLine n F).V)
    (b : (rootsTopRepresentation n F).V) :
    (scalarTimesRootPairing n F).toLinearMap a b = a • b :=
  rfl

/-- Genuine continuous degree-two cohomology retaining its
roots-of-unity coefficient type. -/
abbrev ContinuousKummerCohomologyTwo :=
  (continuousCohomology (ZMod n) (AbsoluteGalois F) 2).obj
    (rootsTopRepresentation n F)

/-- Conditional, noncanonical normalization of a linear readout at a supplied
nonzero continuous Kummer `H²` class.

This is only linear algebra over the prime field `ZMod n`: it neither produces
the nonzero class nor identifies the chosen readout with a local invariant or
any other arithmetic normalization. -/
theorem exists_conditionalNoncanonicalReadout_eq_one
    [Fact (Nat.Prime n)]
    (z : ContinuousKummerCohomologyTwo n F) (hz : z ≠ 0) :
    ∃ readout : ContinuousKummerCohomologyTwo n F →ₗ[ZMod n] ZMod n,
      readout z = 1 :=
  Module.Projective.exists_dual_eq_one (ZMod n) hz

/-- Compose any descended bilinear continuous-`H¹` cup product with the
oriented left and un-oriented right Kummer maps.

Keeping the cup product as an explicit input makes this a reusable adapter;
`kummerPairing` below supplies the canonical descended cup. -/
def kummerPairingFromCup
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (cup : OrientedContinuousH1 n F →ₗ[ZMod n]
      ContinuousKummerCohomologyOne n F →ₗ[ZMod n]
        ContinuousKummerCohomologyTwo n F) :
    KummerClass n F →+ KummerClass n F →+
      ContinuousKummerCohomologyTwo n F where
  toFun x := (cup (leftKummerMap n F zeta hzeta x)).toAddMonoidHom.comp
    (rightKummerMap n F)
  map_zero' := by
    ext y
    simp
  map_add' x y := by
    ext z
    simp

@[simp]
theorem kummerPairingFromCup_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (cup : OrientedContinuousH1 n F →ₗ[ZMod n]
      ContinuousKummerCohomologyOne n F →ₗ[ZMod n]
        ContinuousKummerCohomologyTwo n F)
    (x y : KummerClass n F) :
    kummerPairingFromCup n F zeta hzeta cup x y =
      cup (leftKummerMap n F zeta hzeta x) (rightKummerMap n F y) :=
  rfl

variable [CharZero F]

/-- The actual continuous cup specialized to the oriented scalar/root
coefficient pairing. -/
def kummerCupH1 :
    OrientedContinuousH1 n F →ₗ[ZMod n]
      ContinuousKummerCohomologyOne n F →ₗ[ZMod n]
        ContinuousKummerCohomologyTwo n F :=
  Fermat.Conservation.ContinuousKummerTateCup.cupH1
    (scalarTimesRootPairing n F)

/-- The canonical roots-valued continuous Kummer--Tate `H²` pairing. -/
def kummerPairing
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n) :
    KummerClass n F →+ KummerClass n F →+
      ContinuousKummerCohomologyTwo n F :=
  kummerPairingFromCup n F zeta hzeta (kummerCupH1 n F)

@[simp]
theorem kummerPairing_apply
    (zeta : F) (hzeta : IsPrimitiveRoot zeta n)
    (x y : KummerClass n F) :
    kummerPairing n F zeta hzeta x y =
      kummerCupH1 n F
        (leftKummerMap n F zeta hzeta x)
        (rightKummerMap n F y) :=
  rfl

end Fermat.Conservation.ContinuousKummerTateAlgebra
