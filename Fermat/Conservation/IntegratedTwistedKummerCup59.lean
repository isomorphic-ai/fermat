/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# From a concrete twisted C_(59²) lift to the genuine Kummer cup

This file feeds the second-digit identity from
`ConcreteTwistedLiftCupBridge59` through the homogeneous continuous-cochain
complex and the existing Kummer H¹/H² representative APIs.  Under explicit
pointwise reduction and cyclotomic twisted-action laws, it proves equality
between the pulled carry class and the genuine oriented Kummer cup in
Mathlib's actual continuous cohomology object.

The remaining producer is explicit and separate: this file does not
manufacture the compatible `mu_(59²)` coordinate `q`.  It requires a later
root-coordinate construction to supply `q`, `hred`, and `htwist`.
-/
import Fermat.Conservation.ConcreteTwistedLiftCupBridge59
import Fermat.Conservation.OrientedKummerRepresentative59

noncomputable section

open CategoryTheory
open ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.IntegratedTwistedKummerCup59

open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.ConcreteTwistedLiftCupBridge59
open Fermat.Conservation.ContinuousHomogeneousPullback59
open Fermat.Conservation.FiniteCyclicH2Generator59
open Fermat.Conservation.OrientedKummerRepresentative59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance zmodContinuousSMul : ContinuousSMul (ZMod 59) (ZMod 59) :=
  ⟨continuous_of_discreteTopology⟩

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G]

/-- Turn an inhomogeneous continuous one-cochain into an invariant
homogeneous one-cochain for trivial coefficients. -/
def homogeneousPrimitiveValue (r : C(G, ZMod 59)) : C(G, C(G, ZMod 59)) := by
  let f : C(G × G, ZMod 59) :=
    ⟨fun wx ↦ r (wx.1⁻¹ * wx.2),
      r.continuous.comp (continuous_fst.inv.mul continuous_snd)⟩
  exact ContinuousMap.curry f

/-- The nominal homogeneous primitive associated to an inhomogeneous
continuous one-cochain. -/
def homogeneousPrimitive (r : C(G, ZMod 59)) :
    Cochain (coefficients G) 1 := by
  refine ⟨⟨homogeneousPrimitiveValue r, ?_⟩⟩
  intro a
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  change r ((a⁻¹ * w)⁻¹ * (a⁻¹ * x)) = r (w⁻¹ * x)
  congr 1
  group

omit [LocallyCompactSpace G] in
@[simp]
theorem homogeneousPrimitive_differential_apply
    (r : C(G, ZMod 59)) (w x y : G) :
    twoValue
        (differential (coefficients G) 1 2 (homogeneousPrimitive r)).val
        w x y =
      r (x⁻¹ * y) - r (w⁻¹ * y) + r (w⁻¹ * x) := by
  change r (x⁻¹ * y) - (r (w⁻¹ * y) - r (w⁻¹ * x)) = _
  abel

/-- The concrete `C_(59²)` root/reduction/action data produce a boundary
between the explicit pulled carry and the character cup. -/
theorem pulledCarry_sub_characterCup_eq_boundary_of_twistedLift
    (chi eta : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed59 (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd))) :
    differential (coefficients G) 1 2
        (homogeneousPrimitive (twistedCupPrimitive59 chi eta q)) =
      cycleCochain (coefficients G) 2 3
        (pulledCarryCycle59 chi - characterCupCycle chi eta) := by
  apply Cochain.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro w
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  change twoValue
      (differential (coefficients G) 1 2
        (homogeneousPrimitive (twistedCupPrimitive59 chi eta q))).val
        w x y =
    twoValue
      (cycleCochain (coefficients G) 2 3
        (pulledCarryCycle59 chi - characterCupCycle chi eta)).val w x y
  rw [homogeneousPrimitive_differential_apply, cycleCochain_val]
  change
    twistedCupPrimitive59 chi eta q (x⁻¹ * y) -
        twistedCupPrimitive59 chi eta q (w⁻¹ * y) +
        twistedCupPrimitive59 chi eta q (w⁻¹ * x) =
      Fermat.Conservation.CyclicCarryH2Class59.carry59
          (((chi w)⁻¹ * chi x).toAdd)
          (((chi x)⁻¹ * chi y).toAdd) -
        (((chi x).toAdd - (chi w).toAdd) *
          ((eta y).toAdd - (eta x).toAdd))
  rw [show w⁻¹ * y = (w⁻¹ * x) * (x⁻¹ * y) by group]
  rw [twistedCupPrimitive59_equation chi eta q hred htwist]
  congr 1
  · congr 1 <;>
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  · congr 1 <;>
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv] <;> abel

/-- Hence the pulled carry and character cup have the same nominal `H²`
class under concrete twisted-lift data. -/
theorem h2Projection_pulledCarry_eq_characterCup_of_twistedLift
    (chi eta : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed59 (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd))) :
    h2Projection (coefficients G) (pulledCarryCycle59 chi) =
      h2Projection (coefficients G) (characterCupCycle chi eta) := by
  rw [← sub_eq_zero]
  rw [← map_sub]
  rw [h2Projection_eq_zero_iff]
  exact ⟨homogeneousPrimitive (twistedCupPrimitive59 chi eta q),
    pulledCarry_sub_characterCup_eq_boundary_of_twistedLift
      chi eta q hred htwist⟩

/-- The same equality in Mathlib's actual continuous-cohomology object. -/
theorem actualH2_pulledCarry_eq_characterCup_of_twistedLift
    (chi eta : G →ₜ* CyclicGroup59)
    (q : C(G, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) = chi g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed59 (Multiplicative.ofAdd
          ((eta g).toAdd * (chi h).toAdd))) :
    homologyLinearEquiv (coefficients G) 2
        (h2Projection (coefficients G) (pulledCarryCycle59 chi)) =
      Fermat.Conservation.ContinuousKummerTateCup.cupH1
        (multiplicationPairing (G := G))
        (homologyLinearEquiv (coefficients G) 1
          (h1Projection (coefficients G) (characterCycle chi)))
        (homologyLinearEquiv (coefficients G) 1
          (h1Projection (coefficients G) (characterCycle eta))) := by
  rw [Fermat.Conservation.ContinuousKummerTateCup.cupH1_projection]
  congr 1
  exact h2Projection_pulledCarry_eq_characterCup_of_twistedLift
    chi eta q hred htwist

/-! ## Specialization to the genuine Kummer cup -/

open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.LocalKummerH1

open scoped Fermat.Conservation.LocalKummerH1.KummerRootsDiscrete

variable (F : Type) [Field F] [CharZero F]

local instance absoluteGaloisCompactSpace :
    CompactSpace (AbsoluteGalois F) := by
  change CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  infer_instance

local instance absoluteGaloisT2Space :
    T2Space (AbsoluteGalois F) := by
  change T2Space (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- With an actual compatible `C_(59²)` Kummer coordinate satisfying its
reduction and cyclotomic action laws, the pulled carry class is the oriented
existing Kummer cup. -/
theorem pulledCarry_actualH2_eq_orientedKummerCup_of_twistedLift
    (zeta : F) (hzeta : IsPrimitiveRoot zeta 59) (a : Fˣ)
    (q : C(AbsoluteGalois F, CyclicGroup59Squared))
    (hred : ∀ g, reduction59 (q g) =
      orientedKummerCharacter F zeta hzeta a g)
    (htwist : ∀ g h,
      q (g * h) = q g * q h *
        kernelEmbed59 (Multiplicative.ofAdd
          ((orientedKummerCharacter F zeta hzeta
              (Fermat.Conservation.KummerOrientation.primitiveUnit
                59 F zeta hzeta) g).toAdd *
            (orientedKummerCharacter F zeta hzeta a h).toAdd))) :
    homologyLinearEquiv (coefficients (AbsoluteGalois F)) 2
        (h2Projection (coefficients (AbsoluteGalois F))
          (pulledCarryCycle59
            (orientedKummerCharacter F zeta hzeta a))) =
      orientH2 59 F zeta hzeta
        (kummerCupH1 59 F
          (orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F a))
          (continuousClassOfUnit 59 F
            (Fermat.Conservation.KummerOrientation.primitiveUnit
              59 F zeta hzeta))) := by
  let chi := orientedKummerCharacter F zeta hzeta a
  let eta := orientedKummerCharacter F zeta hzeta
    (Fermat.Conservation.KummerOrientation.primitiveUnit 59 F zeta hzeta)
  calc
    homologyLinearEquiv (coefficients (AbsoluteGalois F)) 2
        (h2Projection (coefficients (AbsoluteGalois F))
          (pulledCarryCycle59 chi)) =
      Fermat.Conservation.ContinuousKummerTateCup.cupH1
        (multiplicationPairing (G := AbsoluteGalois F))
        (homologyLinearEquiv (coefficients (AbsoluteGalois F)) 1
          (h1Projection (coefficients (AbsoluteGalois F))
            (characterCycle chi)))
        (homologyLinearEquiv (coefficients (AbsoluteGalois F)) 1
          (h1Projection (coefficients (AbsoluteGalois F))
            (characterCycle eta))) :=
      actualH2_pulledCarry_eq_characterCup_of_twistedLift
        chi eta q hred htwist
    _ = Fermat.Conservation.ContinuousKummerTateCup.cupH1
        (multiplicationPairing (G := AbsoluteGalois F))
        (orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F a))
        (orientH1 59 F zeta hzeta
          (continuousClassOfUnit 59 F
            (Fermat.Conservation.KummerOrientation.primitiveUnit
              59 F zeta hzeta))) := by
      rw [characterCycle_actualClass_eq_orientedKummer]
      rw [characterCycle_actualClass_eq_orientedKummer]
    _ = orientH2 59 F zeta hzeta
        (kummerCupH1 59 F
          (orientH1 59 F zeta hzeta (continuousClassOfUnit 59 F a))
          (continuousClassOfUnit 59 F
            (Fermat.Conservation.KummerOrientation.primitiveUnit
              59 F zeta hzeta))) :=
      (orientH2_kummerCupH1 F zeta hzeta a
        (Fermat.Conservation.KummerOrientation.primitiveUnit
          59 F zeta hzeta)).symm

end Fermat.Conservation.IntegratedTwistedKummerCup59
