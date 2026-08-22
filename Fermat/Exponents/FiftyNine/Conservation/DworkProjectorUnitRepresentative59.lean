/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Finite unit representatives for the local Kummer projectors at 59

The character projector on the lambda-local Kummer quotient is a normalized
sum of 58 cyclotomic translates.  Although its definition lives in the
additive quotient, that sum has a concrete multiplicative representative:
the corresponding product of translated units, raised to natural-number
representatives of the coefficients modulo 59.

This file constructs that representative and proves exact readback through
`classOfUnit`.  The covariance theorem then rewrites every local translate of
a transported Dwork principal unit as a Dwork translate before transport.
Thus projection loses no finite representative.  No local-symbol evaluation,
nonvanishing claim, or relation-7A closure is made here.
-/
import Fermat.Exponents.FiftyNine.Conservation.DworkCyclotomicTransport59
import Fermat.Experiments.Conservation.GuardDependsOn

open scoped BigOperators NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59

set_option maxRecDepth 100000

open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.LocalKummerTransport
open Fermat.Conservation.WildKummerPairing
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
open Fermat.FiftyNine.Conservation.CriticalUnitCoefficient59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DworkCyclotomicTransport59
open Fermat.FiftyNine.Conservation.DworkPrincipalUnitCandidates59
open Fermat.FiftyNine.Conservation.LambdaCyclotomicCompletionAction59
open Fermat.FiftyNine.Conservation.LambdaLocalKummerCharacterSeat59
open Fermat.FiftyNine.Conservation.LambdaLocalKummerClassAction59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.LocalIntegralTrace59
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter.Conjugation

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

noncomputable local instance instLambdaLocalKummerClass59ModuleZMod :
    Module (ZMod 59) (LambdaLocalKummerClass59 K) :=
  AddCommGroup.zmodModule
    (n := 59) (G := LambdaLocalKummerClass59 K)
    (lambdaLocalKummerClass59_nsmul_eq_zero K)

noncomputable local instance instGaloisIndex59CardInvertibleZMod :
    Invertible (Fintype.card GaloisIndex59 : ZMod 59) :=
  invertibleOfNonzero (by
    rw [galoisIndex59_card]
    decide)

/-! ## A finite representative for every local projector -/

/-- The natural exponent in `[0,58]` representing the normalized idempotent
coefficient attached to `sigma`. -/
noncomputable def projectorExponent59 (t : ZMod 58)
    (sigma : GaloisIndex59) : ℕ :=
  (⅟(Fintype.card GaloisIndex59 : ZMod 59) *
    (↑((powerCharacter59 t sigma)⁻¹) : ZMod 59)).val

/-- The concrete finite product of translated units representing the
power-`t` projector of the Kummer class of `u`. -/
noncomputable def projectorUnitRepresentative59 (t : ZMod 58)
    (u : (LambdaLocalField59 K)ˣ) : (LambdaLocalField59 K)ˣ :=
  ∏ sigma : GaloisIndex59,
    (unitMap
      (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom u) ^
      projectorExponent59 t sigma

/-- The genuine local Kummer action on a unit class is induced by applying
the completed cyclotomic automorphism to the representing unit. -/
@[simp]
theorem lambdaLocalKummerClassRepresentation59_classOfUnit
    (sigma : GaloisIndex59) (u : (LambdaLocalField59 K)ˣ) :
    lambdaLocalKummerClassRepresentation59 K sigma
        (classOfUnit 59 (LambdaLocalField59 K) (Additive.ofMul u)) =
      classOfUnit 59 (LambdaLocalField59 K)
        (Additive.ofMul
          (unitMap
            (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom u)) := by
  rfl

/-- Exact readback: the class of the finite product is the additive
character-projector value. -/
theorem classOfUnit_projectorUnitRepresentative59
    (t : ZMod 58) (u : (LambdaLocalField59 K)ˣ) :
    classOfUnit 59 (LambdaLocalField59 K)
        (Additive.ofMul (projectorUnitRepresentative59 K t u)) =
      (lambdaLocalKummerPowerProjector59 K t
          (classOfUnit 59 (LambdaLocalField59 K) (Additive.ofMul u)) :
        LambdaLocalKummerClass59 K) := by
  rw [lambdaLocalKummerPowerProjector59_apply]
  rw [characterIdempotent, map_smul, map_sum]
  simp only [LinearMap.smul_apply, Representation.asAlgebraHom_single]
  rw [LinearMap.sum_apply]
  rw [Finset.smul_sum]
  simp_rw [LinearMap.smul_apply, smul_smul]
  unfold projectorUnitRepresentative59
  change classOfUnit 59 (LambdaLocalField59 K)
      (Additive.ofMul (∏ sigma : GaloisIndex59,
        (unitMap
          (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom u) ^
            projectorExponent59 t sigma)) = _
  change classOfUnit 59 (LambdaLocalField59 K)
      (∑ sigma : GaloisIndex59,
        (projectorExponent59 t sigma) •
          Additive.ofMul
            (unitMap
              (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom u)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [map_nsmul]
  rw [lambdaLocalKummerClassRepresentation59_classOfUnit]
  calc
    projectorExponent59 t sigma •
        classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul
            (unitMap
              (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom u)) =
      (projectorExponent59 t sigma : ZMod 59) •
        classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul
            (unitMap
              (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom u)) :=
        (Nat.cast_smul_eq_nsmul (ZMod 59)
          (projectorExponent59 t sigma)
          (classOfUnit 59 (LambdaLocalField59 K)
            (Additive.ofMul
              (unitMap
                (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom u)))).symm
    _ = (⅟(Fintype.card GaloisIndex59 : ZMod 59) *
          (↑((powerCharacter59 t sigma)⁻¹) : ZMod 59)) •
        classOfUnit 59 (LambdaLocalField59 K)
          (Additive.ofMul
            (unitMap
              (cyclotomicLambdaCompletionRingEquiv59 K sigma).toRingHom u)) := by
        rw [projectorExponent59, ZMod.natCast_zmod_val]

/-! ## The same representative in Dwork coordinates -/

/-- The finite representative for a depth-indexed Dwork principal unit,
written with the Dwork cyclotomic action before the three transport maps. -/
noncomputable def dworkProjectorUnitRepresentativeAtDepth59
    (t : ZMod 58) (depth : ℕ) (hdepth : depth ≠ 0) :
    (LambdaLocalField59 K)ˣ :=
  ∏ sigma : GaloisIndex59,
    (Units.map (valuedCompletionEquivLambdaField59 K).toRingHom
      (Units.map (valuedIntegerToLambdaCompletion59 K).toMonoidHom
        (Units.map (dworkValuedAlgEquiv59 K).toRingHom
          (Units.map
            (dworkCompleteCyclotomicEquiv (p := 59) K sigma).toMonoidHom
            (dworkPrincipalUnitAtDepth59 K depth hdepth))))) ^
      projectorExponent59 t sigma

/-- Covariance identifies the local-orbit product with the Dwork-orbit
product factor by factor. -/
theorem projectorUnitRepresentative_dworkPrincipalUnitLocal59_eq_dwork
    (t : ZMod 58) (depth : ℕ) (hdepth : depth ≠ 0) :
    projectorUnitRepresentative59 K t
        (dworkPrincipalUnitLocal59 K depth hdepth) =
      dworkProjectorUnitRepresentativeAtDepth59 K t depth hdepth := by
  unfold projectorUnitRepresentative59 dworkProjectorUnitRepresentativeAtDepth59
  apply Finset.prod_congr rfl
  intro sigma hsigma
  rw [dworkPrincipalUnitLocal59_cyclotomic]

/-- Exact Dwork readback through the local Kummer quotient. -/
theorem classOfUnit_dworkProjectorUnitRepresentativeAtDepth59
    (t : ZMod 58) (depth : ℕ) (hdepth : depth ≠ 0) :
    classOfUnit 59 (LambdaLocalField59 K)
        (Additive.ofMul
          (dworkProjectorUnitRepresentativeAtDepth59 K t depth hdepth)) =
      (lambdaLocalKummerPowerProjector59 K t
          (classOfUnit 59 (LambdaLocalField59 K)
            (Additive.ofMul (dworkPrincipalUnitLocal59 K depth hdepth))) :
        LambdaLocalKummerClass59 K) := by
  rw [← projectorUnitRepresentative_dworkPrincipalUnitLocal59_eq_dwork]
  exact classOfUnit_projectorUnitRepresentative59 K t
    (dworkPrincipalUnitLocal59 K depth hdepth)

/-! ## The two seated candidates -/

/-- Dwork-orbit product representing the projected depth-15 candidate. -/
noncomputable def dworkProjectorUnitRepresentativeFifteen59 :
    (LambdaLocalField59 K)ˣ :=
  dworkProjectorUnitRepresentativeAtDepth59 K 15 15 (by norm_num)

/-- Dwork-orbit product representing the projected depth-44 candidate. -/
noncomputable def dworkProjectorUnitRepresentativeFortyFour59 :
    (LambdaLocalField59 K)ˣ :=
  dworkProjectorUnitRepresentativeAtDepth59 K 44 44 (by norm_num)

/-- The depth-15 Dwork product reads back as the already defined literal
power-15 projected Kummer class. -/
theorem classOfUnit_dworkProjectorUnitRepresentativeFifteen59 :
    classOfUnit 59 (LambdaLocalField59 K)
        (Additive.ofMul (dworkProjectorUnitRepresentativeFifteen59 K)) =
      (projectedDworkPrincipalKummerClassFifteen59 K :
        LambdaLocalKummerClass59 K) := by
  simpa [dworkProjectorUnitRepresentativeFifteen59,
    dworkPrincipalUnitLocalFifteen59,
    projectedDworkPrincipalKummerClassFifteen59,
    dworkPrincipalKummerClassFifteen59] using
    (classOfUnit_dworkProjectorUnitRepresentativeAtDepth59 K 15 15
      (by norm_num))

/-- The depth-44 Dwork product reads back as the already defined literal
power-44 projected Kummer class. -/
theorem classOfUnit_dworkProjectorUnitRepresentativeFortyFour59 :
    classOfUnit 59 (LambdaLocalField59 K)
        (Additive.ofMul (dworkProjectorUnitRepresentativeFortyFour59 K)) =
      (projectedDworkPrincipalKummerClassFortyFour59 K :
        LambdaLocalKummerClass59 K) := by
  simpa [dworkProjectorUnitRepresentativeFortyFour59,
    dworkPrincipalUnitLocalFortyFour59,
    projectedDworkPrincipalKummerClassFortyFour59,
    dworkPrincipalKummerClassFortyFour59] using
    (classOfUnit_dworkProjectorUnitRepresentativeAtDepth59 K 44 44
      (by norm_num))

/-! ## Kernel-trust and dependency audit -/

/--
info: 'Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59.classOfUnit_projectorUnitRepresentative59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms classOfUnit_projectorUnitRepresentative59

/--
info: 'Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59.classOfUnit_dworkProjectorUnitRepresentativeAtDepth59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms classOfUnit_dworkProjectorUnitRepresentativeAtDepth59

/--
info: 'Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59.classOfUnit_dworkProjectorUnitRepresentativeFortyFour59' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms classOfUnit_dworkProjectorUnitRepresentativeFortyFour59

/- Readback is the multiplicative realization of the existing genuine
character projector. -/
#guard_depends_on
  classOfUnit_projectorUnitRepresentative59,
  lambdaLocalKummerPowerProjector59_apply

/- The local and Dwork products are compared by the committed covariance
theorem, not by quotient-level choice. -/
#guard_depends_on
  projectorUnitRepresentative_dworkPrincipalUnitLocal59_eq_dwork,
  dworkPrincipalUnitLocal59_cyclotomic

/- The generic Dwork readback retains both structural ingredients. -/
#guard_depends_on
  classOfUnit_dworkProjectorUnitRepresentativeAtDepth59,
  classOfUnit_projectorUnitRepresentative59

#guard_depends_on
  classOfUnit_dworkProjectorUnitRepresentativeAtDepth59,
  projectorUnitRepresentative_dworkPrincipalUnitLocal59_eq_dwork

/- The concrete power-44 endpoint is only a specialization of the generic
finite representative theorem. -/
#guard_depends_on
  classOfUnit_dworkProjectorUnitRepresentativeFortyFour59,
  classOfUnit_dworkProjectorUnitRepresentativeAtDepth59

end Fermat.FiftyNine.Conservation.DworkProjectorUnitRepresentative59
