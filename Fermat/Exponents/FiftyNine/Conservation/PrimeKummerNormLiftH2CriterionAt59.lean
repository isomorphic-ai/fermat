/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The generic norm/lift/H² criterion specialized to twisted lambda at 59

This adapter places the existing `60 * (zeta_59 - 1)` objects beside the
prime-parametric norm/lift/carry/cup architecture.  The concrete extension,
character, lift condition, carry classes, and Kummer cups are the `p = 59`
specializations of the generic objects.  The concrete equivalences below are
therefore consequences of one generic theorem rather than a second Albert or
cohomology argument.
-/
import Fermat.Experiments.Conservation.PrimeKummerNormLiftH2Criterion
import Fermat.Experiments.Conservation.PrimeKummerCyclicQuotientAt59
import Fermat.Experiments.Conservation.PrimeKummerCharacterComparisonAt59
import Fermat.Experiments.Conservation.PrimeOrientedCarryH2ClassAt59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59

set_option maxRecDepth 10000

open Fermat.Conservation
open Fermat.Conservation.ContinuousCarryLiftObstruction59
open Fermat.Conservation.PrimeCyclicExtension
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
open Fermat.FiftyNine.Conservation.TwistedLambdaCarryH2Class59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The old concrete Kummer extension is definitionally the generic
prime-Kummer extension at `p = 59`. -/
theorem twistedLambdaKummerExtension59_eq_primeKummerExtension :
    twistedLambdaKummerExtension59 K =
      PrimeKummerCyclicQuotient.kummerExtension 59
        (LambdaField59 K) (twistedLambda59 K) :=
  rfl

/-- The existing twisted-lambda character is definitionally the generic
prime-Kummer character. -/
theorem twistedLambdaKummerCharacter59_eq_primeKummerCharacter :
    twistedLambdaKummerCharacter59 K =
      PrimeKummerCyclicQuotient.kummerCharacter 59
        (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (twistedLambda59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (twistedLambda59_not_pow K) :=
  rfl

/-- The bundled twisted radicand is definitionally the generic bundled
radicand. -/
theorem twistedLambdaRadicandUnit59_eq_primeRadicandUnit :
    twistedLambdaRadicandUnit59 K =
      PrimeKummerCharacterComparison.radicandUnit 59
        (LambdaField59 K) (twistedLambda59 K)
        (twistedLambda59_not_pow K) :=
  rfl

/-- The concrete no-lift proposition is the generic no-lift proposition at
the twisted radicand. -/
theorem twistedLambdaNoContinuousLift59_eq_primeKummerNoContinuousLift :
    TwistedLambdaNoContinuousLift59 K =
      PrimeKummerCarryLiftCriterion.KummerNoContinuousLift 59
        (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (twistedLambda59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (twistedLambda59_not_pow K) :=
  rfl

/-- The concrete oriented carry class is definitionally the generic pulled
carry class at the twisted radicand. -/
theorem twistedLambdaOrientedCarryH2Class59_eq_primeKummerCarryH2Class :
    twistedLambdaOrientedCarryH2Class59 K =
      PrimeKummerCarryLiftCriterion.kummerCarryH2Class 59
        (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (twistedLambda59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (twistedLambda59_not_pow K) :=
  rfl

/-- The roots-valued concrete carry class is definitionally the generic
roots-valued carry class. -/
theorem twistedLambdaRootsCarryH2Class59_eq_primeKummerRootsCarryH2Class :
    twistedLambdaRootsCarryH2Class59 K =
      PrimeKummerNormLiftH2Criterion.kummerRootsCarryH2Class 59
        (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (twistedLambda59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (twistedLambda59_not_pow K) :=
  rfl

/-- The concrete roots-valued Kummer cup is definitionally the generic cup
obstruction specialized to the twisted radicand. -/
theorem twistedLambdaKummerCupH2Class59_eq_primeRootsKummerCupObstruction :
    twistedLambdaKummerCupH2Class59 K =
      PrimeKummerNormLiftH2Criterion.rootsKummerCupObstruction 59
        (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (twistedLambda59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (twistedLambda59_not_pow K) :=
  rfl

/-- Orienting the concrete cup is definitionally the generic oriented cup
obstruction. -/
theorem twistedLambdaOrientedKummerCup_eq_primeOrientedKummerCupObstruction :
    lambdaH2CoefficientOrientationEquiv59 K
        (twistedLambdaKummerCupH2Class59 K) =
      PrimeKummerNormLiftH2Criterion.orientedKummerCupObstruction 59
        (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (twistedLambda59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (twistedLambda59_not_pow K) :=
  rfl

/-! ## Concrete consequences of the generic endpoint -/

/-- The concrete norm condition is equivalent to the existing 59-shaped
continuous lift condition, by specialization of the generic Albert
criterion. -/
theorem primitiveRoot_is_norm_iff_exists_continuous_lift_via_prime :
    (∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
      ∃ psi : Field.absoluteGaloisGroup (LambdaField59 K) →ₜ*
          CyclicGroup59Squared,
        reduction59.comp psi = twistedLambdaKummerCharacter59 K := by
  exact
    PrimeKummerNormLiftH2Criterion.primitiveRoot_isNorm_iff_exists_compatibleLift
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)

/-- The concrete norm condition is equivalent to vanishing of the existing
oriented pulled carry class. -/
theorem primitiveRoot_is_norm_iff_twistedLambdaOrientedCarryH2Class59_eq_zero_via_prime :
    (∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
      twistedLambdaOrientedCarryH2Class59 K = 0 := by
  exact
    PrimeKummerNormLiftH2Criterion.primitiveRoot_isNorm_iff_kummerCarryH2Class_eq_zero
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)

/-- The concrete norm condition is equivalent to vanishing of the existing
roots-valued pulled carry class. -/
theorem primitiveRoot_is_norm_iff_twistedLambdaRootsCarryH2Class59_eq_zero_via_prime :
    (∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
      twistedLambdaRootsCarryH2Class59 K = 0 := by
  rw [twistedLambdaRootsCarryH2Class59_eq_primeKummerRootsCarryH2Class]
  rw [PrimeKummerNormLiftH2Criterion.kummerRootsCarryH2Class_eq_rootsKummerCupObstruction]
  exact
    PrimeKummerNormLiftH2Criterion.primitiveRoot_isNorm_iff_rootsKummerCupObstruction_eq_zero
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)

/-- The old concrete norm/cup statement is an immediate instance of the
generic norm/roots-cup equivalence. -/
theorem primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero_via_prime :
    (∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
      twistedLambdaKummerCupH2Class59 K = 0 := by
  exact
    PrimeKummerNormLiftH2Criterion.primitiveRoot_isNorm_iff_rootsKummerCupObstruction_eq_zero
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)

/-- The concrete oriented carry/cup equality is the generic equality at the
twisted radicand. -/
theorem twistedLambdaOrientedCarry_eq_orientedKummerCup_via_prime :
    twistedLambdaOrientedCarryH2Class59 K =
      lambdaH2CoefficientOrientationEquiv59 K
        (twistedLambdaKummerCupH2Class59 K) := by
  exact
    PrimeKummerNormLiftH2Criterion.kummerCarryH2Class_eq_orientedKummerCupObstruction
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)

/-- The concrete roots-valued carry/cup equality is likewise the generic
roots-valued equality. -/
theorem twistedLambdaRootsCarryH2Class59_eq_kummerCup_via_prime :
    twistedLambdaRootsCarryH2Class59 K =
      twistedLambdaKummerCupH2Class59 K := by
  exact
    PrimeKummerNormLiftH2Criterion.kummerRootsCarryH2Class_eq_rootsKummerCupObstruction
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)

/-- The concrete primitive-root nonnorm proposition is exactly the existing
no-lift proposition, by the generic negated criterion. -/
theorem primitiveRoot_not_norm_iff_twistedLambdaNoContinuousLift59_via_prime :
    (¬ ∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
      TwistedLambdaNoContinuousLift59 K := by
  exact
    PrimeKummerNormLiftH2Criterion.primitiveRoot_not_norm_iff_noContinuousLift
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)

/-- The existing concrete Kummer cup survives exactly when the concrete
character has no continuous lift. -/
theorem twistedLambdaKummerCupH2Class59_ne_zero_iff_noContinuousLift_via_prime :
    twistedLambdaKummerCupH2Class59 K ≠ 0 ↔
      TwistedLambdaNoContinuousLift59 K := by
  exact
    PrimeKummerNormLiftH2Criterion.rootsKummerCupObstruction_ne_zero_iff_noContinuousLift
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)

/-- The existing concrete Kummer cup survives exactly when the local
primitive root is not a norm. -/
theorem twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm_via_prime :
    twistedLambdaKummerCupH2Class59 K ≠ 0 ↔
      ¬ ∃ beta : twistedLambdaKummerExtension59 K,
        Algebra.norm (LambdaField59 K) beta =
          lambdaLocalPrimitiveRoot59 K := by
  exact
    (PrimeKummerNormLiftH2Criterion.primitiveRoot_not_norm_iff_rootsKummerCupObstruction_ne_zero
      59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)).symm

end Fermat.FiftyNine.Conservation.PrimeKummerNormLiftH2CriterionAt59
