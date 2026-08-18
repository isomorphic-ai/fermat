/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Compatibility of the prime-generic compatible Kummer lift at 59

The original order-59 root choices and coordinates are definitionally the
specialization of `PrimeCompatibleKummerLift`.  The generic theorem therefore
proves the original actual-cohomology carry-to-Kummer-cup statement directly.
-/
import Fermat.Conservation.CompatibleKummerLift59
import Fermat.Conservation.PrimeCompatibleKummerLift

noncomputable section

namespace Fermat.Conservation.PrimeCompatibleKummerLiftAt59

open Fermat.Conservation.LocalKummerH1
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (F : Type) [Field F]
variable (zeta : F) (hzeta : IsPrimitiveRoot zeta 59)

/-- The compatible primitive root is definitionally unchanged. -/
theorem cyclotomicRoot3481_eq_primeCyclotomicRootSquared :
    CompatibleKummerLift59.cyclotomicRoot3481 F zeta hzeta =
      PrimeCompatibleKummerLift.cyclotomicRootSquared
        (p := 59) F zeta hzeta :=
  rfl

/-- The chosen compatible Kummer root is definitionally unchanged. -/
theorem kummerRoot3481_eq_primeKummerRootSquared (a : Fˣ) :
    CompatibleKummerLift59.kummerRoot3481 F a =
      PrimeCompatibleKummerLift.kummerRootSquared (p := 59) F a :=
  rfl

/-- The roots-valued compatible cocycle is definitionally unchanged. -/
theorem compatibleCocycleValue3481_eq_primeCompatibleCocycleValueSquared
    (a : Fˣ) (g : AbsoluteGalois F) :
    CompatibleKummerLift59.compatibleCocycleValue3481 F a g =
      PrimeCompatibleKummerLift.compatibleCocycleValueSquared
        (p := 59) F a g :=
  rfl

/-- The compatible cyclic coordinate is definitionally unchanged. -/
theorem compatibleKummerCoordinate3481_eq_primeCompatibleKummerCoordinateSquared
    (a : Fˣ) :
    CompatibleKummerLift59.compatibleKummerCoordinate3481 F zeta hzeta a =
      PrimeCompatibleKummerLift.compatibleKummerCoordinateSquared
        (p := 59) F zeta hzeta a :=
  rfl

variable [CharZero F]

/-- The arbitrary-prime theorem closes the original order-59
actual-cohomology statement without a conversion lemma. -/
theorem pulledCarry_actualH2_eq_orientedKummerCup_via_prime (a : Fˣ) :
    homologyLinearEquiv
        (ContinuousHomogeneousPullback59.coefficients (AbsoluteGalois F)) 2
        (h2Projection
          (ContinuousHomogeneousPullback59.coefficients (AbsoluteGalois F))
          (ContinuousCarryLiftObstruction59.pulledCarryCycle59
            (OrientedKummerRepresentative59.orientedKummerCharacter
              F zeta hzeta a))) =
      ContinuousKummerOrientation.orientH2 59 F zeta hzeta
        (ContinuousKummerTateAlgebra.kummerCupH1 59 F
          (ContinuousKummerOrientation.orientH1 59 F zeta hzeta
            (ContinuousKummerH1.continuousClassOfUnit 59 F a))
          (ContinuousKummerH1.continuousClassOfUnit 59 F
            (KummerOrientation.primitiveUnit 59 F zeta hzeta))) :=
  PrimeCompatibleKummerLift.pulledCarry_actualH2_eq_orientedKummerCup
    (p := 59) F zeta hzeta a

end Fermat.Conservation.PrimeCompatibleKummerLiftAt59
