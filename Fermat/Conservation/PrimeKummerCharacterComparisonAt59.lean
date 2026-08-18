/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Compatibility of the prime-generic Kummer character comparison at 59

The definitions used by the original order-59 comparison are definitionally
the specialization of `PrimeKummerCharacterComparison`.  Consequently the
generic comparison theorem can close the original order-59 statement without
any conversion, generator rotation, or sign adjustment.
-/
import Fermat.Conservation.KummerCharacterComparison59
import Fermat.Conservation.PrimeKummerCharacterComparison

noncomputable section

namespace Fermat.Conservation.PrimeKummerCharacterComparisonAt59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta 59)
variable (ha : ∀ b : F, b ^ 59 ≠ a)

/-- The splitting root in the original comparison is definitionally the
prime-generic splitting root at `p = 59`. -/
theorem splittingRoot59_eq_primeSplittingRoot :
    KummerCharacterComparison59.splittingRoot59 F a =
      PrimeKummerCharacterComparison.splittingRoot 59 F a :=
  rfl

/-- The unit-valued splitting roots agree definitionally at `p = 59`. -/
theorem splittingRootUnit59_eq_primeSplittingRootUnit :
    KummerCharacterComparison59.splittingRootUnit59 F a ha =
      PrimeKummerCharacterComparison.splittingRootUnit 59 F a ha :=
  rfl

/-- The bundled radicands agree definitionally at `p = 59`. -/
theorem radicandUnit59_eq_primeRadicandUnit :
    KummerCharacterComparison59.radicandUnit59 F a ha =
      PrimeKummerCharacterComparison.radicandUnit 59 F a ha :=
  rfl

/-- Powers of the selected primitive root agree definitionally at `p = 59`. -/
theorem algebraicPowerRoot59_eq_primeAlgebraicPowerRoot (k : ℕ) :
    KummerCharacterComparison59.algebraicPowerRoot59 F zeta hzeta k =
      PrimeKummerCharacterComparison.algebraicPowerRoot 59 F zeta hzeta k :=
  rfl

/-- The generic oriented Kummer value specializes definitionally to the
original order-59 oriented Kummer value. -/
theorem orientedKummerValue59_eq_primeOrientedKummerValue (u : Fˣ) :
    OrientedKummerRepresentative59.orientedKummerValue F zeta hzeta u =
      PrimeKummerCharacterComparison.orientedKummerValue 59 F zeta hzeta u :=
  rfl

/-- The generic oriented Kummer character specializes definitionally to the
original order-59 character. -/
theorem orientedKummerCharacter59_eq_primeOrientedKummerCharacter (u : Fˣ) :
    OrientedKummerRepresentative59.orientedKummerCharacter F zeta hzeta u =
      PrimeKummerCharacterComparison.orientedKummerCharacter
        59 F zeta hzeta u :=
  rfl

/-- The prime-generic theorem proves the original order-59 character
comparison directly. -/
theorem kummerCharacter59_eq_orientedKummerCharacter_via_prime :
    KummerCyclicQuotient59.kummerCharacter59 F zeta a hzeta ha =
      OrientedKummerRepresentative59.orientedKummerCharacter F zeta hzeta
        (KummerCharacterComparison59.radicandUnit59 F a ha) :=
  PrimeKummerCharacterComparison.kummerCharacter_eq_orientedKummerCharacter
    59 F zeta a hzeta ha

end Fermat.Conservation.PrimeKummerCharacterComparisonAt59
