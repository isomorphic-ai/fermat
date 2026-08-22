/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Compatibility of the prime-generic Kummer quotient at 59

The original order-59 construction is definitionally the specialization of
`PrimeKummerCyclicQuotient`.  These equalities keep existing consumers stable
while new code can work over an arbitrary prime.
-/
import Fermat.Experiments.Conservation.KummerCyclicQuotient59
import Fermat.Experiments.Conservation.PrimeKummerCyclicQuotient

noncomputable section

namespace Fermat.Conservation.PrimeKummerCyclicQuotientAt59

open Fermat.Conservation.KummerCyclicQuotient59
open Fermat.Conservation.PrimeKummerCyclicQuotient

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta 59)
variable (ha : ∀ b : F, b ^ 59 ≠ a)

theorem kummerPolynomial59_eq_primeKummerPolynomial :
    kummerPolynomial59 F a = kummerPolynomial 59 F a :=
  rfl

theorem kummerExtension59_eq_primeKummerExtension :
    kummerExtension59 F a = kummerExtension 59 F a :=
  rfl

theorem kummerGalEquiv59_eq_primeKummerGalEquiv :
    kummerGalEquiv59 F zeta a hzeta ha =
      kummerGalEquiv 59 F zeta a hzeta ha :=
  rfl

theorem kummerCharacter59_eq_primeKummerCharacter :
    kummerCharacter59 F zeta a hzeta ha =
      kummerCharacter 59 F zeta a hzeta ha :=
  rfl

end Fermat.Conservation.PrimeKummerCyclicQuotientAt59
