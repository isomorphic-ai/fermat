/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# Compatibility of the prime-generic Albert converse at 59

The generic reduction and Kummer objects specialize definitionally at 59.
This file records that the generic converse directly proves the historical
59-shaped endpoint.
-/
import Fermat.Experiments.Conservation.AlbertCyclicConverse59
import Fermat.Experiments.Conservation.PrimeAlbertCyclicConverse
import Fermat.Experiments.Conservation.PrimeKummerCyclicQuotientAt59

noncomputable section

namespace Fermat.Conservation.PrimeAlbertCyclicConverseAt59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

open Fermat.Conservation.PrimeCyclicExtension

theorem reduction59_eq_primeReduction :
    Fermat.Conservation.AlbertCyclicCompatibility59.cyclicReduction3481To59 =
      reduction 59 :=
  rfl

variable (F : Type) [Field F] [PerfectField F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta 59)
variable (ha : ∀ b : F, b ^ 59 ≠ a)

/-- The prime-generic converse consumes the original 59-shaped compatibility
equation without any adapter data. -/
theorem concreteKummer_exists_norm_of_albertCharacter3481_via_prime
    (psi : Field.absoluteGaloisGroup F →ₜ*
      Fermat.Conservation.AlbertCyclicQuotient59.CyclicGroup3481)
    (hpsi :
      Fermat.Conservation.AlbertCyclicCompatibility59.cyclicReduction3481To59.comp
          psi =
        Fermat.Conservation.KummerCyclicQuotient59.kummerCharacter59
          F zeta a hzeta ha) :
    ∃ beta : Fermat.Conservation.KummerCyclicQuotient59.kummerExtension59 F a,
      Algebra.norm F beta = zeta := by
  apply
    Fermat.Conservation.PrimeAlbertCyclicConverse.concreteKummer_exists_norm_of_albertCharacter
      59 F zeta a hzeta ha psi
  simpa only [reduction59_eq_primeReduction,
    Fermat.Conservation.PrimeKummerCyclicQuotientAt59.kummerCharacter59_eq_primeKummerCharacter]
    using hpsi

end Fermat.Conservation.PrimeAlbertCyclicConverseAt59
