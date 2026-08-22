/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The carry/lift criterion for a prime Kummer character

This file composes the concrete prime-degree Kummer quotient with the
prime-parametric continuous carry obstruction.  For every prime `p`, the
actual continuous carry class attached to a non-`p`-th-power radicand
vanishes exactly when its genuine absolute-Galois Kummer character lifts
through `C_(p^2) -> C_p`.

No norm-residue theorem or arithmetic non-liftability value is asserted.
-/
import Fermat.Experiments.Conservation.PrimeContinuousCarryLift
import Fermat.Experiments.Conservation.PrimeKummerCyclicQuotient

noncomputable section

open CategoryTheory ContinuousCohomology
open Fermat.Conservation.ContinuousKummerTateCupRaw
open Fermat.Conservation.ContinuousKummerTateCup.Nominal

namespace Fermat.Conservation.PrimeKummerCarryLiftCriterion

open Fermat.Conservation.PrimeCyclicExtension
open Fermat.Conservation.PrimeContinuousCarryLift
open Fermat.Conservation.PrimeKummerCyclicQuotient

variable (p : ℕ) [Fact p.Prime]
variable (F : Type) [Field F]
variable (zeta a : F)
variable (hzeta : IsPrimitiveRoot zeta p)
variable (ha : ∀ b : F, b ^ p ≠ a)

/-- The explicit pulled carry cycle of the genuine Kummer character. -/
abbrev kummerCarryCycle :=
  pulledCarryCycle (kummerCharacter p F zeta a hzeta ha)

/-- The actual continuous `H²(G_F, F_p)` class of the genuine Kummer
character. -/
abbrev kummerCarryH2Class :=
  pulledCarryH2Class (kummerCharacter p F zeta a hzeta ha)

/-- The statement that the genuine Kummer character has no continuous
cyclic lift of order `p²`. -/
abbrev KummerNoContinuousLift : Prop :=
  NoContinuousLift (kummerCharacter p F zeta a hzeta ha)

/-- The explicit carry cycle is a boundary exactly when the concrete Kummer
character lifts continuously to `C_(p²)`. -/
theorem kummerCarryCycle_boundary_iff_exists_continuous_lift :
    (∃ b : Cochain
        (Fermat.Conservation.PrimeContinuousHomogeneousPullback.coefficients
          p (Field.absoluteGaloisGroup F)) 1,
      differential
          (Fermat.Conservation.PrimeContinuousHomogeneousPullback.coefficients
            p (Field.absoluteGaloisGroup F)) 1 2 b =
        cycleCochain
          (Fermat.Conservation.PrimeContinuousHomogeneousPullback.coefficients
            p (Field.absoluteGaloisGroup F)) 2 3
          (kummerCarryCycle p F zeta a hzeta ha)) ↔
      ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroupSquared p,
        (reduction p).comp psi = kummerCharacter p F zeta a hzeta ha := by
  exact pulledCarryCycle_boundary_iff_exists_continuous_lift
    (kummerCharacter p F zeta a hzeta ha)

/-- The actual continuous carry class vanishes exactly when the concrete
Kummer character lifts continuously to `C_(p²)`. -/
theorem kummerCarryH2Class_eq_zero_iff_exists_continuous_lift :
    kummerCarryH2Class p F zeta a hzeta ha = 0 ↔
      ∃ psi : Field.absoluteGaloisGroup F →ₜ* CyclicGroupSquared p,
        (reduction p).comp psi = kummerCharacter p F zeta a hzeta ha := by
  exact pulledCarryH2Class_eq_zero_iff_exists_continuous_lift
    (kummerCharacter p F zeta a hzeta ha)

/-- Equivalently, the genuine continuous carry class survives exactly when
the concrete Kummer character has no continuous cyclic lift of order `p²`. -/
theorem kummerCarryH2Class_ne_zero_iff_noContinuousLift :
    kummerCarryH2Class p F zeta a hzeta ha ≠ 0 ↔
      KummerNoContinuousLift p F zeta a hzeta ha := by
  exact pulledCarryH2Class_ne_zero_iff_noContinuousLift
    (kummerCharacter p F zeta a hzeta ha)

end Fermat.Conservation.PrimeKummerCarryLiftCriterion
