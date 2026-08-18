/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The twisted-lambda cup reduces to its unit factor at 59

The explicit identity `Norm(1 + alpha) = zeta_59`, where
`alpha ^ 59 = lambda`, gives a compatible `C_(59^2)` lift for the bare
lambda Kummer character.  The prime-generic carry/Kummer comparison then
shows that the genuine continuous `H^2(mu_59)` cup of bare lambda against
the primitive root vanishes.

Since the continuous Kummer map sends multiplication to addition and the
actual cup is linear in its left input, the cup for
`60 * lambda` is consequently exactly the cup for the unit factor `60`.
No scalar readout or local-reciprocity value is used.
-/
import Fermat.Conservation.PrimeAlbertCyclicCompatibility
import Fermat.Conservation.PrimeKummerNormLiftH2Criterion
import Fermat.FiftyNine.Conservation.BareLambdaNorm59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59

open Fermat.Conservation.ContinuousKummerH1
open Fermat.Conservation.ContinuousKummerOrientation
open Fermat.Conservation.ContinuousKummerTateAlgebra
open Fermat.Conservation.KummerOrientation
open Fermat.Conservation.PrimeAlbertCyclicCompatibility
open Fermat.Conservation.PrimeCyclicExtension
open Fermat.Conservation.PrimeKummerCharacterComparison
open Fermat.Conservation.PrimeKummerNormLiftH2Criterion
open Fermat.Conservation.PrimeOrientedCarryH2Class
open Fermat.FiftyNine.Conservation.BareLambdaNorm59
open Fermat.FiftyNine.Conservation.ContinuousKummerTateLocalization59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- Bare cyclotomic lambda, bundled as a nonzero local-field unit. -/
def bareLambdaRadicandUnit59 : (LambdaField59 K)ˣ :=
  radicandUnit 59 (LambdaField59 K) (canonicalLambda59 K)
    (canonicalLambda59_not_pow K)

/-- The principal unit `60`, bundled as a local-field unit. -/
def unit60RadicandUnit59 : (LambdaField59 K)ˣ :=
  Units.mk0 (twistUnit59 K) (by
    intro hzero
    have hv := twistUnit59_valuation K
    rw [hzero, map_zero] at hv
    exact zero_ne_one hv)

/-- Bundling the identity `60 * lambda` as a field unit preserves its
multiplicative factorization exactly. -/
theorem twistedLambdaRadicandUnit59_eq_unit60_mul_bareLambda :
    twistedLambdaRadicandUnit59 K =
      unit60RadicandUnit59 K * bareLambdaRadicandUnit59 K := by
  apply Units.ext
  rfl

/-- The genuine continuous Kummer `H^1` class of `60 * lambda` is the sum
of the classes of its two multiplicative factors. -/
theorem continuousClassOfTwistedLambda_eq_unit60_add_bareLambda :
    continuousClassOfUnit 59 (LambdaField59 K)
        (twistedLambdaRadicandUnit59 K) =
      continuousClassOfUnit 59 (LambdaField59 K)
          (unit60RadicandUnit59 K) +
        continuousClassOfUnit 59 (LambdaField59 K)
          (bareLambdaRadicandUnit59 K) := by
  rw [twistedLambdaRadicandUnit59_eq_unit60_mul_bareLambda K]
  exact continuousClassOfUnit_mul 59 (LambdaField59 K)
    (unit60RadicandUnit59 K) (bareLambdaRadicandUnit59 K)

/-- The genuine roots-valued continuous Kummer cup for bare lambda against
the selected primitive root. -/
def bareLambdaKummerCupH2Class59 : LambdaRootsContinuousH2 K :=
  lambdaContinuousCup59 K
    (orientH1 59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (continuousClassOfUnit 59 (LambdaField59 K)
        (bareLambdaRadicandUnit59 K)))
    (continuousClassOfUnit 59 (LambdaField59 K)
      (primitiveUnit 59 (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)))

/-- The genuine roots-valued continuous Kummer cup for the unit factor 60
against the selected primitive root. -/
def unit60KummerCupH2Class59 : LambdaRootsContinuousH2 K :=
  lambdaContinuousCup59 K
    (orientH1 59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (continuousClassOfUnit 59 (LambdaField59 K)
        (unit60RadicandUnit59 K)))
    (continuousClassOfUnit 59 (LambdaField59 K)
      (primitiveUnit 59 (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)))

/-- The explicit norm witness for bare lambda constructs an actual
continuous lift of its Kummer character through `C_(59^2) -> C_59`. -/
theorem exists_bareLambda_compatibleKummerLift59 :
    ∃ psi : Field.absoluteGaloisGroup (LambdaField59 K) →ₜ*
        CyclicGroupSquared 59,
      (reduction 59).comp psi =
        Fermat.Conservation.PrimeKummerCyclicQuotient.kummerCharacter
          59 (LambdaField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (canonicalLambda59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K)
          (canonicalLambda59_not_pow K) := by
  obtain ⟨beta, hbeta⟩ := exists_bareLambda_norm_eq_primitiveRoot K
  exact concreteKummer_exists_albertCharacter
    59 (LambdaField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (canonicalLambda59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (canonicalLambda59_not_pow K)
    beta hbeta

/-- The compatible-lift obstruction for the bare-lambda Kummer character
vanishes in its genuine roots-valued continuous `H^2`. -/
theorem bareLambdaRootsCarryH2Class59_eq_zero :
    kummerRootsCarryH2Class 59 (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (canonicalLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (canonicalLambda59_not_pow K) = 0 := by
  exact
    (rootsCarryH2Class_eq_zero_iff_exists_continuous_lift
      (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (Fermat.Conservation.PrimeKummerCyclicQuotient.kummerCharacter
        59 (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (canonicalLambda59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (canonicalLambda59_not_pow K))).2
      (exists_bareLambda_compatibleKummerLift59 K)

/-- The bare-lambda primitive-root cup vanishes in genuine continuous
`H^2(mu_59)`.  This is the actual-cohomology consequence of the explicit
one-plus-root norm witness. -/
theorem bareLambdaKummerCupH2Class59_eq_zero :
    bareLambdaKummerCupH2Class59 K = 0 := by
  have hcarry := bareLambdaRootsCarryH2Class59_eq_zero K
  rw [kummerRootsCarryH2Class_eq_rootsKummerCupObstruction] at hcarry
  simpa [bareLambdaKummerCupH2Class59,
    rootsKummerCupObstruction, bareLambdaRadicandUnit59] using hcarry

/-- In actual continuous `H^2(mu_59)`, the twisted `60 * lambda` cup is
exactly the unit-60 cup.  Kummer multiplicativity supplies the sum, cup
linearity supplies its two terms, and the bare-lambda term is zero. -/
theorem twistedLambdaKummerCupH2Class59_eq_unit60KummerCupH2Class59 :
    twistedLambdaKummerCupH2Class59 K =
      unit60KummerCupH2Class59 K := by
  rw [twistedLambdaKummerCupH2Class59, unit60KummerCupH2Class59]
  rw [continuousClassOfTwistedLambda_eq_unit60_add_bareLambda K]
  rw [map_add, map_add]
  rw [LinearMap.add_apply]
  rw [show lambdaContinuousCup59 K
      (orientH1 59 (LambdaField59 K)
        (lambdaLocalPrimitiveRoot59 K)
        (lambdaLocalPrimitiveRoot59_isPrimitive K)
        (continuousClassOfUnit 59 (LambdaField59 K)
          (bareLambdaRadicandUnit59 K)))
      (continuousClassOfUnit 59 (LambdaField59 K)
        (primitiveUnit 59 (LambdaField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K))) = 0 by
        exact bareLambdaKummerCupH2Class59_eq_zero K]
  exact add_zero _

end Fermat.FiftyNine.Conservation.TwistedLambdaCupUnitReduction59
