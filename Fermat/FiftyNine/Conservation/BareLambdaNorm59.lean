/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The primitive root is a norm for the bare lambda Kummer extension

At the cyclotomic lambda completion, let `lambda = zeta_59 - 1` and let
`alpha^59 = lambda`.  The elementary identity

`Norm(1 + alpha) = 1 + lambda = zeta_59`

gives an explicit norm witness.  This confirms inside Lean that the bare
uniformizer contributes no primitive-root norm obstruction.  Consequently
the nonnorm theorem for the radicand `60 * lambda` must detect the principal
unit twist rather than merely its valuation-one factor.
-/
import Fermat.Conservation.KummerOnePlusRootNorm59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

open scoped NumberField
open Polynomial WithZero

noncomputable section

namespace Fermat.FiftyNine.Conservation.BareLambdaNorm59

open Fermat.Conservation.KummerCyclicQuotient59
open Fermat.Conservation.KummerOnePlusRootNorm59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The canonical cyclotomic lambda is not a 59th power, directly from its
valuation exponent one. -/
theorem canonicalLambda59_not_pow (b : LambdaField59 K) :
    b ^ 59 ≠ canonicalLambda59 K := by
  intro h
  have hv := congrArg (Valued.v : LambdaField59 K → ℤᵐ⁰) h
  rw [map_pow, canonicalLambda59_valuation] at hv
  have hlog := congrArg (WithZero.log : ℤᵐ⁰ → ℤ) hv
  simp only [WithZero.log_pow, WithZero.log_exp] at hlog
  have hdvd : (59 : ℤ) ∣ (-1 : ℤ) :=
    ⟨WithZero.log (Valued.v b), by
      simpa [nsmul_eq_mul] using hlog.symm⟩
  norm_num at hdvd

/-- The bare lambda degree-59 Kummer extension. -/
abbrev bareLambdaKummerExtension59 :
    IntermediateField (LambdaField59 K)
      (AlgebraicClosure (LambdaField59 K)) :=
  kummerExtension59 (LambdaField59 K) (canonicalLambda59 K)

/-- Mathlib's selected 59th root of bare lambda inside its splitting field. -/
def bareLambdaRoot59 : bareLambdaKummerExtension59 K := by
  letI : IsSplittingField (LambdaField59 K)
      (bareLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (canonicalLambda59 K)) :=
    kummerExtension59_isSplittingField
      (LambdaField59 K) (canonicalLambda59 K)
  exact rootOfSplitsXPowSubC (n := 59) (NeZero.pos 59)
    (canonicalLambda59 K) (bareLambdaKummerExtension59 K)

/-- The selected element really is a 59th root of canonical lambda. -/
theorem bareLambdaRoot59_pow :
    bareLambdaRoot59 K ^ 59 =
      algebraMap (LambdaField59 K) (bareLambdaKummerExtension59 K)
        (canonicalLambda59 K) := by
  letI : IsSplittingField (LambdaField59 K)
      (bareLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (canonicalLambda59 K)) :=
    kummerExtension59_isSplittingField
      (LambdaField59 K) (canonicalLambda59 K)
  exact rootOfSplitsXPowSubC_pow (n := 59)
    (canonicalLambda59 K) (bareLambdaKummerExtension59 K)

/-- The explicit one-plus-root witness has norm equal to the local primitive
59th root of unity. -/
theorem norm_one_add_bareLambdaRoot59 :
    Algebra.norm (LambdaField59 K) (1 + bareLambdaRoot59 K) =
      lambdaLocalPrimitiveRoot59 K := by
  letI : IsSplittingField (LambdaField59 K)
      (bareLambdaKummerExtension59 K)
      (kummerPolynomial59 (LambdaField59 K) (canonicalLambda59 K)) :=
    kummerExtension59_isSplittingField
      (LambdaField59 K) (canonicalLambda59 K)
  have hnorm := norm_one_add_kummerRoot59
    (LambdaField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (canonicalLambda59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (canonicalLambda59_not_pow K)
  change Algebra.norm (LambdaField59 K) (1 + bareLambdaRoot59 K) = _
  rw [show Algebra.norm (LambdaField59 K) (1 + bareLambdaRoot59 K) =
      1 + canonicalLambda59 K by exact hnorm]
  rw [canonicalLambda59]
  ring

/-- Existential form: the primitive root is a norm from the bare lambda
Kummer extension. -/
theorem exists_bareLambda_norm_eq_primitiveRoot :
    ∃ beta : bareLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K :=
  ⟨1 + bareLambdaRoot59 K, norm_one_add_bareLambdaRoot59 K⟩

end Fermat.FiftyNine.Conservation.BareLambdaNorm59
