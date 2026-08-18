/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The 60-twisted lambda Kummer quotient at 59

Let `F` be the completion of the 59th cyclotomic field at
`lambda = (zeta_59 - 1)`.  This file replaces an unspecified uniformizer by
the concrete radicand

`a_59 = (1 + 59) * (zeta_59 - 1) = 60 * (zeta_59 - 1)`.

The factor `60` is a lambda-adic unit, so `a_59` still has valuation one.
Consequently it is not a 59th power, and the generic Kummer construction
supplies an honest surjective continuous character

`AbsoluteGalois F -> Multiplicative (ZMod 59)`.

The unit twist is selected for the remaining arithmetic seam: the classical
Artin--Hasse special-value formula predicts that `(1 + 59, zeta_59)_59` is
nontrivial, while the bare lambda factor has trivial symbol against
`zeta_59`.  Together with Albert's cyclic-embedding criterion, that would
show that the character below does not lift through
`Multiplicative (ZMod (59 ^ 2))`.

Neither the Artin--Hasse comparison nor Albert's criterion is proved here.
In particular, this module asserts no non-norm theorem and no no-lift
theorem.
-/
import Fermat.Conservation.KummerCyclicQuotient59
import Fermat.FiftyNine.Conservation.LocalCompletion59
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Tactic

open scoped NumberField
open Polynomial WithZero

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

open LocalCompletion59

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

/-- A short name for the actual completion at
`lambda = (zeta_59 - 1)`. -/
abbrev LambdaField59 := LambdaLocalField59 K

/-- Valuation is preserved by the canonical embedding into the adic
completion. -/
theorem valuation_embedding59 (x : K) :
    Valued.v (NumberField.FinitePlace.embedding (lambdaPlace59 K) x) =
      (lambdaPlace59 K).valuation K x :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
    (lambdaPlace59 K) x

/-- The concrete cyclotomic uniformizer in the completed field. -/
def canonicalLambda59 : LambdaField59 K :=
  lambdaLocalPrimitiveRoot59 K - 1

/-- The canonical cyclotomic lambda has valuation one. -/
@[simp]
theorem canonicalLambda59_valuation :
    Valued.v (canonicalLambda59 K) = WithZero.exp (-1 : ℤ) := by
  rw [canonicalLambda59]
  change Valued.v
    (NumberField.FinitePlace.embedding (lambdaPlace59 K)
      (globalPrimitiveRoot59 K) - 1) = _
  rw [← map_one (NumberField.FinitePlace.embedding (lambdaPlace59 K)),
    ← map_sub, valuation_embedding59]
  rw [show globalPrimitiveRoot59 K - 1 =
      algebraMap (𝓞 K) K
        ((globalPrimitiveRoot59_isPrimitive K).toInteger - 1) by simp]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
  · exact (globalPrimitiveRoot59_isPrimitive K).zeta_sub_one_prime'.ne_zero
  · rfl

/-- The explicit principal unit `1 + 59`, embedded in the completed field. -/
def twistUnit59 : LambdaField59 K :=
  NumberField.FinitePlace.embedding (lambdaPlace59 K) (60 : K)

/-- Since `60` is congruent to one modulo 59, it is a unit at lambda. -/
@[simp]
theorem twistUnit59_valuation : Valued.v (twistUnit59 K) = 1 := by
  rw [twistUnit59, valuation_embedding59]
  change (lambdaPlace59 K).valuation K (60 : K) = 1
  have h60 : (60 : K) = algebraMap (𝓞 K) K (60 : 𝓞 K) :=
    (map_natCast (algebraMap (𝓞 K) K) 60).symm
  rw [h60]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hmem
  letI : (lambdaIdeal59 K).LiesOver
      (Ideal.span ({(59 : ℤ)} : Set ℤ)) :=
    lambdaIdeal59_liesOver K
  have hcomap : (60 : ℤ) ∈ Ideal.span ({(59 : ℤ)} : Set ℤ) :=
    (Ideal.mem_of_liesOver (P := lambdaIdeal59 K)
      (p := Ideal.span ({(59 : ℤ)} : Set ℤ)) (60 : ℤ)).mpr (by
        simpa [lambdaPlace59_asIdeal] using hmem)
  norm_num [Ideal.mem_span_singleton] at hcomap

/-- The concrete 60-twisted lambda radicand. -/
def twistedLambda59 : LambdaField59 K :=
  twistUnit59 K * canonicalLambda59 K

/-- The unit twist preserves the defining lambda valuation. -/
@[simp]
theorem twistedLambda59_valuation :
    Valued.v (twistedLambda59 K) = WithZero.exp (-1 : ℤ) := by
  rw [twistedLambda59, map_mul, twistUnit59_valuation,
    canonicalLambda59_valuation, one_mul]

/-- The twisted radicand cannot be a 59th power: its valuation exponent is
one, which is not divisible by 59. -/
theorem twistedLambda59_not_pow (b : LambdaField59 K) :
    b ^ 59 ≠ twistedLambda59 K := by
  intro h
  have hv := congrArg (Valued.v : LambdaField59 K → ℤᵐ⁰) h
  rw [map_pow, twistedLambda59_valuation] at hv
  have hlog := congrArg (WithZero.log : ℤᵐ⁰ → ℤ) hv
  simp only [WithZero.log_pow, WithZero.log_exp] at hlog
  have hdvd : (59 : ℤ) ∣ (-1 : ℤ) :=
    ⟨WithZero.log (Valued.v b), by
      simpa [nsmul_eq_mul] using hlog.symm⟩
  norm_num at hdvd

/-- The Kummer polynomial attached to the twisted lambda radicand. -/
abbrev twistedLambdaPolynomial59 : (LambdaField59 K)[X] :=
  X ^ 59 - C (twistedLambda59 K)

/-- The concrete twisted-lambda Kummer polynomial is irreducible. -/
theorem twistedLambdaPolynomial59_irreducible :
    Irreducible (twistedLambdaPolynomial59 K) := by
  exact
    Fermat.Conservation.KummerCyclicQuotient59.kummerPolynomial59_irreducible
      (LambdaField59 K) (twistedLambda59 K) (twistedLambda59_not_pow K)

/-- The concrete degree-59 Kummer extension generated by the roots of the
twisted-lambda polynomial. -/
abbrev twistedLambdaKummerExtension59 :
    IntermediateField (LambdaField59 K)
      (AlgebraicClosure (LambdaField59 K)) :=
  Fermat.Conservation.KummerCyclicQuotient59.kummerExtension59
    (LambdaField59 K) (twistedLambda59 K)

/-- The continuous Kummer character for the concrete twisted radicand. -/
def twistedLambdaKummerCharacter59 :
    Field.absoluteGaloisGroup (LambdaField59 K) →ₜ*
      Multiplicative (ZMod 59) :=
  Fermat.Conservation.KummerCyclicQuotient59.kummerCharacter59
    (LambdaField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (twistedLambda59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (twistedLambda59_not_pow K)

/-- Every cyclic coordinate occurs under the concrete twisted-lambda Kummer
character. -/
theorem twistedLambdaKummerCharacter59_surjective :
    Function.Surjective (twistedLambdaKummerCharacter59 K) :=
  Fermat.Conservation.KummerCyclicQuotient59.kummerCharacter59_surjective
    (LambdaField59 K)
    (lambdaLocalPrimitiveRoot59 K)
    (twistedLambda59 K)
    (lambdaLocalPrimitiveRoot59_isPrimitive K)
    (twistedLambda59_not_pow K)

end Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
