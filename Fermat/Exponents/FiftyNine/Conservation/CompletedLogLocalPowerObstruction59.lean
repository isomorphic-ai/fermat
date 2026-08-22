/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The completed-log power obstruction in the actual local field

The completed-log obstruction first rules out a 59th root of `60` inside the
principal-unit domain.  This file proves that no root was lost by restricting
to that domain.  The lambda ideal is the maximal ideal of the actual local
integer ring, and its residue field has characteristic 59.  Consequently, if
an integer unit has 59th power congruent to one, its residue differs from one
by a nilpotent element and hence is itself one.  Such a root is therefore a
principal unit and is excluded by the completed-log theorem.

A hypothetical root in the full local field has valuation one, so it is an
integer unit and the same argument applies.  Thus the concrete local element
`twistUnit59 = 60` is not a 59th power in `K_lambda`.

This is still a power obstruction, not a local norm obstruction.  It does not
assert an Artin--Hasse reciprocity formula, a Hilbert-symbol evaluation, or a
nonvanishing Kummer cup product.
-/
import Fermat.Exponents.FiftyNine.Conservation.CompletedLogPowerObstruction59
import Fermat.Exponents.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

open scoped NumberField Topology Valued WithZero

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59

open KummerCriterion.CyclotomicUnits
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
open Fermat.FiftyNine.Conservation.CompletedLogPowerObstruction59
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The lambda ideal is exactly the maximal ideal of the actual completed
valuation ring. -/
theorem lambdaIdeal59_eq_maximalIdeal :
    lambdaIdeal 59 K =
      IsLocalRing.maximalIdeal (ValuedIntegerRing 59 K) := by
  ext x
  rw [mem_lambdaIdeal_iff_valuation_le_exp_neg_one]
  rw [IsLocalRing.mem_maximalIdeal]
  rw [mem_nonunits_iff]
  have hnonunit :
      (¬ IsUnit x) ↔ Valued.v (x : ValuedCompletion 59 K) < 1 := by
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  rw [hnonunit]
  constructor
  · intro hx
    exact hx.trans_lt (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num)
  · intro hx
    by_cases hx0 : Valued.v (x : ValuedCompletion 59 K) = 0
    · simp [hx0]
    · have hloglt :
          WithZero.log (Valued.v (x : ValuedCompletion 59 K)) < (0 : ℤ) := by
        rw [WithZero.log_lt_iff_lt_exp hx0]
        simpa using hx
      have hlogle :
          WithZero.log (Valued.v (x : ValuedCompletion 59 K)) ≤ (-1 : ℤ) := by
        omega
      exact (WithZero.log_le_iff_le_exp hx0).mp hlogle

/-- The residue field of the lambda-adic integer ring has characteristic
59. -/
theorem lambdaResidueCharP59 :
    CharP (ValuedIntegerRing 59 K ⧸ lambdaIdeal 59 K) 59 := by
  letI : (lambdaIdeal 59 K).IsMaximal := by
    rw [lambdaIdeal59_eq_maximalIdeal K]
    exact IsLocalRing.maximalIdeal.isMaximal _
  apply ringChar.of_eq
  have hpzero :
      (59 : ValuedIntegerRing 59 K ⧸ lambdaIdeal 59 K) = 0 := by
    change Ideal.Quotient.mk (lambdaIdeal 59 K)
      (59 : ValuedIntegerRing 59 K) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (natCast_prime_mem_lambdaIdeal (p := 59) (K := K))
  exact ((Nat.dvd_prime (by decide : Nat.Prime 59)).mp
    (ringChar.dvd hpzero)).resolve_left CharP.ringChar_ne_one

/-- Any 59th root of the principal unit `60` among actual valuation-ring
units is automatically a principal unit, so it belongs to the completed-log
domain. -/
theorem unit_mem_completedLogDomain_of_pow_eq_unit60
    (u : (ValuedIntegerRing 59 K)ˣ)
    (hu : u ^ 59 = (completedLogUnit60 K).1) :
    u ∈ KummerCriterion.Ideal.oneUnitsSubgroup (lambdaIdeal 59 K) := by
  letI : (lambdaIdeal 59 K).IsMaximal := by
    rw [lambdaIdeal59_eq_maximalIdeal K]
    exact IsLocalRing.maximalIdeal.isMaximal _
  let Q := ValuedIntegerRing 59 K ⧸ lambdaIdeal 59 K
  letI : Field Q := Ideal.Quotient.field (lambdaIdeal 59 K)
  letI : CharP Q 59 := lambdaResidueCharP59 K
  let q : ValuedIntegerRing 59 K →+* Q :=
    Ideal.Quotient.mk (lambdaIdeal 59 K)
  have htarget :
      q (((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ) :
          ValuedIntegerRing 59 K) = 1 := by
    rw [← sub_eq_zero, ← map_one q, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (completedLogUnit60 K).2
  have huval :
      ((u : ValuedIntegerRing 59 K) ^ 59) =
        (((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ) :
          ValuedIntegerRing 59 K) := by
    exact congrArg Units.val hu
  have hqpow : (q (u : ValuedIntegerRing 59 K)) ^ 59 = 1 := by
    rw [← map_pow]
    rw [huval]
    exact htarget
  have hsubpow : (q (u : ValuedIntegerRing 59 K) - 1) ^ 59 = 0 := by
    rw [sub_pow_char]
    rw [hqpow]
    simp
  have hsub : q (u : ValuedIntegerRing 59 K) - 1 = 0 :=
    eq_zero_of_pow_eq_zero hsubpow
  rw [KummerCriterion.Ideal.mem_oneUnitsSubgroup]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa [map_sub] using hsub

/-- The actual valuation-ring unit `60` is not a 59th power. -/
theorem completedLogUnit60_not_pow_in_valuedIntegerUnits :
    ¬ ∃ u : (ValuedIntegerRing 59 K)ˣ,
      u ^ 59 = (completedLogUnit60 K).1 := by
  rintro ⟨u, hu⟩
  let v : completedLogDomain (p := 59) (K := K) :=
    ⟨u, unit_mem_completedLogDomain_of_pow_eq_unit60 K u hu⟩
  apply completedLogUnit60_not_pow_in_completedLogDomain K
  refine ⟨v, ?_⟩
  apply Subtype.ext
  exact hu

/-- The concrete principal unit `twistUnit59 = 60` is not a 59th power in
the full actual lambda-adic field. -/
theorem twistUnit59_not_pow_in_localField :
    ¬ ∃ b : LambdaCompletion59 K, b ^ 59 = twistUnit59 K := by
  rintro ⟨b, hb⟩
  have hbvalpow : (Valued.v b) ^ 59 = (1 : ℤᵐ⁰) := by
    calc
      (Valued.v b) ^ 59 = Valued.v (b ^ 59) :=
        (map_pow
          (Valued.v : Valuation (LambdaCompletion59 K) ℤᵐ⁰) b 59).symm
      _ = Valued.v (twistUnit59 K) :=
        congrArg (Valued.v : LambdaCompletion59 K → ℤᵐ⁰) hb
      _ = 1 := twistUnit59_valuation K
  have hbval_ne : Valued.v b ≠ (0 : ℤᵐ⁰) := by
    intro hbzero
    rw [hbzero, zero_pow (by norm_num : (59 : ℕ) ≠ 0)] at hbvalpow
    exact zero_ne_one hbvalpow
  have hblog := congrArg WithZero.log hbvalpow
  simp only [WithZero.log_pow, WithZero.log_one] at hblog
  have hblogzero : WithZero.log (Valued.v b) = 0 := by
    have hmul :
        (59 : ℤ) * WithZero.log (Valued.v b) = 0 := by
      simpa [nsmul_eq_mul] using hblog
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  have hbval : Valued.v b = 1 := by
    have hexplog := WithZero.exp_log hbval_ne
    rw [hblogzero, WithZero.exp_zero] at hexplog
    exact hexplog.symm
  let x : ValuedIntegerRing 59 K := ⟨b, hbval.le⟩
  have hxunit : IsUnit x := by
    exact
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (a := x)).mpr hbval
  let u : (ValuedIntegerRing 59 K)ˣ := hxunit.unit
  have htargetVal :
      ((((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ) :
          ValuedIntegerRing 59 K)) = 60 := by
    change rIntegralRatToValuedInteger 59 K
        (principalUnit60RIntegral :
          KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    change rIntegralRatToValuedInteger 59 K
        (60 : KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    exact map_natCast (rIntegralRatToValuedInteger 59 K) 60
  have htwist : twistUnit59 K = (60 : LambdaCompletion59 K) := by
    rw [twistUnit59]
    exact map_natCast
      (NumberField.FinitePlace.embedding
        (Fermat.FiftyNine.Conservation.LocalCompletion59.lambdaPlace59 K)) 60
  have hpowR :
      x ^ 59 =
        ((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ) := by
    apply Subtype.ext
    change b ^ 59 =
      (((((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ) :
        ValuedIntegerRing 59 K)) : LambdaCompletion59 K)
    calc
      b ^ 59 = twistUnit59 K := hb
      _ = (60 : LambdaCompletion59 K) := htwist
      _ = (((((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ) :
          ValuedIntegerRing 59 K)) : LambdaCompletion59 K) := by
        exact congrArg
          (fun z : ValuedIntegerRing 59 K => (z : LambdaCompletion59 K))
          htargetVal.symm
  have huPow : u ^ 59 = (completedLogUnit60 K).1 := by
    apply Units.ext
    change ((u : ValuedIntegerRing 59 K) ^ 59) =
      ((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ)
    rw [show (u : ValuedIntegerRing 59 K) = x from hxunit.unit_spec]
    exact hpowR
  exact completedLogUnit60_not_pow_in_valuedIntegerUnits K ⟨u, huPow⟩

end Fermat.FiftyNine.Conservation.CompletedLogLocalPowerObstruction59
