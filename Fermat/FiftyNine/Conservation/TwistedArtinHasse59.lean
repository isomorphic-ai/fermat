/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The computable Artin--Hasse half for the 60-twisted lambda radicand

For the explicit radicand

`a_59 = (1 + 59) * (zeta_59 - 1)`,

this file computes the principal-unit contribution without postulating a
Hilbert symbol or a local invariant.  The actual twist coordinate is `59`.
The pinned KummerCriterion finite logarithm therefore gives

`log(1 + 59) = 59 (mod lambda^59)`.

After dividing the finite rational logarithm by `59`, its residue is `1`.
The cyclotomic degree is `58`, so the honest global trace of that rational
scalar has residue

`58 = -1 (mod 59)`,

and is nonzero.

The remaining seam is explicit.  The pinned stack does not currently supply
a finite-dimensional algebra structure for the lambda completion over the
rational 59-adic completion, hence it does not expose the required local
trace.  This file therefore does **not** identify the package finite quotient
or the global scalar trace with a completed-field logarithmic trace, a
59-Hilbert-symbol exponent, an Artin--Hasse reciprocity formula, or Albert's
cyclic-embedding obstruction.  Those are comparison theorems still to be
proved, not definitions or assumptions installed here.
-/
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59
import KummerCriterion.CyclotomicUnits.DworkParameter.Part16

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.TwistedArtinHasse59

open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open KummerCriterion.Furtwaengler.DieudonneDwork
open TwistedLambdaKummerQuotient59
open LocalCompletion59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The principal-unit coordinate of the twist really is `59` in the
concrete completion used by `twistedLambda59`. -/
theorem twistUnit59_sub_one :
    twistUnit59 K - 1 = (59 : LambdaField59 K) := by
  rw [twistUnit59]
  rw [map_ofNat]
  norm_num

/-- The Fermat-side and pinned KummerCriterion-side names designate the same
height-one cyclotomic place. -/
theorem lambdaPlace59_eq_kummerCriterion :
    lambdaPlace59 K =
      KummerCriterion.Furtwaengler.KummerArtinHasse.lambdaHeightOneSpectrum 59 K := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rfl

/-- The rational principal-unit coordinate of `60 = 1 + 59` in the
valuation-completion integer ring. -/
def twistLogCoordinate59 : ValuedIntegerRing 59 K := 59

/-- The field coordinate `twistUnit59 - 1` and the pinned finite-log integer
coordinate are the same element after identifying the two equal place
records. -/
theorem twistUnit59_sub_one_heq_coordinate :
    HEq (twistUnit59 K - 1)
      ((twistLogCoordinate59 K : ValuedIntegerRing 59 K) :
        ValuedCompletion 59 K) := by
  rw [twistUnit59_sub_one]
  cases lambdaPlace59_eq_kummerCriterion K
  rfl

/-- Exact ramification puts the coordinate `59` in `lambda^58`. -/
theorem twistLogCoordinate59_mem :
    twistLogCoordinate59 K ∈ (lambdaIdeal 59 K) ^ 58 := by
  simpa [twistLogCoordinate59] using
    (natCast_prime_pow_mem_lambdaIdeal_pow (p := 59) (K := K)
      (M := 1) (N := 58) (by norm_num))

/-- The package's ordinary same-prime finite logarithm computes
`log(1 + 59) = 59 (mod lambda^59)`.  This is the analytic input before
applying a local trace or a Hilbert-symbol comparison. -/
theorem samePrimeFiniteLog_twist59_eq :
    samePrimeFiniteLog (p := 59) (K := K) 58 (twistLogCoordinate59 K)
        (Ideal.pow_le_self (by norm_num : (58 : ℕ) ≠ 0)
          (twistLogCoordinate59_mem K)) =
      Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 59)
        (twistLogCoordinate59 K) := by
  simpa using
    (samePrimeFiniteLog_eq_mk_of_mem_pow_of_two_le
      (p := 59) (K := K) (m := 58) (by norm_num : 2 ≤ (58 : ℕ))
      (twistLogCoordinate59_mem K))

/-- The rational finite logarithm of `1 + 59`, divided by `59`, with all
terms whose denominators are prime to `59`. -/
def normalizedFiniteLog59 : ℚ :=
  ∑ n ∈ Finset.Icc (1 : ℕ) 58,
    (-1 : ℚ) ^ (n + 1) * (59 : ℚ) ^ (n - 1) / (n : ℚ)

theorem normalizedFiniteLog59_isRIntegral :
    IsRIntegralRat 59 normalizedFiniteLog59 := by
  norm_num [IsRIntegralRat, normalizedFiniteLog59, Finset.sum_Icc_succ_top]

theorem normalizedFiniteLog59_mod59 :
    IsRIntegralRat.toZMod normalizedFiniteLog59
        normalizedFiniteLog59_isRIntegral = (1 : ZMod 59) := by
  norm_num [IsRIntegralRat.toZMod, normalizedFiniteLog59,
    Finset.sum_Icc_succ_top]
  have hA :
      (80555079295066255906699197893286436591787728248672327470683236662754034614329977712555357121493244870740213479663565219471 :
        ZMod 59) = 52 := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq]
  have hB : (54749786241679275146400 : ZMod 59) = 7 := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    norm_num [Nat.ModEq]
  rw [hA, hB]
  have hneg : -(52 : ZMod 59) = 7 := by
    change ((-52 : ℤ) : ZMod 59) = ((7 : ℤ) : ZMod 59)
    apply (ZMod.intCast_eq_intCast_iff _ _ _).2
    norm_num [Int.ModEq]
  rw [← neg_mul, hneg]
  exact ZMod.coe_mul_inv_eq_one 7 (by norm_num)

/-- On a rational scalar, the degree-58 trace multiplies by 58.  This is the
finite scalar expected from `Tr(log(60))/59`. -/
def normalizedTraceFiniteLog59 : ℚ :=
  58 * normalizedFiniteLog59

/-- The global cyclotomic field has degree `phi(59) = 58`.  The same degree
is expected for its lambda-adic completion over `Q_59`, but that local
finite-dimensional instance is not supplied by the pinned stack. -/
theorem cyclotomicFinrank59 : Module.finrank ℚ K = 58 := by
  rw [IsCyclotomicExtension.finrank (K := ℚ) (L := K)
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos 59)),
    Nat.totient_prime (by decide : Nat.Prime 59)]

/-- The honest global trace calculation for the rational finite-log scalar:
trace of a base scalar is degree times that scalar. -/
theorem trace_algebraMap_normalizedFiniteLog59 :
    Algebra.trace ℚ K (algebraMap ℚ K normalizedFiniteLog59) =
      normalizedTraceFiniteLog59 := by
  rw [Algebra.trace_algebraMap, cyclotomicFinrank59 K]
  simp [normalizedTraceFiniteLog59, nsmul_eq_mul]

theorem normalizedTraceFiniteLog59_isRIntegral :
    IsRIntegralRat 59 normalizedTraceFiniteLog59 := by
  have h58 : IsRIntegralRat 59 (58 : ℚ) := by
    norm_num [IsRIntegralRat]
  exact h58.mul normalizedFiniteLog59_isRIntegral

theorem normalizedTraceFiniteLog59_mod59 :
    IsRIntegralRat.toZMod normalizedTraceFiniteLog59
        normalizedTraceFiniteLog59_isRIntegral = (-1 : ZMod 59) := by
  have h58 : IsRIntegralRat 59 (58 : ℚ) := by
    norm_num [IsRIntegralRat]
  calc
    IsRIntegralRat.toZMod normalizedTraceFiniteLog59
        normalizedTraceFiniteLog59_isRIntegral =
        IsRIntegralRat.toZMod (58 : ℚ) h58 *
          IsRIntegralRat.toZMod normalizedFiniteLog59
            normalizedFiniteLog59_isRIntegral := by
      simpa [normalizedTraceFiniteLog59] using
        (IsRIntegralRat.toZMod_mul h58 normalizedFiniteLog59_isRIntegral)
    _ = (58 : ZMod 59) * 1 := by
      rw [normalizedFiniteLog59_mod59]
      norm_num [IsRIntegralRat.toZMod]
    _ = -1 := by
      simp only [mul_one]
      change ((58 : ℤ) : ZMod 59) = ((-1 : ℤ) : ZMod 59)
      apply (ZMod.intCast_eq_intCast_iff _ _ _).2
      norm_num [Int.ModEq]

theorem normalizedTraceFiniteLog59_mod59_ne_zero :
    IsRIntegralRat.toZMod normalizedTraceFiniteLog59
        normalizedTraceFiniteLog59_isRIntegral ≠ (0 : ZMod 59) := by
  rw [normalizedTraceFiniteLog59_mod59]
  norm_num

/-- The corresponding **global scalar-trace** congruence, stated directly
with `Algebra.trace`.  It is not yet the missing local-completion trace
comparison. -/
theorem trace_algebraMap_normalizedFiniteLog59_isRIntegral :
    IsRIntegralRat 59
      (Algebra.trace ℚ K (algebraMap ℚ K normalizedFiniteLog59)) := by
  rw [trace_algebraMap_normalizedFiniteLog59 K]
  exact normalizedTraceFiniteLog59_isRIntegral

theorem trace_algebraMap_normalizedFiniteLog59_mod59 :
    IsRIntegralRat.toZMod
        (Algebra.trace ℚ K (algebraMap ℚ K normalizedFiniteLog59))
        (trace_algebraMap_normalizedFiniteLog59_isRIntegral K) =
      (-1 : ZMod 59) := by
  simpa only [trace_algebraMap_normalizedFiniteLog59 K] using
    normalizedTraceFiniteLog59_mod59

theorem trace_algebraMap_normalizedFiniteLog59_mod59_ne_zero :
    IsRIntegralRat.toZMod
        (Algebra.trace ℚ K (algebraMap ℚ K normalizedFiniteLog59))
        (trace_algebraMap_normalizedFiniteLog59_isRIntegral K) ≠
      (0 : ZMod 59) := by
  rw [trace_algebraMap_normalizedFiniteLog59_mod59 K]
  norm_num

end Fermat.FiftyNine.Conservation.TwistedArtinHasse59
