/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The normalized finite logarithm in the honest local trace at 59

`TwistedArtinHasse59` computes the rational finite logarithm attached to the
principal unit `60 = 1 + 59` and proves that its degree-58 scalar trace has
residue `-1` modulo `59`.

`LocalCyclotomicTrace59` constructs the previously missing finite algebra

`Q_59 -> K_lambda`

and proves that its degree is exactly `58`.  This file joins those results:
the genuine completed-field trace of the embedded finite logarithm is the
embedded rational scalar computed before.  That scalar lies in the rational
completed integer ring, where the actual residue map sends it to `-1`.

This closes the local-completion trace seam.  It does not yet compare the
finite logarithm to a completed p-adic logarithm, Hilbert symbol, or
Artin--Hasse reciprocity law.
-/
import Fermat.Exponents.FiftyNine.Conservation.TwistedArtinHasse59
import Fermat.Exponents.FiftyNine.Conservation.LocalCyclotomicTrace59

open scoped NumberField Topology Valued

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59

open KummerCriterion.Furtwaengler.KummerArtinHasse
open KummerCriterion.Furtwaengler.DieudonneDwork
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.TwistedArtinHasse59
open Fermat.FiftyNine.Conservation.LocalCyclotomicTrace59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- A `59`-integral rational, embedded in the rational completed integer
ring. -/
def rationalInteger59OfRIntegral (q : ℚ) (hq : IsRIntegralRat 59 q) :
    RationalIntegerRing59 := by
  refine ⟨algebraMap ℚ RationalCompletion59 q, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (algebraMap ℚ RationalCompletion59 q) ≤ 1
  rw [show algebraMap ℚ RationalCompletion59 q =
      ((q : WithVal ((lambdaRationalHeightOneSpectrum 59).valuation ℚ)) :
        RationalCompletion59) from rfl]
  rw [Valued.valuedCompletion_apply]
  apply (lambdaRationalValuation_le_one_iff_den (p := 59) q).2
  have hnot_dvd_nat : ¬ 59 ∣ q.den :=
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 59)).mp hq.symm
  intro hmem
  have hnot_dvd_int : ¬ (59 : ℤ) ∣ (q.den : ℤ) := fun h =>
    hnot_dvd_nat (Int.natCast_dvd_natCast.mp h)
  exact hnot_dvd_int (by
    simpa [lambdaRationalPrimeIdeal, Ideal.mem_span_singleton] using hmem)

@[simp]
theorem rationalInteger59OfRIntegral_coe (q : ℚ)
    (hq : IsRIntegralRat 59 q) :
    ((rationalInteger59OfRIntegral q hq : RationalIntegerRing59) :
        RationalCompletion59) =
      algebraMap ℚ RationalCompletion59 q :=
  rfl

/-- Reduction of the completed-integer representative agrees with direct
reduction of the `59`-integral rational. -/
theorem rationalIntegerToZMod_rationalInteger59OfRIntegral
    (q : ℚ) (hq : IsRIntegralRat 59 q) :
    rationalPadicIntegerToZMod 59 (rationalInteger59OfRIntegral q hq) =
      IsRIntegralRat.toZMod q hq := by
  apply IsRIntegralRat.toZMod_eq_of_den_mul_eq hq
  rw [← rationalPadicIntegerToZMod_natCast (p := 59) q.den]
  rw [← map_mul]
  have hden :
      (q.den : RationalIntegerRing59) * rationalInteger59OfRIntegral q hq =
        (q.num : RationalIntegerRing59) := by
    ext
    change (q.den : RationalCompletion59) *
        algebraMap ℚ RationalCompletion59 q =
      (q.num : RationalCompletion59)
    rw [show (q.den : RationalCompletion59) =
        algebraMap ℚ RationalCompletion59 (q.den : ℚ) by norm_num]
    rw [← map_mul]
    rw [Rat.den_mul_eq_num]
    norm_num
  rw [hden]
  simp

/-- The genuine completed-field trace of the normalized finite logarithm. -/
def normalizedLocalTraceFiniteLog59 : RationalCompletion59 :=
  Algebra.trace RationalCompletion59 (LambdaCompletion59 K)
    (algebraMap RationalCompletion59 (LambdaCompletion59 K)
      (algebraMap ℚ RationalCompletion59 normalizedFiniteLog59))

/-- The genuine local trace is the rational degree-58 scalar trace computed
in `TwistedArtinHasse59`. -/
theorem normalizedLocalTraceFiniteLog59_eq :
    normalizedLocalTraceFiniteLog59 K =
      algebraMap ℚ RationalCompletion59 normalizedTraceFiniteLog59 := by
  simpa [normalizedLocalTraceFiniteLog59, normalizedTraceFiniteLog59] using
    (localTrace59_algebraMap_rat K normalizedFiniteLog59)

/-- The integral representative of the genuine local trace. -/
def normalizedLocalTraceFiniteLog59Integer : RationalIntegerRing59 :=
  rationalInteger59OfRIntegral normalizedTraceFiniteLog59
    normalizedTraceFiniteLog59_isRIntegral

theorem normalizedLocalTraceFiniteLog59_eq_integer_coe :
    normalizedLocalTraceFiniteLog59 K =
      (normalizedLocalTraceFiniteLog59Integer : RationalCompletion59) := by
  rw [normalizedLocalTraceFiniteLog59_eq K]
  rfl

/-- The genuine local trace has residue `-1` in the residue field. -/
theorem normalizedLocalTraceFiniteLog59Integer_mod59 :
    rationalPadicIntegerToZMod 59 normalizedLocalTraceFiniteLog59Integer =
      (-1 : ZMod 59) := by
  rw [normalizedLocalTraceFiniteLog59Integer,
    rationalIntegerToZMod_rationalInteger59OfRIntegral]
  exact normalizedTraceFiniteLog59_mod59

theorem normalizedLocalTraceFiniteLog59Integer_mod59_ne_zero :
    rationalPadicIntegerToZMod 59 normalizedLocalTraceFiniteLog59Integer ≠
      (0 : ZMod 59) := by
  rw [normalizedLocalTraceFiniteLog59Integer_mod59]
  norm_num

/-- In particular, the completed-field trace itself is nonzero. -/
theorem normalizedLocalTraceFiniteLog59_ne_zero :
    normalizedLocalTraceFiniteLog59 K ≠ 0 := by
  intro hzero
  apply normalizedLocalTraceFiniteLog59Integer_mod59_ne_zero
  have hinteger : normalizedLocalTraceFiniteLog59Integer = 0 := by
    apply Subtype.ext
    change (normalizedLocalTraceFiniteLog59Integer : RationalCompletion59) = 0
    rw [← normalizedLocalTraceFiniteLog59_eq_integer_coe K, hzero]
  rw [hinteger, map_zero]

/-- A single statement exposing both the completed-field equality and its
nonzero residue. -/
theorem normalizedLocalTraceFiniteLog59_eq_integer_coe_and_residue :
    normalizedLocalTraceFiniteLog59 K =
        (normalizedLocalTraceFiniteLog59Integer : RationalCompletion59) ∧
      rationalPadicIntegerToZMod 59 normalizedLocalTraceFiniteLog59Integer =
        (-1 : ZMod 59) :=
  ⟨normalizedLocalTraceFiniteLog59_eq_integer_coe K,
    normalizedLocalTraceFiniteLog59Integer_mod59⟩

end Fermat.FiftyNine.Conservation.TwistedArtinHasseLocalTrace59
