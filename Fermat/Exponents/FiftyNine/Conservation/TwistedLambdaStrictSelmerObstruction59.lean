/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The explicit twisted-lambda class is not a strict Selmer class

The normalized local cup receipt has an explicit global left representative

`60 * (zeta_59 - 1)`.

Its lambda valuation is `-1` in Mathlib's multiplicative convention.  Every
class in the empty-support 59-Selmer carrier, by contrast, has valuation
divisible by 59 at every height-one place.  The explicit representative can
therefore not itself be seated in any character eigenspace of the strict
Selmer carrier.

This is deliberately a negative routing result.  It does not say that the
wild functional vanishes on the strict Selmer space: another strict global
class could still have a nonzero local cup against the retained reflected
factor.  It proves that W1's ambient cup-one representative is not, by
itself, the missing W4 transversality witness.
-/
import Fermat.Exponents.FiftyNine.Conservation.CyclotomicSelmerAction59
import Fermat.Exponents.FiftyNine.Conservation.NormalizedContinuousKummerPairing59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaStrictSelmerObstruction59

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.Conservation.WildKummerPairing
open CyclotomicSelmerAction59
open LocalCompletion59
open NormalizedContinuousKummerPairing59
open SplitPrimeFourier827
open TwistedLambdaKummerQuotient59
open VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The explicit global twisted-lambda representative has lambda valuation
`-1` in Mathlib's multiplicative valuation convention. -/
theorem globalTwistedLambdaRadicandUnit59_valuation :
    (lambdaPlace59 K).valuationOfNeZero
        (globalTwistedLambdaRadicandUnit59 K) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  rw [← WithZero.coe_inj]
  rw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
  have h60 := twistUnit59_valuation K
  rw [twistUnit59, valuation_embedding59] at h60
  have hlam := canonicalLambda59_valuation K
  rw [canonicalLambda59] at hlam
  change Valued.v
      (NumberField.FinitePlace.embedding (lambdaPlace59 K)
        (globalPrimitiveRoot59 K) - 1) = _ at hlam
  rw [← map_one (NumberField.FinitePlace.embedding (lambdaPlace59 K)),
    ← map_sub, valuation_embedding59] at hlam
  change (lambdaPlace59 K).valuation K
      ((60 : K) * (globalPrimitiveRoot59 K - 1)) = _
  rw [map_mul, h60, hlam, one_mul, WithZero.exp_eq_coe_ofAdd]

/-- Additive readback of the same valuation calculation. -/
theorem globalTwistedLambdaRadicandUnit59_valuation_toAdd :
    ((lambdaPlace59 K).valuationOfNeZero
        (globalTwistedLambdaRadicandUnit59 K)).toAdd = -1 := by
  rw [globalTwistedLambdaRadicandUnit59_valuation]
  rfl

/-- No character eigenspace of the genuine empty-support 59-Selmer carrier
contains the explicit global Kummer class used to normalize W1's cup.

The obstruction is already visible before checking the character law: its
lambda valuation is not divisible by 59. -/
theorem globalTwistedLambdaKummerClass_not_seated
    (chi : Fermat.Conservation.InvolutiveBase.Character
      (PadicInt 59) GaloisIndex59) :
    ¬ ∃ x : OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K) chi,
      toKummerClass x =
        classOfUnit 59 K
          (Additive.ofMul (globalTwistedLambdaRadicandUnit59 K)) := by
  rintro ⟨x, hx⟩
  have hquot := congrArg Additive.toMul hx
  have hy :
      QuotientGroup.mk' (powMonoidHom 59 : Kˣ →* Kˣ).range
          (globalTwistedLambdaRadicandUnit59 K) =
        toKummerQuotient x := by
    simpa using hquot.symm
  have hdvd := representative_valuation_dvd
    (lambdaPlace59 K) x (globalTwistedLambdaRadicandUnit59 K) hy
  rw [globalTwistedLambdaRadicandUnit59_valuation_toAdd] at hdvd
  norm_num at hdvd

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.TwistedLambdaStrictSelmerObstruction59.globalTwistedLambdaRadicandUnit59_valuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms globalTwistedLambdaRadicandUnit59_valuation

/--
info: 'Fermat.FiftyNine.Conservation.TwistedLambdaStrictSelmerObstruction59.globalTwistedLambdaKummerClass_not_seated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms globalTwistedLambdaKummerClass_not_seated

end Fermat.FiftyNine.Conservation.TwistedLambdaStrictSelmerObstruction59
