/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The full norm criterion for the twisted-lambda Kummer cup

The converse Albert construction turns an exact continuous lift of the
twisted-lambda Kummer character through `C_(59^2)` into an element of the
concrete Kummer extension whose norm is the local primitive root.  Together
with the genuine Kummer-cup lift criterion, this closes both directions of
the norm-residue statement without choosing a scalar readout.

No local invariant, Hilbert-symbol formula, auxiliary witness structure, or
per-prime norm value is introduced here.
-/
import Fermat.Conservation.AlbertCyclicConverse59
import Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59

open Fermat.Conservation.AlbertCyclicConverse59
open Fermat.Conservation.AlbertCyclicQuotient59
open Fermat.FiftyNine.Conservation.LocalCompletion59
open Fermat.FiftyNine.Conservation.TwistedLambdaAlbertCriterion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerCupComparison59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerLiftCriterion59
open Fermat.FiftyNine.Conservation.TwistedLambdaKummerQuotient59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩
local instance : NeZero 3481 := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The local primitive root is a norm from the concrete twisted-lambda
Kummer extension exactly when the genuine twisted-lambda Kummer cup
vanishes. -/
theorem primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero :
    (∃ beta : twistedLambdaKummerExtension59 K,
      Algebra.norm (LambdaField59 K) beta =
        lambdaLocalPrimitiveRoot59 K) ↔
      twistedLambdaKummerCupH2Class59 K = 0 := by
  constructor
  · rintro ⟨beta, hbeta⟩
    exact
      twistedLambdaKummerCupH2Class59_eq_zero_of_primitiveRoot_norm
        K beta hbeta
  · intro hcup
    obtain ⟨psi, hpsi⟩ :=
      (twistedLambdaKummerCupH2Class59_eq_zero_iff_exists_continuous_lift K).mp
        hcup
    apply concreteKummer_exists_norm_of_albertCharacter3481
      (LambdaField59 K)
      (lambdaLocalPrimitiveRoot59 K)
      (twistedLambda59 K)
      (lambdaLocalPrimitiveRoot59_isPrimitive K)
      (twistedLambda59_not_pow K)
      psi
    apply ContinuousMonoidHom.ext
    intro g
    have hpoint := DFunLike.congr_fun hpsi g
    change Fermat.Conservation.ContinuousCarryLiftObstruction59.reduction59
      (psi g) =
        Fermat.Conservation.KummerCyclicQuotient59.kummerCharacter59
          (LambdaField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (twistedLambda59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K)
          (twistedLambda59_not_pow K) g at hpoint
    change Fermat.Conservation.AlbertCyclicCompatibility59.cyclicReduction3481To59
      (psi g) =
        Fermat.Conservation.KummerCyclicQuotient59.kummerCharacter59
          (LambdaField59 K)
          (lambdaLocalPrimitiveRoot59 K)
          (twistedLambda59 K)
          (lambdaLocalPrimitiveRoot59_isPrimitive K)
          (twistedLambda59_not_pow K) g
    exact hpoint

/-- Equivalently, the genuine cup survives exactly when no element of the
twisted-lambda Kummer extension has the local primitive root as its norm. -/
theorem twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm :
    twistedLambdaKummerCupH2Class59 K ≠ 0 ↔
      ¬ ∃ beta : twistedLambdaKummerExtension59 K,
        Algebra.norm (LambdaField59 K) beta =
          lambdaLocalPrimitiveRoot59 K := by
  exact
    (not_congr
      (primitiveRoot_is_norm_iff_twistedLambdaKummerCupH2Class59_eq_zero K)).symm

/-- Pointwise form of the non-norm criterion. -/
theorem twistedLambdaKummerCupH2Class59_ne_zero_iff_every_norm_ne_primitiveRoot :
    twistedLambdaKummerCupH2Class59 K ≠ 0 ↔
      ∀ beta : twistedLambdaKummerExtension59 K,
        Algebra.norm (LambdaField59 K) beta ≠
          lambdaLocalPrimitiveRoot59 K := by
  simpa only [not_exists] using
    twistedLambdaKummerCupH2Class59_ne_zero_iff_primitiveRoot_not_norm K

end Fermat.FiftyNine.Conservation.TwistedLambdaKummerNormCriterion59
