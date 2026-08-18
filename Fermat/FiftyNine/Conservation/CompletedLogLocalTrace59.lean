/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, OpenAI

# The completed logarithm of the principal unit 60

This module puts the concrete principal unit `60 = 1 + 59` into the native
completed-logarithm domain.  Its additive coordinate is exactly the twist
coordinate used by the finite logarithm, so stage 59 of the completed
logarithm is the finite-log receipt already connected to the genuine local
trace.

The final section records the exact remaining interface boundary: the
completed logarithm lives in the formal `lambda`-adic completion, while the
local trace lives on the valued field completion.  The imported library does
not yet provide the reverse completion comparison needed to transport the
full infinite logarithm.
-/
import Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59
import KummerCriterion.CyclotomicUnits.LogDomain

open scoped NumberField Topology Valued WithZero

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59

open KummerCriterion.Furtwaengler.DieudonneDwork
open KummerCriterion.CyclotomicUnits
open KummerCriterion.CyclotomicUnits.PadicLogSetup
open KummerCriterion.CyclotomicUnits.PadicLogSetup.DworkParameter
open Fermat.FiftyNine.Conservation.TwistedArtinHasse59
open Fermat.FiftyNine.Conservation.TwistedFiniteLogLocalTrace59

local instance : Fact (Nat.Prime 59) := ⟨by decide⟩

variable (K : Type) [Field K] [NumberField K]
variable [IsCyclotomicExtension {59} ℚ K]

/-- The unit `60` in the ring of `59`-integral rationals. -/
def principalUnit60RIntegral :
    (KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59)ˣ where
  val := 60
  inv := ⟨(1 : ℚ) / 60, by
    change IsRIntegralRat 59 ((1 : ℚ) / 60)
    norm_num [IsRIntegralRat]⟩
  val_inv := by
    apply Subtype.ext
    change (60 : ℚ) * (1 / 60) = 1
    norm_num
  inv_val := by
    apply Subtype.ext
    change ((1 : ℚ) / 60) * 60 = 1
    norm_num

/-- The principal unit `60 = 1 + 59` in the native completed-log domain. -/
def completedLogUnit60 : completedLogDomain (p := 59) (K := K) := by
  let u : (ValuedIntegerRing 59 K)ˣ :=
    Units.map (rIntegralRatToValuedInteger 59 K).toMonoidHom
      principalUnit60RIntegral
  refine ⟨u, ?_⟩
  apply (KummerCriterion.Ideal.mem_oneUnitsSubgroup).2
  change (u : ValuedIntegerRing 59 K) - 1 ∈ lambdaIdeal 59 K
  have hu : (u : ValuedIntegerRing 59 K) = 60 := by
    change rIntegralRatToValuedInteger 59 K
        (principalUnit60RIntegral :
          KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    change rIntegralRatToValuedInteger 59 K
        (60 : KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    exact map_natCast (rIntegralRatToValuedInteger 59 K) 60
  rw [hu]
  have hcoord : (60 : ValuedIntegerRing 59 K) - 1 = 59 := by norm_num
  rw [hcoord]
  exact Ideal.pow_le_self (by norm_num : (58 : ℕ) ≠ 0)
    (twistLogCoordinate59_mem K)

/-- Its additive principal-unit coordinate is exactly the twist coordinate
used in the finite-log computation. -/
theorem completedLogArg_unit60 :
    completedLogArg (p := 59) (K := K) (completedLogUnit60 K) =
      twistLogCoordinate59 K := by
  rw [completedLogArg]
  have hu : (((completedLogUnit60 K).1 : (ValuedIntegerRing 59 K)ˣ) :
      ValuedIntegerRing 59 K) = 60 := by
    change rIntegralRatToValuedInteger 59 K
        (principalUnit60RIntegral :
          KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    change rIntegralRatToValuedInteger 59 K
        (60 : KummerCriterion.Furtwaengler.DieudonneDwork.rIntegralRatSubring 59) = 60
    exact map_natCast (rIntegralRatToValuedInteger 59 K) 60
  rw [hu]
  norm_num [twistLogCoordinate59]

/-- Stage 59 of the completed logarithm is exactly the package finite-log
receipt already connected to the local algebra trace. -/
theorem completedLog_unit60_eval59_eq_scaledNormalizedFiniteLog59 :
    AdicCompletion.evalₐ (lambdaIdeal 59 K) 59
        (completedLog (p := 59) (K := K) (completedLogUnit60 K)) =
      Ideal.Quotient.mk ((lambdaIdeal 59 K) ^ 59)
        (rIntegralRatToValuedInteger 59 K
          scaledNormalizedFiniteLog59RIntegral) := by
  rw [completedLog_evalₐ_succ (u := completedLogUnit60 K) 58]
  rw [samePrimeFiniteLog_eq_of_eq (p := 59) (K := K) (N := 58)
    (completedLogArg_unit60 K)
    (completedLogArg_mem (p := 59) (K := K) (completedLogUnit60 K))
    (Ideal.pow_le_self (by norm_num : (58 : ℕ) ≠ 0)
      (twistLogCoordinate59_mem K))]
  exact samePrimeFiniteLog_twist59_eq_scaledNormalizedFiniteLog59 K

/-!
## Exact comparison boundary

The theorem above is the strongest comparison currently supported by the
imported completion APIs.  The completed logarithm lives in
`DworkCompleteIntegerRing 59 K`, the formal `lambda`-adic completion of
`ValuedIntegerRing 59 K`, whereas the genuine local algebra trace lives on
`LambdaCompletion59 K`, the valued field completion.

There is a canonical map from `ValuedIntegerRing 59 K` into the formal adic
completion, but the imported library does not expose the reverse comparison
map.  `AdicCompletion.ofAlgEquiv` would construct it from an
`IsAdicComplete (lambdaIdeal 59 K) (ValuedIntegerRing 59 K)` instance; that
instance is precisely what is absent.  Consequently transporting
`completedLog 60` into `LambdaCompletion59 K`, and hence applying the local
trace to the full infinite logarithm, remains a completion-comparison task.
No arithmetic hypothesis is introduced here to conceal that boundary.
-/

end Fermat.FiftyNine.Conservation.CompletedLogLocalTrace59
