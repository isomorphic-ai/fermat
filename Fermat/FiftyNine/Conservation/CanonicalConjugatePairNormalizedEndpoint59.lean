/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The normalized endpoint with the canonical 827 lift installed

The canonical conjugate-pair construction discharges the geometric lift
input of the normalized continuous-readout branch.  This module installs
that concrete lift in the existing coefficient diagnostic and conditional
relation-(7a) endpoint.

The one-column reciprocity used by this historical branch still makes the
normalized coefficient zero.  Accordingly the remaining processing premise
is still equivalent to vanishing of the complete class-valued gauge; the
theorems below preserve that warning rather than presenting a circular
conditional as a proof of relation (7a).
-/
import Fermat.FiftyNine.Conservation.CanonicalConjugatePairIncidence827
import Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59

open scoped MonoidAlgebra nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59

open Fermat.Conservation
open Fermat.Conservation.LinkingInterfaces
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.NormalizedContinuousReadout59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.TateBridge
open Fermat.FiftyNine.Conservation.UlamReadout827
open Fermat.FiftyNine.Conservation.VostokovLocalization59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

noncomputable local instance instCanonicalOldPrimal59ModuleZMod :
    Module (ZMod 59)
      (OldPrimal59 (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59) :=
  AddCommGroup.zmodModule
    (oldPrimal59_nsmul_eq_zero K irregularCharacter59)

/-- The still-explicit one-column reciprocity input, specialized only to the
canonical irregular characters. -/
abbrev CanonicalConjugatePairTameSilenceReciprocity59 :=
  NormalizedTameSilenceReciprocity59 K
    canonicalTeichmullerCharacter59 irregularCharacter59

/-- The normalized continuous wild coefficient with the genuine canonical
827 lift installed. -/
noncomputable def canonicalConjugatePairNormalizedWildCoefficient59
    (execution : CanonicalConjugatePairTameSilenceReciprocity59 K) :
    H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59) →ₗ[ZMod 59] ZMod 59 :=
  normalizedWildCoefficientOfCanonicalLift59 K
    canonicalTeichmullerCharacter59 irregularCharacter59
    (canonicalBaseConjugatePairLift827 (K := K)) execution

/-- The concrete lift removes a geometric premise but does not repair the
old one-column reciprocity: that interface still annihilates its coefficient. -/
theorem canonicalConjugatePairNormalizedWildCoefficient59_eq_zero
    (execution : CanonicalConjugatePairTameSilenceReciprocity59 K) :
    canonicalConjugatePairNormalizedWildCoefficient59 K execution = 0 :=
  normalizedWildCoefficientOfCanonicalLift59_eq_zero K
    canonicalTeichmullerCharacter59 irregularCharacter59
    (canonicalBaseConjugatePairLift827 (K := K)) execution

variable {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
variable {solution : FermatState.PrimitiveSecondCaseSolution}
variable {hz : (59 : ℤ) ∣ solution.z}

/-- Exact circularity diagnostic after installing the genuine lift: the old
processing premise is equivalent to vanishing of the entire class gauge. -/
theorem canonicalConjugatePairProcessesAtLeastSevenA_iff_gauge_eq_zero
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (execution : CanonicalConjugatePairTameSilenceReciprocity59 K) :
    WildProcessesAtLeastSevenA gaugeSeating
        (canonicalConjugatePairNormalizedWildCoefficient59 K execution) ↔
      gaugeSeating.gauge = 0 :=
  normalizedCanonicalLiftProcessesAtLeastSevenA_iff_gauge_eq_zero K
    canonicalTeichmullerCharacter59 irregularCharacter59
    (canonicalBaseConjugatePairLift827 (K := K))
    pair hF gaugeSeating execution

/-- The existing normalized endpoint with its former lift argument removed.
This remains deliberately conditional on the processing premise whose exact
circularity is proved immediately above. -/
theorem vandiverSevenA_of_normalizedContinuousCanonicalConjugatePair
    (pair : StateLinkedIdealPair hZeta solution hz)
    (hF : H_FLT (OldPrimal59
      (cyclotomicStrictSelmerRepresentation59 K)
      irregularCharacter59))
    (gaugeSeating : ClassValuedSevenAGaugeSeating pair hF)
    (execution : CanonicalConjugatePairTameSilenceReciprocity59 K)
    (processes : WildProcessesAtLeastSevenA gaugeSeating
      (canonicalConjugatePairNormalizedWildCoefficient59 K execution)) :
    pair.ledger.VandiverSevenA 0 1 :=
  vandiverSevenA_of_normalizedContinuousCanonicalLift K
    canonicalTeichmullerCharacter59 irregularCharacter59
    (canonicalBaseConjugatePairLift827 (K := K))
    pair hF gaugeSeating execution processes

end Fermat.FiftyNine.Conservation.CanonicalConjugatePairNormalizedEndpoint59
