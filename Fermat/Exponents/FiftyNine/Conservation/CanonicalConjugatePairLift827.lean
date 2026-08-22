/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The canonical reflected localization lift at 827

The conjugate-pair source now has both receipts required by the literal
finite-S lift constructor:

* its canonical reflected `(59, 44)` projection has nonzero localization;
* the projected two-prime class obstruction is the identity.

This file composes those results into an actual
`ReflectedQRelaxedLocalizationLift827`.  It also fixes the repository's
explicit base place and records unconditional inhabitation of the canonical
reflected lift type.  No lift, provider, class certificate, or localization
functional remains as an input.
-/
import Fermat.Exponents.FiftyNine.Conservation.CanonicalConjugatePairProjection827
import Fermat.Exponents.FiftyNine.Conservation.ConjugatePairClassSilence827
import Fermat.Exponents.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827

open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.ConjugatePairSource827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalConjugatePairProjection827
open Fermat.FiftyNine.Conservation.ConjugatePairClassSilence827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The literal canonical reflected localization lift constructed from any
actual place over 827. -/
noncomputable def canonicalConjugatePairLift827
    (place : Place827 K) :
    ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
    (conjugatePairSource827 place) place
    (canonical_projected_conjugatePair_coordinate_ne_zero place)
    (projectedCandidateSClassObstruction827_conjugatePair_canonical_eq_one
      place)

/-- The canonical lift based at the explicit residue-kernel place used by
the tame orbit. -/
noncomputable def canonicalBaseConjugatePairLift827 :
    ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59 :=
  canonicalConjugatePairLift827 (tameOrbitBasePlace827 (K := K))

/-- The canonical reflected `(59, 44)` localization-lift type is inhabited
without a lift premise. -/
theorem nonempty_canonicalConjugatePairLift827 :
    Nonempty (ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K)
      canonicalTeichmullerCharacter59 irregularCharacter59) :=
  ⟨canonicalBaseConjugatePairLift827⟩

/-- At every actual place over 827, the pointed localization functional on
the class-silent kernel is nonzero in the canonical reflected mode. -/
theorem canonical_classSilentPointedCoordinate827_ne_zero
    (place : Place827 K) :
    classSilentPointedCoordinate827
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        canonicalTeichmullerCharacter59 irregularCharacter59 place ≠ 0 :=
  (nonempty_cyclotomicReflectedQRelaxedLocalizationLift827_iff
    (K := K) canonicalTeichmullerCharacter59 irregularCharacter59 place).mp
      nonempty_canonicalConjugatePairLift827

end Fermat.FiftyNine.Conservation.CanonicalConjugatePairLift827
