/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Explicit tame-orbit reciprocity at 827

This module combines the honest local tame contexts at all 58 places above
827 with Fourier projection under the complete orbit sum.  Canonical place
coordinates are inverse-oriented relative to the residue-map indices, so the
primal wave is explicitly the selected Fourier component of the inverse-
reindexed raw circular-unit readings.  No pointwise projected comparison is
used.

The final scalar theorem consumes an explicit reciprocity equation between a
wild reading and the sum of these actual tame-symbol values.
-/
import Fermat.FiftyNine.Conservation.LocalReduction827
import Fermat.FiftyNine.Conservation.RawOrbitReciprocity827

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.OrbitPlace827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
open Fermat.FiftyNine.Conservation.FourierPairingProjection827
open Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.RawOrbitReciprocity827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

universe uK

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The residue-field character complementary to the canonically seated
reflected localization wave. -/
abbrev orientedPrimalMode827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    GaloisIndex59 →* (ZMod 59)ˣ :=
  reducedCharacter59 (InvolutiveBase.reflectedCharacter omega chi)

/-- The actual raw circular-unit residue vector in canonical place
coordinates, projected to its correctly oriented character mode.

This deliberately projects `inverseOrientedFullOrbitUnitReading827`; it is
not the older unreindexed circular-unit wave. -/
noncomputable def inverseOrientedPrimalUnitWave827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    GaloisIndex59 → ZMod 59 :=
  characterComponent
    (inverseOrientedFullOrbitUnitReading827 (K := K))
    (orientedPrimalMode827 omega chi)

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
theorem inverseOrientedPrimalUnitWave827_isPureCharacter
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    IsPureCharacter (orientedPrimalMode827 omega chi)
      (inverseOrientedPrimalUnitWave827 (K := K) omega chi) := by
  exact ⟨fourierCoefficient
    (inverseOrientedFullOrbitUnitReading827 (K := K))
    (orientedPrimalMode827 omega chi), rfl⟩

/-- The explicit base place whose regular orbit is used by the actual tame
contexts. -/
noncomputable abbrev tameOrbitBasePlace827 : Place827 K :=
  orbitPlace827Subtype
    (canonicalZeta59_isPrimitive (K := K)) 1

/-- The actual tame-symbol value at canonical place index `tau`.  The local
context is indexed by `tau⁻¹`, exactly as forced by the explicit place
orbit equivalence. -/
noncomputable def actualTameOrbitValue827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) : ZMod 59 :=
  (tameContext827
      (hZeta := canonicalZeta59_isPrimitive (K := K)) tau⁻¹).value
    (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
      (Credit.generatedUnit (canonicalZeta59_isPrimitive (K := K))
          DetectorWitness827.firstLedgerNode :
        (NumberField.RingOfIntegers K)ˣ))
    lift.candidateRepresentative

/-- The actual local symbol is the pointwise product of the inverse-oriented
raw circular-unit residue and the genuine projected q-localization wave. -/
theorem actualTameOrbitValue827_eq_raw_product
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) :
    actualTameOrbitValue827 (K := K) omega chi lift tau =
      inverseOrientedFullOrbitUnitReading827 (K := K) tau *
        projectedLocalizationVector827 (rhoQ827 (K := K)) omega chi
          (tameOrbitBasePlace827 (K := K)) lift.source tau := by
  exact actualTameReading827_eq_inverseOriented_raw_product
    (K := K) omega chi lift tau

/-- The canonical reflected localization really is the inverse character
wave complementary to the oriented primal mode. -/
theorem actualReflectedLocalizationWave827_isPureCharacter
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi) :
    IsPureCharacter (orientedPrimalMode827 omega chi)⁻¹
      (projectedLocalizationVector827 (rhoQ827 (K := K)) omega chi
        (tameOrbitBasePlace827 (K := K)) lift.source) := by
  exact projectedLocalization_isPureCharacter
    (rhoQ827 (K := K)) omega chi
    (tameOrbitBasePlace827 (K := K))
    (cyclotomicQLocalizationEquivariance827 K omega chi
      (tameOrbitBasePlace827 (K := K)))
    lift.source

/-- Summing all 58 actual local tame-symbol values performs the Fourier
projection under the sum.  The result is the negative product of the honest
inverse-oriented primal wave and the reflected localization wave at any
selected orbit index. -/
theorem sum_actualTameOrbitValue827_eq_neg_selectedProduct
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) :
    (∑ tau : GaloisIndex59,
        actualTameOrbitValue827 (K := K) omega chi lift tau) =
      -(inverseOrientedPrimalUnitWave827 (K := K) omega chi selected *
        projectedLocalizationVector827 (rhoQ827 (K := K)) omega chi
          (tameOrbitBasePlace827 (K := K)) lift.source selected) := by
  let eta := orientedPrimalMode827 omega chi
  let raw := inverseOrientedFullOrbitUnitReading827 (K := K)
  let reflected := projectedLocalizationVector827 (rhoQ827 (K := K))
    omega chi (tameOrbitBasePlace827 (K := K)) lift.source
  have hactual :
      (∑ tau : GaloisIndex59,
          actualTameOrbitValue827 (K := K) omega chi lift tau) =
        ∑ tau : GaloisIndex59, raw tau * reflected tau := by
    apply Finset.sum_congr rfl
    intro tau _
    exact actualTameOrbitValue827_eq_raw_product
      (K := K) omega chi lift tau
  have hreflected : IsPureCharacter eta⁻¹ reflected := by
    exact actualReflectedLocalizationWave827_isPureCharacter
      (K := K) omega chi lift
  calc
    (∑ tau : GaloisIndex59,
        actualTameOrbitValue827 (K := K) omega chi lift tau) =
        ∑ tau : GaloisIndex59, raw tau * reflected tau := hactual
    _ = ∑ tau : GaloisIndex59,
        characterComponent raw eta tau * reflected tau :=
      sum_mul_pureInverse_eq_sum_characterComponent_mul
        galoisIndex59_card eta raw reflected hreflected
    _ = -(characterComponent raw eta selected * reflected selected) :=
      galoisIndex59_sum_pointwiseProduct_eq_neg_selected eta
        (characterComponent raw eta) reflected selected
        ⟨fourierCoefficient raw eta, rfl⟩ hreflected
    _ = -(inverseOrientedPrimalUnitWave827 (K := K) omega chi selected *
        projectedLocalizationVector827 (rhoQ827 (K := K)) omega chi
          (tameOrbitBasePlace827 (K := K)) lift.source selected) := rfl

/-- A concrete reciprocity equation for the wild place and these 58 actual
tame values immediately identifies the wild scalar with the selected
inverse-oriented Fourier product. -/
theorem wild_eq_selectedProduct_of_actualTameOrbitReciprocity827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) (wild : ZMod 59)
    (reciprocity : wild + ∑ tau : GaloisIndex59,
      actualTameOrbitValue827 (K := K) omega chi lift tau = 0) :
    wild = inverseOrientedPrimalUnitWave827 (K := K) omega chi selected *
      projectedLocalizationVector827 (rhoQ827 (K := K)) omega chi
        (tameOrbitBasePlace827 (K := K)) lift.source selected := by
  let eta := orientedPrimalMode827 omega chi
  let raw := inverseOrientedFullOrbitUnitReading827 (K := K)
  let reflected := projectedLocalizationVector827 (rhoQ827 (K := K))
    omega chi (tameOrbitBasePlace827 (K := K)) lift.source
  have hreflected : IsPureCharacter eta⁻¹ reflected := by
    exact actualReflectedLocalizationWave827_isPureCharacter
      (K := K) omega chi lift
  have hsum :
      (∑ tau : GaloisIndex59,
          actualTameOrbitValue827 (K := K) omega chi lift tau) =
        ∑ tau : GaloisIndex59, raw tau * reflected tau := by
    apply Finset.sum_congr rfl
    intro tau _
    exact actualTameOrbitValue827_eq_raw_product
      (K := K) omega chi lift tau
  rw [hsum] at reciprocity
  change wild = characterComponent raw eta selected * reflected selected
  exact wild_eq_selectedComponent_of_raw_reciprocity
    galoisIndex59_card eta raw reflected selected hreflected wild reciprocity

end Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
