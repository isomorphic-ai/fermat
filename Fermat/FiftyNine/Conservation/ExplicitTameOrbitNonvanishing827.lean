/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Nonvanishing of the explicit tame orbit and wild reading at 827

This module joins three independently checked arithmetic facts:

* every generated circular unit has a nonzero inverse-oriented Fourier
  coefficient in every nontrivial even mode;
* a genuine reflected q-relaxed lift has nonzero localization at every place
  over 827;
* the sum of the 58 actual tame symbols is the negative selected product.

Consequently the explicit tame ledger is nonzero, and any wild reading that
satisfies the displayed global reciprocity equation is nonzero as well.  The
reciprocity equation remains a visible hypothesis: this file neither invents
local values nor replaces it with a provider structure.
-/
import Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
import Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
import Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827

open scoped BigOperators NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.FourierPairingProjection827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

universe uK

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

omit [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)] in
/-- The selected value of the actual inverse-oriented primal Fourier wave is
nonzero in every nontrivial even mode. -/
theorem inverseOrientedPrimalUnitWave827_ne_zero_of_even_nontrivial
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (heven : orientedPrimalMode827 omega chi (-1) = 1)
    (hne : orientedPrimalMode827 omega chi ≠ 1)
    (selected : GaloisIndex59) :
    inverseOrientedPrimalUnitWave827 (K := K) omega chi selected ≠ 0 := by
  rw [inverseOrientedPrimalUnitWave827, characterComponent_apply]
  apply mul_ne_zero
  · change fourierCoefficient
        (inverseReindex
          (PrimalOrbitResidue827.fullOrbitUnitReading827
            (canonicalZeta59_isPrimitive (K := K))
            (Credit.generatedUnit (canonicalZeta59_isPrimitive (K := K))
              DetectorWitness827.firstLedgerNode :
                (NumberField.RingOfIntegers K)ˣ)))
        (orientedPrimalMode827 omega chi) ≠ 0
    exact
      inverseReindex_fullOrbitUnitReading827_generatedUnit_fourier_ne_zero
        (K := K) (canonicalZeta59_isPrimitive (K := K))
        (orientedPrimalMode827 omega chi) heven hne
        DetectorWitness827.firstLedgerNode
  · exact Units.ne_zero _

/-- Every selected coordinate of the actual reflected localization wave is
nonzero for a genuine q-relaxed lift. -/
theorem actualReflectedLocalizationWave827_ne_zero_of_lift
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) :
    projectedLocalizationVector827 (rhoQ827 (K := K)) omega chi
      (tameOrbitBasePlace827 (K := K)) lift.source selected ≠ 0 := by
  change qLocalizationCoordinate827 (rhoQ827 (K := K)) omega chi
      (indexedPlaceOrbitEquiv827 K (tameOrbitBasePlace827 (K := K)) selected)
      (qRelaxedReflectedProjector827 (rhoQ827 (K := K)) omega chi
        lift.source) ≠ 0
  exact qLocalizationCoordinate_ne_zero_at_every_place_of_lift
    omega chi lift _

/-- Both honest local factors in the selected Fourier product are nonzero. -/
theorem selectedProduct_actualTameOrbit827_ne_zero
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (heven : orientedPrimalMode827 omega chi (-1) = 1)
    (hne : orientedPrimalMode827 omega chi ≠ 1)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) :
    inverseOrientedPrimalUnitWave827 (K := K) omega chi selected *
      projectedLocalizationVector827 (rhoQ827 (K := K)) omega chi
        (tameOrbitBasePlace827 (K := K)) lift.source selected ≠ 0 := by
  exact mul_ne_zero
    (inverseOrientedPrimalUnitWave827_ne_zero_of_even_nontrivial
      (K := K) omega chi heven hne selected)
    (actualReflectedLocalizationWave827_ne_zero_of_lift
      (K := K) omega chi lift selected)

/-- The complete sum of the 58 actual tame-symbol values is nonzero. -/
theorem sum_actualTameOrbitValue827_ne_zero
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (heven : orientedPrimalMode827 omega chi (-1) = 1)
    (hne : orientedPrimalMode827 omega chi ≠ 1)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) :
    (∑ tau : GaloisIndex59,
      actualTameOrbitValue827 (K := K) omega chi lift tau) ≠ 0 := by
  rw [sum_actualTameOrbitValue827_eq_neg_selectedProduct
    (K := K) omega chi lift selected]
  exact neg_ne_zero.mpr
    (selectedProduct_actualTameOrbit827_ne_zero
      (K := K) omega chi heven hne lift selected)

/-- An explicit global reciprocity equation forces its actual wild reading
to be nonzero.  The equation is retained as the sole global arithmetic input
of this implication. -/
theorem wild_ne_zero_of_actualTameOrbitReciprocity827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (heven : orientedPrimalMode827 omega chi (-1) = 1)
    (hne : orientedPrimalMode827 omega chi ≠ 1)
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (selected : GaloisIndex59) (wildReading : ZMod 59)
    (reciprocity : wildReading + ∑ tau : GaloisIndex59,
      actualTameOrbitValue827 (K := K) omega chi lift tau = 0) :
    wildReading ≠ 0 := by
  rw [wild_eq_selectedProduct_of_actualTameOrbitReciprocity827
    (K := K) omega chi lift selected wildReading reciprocity]
  exact selectedProduct_actualTameOrbit827_ne_zero
    (K := K) omega chi heven hne lift selected

end Fermat.FiftyNine.Conservation.ExplicitTameOrbitNonvanishing827
