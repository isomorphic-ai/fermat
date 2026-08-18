/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The honest algebraic W7 closure boundary

Fix a genuine relaxed 827 class and hence the concrete full tame-orbit
functional on the strict Selmer carrier.  If an explicit scalar readout of
the actual 59-torsion ideal-class carrier is supplied, its composition with
the actual Fermat-factor class gauge is that orbit functional, and the
readout is injective, then the two maps have the same pointwise zero locus.

At the actual plus-minus Fermat-factor Selmer difference, the committed
class-gauge seating identifies the class value with `selectedClassGauge59`.
The same kernel comparison therefore says that orbit silence is equivalent
to the actual selected relation-7A class vanishing, and hence to Vandiver's
relation (7a).

This is deliberately a partial W7 closure.  It does not construct or assume
an Artin map through a provider: the readout, its exact map-level
factorization, and its injectivity remain separate visible inputs.  Their
existence and arithmetic nonvanishing are the remaining Kummer--Artin work.
-/
import Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open CanonicalFullOrbitLocalPairing827
open CyclotomicSelmerClassNaturality59
open FermatFactorClassGaugeSeating59
open FermatFactorSelmerGauge59
open SplitPrimeFourier827
open StateFactorPair
open StrictTameOrbitClassFactorization827
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

/-- An injective class readout whose pullback is the concrete 827 orbit
functional detects exactly the zero class-gauge values, point by point.

The three arithmetic objects are explicit arguments: the readout itself,
the equality of linear maps, and injectivity. -/
theorem strictTameOrbitFunctional827_eq_zero_iff_classGauge_eq_zero
    (y : RelaxedCarrier827 K)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (readout_injective : Function.Injective readout)
    (x : StrictCarrier59 K) :
    strictTameOrbitFunctional827 K y x = 0 ↔
      fermatFactorClassGaugeMap59 (K := K) x = 0 := by
  have apply_factorization := LinearMap.congr_fun factorization x
  constructor
  · intro orbit_zero
    apply readout_injective
    rw [map_zero]
    calc
      readout (fermatFactorClassGaugeMap59 (K := K) x) =
          strictTameOrbitFunctional827 K y x := apply_factorization
      _ = 0 := orbit_zero
  · intro gauge_zero
    calc
      strictTameOrbitFunctional827 K y x =
          readout (fermatFactorClassGaugeMap59 (K := K) x) :=
        apply_factorization.symm
      _ = 0 := by rw [gauge_zero, map_zero]

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The two carriers genuinely coincide at the Fermat-factor input: the
actual strict-Selmer class map evaluates to the already selected class-valued
relation-7A word. -/
theorem fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59
    (pair : StateLinkedIdealPair hZeta S hz) :
    fermatFactorClassGaugeMap59 (K := K)
        (fermatFactorSelmerDifference59 pair) =
      selectedClassGauge59 pair := by
  exact (fermatFactorClassGaugeSeating59 pair).gauge_at_fermat

/-- W7 at the actual Fermat input, with every still-missing Kummer--Artin
ingredient explicit: the concrete orbit reading vanishes exactly when the
actual selected relation-7A class vanishes. -/
theorem strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero
    (y : RelaxedCarrier827 K)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (readout_injective : Function.Injective readout)
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictTameOrbitFunctional827 K y
        (fermatFactorSelmerDifference59 pair) = 0 ↔
      selectedClassGauge59 pair = 0 := by
  rw [strictTameOrbitFunctional827_eq_zero_iff_classGauge_eq_zero
      K y readout factorization readout_injective,
    fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59 K pair]

/-- The same honest partial closure in Vandiver's original proposition:
under the explicit injective factorization inputs, concrete 827 orbit
silence at the Fermat-factor difference is exactly relation (7a). -/
theorem strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA
    (y : RelaxedCarrier827 K)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (readout_injective : Function.Injective readout)
    (pair : StateLinkedIdealPair hZeta S hz) :
    strictTameOrbitFunctional827 K y
        (fermatFactorSelmerDifference59 pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  rw [strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_selectedClassGauge59_eq_zero
      K y readout factorization readout_injective pair,
    selectedClassGauge59_eq_zero_iff_vandiverSevenA]

end Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59
