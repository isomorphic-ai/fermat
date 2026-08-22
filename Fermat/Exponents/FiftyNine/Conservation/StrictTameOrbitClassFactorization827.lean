/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The complete 827 orbit as a strict-Selmer scalar functional

Fixing one genuine class in the carrier relaxed at every place above 827
turns the raw bilinear tame construction into a scalar linear functional on
the complete strict 59-Selmer carrier.  The functional is the literal sum of
all 58 globally-root-oriented tame rows; no selected place, Fourier
compression, Artin map, or class readout is supplied.

The strict Selmer class gauge has exactly the global-unit classes as its
kernel and is surjective.  Consequently, this concrete orbit functional
factors through that genuine class gauge by a unique class readout exactly
when it vanishes on every genuine global-unit class.  The equivalence below
specializes the generic algebraic result already proved for the class gauge;
unit silence remains the visible arithmetic obligation.
-/
import Fermat.Exponents.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorClassGaugeSeating59

open scoped BigOperators MonoidAlgebra NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827

open Fermat.Conservation.CommonActionStage
open CanonicalFullOrbitLocalPairing827
open CyclotomicSelmerClassNaturality59
open FermatFactorClassGaugeSeating59
open SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

/-- The complete globally-root-oriented 827 tame-orbit functional on the
strict Selmer carrier, obtained by fixing the relaxed input of the genuine
raw tame pairing and summing all 58 orbit rows. -/
noncomputable def strictTameOrbitFunctional827
    (y : RelaxedCarrier827 K) :
    StrictCarrier59 K →ₗ[ZMod 59] ZMod 59 :=
  (∑ tau : GaloisIndex59,
      (rawTameOrbitReading827 K tau).flip y).toZModLinearMap 59

/-- Evaluation is the literal finite sum of the 58 genuine raw tame
readings, in their existing global-root orientation. -/
@[simp]
theorem strictTameOrbitFunctional827_apply
    (y : RelaxedCarrier827 K) (x : StrictCarrier59 K) :
    strictTameOrbitFunctional827 K y x =
      ∑ tau : GaloisIndex59, rawTameOrbitReading827 K tau x y := by
  simp [strictTameOrbitFunctional827]

/-- **Exact Kummer--Artin factorization boundary for the concrete 827
orbit.**  The genuine full tame-orbit functional admits a unique scalar
readout of the actual 59-torsion ideal-class gauge if and only if it kills
every genuine global-unit class.

No Artin map or readout is assumed: on the right it is constructed uniquely
from unit silence and the already-proved exact strict Selmer class sequence.
-/
theorem unit_silence_strictTameOrbitFunctional827_iff_existsUnique_classReadout
    (y : RelaxedCarrier827 K) :
    (∀ u : UnitModP (NumberField.RingOfIntegers K) 59,
        strictTameOrbitFunctional827 K y
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0) ↔
      ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
        readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
          strictTameOrbitFunctional827 K y := by
  exact existsUnique_classReadout_factorization_iff_unit_silence
    (K := K) (reading := strictTameOrbitFunctional827 K y)

end Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827
