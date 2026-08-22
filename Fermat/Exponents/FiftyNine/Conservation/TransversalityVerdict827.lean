/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The gated transversality verdict at 827

W1--W3 are structurally complete, but neither of their arithmetic seating
interfaces is inhabited in the current cone.  Consequently this file does
not select an unconditional branch.

It does record the strongest justified activation.  If the W1
action/localization seating law is supplied, Fourier forces the retained
conormal class to vanish and activates the already-compiled class-dual
pullback future.  If the W3 Poitou--Tate incidence is supplied as well, its
conserved dimension lands on the reflected-dual obstruction.  No determinant
value, transverse direction, gauge-48 receipt, relation (7a), endpoint, or
transformer is constructed unconditionally.
-/
import Fermat.Exponents.FiftyNine.Conservation.PointedTateIncidence

open scoped nonZeroDivisors NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.TransversalityVerdict827

open Fermat.Conservation
open Fermat.Conservation.SteeringFiber
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.GaugeSteering827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.PointedTateIncidence

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (rhoQ : QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59)
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
  (selected : Place827 K)

/-- Fourier seating makes the retained W2 conormal coordinate vanish. -/
theorem pointedConormalClass_eq_zero_of_fourierSeating
    (seating : QLocalizationEquivariance827 rhoQ omega chi selected) :
    pointedConormalClass827 rhoQ omega chi selected = 0 :=
  (pointedConormalClass827_eq_zero_iff_fixed _ _ _ _).2
    (fixedAttention_of_fourierSeating rhoQ omega chi selected seating)

/-- The pre-compiled fixed future, activated only behind the missing W1
seating law. -/
noncomputable def fixedPointedClassReadoutOfFourierSeating827
    (seating : QLocalizationEquivariance827 rhoQ omega chi selected) :
    Module.Dual (ZMod 59) (ProjectedClassRange827 rhoQ omega chi) :=
  fixedPointedClassReadout827 rhoQ omega chi selected
    (fixedAttention_of_fourierSeating rhoQ omega chi selected seating)

/-- Primitive theorem of the conditional fixed future: on the nonpointed
silent slice, the pointed coordinate is the pullback of the projected-class
dual readout. -/
theorem fixedPointedReadoutOfFourierSeating_pullback
    (seating : QLocalizationEquivariance827 rhoQ omega chi selected)
    (source : QRelaxedSelmerCarrier827 K)
    (hsilence : tameSilence827 rhoQ omega chi selected source = 0) :
    fixedPointedClassReadoutOfFourierSeating827
        rhoQ omega chi selected seating
        (relaxedClassProjection827 rhoQ omega chi source) =
      pointedCoordinate827 rhoQ omega chi selected source :=
  fixedPointedReadout_pullback rhoQ omega chi selected
    (fixedAttention_of_fourierSeating rhoQ omega chi selected seating)
    source hsilence

/-- The same conditional fixed activation makes the scaled gauge independent
of the chosen silent representative of a projected class. -/
theorem fixedGauge_preimage_independent_of_fourierSeating
    (seating : QLocalizationEquivariance827 rhoQ omega chi selected)
    {x y : QRelaxedSelmerCarrier827 K}
    (hclass : relaxedClassProjection827 rhoQ omega chi x =
      relaxedClassProjection827 rhoQ omega chi y)
    (hx : tameSilence827 rhoQ omega chi selected x = 0)
    (hy : tameSilence827 rhoQ omega chi selected y = 0) :
    gaugeReading827 rhoQ omega chi selected x =
      gaugeReading827 rhoQ omega chi selected y :=
  fixedGauge_preimage_independent rhoQ omega chi selected
    (fixedAttention_of_fourierSeating rhoQ omega chi selected seating)
    hclass hx hy

/-- With both missing arithmetic interfaces supplied, W3 records the same
Fourier verdict as reflected-dual obstruction gain one. -/
theorem reflectedDualObstructionGain_eq_one_of_seating
    (incidence : PointedTateIncidence827 rhoQ omega chi selected)
    (seating : QLocalizationEquivariance827 rhoQ omega chi selected) :
    incidence.toPoitouTateFiveTerm.reflectedDualObstructionGain = 1 :=
  reflectedGain_eq_one_of_fourierSeating
    rhoQ omega chi selected incidence seating

/-- The complete conditional rank allocation: Fourier sends none of the
one-dimensional local gain to primal steering and all of it to reflected-dual
obstruction. -/
theorem fixedGainAllocation_of_seating
    (incidence : PointedTateIncidence827 rhoQ omega chi selected)
    (seating : QLocalizationEquivariance827 rhoQ omega chi selected) :
    incidence.toPoitouTateFiveTerm.primalSteeringGain = 0 ∧
      incidence.toPoitouTateFiveTerm.reflectedDualObstructionGain = 1 := by
  have hr := reflectedDualObstructionGain_eq_one_of_seating
    rhoQ omega chi selected incidence seating
  have hb := incidence.conserved_bit
  omega

/-- The opposite pre-compiled future cannot be activated from Fourier
seating: no transverse direction, hence no gauge-48 receipt, can coexist
with that premise. -/
theorem no_transverseDirection_of_seating
    (seating : QLocalizationEquivariance827 rhoQ omega chi selected) :
    ¬ Nonempty
      (TransverseDirection
        (relaxedClassProjection827 rhoQ omega chi)
        (tameSilence827 rhoQ omega chi selected)
        (pointedCoordinate827 rhoQ omega chi selected)) :=
  no_transverseDirection_of_fourierSeating
    rhoQ omega chi selected seating

end Fermat.FiftyNine.Conservation.TransversalityVerdict827
