/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The rational 827 lift in the trivial reflected-character mode

This file carries the concrete rational-827 relaxed source through the
existing reflected localization-lift constructor.  Under the explicit
hypothesis

`reflectedCharacter omega chi = 1`,

the generic character projector fixes that source.  The rational unit 827
is then a literal unit at the two-prime detector support, so the projected
finite-S class obstruction is the identity.  Its valuation `-1` at every
place over 827 supplies the required nonzero localization coordinate.

The result is an actual `ReflectedQRelaxedLocalizationLift827`, and the final
theorem proves this lift type is inhabited without accepting a selected
place as input.  Every reflected result in this module retains the displayed
trivial-character hypothesis.  Nothing here constructs an arbitrary
reflected-character source or closes the general-character lift seam.

No arithmetic provider, splitting datum, or new premise is introduced.
-/
import Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827
import Fermat.FiftyNine.Conservation.ReflectedLocalizationLiftCriterion827

open scoped BigOperators MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

universe uK

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- In the trivial reflected-character mode, the genuine character
projector fixes the rational 827 source. -/
theorem attestationPrime_reflectedProjector_eq_source827
    (hreflected : InvolutiveBase.reflectedCharacter omega chi = 1) :
    (qRelaxedReflectedProjector827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
      (attestationPrimeSource827 K)).1 =
        attestationPrimeSource827 K := by
  exact characterProjectorAt_eq_self_of_mem
    (cyclotomicQRelaxedSelmerRepresentation827 K)
    (InvolutiveBase.reflectedCharacter omega chi)
    (attestationPrimeSource827 K)
    (attestationPrimeSource827_mem_reflectedCharacter_of_eq_one
      K omega chi hreflected)

/-- The rational unit 827, now viewed as a literal unit away from the full
two-prime detector support. -/
noncomputable def attestationPrimeDetectorSUnit827 :
    (detectorSupport827 K).unit K :=
  ⟨attestationPrimeFieldUnit827 K, by
    intro v hv
    have hq : v ∉ placesOver827 K := fun hq ↦ hv (Or.inr hq)
    have hzero :=
      attestationPrime_valuation_toAdd_eq_zero_of_not_mem K v hq
    rw [← v.valuationOfNeZero_eq (attestationPrimeFieldUnit827 K),
      ← WithZero.coe_one, WithZero.coe_inj]
    exact hzero⟩

/-- The finite-S lift of the literal rational unit is exactly the projected
rational source in the trivial reflected-character mode. -/
theorem fromSUnitLift_attestationPrimeDetectorSUnit827
    (hreflected : InvolutiveBase.reflectedCharacter omega chi = 1) :
    IsDedekindDomain.selmerGroup.fromSUnitLift
        (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
          (detectorSupport827 K)
        (QuotientGroup.mk (attestationPrimeDetectorSUnit827 (K := K))) =
      projectedCandidateAtDetectorSupport827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
        (attestationPrimeSource827 K) := by
  apply Subtype.ext
  change
    ((attestationPrimeFieldUnit827 K : Kˣ) :
      Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) =
    (Additive.toMul
      (qRelaxedReflectedProjector827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
        (attestationPrimeSource827 K)).1).1
  rw [attestationPrime_reflectedProjector_eq_source827
    omega chi hreflected]
  rfl

/-- The projected rational source has trivial finite-S class obstruction.
The proof is the literal S-unit range receipt, followed by the existing
finite-S kernel theorem. -/
theorem projectedCandidateSClassObstruction827_attestationPrime_eq_one
    (hreflected : InvolutiveBase.reflectedCharacter omega chi = 1) :
    projectedCandidateSClassObstruction827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
        (attestationPrimeSource827 K) = 1 := by
  have hrange :
      projectedCandidateAtDetectorSupport827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
          (attestationPrimeSource827 K) ∈
        (IsDedekindDomain.selmerGroup.fromSUnitLift
          (R := NumberField.RingOfIntegers K) (K := K) (n := 59)
            (detectorSupport827 K)).range :=
    ⟨QuotientGroup.mk (attestationPrimeDetectorSUnit827 (K := K)),
      fromSUnitLift_attestationPrimeDetectorSUnit827
        omega chi hreflected⟩
  rw [← IsDedekindDomain.selmerGroup.toSClass_ker
    (R := NumberField.RingOfIntegers K) (K := K) (n := 59)] at hrange
  exact hrange

/-- The projected rational source has nonzero localization at every place
over 827: vanishing would make 59 divide its integer valuation `-1`. -/
theorem qLocalizationCoordinate827_attestationPrime_ne_zero
    (hreflected : InvolutiveBase.reflectedCharacter omega chi = 1)
    (place : Place827 K) :
    qLocalizationCoordinate827
        (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi place
        (qRelaxedReflectedProjector827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
          (attestationPrimeSource827 K)) ≠ 0 := by
  intro hzero
  change place.1.valuationOfNeZeroMod 59
      (Additive.toMul
        (qRelaxedReflectedProjector827
          (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi
          (attestationPrimeSource827 K)).1).1 = 1 at hzero
  rw [attestationPrime_reflectedProjector_eq_source827
    omega chi hreflected] at hzero
  have hdvd : (59 : ℤ) ∣
      (place.1.valuationOfNeZero
        (attestationPrimeFieldUnit827 K)).toAdd :=
    (valuationOfNeZeroMod_mk_eq_one_iff_dvd place.1
      (attestationPrimeFieldUnit827 K)).mp hzero
  rw [attestationPrime_valuation_toAdd_eq_neg_one K place] at hdvd
  norm_num at hdvd

/-- The actual reflected q-relaxed localization lift supplied by rational
827 in the explicitly trivial reflected-character mode. -/
noncomputable def attestationPrimeReflectedLocalizationLift827
    (hreflected : InvolutiveBase.reflectedCharacter omega chi = 1)
    (place : Place827 K) :
    ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi :=
  ReflectedQRelaxedLocalizationLift827.ofSource_of_sClassObstruction_eq_one
    (attestationPrimeSource827 K) place
    (qLocalizationCoordinate827_attestationPrime_ne_zero
      omega chi hreflected place)
    (projectedCandidateSClassObstruction827_attestationPrime_eq_one
      omega chi hreflected)

/-- There is an actual rational-827 reflected localization lift whenever
the reflected character is trivial.  Existence of a place over 827 follows
from the already-proved cardinality `58` of the complete support. -/
theorem nonempty_attestationPrimeReflectedLocalizationLift827
    (hreflected : InvolutiveBase.reflectedCharacter omega chi = 1) :
    Nonempty (ReflectedQRelaxedLocalizationLift827
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi) := by
  have hplaces : (placesOver827 K).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by
      rw [placesOver827_ncard_eq_fiftyEight K]
      norm_num)
  let place : Place827 K := ⟨hplaces.choose, hplaces.choose_spec⟩
  exact ⟨attestationPrimeReflectedLocalizationLift827
    omega chi hreflected place⟩

end Fermat.FiftyNine.Conservation.TrivialReflectedAttestationPrimeLift827
