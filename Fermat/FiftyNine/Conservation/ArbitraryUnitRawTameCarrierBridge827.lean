/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Arbitrary global units in the genuine 827 tame carrier

This module follows an actual ring unit through Mathlib's empty-support
Selmer inclusion, the repository's strict Kummer-class forgetful map, and
the canonical local tame pairing at every place above 827.  The right input
remains an arbitrary element of the genuine 827-relaxed Selmer carrier; its
local coordinate is Mathlib's supported valuation, not supplied data.

The explicit residue-root index is contragredient to the canonical place
index.  The final context adapter therefore uses `tau⁻¹`, while changing
from the fixed attestation root to the reduction of the global cyclotomic
root contributes the visible factor `tau`.
-/
import Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827
import Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.OrbitPlace827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.Conservation.SelmerEigenspace

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) : v.asIdeal.IsMaximal :=
  v.isMaximal

local instance residueField
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) :
    Fintype (Residue K v) :=
  Fintype.ofFinite _

noncomputable def ringUnitClass59
    (u : (NumberField.RingOfIntegers K)ˣ) :
    UnitModP (NumberField.RingOfIntegers K) 59 :=
  Additive.ofMul <| QuotientGroup.mk'
    (powMonoidHom 59 :
      (NumberField.RingOfIntegers K)ˣ →*
        (NumberField.RingOfIntegers K)ˣ).range u

omit [IsCyclotomicExtension {59} ℚ K] in
theorem strictKummerClass59_unitInclusion_ringUnitClass59
    (u : (NumberField.RingOfIntegers K)ˣ) :
    strictKummerClass59 K
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (ringUnitClass59 K u)) =
      Additive.ofMul (QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (Units.map
          (algebraMap (NumberField.RingOfIntegers K) K) u)) := by
  rfl

noncomputable def orbitSupportPlace827
    (tau : GaloisIndex59) :
    {v : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) // v ∈ placesOver827 K} :=
  ⟨tameOrbitPlace827 (K := K) tau, by
    rw [← tameOrbitPlace827_range_eq_placesOver827 (K := K)]
    exact ⟨tau, rfl⟩⟩

def relaxedOrbitValuation827 (tau : GaloisIndex59) :
    RelaxedCarrier827 K →+ ZMod 59 :=
  supportValuationAt (orbitSupportPlace827 K tau)

omit [IsCyclotomicExtension {59} ℚ K] in
theorem valuationOfNeZeroMod_mk_toAdd
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K)) (b : Kˣ) :
    Multiplicative.toAdd
        (v.valuationOfNeZeroMod 59
          (QuotientGroup.mk'
            (powMonoidHom 59 : Kˣ →* Kˣ).range b)) =
      ((v.valuationOfNeZero b).toAdd : ZMod 59) := by
  erw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod,
    MonoidHom.comp_apply, QuotientGroup.map_mk']
  rfl

theorem relaxedOrbitValuation827_eq_representative
    (tau : GaloisIndex59) (y : RelaxedCarrier827 K) (b : Kˣ)
    (hb : QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range b =
      Additive.toMul (relaxedKummerClass827 K y)) :
    relaxedOrbitValuation827 K tau y =
      (((tameOrbitPlace827 (K := K) tau).valuationOfNeZero b).toAdd :
        ZMod 59) := by
  change Multiplicative.toAdd
      ((tameOrbitPlace827 (K := K) tau).valuationOfNeZeroMod 59
        (Additive.toMul (relaxedKummerClass827 K y))) = _
  rw [← hb]
  exact valuationOfNeZeroMod_mk_toAdd K _ b

theorem rawTameOrbitReading827_unitInclusion_eq_context_value
    (tau : GaloisIndex59)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (y : RelaxedCarrier827 K) (b : Kˣ)
    (hb : QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range b =
      Additive.toMul (relaxedKummerClass827 K y)) :
    rawTameOrbitReading827 K tau
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (ringUnitClass59 K u)) y =
      (context K
        (tameOrbitPlace827 (K := K) tau)
        (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value
        (Units.map
          (algebraMap (NumberField.RingOfIntegers K) K) u) b := by
  change (context K
      (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
      (strictKummerClass59 K
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (ringUnitClass59 K u)))
      (relaxedKummerClass827 K y) = _
  rw [strictKummerClass59_unitInclusion_ringUnitClass59]
  have hbAdd : Additive.ofMul (QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range b) =
      relaxedKummerClass827 K y := congrArg Additive.ofMul hb
  rw [← hbAdd]
  exact (context K
    (tameOrbitPlace827 (K := K) tau)
    (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP_mk_mk _ _

/-- The raw residue wave in the coordinate used by the globally rooted
canonical tame context.  It combines the forced inverse place orientation
with the visible global-root coordinate factor `tau`. -/
noncomputable def globallyOrientedRawGlobalUnitOrbitWave827
    (u : (NumberField.RingOfIntegers K)ˣ) :
    GaloisIndex59 → ZMod 59 :=
  fun tau ↦ (tau : ZMod 59) *
    inverseOrientedRawGlobalUnitOrbitWave827 u tau

/-- End-to-end carrier/context bridge.  An actual ring unit enters through
Mathlib's empty-support Selmer inclusion; an arbitrary genuine 827-relaxed
class remains in the right leg.  The canonical tame row is exactly the
globally oriented inverse residue wave times Mathlib's supported valuation
coordinate of that relaxed class. -/
theorem rawTameOrbitReading827_unitInclusion_eq_orientedRaw_mul_relaxedValuation
    (tau : GaloisIndex59)
    (u : (NumberField.RingOfIntegers K)ˣ)
    (y : RelaxedCarrier827 K) :
    rawTameOrbitReading827 K tau
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
          (ringUnitClass59 K u)) y =
      globallyOrientedRawGlobalUnitOrbitWave827 K u tau *
        relaxedOrbitValuation827 K tau y := by
  let b : Kˣ := (Additive.toMul (relaxedKummerClass827 K y)).out
  have hb : QuotientGroup.mk'
      (powMonoidHom 59 : Kˣ →* Kˣ).range b =
        Additive.toMul (relaxedKummerClass827 K y) :=
    QuotientGroup.out_eq' _
  rw [rawTameOrbitReading827_unitInclusion_eq_context_value K tau u y b hb]
  rw [canonicalContext827_value_globalUnit_at_tameOrbitPlace827 u b tau]
  rw [relaxedOrbitValuation827_eq_representative K tau y b hb]
  unfold globallyOrientedRawGlobalUnitOrbitWave827
  ring

end Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
