/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Honest local tame reduction of arbitrary global units at 827

The existing local-reduction theorem identifies the first generated real
unit with the corrected `fullOrbitUnitReading827`.  An arbitrary global unit
is different: the fixed-root tame context sees its uncorrected residue-log
wave `rawGlobalUnitOrbitWave827` directly.

This file proves that comparison for every global unit, multiplies it by the
literal valuation of an arbitrary second input, and freezes the inverse
orientation between canonical place coordinate `tau` and explicit residue
index `tau⁻¹`.  For the globally rooted canonical context it also records the
necessary extra coordinate factor `tau`.

No unit-class inclusion, class-gauge factorization, or Kummer--Artin
comparison is asserted here.
-/
import Fermat.Exponents.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827
import Fermat.Exponents.FiftyNine.Conservation.CanonicalGlobalTameLedger827

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.ArbitraryUnitOrbitDecomposition827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.OrbitPlace827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal (v : Place K) :
    v.asIdeal.IsMaximal :=
  v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

/-- The raw global-unit residue wave written in canonical place coordinates.
The inverse is forced by the explicit residue-kernel orbit theorem. -/
noncomputable def inverseOrientedRawGlobalUnitOrbitWave827
    (u : (NumberField.RingOfIntegers K)ˣ) :
    GaloisIndex59 → ZMod 59 :=
  fun tau ↦ rawGlobalUnitOrbitWave827 u tau⁻¹

/-- The residue scalar inside the fixed-root tame context is exactly the raw
residue-log wave of an arbitrary global unit.  No CM norm correction occurs
in this local symbol input. -/
theorem tameContext827_primalResidue_eq_rawGlobalUnitOrbitWave827
    (u : (NumberField.RingOfIntegers K)ˣ)
    (sigma : GaloisIndex59) :
    (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) sigma).residueCharacter
        (Additive.ofMul
          ((tameContext827
              (hZeta := canonicalZeta59_isPrimitive (K := K))
              sigma).angularComponent
            (Units.map
              (algebraMap (NumberField.RingOfIntegers K) K) u))) =
      rawGlobalUnitOrbitWave827 u sigma := by
  rw [tameContext827_angularComponent_globalUnit,
    tameContext827_residueCharacter_eq_residueLog]
  rfl

/-- With an arbitrary global unit in the first leg, the honest fixed-root
tame value is the second leg's literal valuation times the unit's raw residue
wave. -/
theorem tameContext827_value_globalUnit_eq_valuation_mul_rawWave
    (u : (NumberField.RingOfIntegers K)ˣ) (b : Kˣ)
    (sigma : GaloisIndex59) :
    (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) sigma).value
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u) b =
      (((orbitPlace827
          (canonicalZeta59_isPrimitive (K := K)) sigma).valuationOfNeZero
            b).toAdd : ZMod 59) *
        rawGlobalUnitOrbitWave827 u sigma := by
  rw [tameContext827_value_globalUnit,
    tameContext827_primalResidue_eq_rawGlobalUnitOrbitWave827]

/-- At canonical place coordinate `tau`, the fixed-root context is indexed by
the inverse residue root.  Its valuation is literally the valuation at
`tameOrbitPlace827 tau`. -/
theorem tameContext827_value_globalUnit_at_tameOrbitPlace827
    (u : (NumberField.RingOfIntegers K)ˣ) (b : Kˣ)
    (tau : GaloisIndex59) :
    (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) tau⁻¹).value
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u) b =
      (((tameOrbitPlace827 (K := K) tau).valuationOfNeZero b).toAdd :
        ZMod 59) * inverseOrientedRawGlobalUnitOrbitWave827 u tau := by
  rw [tameContext827_value_globalUnit_eq_valuation_mul_rawWave]
  unfold inverseOrientedRawGlobalUnitOrbitWave827
  rw [tameOrbitPlace827_eq_orbitPlace_inv (K := K) tau]

private theorem context_value_eq_of_place_eq
    {v w : Place K} (h : v = w)
    (hv : v ∉ DetectorWitness827.placesOver59 K)
    (hw : w ∉ DetectorWitness827.placesOver59 K)
    (a b : Kˣ) :
    (context K v hv).value a b = (context K w hw).value a b := by
  subst w
  rfl

/-- In the globally rooted canonical context at the literal place, the same
valuation--raw-wave product acquires exactly the coordinate factor `tau`.
This is the normalization that must be retained when passing from the
fixed-attestation-root Fourier ledger to global reciprocity. -/
theorem canonicalContext827_value_globalUnit_at_tameOrbitPlace827
    (u : (NumberField.RingOfIntegers K)ˣ) (b : Kˣ)
    (tau : GaloisIndex59) :
    (context K (tameOrbitPlace827 (K := K) tau)
        (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u) b =
      (tau : ZMod 59) *
        ((((tameOrbitPlace827 (K := K) tau).valuationOfNeZero b).toAdd :
          ZMod 59) * inverseOrientedRawGlobalUnitOrbitWave827 u tau) := by
  let a : Kˣ :=
    Units.map (algebraMap (NumberField.RingOfIntegers K) K) u
  have hcompare := tameContext827_value_eq_sigma_mul_context
    (K := K) tau⁻¹ a b
  have hcontext :
      (context K
        (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) tau⁻¹)
        (orbitPlace827_not_mem_placesOver59 (K := K) tau⁻¹)).value a b =
      (context K (tameOrbitPlace827 (K := K) tau)
        (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value a b :=
    context_value_eq_of_place_eq
      (tameOrbitPlace827_eq_orbitPlace_inv (K := K) tau).symm
      (orbitPlace827_not_mem_placesOver59 (K := K) tau⁻¹)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau) a b
  have hcompare' :
      (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) tau⁻¹).value a b =
      (tau : ZMod 59)⁻¹ *
        (context K (tameOrbitPlace827 (K := K) tau)
          (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value a b := by
    calc
      _ = ((tau⁻¹ : GaloisIndex59) : ZMod 59) *
          (context K
            (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) tau⁻¹)
            (orbitPlace827_not_mem_placesOver59 (K := K) tau⁻¹)).value
              a b := hcompare
      _ = ((tau⁻¹ : GaloisIndex59) : ZMod 59) *
          (context K (tameOrbitPlace827 (K := K) tau)
            (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value
              a b := by rw [hcontext]
      _ = _ := by rw [Units.val_inv_eq_inv_val]
  have hfixed :=
    tameContext827_value_globalUnit_at_tameOrbitPlace827 u b tau
  change (context K (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value a b = _
  have hunit : (tau : ZMod 59) * (tau : ZMod 59)⁻¹ = 1 := by
    exact mul_inv_cancel₀ (Units.ne_zero tau)
  calc
    _ = 1 *
        (context K (tameOrbitPlace827 (K := K) tau)
          (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value
            a b := by rw [one_mul]
    _ = ((tau : ZMod 59) * (tau : ZMod 59)⁻¹) *
        (context K (tameOrbitPlace827 (K := K) tau)
          (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value
            a b := by rw [hunit]
    _ = (tau : ZMod 59) *
        ((tau : ZMod 59)⁻¹ *
          (context K (tameOrbitPlace827 (K := K) tau)
            (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value
              a b) := by rw [mul_assoc]
    _ = (tau : ZMod 59) *
        (tameContext827
          (hZeta := canonicalZeta59_isPrimitive (K := K)) tau⁻¹).value
            a b := by rw [hcompare']
    _ = _ := by rw [hfixed]

section RelaxedRepresentative

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- For an actual q-relaxed representative, the valuation in the preceding
theorem is exactly its retained canonical localization coordinate. -/
theorem tameContext827_value_globalUnit_relaxedRepresentative_eq_raw_product
    (u : (NumberField.RingOfIntegers K)ˣ)
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) :
    (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) tau⁻¹).value
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u)
        lift.candidateRepresentative =
      qLocalizationCoordinate827 (LocalReduction827.rhoQ827 (K := K))
          omega chi
          (indexedPlaceOrbitEquiv827 K (tameOrbitBasePlace827 (K := K)) tau)
          lift.candidate *
        rawGlobalUnitOrbitWave827 u tau⁻¹ := by
  rw [tameContext827_value_globalUnit_at_tameOrbitPlace827]
  unfold inverseOrientedRawGlobalUnitOrbitWave827
  rw [qLocalizationCoordinate827_eq_candidateRepresentative]

end RelaxedRepresentative

end Fermat.FiftyNine.Conservation.ArbitraryUnitLocalReduction827
