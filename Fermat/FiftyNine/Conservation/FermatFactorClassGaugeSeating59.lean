/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The actual Fermat-factor class gauge map

The strict Selmer class map already lands in the genuine 59-torsion ideal
class carrier.  Re-reading that additive map over `ZMod 59` gives a canonical
class-valued gauge on the complete strict Selmer space.  At the literal
plus-minus Fermat-factor difference, its value is exactly Vandiver's
relation-(7a) word.

This removes the formerly arbitrary class-valued gauge seating input.  It
does not construct an Artin readout, compare this gauge with the 827 tame
orbit, or assert relation (7a).
-/
import Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
import Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
import Fermat.FiftyNine.Conservation.UlamReadout827

open scoped MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

namespace Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59

open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.SelmerEigenspace
open CyclotomicSelmerClassNaturality59
open FermatFactorSelmerGauge59
open SplitPrimeFourier827
open StateFactorPair
open UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable {K : Type} [Field K] [NumberField K]

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

/-- The actual strict-Selmer class obstruction, regarded over `ZMod 59`. -/
noncomputable def fermatFactorClassGaugeMap59 :
    SelmerCarrier (NumberField.RingOfIntegers K) K 59 →ₗ[ZMod 59]
      ClassTorsion59 K :=
  (strictSelmerClassLinearMap59 K).toAddMonoidHom.toZModLinearMap 59

@[simp]
theorem fermatFactorClassGaugeMap59_apply
    (x : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    fermatFactorClassGaugeMap59 (K := K) x =
      strictSelmerClassLinearMap59 K x :=
  rfl

/-- The class-valued gauge is onto the complete 59-torsion class carrier. -/
theorem fermatFactorClassGaugeMap59_surjective :
    Function.Surjective (fermatFactorClassGaugeMap59 (K := K)) := by
  exact
    (selmerClassSequenceRealization
      (R := NumberField.RingOfIntegers K) (K := K) (p := 59)).classProjection_surjective

/-- The gauge loses exactly the genuine global-unit classes.  This is the
precise kernel boundary that a future Kummer--Artin readout must respect. -/
theorem fermatFactorClassGaugeMap59_eq_zero_iff_mem_unitRange
    (x : SelmerCarrier (NumberField.RingOfIntegers K) K 59) :
    fermatFactorClassGaugeMap59 (K := K) x = 0 ↔
      x ∈ Set.range (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59)) := by
  let sequence := selmerClassSequenceRealization
    (R := NumberField.RingOfIntegers K) (K := K) (p := 59)
  constructor
  · intro hx
    have hx' : x ∈ {s | sequence.classProjection s = 0} := hx
    rw [← sequence.exact_at_selmer] at hx'
    exact hx'
  · intro hx
    have hx' : x ∈ {s | sequence.classProjection s = 0} := by
      rw [← sequence.exact_at_selmer]
      exact hx
    exact hx'

/-- A scalar Selmer reading factors uniquely through the actual class gauge
exactly when it kills every genuine global-unit class.

This is the algebraic half of the future Kummer--Artin comparison.  For the
827 orbit reading, proving the left side is the remaining arithmetic task;
the Artin readout and its factorization are then forced, not chosen. -/
theorem existsUnique_classReadout_factorization_iff_unit_silence
    (reading :
      SelmerCarrier (NumberField.RingOfIntegers K) K 59 →ₗ[ZMod 59] ZMod 59) :
    (∀ u : UnitModP (NumberField.RingOfIntegers K) 59,
        reading (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0) ↔
      ∃! readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59,
        readout.comp (fermatFactorClassGaugeMap59 (K := K)) = reading := by
  constructor
  · intro hunit
    have hker :
        (fermatFactorClassGaugeMap59 (K := K)).ker ≤ reading.ker := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      obtain ⟨u, rfl⟩ :=
        (fermatFactorClassGaugeMap59_eq_zero_iff_mem_unitRange x).mp hx
      exact hunit u
    obtain ⟨readout, hreadout⟩ :=
      (Fermat.Conservation.ReadoutLedger.fixed_iff_exists_pullback
        (fermatFactorClassGaugeMap59 (K := K)) reading).mp hker
    refine ⟨readout, hreadout, ?_⟩
    intro other hother
    apply LinearMap.ext
    intro c
    obtain ⟨x, rfl⟩ := fermatFactorClassGaugeMap59_surjective (K := K) c
    have hleft := LinearMap.congr_fun hreadout x
    have hright := LinearMap.congr_fun hother x
    exact hright.trans hleft.symm
  · rintro ⟨readout, hreadout, -⟩ u
    have hgauge :
        fermatFactorClassGaugeMap59 (K := K)
            (unitInclusion
              (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) = 0 :=
      (fermatFactorClassGaugeMap59_eq_zero_iff_mem_unitRange _).mpr ⟨u, rfl⟩
    have hvalue := LinearMap.congr_fun hreadout
      (unitInclusion
        (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u)
    change readout
        (fermatFactorClassGaugeMap59 (K := K)
          (unitInclusion
            (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u)) =
      reading
        (unitInclusion
          (R := NumberField.RingOfIntegers K) (K := K) (p := 59) u) at hvalue
    rw [hgauge, map_zero] at hvalue
    exact hvalue.symm

variable [IsCyclotomicExtension {59} ℚ K]
  [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The genuine Selmer difference seats the genuine class-valued 7A gauge.

No readout is chosen: the whole class-valued obstruction is retained. -/
noncomputable def fermatFactorClassGaugeSeating59
    (pair : StateLinkedIdealPair hZeta S hz) :
    ClassValuedSevenAGaugeSeating
      (SelmerChi := SelmerCarrier (NumberField.RingOfIntegers K) K 59)
      pair (fermatFactorSelmerDifference59 pair) where
  gauge := fermatFactorClassGaugeMap59 (K := K)
  gauge_at_fermat := by
    apply Subtype.ext
    calc
      ↑(fermatFactorClassGaugeMap59 (K := K)
          (fermatFactorSelmerDifference59 pair)) =
          FermatFactorSelmerSource59.strictSelmerIdealClass59
            (K := K) (fermatFactorSelmerDifference59 pair) :=
        strictSelmerClassLinearMap59_value
          (K := K) (q := fermatFactorSelmerDifference59 pair)
      _ = pair.ledger.rootClass 0 + 58 • pair.ledger.rootClass 1 :=
        fermatFactorSelmerDifference59_idealClass pair
      _ = Fermat.Conservation.CommonActionStage.differenceGauge
          (Fermat.Conservation.CommonActionStage.AllocatedClass K)
          (Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.classObstruction
            pair) :=
        (Fermat.FiftyNine.Conservation.CommonActionStage.StateLinkedIdealPair.differenceGauge_reading
          pair).symm
      _ = ↑(selectedClassGauge59 pair) :=
        (selectedClassGauge59_value pair).symm

end Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
