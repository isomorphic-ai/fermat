/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Canonical 827 tame-ledger cancellation in the (59,44) mode

The fixed-root 827 ledger has a nonzero unweighted Fourier total, but that
quantity is a detector coordinate and is not the globally normalized
reciprocity ledger. The global cyclotomic root inserts the orbit weight tau.
In the canonical irregular seat this shifts the reflected mode from 14 to 15
and selects inverse-oriented primal mode 43. The actual first circular unit
has zero coefficient there, checked over all 58 entries by the Lean kernel.

Consequently the canonical ledger is nonzero while its scalar total is zero:
it is a live ledger whose local entries cancel. No global reciprocity theorem
or producer is asserted here; the final implication only consumes an
explicitly supplied reciprocity equation.
-/
import Fermat.Conservation.FiniteOrbitLedgerReciprocity
import Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedger827
import Fermat.FiftyNine.Conservation.CanonicalIrregularMode827

open scoped BigOperators NumberField

noncomputable section
set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827

open Fermat.Conservation
open Fermat.Conservation.FiniteOrbitLedgerReciprocity
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.FourierPairingProjection827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The exact odd Fourier coefficient killed by the global-root coordinate
change.  This is checked on all 58 entries of the actual first generated
circular-unit column. -/
theorem inverseFirstGenerated_powerFortyThree_fourier_eq_zero :
    fourierCoefficient
      (inverseReindex
        (fun sigma ↦ fullGeneratedMatrix827 sigma firstLedgerNode))
      (powerCharacter59 43) = 0 := by
  decide +kernel +revert

/-- The physical inverse-oriented circular-unit reading has zero coefficient
in mode 43. -/
theorem inverseOrientedFullOrbitUnitReading827_powerFortyThree_eq_zero
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] :
    fourierCoefficient
      (inverseOrientedFullOrbitUnitReading827 (K := K))
      (powerCharacter59 43) = 0 := by
  have hvector :
      inverseOrientedFullOrbitUnitReading827 (K := K) =
        inverseReindex
          (fun sigma ↦ fullGeneratedMatrix827 sigma firstLedgerNode) := by
    funext tau
    exact fullOrbitUnitReading827_generatedUnit_eq
      (canonicalZeta59_isPrimitive (K := K)) tau⁻¹ firstLedgerNode
  rw [hvector]
  exact inverseFirstGenerated_powerFortyThree_fourier_eq_zero

/-- Multiplying the reflected localization wave by the global-root
coordinate gives the wave appearing in the canonical ledger total. -/
noncomputable def weightedReflectedLocalizationWave827
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K]
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59) :
    GaloisIndex59 → ZMod 59 :=
  fun tau ↦ (tau : ZMod 59) *
    projectedLocalizationVector827 (rhoQ827 (K := K))
      canonicalTeichmullerCharacter59 irregularCharacter59
      (tameOrbitBasePlace827 (K := K)) lift.source tau

set_option maxRecDepth 100000 in
theorem powerCharacter59_fortyFour_inv :
    (powerCharacter59 44)⁻¹ = powerCharacter59 14 := by
  decide +kernel +revert

set_option maxRecDepth 100000 in
theorem powerCharacter59_fortyThree_inv :
    (powerCharacter59 43)⁻¹ = powerCharacter59 15 := by
  decide +kernel +revert

/-- The coordinate weight shifts the reflected wave from mode 14 to mode 15,
the inverse of mode 43. -/
theorem weightedReflectedLocalizationWave827_isPureCharacter
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K]
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59) :
    IsPureCharacter (powerCharacter59 15)
      (weightedReflectedLocalizationWave827 (K := K) lift) := by
  let reflected := projectedLocalizationVector827 (rhoQ827 (K := K))
    canonicalTeichmullerCharacter59 irregularCharacter59
    (tameOrbitBasePlace827 (K := K)) lift.source
  have hreflected : IsPureCharacter (powerCharacter59 14) reflected := by
    rw [← powerCharacter59_fortyFour_inv,
      ← orientedPrimalMode827_canonical_irregular]
    exact actualReflectedLocalizationWave827_isPureCharacter
      (K := K) canonicalTeichmullerCharacter59 irregularCharacter59 lift
  rcases hreflected with ⟨component, hcomponent⟩
  refine ⟨component, ?_⟩
  funext tau
  change (tau : ZMod 59) * reflected tau =
    (component • characterFunction (powerCharacter59 15)) tau
  rw [hcomponent]
  simp only [Pi.smul_apply, smul_eq_mul, characterFunction,
    powerCharacter59_apply]
  rw [show (14 : ZMod 58).val = 14 by decide,
    show (15 : ZMod 58).val = 15 by decide]
  simp only [Units.val_pow_eq_pow_val]
  ring

/-- The global-root weighted sum of the actual 827 local values vanishes in
the canonical irregular character seat. -/
theorem sum_weighted_actualTameOrbitValue827_canonical_irregular_eq_zero
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K]
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59) :
    (∑ tau : GaloisIndex59, (tau : ZMod 59) *
      actualTameOrbitValue827 (K := K) canonicalTeichmullerCharacter59
        irregularCharacter59 lift tau) = 0 := by
  let raw := inverseOrientedFullOrbitUnitReading827 (K := K)
  let reflected := projectedLocalizationVector827 (rhoQ827 (K := K))
    canonicalTeichmullerCharacter59 irregularCharacter59
    (tameOrbitBasePlace827 (K := K)) lift.source
  let weighted := weightedReflectedLocalizationWave827 (K := K) lift
  have hactual :
      (∑ tau : GaloisIndex59, (tau : ZMod 59) *
        actualTameOrbitValue827 (K := K) canonicalTeichmullerCharacter59
          irregularCharacter59 lift tau) =
        ∑ tau : GaloisIndex59, raw tau * weighted tau := by
    apply Finset.sum_congr rfl
    intro tau _
    rw [actualTameOrbitValue827_eq_raw_product]
    change (tau : ZMod 59) * (raw tau * reflected tau) =
      raw tau * ((tau : ZMod 59) * reflected tau)
    ring
  have hweighted : IsPureCharacter (powerCharacter59 43)⁻¹ weighted := by
    rw [powerCharacter59_fortyThree_inv]
    exact weightedReflectedLocalizationWave827_isPureCharacter lift
  have hprojection :=
    sum_mul_pureInverse_eq_sum_characterComponent_mul
      galoisIndex59_card (powerCharacter59 43) raw weighted hweighted
  rw [hactual]
  rw [hprojection]
  have hzero : fourierCoefficient raw (powerCharacter59 43) = 0 :=
    inverseOrientedFullOrbitUnitReading827_powerFortyThree_eq_zero
      (K := K)
  simp only [characterComponent_apply, hzero, zero_mul,
    Finset.sum_const_zero]

/-- The total of the genuinely global-root-oriented tame ledger is zero.
This is a direct theorem about the explicit 827 symbols; no global
reciprocity law is assumed. -/
theorem canonicalTameLedger827_canonical_irregular_sum_eq_zero
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K]
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59) :
    (canonicalTameLedger827 (K := K) canonicalTeichmullerCharacter59
      irregularCharacter59 lift).sum (fun _ value ↦ value) = 0 := by
  rw [canonicalTameLedger827_sum_eq_weighted_actual]
  exact
    sum_weighted_actualTameOrbitValue827_canonical_irregular_eq_zero lift

/-- The globally normalized ledger is nevertheless nonzero.  Thus its zero
total records genuine cancellation among live local entries, not an empty
ledger. -/
theorem canonicalTameLedger827_canonical_irregular_ne_zero
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K]
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59) :
    canonicalTameLedger827 (K := K) canonicalTeichmullerCharacter59
      irregularCharacter59 lift ≠ 0 := by
  have hexists : ∃ tau : GaloisIndex59,
      actualTameOrbitValue827 (K := K) canonicalTeichmullerCharacter59
        irregularCharacter59 lift tau ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply
      sum_actualTameOrbitValue827_canonical_irregular_ne_zero
        (K := K) lift
    simp only [hzero, Finset.sum_const_zero]
  obtain ⟨tau, htau⟩ := hexists
  have hcanonical :
      canonicalTameOrbitValue827 (K := K) canonicalTeichmullerCharacter59
        irregularCharacter59 lift tau ≠ 0 := by
    rw [canonicalTameOrbitValue827_eq_mul_actual]
    exact mul_ne_zero (Units.ne_zero tau) htau
  exact
    orbitLedger_ne_zero_of_value_ne_zero
      (tameOrbitPlace827 (K := K))
      (canonicalTameOrbitValue827 (K := K)
        canonicalTeichmullerCharacter59 irregularCharacter59 lift)
      (tameOrbitPlace827_injective (K := K)) tau hcanonical

/-- A displayed reciprocity equation for the globally normalized ledger
forces the wild scalar to vanish.  This theorem consumes such an equation;
it does not assert or manufacture a global reciprocity producer. -/
theorem wild_eq_zero_of_canonicalTameLedgerReciprocityEquation827
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K]
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) canonicalTeichmullerCharacter59
        irregularCharacter59)
    (wildReading : ZMod 59)
    (reciprocityEquation : wildReading +
      (canonicalTameLedger827 (K := K) canonicalTeichmullerCharacter59
        irregularCharacter59 lift).sum (fun _ value ↦ value) = 0) :
    wildReading = 0 := by
  exact
    distinguished_eq_zero_of_add_ledger_sum_eq_zero
        (canonicalTameLedger827 (K := K) canonicalTeichmullerCharacter59
          irregularCharacter59 lift) wildReading
        (canonicalTameLedger827_canonical_irregular_sum_eq_zero lift)
        reciprocityEquation

end Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
