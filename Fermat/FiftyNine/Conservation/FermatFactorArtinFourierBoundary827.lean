/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The concrete Fourier coordinate behind pointwise 7A faithfulness

For a strict Selmer class, every height-one valuation is divisible by `59`.
At a tame place this removes the valuation contribution of the first Kummer
input, so the local symbol is the supported valuation of the relaxed input
times one honest residue character of the strict input.

Against the normalized full `827` profile, summing the 58 genuine tame rows
therefore reads exactly the negative mode-`44` Fourier coefficient of that
residue wave.  In particular, the unique class readout already constructed
from global-unit silence has an explicit value on the selected relation-7A
class.  Pointwise faithfulness is reduced to one concrete Fourier-zero
implication; no injectivity on the full class group is required.

No Artin map, class-group rank claim, Takagi theorem, relation `(7a)`, new
axiom, provider, or certificate is imported or used here.
-/
import Fermat.FiftyNine.Conservation.NormalizedFullOrbitUnitSilence827
import Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.PrimeFourierPairingCompression
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.ArbitraryUnitTameOrbitSilence827
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalGlobalTameLedgerIrregular827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.FermatFactorClassGaugeSeating59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerGauge59
open Fermat.FiftyNine.Conservation.FermatFactorSelmerSource59
open Fermat.FiftyNine.Conservation.PointwiseFaithfulSevenAReadout827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SevenAArtinPartialClosure59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StateFactorPair
open Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827
open Fermat.FiftyNine.Conservation.UlamReadout827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal
    (v : Place K) : v.asIdeal.IsMaximal := v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

/-! ## One tame row of an arbitrary strict Selmer class -/

/-- The representative retained only to expose an explicit residue wave.
Changing it by a `59`th power cannot change any theorem below because all
uses pass back through the descended tame symbol. -/
noncomputable def strictKummerRepresentative59
    (x : StrictCarrier59 K) : Kˣ :=
  (Additive.toMul (strictKummerClass59 K x)).out

/-- The globally-root-oriented residue-character wave of a genuine strict
Selmer class on the complete orbit above `827`. -/
noncomputable def strictOrbitResidueWave827
    (x : StrictCarrier59 K) : GaloisIndex59 → ZMod 59 :=
  fun tau ↦
    let ctx := context K (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)
    ctx.residueCharacter
      (Additive.ofMul
        (ctx.angularComponent (strictKummerRepresentative59 K x)))

/-- The selected representative really represents the strict Kummer class. -/
theorem strictKummerRepresentative59_mk
    (x : StrictCarrier59 K) :
    Additive.ofMul
        (QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range
          (strictKummerRepresentative59 K x)) =
      strictKummerClass59 K x := by
  exact congrArg Additive.ofMul
    (QuotientGroup.out_eq' (Additive.toMul (strictKummerClass59 K x)))

/-- Every valuation of the representative of a strict Selmer class is
divisible by `59`. -/
theorem fiftyNine_dvd_valuation_strictKummerRepresentative59
    (x : StrictCarrier59 K) (v : Place K) :
    (59 : ℤ) ∣
      (v.valuationOfNeZero (strictKummerRepresentative59 K x)).toAdd := by
  have hxlocal :
      v.valuationOfNeZeroMod 59
          (Additive.toMul (strictKummerClass59 K x)) = 1 := by
    exact (Additive.toMul x).2 v (by simp)
  have hmk :
      QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range
          (strictKummerRepresentative59 K x) =
        Additive.toMul (strictKummerClass59 K x) :=
    QuotientGroup.out_eq' _
  have hzero :
      ((v.valuationOfNeZero
          (strictKummerRepresentative59 K x)).toAdd : ZMod 59) = 0 := by
    rw [← valuationOfNeZeroMod_mk_toAdd K v
      (strictKummerRepresentative59 K x), hmk, hxlocal]
    rfl
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 59).mp hzero

/-- If the first tame input has valuation divisible by `59`, its local
symbol is exactly the valuation of the second input times the residue
character of the first input's angular component. -/
theorem context59_value_eq_ord_mul_residueCharacter_of_dvd_ord_left
    {k : Type} [Fintype k] [Field k]
    (ctx : Context 59 K k) (a b : Kˣ)
    (ha : (59 : ℤ) ∣ ctx.ord (Additive.ofMul a)) :
    ctx.value a b =
      (ctx.ord (Additive.ofMul b) : ZMod 59) *
        ctx.residueCharacter
          (Additive.ofMul (ctx.angularComponent a)) := by
  obtain ⟨m, hm⟩ := ha
  rw [Context.value]
  simp only [Context.raw, hm]
  rw [ctx.residueCharacter_mul, ctx.residueCharacter_mul]
  change
    ctx.residueCharacter
        ((59 * m * ctx.ord (Additive.ofMul b)) •
          Additive.ofMul (-1 : kˣ)) +
      ctx.residueCharacter
        (ctx.ord (Additive.ofMul b) •
          Additive.ofMul (ctx.angularComponent a)) +
      ctx.residueCharacter
        ((-(59 * m)) •
          Additive.ofMul (ctx.angularComponent b)) = _
  rw [map_zsmul, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul]
  push_cast
  rw [show (59 : ZMod 59) = 0 by exact ZMod.natCast_self 59]
  ring

/-- The residue character of the angular component depends only on the
Kummer class.  This removes the `Quotient.out` choice from all later
Fermat-specific statements. -/
theorem context59_residueCharacter_angularComponent_eq_of_kummer_mk_eq
    {k : Type} [Fintype k] [Field k]
    (ctx : Context 59 K k) (a a' : Kˣ)
    (hclass :
      QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range a =
        QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range a') :
    ctx.residueCharacter
        (Additive.ofMul (ctx.angularComponent a)) =
      ctx.residueCharacter
        (Additive.ofMul (ctx.angularComponent a')) := by
  obtain ⟨z, ⟨u, rfl⟩, haz⟩ :=
    (QuotientGroup.mk'_eq_mk'
      (powMonoidHom 59 : Kˣ →* Kˣ).range).mp hclass
  change a * u ^ 59 = a' at haz
  have hpower :
      ctx.residueCharacter
          (Additive.ofMul (ctx.angularComponent (u ^ 59))) = 0 := by
    rw [map_pow]
    change ctx.residueCharacter
        (59 • Additive.ofMul (ctx.angularComponent u)) = 0
    rw [map_nsmul, ZModModule.char_nsmul_eq_zero]
  rw [← haz, map_mul, ctx.residueCharacter_mul, hpower, add_zero]

/-- One genuine tame row factors as the strict residue wave times Mathlib's
supported valuation coordinate of the relaxed class. -/
theorem rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation
    (tau : GaloisIndex59) (x : StrictCarrier59 K)
    (y : RelaxedCarrier827 K) :
    rawTameOrbitReading827 K tau x y =
      strictOrbitResidueWave827 K x tau *
        relaxedOrbitValuation827 K tau y := by
  let a := strictKummerRepresentative59 K x
  let b : Kˣ := (Additive.toMul (relaxedKummerClass827 K y)).out
  have ha :
      Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom 59 : Kˣ →* Kˣ).range a) =
        strictKummerClass59 K x :=
    strictKummerRepresentative59_mk K x
  have hb :
      QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range b =
        Additive.toMul (relaxedKummerClass827 K y) :=
    QuotientGroup.out_eq' _
  change (context K
      (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP
      (strictKummerClass59 K x) (relaxedKummerClass827 K y) = _
  rw [← ha]
  have hbAdd :
      Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom 59 : Kˣ →* Kˣ).range b) =
        relaxedKummerClass827 K y :=
    congrArg Additive.ofMul hb
  rw [← hbAdd]
  rw [Context.modP_mk_mk]
  rw [context59_value_eq_ord_mul_residueCharacter_of_dvd_ord_left
    K _ a b
    (fiftyNine_dvd_valuation_strictKummerRepresentative59 K x
      (tameOrbitPlace827 (K := K) tau))]
  rw [relaxedOrbitValuation827_eq_representative K tau y b hb]
  unfold strictOrbitResidueWave827
  rw [context_ord]
  dsimp only [a]
  ring

/-! ## The normalized orbit is one exact Fourier coefficient -/

/-- Against the normalized inverse-reflected profile, the complete genuine
tame functional is exactly the negative mode-`44` Fourier coefficient of
the strict residue wave. -/
theorem strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (x : StrictCarrier59 K) :
    strictTameOrbitFunctional827 K y x =
      -fourierCoefficient (strictOrbitResidueWave827 K x)
        (powerCharacter59 44) := by
  rw [strictTameOrbitFunctional827_apply]
  calc
    (∑ tau : GaloisIndex59, rawTameOrbitReading827 K tau x y) =
        ∑ tau : GaloisIndex59,
          strictOrbitResidueWave827 K x tau *
            relaxedOrbitValuation827 K tau y := by
      apply Finset.sum_congr rfl
      intro tau _
      exact rawTameOrbitReading827_eq_strictResidueWave_mul_relaxedValuation
        K tau x y
    _ = ∑ tau : GaloisIndex59,
          strictOrbitResidueWave827 K x tau *
            characterFunction (powerCharacter59 14) tau := by
      apply Finset.sum_congr rfl
      intro tau _
      rw [hprofile tau]
      change _ *
          characterFunction
            (inverseReflectedResidueCharacter827
              canonicalTeichmullerCharacter59 irregularCharacter59) tau = _
      rw [inverseReflectedResidueCharacter827_canonical_irregular_eq_powerFourteen]
    _ = -fourierCoefficient (strictOrbitResidueWave827 K x)
          (powerCharacter59 44) := by
      rw [← powerCharacter59_fortyFour_inv]
      unfold fourierCoefficient
      rw [show (58 : ZMod 59)⁻¹ = -1 by decide +kernel +revert]
      simp only [neg_mul, one_mul, neg_neg, characterFunction,
        MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      apply Finset.sum_congr rfl
      intro tau _
      ring

/-- The normalized 58-coordinate profile, rather than a chosen global
representative of its fiber, determines the complete strict tame
functional. -/
theorem strictTameOrbitFunctional827_eq_of_normalizedProfile
    (y y' : RelaxedCarrier827 K)
    (hy : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (hy' : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y' =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau) :
    strictTameOrbitFunctional827 K y =
      strictTameOrbitFunctional827 K y' := by
  ext x
  rw [strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y hy x,
    strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y' hy' x]

/-- The resulting class readout is likewise independent of the point chosen
inside the normalized reflected fiber.  Surjectivity of the genuine Selmer
class gauge transports equality of the two strict functionals to equality
on the whole class carrier. -/
theorem classReadout_eq_of_normalizedProfile
    (y y' : RelaxedCarrier827 K)
    (hy : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (hy' : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y' =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (readout readout' : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (hreadout :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (hreadout' :
      readout'.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y') :
    readout = readout' := by
  have hfunctional :
      strictTameOrbitFunctional827 K y =
        strictTameOrbitFunctional827 K y' :=
    strictTameOrbitFunctional827_eq_of_normalizedProfile K y y' hy hy'
  apply LinearMap.ext
  intro c
  obtain ⟨x, rfl⟩ := fermatFactorClassGaugeMap59_surjective (K := K) c
  calc
    readout (fermatFactorClassGaugeMap59 (K := K) x) =
        strictTameOrbitFunctional827 K y x :=
      LinearMap.congr_fun hreadout x
    _ = strictTameOrbitFunctional827 K y' x :=
      LinearMap.congr_fun hfunctional x
    _ = readout' (fermatFactorClassGaugeMap59 (K := K) x) :=
      (LinearMap.congr_fun hreadout' x).symm

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  {zeta : K} {hZeta : IsPrimitiveRoot zeta 59}
  {S : Fermat.FiftyNine.Conservation.FermatState.PrimitiveSecondCaseSolution}
  {hz : (59 : ℤ) ∣ S.z}

/-- The Kummer--Fourier comparison before specializing to any Fermat class.
For every genuine strict Selmer input, the factorizing class readout is the
negative mode-`44` coefficient of its actual residue wave.  This is an
equality of the two maps at every input, not a hypothesis or a statement
assuming relation `(7a)`. -/
theorem classReadout_classGaugeMap59_eq_neg_fourierCoefficient
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (x : StrictCarrier59 K) :
    readout (fermatFactorClassGaugeMap59 (K := K) x) =
      -fourierCoefficient (strictOrbitResidueWave827 K x)
        (powerCharacter59 44) := by
  change (readout.comp (fermatFactorClassGaugeMap59 (K := K))) x = _
  rw [factorization]
  exact
    strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y hprofile x

/-- The factorizing class readout has a completely explicit value on the
selected relation-7A class: the negative mode-`44` coefficient of the actual
Fermat-factor strict residue wave. -/
theorem classReadout_selectedClassGauge59_eq_neg_fourierCoefficient
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (pair : StateLinkedIdealPair hZeta S hz) :
    readout (selectedClassGauge59 pair) =
      -fourierCoefficient
        (strictOrbitResidueWave827 K
          (fermatFactorSelmerDifference59 pair))
        (powerCharacter59 44) := by
  rw [← fermatFactorClassGaugeMap59_fermatFactorSelmerDifference59 K pair]
  exact classReadout_classGaugeMap59_eq_neg_fourierCoefficient
    K y hprofile readout factorization (fermatFactorSelmerDifference59 pair)

/-- Pointwise faithfulness of the constructed readout is equivalent to one
explicit Fourier-zero implication at the Fermat factor.  This is the exact
remaining arithmetic statement, with the abstract Artin readout eliminated
from its conclusion. -/
theorem classReadout_pointwiseFaithful_iff_fourierCoefficient_zero_implies_selectedClassGauge59_eq_zero
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (pair : StateLinkedIdealPair hZeta S hz) :
    (readout (selectedClassGauge59 pair) = 0 →
        selectedClassGauge59 pair = 0) ↔
      (fourierCoefficient
          (strictOrbitResidueWave827 K
            (fermatFactorSelmerDifference59 pair))
          (powerCharacter59 44) = 0 →
        selectedClassGauge59 pair = 0) := by
  rw [classReadout_selectedClassGauge59_eq_neg_fourierCoefficient
    K y hprofile readout factorization pair]
  simp only [neg_eq_zero]

/-- The easy direction of the Kummer--Artin comparison is now
unconditional: if the selected ideal class is zero, then its concrete
mode-`44` residue coefficient is zero.  The proof uses the actual normalized
global carrier and its uniquely factorizing class readout; no carrier or
readout is supplied by the caller. -/
theorem fourierCoefficient_fermatFactor_eq_zero_of_selectedClassGauge59_eq_zero
    (pair : StateLinkedIdealPair hZeta S hz)
    (hclass : selectedClassGauge59 pair = 0) :
    fourierCoefficient
        (strictOrbitResidueWave827 K
          (fermatFactorSelmerDifference59 pair))
        (powerCharacter59 44) = 0 := by
  obtain ⟨y, _heigen, hprofile, _hringUnit, _hunitClass,
      readout, factorization, _unique⟩ :=
    NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827
      (K := K)
  have hvalue :=
    classReadout_selectedClassGauge59_eq_neg_fourierCoefficient
      K y hprofile readout factorization pair
  rw [hclass, map_zero] at hvalue
  exact neg_eq_zero.mp hvalue.symm

/-- Consequently the explicit Fourier coefficient vanishes whenever
Vandiver's relation `(7a)` holds.  Only the converse remains arithmetic. -/
theorem fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA
    (pair : StateLinkedIdealPair hZeta S hz)
    (sevenA : pair.ledger.VandiverSevenA 0 1) :
    fourierCoefficient
        (strictOrbitResidueWave827 K
          (fermatFactorSelmerDifference59 pair))
        (powerCharacter59 44) = 0 := by
  apply
    fourierCoefficient_fermatFactor_eq_zero_of_selectedClassGauge59_eq_zero
      K pair
  exact (selectedClassGauge59_eq_zero_iff_vandiverSevenA pair).2 sevenA

/-- Thus the final pointwise seam can be stated as just the missing
direction of one concrete equivalence. -/
theorem fourierCoefficient_fermatFactor_eq_zero_iff_vandiverSevenA_of_reflects_zero
    (pair : StateLinkedIdealPair hZeta S hz)
    (reflects_zero :
      fourierCoefficient
          (strictOrbitResidueWave827 K
            (fermatFactorSelmerDifference59 pair))
          (powerCharacter59 44) = 0 →
        selectedClassGauge59 pair = 0) :
    fourierCoefficient
        (strictOrbitResidueWave827 K
          (fermatFactorSelmerDifference59 pair))
        (powerCharacter59 44) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  constructor
  · intro hzero
    exact (selectedClassGauge59_eq_zero_iff_vandiverSevenA pair).1
      (reflects_zero hzero)
  · exact fourierCoefficient_fermatFactor_eq_zero_of_vandiverSevenA K pair

/-- W7 with no readout-level faithfulness premise: it is enough to prove
the single explicit mode-`44` Fourier coefficient reflects zero for the
selected Fermat class. -/
theorem strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_fourierCoefficient_faithful
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (factorization :
      readout.comp (fermatFactorClassGaugeMap59 (K := K)) =
        strictTameOrbitFunctional827 K y)
    (pair : StateLinkedIdealPair hZeta S hz)
    (fourier_faithful :
      fourierCoefficient
          (strictOrbitResidueWave827 K
            (fermatFactorSelmerDifference59 pair))
          (powerCharacter59 44) = 0 →
        selectedClassGauge59 pair = 0) :
    strictTameOrbitFunctional827 K y
        (fermatFactorSelmerDifference59 pair) = 0 ↔
      pair.ledger.VandiverSevenA 0 1 := by
  apply
    strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_pointwiseFaithful
      K y readout factorization pair
  exact
    (classReadout_pointwiseFaithful_iff_fourierCoefficient_zero_implies_selectedClassGauge59_eq_zero
      K y hprofile readout factorization pair).2 fourier_faithful

/-- End-to-end existential consumer.  The actual normalized global carrier
and the unique class readout are constructed internally.  The sole remaining
input is the concrete mode-`44` zero-reflection statement displayed above. -/
theorem exists_normalizedFullOrbit_w7_of_fourierCoefficient_faithful
    (pair : StateLinkedIdealPair hZeta S hz)
    (fourier_faithful :
      fourierCoefficient
          (strictOrbitResidueWave827 K
            (fermatFactorSelmerDifference59 pair))
          (powerCharacter59 44) = 0 →
        selectedClassGauge59 pair = 0) :
    ∃ y : RelaxedCarrier827 K,
      (∀ tau : GaloisIndex59,
        relaxedOrbitValuation827 K tau y =
          normalizedFullOrbitEigenprofileCoordinates827
            canonicalTeichmullerCharacter59 irregularCharacter59 tau) ∧
      (strictTameOrbitFunctional827 K y
          (fermatFactorSelmerDifference59 pair) = 0 ↔
        pair.ledger.VandiverSevenA 0 1) := by
  obtain ⟨y, _heigen, hprofile, _hringUnit, _hunitClass,
      readout, factorization, _unique⟩ :=
    NormalizedFullOrbitUnitSilence827.exists_normalizedFullOrbitProfile_unitSilence_classReadout827
      (K := K)
  refine ⟨y, hprofile, ?_⟩
  exact
    strictTameOrbitFunctional827_fermatFactor_eq_zero_iff_vandiverSevenA_of_fourierCoefficient_faithful
      K y hprofile readout factorization pair fourier_faithful

end Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827
