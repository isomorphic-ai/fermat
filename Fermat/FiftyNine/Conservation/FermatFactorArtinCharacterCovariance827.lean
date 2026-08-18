/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Character covariance of the concrete W5 Fourier readout

The explicit strict residue wave was originally presented through a chosen
Kummer representative.  This file proves that every one of its coordinates
is nevertheless a genuine linear functional: pair the strict Kummer class
with the inverse of the canonical local uniformizer, whose valuation is one.
The tame-symbol formula then recovers exactly the residue coordinate.

Consequently the complete wave and its mode-44 Fourier coefficient commute
with scalar multiplication.  On a genuine cyclotomic character eigenspace,
the concrete W5 Fourier readout therefore transforms by that character.
The same argument proves that every linear class readout is equivariant on
the image of the genuine chi=15 class projector.

This is the strongest covariance supplied by the present implementation
without constructing Galois transport between the varying residue fields.
No Artin reciprocity, class-group rank, character seating, nonvanishing,
provider, certificate, or new axiom is imported or assumed.
-/
import Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.FermatFactorArtinCharacterCovariance827

open Fermat.Conservation
open Fermat.Conservation.CommonActionStage
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.ArbitraryUnitRawTameCarrierBridge827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.CyclotomicSelmerClassNaturality59
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.StrictTameOrbitClassFactorization827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal
    (v : Place K) : v.asIdeal.IsMaximal :=
  v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

local instance instClassTorsion59ModuleZMod :
    Module (ZMod 59) (ClassTorsion59 K) :=
  AddSubgroup.torsionBy.zmodModule

local instance instClassTorsion59ModulePadicInt :
    Module (PadicInt 59) (ClassTorsion59 K) :=
  Module.compHom (ClassTorsion59 K) PadicInt.toZMod

/-! ## The representative wave is a genuine linear map -/

/-- The inverse canonical uniformizer supplies a quotient-level second
Kummer input of valuation one at the selected orbit place. -/
noncomputable def inverseUniformizerKummerClass827
    (tau : GaloisIndex59) : KummerClass 59 K :=
  Additive.ofMul <| QuotientGroup.mk'
    (powMonoidHom 59 : Kˣ →* Kˣ).range
    (chosenUniformizerUnit K (tameOrbitPlace827 (K := K) tau))⁻¹

/-- One residue-wave coordinate, expressed without a representative choice
as a descended tame-symbol linear functional. -/
noncomputable def strictOrbitResidueCoordinateLinearMap827
    (tau : GaloisIndex59) : StrictCarrier59 K →ₗ[ZMod 59] ZMod 59 :=
  (((context K (tameOrbitPlace827 (K := K) tau)
      (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).modP).flip
      (inverseUniformizerKummerClass827 K tau)).comp
    (strictKummerClass59 K) |>.toZModLinearMap 59

/-- The quotient-level linear coordinate is exactly the explicit residue
coordinate defined using `Quotient.out`. -/
@[simp]
theorem strictOrbitResidueCoordinateLinearMap827_apply
    (tau : GaloisIndex59) (x : StrictCarrier59 K) :
    strictOrbitResidueCoordinateLinearMap827 K tau x =
      strictOrbitResidueWave827 K x tau := by
  let v := tameOrbitPlace827 (K := K) tau
  let ctx := context K v
    (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)
  let a := strictKummerRepresentative59 K x
  let b := (chosenUniformizerUnit K v)⁻¹
  have ha :
      Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom 59 : Kˣ →* Kˣ).range a) =
        strictKummerClass59 K x :=
    strictKummerRepresentative59_mk K x
  have hbOrd : ctx.ord (Additive.ofMul b) = 1 := by
    change (v.valuationOfNeZero b).toAdd = 1
    rw [show b = (chosenUniformizerUnit K v)⁻¹ by rfl, map_inv,
      valuationOfNeZero_chosenUniformizerUnit]
    rfl
  change ctx.modP (strictKummerClass59 K x)
      (Additive.ofMul
        (QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range b)) = _
  rw [← ha, Context.modP_mk_mk]
  rw [context59_value_eq_ord_mul_residueCharacter_of_dvd_ord_left
    K ctx a b
    (fiftyNine_dvd_valuation_strictKummerRepresentative59 K x v)]
  rw [hbOrd, Int.cast_one, one_mul]
  unfold strictOrbitResidueWave827
  rfl

/-- The complete explicit residue wave is a linear function of the actual
strict Selmer class. -/
noncomputable def strictOrbitResidueWaveLinearMap827 :
    StrictCarrier59 K →ₗ[ZMod 59] (GaloisIndex59 → ZMod 59) where
  toFun := strictOrbitResidueWave827 K
  map_add' x y := by
    funext tau
    rw [← strictOrbitResidueCoordinateLinearMap827_apply K,
      map_add, strictOrbitResidueCoordinateLinearMap827_apply,
      strictOrbitResidueCoordinateLinearMap827_apply]
    rfl
  map_smul' c x := by
    funext tau
    rw [← strictOrbitResidueCoordinateLinearMap827_apply K,
      map_smul, strictOrbitResidueCoordinateLinearMap827_apply]
    rfl

@[simp]
theorem strictOrbitResidueWaveLinearMap827_apply
    (x : StrictCarrier59 K) :
    strictOrbitResidueWaveLinearMap827 K x =
      strictOrbitResidueWave827 K x :=
  rfl

private theorem fourierCoefficient_add_wave
    (v w : GaloisIndex59 → ZMod 59)
    (eta : GaloisIndex59 →* (ZMod 59)ˣ) :
    fourierCoefficient (v + w) eta =
      fourierCoefficient v eta + fourierCoefficient w eta := by
  unfold fourierCoefficient
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem fourierCoefficient_smul_wave
    (c : ZMod 59) (v : GaloisIndex59 → ZMod 59)
    (eta : GaloisIndex59 →* (ZMod 59)ˣ) :
    fourierCoefficient (c • v) eta =
      c * fourierCoefficient v eta := by
  change fourierCoefficient (fun sigma ↦ c * v sigma) eta = _
  unfold fourierCoefficient
  conv_lhs =>
    enter [2, 2, sigma]
    rw [show ((eta sigma : ZMod 59))⁻¹ * (c * v sigma) =
      c * (((eta sigma : ZMod 59))⁻¹ * v sigma) by ring]
  rw [← Finset.mul_sum]
  ring

/-- The concrete mode-44 Fourier coefficient is itself a linear functional
on the actual strict Selmer carrier. -/
noncomputable def strictOrbitModeFortyFourLinearMap827 :
    StrictCarrier59 K →ₗ[ZMod 59] ZMod 59 where
  toFun x := fourierCoefficient (strictOrbitResidueWave827 K x)
    (powerCharacter59 44)
  map_add' x y := by
    rw [← strictOrbitResidueWaveLinearMap827_apply K (x + y), map_add,
      fourierCoefficient_add_wave,
      strictOrbitResidueWaveLinearMap827_apply,
      strictOrbitResidueWaveLinearMap827_apply]
  map_smul' c x := by
    rw [← strictOrbitResidueWaveLinearMap827_apply K (c • x), map_smul,
      fourierCoefficient_smul_wave,
      strictOrbitResidueWaveLinearMap827_apply]
    rfl

@[simp]
theorem strictOrbitModeFortyFourLinearMap827_apply
    (x : StrictCarrier59 K) :
    strictOrbitModeFortyFourLinearMap827 K x =
      fourierCoefficient (strictOrbitResidueWave827 K x)
        (powerCharacter59 44) :=
  rfl

/-! ## Character covariance on the genuine cyclotomic eigenspace -/

/-- Every explicit orbit coordinate transforms by the source character when
the strict Selmer class genuinely belongs to that character eigenspace. -/
theorem strictOrbitResidueWave827_cyclotomic_of_mem_characterEigenspace
    (chi : Character (PadicInt 59) GaloisIndex59)
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) chi)
    (sigma tau : GaloisIndex59) :
    strictOrbitResidueWave827 K
        (cyclotomicStrictSelmerRepresentation59 K sigma x) tau =
      PadicInt.toZMod (chi sigma : PadicInt 59) *
        strictOrbitResidueWave827 K x tau := by
  rw [(mem_characterEigenspace_iff
    (cyclotomicStrictSelmerRepresentation59 K) chi x).mp hx sigma]
  rw [padicInt_smul_eq_toZMod_smul]
  rw [← strictOrbitResidueCoordinateLinearMap827_apply K tau,
    map_smul, smul_eq_mul,
    strictOrbitResidueCoordinateLinearMap827_apply]

/-- Hence the concrete W5 mode-44 Fourier reading transforms by the source
character on the same genuine eigenspace. -/
theorem strictOrbitModeFortyFour827_cyclotomic_of_mem_characterEigenspace
    (chi : Character (PadicInt 59) GaloisIndex59)
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) chi)
    (sigma : GaloisIndex59) :
    fourierCoefficient
        (strictOrbitResidueWave827 K
          (cyclotomicStrictSelmerRepresentation59 K sigma x))
        (powerCharacter59 44) =
      PadicInt.toZMod (chi sigma : PadicInt 59) *
        fourierCoefficient (strictOrbitResidueWave827 K x)
          (powerCharacter59 44) := by
  rw [(mem_characterEigenspace_iff
    (cyclotomicStrictSelmerRepresentation59 K) chi x).mp hx sigma]
  rw [padicInt_smul_eq_toZMod_smul]
  change strictOrbitModeFortyFourLinearMap827 K
      (PadicInt.toZMod (chi sigma : PadicInt 59) • x) = _
  rw [map_smul, smul_eq_mul,
    strictOrbitModeFortyFourLinearMap827_apply]

/-- Against the normalized 827 profile, the descended complete tame
functional transforms by the source character on every genuine strict
character eigenspace. -/
theorem strictTameOrbitFunctional827_cyclotomic_of_mem_characterEigenspace
    (chi : Character (PadicInt 59) GaloisIndex59)
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) chi)
    (sigma : GaloisIndex59) :
    strictTameOrbitFunctional827 K y
        (cyclotomicStrictSelmerRepresentation59 K sigma x) =
      PadicInt.toZMod (chi sigma : PadicInt 59) *
        strictTameOrbitFunctional827 K y x := by
  rw [strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y hprofile,
    strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y hprofile,
    strictOrbitModeFortyFour827_cyclotomic_of_mem_characterEigenspace
      K chi x hx sigma]
  ring

/-! ## The descended class readout on the chi=15 projector image -/

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]

/-- The canonical chi=15 projection of any strict Selmer class satisfies the
concrete coordinatewise character law, with no seating premise from the
caller. -/
theorem strictOrbitResidueWave827_cyclotomic_irregularProjection
    (source : StrictCarrier59 K) (sigma tau : GaloisIndex59) :
    strictOrbitResidueWave827 K
        (cyclotomicStrictSelmerRepresentation59 K sigma
          (characterProjectorAt
            (cyclotomicStrictSelmerRepresentation59 K)
            irregularCharacter59 source).1) tau =
      PadicInt.toZMod
          (irregularCharacter59 sigma : PadicInt 59) *
        strictOrbitResidueWave827 K
          (characterProjectorAt
            (cyclotomicStrictSelmerRepresentation59 K)
            irregularCharacter59 source).1 tau := by
  exact
    strictOrbitResidueWave827_cyclotomic_of_mem_characterEigenspace
      K irregularCharacter59 _
      (characterProjectorAt
        (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59 source).property sigma tau

/-- The corresponding canonical mode-44 W5 readout transforms by chi=15. -/
theorem strictOrbitModeFortyFour827_cyclotomic_irregularProjection
    (source : StrictCarrier59 K) (sigma : GaloisIndex59) :
    fourierCoefficient
        (strictOrbitResidueWave827 K
          (cyclotomicStrictSelmerRepresentation59 K sigma
            (characterProjectorAt
              (cyclotomicStrictSelmerRepresentation59 K)
              irregularCharacter59 source).1))
        (powerCharacter59 44) =
      PadicInt.toZMod
          (irregularCharacter59 sigma : PadicInt 59) *
        fourierCoefficient
          (strictOrbitResidueWave827 K
            (characterProjectorAt
              (cyclotomicStrictSelmerRepresentation59 K)
              irregularCharacter59 source).1)
          (powerCharacter59 44) := by
  exact
    strictOrbitModeFortyFour827_cyclotomic_of_mem_characterEigenspace
      K irregularCharacter59 _
      (characterProjectorAt
        (cyclotomicStrictSelmerRepresentation59 K)
        irregularCharacter59 source).property sigma

/-- Against the actual normalized 827 profile, the descended complete tame
functional inherits the same chi=15 covariance on the canonical projected
strict source. -/
theorem strictTameOrbitFunctional827_cyclotomic_irregularProjection
    (y : RelaxedCarrier827 K)
    (hprofile : ∀ tau : GaloisIndex59,
      relaxedOrbitValuation827 K tau y =
        normalizedFullOrbitEigenprofileCoordinates827
          canonicalTeichmullerCharacter59 irregularCharacter59 tau)
    (source : StrictCarrier59 K) (sigma : GaloisIndex59) :
    strictTameOrbitFunctional827 K y
        (cyclotomicStrictSelmerRepresentation59 K sigma
          (characterProjectorAt
            (cyclotomicStrictSelmerRepresentation59 K)
            irregularCharacter59 source).1) =
      PadicInt.toZMod
          (irregularCharacter59 sigma : PadicInt 59) *
        strictTameOrbitFunctional827 K y
          (characterProjectorAt
            (cyclotomicStrictSelmerRepresentation59 K)
            irregularCharacter59 source).1 := by
  rw [strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y hprofile,
    strictTameOrbitFunctional827_eq_neg_fourierCoefficient_powerFortyFour
      K y hprofile,
    strictOrbitModeFortyFour827_cyclotomic_irregularProjection]
  ring

/-- The image of the genuine class projector satisfies the expected
cyclotomic eigenlaw. -/
theorem cyclotomicClassProjector59_eigen
    (sigma : GaloisIndex59) (c : ClassTorsion59 K) :
    cyclotomicClassTorsionRepresentation59 K sigma
        (cyclotomicClassProjector59 K irregularCharacter59 c) =
      (irregularCharacter59 sigma : PadicInt 59) •
        cyclotomicClassProjector59 K irregularCharacter59 c := by
  let rho := cyclotomicClassTorsionRepresentation59 K
  calc
    rho sigma (cyclotomicClassProjector59 K irregularCharacter59 c) =
        rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 sigma)
          (rho.asAlgebraHom (characterIdempotent irregularCharacter59) c) := by
      rw [Representation.asAlgebraHom_of]
      rfl
    _ = rho.asAlgebraHom
          (MonoidAlgebra.of (PadicInt 59) GaloisIndex59 sigma *
            characterIdempotent irregularCharacter59) c := by
      rw [map_mul]
      rfl
    _ = rho.asAlgebraHom
          ((irregularCharacter59 sigma : PadicInt 59) •
            characterIdempotent irregularCharacter59) c := by
      rw [groupElement_mul_characterIdempotent]
    _ = (irregularCharacter59 sigma : PadicInt 59) •
          cyclotomicClassProjector59 K irregularCharacter59 c := by
      rw [map_smul]
      rfl

/-- Any scalar class readout, and therefore in particular the uniquely
factorizing W5 readout, is character-equivariant on the genuine chi=15
projector image.  Factorization is not needed for this stronger statement. -/
theorem classReadout_cyclotomic_on_irregularProjectorImage
    (readout : ClassTorsion59 K →ₗ[ZMod 59] ZMod 59)
    (sigma : GaloisIndex59) (c : ClassTorsion59 K) :
    readout
        (cyclotomicClassTorsionRepresentation59 K sigma
          (cyclotomicClassProjector59 K irregularCharacter59 c)) =
      PadicInt.toZMod (irregularCharacter59 sigma : PadicInt 59) *
        readout (cyclotomicClassProjector59 K irregularCharacter59 c) := by
  rw [cyclotomicClassProjector59_eigen]
  change readout
      (PadicInt.toZMod (irregularCharacter59 sigma : PadicInt 59) •
        cyclotomicClassProjector59 K irregularCharacter59 c) = _
  rw [map_smul, smul_eq_mul]

end Fermat.FiftyNine.Conservation.FermatFactorArtinCharacterCovariance827
