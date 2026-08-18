/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The primal circular-unit residue wave above 827

The capacity certificate originally evaluates its real circular units at 28
selected residue roots.  This file extends the same construction to every
primitive 59th root in `ZMod 827`, indexed by the full 58-element cyclotomic
Galois index.  At the identity index it recovers the already checked capacity
entry `48`.

The Fourier projector then extracts the reduced reflected-character mode of
this actual circular-unit residue vector.  It is complementary to the inverse
mode occupied by the canonical projected reflected localization, so their
full-orbit pointwise product compresses to the negative of one selected
product.

This module does not yet identify the kernels of the 58 reduction maps with
the `Place827` orbit, nor does it identify the scalar pointwise products with
local Kummer--Tate pairings.  Those are separate arithmetic comparisons.
-/
import Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
import Fermat.FiftyNine.Conservation.CapacityCertificate

open scoped BigOperators NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.PrimalOrbitResidue827

open Polynomial
open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.CapacityCertificate
open Fermat.FiftyNine.Conservation.ComplementaryWaveCompression827
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

/-- The order-59 root corresponding to one of the 58 cyclotomic embeddings
into the 827 residue field. -/
def orbitRoot827 (sigma : GaloisIndex59) : ZMod Credit.attestationPrime :=
  Credit.attestationRoot ^ (sigma : ZMod 59).val

theorem orbitRoot827_isPrimitive (sigma : GaloisIndex59) :
    IsPrimitiveRoot (orbitRoot827 sigma) 59 := by
  exact (IsPrimitiveRoot.iff_orderOf.mpr Credit.attestationRoot_order).pow_of_coprime
    (sigma : ZMod 59).val (ZMod.val_coe_unit_coprime sigma)

universe uK

variable {K : Type uK} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} (hZeta : IsPrimitiveRoot zeta 59)

omit [IsCyclotomicExtension {59} ℚ K] in
private theorem minpoly_toInteger_eq_cyclotomic827 :
    minpoly ℤ hZeta.toInteger = Polynomial.cyclotomic 59 ℤ := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ)
    (RingHom.injective_int (algebraMap ℤ ℚ))
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ K,
    show algebraMap (NumberField.RingOfIntegers K) K hZeta.toInteger = zeta from rfl,
    ← Polynomial.cyclotomic_eq_minpoly_rat hZeta (by norm_num),
    Polynomial.map_cyclotomic]
  exact IsIntegralClosure.isIntegral _ K _

/-- Evaluation at every primitive 59th root in the 827 residue field. -/
noncomputable def orbitReductionHom827 (sigma : GaloisIndex59) :
    NumberField.RingOfIntegers K →+* ZMod Credit.attestationPrime :=
  (hZeta.integralPowerBasis.lift (orbitRoot827 sigma) (by
    rw [hZeta.integralPowerBasis_gen,
      minpoly_toInteger_eq_cyclotomic827 hZeta]
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic, IsRoot.def] using
      (orbitRoot827_isPrimitive sigma).isRoot_cyclotomic
        (by norm_num))).toRingHom

@[simp]
theorem orbitReductionHom827_zeta (sigma : GaloisIndex59) :
    orbitReductionHom827 hZeta sigma hZeta.toInteger = orbitRoot827 sigma := by
  rw [orbitReductionHom827, ← hZeta.integralPowerBasis_gen]
  exact PowerBasis.lift_gen _ _ _

theorem orbitRoot827_one_eq_firstRowRoot :
    orbitRoot827 (1 : GaloisIndex59) =
      CapacityCertificate.rowRoot DetectorWitness827.firstLedgerNode := by
  rw [orbitRoot827, CapacityCertificate.rowRoot]
  have hone : ((1 : GaloisIndex59) : ZMod 59).val = 1 := by
    decide +kernel +revert
  rw [hone]
  rfl

theorem orbitReductionHom827_one_eq_firstReductionHom :
    orbitReductionHom827 hZeta 1 =
      CapacityCertificate.reductionHom hZeta
        DetectorWitness827.firstLedgerNode := by
  apply RingHom.ext
  intro x
  let leftAlg : NumberField.RingOfIntegers K →ₐ[ℤ]
      ZMod Credit.attestationPrime :=
    hZeta.integralPowerBasis.lift (orbitRoot827 1) (by
      rw [hZeta.integralPowerBasis_gen,
        minpoly_toInteger_eq_cyclotomic827 hZeta]
      simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.map_cyclotomic, IsRoot.def] using
        (orbitRoot827_isPrimitive 1).isRoot_cyclotomic (by norm_num))
  let rightAlg : NumberField.RingOfIntegers K →ₐ[ℤ]
      ZMod Credit.attestationPrime :=
    hZeta.integralPowerBasis.lift
      (CapacityCertificate.rowRoot DetectorWitness827.firstLedgerNode) (by
        rw [hZeta.integralPowerBasis_gen]
        rw [show minpoly ℤ hZeta.toInteger =
          Polynomial.cyclotomic 59 ℤ from
            minpoly_toInteger_eq_cyclotomic827 hZeta]
        simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          Polynomial.map_cyclotomic, IsRoot.def] using
          (show IsPrimitiveRoot
              (CapacityCertificate.rowRoot
                DetectorWitness827.firstLedgerNode) 59 from by
            rw [← orbitRoot827_one_eq_firstRowRoot]
            exact orbitRoot827_isPrimitive 1).isRoot_cyclotomic
              (by norm_num))
  have heq : leftAlg = rightAlg := by
    apply hZeta.integralPowerBasis.algHom_ext
    dsimp [leftAlg, rightAlg]
    rw [PowerBasis.lift_gen, PowerBasis.lift_gen]
    exact orbitRoot827_one_eq_firstRowRoot
  have happ := DFunLike.congr_fun heq x
  exact happ

/-- The full 58-embedding residue-character family on actual global units. -/
noncomputable def fullOrbitUnitReading827
    (u : (NumberField.RingOfIntegers K)ˣ) :
    GaloisIndex59 → ZMod 59 :=
  fun sigma ↦
    CapacityCertificate.halfScale
      (CapacityCertificate.residueLog <|
        Additive.ofMul <|
          ((Units.map (orbitReductionHom827 hZeta sigma)).comp
            (CapacityCertificate.realNorm (K := K))) u)

/-- At the identity embedding, the full-orbit construction recovers the
existing checked first capacity entry. -/
theorem fullOrbitUnitReading827_firstGenerated_one :
    fullOrbitUnitReading827 hZeta
        (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
          (NumberField.RingOfIntegers K)ˣ) 1 =
      DetectorWitness827.firstLampReading827 := by
  rw [fullOrbitUnitReading827,
    orbitReductionHom827_one_eq_firstReductionHom hZeta]
  change CapacityCertificate.correctedCharacter hZeta
      DetectorWitness827.firstLedgerNode
        (Additive.ofMul
          (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
            (NumberField.RingOfIntegers K)ˣ)) =
    DetectorWitness827.firstLampReading827
  change CapacityCertificate.residueFunctional hZeta
      DetectorWitness827.firstLedgerNode
        (CapacityCertificate.unitClass
          (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
            (NumberField.RingOfIntegers K)ˣ)) =
    CapacityCertificate.generatedMatrix
      DetectorWitness827.firstLedgerNode DetectorWitness827.firstLedgerNode
  exact CapacityCertificate.residueFunctional_generatedUnit_eq hZeta
    DetectorWitness827.firstLedgerNode DetectorWitness827.firstLedgerNode

/-- Project an actual unit's complete residue vector to one Fourier mode. -/
noncomputable def unitCharacterWave827
    (u : (NumberField.RingOfIntegers K)ˣ)
    (eta : GaloisIndex59 →* (ZMod 59)ˣ) :
    GaloisIndex59 → ZMod 59 :=
  characterComponent (fullOrbitUnitReading827 hZeta u) eta

theorem unitCharacterWave827_isPureCharacter
    (u : (NumberField.RingOfIntegers K)ˣ)
    (eta : GaloisIndex59 →* (ZMod 59)ˣ) :
    IsPureCharacter eta (unitCharacterWave827 hZeta u eta) := by
  exact ⟨fourierCoefficient (fullOrbitUnitReading827 hZeta u) eta, rfl⟩

/-- The projected unit wave obeys its character law on the regular index
group. -/
theorem unitCharacterWave827_mul_apply
    (u : (NumberField.RingOfIntegers K)ˣ)
    (eta : GaloisIndex59 →* (ZMod 59)ˣ)
    (tau sigma : GaloisIndex59) :
    unitCharacterWave827 hZeta u eta (tau * sigma) =
      (eta tau : ZMod 59) * unitCharacterWave827 hZeta u eta sigma := by
  simp only [unitCharacterWave827, characterComponent_apply,
    map_mul, Units.val_mul]
  ring

/-! ## The complementary primal unit mode -/

/-- The reflected-character Fourier component of the actual first generated
circular unit's complete 827 residue vector.  This is the character mode
complementary to the canonically seated reflected localization wave. -/
noncomputable def complementaryPrimalUnitWave827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    GaloisIndex59 → ZMod 59 :=
  unitCharacterWave827 hZeta
    (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
      (NumberField.RingOfIntegers K)ˣ)
    (reducedCharacter59
      (InvolutiveBase.reflectedCharacter omega chi))

theorem complementaryPrimalUnitWave827_isPureCharacter
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    IsPureCharacter
      (reducedCharacter59
        (InvolutiveBase.reflectedCharacter omega chi))
      (complementaryPrimalUnitWave827 hZeta omega chi) :=
  unitCharacterWave827_isPureCharacter hZeta _ _

/-- Full-orbit compression for the actual first circular-unit residue mode
and the actual canonically seated projected reflected localization.  This
still does not identify the pointwise scalar products with local Tate
pairings. -/
theorem complementaryPrimalUnitWave827_product_sum_eq_neg_selected
    [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (selectedPlace : Place827 K)
    (source : QRelaxedSelmerCarrier827 K)
    (selectedIndex : GaloisIndex59) :
    (∑ sigma : GaloisIndex59,
        complementaryPrimalUnitWave827 hZeta omega chi sigma *
          projectedLocalizationVector827
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            omega chi selectedPlace source sigma) =
      -(complementaryPrimalUnitWave827 hZeta omega chi selectedIndex *
          projectedLocalizationVector827
            (cyclotomicQRelaxedSelmerRepresentation827 K)
            omega chi selectedPlace source selectedIndex) :=
  cyclotomic_projectedLocalization_product_sum_eq_neg_selected
    omega chi selectedPlace source
    (complementaryPrimalUnitWave827 hZeta omega chi) selectedIndex
    (complementaryPrimalUnitWave827_isPureCharacter hZeta omega chi)

end Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
