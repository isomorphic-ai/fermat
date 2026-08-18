/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Honest local tame reduction at the explicit places above 827

This module constructs the valuation ring, angular component, and tame-symbol
context at each explicit residue-kernel place over 827. It identifies the
resulting local reading of the first circular unit with the actual residue
orbit and the retained valuation coordinate of a q-relaxed reflected lift.
The canonical place orbit is contragredient, so the final pointwise theorem
uses the inverse-reindexed raw residue wave.
-/
import Fermat.FiftyNine.Conservation.ExplicitResiduePlaceOrbit827
import Fermat.Conservation.TameSymbol

open scoped NumberField

noncomputable section

set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.LocalReduction827

open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.OrbitPlace827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace

local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩
local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} (hZeta : IsPrimitiveRoot zeta 59)

abbrev LocalRing827 (sigma : GaloisIndex59) :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
    (orbitPlace827 hZeta sigma)

noncomputable def localReductionHom827 (sigma : GaloisIndex59) :
    LocalRing827 hZeta sigma →+* ZMod Credit.attestationPrime :=
  IsLocalization.lift
    (M := (orbitPlace827 hZeta sigma).asIdeal.primeCompl)
    (S := LocalRing827 hZeta sigma)
    (g := orbitReductionHom827 hZeta sigma) (fun y ↦ by
      apply isUnit_iff_ne_zero.mpr
      intro hy
      exact y.2 (show y.1 ∈ RingHom.ker (orbitReductionHom827 hZeta sigma) by
        exact RingHom.mem_ker.mpr hy))

theorem localReductionHom827_algebraMap (sigma : GaloisIndex59)
    (x : NumberField.RingOfIntegers K) :
    localReductionHom827 hZeta sigma
        (algebraMap (NumberField.RingOfIntegers K)
          (LocalRing827 hZeta sigma) x) =
      orbitReductionHom827 hZeta sigma x := by
  exact IsLocalization.lift_eq
    (M := (orbitPlace827 hZeta sigma).asIdeal.primeCompl) _ x

noncomputable def chosenUniformizer827 (sigma : GaloisIndex59) : K :=
  Classical.choose ((orbitPlace827 hZeta sigma).valuation_exists_uniformizer K)

theorem chosenUniformizer827_spec (sigma : GaloisIndex59) :
    (orbitPlace827 hZeta sigma).valuation K
        (chosenUniformizer827 hZeta sigma) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec
    ((orbitPlace827 hZeta sigma).valuation_exists_uniformizer K)

theorem chosenUniformizer827_ne_zero (sigma : GaloisIndex59) :
    chosenUniformizer827 hZeta sigma ≠ 0 := by
  exact IsDedekindDomain.HeightOneSpectrum.valuation_uniformizer_ne_zero K
    (orbitPlace827 hZeta sigma)

noncomputable def chosenUniformizerUnit827 (sigma : GaloisIndex59) : Kˣ :=
  Units.mk0 (chosenUniformizer827 hZeta sigma)
    (chosenUniformizer827_ne_zero hZeta sigma)

theorem valuationOfNeZero_chosenUniformizerUnit827
    (sigma : GaloisIndex59) :
    (orbitPlace827 hZeta sigma).valuationOfNeZero
        (chosenUniformizerUnit827 hZeta sigma) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  apply WithZero.coe_injective
  rw [(orbitPlace827 hZeta sigma).valuationOfNeZero_eq]
  exact chosenUniformizer827_spec hZeta sigma

noncomputable def localUnitPart827 (sigma : GaloisIndex59) :
    Kˣ →* (LocalRing827 hZeta sigma).unitGroup where
  toFun a := ⟨a * chosenUniformizerUnit827 hZeta sigma ^
      ((orbitPlace827 hZeta sigma).valuationOfNeZero a).toAdd, by
    change _ ∈
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
        (orbitPlace827 hZeta sigma)).unitGroup
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    rw [Valuation.mem_unitGroup_iff]
    have hvunit :
        (orbitPlace827 hZeta sigma).valuationOfNeZero
            (a * chosenUniformizerUnit827 hZeta sigma ^
              ((orbitPlace827 hZeta sigma).valuationOfNeZero a).toAdd) = 1 := by
      rw [map_mul, map_zpow,
        valuationOfNeZero_chosenUniformizerUnit827 hZeta sigma]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, Int.toAdd_zpow, toAdd_ofAdd, toAdd_one]
      ring
    rw [← (orbitPlace827 hZeta sigma).valuationOfNeZero_eq]
    exact congrArg ((↑) : Multiplicative ℤ → WithZero (Multiplicative ℤ)) hvunit⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    simp only [toAdd_mul]
    rw [zpow_add]
    ac_rfl

noncomputable def angularComponent827 (sigma : GaloisIndex59) :
    Kˣ →* (ZMod Credit.attestationPrime)ˣ :=
  (Units.map (localReductionHom827 hZeta sigma)).comp
    ((LocalRing827 hZeta sigma).unitGroupMulEquiv.toMonoidHom.comp
      (localUnitPart827 hZeta sigma))

theorem angularComponent827_globalUnit (sigma : GaloisIndex59)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    angularComponent827 hZeta sigma
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u) =
      Units.map (orbitReductionHom827 hZeta sigma) u := by
  let embedded : Kˣ :=
    Units.map (algebraMap (NumberField.RingOfIntegers K) K) u
  have hunitPart :
      ((localUnitPart827 hZeta sigma embedded :
          (LocalRing827 hZeta sigma).unitGroup) : Kˣ) = embedded := by
    change embedded * chosenUniformizerUnit827 hZeta sigma ^
        ((orbitPlace827 hZeta sigma).valuationOfNeZero embedded).toAdd = embedded
    simp only [embedded, (orbitPlace827 hZeta sigma).valuation_of_unit_eq,
      toAdd_one, zpow_zero, mul_one]
  have hlocal :
      (LocalRing827 hZeta sigma).unitGroupMulEquiv
          (localUnitPart827 hZeta sigma embedded) =
        Units.map
          (algebraMap (NumberField.RingOfIntegers K)
            (LocalRing827 hZeta sigma)) u := by
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val hunitPart
  apply Units.ext
  change localReductionHom827 hZeta sigma
      (((LocalRing827 hZeta sigma).unitGroupMulEquiv
        (localUnitPart827 hZeta sigma
          (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u)) :
            LocalRing827 hZeta sigma)) =
    orbitReductionHom827 hZeta sigma u
  change localReductionHom827 hZeta sigma
      (((LocalRing827 hZeta sigma).unitGroupMulEquiv
        (localUnitPart827 hZeta sigma embedded) :
          LocalRing827 hZeta sigma)) = _
  rw [hlocal]
  exact localReductionHom827_algebraMap hZeta sigma u

theorem attestationRootUnit_isPrimitive_public :
    IsPrimitiveRoot CapacityCertificate.attestationRootUnit 59 := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  simpa [CapacityCertificate.attestationRootUnit] using
    (IsPrimitiveRoot.iff_orderOf.mpr Credit.attestationRoot_order :
      IsPrimitiveRoot Credit.attestationRoot 59)

noncomputable def tameContext827 (sigma : GaloisIndex59) :
    TameSymbol.Context 59 K (ZMod Credit.attestationPrime) where
  ord := MonoidHom.toAdditive (orbitPlace827 hZeta sigma).valuationOfNeZero
  angularComponent := angularComponent827 hZeta sigma
  residueChar_ne := by
    rw [ZMod.ringChar_zmod_n]
    norm_num [Credit.attestationPrime]
  card_sub_one_dvd := by norm_num [Credit.attestationPrime]
  primitiveRoot := CapacityCertificate.attestationRootUnit
  primitiveRoot_spec := attestationRootUnit_isPrimitive_public

@[simp]
theorem tameContext827_ord (sigma : GaloisIndex59) (a : Kˣ) :
    (tameContext827 (hZeta := hZeta) sigma).ord (Additive.ofMul a) =
      ((orbitPlace827 hZeta sigma).valuationOfNeZero a).toAdd :=
  rfl

theorem tameContext827_angularComponent_globalUnit
    (sigma : GaloisIndex59)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    (tameContext827 (hZeta := hZeta) sigma).angularComponent
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u) =
      Units.map (orbitReductionHom827 hZeta sigma).toMonoidHom u :=
  angularComponent827_globalUnit hZeta sigma u

theorem tameContext827_residueCharacter_eq_residueLog
    (sigma : GaloisIndex59) :
    (tameContext827 (hZeta := hZeta) sigma).residueCharacter =
      CapacityCertificate.residueLog := by
  ext u
  change attestationRootUnit_isPrimitive_public.zmodEquivZPowers.symm
      (Additive.ofMul
        ((tameContext827 (hZeta := hZeta) sigma).rootsEquivZPowers
          ((tameContext827 (hZeta := hZeta) sigma).powerToRoots
            (Additive.toMul u)))) =
    attestationRootUnit_isPrimitive_public.zmodEquivZPowers.symm
      (Additive.ofMul (CapacityCertificate.symbolPower (Additive.toMul u)))
  congr 1
  apply Subtype.ext
  change (Additive.toMul u) ^
      ((Fintype.card (ZMod Credit.attestationPrime) - 1) / 59) =
    (Additive.toMul u) ^ (2 * 7)
  norm_num [Credit.attestationPrime]

local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.Rat.isCMField
    (S := {59}) K ⟨59, rfl, by norm_num⟩

theorem realNorm_firstGeneratedUnit_eq_sq :
    CapacityCertificate.realNorm
        (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
          (NumberField.RingOfIntegers K)ˣ) =
      (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
        (NumberField.RingOfIntegers K)ˣ) ^ 2 := by
  change (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
      (NumberField.RingOfIntegers K)ˣ) *
      NumberField.IsCMField.unitsComplexConj K
        (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
          (NumberField.RingOfIntegers K)ˣ) = _
  rw [(NumberField.IsCMField.unitsComplexConj_eq_self_iff K _).mpr
    (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode).2]
  exact (pow_two _).symm

set_option maxHeartbeats 5000000 in
/-- The primal scalar in the honest tame context is the unprojected actual
827 residue wave. -/
theorem tameContext827_primalResidue_eq_fullOrbitUnitReading
    (sigma : GaloisIndex59) :
    (tameContext827 (hZeta := hZeta) sigma).residueCharacter
        (Additive.ofMul
          ((tameContext827 (hZeta := hZeta) sigma).angularComponent
            (Units.map
              (algebraMap (NumberField.RingOfIntegers K) K)
              (Credit.generatedUnit hZeta
                DetectorWitness827.firstLedgerNode :
                  (NumberField.RingOfIntegers K)ˣ)))) =
      fullOrbitUnitReading827 hZeta
        (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
          (NumberField.RingOfIntegers K)ˣ) sigma := by
  rw [tameContext827_angularComponent_globalUnit,
    tameContext827_residueCharacter_eq_residueLog]
  rw [fullOrbitUnitReading827]
  simp only [MonoidHom.comp_apply]
  rw [realNorm_firstGeneratedUnit_eq_sq]
  simp only [map_pow]
  rw [ofMul_pow, map_nsmul]
  let x : ZMod 59 := CapacityCertificate.residueLog
    (Additive.ofMul
      (Units.map (orbitReductionHom827 hZeta sigma)
        (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
          (NumberField.RingOfIntegers K)ˣ)))
  change x = CapacityCertificate.halfScale (2 • x)
  change x = (2 : ZMod 59)⁻¹ * (2 • x)
  rw [show 2 • x = (2 : ZMod 59) * x by simp [two_mul]]
  rw [← mul_assoc,
    inv_mul_cancel₀ (by decide : (2 : ZMod 59) ≠ 0), one_mul]

/-- In the honest tame context, a global integral unit in the first leg
reduces the tame formula to valuation times its canonical residue
character. -/
theorem tameContext827_value_globalUnit
    (sigma : GaloisIndex59)
    (u : (NumberField.RingOfIntegers K)ˣ) (b : Kˣ) :
    (tameContext827 (hZeta := hZeta) sigma).value
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K) u) b =
      (((orbitPlace827 hZeta sigma).valuationOfNeZero b).toAdd : ZMod 59) *
        (tameContext827 (hZeta := hZeta) sigma).residueCharacter
          (Additive.ofMul
            ((tameContext827 (hZeta := hZeta) sigma).angularComponent
              (Units.map
                (algebraMap (NumberField.RingOfIntegers K) K) u))) := by
  rw [TameSymbol.Context.value, TameSymbol.Context.raw]
  have hu := (orbitPlace827 hZeta sigma).valuation_of_unit_eq (K := K) u
  simp only [tameContext827_ord, hu, toAdd_one,
    zero_mul, one_mul, neg_zero, zpow_zero, mul_one]
  change (tameContext827 (hZeta := hZeta) sigma).residueCharacter
      (((orbitPlace827 hZeta sigma).valuationOfNeZero b).toAdd •
        Additive.ofMul
          ((tameContext827 (hZeta := hZeta) sigma).angularComponent
            (Units.map
              (algebraMap (NumberField.RingOfIntegers K) K) u))) = _
  rw [map_zsmul]
  simp only [zsmul_eq_mul]

/-- The canonical primitive root used by the repository's cyclotomic place
action. -/
abbrev canonicalZeta59 : K := IsCyclotomicExtension.zeta 59 ℚ K

abbrev canonicalZeta59_isPrimitive :
    IsPrimitiveRoot (canonicalZeta59 (K := K)) 59 :=
  IsCyclotomicExtension.zeta_spec 59 ℚ K

/-- The raw circular-unit residue vector reindexed by actual places.  The
inverse is forced by `indexedPlaceOrbitEquiv827_eq_orbitPlace827Subtype_inv`.
-/
noncomputable def inverseOrientedFullOrbitUnitReading827 :
    GaloisIndex59 → ZMod 59 :=
  fun tau ↦
    fullOrbitUnitReading827 (canonicalZeta59_isPrimitive (K := K))
      (Credit.generatedUnit (canonicalZeta59_isPrimitive (K := K))
          DetectorWitness827.firstLedgerNode :
        (NumberField.RingOfIntegers K)ˣ) tau⁻¹

section ReflectedRepresentative

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

abbrev rhoQ827 := cyclotomicQRelaxedSelmerRepresentation827 K

/-- Every supported localization coordinate is literally the corresponding
height-one valuation of the representative retained by the lift. -/
theorem qLocalizationCoordinate827_eq_candidateRepresentative
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (place : Place827 K) :
    qLocalizationCoordinate827 (rhoQ827 (K := K)) omega chi place
        lift.candidate =
      ((place.1.valuationOfNeZero lift.candidateRepresentative).toAdd :
        ZMod 59) := by
  change Multiplicative.toAdd
      (place.1.valuationOfNeZeroMod 59
        (SelmerEigenspace.toKummerQuotientAt lift.candidate)) = _
  rw [show SelmerEigenspace.toKummerQuotientAt lift.candidate =
      (lift.candidateRepresentative :
        Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) from by
    simpa [ReflectedQRelaxedLocalizationLift827.candidate] using
      lift.candidate_represents.symm]
  rfl

/-- At every explicit residue-kernel place, the actual tame symbol of the
first circular unit and the retained q-relaxed representative is exactly
the pointwise product of the raw primal residue and supported valuation. -/
theorem actualTameReadingAtOrbitPlace827_eq_raw_product
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (sigma : GaloisIndex59) :
    (tameContext827 (hZeta := hZeta) sigma).value
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
          (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
            (NumberField.RingOfIntegers K)ˣ))
        lift.candidateRepresentative =
      fullOrbitUnitReading827 hZeta
          (Credit.generatedUnit hZeta DetectorWitness827.firstLedgerNode :
            (NumberField.RingOfIntegers K)ˣ) sigma *
        qLocalizationCoordinate827 (rhoQ827 (K := K)) omega chi
          (orbitPlace827Subtype hZeta sigma) lift.candidate := by
  rw [tameContext827_value_globalUnit,
    tameContext827_primalResidue_eq_fullOrbitUnitReading]
  rw [qLocalizationCoordinate827_eq_candidateRepresentative]
  simp only [orbitPlace827Subtype, mul_comm]

/-- In canonical place-orbit coordinates, the physical local tame reading
is the inverse-reindexed raw residue wave times the projected reflected
localization vector. -/
theorem actualTameReading827_eq_inverseOriented_raw_product
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) :
    (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) tau⁻¹).value
        (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
          (Credit.generatedUnit (canonicalZeta59_isPrimitive (K := K))
              DetectorWitness827.firstLedgerNode :
            (NumberField.RingOfIntegers K)ˣ))
        lift.candidateRepresentative =
      inverseOrientedFullOrbitUnitReading827 (K := K) tau *
        projectedLocalizationVector827 (rhoQ827 (K := K)) omega chi
          (orbitPlace827Subtype
            (canonicalZeta59_isPrimitive (K := K)) 1)
          lift.source tau := by
  rw [actualTameReadingAtOrbitPlace827_eq_raw_product]
  change _ = _ * qLocalizationCoordinate827 (rhoQ827 (K := K)) omega chi
      (indexedPlaceOrbitEquiv827 K
        (orbitPlace827Subtype
          (canonicalZeta59_isPrimitive (K := K)) 1) tau)
      (qRelaxedReflectedProjector827 (rhoQ827 (K := K)) omega chi
        lift.source)
  rw [OrbitPlace827.indexedPlaceOrbitEquiv827_eq_orbitPlace827Subtype_inv]
  rfl

end ReflectedRepresentative

end Fermat.FiftyNine.Conservation.LocalReduction827
