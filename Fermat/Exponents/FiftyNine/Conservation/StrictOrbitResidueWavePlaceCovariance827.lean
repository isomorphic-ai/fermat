/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Place-index covariance of the strict 827 residue wave

This file derives the place permutation of the concrete strict residue wave
from the actual cyclotomic action.  The rational element `827` is used as a
canonical simultaneous uniformizer at all 58 split places: its valuation is
`-1` everywhere on the orbit and every cyclotomic automorphism fixes it.
For a strict Kummer representative its exponent is divisible by `59`, so
this normalization changes neither its Kummer class nor its residue
character.  It removes both `Quotient.out` and the unrelated local choices
of uniformizer before the residue transport is performed.

No Artin reciprocity, source of a nonzero coordinate, provider, certificate,
or new axiom is used.
-/
import Fermat.Experiments.Conservation.GuardDependsOn
import Fermat.Exponents.FiftyNine.Conservation.FermatFactorArtinCharacterCovariance827
import Fermat.Exponents.FiftyNine.Conservation.KummerFrobeniusRead827
import Fermat.Exponents.FiftyNine.Conservation.RationalAttestationPrimeSource827

open scoped BigOperators MonoidAlgebra NumberField nonZeroDivisors

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Fermat.FiftyNine.Conservation.StrictOrbitResidueWavePlaceCovariance827

open Fermat.Conservation
open Fermat.Conservation.InvolutiveBase
open Fermat.Conservation.SelmerEigenspace
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.CanonicalFullOrbitLocalPairing827
open Fermat.FiftyNine.Conservation.CanonicalIrregularMode827
open Fermat.FiftyNine.Conservation.CanonicalTameLedger827
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.FermatFactorArtinCharacterCovariance827
open Fermat.FiftyNine.Conservation.FermatFactorArtinFourierBoundary827
open Fermat.FiftyNine.Conservation.KummerFrobeniusRead827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.OrbitPlace827
open Fermat.FiftyNine.Conservation.PrimalFourierNonvanishing827
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (0 < 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

private abbrev canonicalZeta827 : K :=
  IsCyclotomicExtension.zeta 59 ℚ K

private abbrev canonicalZeta827_isPrimitive :
    IsPrimitiveRoot (canonicalZeta827 K) 59 :=
  IsCyclotomicExtension.zeta_spec 59 ℚ K

/-! ## Localized cyclotomic transport -/

/-- The cyclotomic field action sends the valuation ring at explicit residue
index `sigma * tau` into the valuation ring at index `sigma`. -/
noncomputable def cyclotomicLocalRingHom827
    (sigma tau : GaloisIndex59) :
    LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau) →+*
      LocalRing827 (canonicalZeta827_isPrimitive K) sigma where
  toFun x := ⟨
    KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K tau (x : K),
    by
      change KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K tau
          (x : K) ∈
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
          (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma)
      rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
        Valuation.mem_valuationSubring_iff]
      by_cases hx : (x : K) = 0
      · simp [hx]
      · let ux : Kˣ := Units.mk0 (x : K) hx
        have hcov := valuationOfNeZero_cyclotomic59 K tau
          (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) ux
        have hplace :
            cyclotomicPlaceEquiv59 K tau⁻¹
                (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) =
              orbitPlace827 (canonicalZeta827_isPrimitive K) (sigma * tau) := by
          simpa using cyclotomicPlaceEquiv59_orbitPlace
            (K := K) sigma tau⁻¹
        have hxmem :
            (orbitPlace827 (canonicalZeta827_isPrimitive K)
              (sigma * tau)).valuation K (x : K) ≤ 1 := by
          rw [← Valuation.mem_valuationSubring_iff]
          rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
          exact x.property
        rw [show KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K tau
            (x : K) = (cyclotomicUnitEquiv59 K tau ux : K) by rfl]
        rw [← (orbitPlace827
          (canonicalZeta827_isPrimitive K) sigma).valuationOfNeZero_eq]
        rw [hcov, hplace]
        rw [(orbitPlace827 (canonicalZeta827_isPrimitive K)
          (sigma * tau)).valuationOfNeZero_eq]
        exact hxmem⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp

/-- Local reduction after cyclotomic transport is reduction at the translated
explicit residue index.  This is the localization-level extension of
`orbitReductionHom827_comp_cyclotomicRingEquiv`. -/
theorem localReductionHom827_comp_cyclotomicLocalRingHom827
    (sigma tau : GaloisIndex59) :
    (localReductionHom827 (canonicalZeta827_isPrimitive K) sigma).comp
        (cyclotomicLocalRingHom827 K sigma tau) =
      localReductionHom827 (canonicalZeta827_isPrimitive K) (sigma * tau) := by
  apply IsLocalization.ringHom_ext
    (orbitPlace827 (canonicalZeta827_isPrimitive K) (sigma * tau)).asIdeal.primeCompl
  apply RingHom.ext
  intro x
  change localReductionHom827 (canonicalZeta827_isPrimitive K) sigma
      (cyclotomicLocalRingHom827 K sigma tau
        (algebraMap (NumberField.RingOfIntegers K)
          (LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau)) x)) =
    localReductionHom827 (canonicalZeta827_isPrimitive K) (sigma * tau)
      (algebraMap (NumberField.RingOfIntegers K)
        (LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau)) x)
  have hmap :
      cyclotomicLocalRingHom827 K sigma tau
          (algebraMap (NumberField.RingOfIntegers K)
            (LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau)) x) =
        algebraMap (NumberField.RingOfIntegers K)
          (LocalRing827 (canonicalZeta827_isPrimitive K) sigma)
          (KummerCriterion.cyclotomicRingOfIntegersEquiv
            (p := 59) K tau x) := by
    apply Subtype.ext
    exact algebraMap.coe_smul'
      (KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K tau) x K
  rw [hmap, localReductionHom827_algebraMap,
    localReductionHom827_algebraMap]
  exact DFunLike.congr_fun
    (orbitReductionHom827_comp_cyclotomicRingEquiv
      (K := K) sigma tau) x

@[simp]
theorem localReductionHom827_cyclotomicLocalRingHom827_apply
    (sigma tau : GaloisIndex59)
    (x : LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau)) :
    localReductionHom827 (canonicalZeta827_isPrimitive K) sigma
        (cyclotomicLocalRingHom827 K sigma tau x) =
      localReductionHom827 (canonicalZeta827_isPrimitive K) (sigma * tau) x := by
  exact DFunLike.congr_fun
    (localReductionHom827_comp_cyclotomicLocalRingHom827 K sigma tau) x

/-! ## Canonical rational normalization -/

/-- Multiply a field unit by the unique power of rational `827` that makes
its valuation zero at the selected explicit place. -/
def rationallyNormalizedUnit827
    (sigma : GaloisIndex59) (a : Kˣ) : Kˣ :=
  a * attestationPrimeFieldUnit827 K ^
    ((orbitPlace827 (canonicalZeta827_isPrimitive K) sigma).valuationOfNeZero a).toAdd

/-- The rational normalization has valuation zero at its selected place. -/
theorem rationallyNormalizedUnit827_valuation_toAdd
    (sigma : GaloisIndex59) (a : Kˣ) :
    ((orbitPlace827 (canonicalZeta827_isPrimitive K) sigma).valuationOfNeZero
      (rationallyNormalizedUnit827 K sigma a)).toAdd = 0 := by
  unfold rationallyNormalizedUnit827
  rw [map_mul, map_zpow]
  simp only [toAdd_mul, Int.toAdd_zpow]
  have hq := attestationPrime_valuation_toAdd_eq_neg_one K
    (orbitPlace827Subtype (canonicalZeta827_isPrimitive K) sigma)
  change ((orbitPlace827
      (canonicalZeta827_isPrimitive K) sigma).valuationOfNeZero
        (attestationPrimeFieldUnit827 K)).toAdd = -1 at hq
  rw [hq]
  ring

/-- The cyclotomic action commutes exactly with rational normalization; the
translated index is forced by contragredient place transport. -/
theorem cyclotomicUnitEquiv59_rationallyNormalizedUnit827
    (sigma tau : GaloisIndex59) (a : Kˣ) :
    cyclotomicUnitEquiv59 K tau
        (rationallyNormalizedUnit827 K (sigma * tau) a) =
      rationallyNormalizedUnit827 K sigma
        (cyclotomicUnitEquiv59 K tau a) := by
  unfold rationallyNormalizedUnit827
  rw [map_mul, map_zpow]
  have hfix :
      cyclotomicUnitEquiv59 K tau (attestationPrimeFieldUnit827 K) =
        attestationPrimeFieldUnit827 K := by
    apply Units.ext
    change KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K tau
        (Credit.attestationPrime : K) = Credit.attestationPrime
    exact map_natCast
      (KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K tau)
      Credit.attestationPrime
  rw [hfix]
  have hcov := valuationOfNeZero_cyclotomic59 K tau
    (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) a
  have hplace :
      cyclotomicPlaceEquiv59 K tau⁻¹
          (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) =
        orbitPlace827 (canonicalZeta827_isPrimitive K) (sigma * tau) := by
    simpa using cyclotomicPlaceEquiv59_orbitPlace
      (K := K) sigma tau⁻¹
  rw [hplace] at hcov
  rw [hcov]

/-- When the selected valuation is divisible by `59`, rational normalization
does not alter the Kummer class. -/
theorem rationallyNormalizedUnit827_kummer_mk_eq
    (sigma : GaloisIndex59) (a : Kˣ)
    (hdiv : (59 : ℤ) ∣
      ((orbitPlace827 (canonicalZeta827_isPrimitive K) sigma).valuationOfNeZero a).toAdd) :
    QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (rationallyNormalizedUnit827 K sigma a) =
      QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range a := by
  obtain ⟨m, hm⟩ := hdiv
  unfold rationallyNormalizedUnit827
  rw [hm]
  apply (QuotientGroup.mk'_eq_mk'
    (powMonoidHom 59 : Kˣ →* Kˣ).range).mpr
  refine ⟨attestationPrimeFieldUnit827 K ^ (-((59 : ℤ) * m)), ?_, ?_⟩
  · refine ⟨attestationPrimeFieldUnit827 K ^ (-m), ?_⟩
    change (attestationPrimeFieldUnit827 K ^ (-m)) ^ 59 =
      attestationPrimeFieldUnit827 K ^ (-((59 : ℤ) * m))
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  · rw [zpow_neg]
    group

/-- The residue-character coordinate is unchanged by rational
normalization.  This is the quotient-level step that removes the chosen
Kummer representative from the subsequent place transport. -/
theorem context59_residueCharacter_rationallyNormalizedUnit827
    {k : Type} [Fintype k] [Field k]
    (ctx : Context 59 K k) (sigma : GaloisIndex59) (a : Kˣ)
    (hdiv : (59 : ℤ) ∣
      ((orbitPlace827 (canonicalZeta827_isPrimitive K) sigma).valuationOfNeZero a).toAdd) :
    ctx.residueCharacter (Additive.ofMul (ctx.angularComponent a)) =
      ctx.residueCharacter
        (Additive.ofMul
          (ctx.angularComponent (rationallyNormalizedUnit827 K sigma a))) := by
  exact context59_residueCharacter_angularComponent_eq_of_kummer_mk_eq
    K ctx a (rationallyNormalizedUnit827 K sigma a)
      (rationallyNormalizedUnit827_kummer_mk_eq K sigma a hdiv).symm

/-! ## Transport after normalization -/

/-- Once a field unit has valuation zero, its explicit angular component
commutes with cyclotomic transport.  The proof is performed in the actual
localized valuation rings and then reduced by the preceding localization
compatibility theorem. -/
theorem angularComponent827_cyclotomic_of_valuation_zero
    (sigma tau : GaloisIndex59) (a : Kˣ)
    (hzero :
      ((orbitPlace827 (canonicalZeta827_isPrimitive K)
        (sigma * tau)).valuationOfNeZero a).toAdd = 0) :
    angularComponent827 (canonicalZeta827_isPrimitive K) sigma
        (cyclotomicUnitEquiv59 K tau a) =
      angularComponent827 (canonicalZeta827_isPrimitive K) (sigma * tau) a := by
  have hcov := valuationOfNeZero_cyclotomic59 K tau
    (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) a
  have hplace :
      cyclotomicPlaceEquiv59 K tau⁻¹
          (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) =
        orbitPlace827 (canonicalZeta827_isPrimitive K) (sigma * tau) := by
    simpa using cyclotomicPlaceEquiv59_orbitPlace
      (K := K) sigma tau⁻¹
  rw [hplace] at hcov
  have hzeroAction :
      ((orbitPlace827 (canonicalZeta827_isPrimitive K) sigma).valuationOfNeZero
        (cyclotomicUnitEquiv59 K tau a)).toAdd = 0 := by
    rw [hcov, hzero]
  let sourceLocalUnit :=
    (LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau)).unitGroupMulEquiv
      (localUnitPart827 (canonicalZeta827_isPrimitive K) (sigma * tau) a)
  let targetLocalUnit :=
    (LocalRing827 (canonicalZeta827_isPrimitive K) sigma).unitGroupMulEquiv
      (localUnitPart827 (canonicalZeta827_isPrimitive K) sigma
        (cyclotomicUnitEquiv59 K tau a))
  have hsourcePart :
      (localUnitPart827 (canonicalZeta827_isPrimitive K) (sigma * tau) a : Kˣ) = a := by
    apply Units.ext
    simp [localUnitPart827, hzero]
  have htargetPart :
      (localUnitPart827 (canonicalZeta827_isPrimitive K) sigma
        (cyclotomicUnitEquiv59 K tau a) : Kˣ) =
          cyclotomicUnitEquiv59 K tau a := by
    apply Units.ext
    simp [localUnitPart827, hzeroAction]
  have hlocal :
      cyclotomicLocalRingHom827 K sigma tau
          (sourceLocalUnit :
            LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau)) =
        (targetLocalUnit :
          LocalRing827 (canonicalZeta827_isPrimitive K) sigma) := by
    apply Subtype.ext
    dsimp only [sourceLocalUnit, targetLocalUnit]
    change KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K tau
        ((((LocalRing827 (canonicalZeta827_isPrimitive K)
          (sigma * tau)).unitGroupMulEquiv
            (localUnitPart827 (canonicalZeta827_isPrimitive K)
              (sigma * tau) a) :
                LocalRing827 (canonicalZeta827_isPrimitive K)
                  (sigma * tau)) : K)) =
      (((localUnitPart827 (canonicalZeta827_isPrimitive K) sigma
        (cyclotomicUnitEquiv59 K tau a) : Kˣ) : K))
    rw [ValuationSubring.coe_unitGroupMulEquiv_apply]
    rw [hsourcePart, htargetPart]
    rfl
  apply Units.ext
  change localReductionHom827 (canonicalZeta827_isPrimitive K) sigma
      (targetLocalUnit : LocalRing827 (canonicalZeta827_isPrimitive K) sigma) =
    localReductionHom827 (canonicalZeta827_isPrimitive K) (sigma * tau)
      (sourceLocalUnit :
        LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau))
  rw [← hlocal]
  exact localReductionHom827_cyclotomicLocalRingHom827_apply K sigma tau
    (sourceLocalUnit :
      LocalRing827 (canonicalZeta827_isPrimitive K) (sigma * tau))

/-- With the fixed attestation root as coordinate, residue characters are
strictly invariant under the same localized transport. -/
theorem tameContext827_residueCharacter_cyclotomic_of_valuation_zero
    (sigma tau : GaloisIndex59) (a : Kˣ)
    (hzero :
      ((orbitPlace827 (canonicalZeta827_isPrimitive K)
        (sigma * tau)).valuationOfNeZero a).toAdd = 0) :
    (tameContext827
        (hZeta := canonicalZeta827_isPrimitive K) sigma).residueCharacter
        (Additive.ofMul
          ((tameContext827
            (hZeta := canonicalZeta827_isPrimitive K) sigma).angularComponent
              (cyclotomicUnitEquiv59 K tau a))) =
      (tameContext827
        (hZeta := canonicalZeta827_isPrimitive K)
          (sigma * tau)).residueCharacter
        (Additive.ofMul
          ((tameContext827
            (hZeta := canonicalZeta827_isPrimitive K)
              (sigma * tau)).angularComponent a)) := by
  rw [tameContext827_residueCharacter_eq_residueLog,
    tameContext827_residueCharacter_eq_residueLog]
  exact congrArg (fun u : (ZMod Credit.attestationPrime)ˣ ↦
      CapacityCertificate.residueLog (Additive.ofMul u))
    (angularComponent827_cyclotomic_of_valuation_zero
      K sigma tau a hzero)

/-! ## The quotient-independent fixed-root wave -/

/-- The strict residue wave in the explicit residue-kernel indexing, using
the same fixed primitive root at every coordinate. -/
noncomputable def strictFixedRootResidueWave827
    (x : StrictCarrier59 K) : GaloisIndex59 → ZMod 59 :=
  fun sigma ↦
    (tameContext827
      (hZeta := canonicalZeta827_isPrimitive K) sigma).residueCharacter
      (Additive.ofMul
        ((tameContext827
          (hZeta := canonicalZeta827_isPrimitive K) sigma).angularComponent
            (strictKummerRepresentative59 K x)))

/-- A representative of a cyclotomic translate and the translate of the
selected representative define the same Kummer class. -/
theorem strictKummerRepresentative59_cyclotomic_mk_eq
    (x : StrictCarrier59 K) (tau : GaloisIndex59) :
    QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (strictKummerRepresentative59 K
          (cyclotomicStrictSelmerRepresentation59 K tau x)) =
      QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (cyclotomicUnitEquiv59 K tau
          (strictKummerRepresentative59 K x)) := by
  calc
    _ = Additive.toMul
        (strictKummerClass59 K
          (cyclotomicStrictSelmerRepresentation59 K tau x)) := by
      exact congrArg Additive.toMul
        (strictKummerRepresentative59_mk K
          (cyclotomicStrictSelmerRepresentation59 K tau x))
    _ = cyclotomicKummerHom59 K tau
        (Additive.toMul (strictKummerClass59 K x)) := rfl
    _ = cyclotomicKummerHom59 K tau
        (QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range
          (strictKummerRepresentative59 K x)) := by
      exact congrArg (cyclotomicKummerHom59 K tau)
        (congrArg Additive.toMul
          (strictKummerRepresentative59_mk K x)).symm
    _ = _ := cyclotomicKummerHom59_mk K tau
      (strictKummerRepresentative59 K x)

/-- In fixed-root explicit residue coordinates, cyclotomic action on the
strict Kummer class is exactly right translation of the place index. -/
theorem strictFixedRootResidueWave827_cyclotomic
    (x : StrictCarrier59 K) (sigma tau : GaloisIndex59) :
    strictFixedRootResidueWave827 K
        (cyclotomicStrictSelmerRepresentation59 K tau x) sigma =
      strictFixedRootResidueWave827 K x (sigma * tau) := by
  let a := strictKummerRepresentative59 K x
  let actedA := cyclotomicUnitEquiv59 K tau a
  let normalizedA := rationallyNormalizedUnit827 K (sigma * tau) a
  let ctxSigma := tameContext827
    (hZeta := canonicalZeta827_isPrimitive K) sigma
  let ctxShift := tameContext827
    (hZeta := canonicalZeta827_isPrimitive K) (sigma * tau)
  have hrep :
      QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range
          (strictKummerRepresentative59 K
            (cyclotomicStrictSelmerRepresentation59 K tau x)) =
        QuotientGroup.mk'
          (powMonoidHom 59 : Kˣ →* Kˣ).range actedA := by
    exact strictKummerRepresentative59_cyclotomic_mk_eq K x tau
  have hdiv : (59 : ℤ) ∣
      ((orbitPlace827 (canonicalZeta827_isPrimitive K)
        (sigma * tau)).valuationOfNeZero a).toAdd := by
    exact fiftyNine_dvd_valuation_strictKummerRepresentative59 K x
      (orbitPlace827 (canonicalZeta827_isPrimitive K) (sigma * tau))
  have hcov := valuationOfNeZero_cyclotomic59 K tau
    (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) a
  have hplace :
      cyclotomicPlaceEquiv59 K tau⁻¹
          (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) =
        orbitPlace827 (canonicalZeta827_isPrimitive K) (sigma * tau) := by
    simpa using cyclotomicPlaceEquiv59_orbitPlace
      (K := K) sigma tau⁻¹
  rw [hplace] at hcov
  have hdivActed : (59 : ℤ) ∣
      ((orbitPlace827 (canonicalZeta827_isPrimitive K) sigma).valuationOfNeZero
        actedA).toAdd := by
    rw [show actedA = cyclotomicUnitEquiv59 K tau a by rfl, hcov]
    exact hdiv
  have hzero :
      ((orbitPlace827 (canonicalZeta827_isPrimitive K)
        (sigma * tau)).valuationOfNeZero normalizedA).toAdd = 0 := by
    exact rationallyNormalizedUnit827_valuation_toAdd K (sigma * tau) a
  unfold strictFixedRootResidueWave827
  calc
    ctxSigma.residueCharacter
        (Additive.ofMul
          (ctxSigma.angularComponent
            (strictKummerRepresentative59 K
              (cyclotomicStrictSelmerRepresentation59 K tau x)))) =
      ctxSigma.residueCharacter
        (Additive.ofMul (ctxSigma.angularComponent actedA)) := by
          exact context59_residueCharacter_angularComponent_eq_of_kummer_mk_eq
            K ctxSigma _ actedA hrep
    _ = ctxSigma.residueCharacter
        (Additive.ofMul
          (ctxSigma.angularComponent
            (rationallyNormalizedUnit827 K sigma actedA))) := by
          exact context59_residueCharacter_rationallyNormalizedUnit827
            K ctxSigma sigma actedA hdivActed
    _ = ctxSigma.residueCharacter
        (Additive.ofMul
          (ctxSigma.angularComponent
            (cyclotomicUnitEquiv59 K tau normalizedA))) := by
          rw [cyclotomicUnitEquiv59_rationallyNormalizedUnit827
            K sigma tau a]
    _ = ctxShift.residueCharacter
        (Additive.ofMul (ctxShift.angularComponent normalizedA)) := by
          exact tameContext827_residueCharacter_cyclotomic_of_valuation_zero
            K sigma tau normalizedA hzero
    _ = ctxShift.residueCharacter
        (Additive.ofMul (ctxShift.angularComponent a)) := by
          exact (context59_residueCharacter_rationallyNormalizedUnit827
            K ctxShift (sigma * tau) a hdiv).symm

/-! ## Return to globally rooted place coordinates -/

/-- The fixed-root coordinate at explicit residue index `sigma` is `sigma`
times the globally rooted coordinate at the inverse place index. -/
theorem strictFixedRootResidueWave827_eq_index_mul_frobeniusWave
    (x : StrictCarrier59 K) (sigma : GaloisIndex59) :
    strictFixedRootResidueWave827 K x sigma =
      (sigma : ZMod 59) *
        strictOrbitFrobeniusExponentWave827 K x sigma⁻¹ := by
  let fixedCtx := tameContext827
    (hZeta := canonicalZeta827_isPrimitive K) sigma
  let globalCtx := canonicalOrbitTameContext827 (K := K) sigma
  let u := globalCtx.angularComponent (strictKummerRepresentative59 K x)
  have hprimitive :
      globalCtx.primitiveRoot = fixedCtx.primitiveRoot ^ (sigma : ZMod 59).val := by
    rfl
  have h := TameSymbol.Context.residueCharacter_primitiveRoot_pow
    fixedCtx globalCtx (sigma : ZMod 59).val hprimitive u
  change fixedCtx.residueCharacter
      (Additive.ofMul
        (fixedCtx.angularComponent (strictKummerRepresentative59 K x))) =
    (sigma : ZMod 59) * globalCtx.residueCharacter
      (Additive.ofMul
        (globalCtx.angularComponent (strictKummerRepresentative59 K x)))
  rw [show fixedCtx.angularComponent (strictKummerRepresentative59 K x) =
      globalCtx.angularComponent (strictKummerRepresentative59 K x) by rfl]
  simpa only [u, ZMod.natCast_zmod_val] using h.symm

/-- Equivalent comparison with the canonical strict residue wave. -/
theorem strictFixedRootResidueWave827_eq_index_mul_residueWave
    (x : StrictCarrier59 K) (sigma : GaloisIndex59) :
    strictFixedRootResidueWave827 K x sigma =
      (sigma : ZMod 59) * strictOrbitResidueWave827 K x sigma⁻¹ := by
  rw [strictFixedRootResidueWave827_eq_index_mul_frobeniusWave,
    strictOrbitFrobeniusExponentWave827_eq_residueWave]

/-- Actual place-index covariance of the canonical globally rooted wave.
The additional factor `tau` is the cyclotomic-root twist; it is precisely
what converts the source character into its reflected character. -/
theorem strictOrbitResidueWave827_cyclotomic_place
    (x : StrictCarrier59 K) (tau position : GaloisIndex59) :
    strictOrbitResidueWave827 K
        (cyclotomicStrictSelmerRepresentation59 K tau x) position =
      (tau : ZMod 59) *
        strictOrbitResidueWave827 K x (tau⁻¹ * position) := by
  have hcov :
      ((position⁻¹ : GaloisIndex59) : ZMod 59) *
          strictOrbitResidueWave827 K
            (cyclotomicStrictSelmerRepresentation59 K tau x) position =
        ((position⁻¹ * tau : GaloisIndex59) : ZMod 59) *
          strictOrbitResidueWave827 K x
            (position⁻¹ * tau)⁻¹ := by
    calc
      _ = strictFixedRootResidueWave827 K
          (cyclotomicStrictSelmerRepresentation59 K tau x) position⁻¹ := by
            simpa only [inv_inv] using
              (strictFixedRootResidueWave827_eq_index_mul_residueWave K
                (cyclotomicStrictSelmerRepresentation59 K tau x)
                position⁻¹).symm
      _ = strictFixedRootResidueWave827 K x (position⁻¹ * tau) :=
        strictFixedRootResidueWave827_cyclotomic K x position⁻¹ tau
      _ = _ := strictFixedRootResidueWave827_eq_index_mul_residueWave
        K x (position⁻¹ * tau)
  have hcancel :
      ((position⁻¹ : GaloisIndex59) : ZMod 59) *
        strictOrbitResidueWave827 K
          (cyclotomicStrictSelmerRepresentation59 K tau x) position =
        ((position⁻¹ : GaloisIndex59) : ZMod 59) *
        ((tau : ZMod 59) *
          strictOrbitResidueWave827 K x (tau⁻¹ * position)) := by
    calc
      _ = ((position⁻¹ * tau : GaloisIndex59) : ZMod 59) *
          strictOrbitResidueWave827 K x
            (position⁻¹ * tau)⁻¹ := hcov
      _ = _ := by
        rw [show (position⁻¹ * tau)⁻¹ = tau⁻¹ * position by group]
        change ((position⁻¹ : GaloisIndex59) : ZMod 59) *
            (tau : ZMod 59) *
              strictOrbitResidueWave827 K x (tau⁻¹ * position) = _
        ring
  exact mul_left_cancel₀ (Units.ne_zero position⁻¹) hcancel

/-! ## Character reflection and pure mode 44 -/

/-- Combining source-eigenspace covariance with actual place transport
reflects the character: the root coordinate contributes one copy of the
Teichmuller character and place translation contributes the inverse source
character. -/
theorem strictOrbitResidueWave827_mul_of_mem_characterEigenspace_raw
    (chi : Character (PadicInt 59) GaloisIndex59)
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) chi)
    (sigma position : GaloisIndex59) :
    strictOrbitResidueWave827 K x (sigma * position) =
      (sigma : ZMod 59) *
        PadicInt.toZMod (chi sigma⁻¹ : PadicInt 59) *
          strictOrbitResidueWave827 K x position := by
  have hsource :=
    strictOrbitResidueWave827_cyclotomic_of_mem_characterEigenspace
      K chi x hx sigma⁻¹ position
  have hplace := strictOrbitResidueWave827_cyclotomic_place
    K x sigma⁻¹ position
  have heq :
      PadicInt.toZMod (chi sigma⁻¹ : PadicInt 59) *
          strictOrbitResidueWave827 K x position =
        ((sigma⁻¹ : GaloisIndex59) : ZMod 59) *
          strictOrbitResidueWave827 K x (sigma * position) := by
    calc
      _ = strictOrbitResidueWave827 K
          (cyclotomicStrictSelmerRepresentation59 K sigma⁻¹ x)
            position := hsource.symm
      _ = _ := by simpa only [inv_inv] using hplace
  have hunit :
      (sigma : ZMod 59) * ((sigma⁻¹ : GaloisIndex59) : ZMod 59) = 1 := by
    exact congrArg Units.val (mul_inv_cancel sigma)
  calc
    strictOrbitResidueWave827 K x (sigma * position) =
        1 * strictOrbitResidueWave827 K x (sigma * position) := by rw [one_mul]
    _ = ((sigma : ZMod 59) * ((sigma⁻¹ : GaloisIndex59) : ZMod 59)) *
        strictOrbitResidueWave827 K x (sigma * position) := by rw [hunit]
    _ = (sigma : ZMod 59) *
        (((sigma⁻¹ : GaloisIndex59) : ZMod 59) *
          strictOrbitResidueWave827 K x (sigma * position)) := by
            rw [mul_assoc]
    _ = (sigma : ZMod 59) *
        (PadicInt.toZMod (chi sigma⁻¹ : PadicInt 59) *
          strictOrbitResidueWave827 K x position) := by rw [← heq]
    _ = _ := by ring

/-- Character-theoretic spelling of the preceding law. -/
theorem strictOrbitResidueWave827_mul_of_mem_characterEigenspace
    (chi : Character (PadicInt 59) GaloisIndex59)
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) chi)
    (sigma position : GaloisIndex59) :
    strictOrbitResidueWave827 K x (sigma * position) =
      ((reducedCharacter59
        (reflectedCharacter canonicalTeichmullerCharacter59 chi) sigma :
          (ZMod 59)ˣ) : ZMod 59) *
        strictOrbitResidueWave827 K x position := by
  rw [strictOrbitResidueWave827_mul_of_mem_characterEigenspace_raw
    K chi x hx sigma position]
  congr 1
  rw [reducedCharacter59_reflectedCharacter]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply,
    Units.val_mul, Units.val_inv_eq_inv_val,
    reducedCharacter59_apply]
  have homega := congrArg Units.val
    (canonicalTeichmullerCharacter59_reduction_apply sigma)
  change PadicInt.toZMod
      (canonicalTeichmullerCharacter59 sigma : PadicInt 59) =
    (sigma : ZMod 59) at homega
  rw [homega]
  change (sigma : ZMod 59) *
      PadicInt.toZMod (chi sigma⁻¹ : PadicInt 59) =
    (sigma : ZMod 59) *
      (PadicInt.toZMod (chi sigma : PadicInt 59))⁻¹
  congr 1
  have hchi := congrArg Units.val
    (map_inv (reducedCharacter59 chi) sigma)
  simpa only [reducedCharacter59_apply,
    Units.val_inv_eq_inv_val] using hchi

/-- In the genuine chi=15 strict eigenspace the complete 827 residue wave is
exactly pure mode 44. -/
theorem strictOrbitResidueWave827_irregular_mul
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59)
    (sigma position : GaloisIndex59) :
    strictOrbitResidueWave827 K x (sigma * position) =
      ((powerCharacter59 44 sigma : (ZMod 59)ˣ) : ZMod 59) *
        strictOrbitResidueWave827 K x position := by
  rw [← orientedPrimalMode827_canonical_irregular]
  exact strictOrbitResidueWave827_mul_of_mem_characterEigenspace
    K irregularCharacter59 x hx sigma position

/-- The whole strict residue wave of a genuine chi=15 class occupies the
single reflected Fourier mode 44. -/
theorem strictOrbitResidueWave827_isPure_powerFortyFour
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59) :
    IsPureCharacter (powerCharacter59 44)
      (strictOrbitResidueWave827 K x) := by
  refine ⟨strictOrbitResidueWave827 K x 1, ?_⟩
  funext sigma
  change strictOrbitResidueWave827 K x sigma =
    strictOrbitResidueWave827 K x 1 *
      ((powerCharacter59 44 sigma : (ZMod 59)ˣ) : ZMod 59)
  have h := strictOrbitResidueWave827_irregular_mul K x hx sigma 1
  rw [mul_one] at h
  rw [h]
  ring

/-- On the chi=15 eigenspace a single nonzero place coordinate forces the
mode-44 Fourier coefficient to be nonzero, because there are no other modes
present. -/
theorem fourierCoefficient_powerFortyFour_ne_zero_of_coordinate_ne_zero
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59)
    (position : GaloisIndex59)
    (hposition : strictOrbitResidueWave827 K x position ≠ 0) :
    fourierCoefficient (strictOrbitResidueWave827 K x)
      (powerCharacter59 44) ≠ 0 := by
  obtain ⟨component, hpure⟩ :=
    strictOrbitResidueWave827_isPure_powerFortyFour K x hx
  have hcomponent : component ≠ 0 := by
    intro hzero
    subst component
    rw [hpure] at hposition
    simp at hposition
  rw [hpure, fourierCoefficient_pureCharacter galoisIndex59_card]
  exact hcomponent

/-- The literal residue-Frobenius exponent wave has the same pure mode. -/
theorem strictOrbitFrobeniusExponentWave827_isPure_powerFortyFour
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59) :
    IsPureCharacter (powerCharacter59 44)
      (strictOrbitFrobeniusExponentWave827 K x) := by
  rw [strictOrbitFrobeniusExponentWave827_eq_residueWave]
  exact strictOrbitResidueWave827_isPure_powerFortyFour K x hx

/-- Frobenius spelling of pointwise faithfulness. -/
theorem frobeniusFourier_powerFortyFour_ne_zero_of_coordinate_ne_zero
    (x : StrictCarrier59 K)
    (hx : x ∈ characterEigenspace
      (cyclotomicStrictSelmerRepresentation59 K) irregularCharacter59)
    (position : GaloisIndex59)
    (hposition : strictOrbitFrobeniusExponentWave827 K x position ≠ 0) :
    fourierCoefficient (strictOrbitFrobeniusExponentWave827 K x)
      (powerCharacter59 44) ≠ 0 := by
  rw [strictOrbitFrobeniusExponentWave827_eq_residueWave] at hposition ⊢
  exact fourierCoefficient_powerFortyFour_ne_zero_of_coordinate_ne_zero
    K x hx position hposition

/-! ## Axiom audit -/

/--
info: 'Fermat.FiftyNine.Conservation.StrictOrbitResidueWavePlaceCovariance827.localReductionHom827_comp_cyclotomicLocalRingHom827' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms localReductionHom827_comp_cyclotomicLocalRingHom827

/--
info: 'Fermat.FiftyNine.Conservation.StrictOrbitResidueWavePlaceCovariance827.strictOrbitResidueWave827_cyclotomic_place' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strictOrbitResidueWave827_cyclotomic_place

/--
info: 'Fermat.FiftyNine.Conservation.StrictOrbitResidueWavePlaceCovariance827.strictOrbitResidueWave827_isPure_powerFortyFour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strictOrbitResidueWave827_isPure_powerFortyFour

/--
info: 'Fermat.FiftyNine.Conservation.StrictOrbitResidueWavePlaceCovariance827.frobeniusFourier_powerFortyFour_ne_zero_of_coordinate_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms frobeniusFourier_powerFortyFour_ne_zero_of_coordinate_ne_zero

/-! The transport proof consumes the literal residue-kernel covariance and
the genuine strict cyclotomic action; the Fourier endpoint consumes the
newly proved pure-mode theorem and ordinary character orthogonality. -/

#guard_depends_on
  localReductionHom827_comp_cyclotomicLocalRingHom827,
  Fermat.FiftyNine.Conservation.OrbitPlace827.orbitReductionHom827_comp_cyclotomicRingEquiv
#guard_depends_on
  rationallyNormalizedUnit827_valuation_toAdd,
  Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827.attestationPrime_valuation_toAdd_eq_neg_one
#guard_depends_on
  strictOrbitResidueWave827_cyclotomic_place,
  localReductionHom827_comp_cyclotomicLocalRingHom827
#guard_depends_on
  strictOrbitResidueWave827_isPure_powerFortyFour,
  strictOrbitResidueWave827_cyclotomic_place
#guard_depends_on
  strictOrbitResidueWave827_isPure_powerFortyFour,
  Fermat.FiftyNine.Conservation.FermatFactorArtinCharacterCovariance827.strictOrbitResidueWave827_cyclotomic_of_mem_characterEigenspace
#guard_depends_on
  fourierCoefficient_powerFortyFour_ne_zero_of_coordinate_ne_zero,
  strictOrbitResidueWave827_isPure_powerFortyFour
#guard_depends_on
  fourierCoefficient_powerFortyFour_ne_zero_of_coordinate_ne_zero,
  Fermat.FiftyNine.Conservation.SplitPrimeFourier827.fourierCoefficient_pureCharacter

end Fermat.FiftyNine.Conservation.StrictOrbitResidueWavePlaceCovariance827
