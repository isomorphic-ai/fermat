/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Explicit residue kernels and the place orbit above 827

The full residue family constructed in `PrimalOrbitResidue827` has one
surjective reduction map for each cyclotomic Galois index.  This file proves
that their kernels are precisely the 58 places above 827 and identifies the
orientation of this explicit enumeration with the repository's canonical
cyclotomic place orbit.

The orientation is contragredient: the place indexed by `tau` is the kernel
of the explicit reduction map indexed by `tau⁻¹`.  This is the arithmetic
alignment needed before a Fourier residue wave can be compared with local
readings indexed by places.
-/
import Fermat.FiftyNine.Conservation.PrimalOrbitResidue827

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.OrbitPlace827

open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.CyclotomicLocalizationEquivariance827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]
  {zeta : K} (hZeta : IsPrimitiveRoot zeta 59)

theorem orbitReductionHom827_surjective (sigma : GaloisIndex59) :
    Function.Surjective (orbitReductionHom827 hZeta sigma) :=
  ZMod.ringHom_surjective _

theorem orbitRoot827_injective :
    Function.Injective orbitRoot827 := by
  intro sigma tau hroot
  have hsigma : (sigma : ZMod 59).val <
      orderOf Credit.attestationRoot := by
    rw [Credit.attestationRoot_order]
    exact ZMod.val_lt _
  have htau : (tau : ZMod 59).val <
      orderOf Credit.attestationRoot := by
    rw [Credit.attestationRoot_order]
    exact ZMod.val_lt _
  have hval : (sigma : ZMod 59).val = (tau : ZMod 59).val :=
    pow_injOn_Iio_orderOf hsigma htau hroot
  apply Units.ext
  exact ZMod.val_injective 59 hval

theorem orbitReductionHom827_ker_ne_bot (sigma : GaloisIndex59) :
    RingHom.ker (orbitReductionHom827 hZeta sigma) ≠ ⊥ := by
  intro hbot
  have hmem :
      (Credit.attestationPrime : NumberField.RingOfIntegers K) ∈
        RingHom.ker (orbitReductionHom827 hZeta sigma) := by
    rw [RingHom.mem_ker, map_natCast]
    exact ZMod.natCast_self Credit.attestationPrime
  rw [hbot, Ideal.mem_bot] at hmem
  norm_num [Credit.attestationPrime] at hmem

noncomputable def orbitPlace827 (sigma : GaloisIndex59) :
    IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K) where
  asIdeal := RingHom.ker (orbitReductionHom827 hZeta sigma)
  isPrime := RingHom.ker_isPrime _
  ne_bot := orbitReductionHom827_ker_ne_bot hZeta sigma

theorem orbitReductionHom827_comp_algebraMap
    (sigma : GaloisIndex59) :
    (orbitReductionHom827 hZeta sigma).comp
        (algebraMap ℤ (NumberField.RingOfIntegers K)) =
      Int.castRingHom (ZMod Credit.attestationPrime) := by
  ext n
  simp

theorem orbitPlace827_under_int (sigma : GaloisIndex59) :
    (orbitPlace827 hZeta sigma).asIdeal.under ℤ =
      Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) := by
  rw [Ideal.under_def]
  rw [← ZMod.ker_intCastRingHom Credit.attestationPrime]
  rw [← orbitReductionHom827_comp_algebraMap hZeta sigma]
  ext n
  change orbitReductionHom827 hZeta sigma
      (algebraMap ℤ (NumberField.RingOfIntegers K) n) = 0 ↔
    ((orbitReductionHom827 hZeta sigma).comp
      (algebraMap ℤ (NumberField.RingOfIntegers K))) n = 0
  rfl

theorem orbitPlace827_mem_placesOver827 (sigma : GaloisIndex59) :
    orbitPlace827 hZeta sigma ∈ placesOver827 K := by
  change Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) =
    (orbitPlace827 hZeta sigma).asIdeal.under ℤ
  exact (orbitPlace827_under_int hZeta sigma).symm

noncomputable def orbitPlace827Subtype (sigma : GaloisIndex59) :
    Place827 K :=
  ⟨orbitPlace827 hZeta sigma, orbitPlace827_mem_placesOver827 hZeta sigma⟩

theorem orbitPlace827Subtype_injective :
    Function.Injective (orbitPlace827Subtype hZeta) := by
  intro sigma tau hplace
  have hker :
      RingHom.ker (orbitReductionHom827 hZeta sigma) =
        RingHom.ker (orbitReductionHom827 hZeta tau) := by
    exact congrArg
      (fun v : Place827 K ↦ v.1.asIdeal) hplace
  have hhom : orbitReductionHom827 hZeta sigma =
      orbitReductionHom827 hZeta tau :=
    ZMod.ringHom_eq_of_ker_eq _ _ hker
  apply orbitRoot827_injective
  rw [← orbitReductionHom827_zeta hZeta sigma,
    ← orbitReductionHom827_zeta hZeta tau, hhom]

/-- The 58 explicit residue kernels exhaust the complete set of places above
827. -/
noncomputable def orbitPlaceEquiv827 :
    GaloisIndex59 ≃ Place827 K := by
  letI : Fintype (Place827 K) := (placesOver827_finite K).fintype
  refine Equiv.ofBijective (orbitPlace827Subtype hZeta) ?_
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact orbitPlace827Subtype_injective hZeta
  · rw [galoisIndex59_card]
    have hcard := placesOver827_ncard_eq_fiftyEight K
    change Nat.card (Place827 K) = 58 at hcard
    simpa only [Nat.card_eq_fintype_card] using hcard.symm

/-! ## Compatibility with the canonical cyclotomic action -/

private abbrev canonicalZeta827 (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] : K :=
  IsCyclotomicExtension.zeta 59 ℚ K

private abbrev canonicalZeta827_isPrimitive
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {59} ℚ K] :
    IsPrimitiveRoot (canonicalZeta827 K) 59 :=
  IsCyclotomicExtension.zeta_spec 59 ℚ K

theorem orbitRoot827_mul (sigma tau : GaloisIndex59) :
    orbitRoot827 sigma ^ (tau : ZMod 59).val =
      orbitRoot827 (sigma * tau) := by
  rw [orbitRoot827, orbitRoot827, ← pow_mul]
  apply pow_eq_pow_of_modEq _
    (IsPrimitiveRoot.iff_orderOf.mpr Credit.attestationRoot_order).pow_eq_one
  rw [← ZMod.natCast_eq_natCast_iff]
  calc
    (((sigma : ZMod 59).val * (tau : ZMod 59).val : ℕ) : ZMod 59) =
        (sigma : ZMod 59) * (tau : ZMod 59) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    _ = ((sigma * tau : GaloisIndex59) : ZMod 59) := rfl
    _ = ((((sigma * tau : GaloisIndex59) : ZMod 59).val : ℕ) :
        ZMod 59) := by
      rw [ZMod.natCast_zmod_val]

theorem orbitReductionHom827_comp_cyclotomicRingEquiv
    (sigma tau : GaloisIndex59) :
    (orbitReductionHom827 (canonicalZeta827_isPrimitive K) sigma).comp
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K tau).toRingHom =
      orbitReductionHom827 (canonicalZeta827_isPrimitive K) (sigma * tau) := by
  apply RingHom.ext
  intro x
  let leftAlg := ((orbitReductionHom827
    (canonicalZeta827_isPrimitive K) sigma).comp
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K tau).toRingHom).toIntAlgHom
  let rightAlg :=
    (orbitReductionHom827 (canonicalZeta827_isPrimitive K)
      (sigma * tau)).toIntAlgHom
  have heq : leftAlg = rightAlg := by
    apply (canonicalZeta827_isPrimitive K).integralPowerBasis.algHom_ext
    dsimp [leftAlg, rightAlg]
    rw [(canonicalZeta827_isPrimitive K).integralPowerBasis_gen]
    change orbitReductionHom827 (canonicalZeta827_isPrimitive K) sigma
        (KummerCriterion.cyclotomicRingOfIntegersEquiv
          (p := 59) K tau
            (canonicalZeta827_isPrimitive K).toInteger) =
      orbitReductionHom827 (canonicalZeta827_isPrimitive K) (sigma * tau)
        (canonicalZeta827_isPrimitive K).toInteger
    have hzeta :
        KummerCriterion.cyclotomicRingOfIntegersEquiv
            (p := 59) K tau
              (canonicalZeta827_isPrimitive K).toInteger =
          (canonicalZeta827_isPrimitive K).toInteger ^
            (tau : ZMod 59).val := by
      exact KummerCriterion.cyclotomicSigmaOfUnit_smul_zetaInteger
        (p := 59) K tau
    rw [hzeta, map_pow, orbitReductionHom827_zeta,
      orbitReductionHom827_zeta]
    exact orbitRoot827_mul sigma tau
  exact DFunLike.congr_fun heq x

theorem cyclotomicRingOfIntegersEquiv59_symm_local
    (tau : GaloisIndex59) :
    (KummerCriterion.cyclotomicRingOfIntegersEquiv
      (p := 59) K tau).symm =
      KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K tau⁻¹ := by
  apply RingEquiv.ext
  intro x
  apply (KummerCriterion.cyclotomicRingOfIntegersEquiv
    (p := 59) K tau).injective
  rw [RingEquiv.apply_symm_apply,
    ← KummerCriterion.cyclotomicRingOfIntegersEquiv_mul_apply,
    mul_inv_cancel,
    KummerCriterion.cyclotomicRingOfIntegersEquiv_one_apply]

theorem cyclotomicPlaceEquiv59_orbitPlace
    (sigma tau : GaloisIndex59) :
    cyclotomicPlaceEquiv59 K tau
        (orbitPlace827 (canonicalZeta827_isPrimitive K) sigma) =
      orbitPlace827 (canonicalZeta827_isPrimitive K) (sigma * tau⁻¹) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
  change Ideal.comap
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K tau).symm.toRingHom
      (RingHom.ker
        (orbitReductionHom827 (canonicalZeta827_isPrimitive K) sigma)) =
    RingHom.ker
      (orbitReductionHom827 (canonicalZeta827_isPrimitive K)
        (sigma * tau⁻¹))
  rw [cyclotomicRingOfIntegersEquiv59_symm_local]
  ext x
  change orbitReductionHom827 (canonicalZeta827_isPrimitive K) sigma
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := 59) K tau⁻¹ x) = 0 ↔
    orbitReductionHom827 (canonicalZeta827_isPrimitive K)
      (sigma * tau⁻¹) x = 0
  have happ := DFunLike.congr_fun
    (orbitReductionHom827_comp_cyclotomicRingEquiv
      (K := K) sigma tau⁻¹) x
  exact Iff.of_eq (congrArg (fun y : ZMod 827 ↦ y = 0) happ)

/-- With the identity residue kernel as the selected place, the repository's
place-orbit indexing is the inverse of the explicit residue-root indexing. -/
theorem indexedPlaceOrbitEquiv827_eq_orbitPlace827Subtype_inv
    (tau : GaloisIndex59) :
    indexedPlaceOrbitEquiv827 K
        (orbitPlace827Subtype (canonicalZeta827_isPrimitive K) 1) tau =
      orbitPlace827Subtype (canonicalZeta827_isPrimitive K) tau⁻¹ := by
  apply Subtype.ext
  change (indexedPlaceOrbitEquiv827 K
      (orbitPlace827Subtype (canonicalZeta827_isPrimitive K) 1) tau).1 = _
  rw [indexedPlaceOrbitEquiv827_eq_cyclotomicPlaceEquiv59]
  change cyclotomicPlaceEquiv59 K tau
      (orbitPlace827 (canonicalZeta827_isPrimitive K) 1) =
    orbitPlace827 (canonicalZeta827_isPrimitive K) tau⁻¹
  simpa using cyclotomicPlaceEquiv59_orbitPlace (K := K) 1 tau

end Fermat.FiftyNine.Conservation.OrbitPlace827
