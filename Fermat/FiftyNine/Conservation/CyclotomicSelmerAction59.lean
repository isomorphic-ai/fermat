/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The canonical cyclotomic action on the 59-Selmer carriers

This file is the thin `p = 59` adapter for the prime-generic cyclotomic
Selmer action.  The field, unit, Kummer-quotient, place, valuation, and
stable-support constructions all come from
`Fermat.Conservation.PrimeCyclotomicSelmerAction`.

Only the support at the rational prime 827 and its reflected landing remain
specific to the 59 campaign.  The strict and 827-supported representations
therefore restrict one and the same generic ambient action, and their
canonical inclusion intertwines by construction.
-/
import Fermat.Conservation.PrimeCyclotomicSelmerAction
import Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827

open scoped MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59

open Fermat.Conservation
open Fermat.Conservation.PrimeCyclotomicSelmerAction
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## The prime-generic action specialized at 59 -/

/-- The canonical action of `(ZMod 59)ˣ` on the cyclotomic field. -/
noncomputable abbrev cyclotomicFieldAction59 :
    MulSemiringAction GaloisIndex59 K :=
  cyclotomicFieldAction 59 K

/-- The cyclotomic field automorphism on nonzero elements. -/
noncomputable abbrev cyclotomicUnitEquiv59 (sigma : GaloisIndex59) :
    Kˣ ≃* Kˣ :=
  cyclotomicUnitEquiv 59 K sigma

@[simp]
theorem cyclotomicUnitEquiv59_one_apply (x : Kˣ) :
    cyclotomicUnitEquiv59 K 1 x = x :=
  cyclotomicUnitEquiv_one_apply 59 K x

@[simp]
theorem cyclotomicUnitEquiv59_mul_apply
    (sigma tau : GaloisIndex59) (x : Kˣ) :
    cyclotomicUnitEquiv59 K (sigma * tau) x =
      cyclotomicUnitEquiv59 K sigma (cyclotomicUnitEquiv59 K tau x) :=
  cyclotomicUnitEquiv_mul_apply 59 K sigma tau x

/-- Cyclotomic automorphisms preserve the subgroup of 59th powers. -/
theorem cyclotomicUnitEquiv59_maps_powerRange
    (sigma : GaloisIndex59) :
    (powMonoidHom 59 : Kˣ →* Kˣ).range ≤
      Subgroup.comap (cyclotomicUnitEquiv59 K sigma).toMonoidHom
        (powMonoidHom 59 : Kˣ →* Kˣ).range :=
  cyclotomicUnitEquiv_maps_powerRange 59 K sigma

/-- One cyclotomic automorphism descended to the ambient Kummer quotient. -/
noncomputable abbrev cyclotomicKummerHom59 (sigma : GaloisIndex59) :
    (Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) →*
      (Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) :=
  cyclotomicKummerHom 59 K sigma

@[simp]
theorem cyclotomicKummerHom59_mk
    (sigma : GaloisIndex59) (x : Kˣ) :
    cyclotomicKummerHom59 K sigma
        (QuotientGroup.mk' (powMonoidHom 59 : Kˣ →* Kˣ).range x) =
      QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (cyclotomicUnitEquiv59 K sigma x) :=
  cyclotomicKummerHom_mk 59 K sigma x

@[simp]
theorem cyclotomicKummerHom59_one_apply
    (q : Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) :
    cyclotomicKummerHom59 K 1 q = q :=
  cyclotomicKummerHom_one_apply 59 K q

theorem cyclotomicKummerHom59_mul_apply
    (sigma tau : GaloisIndex59)
    (q : Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) :
    cyclotomicKummerHom59 K (sigma * tau) q =
      cyclotomicKummerHom59 K sigma (cyclotomicKummerHom59 K tau q) :=
  cyclotomicKummerHom_mul_apply 59 K sigma tau q

/-- The same cyclotomic action restricted to the ring of integers. -/
noncomputable abbrev cyclotomicIntegerAction59 :
    MulSemiringAction GaloisIndex59 (𝓞 K) :=
  cyclotomicIntegerAction 59 K

local instance : MulSemiringAction GaloisIndex59 (𝓞 K) :=
  cyclotomicIntegerAction59 K

/-- A cyclotomic automorphism transports a height-one place by ideal image. -/
noncomputable abbrev cyclotomicPlaceEquiv59 (sigma : GaloisIndex59) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) ≃
      IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  cyclotomicPlaceEquiv 59 K sigma

theorem cyclotomicPlaceEquiv59_asIdeal
    (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (cyclotomicPlaceEquiv59 K sigma v).asIdeal = sigma • v.asIdeal :=
  cyclotomicPlaceEquiv_asIdeal 59 K sigma v

/-- Cyclotomic transport preserves the rational prime below a place. -/
theorem cyclotomicPlaceEquiv59_under_int
    (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (cyclotomicPlaceEquiv59 K sigma v).asIdeal.under ℤ =
      v.asIdeal.under ℤ :=
  cyclotomicPlaceEquiv_under_int 59 K sigma v

/-- In particular, the complete set of places above 827 is stable under the
cyclotomic action. -/
theorem cyclotomicPlaceEquiv59_mem_placesOver827_iff
    (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    cyclotomicPlaceEquiv59 K sigma v ∈ placesOver827 K ↔
      v ∈ placesOver827 K := by
  rw [mem_placesOver827_iff, mem_placesOver827_iff,
    cyclotomicPlaceEquiv59_under_int]

/-- Integer-valued height-one valuations are natural under the canonical
cyclotomic action, with contragredient place transport. -/
theorem valuationOfNeZero_cyclotomic59
    (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (x : Kˣ) :
    v.valuationOfNeZero (cyclotomicUnitEquiv59 K sigma x) =
      (cyclotomicPlaceEquiv59 K sigma⁻¹ v).valuationOfNeZero x :=
  valuationOfNeZero_cyclotomic 59 K sigma v x

/-! ## Valuation covariance and stable support -/

/-- The quotient-valued spelling of
`ord_v (sigma a) = ord_(sigma⁻¹ v) a`. -/
abbrev CyclotomicValuationCovariance59 : Prop :=
  CyclotomicValuationCovariance 59 K

/-- Cyclotomic valuation covariance, proved once in the prime-generic core. -/
theorem cyclotomicValuationCovariance59 :
    CyclotomicValuationCovariance59 K :=
  cyclotomicValuationCovariance 59 K

/-- A support preserved by every cyclotomic place transport. -/
abbrev CyclotomicStableSupport59
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Prop :=
  CyclotomicStableSupport 59 K S

/-- The empty support is cyclotomic-stable. -/
theorem cyclotomicStableSupport59_empty :
    CyclotomicStableSupport59 K
      (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :=
  cyclotomicStableSupport_empty 59 K

/-- The full 827 support is cyclotomic-stable. -/
theorem cyclotomicStableSupport59_placesOver827 :
    CyclotomicStableSupport59 K (placesOver827 K) := by
  intro sigma v
  exact cyclotomicPlaceEquiv59_mem_placesOver827_iff K sigma v

/-! ## Restriction of the generic action -/

/-- Restrict one ambient cyclotomic Kummer map to a stable supported Selmer
carrier.  Covariance is proved in the generic core and is not caller data. -/
noncomputable abbrev cyclotomicSelmerAddHomAt59
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport59 K S)
    (sigma : GaloisIndex59) :
    SelmerCarrierAt (𝓞 K) K S 59 →+ SelmerCarrierAt (𝓞 K) K S 59 :=
  cyclotomicSelmerAddHomAt 59 K S hS sigma

/-- The restricted map as a `PadicInt 59`-linear map. -/
noncomputable abbrev cyclotomicSelmerLinearMapAt59
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport59 K S)
    (sigma : GaloisIndex59) :
    SelmerCarrierAt (𝓞 K) K S 59 →ₗ[PadicInt 59]
      SelmerCarrierAt (𝓞 K) K S 59 :=
  cyclotomicSelmerLinearMapAt 59 K S hS sigma

/-- The canonical cyclotomic representation on a stable supported carrier. -/
noncomputable abbrev cyclotomicSelmerRepresentationAt59
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport59 K S) :
    SelmerDeltaRepresentationAt (R := 𝓞 K) (K := K) (p := 59)
      (Delta := GaloisIndex59) S :=
  cyclotomicSelmerRepresentationAt 59 K S hS

/-- The canonical strict 59-Selmer representation. -/
noncomputable abbrev cyclotomicStrictSelmerRepresentation59 :
    SelmerDeltaRepresentation (R := 𝓞 K) (K := K) (p := 59)
      (Delta := GaloisIndex59) :=
  cyclotomicStrictSelmerRepresentation 59 K

/-! ## The 827-specific adapter -/

/-- The canonical representation on the carrier relaxed at every place over
827. -/
noncomputable abbrev cyclotomicQRelaxedSelmerRepresentation827 :
    QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59 :=
  cyclotomicSelmerRepresentationAt59 K (placesOver827 K)
    (cyclotomicStableSupport59_placesOver827 K)

/-- The strict and 827-relaxed actions agree along the canonical support
inclusion, by specialization of the prime-generic compatibility theorem. -/
def cyclotomicEmptySupportActionCompatibility827 :
    EmptySupportActionCompatibility
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K) :=
  cyclotomicEmptySupportActionCompatibilityAt 59 K (placesOver827 K)
    (cyclotomicStableSupport59_placesOver827 K)

/-- The canonical reflected strict-to-827-supported landing for every pair
of characters, specialized from the prime-generic reflected landing. -/
def cyclotomicReflectedEmptySupportLanding827
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) :
    ReflectedEmptySupportLanding827
      (cyclotomicStrictSelmerRepresentation59 K)
      (cyclotomicQRelaxedSelmerRepresentation827 K) omega chi :=
  cyclotomicReflectedEmptySupportLandingAt 59 K (placesOver827 K)
    (cyclotomicStableSupport59_placesOver827 K) omega chi

end Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
