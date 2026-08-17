/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The canonical cyclotomic action on the 59-Selmer carriers

This file builds the common ambient action underlying the strict and
827-supported Selmer carriers.  The action starts with the actual cyclotomic
field automorphisms, descends through the Kummer quotient, and is then
restricted to Selmer conditions.

The only arithmetic boundary retained below is covariance of the height-one
valuations under a field automorphism.  Everything after that statement is
carrier restriction and subtype bookkeeping; in particular the canonical
empty-support inclusion intertwines by construction.
-/
import Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
import KummerCriterion.UnitQuotient.DeltaAction
import Mathlib.GroupTheory.GroupAction.Quotient

open scoped MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.EmptySupportReflectedInclusion827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-! ## The common ambient action -/

/-- The actual action of `(ZMod 59)ˣ` on the cyclotomic field, transported
from `Gal(K/ℚ)` along the standard cyclotomic Galois equivalence. -/
noncomputable abbrev cyclotomicFieldAction59 :
    MulSemiringAction GaloisIndex59 K :=
  MulSemiringAction.compHom K
    (KummerCriterion.cyclotomicGalEquivZMod (p := 59) K).symm.toMonoidHom

/-- The field automorphism on nonzero elements, bundled as a monoid
automorphism. -/
noncomputable def cyclotomicUnitEquiv59 (sigma : GaloisIndex59) :
    Kˣ ≃* Kˣ :=
  Units.mapEquiv
    (KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K sigma).toMulEquiv

@[simp]
theorem cyclotomicUnitEquiv59_one_apply (x : Kˣ) :
    cyclotomicUnitEquiv59 K 1 x = x := by
  apply Units.ext
  simp [cyclotomicUnitEquiv59,
    KummerCriterion.cyclotomicSigmaOfUnit_one]

@[simp]
theorem cyclotomicUnitEquiv59_mul_apply
    (sigma tau : GaloisIndex59) (x : Kˣ) :
    cyclotomicUnitEquiv59 K (sigma * tau) x =
      cyclotomicUnitEquiv59 K sigma (cyclotomicUnitEquiv59 K tau x) := by
  apply Units.ext
  simp [cyclotomicUnitEquiv59,
    KummerCriterion.cyclotomicSigmaOfUnit_mul]

/-- Cyclotomic automorphisms preserve the subgroup of 59th powers. -/
theorem cyclotomicUnitEquiv59_maps_powerRange
    (sigma : GaloisIndex59) :
    (powMonoidHom 59 : Kˣ →* Kˣ).range ≤
      Subgroup.comap (cyclotomicUnitEquiv59 K sigma).toMonoidHom
        (powMonoidHom 59 : Kˣ →* Kˣ).range := by
  rintro _ ⟨y, rfl⟩
  refine ⟨cyclotomicUnitEquiv59 K sigma y, ?_⟩
  change (cyclotomicUnitEquiv59 K sigma y) ^ 59 =
    cyclotomicUnitEquiv59 K sigma (y ^ 59)
  exact (map_pow (cyclotomicUnitEquiv59 K sigma) y 59).symm

/-- One cyclotomic automorphism descended to the ambient Kummer quotient. -/
noncomputable def cyclotomicKummerHom59 (sigma : GaloisIndex59) :
    (Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) →*
      (Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) :=
  QuotientGroup.map
    (powMonoidHom 59 : Kˣ →* Kˣ).range
    (powMonoidHom 59 : Kˣ →* Kˣ).range
    (cyclotomicUnitEquiv59 K sigma).toMonoidHom
    (cyclotomicUnitEquiv59_maps_powerRange K sigma)

@[simp]
theorem cyclotomicKummerHom59_mk
    (sigma : GaloisIndex59) (x : Kˣ) :
    cyclotomicKummerHom59 K sigma
        (QuotientGroup.mk' (powMonoidHom 59 : Kˣ →* Kˣ).range x) =
      QuotientGroup.mk'
        (powMonoidHom 59 : Kˣ →* Kˣ).range
        (cyclotomicUnitEquiv59 K sigma x) :=
  rfl

@[simp]
theorem cyclotomicKummerHom59_one_apply
    (q : Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) :
    cyclotomicKummerHom59 K 1 q = q := by
  induction q using QuotientGroup.induction_on with
  | _ x =>
      change QuotientGroup.mk' _ (cyclotomicUnitEquiv59 K 1 x) =
        QuotientGroup.mk' _ x
      rw [cyclotomicUnitEquiv59_one_apply]

theorem cyclotomicKummerHom59_mul_apply
    (sigma tau : GaloisIndex59)
    (q : Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) :
    cyclotomicKummerHom59 K (sigma * tau) q =
      cyclotomicKummerHom59 K sigma (cyclotomicKummerHom59 K tau q) := by
  induction q using QuotientGroup.induction_on with
  | _ x =>
      change QuotientGroup.mk' _ (cyclotomicUnitEquiv59 K (sigma * tau) x) =
        QuotientGroup.mk' _
          (cyclotomicUnitEquiv59 K sigma (cyclotomicUnitEquiv59 K tau x))
      rw [cyclotomicUnitEquiv59_mul_apply]

/-! ## The induced action on height-one places -/

/-- The same cyclotomic action restricted to the ring of integers. -/
noncomputable abbrev cyclotomicIntegerAction59 :
    MulSemiringAction GaloisIndex59 (𝓞 K) :=
  MulSemiringAction.compHom (𝓞 K)
    (KummerCriterion.cyclotomicGalEquivZMod (p := 59) K).symm.toMonoidHom

local instance : MulSemiringAction GaloisIndex59 (𝓞 K) :=
  cyclotomicIntegerAction59 K

/-- A cyclotomic automorphism transports a height-one place by ideal image. -/
noncomputable def cyclotomicPlaceEquiv59 (sigma : GaloisIndex59) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) ≃
      IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := 59) K sigma)

theorem cyclotomicPlaceEquiv59_asIdeal
    (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (cyclotomicPlaceEquiv59 K sigma v).asIdeal = sigma • v.asIdeal := by
  change v.asIdeal.comap
      (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := 59) K sigma).symm =
    sigma • v.asIdeal
  rw [Ideal.comap_symm]
  rfl

/-- Cyclotomic transport preserves the rational prime below a place. -/
theorem cyclotomicPlaceEquiv59_under_int
    (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (cyclotomicPlaceEquiv59 K sigma v).asIdeal.under ℤ =
      v.asIdeal.under ℤ := by
  rw [cyclotomicPlaceEquiv59_asIdeal]
  exact Ideal.under_smul ℤ v.asIdeal sigma

/-- In particular, the complete set of places above 827 is stable under the
cyclotomic action. -/
theorem cyclotomicPlaceEquiv59_mem_placesOver827_iff
    (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    cyclotomicPlaceEquiv59 K sigma v ∈ placesOver827 K ↔
      v ∈ placesOver827 K := by
  rw [mem_placesOver827_iff, mem_placesOver827_iff,
    cyclotomicPlaceEquiv59_under_int]

/-! ## The exact valuation-naturality boundary -/

/-- The sole missing arithmetic naturality lemma.

This is the quotient-valued spelling of
`ord_v (sigma a) = ord_(sigma⁻¹ v) a`.  It is a proposition rather than an
axiom or provider object: once Mathlib's height-one valuation API supplies
this naturality theorem, callers can discharge this argument canonically. -/
def CyclotomicValuationCovariance59 : Prop :=
  ∀ (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range),
    v.valuationOfNeZeroMod 59 (cyclotomicKummerHom59 K sigma q) =
      (cyclotomicPlaceEquiv59 K sigma⁻¹ v).valuationOfNeZeroMod 59 q

/-! ## Restriction of the common ambient action -/

/-- A stable support is one preserved by every cyclotomic place transport. -/
def CyclotomicStableSupport59
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ (sigma : GaloisIndex59)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    cyclotomicPlaceEquiv59 K sigma v ∈ S ↔ v ∈ S

/-- The empty support is cyclotomic-stable. -/
theorem cyclotomicStableSupport59_empty :
    CyclotomicStableSupport59 K
      (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) := by
  intro sigma v
  simp

/-- The full 827 support is cyclotomic-stable. -/
theorem cyclotomicStableSupport59_placesOver827 :
    CyclotomicStableSupport59 K (placesOver827 K) := by
  intro sigma v
  exact cyclotomicPlaceEquiv59_mem_placesOver827_iff K sigma v

/-- Restrict one ambient cyclotomic Kummer map to a stable supported Selmer
carrier. -/
noncomputable def cyclotomicSelmerAddHomAt59
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport59 K S)
    (hcov : CyclotomicValuationCovariance59 K)
    (sigma : GaloisIndex59) :
    SelmerCarrierAt (𝓞 K) K S 59 →+
      SelmerCarrierAt (𝓞 K) K S 59 where
  toFun x := Additive.ofMul ⟨
    cyclotomicKummerHom59 K sigma (Additive.toMul x).1,
    by
      intro v hv
      rw [hcov sigma v (Additive.toMul x).1]
      exact (Additive.toMul x).2
        (cyclotomicPlaceEquiv59 K sigma⁻¹ v)
        (fun hmem => hv ((hS sigma⁻¹ v).mp hmem))⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact map_one (cyclotomicKummerHom59 K sigma)
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact map_mul (cyclotomicKummerHom59 K sigma)
      (Additive.toMul x).1 (Additive.toMul y).1

/-- The restricted additive map is automatically `PadicInt 59`-linear,
because the coefficient action factors through the canonical `ZMod 59`
module structure. -/
noncomputable def cyclotomicSelmerLinearMapAt59
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport59 K S)
    (hcov : CyclotomicValuationCovariance59 K)
    (sigma : GaloisIndex59) :
    SelmerCarrierAt (𝓞 K) K S 59 →ₗ[PadicInt 59]
      SelmerCarrierAt (𝓞 K) K S 59 where
  toFun := cyclotomicSelmerAddHomAt59 K S hS hcov sigma
  map_add' := map_add _
  map_smul' a x := by
    change cyclotomicSelmerAddHomAt59 K S hS hcov sigma
        (PadicInt.toZMod a • x) =
      PadicInt.toZMod a •
        cyclotomicSelmerAddHomAt59 K S hS hcov sigma x
    exact ZMod.map_smul
      (cyclotomicSelmerAddHomAt59 K S hS hcov sigma)
      (PadicInt.toZMod a) x

/-- The actual cyclotomic representation on any stable supported Selmer
carrier.  No per-prime or per-class action data are supplied. -/
noncomputable def cyclotomicSelmerRepresentationAt59
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport59 K S)
    (hcov : CyclotomicValuationCovariance59 K) :
    SelmerDeltaRepresentationAt (R := 𝓞 K) (K := K) (p := 59)
      (Delta := GaloisIndex59) S where
  toFun sigma := cyclotomicSelmerLinearMapAt59 K S hS hcov sigma
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact cyclotomicKummerHom59_one_apply K (Additive.toMul x).1
  map_mul' sigma tau := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact cyclotomicKummerHom59_mul_apply K sigma tau
      (Additive.toMul x).1

/-- The canonical strict 59-Selmer representation. -/
noncomputable def cyclotomicStrictSelmerRepresentation59
    (hcov : CyclotomicValuationCovariance59 K) :
    SelmerDeltaRepresentation (R := 𝓞 K) (K := K) (p := 59)
      (Delta := GaloisIndex59) :=
  cyclotomicSelmerRepresentationAt59 K ∅
    (cyclotomicStableSupport59_empty K) hcov

/-- The canonical representation on the carrier relaxed at every place over
827. -/
noncomputable def cyclotomicQRelaxedSelmerRepresentation827
    (hcov : CyclotomicValuationCovariance59 K) :
    QRelaxedSelmerDeltaRepresentation827 K GaloisIndex59 :=
  cyclotomicSelmerRepresentationAt59 K (placesOver827 K)
    (cyclotomicStableSupport59_placesOver827 K) hcov

/-- The strict and 827-relaxed actions agree along the canonical support
inclusion, because both are restrictions of the same ambient quotient map. -/
def cyclotomicEmptySupportActionCompatibility827
    (hcov : CyclotomicValuationCovariance59 K) :
    EmptySupportActionCompatibility
      (cyclotomicStrictSelmerRepresentation59 K hcov)
      (cyclotomicQRelaxedSelmerRepresentation827 K hcov) where
  inclusion_intertwines := by
    intro sigma x
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl

end Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
