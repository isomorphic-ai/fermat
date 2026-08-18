/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The prime-generic cyclotomic action on Selmer carriers

For a prime `p`, this file constructs the actual action of
`(ZMod p)ˣ` on the Kummer quotient of a `p`-th cyclotomic field and
restricts it to every cyclotomic-stable supported Selmer carrier.

The action is built from the canonical cyclotomic Galois equivalence.  In
particular, no action or covariance certificate is supplied by a caller.
The empty-support specialization is the genuine
strict Selmer representation used by the unit and class naturality maps.
-/
import Fermat.Conservation.SelmerEigenspace
import KummerCriterion.UnitQuotient.DeltaAction
import Mathlib.GroupTheory.GroupAction.Quotient

open scoped MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.Conservation.PrimeCyclotomicSelmerAction

open Fermat.Conservation.SelmerEigenspace

set_option maxRecDepth 10000
set_option maxHeartbeats 0

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K]

local instance : Fact (0 < p) := ⟨(Fact.out : Nat.Prime p).pos⟩

/-! ## The common ambient action -/

/-- The actual action of `(ZMod p)ˣ` on the cyclotomic field, transported
from `Gal(K/ℚ)` along the standard cyclotomic Galois equivalence. -/
noncomputable abbrev cyclotomicFieldAction :
    MulSemiringAction (KummerCriterion.CyclotomicUnitDelta p) K :=
  MulSemiringAction.compHom K
    (KummerCriterion.cyclotomicGalEquivZMod (p := p) K).symm.toMonoidHom

/-- The field automorphism on nonzero elements, bundled as a monoid
automorphism. -/
noncomputable def cyclotomicUnitEquiv
    (sigma : KummerCriterion.CyclotomicUnitDelta p) : Kˣ ≃* Kˣ :=
  Units.mapEquiv
    (KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma).toMulEquiv

@[simp]
theorem cyclotomicUnitEquiv_one_apply (x : Kˣ) :
    cyclotomicUnitEquiv p K 1 x = x := by
  apply Units.ext
  simp [cyclotomicUnitEquiv, KummerCriterion.cyclotomicSigmaOfUnit_one]

@[simp]
theorem cyclotomicUnitEquiv_mul_apply
    (sigma tau : KummerCriterion.CyclotomicUnitDelta p) (x : Kˣ) :
    cyclotomicUnitEquiv p K (sigma * tau) x =
      cyclotomicUnitEquiv p K sigma (cyclotomicUnitEquiv p K tau x) := by
  apply Units.ext
  simp [cyclotomicUnitEquiv, KummerCriterion.cyclotomicSigmaOfUnit_mul]

/-- Cyclotomic automorphisms preserve the subgroup of `p`-th powers. -/
theorem cyclotomicUnitEquiv_maps_powerRange
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    (powMonoidHom p : Kˣ →* Kˣ).range ≤
      Subgroup.comap (cyclotomicUnitEquiv p K sigma).toMonoidHom
        (powMonoidHom p : Kˣ →* Kˣ).range := by
  rintro _ ⟨y, rfl⟩
  refine ⟨cyclotomicUnitEquiv p K sigma y, ?_⟩
  change (cyclotomicUnitEquiv p K sigma y) ^ p =
    cyclotomicUnitEquiv p K sigma (y ^ p)
  exact (map_pow (cyclotomicUnitEquiv p K sigma) y p).symm

/-- One cyclotomic automorphism descended to the ambient Kummer quotient. -/
noncomputable def cyclotomicKummerHom
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
      (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :=
  QuotientGroup.map
    (powMonoidHom p : Kˣ →* Kˣ).range
    (powMonoidHom p : Kˣ →* Kˣ).range
    (cyclotomicUnitEquiv p K sigma).toMonoidHom
    (cyclotomicUnitEquiv_maps_powerRange p K sigma)

@[simp]
theorem cyclotomicKummerHom_mk
    (sigma : KummerCriterion.CyclotomicUnitDelta p) (x : Kˣ) :
    cyclotomicKummerHom p K sigma
        (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range x) =
      QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range
        (cyclotomicUnitEquiv p K sigma x) :=
  rfl

@[simp]
theorem cyclotomicKummerHom_one_apply
    (q : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :
    cyclotomicKummerHom p K 1 q = q := by
  induction q using QuotientGroup.induction_on with
  | _ x =>
      change QuotientGroup.mk' _ (cyclotomicUnitEquiv p K 1 x) =
        QuotientGroup.mk' _ x
      rw [cyclotomicUnitEquiv_one_apply]

theorem cyclotomicKummerHom_mul_apply
    (sigma tau : KummerCriterion.CyclotomicUnitDelta p)
    (q : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :
    cyclotomicKummerHom p K (sigma * tau) q =
      cyclotomicKummerHom p K sigma (cyclotomicKummerHom p K tau q) := by
  induction q using QuotientGroup.induction_on with
  | _ x =>
      change QuotientGroup.mk' _ (cyclotomicUnitEquiv p K (sigma * tau) x) =
        QuotientGroup.mk' _
          (cyclotomicUnitEquiv p K sigma (cyclotomicUnitEquiv p K tau x))
      rw [cyclotomicUnitEquiv_mul_apply]

/-! ## The induced action on height-one places -/

/-- The same cyclotomic action restricted to the ring of integers. -/
noncomputable abbrev cyclotomicIntegerAction :
    MulSemiringAction (KummerCriterion.CyclotomicUnitDelta p) (𝓞 K) :=
  MulSemiringAction.compHom (𝓞 K)
    (KummerCriterion.cyclotomicGalEquivZMod (p := p) K).symm.toMonoidHom

local instance :
    MulSemiringAction (KummerCriterion.CyclotomicUnitDelta p) (𝓞 K) :=
  cyclotomicIntegerAction p K

/-- A cyclotomic automorphism transports a height-one place by ideal image. -/
noncomputable def cyclotomicPlaceEquiv
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) ≃
      IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K sigma)

theorem cyclotomicPlaceEquiv_asIdeal
    (sigma : KummerCriterion.CyclotomicUnitDelta p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (cyclotomicPlaceEquiv p K sigma v).asIdeal = sigma • v.asIdeal := by
  change v.asIdeal.comap
      (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K sigma).symm =
    sigma • v.asIdeal
  rw [Ideal.comap_symm]
  rfl

/-- Cyclotomic transport preserves the rational prime below a place. -/
theorem cyclotomicPlaceEquiv_under_int
    (sigma : KummerCriterion.CyclotomicUnitDelta p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (cyclotomicPlaceEquiv p K sigma v).asIdeal.under ℤ =
      v.asIdeal.under ℤ := by
  rw [cyclotomicPlaceEquiv_asIdeal]
  exact Ideal.under_smul ℤ v.asIdeal sigma

/-! ## Valuation transport through ring equivalences -/

/-- Mapping ideals along a ring equivalence is multiplicative and bijective. -/
private def idealMapMulEquiv {R : Type*} [CommSemiring R]
    (e : R ≃+* R) : Ideal R ≃* Ideal R :=
  MulEquiv.ofBijective (Ideal.mapHom e.toRingHom) <| by
    constructor
    · intro I J h
      change I.map e.toRingHom = J.map e.toRingHom at h
      have h' := congrArg (fun L : Ideal R => L.map e.symm.toRingHom) h
      calc
        I = (I.map (e : R →+* R)).map (e.symm : R →+* R) :=
          (Ideal.map_of_equiv e).symm
        _ = (J.map (e : R →+* R)).map (e.symm : R →+* R) := h'
        _ = J := Ideal.map_of_equiv e
    · exact Ideal.map_surjective_of_surjective e.toRingHom e.surjective

private theorem idealMapMulEquiv_apply {R : Type*} [CommSemiring R]
    (e : R ≃+* R) (I : Ideal R) :
    idealMapMulEquiv e I = I.map e.toRingHom :=
  rfl

/-- The normalized height-one valuation on a Dedekind domain is natural under
a ring equivalence, with the place transported contragrediently. -/
private theorem intValuation_equiv
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R)
    (v : IsDedekindDomain.HeightOneSpectrum R) (r : R) :
    v.intValuation (e r) =
      (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.symm v).intValuation r := by
  by_cases hr : r = 0
  · subst r
    simp
  · rw [v.intValuation_eq_exp_neg_multiplicity (by simpa using hr),
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity
        (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.symm v) hr]
    congr 3
    have h := multiplicity_map_eq (idealMapMulEquiv e)
      (a := (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.symm v).asIdeal)
      (b := Ideal.span {r})
    rw [idealMapMulEquiv_apply, idealMapMulEquiv_apply] at h
    change multiplicity (Ideal.map e.toRingHom (v.asIdeal.comap e.toRingHom))
        (Ideal.map e.toRingHom (Ideal.span {r})) =
      multiplicity (v.asIdeal.comap e.toRingHom) (Ideal.span {r}) at h
    rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective,
      Ideal.map_span, Set.image_singleton] at h
    exact h

/-- The corresponding fraction-field valuation is natural under the unique
extension of the ring equivalence. -/
private theorem valuation_equiv
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
    (e : R ≃+* R)
    (v : IsDedekindDomain.HeightOneSpectrum R) (x : F) :
    v.valuation F (IsFractionRing.ringEquivOfRingEquiv e x) =
      (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv e.symm v).valuation F x := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
  simp only [IsFractionRing.ringEquivOfRingEquiv,
    IsLocalization.ringEquivOfRingEquiv_mk']
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    intValuation_equiv e v r, intValuation_equiv e v s]

/-- Readback of the quotient valuation on a Kummer representative. -/
private theorem valuationOfNeZeroMod_mk
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
    (v : IsDedekindDomain.HeightOneSpectrum R) (n : ℕ) (x : Fˣ) :
    v.valuationOfNeZeroMod n
        (QuotientGroup.mk' (powMonoidHom n : Fˣ →* Fˣ).range x) =
      (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative
        (QuotientGroup.mk'
          (AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)))
          (v.valuationOfNeZero x)) := by
  erw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod,
    MonoidHom.comp_apply, QuotientGroup.map_mk']

/-- The fraction-field equivalence induced from the ring-of-integers action is
the original cyclotomic field automorphism. -/
private theorem cyclotomicFractionEquiv_eq
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    IsFractionRing.ringEquivOfRingEquiv
        (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K sigma) =
      (KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma).toRingEquiv := by
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext
    (nonZeroDivisors (NumberField.RingOfIntegers K))
  ext x
  change IsFractionRing.ringEquivOfRingEquiv
      (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K sigma)
        (algebraMap (NumberField.RingOfIntegers K) K x) =
    KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma
      (algebraMap (NumberField.RingOfIntegers K) K x)
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  change ((KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma • x :
      NumberField.RingOfIntegers K) : K) =
    KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma • (x : K)
  exact algebraMap.coe_smul'
    (KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma) x K

/-- Inversion of the index agrees with inversion of the induced
ring-of-integers equivalence. -/
private theorem cyclotomicRingOfIntegersEquiv_symm
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K sigma).symm =
      KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K sigma⁻¹ := by
  apply RingEquiv.ext
  intro x
  apply (KummerCriterion.cyclotomicRingOfIntegersEquiv
    (p := p) K sigma).injective
  rw [RingEquiv.apply_symm_apply,
    ← KummerCriterion.cyclotomicRingOfIntegersEquiv_mul_apply,
    mul_inv_cancel, KummerCriterion.cyclotomicRingOfIntegersEquiv_one_apply]

/-- Integer-valued height-one valuations of field units are natural under
the canonical cyclotomic action, with contragredient place transport. -/
theorem valuationOfNeZero_cyclotomic
    (sigma : KummerCriterion.CyclotomicUnitDelta p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    v.valuationOfNeZero (cyclotomicUnitEquiv p K sigma x) =
      (cyclotomicPlaceEquiv p K sigma⁻¹ v).valuationOfNeZero x := by
  rw [← WithZero.coe_inj,
    IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq,
    IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
  change v.valuation K
      (KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma (x : K)) = _
  have heval :
      KummerCriterion.cyclotomicSigmaOfUnit (p := p) K sigma (x : K) =
        IsFractionRing.ringEquivOfRingEquiv
          (KummerCriterion.cyclotomicRingOfIntegersEquiv (p := p) K sigma)
          (x : K) :=
    congrArg (fun e : K ≃+* K => e (x : K))
      (cyclotomicFractionEquiv_eq p K sigma).symm
  rw [heval, valuation_equiv]
  change
    (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
      (KummerCriterion.cyclotomicRingOfIntegersEquiv
        (p := p) K sigma).symm v).valuation K (x : K) = _
  rw [cyclotomicRingOfIntegersEquiv_symm]
  rfl

/-! ## The exact valuation-naturality boundary -/

/-- Quotient-valued cyclotomic valuation covariance. -/
def CyclotomicValuationCovariance : Prop :=
  ∀ (sigma : KummerCriterion.CyclotomicUnitDelta p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range),
    v.valuationOfNeZeroMod p (cyclotomicKummerHom p K sigma q) =
      (cyclotomicPlaceEquiv p K sigma⁻¹ v).valuationOfNeZeroMod p q

/-- Cyclotomic covariance follows from ideal-multiplicity transport. -/
theorem cyclotomicValuationCovariance :
    CyclotomicValuationCovariance p K := by
  intro sigma v q
  induction q using QuotientGroup.induction_on with
  | _ x =>
      change v.valuationOfNeZeroMod p
          (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range
            (cyclotomicUnitEquiv p K sigma x)) =
        (cyclotomicPlaceEquiv p K sigma⁻¹ v).valuationOfNeZeroMod p
          (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range x)
      rw [valuationOfNeZeroMod_mk, valuationOfNeZeroMod_mk,
        valuationOfNeZero_cyclotomic]

/-! ## Restriction of the common ambient action -/

/-- A support is stable when every cyclotomic place transport preserves it. -/
def CyclotomicStableSupport
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ (sigma : KummerCriterion.CyclotomicUnitDelta p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    cyclotomicPlaceEquiv p K sigma v ∈ S ↔ v ∈ S

/-- The empty support is cyclotomic-stable. -/
theorem cyclotomicStableSupport_empty :
    CyclotomicStableSupport p K
      (∅ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) := by
  intro sigma v
  simp

/-- Restrict one ambient cyclotomic Kummer map to a stable supported Selmer
carrier. -/
noncomputable def cyclotomicSelmerAddHomAt
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    SelmerCarrierAt (𝓞 K) K S p →+ SelmerCarrierAt (𝓞 K) K S p where
  toFun x := Additive.ofMul ⟨
    cyclotomicKummerHom p K sigma (Additive.toMul x).1,
    by
      intro v hv
      rw [cyclotomicValuationCovariance p K sigma v (Additive.toMul x).1]
      exact (Additive.toMul x).2
        (cyclotomicPlaceEquiv p K sigma⁻¹ v)
        (fun hmem => hv ((hS sigma⁻¹ v).mp hmem))⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact map_one (cyclotomicKummerHom p K sigma)
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact map_mul (cyclotomicKummerHom p K sigma)
      (Additive.toMul x).1 (Additive.toMul y).1

/-- The restricted additive map is automatically `PadicInt p`-linear. -/
noncomputable def cyclotomicSelmerLinearMapAt
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S)
    (sigma : KummerCriterion.CyclotomicUnitDelta p) :
    SelmerCarrierAt (𝓞 K) K S p →ₗ[PadicInt p]
      SelmerCarrierAt (𝓞 K) K S p where
  toFun := cyclotomicSelmerAddHomAt p K S hS sigma
  map_add' := map_add _
  map_smul' a x := by
    change cyclotomicSelmerAddHomAt p K S hS sigma
        (PadicInt.toZMod a • x) =
      PadicInt.toZMod a • cyclotomicSelmerAddHomAt p K S hS sigma x
    exact ZMod.map_smul (cyclotomicSelmerAddHomAt p K S hS sigma)
      (PadicInt.toZMod a) x

/-- The actual cyclotomic representation on any stable supported Selmer
carrier. -/
noncomputable def cyclotomicSelmerRepresentationAt
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (hS : CyclotomicStableSupport p K S) :
    SelmerDeltaRepresentationAt (R := 𝓞 K) (K := K) (p := p)
      (Delta := KummerCriterion.CyclotomicUnitDelta p) S where
  toFun sigma := cyclotomicSelmerLinearMapAt p K S hS sigma
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact cyclotomicKummerHom_one_apply p K (Additive.toMul x).1
  map_mul' sigma tau := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact cyclotomicKummerHom_mul_apply p K sigma tau (Additive.toMul x).1

/-- The canonical strict `p`-Selmer representation. -/
noncomputable def cyclotomicStrictSelmerRepresentation :
    SelmerDeltaRepresentation (R := 𝓞 K) (K := K) (p := p)
      (Delta := KummerCriterion.CyclotomicUnitDelta p) :=
  cyclotomicSelmerRepresentationAt p K ∅
    (cyclotomicStableSupport_empty p K)

end Fermat.Conservation.PrimeCyclotomicSelmerAction
