/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Fable

# A receipted carrier for ideal classes

An ideal class is intentionally lossy: multiplication by a principal ideal is
forgotten.  This module keeps a bounded representative, the principal scalar
which relates it to the source ideal, and every annihilator certificate.  Only
the explicit `lossyProjection` forgets those receipts.

The algebraic interface is generic over a commutative multiplicative carrier.
For rings of integers in number fields, Mathlib's Minkowski theorem supplies a
concrete bounded representative, and quotient-group equality supplies its
principalization scalar.
-/
import Mathlib.NumberTheory.NumberField.ClassNumber

open scoped nonZeroDivisors NumberField Real

namespace Fermat.Conservation.ClassCarrier

universe uS uG uO uP

/-- A bounded-region specification.  This packages only the membership
predicate; a `BoundedRepresentativeInterface` must separately prove that its
chosen representatives lie in it. -/
structure BoundedRegion (G : Type uG) where
  contains : G → Prop

/-- A proof-bearing record that an operator annihilates a payload.  The
operator and payload are retained alongside the equation, rather than being
collapsed to a Boolean or a class label. -/
structure AnnihilatorReceipt (Operator : Type uO) (Payload : Type uP)
    [SMul Operator Payload] [Zero Payload] where
  operator : Operator
  payload : Payload
  annihilates : operator • payload = 0

/-- The scalar discarded by quotienting by principal elements, together with
the exact equation which makes that discard legitimate. -/
structure PrincipalizationReceipt {S : Type uS} {G : Type uG}
    [Group S] [CommGroup G] (principal : S →* G) (source reduced : G) where
  beta : S
  source_eq : source = principal beta * reduced

/-- The non-lossy state above a source element.  Its representative is in the
stated bounded region; the principalization and annihilator receipts remain
part of the state. -/
structure State {S : Type uS} {G : Type uG} [Group S] [CommGroup G]
    (region : BoundedRegion G) (principal : S →* G) (source : G)
    (Operator : Type uO) (Payload : Type uP) [SMul Operator Payload]
    [Zero Payload] where
  reduced : G
  reduced_mem : region.contains reduced
  principalization : PrincipalizationReceipt principal source reduced
  annihilatorReceipts : List (AnnihilatorReceipt Operator Payload)

namespace State

variable {S : Type uS} {G : Type uG} [Group S] [CommGroup G]
  {region : BoundedRegion G} {principal : S →* G} {source : G}
  {Operator : Type uO} {Payload : Type uP} [SMul Operator Payload]
  [Zero Payload]

/-- The retained principalization scalar. -/
def beta (state : State region principal source Operator Payload) : S :=
  state.principalization.beta

/-- Reading the receipt recovers the source element exactly. -/
theorem source_eq_principal_mul_reduced
    (state : State region principal source Operator Payload) :
    source = principal state.beta * state.reduced :=
  state.principalization.source_eq

/-- The only intentionally lossy map: keep the representative's quotient
class and erase its principalization scalar and annihilator receipts. -/
def lossyProjection (state : State region principal source Operator Payload) :
    G ⧸ principal.range :=
  QuotientGroup.mk' principal.range state.reduced

/-- The receipted representative and its source have the same lossy class. -/
theorem lossyProjection_eq_source
    (state : State region principal source Operator Payload) :
    state.lossyProjection = QuotientGroup.mk' principal.range source := by
  have hprincipal :
      QuotientGroup.mk' principal.range (principal state.beta) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨state.beta, rfl⟩
  have hsource := congrArg (QuotientGroup.mk' principal.range)
    state.source_eq_principal_mul_reduced
  rw [map_mul, hprincipal, one_mul] at hsource
  exact hsource.symm

/-- Quotient projection cannot distinguish different receipt histories once
the reduced representative is the same.  This is the precise loss incurred
by passing from `State` to a quotient class. -/
theorem lossyProjection_ignores_receipts
    (left right : State region principal source Operator Payload)
    (h : left.reduced = right.reduced) :
    left.lossyProjection = right.lossyProjection := by
  rw [lossyProjection, lossyProjection, h]

/-- In particular, no equality of `beta` values or annihilator receipt lists
is required for equal quotient projections.  Neither receipt component is
claimed to be unique. -/
theorem lossyProjection_forgets_beta_and_annihilators
    (left right : State region principal source Operator Payload)
    (h : left.reduced = right.reduced) :
    left.lossyProjection = right.lossyProjection :=
  lossyProjection_ignores_receipts left right h

end State

/-- An explicit bounded-representative interface.  Supplying this value is the
generic Minkowski boundary: no instance and no axiom asserts that an arbitrary
multiplicative carrier has such a reduction. -/
structure BoundedRepresentativeInterface {S : Type uS} {G : Type uG}
    [Group S] [CommGroup G] (principal : S →* G) where
  region : BoundedRegion G
  reduced : G → G
  reduced_mem : ∀ source, region.contains (reduced source)
  principalization : ∀ source,
    PrincipalizationReceipt principal source (reduced source)

namespace BoundedRepresentativeInterface

variable {S : Type uS} {G : Type uG} [Group S] [CommGroup G]
  {principal : S →* G} {Operator : Type uO} {Payload : Type uP}
  [SMul Operator Payload] [Zero Payload]

/-- Run a bounded reduction while carrying the complete input receipt list
into the output state. -/
def reduce (reduction : BoundedRepresentativeInterface principal) (source : G)
    (receipts : List (AnnihilatorReceipt Operator Payload)) :
    State reduction.region principal source Operator Payload where
  reduced := reduction.reduced source
  reduced_mem := reduction.reduced_mem source
  principalization := reduction.principalization source
  annihilatorReceipts := receipts

@[simp]
theorem reduction_emits_all_annihilator_receipts
    (reduction : BoundedRepresentativeInterface principal) (source : G)
    (receipts : List (AnnihilatorReceipt Operator Payload)) :
    (reduction.reduce source receipts).annihilatorReceipts = receipts :=
  rfl

/-- Reduction has no silent discard: its emitted scalar reconstructs the
source from the emitted bounded representative. -/
theorem reduction_no_silent_discard
    (reduction : BoundedRepresentativeInterface principal) (source : G)
    (receipts : List (AnnihilatorReceipt Operator Payload)) :
    source = principal (reduction.reduce source receipts).beta *
      (reduction.reduce source receipts).reduced :=
  (reduction.reduce source receipts).source_eq_principal_mul_reduced

end BoundedRepresentativeInterface

/-! ## Quotients and ideal class groups -/

variable {S : Type uS} {G : Type uG} [Group S] [CommGroup G]

/-- Equality in the quotient by principal elements emits an explicit
principalization receipt. -/
theorem exists_principalizationReceipt_of_same_quotient
    (principal : S →* G) {source reduced : G}
    (h : QuotientGroup.mk' principal.range reduced =
      QuotientGroup.mk' principal.range source) :
    Nonempty (PrincipalizationReceipt principal source reduced) := by
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, ⟨beta, rfl⟩, hz⟩ := h
  exact ⟨⟨beta, by simpa only [mul_comm] using hz.symm⟩⟩

section IdealClass

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Equal ideal classes emit the missing scalar as a principalization
receipt, after transporting the equality through Mathlib's quotient
description of `ClassGroup`. -/
theorem exists_principalizationReceipt_of_same_class
    {source reduced : (FractionalIdeal R⁰ K)ˣ}
    (h : ClassGroup.mk K reduced = ClassGroup.mk K source) :
    Nonempty (PrincipalizationReceipt (toPrincipalIdeal R K) source reduced) := by
  apply exists_principalizationReceipt_of_same_quotient (toPrincipalIdeal R K)
  have hq := congrArg (ClassGroup.equiv K) h
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_mulEquiv_refl] at hq
  have hmap (I : (FractionalIdeal R⁰ K)ˣ) :
      Units.mapEquiv (MulEquiv.refl (FractionalIdeal R⁰ K)) I = I := by
    apply Units.ext
    rfl
  rw [hmap reduced, hmap source] at hq
  exact hq

variable {Operator : Type uO} {Payload : Type uP}
  [SMul Operator Payload] [Zero Payload]
  {region : BoundedRegion ((FractionalIdeal R⁰ K)ˣ)}
  {source : (FractionalIdeal R⁰ K)ˣ}

/-- The actual ideal-class projection of a receipted state. -/
noncomputable def idealClassProjection
    (state : State region (toPrincipalIdeal R K) source Operator Payload) :
    ClassGroup R :=
  ClassGroup.mk K state.reduced

/-- The projected class is the source ideal's class; the proof necessarily
uses the retained principalization receipt. -/
theorem idealClassProjection_eq_source_class
    (state : State region (toPrincipalIdeal R K) source Operator Payload) :
    idealClassProjection state = ClassGroup.mk K source := by
  change ClassGroup.mk K state.reduced = ClassGroup.mk K source
  have hprincipal :
      ClassGroup.mk K (toPrincipalIdeal R K state.beta) = 1 := by
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
    exact ⟨(state.beta : K), coe_toPrincipalIdeal state.beta⟩
  have hsource := congrArg (ClassGroup.mk K)
    state.source_eq_principal_mul_reduced
  rw [map_mul, hprincipal, one_mul] at hsource
  exact hsource.symm

/-- The actual class-group projection needs no equality of principalization
scalars or annihilator receipt lists once the reduced ideal is fixed. -/
theorem idealClassProjection_forgets_beta_and_annihilators
    (left right : State region (toPrincipalIdeal R K) source Operator Payload)
    (h : left.reduced = right.reduced) :
    idealClassProjection left = idealClassProjection right := by
  change ClassGroup.mk K left.reduced = ClassGroup.mk K right.reduced
  rw [h]

/-- Under Mathlib's canonical equivalence, the ideal class group projection is
literally `State.lossyProjection`.  Thus the class group is precisely the
lossy quotient of the receipted carrier, not the carrier itself. -/
theorem classGroup_is_lossy_projection
    (state : State region (toPrincipalIdeal R K) source Operator Payload) :
    ClassGroup.equiv K (idealClassProjection state) = state.lossyProjection := by
  change ClassGroup.equiv K (ClassGroup.mk K state.reduced) =
    QuotientGroup.mk' (toPrincipalIdeal R K).range state.reduced
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    RingEquiv.coe_mulEquiv_refl]
  congr 1

end IdealClass

/-! ## The number-field Minkowski implementation -/

open Module NumberField NumberField.InfinitePlace

/-- The classical Minkowski class bound used by
`NumberField.exists_ideal_in_class_of_norm_le`. -/
noncomputable def minkowskiClassBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ nrComplexPlaces K *
    (((Module.finrank ℚ K).factorial : ℝ) /
      (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
        Real.sqrt |(NumberField.discr K : ℝ)|)

/-- The bounded region of integral ideal representatives whose absolute norm
is at most the classical Minkowski class bound. -/
def numberFieldMinkowskiRegion (K : Type*) [Field K] [NumberField K] :
    BoundedRegion ((FractionalIdeal (𝓞 K)⁰ K)ˣ) where
  contains I := ∃ J : (Ideal (𝓞 K))⁰,
    I = FractionalIdeal.mk0 K J ∧
      (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ≤ minkowskiClassBound K

/-- A noncomputably chosen integral ideal in the source class and under the
Minkowski bound. -/
noncomputable def minkowskiIdealRepresentative
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (Ideal (𝓞 K))⁰ :=
  Classical.choose
    (NumberField.exists_ideal_in_class_of_norm_le (ClassGroup.mk K source))

/-- The chosen integral ideal represents the source class. -/
theorem minkowskiIdealRepresentative_class
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk0 (minkowskiIdealRepresentative K source) =
      ClassGroup.mk K source :=
  (Classical.choose_spec
    (NumberField.exists_ideal_in_class_of_norm_le (ClassGroup.mk K source))).1

/-- The chosen integral representative satisfies the actual Mathlib
Minkowski norm bound. -/
theorem minkowskiIdealRepresentative_norm_le
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (Ideal.absNorm (minkowskiIdealRepresentative K source : Ideal (𝓞 K)) : ℝ) ≤
      minkowskiClassBound K := by
  simpa only [minkowskiClassBound, minkowskiIdealRepresentative] using
    (Classical.choose_spec
      (NumberField.exists_ideal_in_class_of_norm_le
        (ClassGroup.mk K source))).2

/-- The bounded integral ideal, regarded as an invertible fractional ideal. -/
noncomputable def numberFieldReduced
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K (minkowskiIdealRepresentative K source)

theorem numberFieldReduced_mem
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (numberFieldMinkowskiRegion K).contains (numberFieldReduced K source) := by
  exact ⟨minkowskiIdealRepresentative K source, rfl,
    minkowskiIdealRepresentative_norm_le K source⟩

/-- The reduced ideal and the source have the same ideal class. -/
theorem numberFieldReduced_same_class
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K (numberFieldReduced K source) = ClassGroup.mk K source := by
  rw [numberFieldReduced, ClassGroup.mk_mk0]
  exact minkowskiIdealRepresentative_class K source

/-- The concrete principalization receipt extracted from equality of the
source and reduced ideal classes. -/
noncomputable def numberFieldPrincipalizationReceipt
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    PrincipalizationReceipt (toPrincipalIdeal (𝓞 K) K) source
      (numberFieldReduced K source) :=
  Classical.choice
    (exists_principalizationReceipt_of_same_class
      (numberFieldReduced_same_class K source))

/-- The scalar retained by the concrete number-field reduction.  No
uniqueness is asserted. -/
noncomputable def numberFieldBeta
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Kˣ :=
  (numberFieldPrincipalizationReceipt K source).beta

/-- The concrete source ideal is reconstructed exactly from the chosen
Minkowski representative and the emitted principal scalar. -/
theorem numberField_source_eq_principal_mul_reduced
    (K : Type*) [Field K] [NumberField K]
    (source : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    source = toPrincipalIdeal (𝓞 K) K (numberFieldBeta K source) *
      numberFieldReduced K source :=
  (numberFieldPrincipalizationReceipt K source).source_eq

/-- Mathlib's class-number Minkowski theorem closes the bounded-representative
interface for rings of integers in number fields.  The choice is
noncomputable, but every choice is accompanied by its exact scalar receipt. -/
noncomputable def numberFieldBoundedRepresentative
    (K : Type*) [Field K] [NumberField K] :
    BoundedRepresentativeInterface (toPrincipalIdeal (𝓞 K) K) where
  region := numberFieldMinkowskiRegion K
  reduced := numberFieldReduced K
  reduced_mem := numberFieldReduced_mem K
  principalization := numberFieldPrincipalizationReceipt K

end Fermat.Conservation.ClassCarrier
