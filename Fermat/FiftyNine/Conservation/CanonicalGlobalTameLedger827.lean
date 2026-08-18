/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Canonically oriented tame ledger at 827

The computational 827 ledger uses one fixed primitive root in every residue
field. Global Hilbert reciprocity instead requires the reduction of one
fixed global cyclotomic root at every place. This file proves the exact
coordinate change between those conventions and constructs the resulting
genuine finite tame ledger.

At canonical orbit coordinate tau, the globally oriented value is tau times
the fixed-root value. Consequently its total is a weighted, not an
unweighted, Fourier sum. This module proves only that exact normalization
and support statement; it does not assume or package global reciprocity.
-/
import Fermat.Conservation.TameSymbolTransport
import Fermat.Conservation.FiniteOrbitLedger
import Fermat.FiftyNine.Conservation.ActualTameLedger827

open scoped BigOperators NumberField

noncomputable section
set_option maxRecDepth 10000

namespace Fermat.FiftyNine.Conservation.CanonicalTameLedger827

open Fermat.Conservation
open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.ActualTameLedger827
open Fermat.FiftyNine.Conservation.CyclotomicTameContext59
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.ExplicitTameOrbitReciprocity827
open Fermat.FiftyNine.Conservation.LocalReduction827
open Fermat.FiftyNine.Conservation.OrbitPlace827
open Fermat.FiftyNine.Conservation.PrimalOrbitResidue827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance residueIdealIsMaximal
    (v : Place K) : v.asIdeal.IsMaximal := v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

noncomputable def orbitResidueEquiv827
    (sigma : GaloisIndex59) :
    Residue K
        (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma) ≃+*
      ZMod Credit.attestationPrime :=
  RingHom.quotientKerEquivOfSurjective
    (orbitReductionHom827_surjective
      (canonicalZeta59_isPrimitive (K := K)) sigma)

theorem orbitPlace827_not_mem_placesOver59
    (sigma : GaloisIndex59) :
    orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma ∉
      placesOver59 K := by
  intro h59
  have heq : Ideal.span ({(59 : ℤ)} : Set ℤ) =
      Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) :=
    h59.trans
      (orbitPlace827_under_int
        (canonicalZeta59_isPrimitive (K := K)) sigma)
  have hmem : (59 : ℤ) ∈
      Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) := by
    rw [← heq]
    exact Ideal.subset_span (by simp)
  rw [Ideal.mem_span_singleton] at hmem
  norm_num [Credit.attestationPrime] at hmem

@[simp]
theorem orbitResidueEquiv827_mk
    (sigma : GaloisIndex59) (x : NumberField.RingOfIntegers K) :
    orbitResidueEquiv827 (K := K) sigma
        (Ideal.Quotient.mk
          (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma).asIdeal x) =
      orbitReductionHom827 (canonicalZeta59_isPrimitive (K := K)) sigma x := by
  change (RingHom.quotientKerEquivOfSurjective
      (orbitReductionHom827_surjective
        (canonicalZeta59_isPrimitive (K := K)) sigma))
      (Ideal.Quotient.mk
        (RingHom.ker (orbitReductionHom827
          (canonicalZeta59_isPrimitive (K := K)) sigma)) x) = _
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ _

theorem orbitResidueEquiv827_localReductionHom
    (sigma : GaloisIndex59) :
    (orbitResidueEquiv827 (K := K) sigma).toRingHom.comp
        (localReductionHom K
          (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)) =
      localReductionHom827 (canonicalZeta59_isPrimitive (K := K)) sigma := by
  apply IsLocalization.ringHom_ext
    (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma).asIdeal.primeCompl
  apply RingHom.ext
  intro x
  change orbitResidueEquiv827 (K := K) sigma
      (localReductionHom K
        (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)
        (algebraMap (NumberField.RingOfIntegers K)
          (LocalRing K
            (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)) x)) =
    localReductionHom827 (canonicalZeta59_isPrimitive (K := K)) sigma
      (algebraMap (NumberField.RingOfIntegers K)
        (LocalRing K
          (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)) x)
  rw [localReductionHom_algebraMap,
    localReductionHom827_algebraMap, orbitResidueEquiv827_mk]

theorem orbitResidueEquiv827_angularComponent
    (sigma : GaloisIndex59) (a : Kˣ) :
    angularComponent827 (canonicalZeta59_isPrimitive (K := K)) sigma a =
      Units.map (orbitResidueEquiv827 (K := K) sigma).toRingHom
        (angularComponent K
          (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma) a) := by
  unfold angularComponent827 angularComponent
  simp only [MonoidHom.comp_apply]
  have hpart :
      localUnitPart827 (canonicalZeta59_isPrimitive (K := K)) sigma a =
        localUnitPart K
          (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma) a := by
    rfl
  rw [hpart]
  change Units.map
      (localReductionHom827
        (canonicalZeta59_isPrimitive (K := K)) sigma).toMonoidHom _ =
    ((Units.map (orbitResidueEquiv827 (K := K) sigma).toMonoidHom).comp
      (Units.map (localReductionHom K
        (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)).toMonoidHom)) _
  rw [← Units.map_comp]
  have hred :
      (orbitResidueEquiv827 (K := K) sigma).toMonoidHom.comp
          (localReductionHom K
            (orbitPlace827
              (canonicalZeta59_isPrimitive (K := K)) sigma)).toMonoidHom =
        (localReductionHom827
          (canonicalZeta59_isPrimitive (K := K)) sigma).toMonoidHom :=
    congrArg RingHom.toMonoidHom
      (orbitResidueEquiv827_localReductionHom (K := K) sigma)
  rw [hred]

theorem orbitResidueEquiv827_residueRootUnit
    (sigma : GaloisIndex59) :
    Units.map (orbitResidueEquiv827 (K := K) sigma).toRingHom
        (residueRootUnit K
          (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)
          (orbitPlace827_not_mem_placesOver59 (K := K) sigma)) =
      CapacityCertificate.attestationRootUnit ^
        (sigma : ZMod 59).val := by
  apply Units.ext
  change orbitResidueEquiv827 (K := K) sigma
      (residueRootUnit K
        (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)
        (orbitPlace827_not_mem_placesOver59 (K := K) sigma) :
          Residue K
            (orbitPlace827
              (canonicalZeta59_isPrimitive (K := K)) sigma)) = _
  rw [show (residueRootUnit K
      (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)
      (orbitPlace827_not_mem_placesOver59 (K := K) sigma) :
        Residue K
          (orbitPlace827
            (canonicalZeta59_isPrimitive (K := K)) sigma)) =
      Ideal.Quotient.mk
        (orbitPlace827
          (canonicalZeta59_isPrimitive (K := K)) sigma).asIdeal
        (canonicalZeta59_isPrimitive (K := K)).toInteger by
    exact ((residueRoot_isPrimitive K
      (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)
      (orbitPlace827_not_mem_placesOver59 (K := K) sigma)).isUnit
        (by norm_num)).unit_spec]
  rw [orbitResidueEquiv827_mk, orbitReductionHom827_zeta]
  rfl

/-- The explicit 827 context oriented by the reduction of the global
cyclotomic root rather than by the fixed first attestation root. -/
noncomputable def canonicalOrbitTameContext827
    (sigma : GaloisIndex59) :
    TameSymbol.Context 59 K (ZMod Credit.attestationPrime) where
  ord := MonoidHom.toAdditive
    (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma).valuationOfNeZero
  angularComponent :=
    angularComponent827 (canonicalZeta59_isPrimitive (K := K)) sigma
  residueChar_ne := by
    rw [ZMod.ringChar_zmod_n]
    norm_num [Credit.attestationPrime]
  card_sub_one_dvd := by norm_num [Credit.attestationPrime]
  primitiveRoot := CapacityCertificate.attestationRootUnit ^
    (sigma : ZMod 59).val
  primitiveRoot_spec :=
    attestationRootUnit_isPrimitive_public.pow_of_coprime
      (sigma : ZMod 59).val (ZMod.val_coe_unit_coprime sigma)

/-- Under the first-isomorphism identification of the literal residue field
with `ZMod 827`, the canonical all-tame-place context gives exactly the
globally oriented orbit context. -/
theorem canonicalOrbitTameContext827_value_eq_context
    (sigma : GaloisIndex59) (a b : Kˣ) :
    (canonicalOrbitTameContext827 (K := K) sigma).value a b =
      (context K
        (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)
        (orbitPlace827_not_mem_placesOver59 (K := K) sigma)).value a b := by
  apply TameSymbol.Context.value_eq_of_residue_equiv
    (context K
      (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)
      (orbitPlace827_not_mem_placesOver59 (K := K) sigma))
    (orbitResidueEquiv827 (K := K) sigma)
    (canonicalOrbitTameContext827 (K := K) sigma)
  · rfl
  · intro x
    exact orbitResidueEquiv827_angularComponent (K := K) sigma x
  · exact orbitResidueEquiv827_residueRootUnit (K := K) sigma

/-- The fixed-root Fourier context differs from the globally oriented
context by exactly the Galois index `sigma`. -/
theorem tameContext827_value_eq_sigma_mul_canonical
    (sigma : GaloisIndex59) (a b : Kˣ) :
    (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) sigma).value a b =
      (sigma : ZMod 59) *
        (canonicalOrbitTameContext827 (K := K) sigma).value a b := by
  symm
  simpa only [ZMod.natCast_zmod_val] using
    (TameSymbol.Context.value_primitiveRoot_pow
      (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) sigma)
      (canonicalOrbitTameContext827 (K := K) sigma)
      (sigma : ZMod 59).val rfl rfl rfl a b)

/-- Exact comparison with the canonical tame symbol in the literal residue
field at the height-one place: the old fixed-root value is `sigma` times the
global-root coordinate. -/
theorem tameContext827_value_eq_sigma_mul_context
    (sigma : GaloisIndex59) (a b : Kˣ) :
    (tameContext827
        (hZeta := canonicalZeta59_isPrimitive (K := K)) sigma).value a b =
      (sigma : ZMod 59) *
        (context K
          (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) sigma)
          (orbitPlace827_not_mem_placesOver59 (K := K) sigma)).value a b := by
  rw [tameContext827_value_eq_sigma_mul_canonical,
    canonicalOrbitTameContext827_value_eq_context]

theorem tameOrbitPlace827_eq_orbitPlace_inv
    (tau : GaloisIndex59) :
    tameOrbitPlace827 (K := K) tau =
      orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) tau⁻¹ := by
  exact congrArg Subtype.val
    (indexedPlaceOrbitEquiv827_eq_orbitPlace827Subtype_inv
      (K := K) tau)

theorem tameOrbitPlace827_not_mem_placesOver59
    (tau : GaloisIndex59) :
    tameOrbitPlace827 (K := K) tau ∉ placesOver59 K := by
  rw [tameOrbitPlace827_eq_orbitPlace_inv (K := K) tau]
  exact orbitPlace827_not_mem_placesOver59 (K := K) tau⁻¹

private theorem context_value_eq_of_place_eq
    {v w : Place K} (h : v = w)
    (hv : v ∉ placesOver59 K) (hw : w ∉ placesOver59 K)
    (a b : Kˣ) :
    (context K v hv).value a b = (context K w hw).value a b := by
  subst w
  rfl

section Ledger

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)

/-- The genuine tame Hilbert-symbol value at canonical place coordinate
`tau`, using the reduction of the one global cyclotomic root as coordinate. -/
noncomputable def canonicalTameOrbitValue827
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) : ZMod 59 :=
  (context K
      (orbitPlace827 (canonicalZeta59_isPrimitive (K := K)) tau⁻¹)
      (orbitPlace827_not_mem_placesOver59 (K := K) tau⁻¹)).value
    (ReflectedQRelaxedLocalizationLift827.primalRepresentative
      (canonicalZeta59_isPrimitive (K := K)))
    lift.candidateRepresentative

/-- Readback at the literal place used to seat the orbit coordinate. -/
theorem canonicalTameOrbitValue827_eq_context_at_place
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) :
    canonicalTameOrbitValue827 (K := K) omega chi lift tau =
      (context K (tameOrbitPlace827 (K := K) tau)
        (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)).value
        (ReflectedQRelaxedLocalizationLift827.primalRepresentative
          (canonicalZeta59_isPrimitive (K := K)))
        lift.candidateRepresentative := by
  exact context_value_eq_of_place_eq
    (tameOrbitPlace827_eq_orbitPlace_inv (K := K) tau).symm
    (orbitPlace827_not_mem_placesOver59 (K := K) tau⁻¹)
    (tameOrbitPlace827_not_mem_placesOver59 (K := K) tau)
    _ _

/-- Exact normalization receipt at canonical place index `tau`: the old
fixed-root Fourier value is `tau⁻¹` times the global-root value. -/
theorem actualTameOrbitValue827_eq_inv_mul_canonical
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) :
    actualTameOrbitValue827 (K := K) omega chi lift tau =
      (tau⁻¹ : ZMod 59) *
        canonicalTameOrbitValue827 (K := K) omega chi lift tau := by
  rw [actualTameOrbitValue827, canonicalTameOrbitValue827,
    ReflectedQRelaxedLocalizationLift827.primalRepresentative]
  simpa only [Units.val_inv_eq_inv_val] using
    (tameContext827_value_eq_sigma_mul_context
      (K := K) tau⁻¹
      (Units.map (algebraMap (NumberField.RingOfIntegers K) K)
        (Credit.generatedUnit (canonicalZeta59_isPrimitive (K := K))
          DetectorWitness827.firstLedgerNode :
            (NumberField.RingOfIntegers K)ˣ))
      lift.candidateRepresentative)

/-- Equivalently, the genuine global-root value is `tau` times the fixed-root
Fourier value. -/
theorem canonicalTameOrbitValue827_eq_mul_actual
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) :
    canonicalTameOrbitValue827 (K := K) omega chi lift tau =
      (tau : ZMod 59) *
        actualTameOrbitValue827 (K := K) omega chi lift tau := by
  rw [actualTameOrbitValue827_eq_inv_mul_canonical
    (K := K) omega chi lift tau]
  have hunit : (tau : ZMod 59) * (tau⁻¹ : ZMod 59) = 1 := by
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one] using
      congrArg Units.val (mul_inv_cancel tau)
  rw [← mul_assoc, hunit, one_mul]

/-- The globally normalized finite tame ledger, seated on the same genuine
height-one places as the fixed-root computational ledger. -/
noncomputable def canonicalTameLedger827
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi) :
    Place K →₀ ZMod 59 :=
  FiniteOrbitLedger.orbitLedger
    (tameOrbitPlace827 (K := K))
    (canonicalTameOrbitValue827 (K := K) omega chi lift)

@[simp]
theorem canonicalTameLedger827_apply_orbit
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi)
    (tau : GaloisIndex59) :
    canonicalTameLedger827 (K := K) omega chi lift
        (tameOrbitPlace827 (K := K) tau) =
      canonicalTameOrbitValue827 (K := K) omega chi lift tau := by
  exact FiniteOrbitLedger.orbitLedger_apply
    (tameOrbitPlace827 (K := K))
    (canonicalTameOrbitValue827 (K := K) omega chi lift)
    (tameOrbitPlace827_injective (K := K)) tau

/-- Every canonical ledger row outside the actual set of places over 827 is
zero. -/
theorem canonicalTameLedger827_apply_eq_zero_of_not_over827
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi)
    (v : Place K) (hv : v ∉ placesOver827 K) :
    canonicalTameLedger827 (K := K) omega chi lift v = 0 := by
  apply FiniteOrbitLedger.orbitLedger_apply_eq_zero_of_not_mem_range
  rintro ⟨tau, rfl⟩
  exact hv ((indexedPlaceOrbitEquiv827 K
    (tameOrbitBasePlace827 (K := K)) tau).2)

/-- At every omitted nonwild place, the canonical local Hilbert symbol is
exactly the zero entry of the globally normalized ledger. -/
theorem canonicalTameValue_eq_canonicalLedger_of_outside_support
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi)
    (v : Place K) (hp : v ∉ placesOver59 K)
    (hq : v ∉ placesOver827 K) :
    (context K v hp).value
        (ReflectedQRelaxedLocalizationLift827.primalRepresentative
          (canonicalZeta59_isPrimitive (K := K)))
        lift.candidateRepresentative =
      canonicalTameLedger827 (K := K) omega chi lift v := by
  rw [CyclotomicTameContext59.value_firstGenerated_candidate_eq_zero_outside_support
      K omega chi lift v hp hq,
    canonicalTameLedger827_apply_eq_zero_of_not_over827
      (K := K) omega chi lift v hq]

/-- Aggregating the globally normalized ledger gives the weighted fixed-root
orbit sum.  The `tau` factor is forced by the global primitive-root
normalization and must be present before invoking reciprocity. -/
theorem canonicalTameLedger827_sum_eq_weighted_actual
    (lift : ReflectedQRelaxedLocalizationLift827
      (LocalReduction827.rhoQ827 (K := K)) omega chi) :
    (canonicalTameLedger827 (K := K) omega chi lift).sum
        (fun _ value ↦ value) =
      ∑ tau : GaloisIndex59, (tau : ZMod 59) *
        actualTameOrbitValue827 (K := K) omega chi lift tau := by
  rw [canonicalTameLedger827, FiniteOrbitLedger.orbitLedger_sum]
  apply Finset.sum_congr rfl
  intro tau _
  exact canonicalTameOrbitValue827_eq_mul_actual
    (K := K) omega chi lift tau

end Ledger

end Fermat.FiftyNine.Conservation.CanonicalTameLedger827
