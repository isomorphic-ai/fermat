/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# Canonical tame contexts away from 59

At every height-one place of the 59th cyclotomic integer ring away from the
wild rational prime, this module constructs the finite residue field, the
reduction of the valuation ring, a normalized angular component, and the
resulting explicit tame-symbol context.  No residue field or angular
component is supplied by a caller.

The final theorem applies the constructed context to the actual first
circular unit and a genuine q-relaxed reflected lift.  Literal representative
support then proves that every tame reading outside the rational supports 59
and 827 is zero.  This is a local-symbol theorem only: it neither manufactures
a place-indexed global pairing nor asserts reciprocity.
-/
import Fermat.Conservation.TameSymbol
import Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
import Mathlib.NumberTheory.NumberField.Ideal.Basic

open scoped NumberField

noncomputable section

namespace Fermat.FiftyNine.Conservation.CyclotomicTameContext59

open Fermat.Conservation.TameSymbol
open Fermat.FiftyNine.Conservation.DetectorWitness827

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩

variable (K : Type*) [Field K] [NumberField K]

abbrev Place :=
  IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- The literal residue field of one height-one prime. -/
abbrev Residue (v : Place K) :=
  NumberField.RingOfIntegers K ⧸ v.asIdeal

local instance residueIdealIsMaximal (v : Place K) :
    v.asIdeal.IsMaximal :=
  v.isMaximal

local instance residueField (v : Place K) : Field (Residue K v) :=
  Ideal.Quotient.field v.asIdeal

local instance residueFintype (v : Place K) : Fintype (Residue K v) :=
  Fintype.ofFinite _

/-- The valuation ring at a height-one place. -/
abbrev LocalRing (v : Place K) :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v

/-- Reduction from the valuation ring to the literal ideal quotient. -/
noncomputable def localReductionHom (v : Place K) :
    LocalRing K v →+* Residue K v :=
  IsLocalization.lift
    (M := v.asIdeal.primeCompl)
    (S := LocalRing K v)
    (g := Ideal.Quotient.mk v.asIdeal) (fun y ↦ by
      apply isUnit_iff_ne_zero.mpr
      intro hy
      exact y.2 (Ideal.Quotient.eq_zero_iff_mem.mp hy))

theorem localReductionHom_algebraMap (v : Place K)
    (x : NumberField.RingOfIntegers K) :
    localReductionHom K v
        (algebraMap (NumberField.RingOfIntegers K) (LocalRing K v) x) =
      Ideal.Quotient.mk v.asIdeal x := by
  exact IsLocalization.lift_eq (M := v.asIdeal.primeCompl) _ x

/-- A chosen element of normalized valuation `-1`. -/
noncomputable def chosenUniformizer (v : Place K) : K :=
  Classical.choose (v.valuation_exists_uniformizer K)

theorem chosenUniformizer_spec (v : Place K) :
    v.valuation K (chosenUniformizer K v) = WithZero.exp (-1 : ℤ) :=
  Classical.choose_spec (v.valuation_exists_uniformizer K)

theorem chosenUniformizer_ne_zero (v : Place K) :
    chosenUniformizer K v ≠ 0 :=
  IsDedekindDomain.HeightOneSpectrum.valuation_uniformizer_ne_zero K v

noncomputable def chosenUniformizerUnit (v : Place K) : Kˣ :=
  Units.mk0 (chosenUniformizer K v) (chosenUniformizer_ne_zero K v)

theorem valuationOfNeZero_chosenUniformizerUnit (v : Place K) :
    v.valuationOfNeZero (chosenUniformizerUnit K v) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  apply WithZero.coe_injective
  rw [v.valuationOfNeZero_eq]
  exact chosenUniformizer_spec K v

/-- Remove the complete valuation of a nonzero field element, leaving a unit
of the valuation ring. -/
noncomputable def localUnitPart (v : Place K) :
    Kˣ →* (LocalRing K v).unitGroup where
  toFun a := ⟨a * chosenUniformizerUnit K v ^
      (v.valuationOfNeZero a).toAdd, by
    change _ ∈
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v).unitGroup
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    rw [Valuation.mem_unitGroup_iff]
    have hvunit :
        v.valuationOfNeZero
            (a * chosenUniformizerUnit K v ^
              (v.valuationOfNeZero a).toAdd) = 1 := by
      rw [map_mul, map_zpow,
        valuationOfNeZero_chosenUniformizerUnit K v]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, Int.toAdd_zpow, toAdd_ofAdd, toAdd_one]
      ring
    rw [← v.valuationOfNeZero_eq]
    exact congrArg
      ((↑) : Multiplicative ℤ → WithZero (Multiplicative ℤ)) hvunit⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    simp only [toAdd_mul]
    rw [zpow_add]
    ac_rfl

/-- The residue of the normalized unit part. -/
noncomputable def angularComponent (v : Place K) :
    Kˣ →* (Residue K v)ˣ :=
  (Units.map (localReductionHom K v)).comp
    ((LocalRing K v).unitGroupMulEquiv.toMonoidHom.comp
      (localUnitPart K v))

/-- A height-one ideal not above 59 has absolute norm coprime to 59. -/
theorem absNorm_coprime_59_of_not_over59 (v : Place K)
    (hv : v ∉ placesOver59 K) :
    (Ideal.absNorm v.asIdeal).Coprime 59 := by
  rw [Nat.coprime_comm, (by norm_num : Nat.Prime 59).coprime_iff_not_dvd]
  intro hdvd
  have hdvdZ : (59 : ℤ) ∣ (Ideal.absNorm v.asIdeal : ℤ) := by
    exact_mod_cast hdvd
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm
      (show Prime (59 : ℤ) by norm_num) v.asIdeal hdvdZ
  have heq : v.asIdeal = P :=
    v.isMaximal.eq_of_le hPmax.ne_top (Ideal.dvd_iff_le.mp hPdvd)
  apply hv
  change Ideal.span ({(59 : ℤ)} : Set ℤ) = v.asIdeal.under ℤ
  rw [heq, hPunder]

/-- The residue characteristic away from the wild support is not 59. -/
theorem residueChar_ne_59 (v : Place K)
    (hv : v ∉ placesOver59 K) : ringChar (Residue K v) ≠ 59 := by
  rw [Ideal.ringChar_quot]
  intro heq
  apply hv
  change Ideal.span ({(59 : ℤ)} : Set ℤ) = v.asIdeal.under ℤ
  rw [show (59 : ℤ) = (Ideal.absNorm (v.asIdeal.under ℤ) : ℤ) by
    exact_mod_cast heq.symm]
  exact Int.ideal_span_absNorm_eq_self (v.asIdeal.under ℤ)

section Cyclotomic

variable [IsCyclotomicExtension {59} ℚ K]

/-- Reduction preserves primitivity of the canonical cyclotomic root at
every place away from 59. -/
theorem residueRoot_isPrimitive (v : Place K)
    (hv : v ∉ placesOver59 K) :
    IsPrimitiveRoot
      (Ideal.Quotient.mk v.asIdeal
        (IsCyclotomicExtension.zeta_spec 59 ℚ K).toInteger) 59 := by
  apply IsPrimitiveRoot.idealQuotient_mk
      (IsCyclotomicExtension.zeta_spec 59 ℚ K).toInteger_isPrimitiveRoot
  · exact Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top
  · exact absNorm_coprime_59_of_not_over59 K v hv

/-- The reduced canonical root, bundled as a residue-field unit. -/
noncomputable def residueRootUnit (v : Place K)
    (hv : v ∉ placesOver59 K) : (Residue K v)ˣ :=
  ((residueRoot_isPrimitive K v hv).isUnit (by norm_num)).unit

theorem residueRootUnit_isPrimitive (v : Place K)
    (hv : v ∉ placesOver59 K) :
    IsPrimitiveRoot (residueRootUnit K v hv) 59 :=
  (residueRoot_isPrimitive K v hv).isUnit_unit (by norm_num)

/-- Existence of the reduced primitive root forces 59 to divide the order
of the residue-field unit group. -/
theorem card_sub_one_dvd_59 (v : Place K)
    (hv : v ∉ placesOver59 K) :
    59 ∣ Fintype.card (Residue K v) - 1 := by
  classical
  have h := orderOf_dvd_card (x := residueRootUnit K v hv)
  rw [← (residueRootUnit_isPrimitive K v hv).eq_orderOf] at h
  rw [← Fintype.card_units (Residue K v)]
  exact h

/-- The canonical explicit tame-symbol context at every height-one place
away from 59. -/
noncomputable def context (v : Place K)
    (hv : v ∉ placesOver59 K) : Context 59 K (Residue K v) where
  ord := MonoidHom.toAdditive v.valuationOfNeZero
  angularComponent := angularComponent K v
  residueChar_ne := residueChar_ne_59 K v hv
  card_sub_one_dvd := card_sub_one_dvd_59 K v hv
  primitiveRoot := residueRootUnit K v hv
  primitiveRoot_spec := residueRootUnit_isPrimitive K v hv

@[simp]
theorem context_ord (v : Place K) (hv : v ∉ placesOver59 K) (a : Kˣ) :
    (context K v hv).ord (Additive.ofMul a) =
      (v.valuationOfNeZero a).toAdd :=
  rfl

section SupportedRepresentative

open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827

variable [Invertible (Fintype.card GaloisIndex59 : PadicInt 59)]
  (omega chi : Fermat.Conservation.InvolutiveBase.Character
    (PadicInt 59) GaloisIndex59)

abbrev rhoQ827 := cyclotomicQRelaxedSelmerRepresentation827 K

/-- **Actual outside-support tame silence.**  For the first circular unit
and any genuine q-relaxed reflected lift, the canonical tame symbol is zero
at every height-one place outside the rational supports 59 and 827. -/
theorem value_firstGenerated_candidate_eq_zero_outside_support
    (lift : ReflectedQRelaxedLocalizationLift827
      (rhoQ827 K) omega chi)
    (v : Place K) (hp : v ∉ placesOver59 K)
    (hq : v ∉ placesOver827 K) :
    (context K v hp).value
        (ReflectedQRelaxedLocalizationLift827.primalRepresentative
          (IsCyclotomicExtension.zeta_spec 59 ℚ K))
        lift.candidateRepresentative = 0 := by
  exact lift.outside_reading_eq_zero_of_both_units
    (IsCyclotomicExtension.zeta_spec 59 ℚ K) v (context K v hp)
    (context_ord K v hp) hp hq

end SupportedRepresentative

end Cyclotomic

end Fermat.FiftyNine.Conservation.CyclotomicTameContext59
