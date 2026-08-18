/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz, Codex

# The rational 827 source in the relaxed 59-Selmer carrier

The rational auxiliary prime 827 itself gives a concrete Kummer class whose
valuation is `-1` at every place above 827 and zero away from those places.
It therefore belongs to the carrier relaxed at the complete 827-support and
is nonzero there.

Because 827 is rational, every cyclotomic automorphism fixes this class.  It
is consequently a source in the **trivial** character eigenspace.  The final
theorem below deliberately requires
`reflectedCharacter omega chi = 1` before seating the source in a reflected
eigenspace.  Thus this module does not produce a source for an arbitrary
reflected character, does not prove class-group silence, and does not
construct a reflected localization lift.

No arithmetic provider, splitting datum, or new premise is introduced.
-/
import Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59

open scoped MonoidAlgebra nonZeroDivisors NumberField Pointwise

noncomputable section

namespace Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827

open Fermat.Conservation
open Fermat.Conservation.SelmerEigenspace
open Fermat.FiftyNine.Conservation.Credit
open Fermat.FiftyNine.Conservation.DetectorWitness827
open Fermat.FiftyNine.Conservation.SplitPrimeFourier827
open Fermat.FiftyNine.Conservation.CyclotomicSelmerAction59

local instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime Credit.attestationPrime) :=
  ⟨Credit.attestationPrime_isPrime⟩

set_option maxHeartbeats 800000
set_option maxRecDepth 2000

universe uK

variable (K : Type uK) [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

/-- The rational auxiliary prime 827, viewed as a nonzero field unit. -/
def attestationPrimeFieldUnit827 : Kˣ :=
  Units.mk0 (Credit.attestationPrime : K) (by
    norm_num [Credit.attestationPrime])

/-- At every place over 827, the normalized valuation of the rational
auxiliary prime is `-1`.  The sign follows Mathlib's multiplicative
height-one-valuation convention. -/
theorem attestationPrime_valuation_toAdd_eq_neg_one
    (place : Place827 K) :
    (place.1.valuationOfNeZero
      (attestationPrimeFieldUnit827 K)).toAdd = -1 := by
  apply congrArg Multiplicative.toAdd
  rw [← WithZero.coe_inj, place.1.valuationOfNeZero_eq]
  change place.1.valuation K (Credit.attestationPrime : K) =
    WithZero.exp (-1 : ℤ)
  rw [show (Credit.attestationPrime : K) =
      algebraMap (NumberField.RingOfIntegers K) K
        (Credit.attestationPrime : NumberField.RingOfIntegers K) by norm_num]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [place.1.intValuation_eq_exp_neg_multiplicity (by
    norm_num [Credit.attestationPrime])]
  congr 2
  norm_cast
  haveI : place.1.asIdeal.IsPrime := place.1.isPrime
  haveI : place.1.asIdeal.LiesOver
      (Ideal.span {(Credit.attestationPrime : ℤ)}) :=
    Ideal.LiesOver.mk place.2
  have hspan : Ideal.map
      (algebraMap ℤ (NumberField.RingOfIntegers K)) rationalPrimeIdeal827 =
      Ideal.span
        {(Credit.attestationPrime : NumberField.RingOfIntegers K)} := by
    simp [rationalPrimeIdeal827, Ideal.map_span]
  rw [← hspan]
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity]
  · exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
      Credit.attestationPrime K place.1.asIdeal
        attestationPrime_not_dvd_fiftyNine
  · simpa [rationalPrimeIdeal827, Ideal.map_span] using
      (Ideal.map_ne_bot_of_ne_bot
        (R := ℤ) (S := NumberField.RingOfIntegers K)
        rationalPrimeIdeal827_ne_bot)
  · exact place.1.isPrime

omit [IsCyclotomicExtension {59} ℚ K] in
/-- Away from the complete set of places over 827, the rational auxiliary
prime has zero normalized valuation.  This statement does not use the
cyclotomic-field hypothesis. -/
theorem attestationPrime_valuation_toAdd_eq_zero_of_not_mem
    (v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers K))
    (hv : v ∉ placesOver827 K) :
    (v.valuationOfNeZero
      (attestationPrimeFieldUnit827 K)).toAdd = 0 := by
  have hzero :
      (v.valuationOfNeZero
        (attestationPrimeFieldUnit827 K)).toAdd = 0 ↔
        v.valuation K (attestationPrimeFieldUnit827 K) = 1 := by
    rw [← v.valuationOfNeZero_eq (attestationPrimeFieldUnit827 K),
      ← WithZero.coe_one, WithZero.coe_inj]
    rfl
  apply hzero.mpr
  change v.valuation K (Credit.attestationPrime : K) = 1
  rw [show (Credit.attestationPrime : K) =
      algebraMap (NumberField.RingOfIntegers K) K
        (Credit.attestationPrime : NumberField.RingOfIntegers K) by norm_num]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [v.intValuation_eq_one_iff]
  intro hmem
  apply hv
  change Ideal.span ({(Credit.attestationPrime : ℤ)} : Set ℤ) =
    v.asIdeal.under ℤ
  apply Ideal.IsMaximal.eq_of_le
    (Int.ideal_span_isMaximal_of_prime Credit.attestationPrime)
    Ideal.IsPrime.ne_top'
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  simpa using hmem

/-- The rational auxiliary prime gives a literal element of the 59-Selmer
carrier relaxed at all places over 827. -/
noncomputable def attestationPrimeSource827 :
    QRelaxedSelmerCarrier827 K :=
  Additive.ofMul ⟨
    QuotientGroup.mk (attestationPrimeFieldUnit827 K), by
      intro v hv
      apply (valuationOfNeZeroMod_mk_eq_one_iff_dvd v
        (attestationPrimeFieldUnit827 K)).mpr
      rw [attestationPrime_valuation_toAdd_eq_zero_of_not_mem K v hv]
      exact dvd_zero 59⟩

/-- Every canonical cyclotomic automorphism fixes the rational 827 source.
This is the precise sense in which the construction belongs to the trivial
character mode. -/
theorem cyclotomicQRelaxedSelmerRepresentation827_attestationPrimeSource
    (sigma : GaloisIndex59) :
    cyclotomicQRelaxedSelmerRepresentation827 K sigma
        (attestationPrimeSource827 K) =
      attestationPrimeSource827 K := by
  apply Additive.toMul.injective
  apply Subtype.ext
  calc
    cyclotomicKummerHom59 K sigma
        (QuotientGroup.mk (attestationPrimeFieldUnit827 K)) =
      QuotientGroup.mk
          (cyclotomicUnitEquiv59 K sigma
            (attestationPrimeFieldUnit827 K)) :=
        cyclotomicKummerHom59_mk K sigma
          (attestationPrimeFieldUnit827 K)
    _ = QuotientGroup.mk (attestationPrimeFieldUnit827 K) := by
      congr 1
      apply Units.ext
      change KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K sigma
          (Credit.attestationPrime : K) = Credit.attestationPrime
      exact map_natCast
        (KummerCriterion.cyclotomicSigmaOfUnit (p := 59) K sigma)
        Credit.attestationPrime

/-- The relaxed source is genuinely nonzero.  Its valuation at any chosen
place over 827 is `-1`, which is not divisible by 59. -/
theorem attestationPrimeSource827_ne_zero
    (place : Place827 K) :
    attestationPrimeSource827 K ≠ 0 := by
  intro hzero
  have hquotient :
      (QuotientGroup.mk (attestationPrimeFieldUnit827 K) :
          Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) = 1 := by
    have := congrArg (fun source : QRelaxedSelmerCarrier827 K =>
      (Additive.toMul source).1) hzero
    simpa [attestationPrimeSource827] using this
  have hmod :
      place.1.valuationOfNeZeroMod 59
          (QuotientGroup.mk (attestationPrimeFieldUnit827 K) :
            Kˣ ⧸ (powMonoidHom 59 : Kˣ →* Kˣ).range) = 1 := by
    rw [hquotient]
    exact map_one _
  have hdvd : (59 : ℤ) ∣
      (place.1.valuationOfNeZero
        (attestationPrimeFieldUnit827 K)).toAdd :=
    (valuationOfNeZeroMod_mk_eq_one_iff_dvd place.1
      (attestationPrimeFieldUnit827 K)).mp hmod
  rw [attestationPrime_valuation_toAdd_eq_neg_one K place] at hdvd
  norm_num at hdvd

/-- The rational 827 source is seated in the literal trivial-character
eigenspace of the canonical relaxed action. -/
theorem attestationPrimeSource827_mem_trivial_characterEigenspace :
    attestationPrimeSource827 K ∈
      characterEigenspaceAt
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        (1 : InvolutiveBase.Character (PadicInt 59) GaloisIndex59) := by
  rw [mem_characterEigenspaceAt_iff]
  intro sigma
  rw [cyclotomicQRelaxedSelmerRepresentation827_attestationPrimeSource]
  simp

/-- The only reflected seating exported by this module is guarded by the
explicit assertion that the reflected character is trivial.  In particular,
this theorem cannot be instantiated for arbitrary `omega` and `chi`. -/
theorem attestationPrimeSource827_mem_reflectedCharacter_of_eq_one
    (omega chi : InvolutiveBase.Character (PadicInt 59) GaloisIndex59)
    (hreflected : InvolutiveBase.reflectedCharacter omega chi = 1) :
    attestationPrimeSource827 K ∈
      characterEigenspaceAt
        (cyclotomicQRelaxedSelmerRepresentation827 K)
        (InvolutiveBase.reflectedCharacter omega chi) := by
  rw [hreflected]
  exact attestationPrimeSource827_mem_trivial_characterEigenspace K

end Fermat.FiftyNine.Conservation.RationalAttestationPrimeSource827
