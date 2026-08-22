import Fermat.Descent.GenericIrregular.ChannelCertificate
import Fermat.Descent.GenericIrregular.LemmaTwo
import Fermat.Descent.Irregular.VandiverHistoricalAssemblyPrime
import Fermat.Descent.Irregular.VandiverHistoricalStartPrime
import Fermat.Descent.Irregular.VandiverRealNormalizationPrime

/-!
# Prime-generic assembly of the historical second case

This module connects the already-proved prime-generic historical descent to
the axis-8 finite channel certificate.  The plus-class statement, Vandiver's
Lemma II, and finite channel data remain visibly separate inputs.

`secondCaseExcluded_of_plusClass_of_lemmaTwo_of_channels` is an intermediate
boundary, not the final fixed-exponent certificate: later modules must derive
Lemma II from its finite cyclotomic-unit and derivative data rather than store
the conclusion as a certificate field.
-/

namespace Fermat.GenericIrregular.SecondCase

open scoped NumberField

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.GenericIrregular.LemmaTwo
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime

noncomputable section

variable {K : Type} {p N : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- All fixed-prime data needed by the historical second case.

The fields are deliberately upstream mathematical certificates: plus-class
nondivisibility, a finite cyclotomic-unit/derivative system, and axis-8
Bernoulli channels.  In particular, neither `VandiverLemmaTwo` nor
`SecondCaseExcluded` is stored. -/
structure FixedSecondCaseCertificate (K : Type) (p N : ℕ)
    [Fact p.Prime] [Field K] [NumberField K]
    [NumberField.IsCMField K] [IsCyclotomicExtension {p} ℚ K] where
  plusClassNondivisibility : PlusClassNondivisibility K p
  unitSystem : LemmaTwoUnitSystem K p
  channels : FixedChannelCertificate p N

/-- The complete generic historical assembly at a fixed prime, with its
three honest mathematical inputs kept explicit. -/
theorem secondCaseExcluded_of_plusClass_of_lemmaTwo_of_channels
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hplus : PlusClassNondivisibility K p)
    (hLemmaTwo :
      Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K p)
    (channels : FixedChannelCertificate p N) :
    Fermat.SecondCaseExcluded p := by
  have hp2 : p ≠ 2 := by
    omega
  obtain ⟨r, hr⟩ :=
    (Fact.out : p.Prime).odd_of_ne_two hp2
  let normalizer :=
    Fermat.Irregular.VandiverRealNormalizationPrime.realGeneratorNormalizer
      (K := K) hr hζ
  have hroot :
      RealUnitRootNormalization hζ :=
    Fermat.Irregular.VandiverRealNormalizationPrime.realUnitRootNormalization
      (K := K) (by omega) hζ
  have heliminate :
      RealPrincipalGeneratorElimination hζ :=
    Fermat.Irregular.VandiverHistoricalAssemblyPrime.realPrincipalGeneratorElimination_of_plusClass
      (K := K) hp5 hζ hplus
  have hstart :
      SecondCaseStartsHistoricalDescent hζ
        (RealSourceAdmissible hζ) :=
    Fermat.Irregular.VandiverHistoricalStartPrime.secondCaseStartsHistoricalDescent
      (K := K) hp5 hr hζ
  have hreduce :
      EquationsSevenToTenReduction hζ
        (RealSourceAdmissible hζ) :=
    equationsSevenToTenReduction hζ normalizer hroot heliminate
  intro a b c ha hb hc hgcd hdiv
  exact
    (secondCaseExcluded_of_vandiverLemmaTwo
      hp5 hζ (RealSourceAdmissible hζ) hstart hreduce
      hLemmaTwo (channels.bernoulliCubeCondition hp5))
      ha hb hc hgcd hdiv

/-- The end-to-end generic second-case theorem from honest fixed-prime
certificate data.  Vandiver's Lemma II is derived internally from the
finite unit system. -/
theorem secondCaseExcluded_of_certificate
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (certificate : FixedSecondCaseCertificate K p N) :
    Fermat.SecondCaseExcluded p :=
  secondCaseExcluded_of_plusClass_of_lemmaTwo_of_channels
    hp5 hζ certificate.plusClassNondivisibility
    (vandiverLemmaTwo_of_unitSystem hp5 certificate.unitSystem)
    certificate.channels

end

end Fermat.GenericIrregular.SecondCase
