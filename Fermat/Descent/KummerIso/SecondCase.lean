import Fermat.Descent.GenericIrregular.SecondCase
import Fermat.Descent.KummerIso.Principalization
import Fermat.Descent.KummerIso.UnitExtraction

/-!
# Historical second case through the Kummer correction

This module reassembles the generic fixed-prime second case while routing
Vandiver's Lemma II through `KummerIso.UnitExtraction`.

The call graph is intentionally explicit:

1. plus-class nondivisibility supplies the historical principal-generator
   elimination;
2. equations (7)--(10) construct the exact quotient unit and its
   depth-`2p` congruence;
3. the finite unit system and axis-8 channels supply the correction-based
   deep-unit power conclusion;
4. the existing well-founded historical descent applies that conclusion to
   the exact quotient unit.

In particular, this module does not call
`GenericIrregular.LemmaTwo.vandiverLemmaTwo_of_unitSystem` or
`GenericIrregular.SecondCase.secondCaseExcluded_of_certificate`.
-/

open scoped NumberField

namespace Fermat.KummerIso.SecondCase

noncomputable section

open Fermat.GenericIrregular.ChannelCertificate
open Fermat.GenericIrregular.LemmaTwo
open Fermat.GenericIrregular.SecondCase
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime

variable {K : Type} {p N : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The complete correction-based historical assembly with its three
upstream inputs kept explicit.

`hreduce` produces `EquationSevenToTenData`.  The descent theorem then
applies `hkummer` to that data's literal `quotientUnit`, using its literal
`highCongruence`; there is no bridge through a merely semiprimary unit. -/
theorem secondCaseExcluded_of_plusClass_of_unitSystem_of_channels
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hplus : PlusClassNondivisibility K p)
    (system : LemmaTwoUnitSystem K p)
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
    Fermat.KummerIso.Principalization.realPrincipalGeneratorElimination_of_plusClass
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
  have hkummer :
      Fermat.Irregular.VandiverCriterion.KummerUnitPowerConclusion
        K p :=
    Fermat.Irregular.VandiverUnitLemma.kummerUnitPowerConclusion_of_lemmaTwo
      hp5
      (Fermat.KummerIso.UnitExtraction.vandiverLemmaTwo_of_unitSystem
        hp5 system)
      (channels.bernoulliCubeCondition hp5)
  intro a b c ha hb hc hgcd hdiv
  exact
    (secondCaseExcluded_of_historical_descent
      hp2 hζ (RealSourceAdmissible hζ) hstart hreduce hkummer)
      ha hb hc hgcd hdiv

/-- An existing honest fixed-second-case certificate excludes Case II via
the normalized Kummer correction.

The certificate type is reused from `GenericIrregular.SecondCase`; only its
assembly theorem is replaced. -/
theorem secondCaseExcluded_of_certificate
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (certificate : FixedSecondCaseCertificate K p N) :
    Fermat.SecondCaseExcluded p :=
  secondCaseExcluded_of_plusClass_of_unitSystem_of_channels
    hp5 hζ certificate.plusClassNondivisibility
      certificate.unitSystem certificate.channels

end

end Fermat.KummerIso.SecondCase
