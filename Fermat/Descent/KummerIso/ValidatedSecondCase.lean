import Fermat.Descent.Irregular.VandiverHistoricalStartPrime
import Fermat.Core.Cases
import Fermat.Descent.KummerIso.BernoulliValidationBound
import Fermat.Descent.KummerIso.FermatEquationSevenD
import Fermat.Descent.KummerIso.UnitExtraction

/-!
# Case II with an explicit Morishima hypothesis

This is the production assembly for the working-first Kummer splice.

* `FermatEquationSevenD` supplies the historical equations-(7)--(10)
  construction, including the exact depth-`2p` quotient unit.
* `MorishimaConjectureAt p` is the explicit no-Bernoulli-cube hypothesis.
* `CanonicalDeepDerivativeSourceValidation` is the separate temporary
  canonical-family derivative-source seam.

Everything else in this file is checked plumbing.  The conjectural
arithmetic premise is visible in every generic endpoint that consumes it.
-/

namespace Fermat.KummerIso

open scoped NumberField

open Fermat.Irregular
open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverLemmaTwoCore
open Fermat.Irregular.VandiverUnitLemma
open Fermat.GenericIrregular.DeepReality
open Fermat.KummerIso.UnitAdaptiveRelationHarness

noncomputable section

variable {K : Type} {p : ℕ} [Fact p.Prime]
  [Field K] [NumberField K] [NumberField.IsCMField K]
  [IsCyclotomicExtension {p} ℚ K]

/-- The explicit Morishima hypothesis and the separately named derivative
source, followed only by checked generic adapters, produce the exact
deep-unit root interface consumed by the historical descent. -/
theorem kummerUnitPowerConclusion_of_canonicalCubeCongruences
    (hp5 : 5 ≤ p)
    (hMorishima : MorishimaConjectureAt p) :
    Fermat.Irregular.VandiverCriterion.KummerUnitPowerConclusion K p := by
  intro ζ hζ u hdeep
  let uReal : NumberField.IsCMField.realUnits K :=
    deepRealUnit hp5 hζ u hdeep
  let EReal :
      SourceIndex p → NumberField.IsCMField.realUnits K :=
    realCircularUnitFamily hζ (by omega)
  have hcubeAmbient :
      PrimitiveRelationCubeCongruences p u
        (circularUnitFamily hζ (by omega)) :=
    canonicalPrimitiveRelationCubeCongruences hp5 hζ u hdeep
  have hcubeReal :
      PrimitiveRelationCubeCongruences p uReal EReal := by
    intro t a ht hrel hprimitive
    apply hcubeAmbient t a ht
    · have hrel' := congrArg
          ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hrel
      simpa only [uReal, EReal, deepRealUnit_coe,
        realCircularUnitFamily_coe, Subgroup.coe_pow,
        Subgroup.coe_zpow, SubmonoidClass.coe_finsetProd] using hrel'
    · exact hprimitive
  letI :
      (Subgroup.closure (Set.range EReal)).FiniteIndex := by
    simpa only [EReal] using
      real_closure_finiteIndex (by omega : 2 < p) hζ
  obtain ⟨v, hv⟩ :=
    isPower_of_primitiveRelationCubeCongruences
      hMorishima
      (Fermat.Irregular.VandiverRealUnits.odd_pow_injective
        (K := K) p
        ((Fact.out : p.Prime).odd_of_ne_two (by omega)))
      uReal EReal hcubeReal
  refine ⟨(v : (𝓞 K)ˣ), ?_⟩
  have hv' := congrArg
    ((↑) : NumberField.IsCMField.realUnits K → (𝓞 K)ˣ) hv
  simpa only [uReal, deepRealUnit_coe, Subgroup.coe_pow] using hv'

/-- Checked historical Case II from an explicitly supplied equations-(7)--(10)
reduction and the exact Kummer unit-power conclusion consumed by the descent.

This is the common assembly boundary. It carries no validation policy:
callers may obtain `hkummer` from the conditional canonical-family route or
from a finite unit system together with axis-8 channel data. -/
theorem secondCaseExcluded_of_historicalReduction_of_kummerConclusion
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hreduce :
      EquationsSevenToTenReduction hζ
        (RealSourceAdmissible hζ))
    (hkummer :
      Fermat.Irregular.VandiverCriterion.KummerUnitPowerConclusion
        K p) :
    Fermat.SecondCaseExcluded p := by
  have hp2 : p ≠ 2 := by
    omega
  obtain ⟨r, hr⟩ :=
    (Fact.out : p.Prime).odd_of_ne_two hp2
  have hstart :
      SecondCaseStartsHistoricalDescent hζ
        (RealSourceAdmissible hζ) :=
    Fermat.Irregular.VandiverHistoricalStartPrime.secondCaseStartsHistoricalDescent
      (K := K) hp5 hr hζ
  intro a b c ha hb hc hgcd hdiv
  exact
    (secondCaseExcluded_of_historical_descent
      hp2 hζ (RealSourceAdmissible hζ)
      hstart hreduce hkummer)
      ha hb hc hgcd hdiv

/-- End-to-end historical Case II from an explicitly supplied historical
equations-(7)--(10) reduction.

Morishima's conjecture is an explicit premise.  The canonical derivative
source is the only project axiom used internally here; callers may construct
the ideal side either through `FermatEquationSevenD` or through finite
residue certificates. -/
theorem secondCaseExcluded_of_historicalReduction
    (hp5 : 5 ≤ p)
    (hMorishima : MorishimaConjectureAt p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hreduce :
      EquationsSevenToTenReduction hζ
        (RealSourceAdmissible hζ)) :
    Fermat.SecondCaseExcluded p :=
  secondCaseExcluded_of_historicalReduction_of_kummerConclusion
    hp5 hζ hreduce
    (kummerUnitPowerConclusion_of_canonicalCubeCongruences
      hp5 hMorishima)

/-- A finite unit system and its axis-8 channels discharge the Kummer-unit
side of the historical reduction without using Morishima's conjecture or
the canonical derivative-source axiom.

The theorem deliberately takes the equations-(7)--(10) reduction separately:
in fixed-residue regressions that reduction comes from an independently
checked circular-unit residue certificate. -/
theorem secondCaseExcluded_of_historicalReduction_of_unitSystem_of_channels
    {N : ℕ}
    (hp5 : 5 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hreduce :
      EquationsSevenToTenReduction hζ
        (RealSourceAdmissible hζ))
    (system :
      Fermat.GenericIrregular.LemmaTwo.LemmaTwoUnitSystem K p)
    (channels :
      Fermat.GenericIrregular.ChannelCertificate.FixedChannelCertificate
        p N) :
    Fermat.SecondCaseExcluded p :=
  secondCaseExcluded_of_historicalReduction_of_kummerConclusion
    hp5 hζ hreduce
    (Fermat.KummerIso.UnitExtraction.kummerUnitPowerConclusion_of_unitSystem_of_channels
      hp5 system channels)

/-- End-to-end historical Case II through the equation-(7d) and canonical
derivative-source seams, conditional on the explicit Morishima hypothesis. -/
theorem secondCaseExcluded_of_two_validation_seams
    (hp5 : 5 ≤ p)
    (hMorishima : MorishimaConjectureAt p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Fermat.SecondCaseExcluded p :=
  secondCaseExcluded_of_historicalReduction hp5 hMorishima hζ
    (historicalEquationsSevenToTenReduction hp5 hζ)

/-- End-to-end FLT after combining an explicit Morishima hypothesis and the
two Case-II validation seams with the proof-producing Sophie--Germain search
for Case I.

The three visible project axioms are `FermatEquationSevenD`,
`CanonicalDeepDerivativeSourceValidation`, and successful termination of the
executable Sophie--Germain auxiliary-prime search. -/
theorem holdsAt_of_validation_seams
    (hp5 : 5 ≤ p)
    (hMorishima : MorishimaConjectureAt p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Fermat.HoldsAt p :=
  Fermat.holdsAt_of_sophieGermainSearch_of_secondCaseExcluded
    (secondCaseExcluded_of_two_validation_seams hp5 hMorishima hζ)

end

end Fermat.KummerIso
