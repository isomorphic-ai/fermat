import Fermat.Irregular.VandiverGeneratorSupportPrime
import Fermat.Irregular.VandiverEquationEightAGeneratorPrime
import Fermat.Irregular.VandiverHistoricalQuadraticPrime
import Fermat.Irregular.VandiverRealNormalizationPrime
import Fermat.Irregular.VandiverHistoricalStartPrime
import Fermat.Irregular.VandiverHistoricalStatePrime
import Fermat.Irregular.VandiverLinearComparisonPrime
import Fermat.OneThousandEightHundredThirtyOne.VandiverData

/-!
# Historical-descent infrastructure at exponent 1831

This file instantiates the prime-generic parts of Vandiver's historical
descent at `p = 1831`:

* the initial state has exponent `915`;
* generators with a root-of-unity conjugation quotient can be made real;
* roots of real `1831`st-power units can be chosen real;
* the four equation-(8) generators have the required product
  coprimalities; and
* a concrete finite elimination through equation (10a) implies the full
  well-founded reduction and hence excludes the second case.

Thus the remaining historical boundary at this exponent is exactly
`RealPrincipalGeneratorElimination1831`: constructing the displayed
conjugation-power data from each admissible historical state.  Compared
with the completed `691` assembly, its finite payload consists of:

1. the distinguished equation-(8a) ideal and generator;
2. prepared conjugate equation-(8) pairs at exponents `±1` and `±2`;
3. the depth-`(2 * m - 2) * 1831` coefficient comparison and its
   depth-`2 * 1831 = 3662` truncation;
4. the integral-ratio and negative-square calculation; and
5. the remaining realness checks on trace and coefficient units.

The quadratic elimination, generator coprimality, strict support
bookkeeping, all real normalizations, successor-state construction, and
well-founded descent are discharged by the imported generic theorems.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverHistoricalSupportPrime

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1831) K (by norm_num)

/-- The exact finite, source-faithful boundary remaining at exponent
`1831`. -/
abbrev RealPrincipalGeneratorElimination1831 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 1831) : Prop :=
  RealPrincipalGeneratorElimination hζ

/-- The inverse-of-two root-of-unity adjustment at `1831 = 2 * 915 + 1`. -/
def realGeneratorNormalizer1831 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 1831) :
    RealGeneratorNormalizer hζ :=
  Fermat.Irregular.VandiverRealNormalizationPrime.realGeneratorNormalizer
    (p := 1831) (r := 915) (by norm_num) hζ

/-- Every `1831`st-power presentation of a real unit admits a real root. -/
theorem realUnitRootNormalization1831 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 1831) :
    RealUnitRootNormalization hζ :=
  Fermat.Irregular.VandiverRealNormalizationPrime.realUnitRootNormalization
    (p := 1831) (by norm_num) hζ

/-- A primitive rational second-case solution starts the historical
descent with exponent `m = 915`. -/
theorem secondCaseStartsHistoricalDescent_1831 {ζ : K}
    (hζ : IsPrimitiveRoot ζ 1831) :
    SecondCaseStartsHistoricalDescent hζ (RealSourceAdmissible hζ) :=
  Fermat.Irregular.VandiverHistoricalStartPrime.secondCaseStartsHistoricalDescent
    (p := 1831) (r := 915) (by norm_num) (by norm_num) hζ

/-- The real factor `ω + θ` carries the full source depth
`(2*m - 1)*1831 + 1`; this is the prime-generic distinguished-root
calculation specialized to exponent `1831`. -/
theorem historicalState_omega_add_theta_fullHighDivisibility1831
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s) :
    ((hζ.unit' : 𝓞 K) - 1) ^
        ((2 * s.m - 1) * 1831 + 1) ∣
      s.omega + s.theta :=
  Fermat.Irregular.VandiverHistoricalStatePrime.historicalState_omega_add_theta_fullHighDivisibility
    (p := 1831) (by norm_num) hζ s hs

/-- End-to-end historical-state form of the depth-3662 coefficient
comparison.  Unlike the low-level linear wrapper, this theorem derives its
high-divisibility premise from real admissibility. -/
theorem historicalEquationEight_one_two_coefficients_close3662_of_real
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s)
    (r₁ r₂ : 𝓞 K) (η₁ η₂ : (𝓞 K)ˣ)
    (heq₁ :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * η₁ * r₁ ^ 1831)
    (heq₂ :
      s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * η₂ * r₂ ^ 1831) :
    ((hζ.unit' : 𝓞 K) - 1) ^ 3662 ∣
      (η₁ : 𝓞 K) * r₁ ^ 1831 -
        (η₂ : 𝓞 K) * r₂ ^ 1831 := by
  have hle :
      3663 ≤ (2 * s.m - 1) * 1831 + 1 := by
    have hm := s.one_lt_m
    omega
  have hhigh :
      ((hζ.unit' : 𝓞 K) - 1) ^ 3663 ∣
        s.omega + s.theta :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) hle).trans
      (historicalState_omega_add_theta_fullHighDivisibility1831 hζ s hs)
  apply
    Fermat.Irregular.VandiverLinearComparisonPrime.equationEight_one_two_coefficients_close
      (p := 1831) (by norm_num) hζ 3662
      s.omega s.theta r₁ r₂ η₁ η₂
  · simpa only [show 3662 + 1 = 3663 by norm_num] using hhigh
  · exact heq₁
  · exact heq₂

omit [IsCyclotomicExtension {1831} ℚ K] in
/-- The prime-independent support theorem specialized to the square of an
equation-(8a) generator in the `1831` descent. -/
theorem square_support_strict1831
    {ξ ρ : 𝓞 K} {I Q : Ideal (𝓞 K)}
    (hξ : ξ ≠ 0)
    (hgenerator : I = Ideal.span {ρ})
    (hfactor : Ideal.span {ξ} = I * Q)
    (hQ : Q ≠ ⊤)
    (hcop : IsCoprime I Q) :
    primeIdealFactorSupport (ρ ^ 2) ⊂
      primeIdealFactorSupport ξ :=
  square_support_strict_of_generator
    hξ hgenerator hfactor hQ hcop

set_option maxRecDepth 50000 in
/-- At exponent `1831`, plus-class nondivisibility turns any nonzero real
principal `1831`st ideal power into the exact squared-conjugation generator
required by historical equation (8a). -/
theorem exists_squaredConjugationGenerator_of_real_pow1831
    (hplus : PlusClassNondivisibility K 1831)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831)
    (J : Ideal (𝓞 K)) (q : 𝓞 K) (hq0 : q ≠ 0)
    (hqreal :
      NumberField.IsCMField.ringOfIntegersComplexConj K q = q)
    (hpow : J ^ 1831 = Ideal.span {q}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ) (j : ℕ),
      J = Ideal.span {ρ} ∧
      q = η * ρ ^ 1831 ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K (ρ ^ 2) =
        (hζ.unit' ^ j : (𝓞 K)ˣ) * ρ ^ 2 :=
  Fermat.Irregular.VandiverEquationEightAGeneratorPrime.exists_squaredConjugationGenerator_of_real_pow
    (p := 1831) hplus (by norm_num) (by norm_num)
    hζ J q hq0 hqreal hpow

/-- The four conjugate equation-(8) generators give the three product
coprimalities needed by the `1831` reduction data. -/
theorem equationEight_generators_products_coprime1831
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831)
    {ω θ r₁ rminus₁ r₂ rminus₂ r₀ : 𝓞 K}
    (ε₁ εminus₁ ε₂ εminus₂ : (𝓞 K)ˣ) (d : 𝓞 K)
    (hr₀ : r₀ ≠ 0)
    (hωθ : IsCoprime ω θ)
    (heq₁ :
      ω + (hζ.unit' : 𝓞 K) * θ =
        (1 - (hζ.unit' : 𝓞 K)) * ε₁ * r₁ ^ 1831)
    (heqminus₁ :
      ω + (hζ.unit'⁻¹ : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit'⁻¹ : (𝓞 K)ˣ)) * εminus₁ *
          rminus₁ ^ 1831)
    (heq₂ :
      ω + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * ε₂ * r₂ ^ 1831)
    (heqminus₂ :
      ω + ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ) * θ =
        (1 - ((hζ.unit' ^ 2)⁻¹ : (𝓞 K)ˣ)) * εminus₂ *
          rminus₂ ^ 1831)
    (hzero : ω + θ = d * r₀ ^ 1831)
    (hr₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₁)
    (hrminus₁π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₁)
    (hr₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ r₂)
    (hrminus₂π : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rminus₂) :
    r₀ ^ 2 ≠ 0 ∧
      IsCoprime (r₁ * rminus₁) (r₂ * rminus₂) ∧
      IsCoprime (r₂ * rminus₂) (r₀ ^ 2) ∧
      IsCoprime (r₁ * rminus₁) (r₀ ^ 2) :=
  Fermat.Irregular.VandiverGeneratorSupportPrime.equationEight_generators_products_coprime
      (p := 1831) (by norm_num) hζ
      ε₁ εminus₁ ε₂ εminus₂ d hr₀ hωθ
      heq₁ heqminus₁ heq₂ heqminus₂ hzero
      hr₁π hrminus₁π hr₂π hrminus₂π

omit [NumberField K] [IsCyclotomicExtension {1831} ℚ K] in
/-- Squaring the distinguished equation-(8a) factor gives its normalized
quadratic equation at `1831 = 2 * 915 + 1`. -/
lemma historicalEquationEightA_quadratic1831
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831)
    (s : HistoricalState hζ)
    (rhoZero : 𝓞 K) (etaZero : (𝓞 K)ˣ)
    (hzero :
      s.omega + s.theta =
        etaZero * kappa hζ ^ (1831 * s.m - 915) *
          rhoZero ^ 1831) :
    s.omega ^ 2 + 2 * (s.omega * s.theta) + s.theta ^ 2 =
      kappa hζ *
        ((etaZero ^ 2 : (𝓞 K)ˣ) *
          (kappa hζ ^ (2 * s.m - 1) * rhoZero ^ 2) ^ 1831) :=
  Fermat.Irregular.VandiverHistoricalQuadraticPrime.historicalEquationEightA_quadratic
      (p := 1831) (r := 915) (by norm_num)
      hζ s.m s.one_lt_m s.omega s.theta rhoZero etaZero hzero

/-- A concrete finite elimination at `1831` supplies the complete
equations-(7)--(10) reduction relation. -/
theorem equationsSevenToTenReduction_1831
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831)
    (heliminate : RealPrincipalGeneratorElimination1831 hζ) :
    EquationsSevenToTenReduction hζ (RealSourceAdmissible hζ) :=
  equationsSevenToTenReduction hζ
    (realGeneratorNormalizer1831 hζ)
    (realUnitRootNormalization1831 hζ)
    heliminate

/-- The exact historical finite elimination and Kummer's deep unit
conclusion already suffice to exclude the second case at `1831`. -/
theorem secondCaseExcluded_1831_of_historical
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831)
    (heliminate : RealPrincipalGeneratorElimination1831 hζ)
    (hkummer :
      Fermat.Irregular.VandiverCriterion.KummerUnitPowerConclusion K 1831) :
    Fermat.SecondCaseExcluded 1831 :=
  secondCaseExcluded_of_historical_descent
    (p := 1831) (by norm_num) hζ
    (RealSourceAdmissible hζ)
    (secondCaseStartsHistoricalDescent_1831 hζ)
    (equationsSevenToTenReduction_1831 hζ heliminate)
    hkummer

/-- Once the exact finite elimination is constructed, the checked
Bernoulli cube condition and Vandiver's Lemma II exclude the second case
at exponent `1831`. -/
theorem secondCaseExcluded_1831_of_vandiverLemmaTwo
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1831)
    (heliminate : RealPrincipalGeneratorElimination1831 hζ)
    (hLemmaTwo :
      Fermat.Irregular.VandiverUnitLemma.VandiverLemmaTwo K 1831) :
    Fermat.SecondCaseExcluded 1831 :=
  secondCaseExcluded_of_vandiverLemmaTwo
    (p := 1831) (by norm_num) hζ
    (RealSourceAdmissible hζ)
    (secondCaseStartsHistoricalDescent_1831 hζ)
    (equationsSevenToTenReduction_1831 hζ heliminate)
    hLemmaTwo
    Fermat.OneThousandEightHundredThirtyOne.VandiverData.bernoulliCubeCondition_oneThousandEightHundredThirtyOne

end

end Fermat.OneThousandEightHundredThirtyOne.VandiverHistorical
