import Fermat.Irregular.VandiverTakagiPairPrime
import Fermat.OneThousandThreeHundredEightyOne.VandiverHistoricalInfrastructure1381

/-!
# Explicit Takagi pair interface at exponent 1381

This module records the precise remaining Takagi input at exponent `1381`.
For each of the exponents `1` and `2`, it is enough to construct one
equation-(8) generator with a real coefficient unit and prove that the
generator is prime to `ζ-1`.  The generic conjugation theorem then supplies
the `-1` and `-2` equations, conjugate generators, nonramification on both
sides, real products, quadratic identities, and all three product
coprimalities.

No existence of the two plus equations is attributed to the uploaded
1381/1831 folding package; they are the separate historical
Takagi--Furtwängler boundary.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverHistorical

open scoped NumberField

open Fermat.Irregular.VandiverHistoricalDescent
open Fermat.Irregular.VandiverHistoricalPrime
open Fermat.Irregular.VandiverTakagiPairPrime

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 1381) K (by norm_num)

/-- A conjugate equation-(8) pair at exponent `1381`. -/
abbrev EquationEightPair1381
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381)
    (s : HistoricalState hζ) (t : (𝓞 K)ˣ) :=
  ConjugateEquationEightPair hζ s.omega s.theta t

/-- The two conjugate pairs at exponents `±1` and `±2` needed by
Vandiver's equation (10). -/
structure EquationEightPairs1381
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381)
    (s : HistoricalState hζ) where
  one : EquationEightPair1381 hζ s hζ.unit'
  two : EquationEightPair1381 hζ s (hζ.unit' ^ 2)

/-- One plus equation at exponent `1` supplies the full `±1` pair. -/
theorem equationEightPair_one1381_of_plus
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s)
    (rho : 𝓞 K) (eta : (𝓞 K)ˣ)
    (heta :
      NumberField.IsCMField.unitsComplexConj K eta = eta)
    (hplus :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * eta * rho ^ 1381)
    (hrho : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rho) :
    Nonempty (EquationEightPair1381 hζ s hζ.unit') := by
  have hplus' :
      s.omega + (hζ.unit' ^ 1 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 1 : (𝓞 K)ˣ)) * eta *
          rho ^ 1381 := by
    simpa only [pow_one] using hplus
  simpa only [EquationEightPair1381, pow_one] using
    (conjugateEquationEightPair_of_zetaPow_plus
      (p := 1381) hζ 1 eta hs.1 hs.2.1 heta hplus' hrho)

/-- One plus equation at exponent `2` supplies the full `±2` pair. -/
theorem equationEightPair_two1381_of_plus
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s)
    (rho : 𝓞 K) (eta : (𝓞 K)ˣ)
    (heta :
      NumberField.IsCMField.unitsComplexConj K eta = eta)
    (hplus :
      s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * eta * rho ^ 1381)
    (hrho : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rho) :
    Nonempty (EquationEightPair1381 hζ s (hζ.unit' ^ 2)) :=
  conjugateEquationEightPair_of_zetaPow_plus
    (p := 1381) hζ 2 eta hs.1 hs.2.1 heta hplus hrho

/-- The exact two-plus-equation Takagi interface at exponent `1381`. -/
theorem equationEightPairs1381_of_plus
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381)
    (s : HistoricalState hζ) (hs : RealSourceAdmissible hζ s)
    (rhoOne rhoTwo : 𝓞 K) (etaOne etaTwo : (𝓞 K)ˣ)
    (hetaOne :
      NumberField.IsCMField.unitsComplexConj K etaOne = etaOne)
    (hetaTwo :
      NumberField.IsCMField.unitsComplexConj K etaTwo = etaTwo)
    (hone :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * etaOne * rhoOne ^ 1381)
    (htwo :
      s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * etaTwo *
          rhoTwo ^ 1381)
    (hrhoOne : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rhoOne)
    (hrhoTwo : ¬ (hζ.unit' : 𝓞 K) - 1 ∣ rhoTwo) :
    Nonempty (EquationEightPairs1381 hζ s) := by
  obtain ⟨one⟩ :=
    equationEightPair_one1381_of_plus
      hζ s hs rhoOne etaOne hetaOne hone hrhoOne
  obtain ⟨two⟩ :=
    equationEightPair_two1381_of_plus
      hζ s hs rhoTwo etaTwo hetaTwo htwo hrhoTwo
  exact ⟨⟨one, two⟩⟩

namespace EquationEightPairs1381

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 1381)
  (s : HistoricalState hζ) (d : EquationEightPairs1381 hζ s)

/-- Once the two Takagi pairs and the distinguished equation-(8a)
generator are available, all three product coprimalities required by the
historical reduction follow. -/
theorem products_coprime
    (rhoZero cZero : 𝓞 K) (hrhoZero : rhoZero ≠ 0)
    (hzero : s.omega + s.theta = cZero * rhoZero ^ 1381) :
    rhoZero ^ 2 ≠ 0 ∧
      IsCoprime
          (d.one.rplus * d.one.rminus)
          (d.two.rplus * d.two.rminus) ∧
      IsCoprime
          (d.two.rplus * d.two.rminus)
          (rhoZero ^ 2) ∧
      IsCoprime
          (d.one.rplus * d.one.rminus)
          (rhoZero ^ 2) :=
  equationEight_generators_products_coprime1381 hζ
    d.one.coefficient d.one.coefficient
    d.two.coefficient d.two.coefficient cZero
    hrhoZero s.coprime_omega_theta
    d.one.equation_plus d.one.equation_minus
    d.two.equation_plus d.two.equation_minus hzero
    d.one.rplus_not_ramified d.one.rminus_not_ramified
    d.two.rplus_not_ramified d.two.rminus_not_ramified

end EquationEightPairs1381

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverHistorical
