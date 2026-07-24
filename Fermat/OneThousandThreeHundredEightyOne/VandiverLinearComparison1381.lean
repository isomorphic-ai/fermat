import Fermat.Irregular.VandiverLinearComparisonPrime

/-!
# The depth-2762 equation-(8) coefficient comparison at exponent 1381

This is the small algebraic bridge used after the prepared pairs at
exponents one and two have been constructed.  The generic comparison
cancels one copy of the cyclotomic uniformizer from a depth-`2763`
divisibility of `ω+θ`, leaving the depth-`2762 = 2 * 1381` congruence
needed by the integer-ratio calculation.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.VandiverHistorical

open scoped NumberField nonZeroDivisors

open Fermat.Irregular.VandiverHistoricalDescent

noncomputable section

variable {K : Type} [Field K] [NumberField K]

local instance : Fact (Nat.Prime 1381) := ⟨by norm_num⟩

/-- Equation-(8) at exponents one and two has coefficient sides congruent
modulo `(ζ-1)^2762`, provided the distinguished factor has the one-step
deeper divisibility. -/
theorem equationEight_one_two_coefficients_close2762
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381)
    (ω θ r₁ r₂ : 𝓞 K) (η₁ η₂ : (𝓞 K)ˣ)
    (hhigh :
      ((hζ.unit' : 𝓞 K) - 1) ^ 2763 ∣ ω + θ)
    (heq₁ :
      ω + (hζ.unit' : 𝓞 K) * θ =
        (1 - (hζ.unit' : 𝓞 K)) * η₁ * r₁ ^ 1381)
    (heq₂ :
      ω + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * θ =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * η₂ * r₂ ^ 1381) :
    ((hζ.unit' : 𝓞 K) - 1) ^ 2762 ∣
      (η₁ : 𝓞 K) * r₁ ^ 1381 -
        (η₂ : 𝓞 K) * r₂ ^ 1381 := by
  apply
    Fermat.Irregular.VandiverLinearComparisonPrime.equationEight_one_two_coefficients_close
        (p := 1381) (by norm_num) hζ 2762
        ω θ r₁ r₂ η₁ η₂
  · simpa only [show 2762 + 1 = 2763 by norm_num] using hhigh
  · exact heq₁
  · exact heq₂

/-- Historical-state wrapper: the full distinguished-factor divisibility
automatically supplies the fixed depth `2763` required above. -/
theorem historicalEquationEight_one_two_coefficients_close2762
    {ζ : K} (hζ : IsPrimitiveRoot ζ 1381)
    (s : HistoricalState hζ)
    (hfull :
      ((hζ.unit' : 𝓞 K) - 1) ^
          ((2 * s.m - 1) * 1381 + 1) ∣
        s.omega + s.theta)
    (r₁ r₂ : 𝓞 K) (η₁ η₂ : (𝓞 K)ˣ)
    (heq₁ :
      s.omega + (hζ.unit' : 𝓞 K) * s.theta =
        (1 - (hζ.unit' : 𝓞 K)) * η₁ * r₁ ^ 1381)
    (heq₂ :
      s.omega + (hζ.unit' ^ 2 : (𝓞 K)ˣ) * s.theta =
        (1 - (hζ.unit' ^ 2 : (𝓞 K)ˣ)) * η₂ * r₂ ^ 1381) :
    ((hζ.unit' : 𝓞 K) - 1) ^ 2762 ∣
      (η₁ : 𝓞 K) * r₁ ^ 1381 -
        (η₂ : 𝓞 K) * r₂ ^ 1381 := by
  have hle :
      2763 ≤ (2 * s.m - 1) * 1381 + 1 := by
    have hm := s.one_lt_m
    omega
  have hhigh :
      ((hζ.unit' : 𝓞 K) - 1) ^ 2763 ∣
        s.omega + s.theta :=
    (pow_dvd_pow ((hζ.unit' : 𝓞 K) - 1) hle).trans hfull
  exact equationEight_one_two_coefficients_close2762
    hζ s.omega s.theta r₁ r₂ η₁ η₂ hhigh heq₁ heq₂

end

end Fermat.OneThousandThreeHundredEightyOne.VandiverHistorical
