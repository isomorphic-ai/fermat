import Fermat.Irregular.VandiverEquationEightAGeneratorPrime
import Fermat.SixHundredNinetyOne.SinnottKummer

/-!
# Regression specialization of the generic equation-(8a) generator at 691

The historical exponent-691 development originally proved this generator
extraction directly.  This small specialization keeps the same mathematical
statement as a regression for the prime-generic implementation, discharging
its plus-class input with the existing Sinnott--Kummer certificate.
-/

namespace Fermat.SixHundredNinetyOne.VandiverHistorical

open scoped NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

local instance : Fact (Nat.Prime 691) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  IsCyclotomicExtension.IsCMField (p := 691) K (by norm_num)

set_option maxRecDepth 50000 in
/-- The generic real-ideal generator theorem reproduces the established
exponent-691 interface. -/
theorem exists_squaredConjugationGenerator_of_real_pow_primeGeneric691
    {ζ : K} (hζ : IsPrimitiveRoot ζ 691)
    (J : Ideal (𝓞 K)) (q : 𝓞 K) (hq0 : q ≠ 0)
    (hqreal :
      NumberField.IsCMField.ringOfIntegersComplexConj K q = q)
    (hpow : J ^ 691 = Ideal.span {q}) :
    ∃ (ρ : 𝓞 K) (η : (𝓞 K)ˣ) (j : ℕ),
      J = Ideal.span {ρ} ∧
      q = η * ρ ^ 691 ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K (ρ ^ 2) =
        (hζ.unit' ^ j : (𝓞 K)ˣ) * ρ ^ 2 :=
  Fermat.Irregular.VandiverEquationEightAGeneratorPrime.exists_squaredConjugationGenerator_of_real_pow
    (p := 691)
    (Fermat.SixHundredNinetyOne.SinnottKummer.not_dvd_classNumber hζ)
    (by norm_num) (by norm_num) hζ J q hq0 hqreal hpow

end

end Fermat.SixHundredNinetyOne.VandiverHistorical
