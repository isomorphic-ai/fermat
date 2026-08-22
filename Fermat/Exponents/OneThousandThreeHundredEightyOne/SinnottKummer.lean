import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitResidues
import Fermat.Descent.Irregular.CyclotomicSinnottBridgePrime

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 1381

The checked compressed residue matrix at `38669` is combined with the
generic odd-prime Sinnott--Kummer theorem, proving plus-class-number
nondivisibility.
-/

open scoped NumberField

namespace Fermat.OneThousandThreeHundredEightyOne.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1381} ℚ K]

local instance : Fact (Nat.Prime 1381) :=
  ⟨Fermat.OneThousandThreeHundredEightyOne.prime_1381⟩
local instance : Fact (2 < 1381) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.OneThousandThreeHundredEightyOne.prime_1381 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit1381_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 1381) (K := K) hzeta

/-- The plus class number is prime to `1381`. -/
theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1381) :
    ¬1381 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit1381_realIndex_eq_classNumber hzeta]
  exact
    Fermat.OneThousandThreeHundredEightyOne.CircularUnitResidues.not_dvd_circularUnit1381_real_index
      hzeta

end

end Fermat.OneThousandThreeHundredEightyOne.SinnottKummer
