import Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues
import Fermat.Irregular.CyclotomicSinnottBridgePrime

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 1831

The checked compressed residue matrix at `358877` is combined with the
generic odd-prime Sinnott--Kummer theorem, proving plus-class-number
nondivisibility.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : Fact (2 < 1831) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.OneThousandEightHundredThirtyOne.prime_1831 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit1831_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 1831) (K := K) hzeta

/-- The plus class number is prime to `1831`. -/
theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 1831) :
    ¬1831 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit1831_realIndex_eq_classNumber hzeta]
  exact
    Fermat.OneThousandEightHundredThirtyOne.CircularUnitResidues.not_dvd_circularUnit1831_real_index
      hzeta

end

end Fermat.OneThousandEightHundredThirtyOne.SinnottKummer
