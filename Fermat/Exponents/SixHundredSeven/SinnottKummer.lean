import Fermat.Exponents.SixHundredSeven.CircularUnitResidues
import Fermat.Descent.Irregular.CyclotomicSinnottBridgePrime

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 607

The checked compressed residue matrix at `20639` is combined with the
generic odd-prime Sinnott--Kummer theorem, proving plus-class-number
nondivisibility. The separate package prime `118973` is a norm/branch
selector and is not used by this circular-unit argument.
-/

open scoped NumberField

namespace Fermat.SixHundredSeven.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {607} ℚ K]

local instance : Fact (Nat.Prime 607) :=
  ⟨Fermat.SixHundredSeven.prime_607⟩
local instance : Fact (2 < 607) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.SixHundredSeven.prime_607 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit607_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 607) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 607) (K := K) hzeta

/-- The plus class number is prime to `607`. -/
theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 607) :
    ¬607 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit607_realIndex_eq_classNumber hzeta]
  exact
    Fermat.SixHundredSeven.CircularUnitResidues.not_dvd_circularUnit607_real_index
      hzeta

end

end Fermat.SixHundredSeven.SinnottKummer
