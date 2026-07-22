import Fermat.FiftyNine.CircularUnitIndex
import Fermat.Irregular.CyclotomicSinnottBridgePrime

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 59

The checked finite-field residue matrix is combined with the generic
odd-prime Sinnott--Kummer theorem.  Consequently `59` is prime to the
class number of the maximal real subfield.
-/

open scoped NumberField

namespace Fermat.FiftyNine.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {59} ℚ K]

local instance : Fact (Nat.Prime 59) := ⟨Fermat.FiftyNine.prime_59⟩
local instance : Fact (2 < 59) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.FiftyNine.prime_59 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit59_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 59) (K := K) hzeta

theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 59) :
    ¬ 59 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit59_realIndex_eq_classNumber hzeta]
  simpa only [Fermat.FiftyNine.CircularUnitIndex.circularUnits59,
    realUnitRelIndex] using
      Fermat.FiftyNine.CircularUnitIndex.not_dvd_circularUnits59_realIndex hzeta

end

end Fermat.FiftyNine.SinnottKummer
