import Fermat.FourHundredNinetyOne.CircularUnitResidues
import Fermat.Irregular.CyclotomicSinnottBridgePrime

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 491

The checked compressed residue matrix at `983` is combined with the generic
odd-prime Sinnott--Kummer theorem, proving plus-class-number
nondivisibility.
-/

open scoped NumberField

namespace Fermat.FourHundredNinetyOne.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {491} ℚ K]

local instance : Fact (Nat.Prime 491) :=
  ⟨Fermat.FourHundredNinetyOne.prime_491⟩
local instance : Fact (2 < 491) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.FourHundredNinetyOne.prime_491 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit491_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 491) (K := K) hzeta

/-- The plus class number is prime to `491`. -/
theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 491) :
    ¬491 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit491_realIndex_eq_classNumber hzeta]
  exact Fermat.FourHundredNinetyOne.CircularUnitResidues.not_dvd_circularUnit491_real_index
    hzeta

end

end Fermat.FourHundredNinetyOne.SinnottKummer
