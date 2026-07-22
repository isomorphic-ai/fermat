import Fermat.OneHundredFiftySeven.CircularUnitResidues
import Fermat.Irregular.CyclotomicSinnottBridgePrime

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 157

The checked `77 × 77` residue matrix at `7537` is combined with the generic
odd-prime Sinnott--Kummer theorem, proving plus-class-number nondivisibility.
-/

open scoped NumberField

namespace Fermat.OneHundredFiftySeven.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {157} ℚ K]

local instance : Fact (Nat.Prime 157) :=
  ⟨Fermat.OneHundredFiftySeven.prime_157⟩
local instance : Fact (2 < 157) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.OneHundredFiftySeven.prime_157 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit157_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 157) (K := K) hzeta

theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 157) :
    ¬ 157 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit157_realIndex_eq_classNumber hzeta]
  exact Fermat.OneHundredFiftySeven.CircularUnitResidues.not_dvd_circularUnit157_real_index
    hzeta

end

end Fermat.OneHundredFiftySeven.SinnottKummer
