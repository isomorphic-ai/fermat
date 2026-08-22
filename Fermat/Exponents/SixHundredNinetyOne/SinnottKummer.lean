import Fermat.Exponents.SixHundredNinetyOne.CircularUnitResidues
import Fermat.Descent.Irregular.CyclotomicSinnottBridgePrime

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 691

The checked compressed residue matrix at `11057` is combined with the generic
odd-prime Sinnott--Kummer theorem, proving plus-class-number
nondivisibility.
-/

open scoped NumberField

namespace Fermat.SixHundredNinetyOne.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {691} ℚ K]

local instance : Fact (Nat.Prime 691) :=
  ⟨Fermat.SixHundredNinetyOne.prime_691⟩
local instance : Fact (2 < 691) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.SixHundredNinetyOne.prime_691 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit691_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 691) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 691) (K := K) hzeta

/-- The plus class number is prime to `691`. -/
theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 691) :
    ¬691 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit691_realIndex_eq_classNumber hzeta]
  exact Fermat.SixHundredNinetyOne.CircularUnitResidues.not_dvd_circularUnit691_real_index
    hzeta

end

end Fermat.SixHundredNinetyOne.SinnottKummer
