import Fermat.SixtySeven.CircularUnitResidues
import Fermat.Irregular.CyclotomicSinnottBridgePrime

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 67

The checked residue matrix at `269` is combined with the generic odd-prime
Sinnott--Kummer theorem, proving plus-class-number nondivisibility.
-/

open scoped NumberField

namespace Fermat.SixtySeven.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {67} ℚ K]

local instance : Fact (Nat.Prime 67) := ⟨Fermat.SixtySeven.prime_67⟩
local instance : Fact (2 < 67) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.SixtySeven.prime_67 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit67_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 67) (K := K) hzeta

theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 67) :
    ¬ 67 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit67_realIndex_eq_classNumber hzeta]
  exact Fermat.SixtySeven.CircularUnitResidues.not_dvd_circularUnit67_real_index
    hzeta

end

end Fermat.SixtySeven.SinnottKummer
