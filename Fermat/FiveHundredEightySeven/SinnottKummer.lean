import Fermat.FiveHundredEightySeven.CircularUnitResidues
import Fermat.Irregular.CyclotomicSinnottBridgePrime

/-!
# Sinnott--Kummer endpoint at exponent 587

The compressed residue-symbol matrix at `8219` is combined with the generic
odd-prime circular-unit index theorem.  This proves the exact plus-class
input used by the historical second-case descent.
-/

open scoped NumberField

namespace Fermat.FiveHundredEightySeven.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.SinnottIndexPrime
open Fermat.Irregular.CyclotomicSinnottBridgePrime

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {587} ℚ K]

local instance : Fact (Nat.Prime 587) :=
  ⟨Fermat.FiveHundredEightySeven.prime_587⟩
local instance : Fact (2 < 587) := ⟨by norm_num⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (K := K)
    Fermat.FiveHundredEightySeven.prime_587 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem circularUnit587_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 587) :
    realUnitRelIndex (circularUnitFamily hzeta (by norm_num)) =
      NumberField.classNumber K⁺ :=
  circularUnit_realIndex_eq_classNumber (p := 587) (K := K) hzeta

theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 587) :
    ¬ 587 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit587_realIndex_eq_classNumber hzeta]
  exact Fermat.FiveHundredEightySeven.CircularUnitResidues.not_dvd_circularUnit587_real_index
    hzeta

end

end Fermat.FiveHundredEightySeven.SinnottKummer
