import Fermat.Irregular.CyclotomicSinnottBridge37
import Fermat.ThirtySeven.ResidueHomomorphisms

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 37

This file connects the concrete, kernel-checked residue matrix to the analytic
bridge.  Once the standard cyclotomic Artin factorization on `Re(s) > 1` is
supplied, the maximal-real class number is prime to `37`.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.CyclotomicSinnottBridge37

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {37} ℚ K]

local instance : NumberField.IsCMField K := cyclotomic37_isCMField (K := K)
local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The concrete exponent-37 circular-unit residue certificate, together
with cyclotomic Artin factorization, proves the needed plus-class-number
nondivisibility. -/
theorem not_dvd_classNumber_of_zetaFactorization
    (hfactor : CyclotomicZetaFactorization37 K)
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    ¬ 37 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit37_realIndex_eq_classNumber_of_zetaFactorization hfactor hzeta]
  exact Fermat.ThirtySeven.ResidueHomomorphisms.not_dvd_circularUnit37_real_index_of_cyclotomic
    hzeta

end

end Fermat.ThirtySeven.SinnottKummer
