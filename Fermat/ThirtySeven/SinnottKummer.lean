import Fermat.Irregular.CyclotomicZetaFactorization37
import Fermat.ThirtySeven.ResidueHomomorphisms

/-!
# End-to-end Sinnott--Kummer endpoint for exponent 37

This file connects the concrete, kernel-checked residue matrix to the now-proved
cyclotomic Artin factorization.  The resulting Sinnott--Kummer formula shows
unconditionally that the maximal-real class number is prime to `37`.
-/

open scoped NumberField

namespace Fermat.ThirtySeven.SinnottKummer

noncomputable section

open Fermat.Irregular.CircularUnitIndex
open Fermat.Irregular.SinnottIndex
open Fermat.Irregular.CyclotomicSinnottBridge37
open Fermat.Irregular.CyclotomicZetaFactorization37

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

/-- The circular-unit index is the maximal-real class number at exponent `37`. -/
theorem circularUnit37_realIndex_eq_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    realUnitRelIndex (circularUnit37 hzeta) = NumberField.classNumber K⁺ :=
  circularUnit37_realIndex_eq_classNumber_of_zetaFactorization
    (cyclotomicZetaFactorization37 (K := K)) hzeta

/-- The concrete circular-unit residue certificate and the unconditional
Sinnott--Kummer formula prove that `37` does not divide the plus class number. -/
theorem not_dvd_classNumber
    {zeta : K} (hzeta : IsPrimitiveRoot zeta 37) :
    ¬ 37 ∣ NumberField.classNumber K⁺ := by
  rw [← circularUnit37_realIndex_eq_classNumber hzeta]
  exact Fermat.ThirtySeven.ResidueHomomorphisms.not_dvd_circularUnit37_real_index_of_cyclotomic
    hzeta

end

end Fermat.ThirtySeven.SinnottKummer
