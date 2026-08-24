import Fermat.Certificates.CaseII_1.CircularUnitProjectionReceipt1831AtQ18311

/-!
# Normalized Case-II.1 projection receipt at exponent 1831

This is the q-free certificate interface consumed by descent. The current
implementation obtains provenance from `q = 18311`; replacing that backend
does not change this theorem's statement or any downstream proof.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjectionReceipt

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjection
open KummerCriterion
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

/-- Every global `1831`st-power relation lies in the kernel of the intrinsic
Bernoulli-`1274` projection. No auxiliary prime occurs in the statement. -/
theorem projection_eq_zero_of_CPlus_product_mem_powers
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {1831} ℚ K] [NumberField.IsCMField K]
    (s : ℤ) (e : Fin 914 → ℤ)
    (hpow : CPlusExponentProduct (p := 1831) (K := K) (by norm_num) s e ∈
      pPowerSubgroup (EPlus (K := K)) 1831) :
    projection (fun i ↦ (e i : ZMod 1831)) = 0 :=
  Fermat.Certificates.CaseII_1.CircularUnitProjectionReceipt1831AtQ18311.projection_eq_zero_of_CPlus_product_mem_powers
    s e hpow

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjectionReceipt
