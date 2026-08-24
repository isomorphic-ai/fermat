import Fermat.Certificates.CaseII_1.CircularUnitProjectionReceipt1831
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannelsIntrinsic

/-!
# Normalized selective Case-II.1 route at exponent 1831

This one-line assembly selects an authenticated backend for the q-free
intrinsic projection receipt. The downstream saturation theorem contains no
auxiliary prime; changing provenance changes only the theorem supplied here.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannelsNormalized

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular.CircularUnitFamily
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjectionReceipt
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannelsIntrinsic
open KummerCriterion
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (p := 1831) (K := K) (by decide) (by norm_num)

/-- The normalized projection receipt makes the real cyclotomic-unit
subgroup `1831`-saturated. -/
theorem CPlus_pSaturated_channels :
    pSaturated
      (CPlus (p := 1831) (K := K) (by norm_num))
      (EPlus (K := K)) 1831 :=
  CPlus_pSaturated_of_projection_receipt
    projection_eq_zero_of_CPlus_product_mem_powers

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannelsNormalized
