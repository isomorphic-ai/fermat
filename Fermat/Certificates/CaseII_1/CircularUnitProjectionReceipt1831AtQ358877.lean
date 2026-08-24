import Fermat.Descent.Irregular.SelectiveCircularUnitResidues
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitProjection1831

/-!
# Intrinsic 1831 projection receipt from q = 358877

The original auxiliary residue certificate at `q = 358877` produces the
same q-free Bernoulli-`1274` projection theorem as the smaller auxiliary
prime. This module is an interchangeable provenance backend.
-/

namespace Fermat.Certificates.CaseII_1.CircularUnitProjectionReceipt1831AtQ358877

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SelectiveCircularUnitResidues
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ358877
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjection
open KummerCriterion
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 358877) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_358877⟩

/-- The normalized intrinsic projection annihilates every plus-side power
relation. Its statement is identical to the q=18311 receipt. -/
theorem projection_eq_zero_of_CPlus_product_mem_powers
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {1831} ℚ K] [NumberField.IsCMField K]
    (s : ℤ) (e : Fin 914 → ℤ)
    (hpow : CPlusExponentProduct (p := 1831) (K := K) (by norm_num) s e ∈
      pPowerSubgroup (EPlus (K := K)) 1831) :
    projection (fun i ↦ (e i : ZMod 1831)) = 0 := by
  have hscalar :
      (factorization irregularKummerRow).scalar ≠ 0 := by
    change
      (factorization
        Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelCoordinates.irregularKummerRow).scalar ≠ 0
    rw [irregular_scalar_eq]
    decide
  exact canonicalKummerChannel_exponents_eq_zero_of_CPlus_product_mem_powers
    (K := K) QCertificate.certificate (by norm_num)
    (factorization irregularKummerRow) hscalar s e hpow

end

end Fermat.Certificates.CaseII_1.CircularUnitProjectionReceipt1831AtQ358877
