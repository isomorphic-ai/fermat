import Fermat.Descent.Irregular.SelectiveCircularUnitResidues
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitProjection1831

/-!
# Intrinsic 1831 projection receipt from q = 18311

The auxiliary residue certificate at `q = 18311` is used only as provenance
for the q-free conclusion that every global `1831`st-power relation is
annihilated by the intrinsic Bernoulli-`1274` projection.
-/

namespace Fermat.Certificates.CaseII_1.CircularUnitProjectionReceipt1831AtQ18311

noncomputable section

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SelectiveCircularUnitResidues
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitChannelAtQ18311
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjection
open KummerCriterion
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 18311) := ⟨by norm_num⟩

/-- The normalized intrinsic projection annihilates every plus-side power
relation. The theorem statement contains no auxiliary prime or residue
certificate. -/
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

end Fermat.Certificates.CaseII_1.CircularUnitProjectionReceipt1831AtQ18311
