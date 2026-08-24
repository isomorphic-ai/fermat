import Fermat.Certificates.CaseII_1.IrregularSupport1831
import Fermat.Descent.Irregular.CircularUnitFamily
import Fermat.Descent.Irregular.SelectiveKummerSaturation
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitProjection1831

/-!
# Intrinsic selective Case-II.1 route at exponent 1831

The descent consumes only two p-side facts: the complete Bernoulli support
and a normalized theorem that every power relation is annihilated by the
canonical row `636`. The latter is an explicit theorem argument, so this
module has no auxiliary-prime provenance dependency at all.
-/

open scoped Matrix NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannelsIntrinsic

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular.CircularUnitFamily
open Fermat.Irregular.SelectiveKummerSaturation
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitProjection
open Fermat.OneThousandEightHundredThirtyOne.IrregularSupport
open KummerCriterion
open KummerCriterion.CyclotomicUnits

local instance : Fact (Nat.Prime 1831) := ⟨by norm_num⟩

/-- The sole possibly irregular Kummer row. -/
def exceptionalRow (j : Fin (kummerLogRank 1831)) : Prop :=
  j = irregularKummerRow

/-- The low scan confines every Bernoulli-divisible Kummer row to row 636. -/
theorem bernoulli_support (j : Fin (kummerLogRank 1831))
    (hdiv : (1831 : ℤ) ∣
      (bernoulli (2 * kummerLogRowIndex (p := 1831) j)).num) :
    exceptionalRow j := by
  have hmem : 2 * kummerLogRowIndex (p := 1831) j ∈
      Fermat.Irregular.VandiverData.indices 1831 := by
    simp only [Fermat.Irregular.VandiverData.indices,
      Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by
      have := kummerLogRowIndex_one_le (p := 1831) j
      omega, by
      simpa using
        two_mul_kummerLogRowIndex_le_sub_three (p := 1831) j⟩,
      even_two_mul _⟩
  have hindex := irregular_index_eq_1274
    (2 * kummerLogRowIndex (p := 1831) j) hmem hdiv
  unfold exceptionalRow
  apply Fin.ext
  change j.val = 636
  change 2 * (j.val + 1) = 1274 at hindex
  omega

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (p := 1831) (K := K) (by decide) (by norm_num)

/-- Any proof that global power relations lie in the normalized irregular
projection kernel combines with the regular Kummer rows to prove saturation.
This is the q-free consumer boundary. -/
theorem CPlus_pSaturated_of_projection_receipt
    (hprojection : ∀ (s : ℤ) (e : Fin 914 → ℤ),
      CPlusExponentProduct (p := 1831) (K := K) (by norm_num) s e ∈
          pPowerSubgroup (EPlus (K := K)) 1831 →
        projection (fun i ↦ (e i : ZMod 1831)) = 0) :
    pSaturated
      (CPlus (p := 1831) (K := K) (by norm_num))
      (EPlus (K := K)) 1831 := by
  apply CPlus_pSaturated_of_irregular_support_kummer_rows
    (p := 1831) (K := K) (by norm_num) (by norm_num)
    exceptionalRow bernoulli_support
  intro s e hpow j hj
  subst j
  exact hprojection s e hpow

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannelsIntrinsic
