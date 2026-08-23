import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311
import KummerCriterion.CyclotomicUnits.SaturationIndex

/-!
# Selective Sinnott--Kummer endpoint at q = 18311

This endpoint converts the alternate `q = 18311` one-channel saturation
theorem into plus-class-number nondivisibility. Its residue matrix is singular,
so this proof cannot pass through the old full-determinant premise.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.SinnottKummerChannels18311

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Fermat.Irregular.CircularUnitFamily
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels18311
open KummerCriterion

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : Fact (Nat.Prime 1831) := ⟨by decide⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (p := 1831) (K := K) (by decide) (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The q=18311 selective saturation result makes the squared real
cyclotomic-unit index prime to `1831`. -/
theorem not_dvd_CPlus_index :
    ¬1831 ∣ (CPlus (p := 1831) (K := K) (by norm_num)).index :=
  not_dvd_index_of_pSaturated (p := 1831) (K := K) (by norm_num)
    CPlus_pSaturated_channels

/-- The p-primary Sinnott index formula transports the q=18311 result to
the plus class number. -/
theorem not_dvd_hPlus : ¬1831 ∣ hPlus K := by
  intro hdiv
  apply not_dvd_CPlus_index (K := K)
  have hnormalized :
      1831 ∣ (normalizedCPlus (p := 1831) (K := K)
        (by norm_num) (by norm_num)).index :=
    (cyclotomicUnitIndex_primeConductor_pPrimary
      (p := 1831) (K := K) (by norm_num)).mpr hdiv
  exact (CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd
    (p := 1831) (K := K) (by norm_num) (by norm_num)).mpr hnormalized

/-- The plus class number is prime to `1831`, proved with the singular
q=18311 residue matrix and only its frequency-278 detector. -/
theorem not_dvd_classNumber :
    ¬1831 ∣ NumberField.classNumber K⁺ := by
  simpa [hPlus, NumberField.classNumber] using not_dvd_hPlus (K := K)

end

end Fermat.OneThousandEightHundredThirtyOne.SinnottKummerChannels18311
