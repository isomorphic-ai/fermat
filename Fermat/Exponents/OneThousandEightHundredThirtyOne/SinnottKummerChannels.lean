import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels
import KummerCriterion.CyclotomicUnits.SaturationIndex

/-!
# Selective Sinnott--Kummer endpoint for exponent 1831

This independent endpoint converts the one-channel circular-unit saturation
theorem into plus-class-number nondivisibility. It leaves the legacy full
residue-matrix route unchanged and does not import its determinant receipt.
-/

open scoped NumberField

namespace Fermat.OneThousandEightHundredThirtyOne.SinnottKummerChannels

noncomputable section

set_option maxHeartbeats 0

open Fermat.Irregular.CircularUnitFamily
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitResiduesChannels
open KummerCriterion

variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {1831} ℚ K]

local instance : Fact (Nat.Prime 1831) :=
  ⟨Fermat.OneThousandEightHundredThirtyOne.prime_1831⟩
local instance : NumberField.IsCMField K :=
  cyclotomicPrime_isCMField (p := 1831) (K := K)
    Fermat.OneThousandEightHundredThirtyOne.prime_1831 (by norm_num)

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Selective saturation makes the squared real cyclotomic-unit index prime
to `1831`. -/
theorem not_dvd_CPlus_index :
    ¬1831 ∣ (CPlus (p := 1831) (K := K) (by norm_num)).index :=
  not_dvd_index_of_pSaturated (p := 1831) (K := K) (by norm_num)
    CPlus_pSaturated_channels

/-- The p-primary Sinnott index formula transports the selective result to
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

/-- The plus class number is prime to `1831`, using only the single
frequency-278 detector on the finite residue side. -/
theorem not_dvd_classNumber :
    ¬1831 ∣ NumberField.classNumber K⁺ := by
  simpa [hPlus, NumberField.classNumber] using not_dvd_hPlus (K := K)

end

end Fermat.OneThousandEightHundredThirtyOne.SinnottKummerChannels
