import Fermat.Core.Basic

/-!
# Modular power sums for the exponent-12613 Bernoulli channels

The paired finite package reports four irregular indices.  Their lifted
indices are

* `308 * 12613 = 3884804`,
* `502 * 12613 = 6331726`,
* `9400 * 12613 = 118562200`, and
* `10536 * 12613 = 132890568`.

The four computations below retain the package residues modulo `12613⁴`.
Repeated squaring keeps evaluation logarithmic in the lifted exponent.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem pow_3884804_eq_bin (a : ZMod (12613 ^ 4)) :
    a ^ 3884804 = npowBinRec 3884804 a := by
  change npowRecAuto 3884804 a = npowBinRecAuto 3884804 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_6331726_eq_bin (a : ZMod (12613 ^ 4)) :
    a ^ 6331726 = npowBinRec 6331726 a := by
  change npowRecAuto 6331726 a = npowBinRecAuto 6331726 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_118562200_eq_bin (a : ZMod (12613 ^ 4)) :
    a ^ 118562200 = npowBinRec 118562200 a := by
  change npowRecAuto 118562200 a = npowBinRecAuto 118562200 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_132890568_eq_bin (a : ZMod (12613 ^ 4)) :
    a ^ 132890568 = npowBinRec 132890568 a := by
  change npowRecAuto 132890568 a = npowBinRecAuto 132890568 a
  rw [npowRec_eq_npowBinRec]

/-- The lifted `j = 308` power-sum certificate modulo `12613⁴`. -/
theorem powerSum_3884804 :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ 3884804) =
        12613 * 411878233941 := by
  simp_rw [pow_3884804_eq_bin]
  decide

/-- The lifted `j = 502` power-sum certificate modulo `12613⁴`. -/
theorem powerSum_6331726 :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ 6331726) =
        12613 * 1858463317458 := by
  simp_rw [pow_6331726_eq_bin]
  decide

/-- The lifted `j = 9400` power-sum certificate modulo `12613⁴`. -/
theorem powerSum_118562200 :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ 118562200) =
        12613 * 481876852301 := by
  simp_rw [pow_118562200_eq_bin]
  decide

/-- The lifted `j = 10536` power-sum certificate modulo `12613⁴`. -/
theorem powerSum_132890568 :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ 132890568) =
        12613 * 147951625170 := by
  simp_rw [pow_132890568_eq_bin]
  decide

theorem correctionQuotient_3884804 :
    411878233941 = 12613 ^ 2 * 2589 := by
  norm_num

theorem correctionQuotient_6331726 :
    1858463317458 = 12613 ^ 2 * 11682 := by
  norm_num

theorem correctionQuotient_118562200 :
    481876852301 = 12613 ^ 2 * 3029 := by
  norm_num

theorem correctionQuotient_132890568 :
    147951625170 = 12613 ^ 2 * 930 := by
  norm_num

theorem correctionQuotient_3884804_not_dvd_cube :
    ¬(12613 : ℤ) ^ 3 ∣ (411878233941 : ℤ) := by
  norm_num

theorem correctionQuotient_6331726_not_dvd_cube :
    ¬(12613 : ℤ) ^ 3 ∣ (1858463317458 : ℤ) := by
  norm_num

theorem correctionQuotient_118562200_not_dvd_cube :
    ¬(12613 : ℤ) ^ 3 ∣ (481876852301 : ℤ) := by
  norm_num

theorem correctionQuotient_132890568_not_dvd_cube :
    ¬(12613 : ℤ) ^ 3 ∣ (147951625170 : ℤ) := by
  norm_num

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
