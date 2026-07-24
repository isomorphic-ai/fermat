import Fermat.Basic

/-!
# Modular power sums for the exponent-587 Bernoulli channels

These are the two finite inputs at the irregular indices `90` and `92`.
Repeated squaring keeps kernel evaluation logarithmic in the large
exponents.
-/

namespace Fermat.FiveHundredEightySeven.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem pow_52830_eq_bin (a : ZMod (587 ^ 4)) :
    a ^ 52830 = npowBinRec 52830 a := by
  change npowRecAuto 52830 a = npowBinRecAuto 52830 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_54004_eq_bin (a : ZMod (587 ^ 4)) :
    a ^ 54004 = npowBinRec 54004 a := by
  change npowRecAuto 54004 a = npowBinRecAuto 54004 a
  rw [npowRec_eq_npowBinRec]

/-- The lifted `r = 90` power-sum certificate modulo `587⁴`. -/
theorem powerSum_52830 :
    (∑ a ∈ Finset.range 587, (a : ZMod (587 ^ 4)) ^ 52830) =
      587 * 171595362 := by
  simp_rw [pow_52830_eq_bin]
  decide

/-- The lifted `r = 92` power-sum certificate modulo `587⁴`. -/
theorem powerSum_54004 :
    (∑ a ∈ Finset.range 587, (a : ZMod (587 ^ 4)) ^ 54004) =
      587 * 83385698 := by
  simp_rw [pow_54004_eq_bin]
  decide

theorem correctionQuotients :
    171595362 = 587 ^ 2 * 498 ∧
      83385698 = 587 ^ 2 * 242 := by
  norm_num

theorem correctionQuotients_not_dvd_cube :
    ¬(587 : ℤ) ^ 3 ∣ (171595362 : ℤ) ∧
      ¬(587 : ℤ) ^ 3 ∣ (83385698 : ℤ) := by
  norm_num

end Fermat.FiveHundredEightySeven.PowerSumCertificates
