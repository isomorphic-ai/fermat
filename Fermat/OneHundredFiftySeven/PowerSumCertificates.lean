import Fermat.Basic

/-!
# Modular power sums for the exponent-157 correction channels

These are the two expensive but finite inputs to the shared direct-Faulhaber
endpoint.  They live separately from the structural folds so clients that
only inspect the seven-fold trace do not need to elaborate the modular sums.
-/

namespace Fermat.OneHundredFiftySeven.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Kernel evaluation of the ordinary power can be linear in the exponent.
This certified rewrite selects Mathlib's propositionally equal
repeated-squaring implementation. -/
private theorem pow_9734_eq_bin (a : ZMod (157 ^ 4)) :
    a ^ 9734 = npowBinRec 9734 a := by
  change npowRecAuto 9734 a = npowBinRecAuto 9734 a
  rw [npowRec_eq_npowBinRec]

private theorem pow_17270_eq_bin (a : ZMod (157 ^ 4)) :
    a ^ 17270 = npowBinRec 17270 a := by
  change npowRecAuto 17270 a = npowBinRecAuto 17270 a
  rw [npowRec_eq_npowBinRec]

/-- The `r = 62` power-sum certificate modulo `157⁴`. -/
theorem powerSum_9734 :
    (∑ a ∈ Finset.range 157, (a : ZMod (157 ^ 4)) ^ 9734) =
      157 * 73947 := by
  simp_rw [pow_9734_eq_bin]
  decide

/-- The `r = 110` power-sum certificate modulo `157⁴`. -/
theorem powerSum_17270 :
    (∑ a ∈ Finset.range 157, (a : ZMod (157 ^ 4)) ^ 17270) =
      157 * 394384 := by
  simp_rw [pow_17270_eq_bin]
  decide

theorem correctionQuotients :
    73947 = 157 ^ 2 * 3 ∧ 394384 = 157 ^ 2 * 16 := by
  norm_num

theorem correctionQuotients_not_dvd_cube :
    ¬(157 : ℤ) ^ 3 ∣ (73947 : ℤ) ∧
      ¬(157 : ℤ) ^ 3 ∣ (394384 : ℤ) := by
  norm_num

end Fermat.OneHundredFiftySeven.PowerSumCertificates
