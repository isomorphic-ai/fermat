import Fermat.Basic

/-!
# Modular power sum for the exponent-1381 Bernoulli channel

This is the finite input at the irregular index `266`.  Repeated squaring
keeps kernel evaluation logarithmic in the lifted exponent.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem pow_367346_eq_bin (a : ZMod (1381 ^ 4)) :
    a ^ 367346 = npowBinRec 367346 a := by
  change npowRecAuto 367346 a = npowBinRecAuto 367346 a
  rw [npowRec_eq_npowBinRec]

/-- The lifted `j = 266` power-sum certificate modulo `1381⁴`. -/
theorem powerSum_367346 :
    (∑ a ∈ Finset.range 1381, (a : ZMod (1381 ^ 4)) ^ 367346) =
      1381 * 1069917321 := by
  simp_rw [pow_367346_eq_bin]
  decide

/-- The nonzero correction is exactly `561 * 1381²`. -/
theorem correctionQuotient :
    1069917321 = 1381 ^ 2 * 561 := by
  norm_num

theorem correctionQuotient_not_dvd_cube :
    ¬(1381 : ℤ) ^ 3 ∣ (1069917321 : ℤ) := by
  norm_num

end Fermat.OneThousandThreeHundredEightyOne.PowerSumCertificates
