import Fermat.Basic

/-!
# Modular power sum for the exponent-1831 Bernoulli channel

This is the finite input at the irregular index `1274`.  Repeated squaring
keeps kernel evaluation logarithmic in the lifted exponent.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem pow_2332694_eq_bin (a : ZMod (1831 ^ 4)) :
    a ^ 2332694 = npowBinRec 2332694 a := by
  change npowRecAuto 2332694 a = npowBinRecAuto 2332694 a
  rw [npowRec_eq_npowBinRec]

/-- The lifted `j = 1274` power-sum certificate modulo `1831⁴`. -/
theorem powerSum_2332694 :
    (∑ a ∈ Finset.range 1831, (a : ZMod (1831 ^ 4)) ^ 2332694) =
      1831 * 4975200524 := by
  simp_rw [pow_2332694_eq_bin]
  decide

/-- The nonzero correction is exactly `1484 * 1831²`. -/
theorem correctionQuotient :
    4975200524 = 1831 ^ 2 * 1484 := by
  norm_num

theorem correctionQuotient_not_dvd_cube :
    ¬(1831 : ℤ) ^ 3 ∣ (4975200524 : ℤ) := by
  norm_num

end Fermat.OneThousandEightHundredThirtyOne.PowerSumCertificates
