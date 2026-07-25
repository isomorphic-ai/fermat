import Fermat.TwelveThousandSixHundredThirteen.PowerSumCore

/-!
# Lifted power-sum block 11 for the j=9400 channel

This certificate covers the half-open interval `[11264, 12288)` in the
`j = 9400` channel, whose lifted exponent is `9400 * 12613 = 118562200`.
The modulus is `12613 ^ 4 = 25308918245397361`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem pow_118562200_eq_bin (a : ZMod (12613 ^ 4)) :
    a ^ 118562200 = npowBinRec 118562200 a := by
  change npowRecAuto 118562200 a = npowBinRecAuto 118562200 a
  rw [npowRec_eq_npowBinRec]

/-- The `[11264, 12288)` block for the lifted `j = 9400` power sum. -/
theorem partialPowerSum_118562200_11264_12288 :
    partialPowerSum 118562200 11264 12288 = 9979857156462637 := by
  unfold partialPowerSum
  simp_rw [pow_118562200_eq_bin]
  decide

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
