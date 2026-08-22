import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCore

/-!
# Lifted power-sum block 1 for the j=9400 channel

This certificate covers the half-open interval `[1024, 2048)` in the
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

/-- The `[1024, 2048)` block for the lifted `j = 9400` power sum. -/
theorem partialPowerSum_118562200_1024_2048 :
    partialPowerSum 118562200 1024 2048 = 23488534467565921 := by
  unfold partialPowerSum
  simp_rw [pow_118562200_eq_bin]
  decide

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
