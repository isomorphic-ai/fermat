import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCore

/-!
# Lifted power-sum block 6 for the j=10536 channel

This certificate covers the half-open interval `[6144, 7168)` in the
`j = 10536` channel, whose lifted exponent is `10536 * 12613 = 132890568`.
The modulus is `12613 ^ 4 = 25308918245397361`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem pow_132890568_eq_bin (a : ZMod (12613 ^ 4)) :
    a ^ 132890568 = npowBinRec 132890568 a := by
  change npowRecAuto 132890568 a = npowBinRecAuto 132890568 a
  rw [npowRec_eq_npowBinRec]

/-- The `[6144, 7168)` block for the lifted `j = 10536` power sum. -/
theorem partialPowerSum_132890568_6144_7168 :
    partialPowerSum 132890568 6144 7168 = 7873857301757688 := by
  unfold partialPowerSum
  simp_rw [pow_132890568_eq_bin]
  decide

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
