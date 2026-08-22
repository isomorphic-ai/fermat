import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCore

/-!
# Lifted power-sum block 8 for the j=502 channel

This certificate covers the half-open interval `[8192, 9216)` in the
`j = 502` channel, whose lifted exponent is `502 * 12613 = 6331726`.
The modulus is `12613 ^ 4 = 25308918245397361`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem pow_6331726_eq_bin (a : ZMod (12613 ^ 4)) :
    a ^ 6331726 = npowBinRec 6331726 a := by
  change npowRecAuto 6331726 a = npowBinRecAuto 6331726 a
  rw [npowRec_eq_npowBinRec]

/-- The `[8192, 9216)` block for the lifted `j = 502` power sum. -/
theorem partialPowerSum_6331726_8192_9216 :
    partialPowerSum 6331726 8192 9216 = 1696250384256957 := by
  unfold partialPowerSum
  simp_rw [pow_6331726_eq_bin]
  decide

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
