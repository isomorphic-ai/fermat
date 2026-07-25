import Fermat.TwelveThousandSixHundredThirteen.PowerSumCore

/-!
# Lifted power-sum block 11 at exponent 12613

This certificate covers the half-open interval `[11264, 12288)` in the
`j = 308` channel, whose lifted exponent is `308 * 12613 = 3884804`.
The modulus is `12613 ^ 4 = 25308918245397361`.

It is leaf 11 in the bounded-memory partition of
`partialPowerSum 3884804 0 12613`.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem pow_3884804_eq_bin (a : ZMod (12613 ^ 4)) :
    a ^ 3884804 = npowBinRec 3884804 a := by
  change npowRecAuto 3884804 a = npowBinRecAuto 3884804 a
  rw [npowRec_eq_npowBinRec]

/-- The `[11264, 12288)` block for the lifted `j = 308` power sum, modulo
`12613 ^ 4 = 25308918245397361`. -/
theorem partialPowerSum_3884804_11264_12288 :
    partialPowerSum 3884804 11264 12288 = 6172294921349104 := by
  unfold partialPowerSum
  simp_rw [pow_3884804_eq_bin]
  decide

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
