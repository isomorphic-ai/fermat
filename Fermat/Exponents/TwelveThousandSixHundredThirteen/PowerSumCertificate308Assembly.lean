import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk0
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk1
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk2
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk3
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk4
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk5
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk6
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk7
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk8
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk9
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk10
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk11
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Chunk12

/-!
# Balanced assembly of the lifted j=308 power sum

The committed `[0, 1024)` pilot and the twelve generated leaves are joined
through a balanced tree of `partialPowerSum_consecutive` applications.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem partialPowerSum_3884804_zero_2048 :
    partialPowerSum 3884804 0 2048 = 12121968159209313 := by
  calc
    partialPowerSum 3884804 0 2048 =
        partialPowerSum 3884804 0 1024 +
          partialPowerSum 3884804 1024 2048 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 0) (mid := 1024) (hi := 2048)
        (by norm_num) (by norm_num)
    _ = 12121968159209313 := by
      rw [partialPowerSum_3884804_zero_1024,
        partialPowerSum_3884804_1024_2048]
      decide

private theorem partialPowerSum_3884804_2048_4096 :
    partialPowerSum 3884804 2048 4096 = 20900404458671543 := by
  calc
    partialPowerSum 3884804 2048 4096 =
        partialPowerSum 3884804 2048 3072 +
          partialPowerSum 3884804 3072 4096 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 2048) (mid := 3072) (hi := 4096)
        (by norm_num) (by norm_num)
    _ = 20900404458671543 := by
      rw [partialPowerSum_3884804_2048_3072,
        partialPowerSum_3884804_3072_4096]
      decide

private theorem partialPowerSum_3884804_4096_6144 :
    partialPowerSum 3884804 4096 6144 = 22814005712957759 := by
  calc
    partialPowerSum 3884804 4096 6144 =
        partialPowerSum 3884804 4096 5120 +
          partialPowerSum 3884804 5120 6144 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 4096) (mid := 5120) (hi := 6144)
        (by norm_num) (by norm_num)
    _ = 22814005712957759 := by
      rw [partialPowerSum_3884804_4096_5120,
        partialPowerSum_3884804_5120_6144]
      decide

private theorem partialPowerSum_3884804_6144_8192 :
    partialPowerSum 3884804 6144 8192 = 1745133776186198 := by
  calc
    partialPowerSum 3884804 6144 8192 =
        partialPowerSum 3884804 6144 7168 +
          partialPowerSum 3884804 7168 8192 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 6144) (mid := 7168) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 1745133776186198 := by
      rw [partialPowerSum_3884804_6144_7168,
        partialPowerSum_3884804_7168_8192]
      decide

private theorem partialPowerSum_3884804_8192_10240 :
    partialPowerSum 3884804 8192 10240 = 10605061711087582 := by
  calc
    partialPowerSum 3884804 8192 10240 =
        partialPowerSum 3884804 8192 9216 +
          partialPowerSum 3884804 9216 10240 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 8192) (mid := 9216) (hi := 10240)
        (by norm_num) (by norm_num)
    _ = 10605061711087582 := by
      rw [partialPowerSum_3884804_8192_9216,
        partialPowerSum_3884804_9216_10240]
      decide

private theorem partialPowerSum_3884804_10240_12288 :
    partialPowerSum 3884804 10240 12288 = 23537229792696750 := by
  calc
    partialPowerSum 3884804 10240 12288 =
        partialPowerSum 3884804 10240 11264 +
          partialPowerSum 3884804 11264 12288 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 10240) (mid := 11264) (hi := 12288)
        (by norm_num) (by norm_num)
    _ = 23537229792696750 := by
      rw [partialPowerSum_3884804_10240_11264,
        partialPowerSum_3884804_11264_12288]
      decide

private theorem partialPowerSum_3884804_zero_4096 :
    partialPowerSum 3884804 0 4096 = 7713454372483495 := by
  calc
    partialPowerSum 3884804 0 4096 =
        partialPowerSum 3884804 0 2048 +
          partialPowerSum 3884804 2048 4096 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 0) (mid := 2048) (hi := 4096)
        (by norm_num) (by norm_num)
    _ = 7713454372483495 := by
      rw [partialPowerSum_3884804_zero_2048,
        partialPowerSum_3884804_2048_4096]
      decide

private theorem partialPowerSum_3884804_4096_8192 :
    partialPowerSum 3884804 4096 8192 = 24559139489143957 := by
  calc
    partialPowerSum 3884804 4096 8192 =
        partialPowerSum 3884804 4096 6144 +
          partialPowerSum 3884804 6144 8192 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 4096) (mid := 6144) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 24559139489143957 := by
      rw [partialPowerSum_3884804_4096_6144,
        partialPowerSum_3884804_6144_8192]
      decide

private theorem partialPowerSum_3884804_8192_12288 :
    partialPowerSum 3884804 8192 12288 = 8833373258386971 := by
  calc
    partialPowerSum 3884804 8192 12288 =
        partialPowerSum 3884804 8192 10240 +
          partialPowerSum 3884804 10240 12288 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 8192) (mid := 10240) (hi := 12288)
        (by norm_num) (by norm_num)
    _ = 8833373258386971 := by
      rw [partialPowerSum_3884804_8192_10240,
        partialPowerSum_3884804_10240_12288]
      decide

private theorem partialPowerSum_3884804_zero_8192 :
    partialPowerSum 3884804 0 8192 = 6963675616230091 := by
  calc
    partialPowerSum 3884804 0 8192 =
        partialPowerSum 3884804 0 4096 +
          partialPowerSum 3884804 4096 8192 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 0) (mid := 4096) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 6963675616230091 := by
      rw [partialPowerSum_3884804_zero_4096,
        partialPowerSum_3884804_4096_8192]
      decide

private theorem partialPowerSum_3884804_8192_12613 :
    partialPowerSum 3884804 8192 12613 = 23540262793865103 := by
  calc
    partialPowerSum 3884804 8192 12613 =
        partialPowerSum 3884804 8192 12288 +
          partialPowerSum 3884804 12288 12613 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 8192) (mid := 12288) (hi := 12613)
        (by norm_num) (by norm_num)
    _ = 23540262793865103 := by
      rw [partialPowerSum_3884804_8192_12288,
        partialPowerSum_3884804_12288_12613]
      decide

theorem partialPowerSum_3884804_zero_12613 :
    partialPowerSum 3884804 0 12613 = 12613 * 411878233941 := by
  calc
    partialPowerSum 3884804 0 12613 =
        partialPowerSum 3884804 0 8192 +
          partialPowerSum 3884804 8192 12613 := by
      symm
      exact partialPowerSum_consecutive 3884804
        (lo := 0) (mid := 8192) (hi := 12613)
        (by norm_num) (by norm_num)
    _ = 12613 * 411878233941 := by
      rw [partialPowerSum_3884804_zero_8192,
        partialPowerSum_3884804_8192_12613]
      decide

/-- The chunked theorem in the shape consumed by `HighBernoulli`. -/
theorem powerSum_3884804_chunked :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ 3884804) =
        12613 * 411878233941 := by
  calc
    (∑ a ∈ Finset.range 12613,
        (a : ZMod (12613 ^ 4)) ^ 3884804) =
        partialPowerSum 3884804 0 12613 :=
      powerSum_eq_partialPowerSum 3884804
    _ = 12613 * 411878233941 :=
      partialPowerSum_3884804_zero_12613

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
