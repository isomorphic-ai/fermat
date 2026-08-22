import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk0
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk1
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk2
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk3
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk4
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk5
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk6
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk7
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk8
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk9
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk10
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk11
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Chunk12

/-!
# Balanced assembly of the lifted j=9400 power sum

The thirteen independently checked leaves are joined through a balanced tree
of `partialPowerSum_consecutive` applications.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem partialPowerSum_118562200_zero_2048 :
    partialPowerSum 118562200 0 2048 = 23811940982303176 := by
  calc
    partialPowerSum 118562200 0 2048 =
        partialPowerSum 118562200 0 1024 +
          partialPowerSum 118562200 1024 2048 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 0) (mid := 1024) (hi := 2048)
        (by norm_num) (by norm_num)
    _ = 23811940982303176 := by
      rw [partialPowerSum_118562200_zero_1024,
        partialPowerSum_118562200_1024_2048]
      decide

private theorem partialPowerSum_118562200_2048_4096 :
    partialPowerSum 118562200 2048 4096 = 3063379539801767 := by
  calc
    partialPowerSum 118562200 2048 4096 =
        partialPowerSum 118562200 2048 3072 +
          partialPowerSum 118562200 3072 4096 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 2048) (mid := 3072) (hi := 4096)
        (by norm_num) (by norm_num)
    _ = 3063379539801767 := by
      rw [partialPowerSum_118562200_2048_3072,
        partialPowerSum_118562200_3072_4096]
      decide

private theorem partialPowerSum_118562200_4096_6144 :
    partialPowerSum 118562200 4096 6144 = 20501705254203857 := by
  calc
    partialPowerSum 118562200 4096 6144 =
        partialPowerSum 118562200 4096 5120 +
          partialPowerSum 118562200 5120 6144 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 4096) (mid := 5120) (hi := 6144)
        (by norm_num) (by norm_num)
    _ = 20501705254203857 := by
      rw [partialPowerSum_118562200_4096_5120,
        partialPowerSum_118562200_5120_6144]
      decide

private theorem partialPowerSum_118562200_6144_8192 :
    partialPowerSum 118562200 6144 8192 = 16345633962579549 := by
  calc
    partialPowerSum 118562200 6144 8192 =
        partialPowerSum 118562200 6144 7168 +
          partialPowerSum 118562200 7168 8192 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 6144) (mid := 7168) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 16345633962579549 := by
      rw [partialPowerSum_118562200_6144_7168,
        partialPowerSum_118562200_7168_8192]
      decide

private theorem partialPowerSum_118562200_8192_10240 :
    partialPowerSum 118562200 8192 10240 = 9426600086199431 := by
  calc
    partialPowerSum 118562200 8192 10240 =
        partialPowerSum 118562200 8192 9216 +
          partialPowerSum 118562200 9216 10240 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 8192) (mid := 9216) (hi := 10240)
        (by norm_num) (by norm_num)
    _ = 9426600086199431 := by
      rw [partialPowerSum_118562200_8192_9216,
        partialPowerSum_118562200_9216_10240]
      decide

private theorem partialPowerSum_118562200_10240_12288 :
    partialPowerSum 118562200 10240 12288 = 24427556510117037 := by
  calc
    partialPowerSum 118562200 10240 12288 =
        partialPowerSum 118562200 10240 11264 +
          partialPowerSum 118562200 11264 12288 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 10240) (mid := 11264) (hi := 12288)
        (by norm_num) (by norm_num)
    _ = 24427556510117037 := by
      rw [partialPowerSum_118562200_10240_11264,
        partialPowerSum_118562200_11264_12288]
      decide

private theorem partialPowerSum_118562200_zero_4096 :
    partialPowerSum 118562200 0 4096 = 1566402276707582 := by
  calc
    partialPowerSum 118562200 0 4096 =
        partialPowerSum 118562200 0 2048 +
          partialPowerSum 118562200 2048 4096 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 0) (mid := 2048) (hi := 4096)
        (by norm_num) (by norm_num)
    _ = 1566402276707582 := by
      rw [partialPowerSum_118562200_zero_2048,
        partialPowerSum_118562200_2048_4096]
      decide

private theorem partialPowerSum_118562200_4096_8192 :
    partialPowerSum 118562200 4096 8192 = 11538420971386045 := by
  calc
    partialPowerSum 118562200 4096 8192 =
        partialPowerSum 118562200 4096 6144 +
          partialPowerSum 118562200 6144 8192 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 4096) (mid := 6144) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 11538420971386045 := by
      rw [partialPowerSum_118562200_4096_6144,
        partialPowerSum_118562200_6144_8192]
      decide

private theorem partialPowerSum_118562200_8192_12288 :
    partialPowerSum 118562200 8192 12288 = 8545238350919107 := by
  calc
    partialPowerSum 118562200 8192 12288 =
        partialPowerSum 118562200 8192 10240 +
          partialPowerSum 118562200 10240 12288 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 8192) (mid := 10240) (hi := 12288)
        (by norm_num) (by norm_num)
    _ = 8545238350919107 := by
      rw [partialPowerSum_118562200_8192_10240,
        partialPowerSum_118562200_10240_12288]
      decide

private theorem partialPowerSum_118562200_zero_8192 :
    partialPowerSum 118562200 0 8192 = 13104823248093627 := by
  calc
    partialPowerSum 118562200 0 8192 =
        partialPowerSum 118562200 0 4096 +
          partialPowerSum 118562200 4096 8192 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 0) (mid := 4096) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 13104823248093627 := by
      rw [partialPowerSum_118562200_zero_4096,
        partialPowerSum_118562200_4096_8192]
      decide

private theorem partialPowerSum_118562200_8192_12613 :
    partialPowerSum 118562200 8192 12613 = 18282007735376247 := by
  calc
    partialPowerSum 118562200 8192 12613 =
        partialPowerSum 118562200 8192 12288 +
          partialPowerSum 118562200 12288 12613 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 8192) (mid := 12288) (hi := 12613)
        (by norm_num) (by norm_num)
    _ = 18282007735376247 := by
      rw [partialPowerSum_118562200_8192_12288,
        partialPowerSum_118562200_12288_12613]
      decide

theorem partialPowerSum_118562200_zero_12613 :
    partialPowerSum 118562200 0 12613 = 12613 * 481876852301 := by
  calc
    partialPowerSum 118562200 0 12613 =
        partialPowerSum 118562200 0 8192 +
          partialPowerSum 118562200 8192 12613 := by
      symm
      exact partialPowerSum_consecutive 118562200
        (lo := 0) (mid := 8192) (hi := 12613)
        (by norm_num) (by norm_num)
    _ = 12613 * 481876852301 := by
      rw [partialPowerSum_118562200_zero_8192,
        partialPowerSum_118562200_8192_12613]
      decide

/-- The chunked theorem in the shape consumed by `HighBernoulli`. -/
theorem powerSum_118562200_chunked :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ 118562200) =
        12613 * 481876852301 := by
  calc
    (∑ a ∈ Finset.range 12613,
        (a : ZMod (12613 ^ 4)) ^ 118562200) =
        partialPowerSum 118562200 0 12613 :=
      powerSum_eq_partialPowerSum 118562200
    _ = 12613 * 481876852301 :=
      partialPowerSum_118562200_zero_12613

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
