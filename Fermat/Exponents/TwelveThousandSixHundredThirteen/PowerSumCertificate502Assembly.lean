import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk0
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk1
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk2
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk3
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk4
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk5
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk6
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk7
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk8
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk9
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk10
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk11
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Chunk12

/-!
# Balanced assembly of the lifted j=502 power sum

The thirteen independently checked leaves are joined through a balanced tree
of `partialPowerSum_consecutive` applications.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem partialPowerSum_6331726_zero_2048 :
    partialPowerSum 6331726 0 2048 = 18460870412333544 := by
  calc
    partialPowerSum 6331726 0 2048 =
        partialPowerSum 6331726 0 1024 +
          partialPowerSum 6331726 1024 2048 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 0) (mid := 1024) (hi := 2048)
        (by norm_num) (by norm_num)
    _ = 18460870412333544 := by
      rw [partialPowerSum_6331726_zero_1024,
        partialPowerSum_6331726_1024_2048]
      decide

private theorem partialPowerSum_6331726_2048_4096 :
    partialPowerSum 6331726 2048 4096 = 4815153493654200 := by
  calc
    partialPowerSum 6331726 2048 4096 =
        partialPowerSum 6331726 2048 3072 +
          partialPowerSum 6331726 3072 4096 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 2048) (mid := 3072) (hi := 4096)
        (by norm_num) (by norm_num)
    _ = 4815153493654200 := by
      rw [partialPowerSum_6331726_2048_3072,
        partialPowerSum_6331726_3072_4096]
      decide

private theorem partialPowerSum_6331726_4096_6144 :
    partialPowerSum 6331726 4096 6144 = 9053257720778870 := by
  calc
    partialPowerSum 6331726 4096 6144 =
        partialPowerSum 6331726 4096 5120 +
          partialPowerSum 6331726 5120 6144 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 4096) (mid := 5120) (hi := 6144)
        (by norm_num) (by norm_num)
    _ = 9053257720778870 := by
      rw [partialPowerSum_6331726_4096_5120,
        partialPowerSum_6331726_5120_6144]
      decide

private theorem partialPowerSum_6331726_6144_8192 :
    partialPowerSum 6331726 6144 8192 = 7246837898541963 := by
  calc
    partialPowerSum 6331726 6144 8192 =
        partialPowerSum 6331726 6144 7168 +
          partialPowerSum 6331726 7168 8192 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 6144) (mid := 7168) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 7246837898541963 := by
      rw [partialPowerSum_6331726_6144_7168,
        partialPowerSum_6331726_7168_8192]
      decide

private theorem partialPowerSum_6331726_8192_10240 :
    partialPowerSum 6331726 8192 10240 = 13799843969587120 := by
  calc
    partialPowerSum 6331726 8192 10240 =
        partialPowerSum 6331726 8192 9216 +
          partialPowerSum 6331726 9216 10240 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 8192) (mid := 9216) (hi := 10240)
        (by norm_num) (by norm_num)
    _ = 13799843969587120 := by
      rw [partialPowerSum_6331726_8192_9216,
        partialPowerSum_6331726_9216_10240]
      decide

private theorem partialPowerSum_6331726_10240_12288 :
    partialPowerSum 6331726 10240 12288 = 12625218805551547 := by
  calc
    partialPowerSum 6331726 10240 12288 =
        partialPowerSum 6331726 10240 11264 +
          partialPowerSum 6331726 11264 12288 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 10240) (mid := 11264) (hi := 12288)
        (by norm_num) (by norm_num)
    _ = 12625218805551547 := by
      rw [partialPowerSum_6331726_10240_11264,
        partialPowerSum_6331726_11264_12288]
      decide

private theorem partialPowerSum_6331726_zero_4096 :
    partialPowerSum 6331726 0 4096 = 23276023905987744 := by
  calc
    partialPowerSum 6331726 0 4096 =
        partialPowerSum 6331726 0 2048 +
          partialPowerSum 6331726 2048 4096 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 0) (mid := 2048) (hi := 4096)
        (by norm_num) (by norm_num)
    _ = 23276023905987744 := by
      rw [partialPowerSum_6331726_zero_2048,
        partialPowerSum_6331726_2048_4096]
      decide

private theorem partialPowerSum_6331726_4096_8192 :
    partialPowerSum 6331726 4096 8192 = 16300095619320833 := by
  calc
    partialPowerSum 6331726 4096 8192 =
        partialPowerSum 6331726 4096 6144 +
          partialPowerSum 6331726 6144 8192 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 4096) (mid := 6144) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 16300095619320833 := by
      rw [partialPowerSum_6331726_4096_6144,
        partialPowerSum_6331726_6144_8192]
      decide

private theorem partialPowerSum_6331726_8192_12288 :
    partialPowerSum 6331726 8192 12288 = 1116144529741306 := by
  calc
    partialPowerSum 6331726 8192 12288 =
        partialPowerSum 6331726 8192 10240 +
          partialPowerSum 6331726 10240 12288 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 8192) (mid := 10240) (hi := 12288)
        (by norm_num) (by norm_num)
    _ = 1116144529741306 := by
      rw [partialPowerSum_6331726_8192_10240,
        partialPowerSum_6331726_10240_12288]
      decide

private theorem partialPowerSum_6331726_zero_8192 :
    partialPowerSum 6331726 0 8192 = 14267201279911216 := by
  calc
    partialPowerSum 6331726 0 8192 =
        partialPowerSum 6331726 0 4096 +
          partialPowerSum 6331726 4096 8192 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 0) (mid := 4096) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 14267201279911216 := by
      rw [partialPowerSum_6331726_zero_4096,
        partialPowerSum_6331726_4096_8192]
      decide

private theorem partialPowerSum_6331726_8192_12613 :
    partialPowerSum 6331726 8192 12613 = 9173596543186538 := by
  calc
    partialPowerSum 6331726 8192 12613 =
        partialPowerSum 6331726 8192 12288 +
          partialPowerSum 6331726 12288 12613 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 8192) (mid := 12288) (hi := 12613)
        (by norm_num) (by norm_num)
    _ = 9173596543186538 := by
      rw [partialPowerSum_6331726_8192_12288,
        partialPowerSum_6331726_12288_12613]
      decide

theorem partialPowerSum_6331726_zero_12613 :
    partialPowerSum 6331726 0 12613 = 12613 * 1858463317458 := by
  calc
    partialPowerSum 6331726 0 12613 =
        partialPowerSum 6331726 0 8192 +
          partialPowerSum 6331726 8192 12613 := by
      symm
      exact partialPowerSum_consecutive 6331726
        (lo := 0) (mid := 8192) (hi := 12613)
        (by norm_num) (by norm_num)
    _ = 12613 * 1858463317458 := by
      rw [partialPowerSum_6331726_zero_8192,
        partialPowerSum_6331726_8192_12613]
      decide

/-- The chunked theorem in the shape consumed by `HighBernoulli`. -/
theorem powerSum_6331726_chunked :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ 6331726) =
        12613 * 1858463317458 := by
  calc
    (∑ a ∈ Finset.range 12613,
        (a : ZMod (12613 ^ 4)) ^ 6331726) =
        partialPowerSum 6331726 0 12613 :=
      powerSum_eq_partialPowerSum 6331726
    _ = 12613 * 1858463317458 :=
      partialPowerSum_6331726_zero_12613

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
