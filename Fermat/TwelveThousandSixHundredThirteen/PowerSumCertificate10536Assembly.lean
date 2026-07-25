import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk0
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk1
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk2
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk3
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk4
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk5
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk6
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk7
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk8
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk9
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk10
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk11
import Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Chunk12

/-!
# Balanced assembly of the lifted j=10536 power sum

The thirteen independently checked leaves are joined through a balanced tree
of `partialPowerSum_consecutive` applications.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem partialPowerSum_132890568_zero_2048 :
    partialPowerSum 132890568 0 2048 = 13646202330973919 := by
  calc
    partialPowerSum 132890568 0 2048 =
        partialPowerSum 132890568 0 1024 +
          partialPowerSum 132890568 1024 2048 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 0) (mid := 1024) (hi := 2048)
        (by norm_num) (by norm_num)
    _ = 13646202330973919 := by
      rw [partialPowerSum_132890568_zero_1024,
        partialPowerSum_132890568_1024_2048]
      decide

private theorem partialPowerSum_132890568_2048_4096 :
    partialPowerSum 132890568 2048 4096 = 227980964254664 := by
  calc
    partialPowerSum 132890568 2048 4096 =
        partialPowerSum 132890568 2048 3072 +
          partialPowerSum 132890568 3072 4096 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 2048) (mid := 3072) (hi := 4096)
        (by norm_num) (by norm_num)
    _ = 227980964254664 := by
      rw [partialPowerSum_132890568_2048_3072,
        partialPowerSum_132890568_3072_4096]
      decide

private theorem partialPowerSum_132890568_4096_6144 :
    partialPowerSum 132890568 4096 6144 = 223277173251527 := by
  calc
    partialPowerSum 132890568 4096 6144 =
        partialPowerSum 132890568 4096 5120 +
          partialPowerSum 132890568 5120 6144 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 4096) (mid := 5120) (hi := 6144)
        (by norm_num) (by norm_num)
    _ = 223277173251527 := by
      rw [partialPowerSum_132890568_4096_5120,
        partialPowerSum_132890568_5120_6144]
      decide

private theorem partialPowerSum_132890568_6144_8192 :
    partialPowerSum 132890568 6144 8192 = 23482629024611668 := by
  calc
    partialPowerSum 132890568 6144 8192 =
        partialPowerSum 132890568 6144 7168 +
          partialPowerSum 132890568 7168 8192 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 6144) (mid := 7168) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 23482629024611668 := by
      rw [partialPowerSum_132890568_6144_7168,
        partialPowerSum_132890568_7168_8192]
      decide

private theorem partialPowerSum_132890568_8192_10240 :
    partialPowerSum 132890568 8192 10240 = 6706220624804899 := by
  calc
    partialPowerSum 132890568 8192 10240 =
        partialPowerSum 132890568 8192 9216 +
          partialPowerSum 132890568 9216 10240 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 8192) (mid := 9216) (hi := 10240)
        (by norm_num) (by norm_num)
    _ = 6706220624804899 := by
      rw [partialPowerSum_132890568_8192_9216,
        partialPowerSum_132890568_9216_10240]
      decide

private theorem partialPowerSum_132890568_10240_12288 :
    partialPowerSum 132890568 10240 12288 = 483041120329706 := by
  calc
    partialPowerSum 132890568 10240 12288 =
        partialPowerSum 132890568 10240 11264 +
          partialPowerSum 132890568 11264 12288 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 10240) (mid := 11264) (hi := 12288)
        (by norm_num) (by norm_num)
    _ = 483041120329706 := by
      rw [partialPowerSum_132890568_10240_11264,
        partialPowerSum_132890568_11264_12288]
      decide

private theorem partialPowerSum_132890568_zero_4096 :
    partialPowerSum 132890568 0 4096 = 13874183295228583 := by
  calc
    partialPowerSum 132890568 0 4096 =
        partialPowerSum 132890568 0 2048 +
          partialPowerSum 132890568 2048 4096 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 0) (mid := 2048) (hi := 4096)
        (by norm_num) (by norm_num)
    _ = 13874183295228583 := by
      rw [partialPowerSum_132890568_zero_2048,
        partialPowerSum_132890568_2048_4096]
      decide

private theorem partialPowerSum_132890568_4096_8192 :
    partialPowerSum 132890568 4096 8192 = 23705906197863195 := by
  calc
    partialPowerSum 132890568 4096 8192 =
        partialPowerSum 132890568 4096 6144 +
          partialPowerSum 132890568 6144 8192 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 4096) (mid := 6144) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 23705906197863195 := by
      rw [partialPowerSum_132890568_4096_6144,
        partialPowerSum_132890568_6144_8192]
      decide

private theorem partialPowerSum_132890568_8192_12288 :
    partialPowerSum 132890568 8192 12288 = 7189261745134605 := by
  calc
    partialPowerSum 132890568 8192 12288 =
        partialPowerSum 132890568 8192 10240 +
          partialPowerSum 132890568 10240 12288 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 8192) (mid := 10240) (hi := 12288)
        (by norm_num) (by norm_num)
    _ = 7189261745134605 := by
      rw [partialPowerSum_132890568_8192_10240,
        partialPowerSum_132890568_10240_12288]
      decide

private theorem partialPowerSum_132890568_zero_8192 :
    partialPowerSum 132890568 0 8192 = 12271171247694417 := by
  calc
    partialPowerSum 132890568 0 8192 =
        partialPowerSum 132890568 0 4096 +
          partialPowerSum 132890568 4096 8192 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 0) (mid := 4096) (hi := 8192)
        (by norm_num) (by norm_num)
    _ = 12271171247694417 := by
      rw [partialPowerSum_132890568_zero_4096,
        partialPowerSum_132890568_4096_8192]
      decide

private theorem partialPowerSum_132890568_8192_12613 :
    partialPowerSum 132890568 8192 12613 = 14903860845972154 := by
  calc
    partialPowerSum 132890568 8192 12613 =
        partialPowerSum 132890568 8192 12288 +
          partialPowerSum 132890568 12288 12613 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 8192) (mid := 12288) (hi := 12613)
        (by norm_num) (by norm_num)
    _ = 14903860845972154 := by
      rw [partialPowerSum_132890568_8192_12288,
        partialPowerSum_132890568_12288_12613]
      decide

theorem partialPowerSum_132890568_zero_12613 :
    partialPowerSum 132890568 0 12613 = 12613 * 147951625170 := by
  calc
    partialPowerSum 132890568 0 12613 =
        partialPowerSum 132890568 0 8192 +
          partialPowerSum 132890568 8192 12613 := by
      symm
      exact partialPowerSum_consecutive 132890568
        (lo := 0) (mid := 8192) (hi := 12613)
        (by norm_num) (by norm_num)
    _ = 12613 * 147951625170 := by
      rw [partialPowerSum_132890568_zero_8192,
        partialPowerSum_132890568_8192_12613]
      decide

/-- The chunked theorem in the shape consumed by `HighBernoulli`. -/
theorem powerSum_132890568_chunked :
    (∑ a ∈ Finset.range 12613,
      (a : ZMod (12613 ^ 4)) ^ 132890568) =
        12613 * 147951625170 := by
  calc
    (∑ a ∈ Finset.range 12613,
        (a : ZMod (12613 ^ 4)) ^ 132890568) =
        partialPowerSum 132890568 0 12613 :=
      powerSum_eq_partialPowerSum 132890568
    _ = 12613 * 147951625170 :=
      partialPowerSum_132890568_zero_12613

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificates
