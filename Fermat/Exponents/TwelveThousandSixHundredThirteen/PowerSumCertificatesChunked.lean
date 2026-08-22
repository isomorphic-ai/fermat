import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate308Assembly
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate502Assembly
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate9400Assembly
import Fermat.Exponents.TwelveThousandSixHundredThirteen.PowerSumCertificate10536Assembly

/-!
# Chunked modular power sums for the exponent-12613 Bernoulli channels

The four bounded-memory assembly modules provide the lifted power sums at
`j ∈ {308, 502, 9400, 10536}`.  This companion module records the arithmetic
shape and cube nondivisibility of their correction quotients under names
that remain disjoint from the preserved monolithic certificate module.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificatesChunked

theorem correctionQuotient_3884804_chunked :
    411878233941 = 12613 ^ 2 * 2589 := by
  norm_num

theorem correctionQuotient_6331726_chunked :
    1858463317458 = 12613 ^ 2 * 11682 := by
  norm_num

theorem correctionQuotient_118562200_chunked :
    481876852301 = 12613 ^ 2 * 3029 := by
  norm_num

theorem correctionQuotient_132890568_chunked :
    147951625170 = 12613 ^ 2 * 930 := by
  norm_num

theorem correctionQuotient_3884804_not_dvd_cube_chunked :
    ¬(12613 : ℤ) ^ 3 ∣ (411878233941 : ℤ) := by
  norm_num

theorem correctionQuotient_6331726_not_dvd_cube_chunked :
    ¬(12613 : ℤ) ^ 3 ∣ (1858463317458 : ℤ) := by
  norm_num

theorem correctionQuotient_118562200_not_dvd_cube_chunked :
    ¬(12613 : ℤ) ^ 3 ∣ (481876852301 : ℤ) := by
  norm_num

theorem correctionQuotient_132890568_not_dvd_cube_chunked :
    ¬(12613 : ℤ) ^ 3 ∣ (147951625170 : ℤ) := by
  norm_num

end Fermat.TwelveThousandSixHundredThirteen.PowerSumCertificatesChunked
