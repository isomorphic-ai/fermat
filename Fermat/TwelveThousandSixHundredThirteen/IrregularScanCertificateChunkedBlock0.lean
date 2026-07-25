import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan pilot: block 0

This pilot covers coordinates `[0, 50)`, hence the even Bernoulli indices
`2, 4, ..., 100`.  A single decision checks the complete batch result.
The coordinate-independent follow-up decision examines only that explicit
list; it does not evaluate `scanResidue` again.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates `[0, 50)`. -/
def block0ExpectedResidues_chunked : List (ZMod 12613) :=
  [9460, 7883, 9460, 10247, 3161, 10950, 10825, 1301, 9107, 8854,
    12242, 4180, 10540, 9968, 6972, 5245, 7464, 4273, 5489, 4303,
    10033, 12268, 11474, 6042, 2122, 61, 1980, 11212, 7254, 7863,
    11647, 10043, 10993, 11776, 12111, 2950, 8295, 3460, 8739, 7066,
    4178, 8634, 9076, 6700, 7977, 3536, 8866, 6589, 2633, 10210]

/-- The one batched computation certificate for block 0. -/
theorem scanBlockResidues_block0_eq_chunked :
    scanBlockResidues 0 50 = block0ExpectedResidues_chunked := by
  decide

private theorem block0ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block0ExpectedResidues_chunked[i.val]'(by
        simp [block0ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 0 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 0 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block0_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 0 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 0 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 0) (width := 50) (hbound := by omega)
      (expected := block0ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block0_eq_chunked)
      (hzeroCandidates :=
        block0ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
