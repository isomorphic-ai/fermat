import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 74

This block covers scan coordinates `[3700, 3750)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3700, 3750)`. -/
def block74ExpectedResidues_chunked : List (ZMod 12613) :=
  [8933, 8474, 11835, 4914, 4511, 9095, 495, 12013, 2442, 123,
    1986, 6367, 1004, 12545, 1531, 5713, 6563, 8977, 6579, 3055,
    4988, 10795, 1474, 8005, 6639, 2044, 4673, 1982, 11445, 6033,
    3034, 4082, 1112, 3710, 10963, 3209, 330, 4004, 9525, 11423,
    8955, 8414, 5583, 4399, 5636, 5908, 4341, 2383, 3080, 12502]

/-- The one batched computation certificate for block 74. -/
theorem scanBlockResidues_block74_eq_chunked :
    scanBlockResidues 3700 50 = block74ExpectedResidues_chunked := by
  decide

private theorem block74ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block74ExpectedResidues_chunked[i.val]'(by
        simp [block74ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3700 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 74 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block74_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3700 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3700 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3700) (width := 50) (hbound := by omega)
      (expected := block74ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block74_eq_chunked)
      (hzeroCandidates := block74ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
