import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 101

This block covers scan coordinates `[5050, 5100)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5050, 5100)`. -/
def block101ExpectedResidues_chunked : List (ZMod 12613) :=
  [1747, 1825, 7164, 6043, 6393, 9197, 10765, 4208, 399, 12585,
    2862, 243, 10971, 9343, 8265, 137, 12199, 4604, 7205, 11626,
    11414, 2964, 11060, 5089, 1531, 2067, 2231, 1044, 1376, 3669,
    9003, 1232, 12552, 220, 7178, 637, 3964, 6, 4354, 12018,
    4667, 10791, 10608, 5201, 6299, 1655, 11986, 10009, 9245, 2738]

/-- The one batched computation certificate for block 101. -/
theorem scanBlockResidues_block101_eq_chunked :
    scanBlockResidues 5050 50 = block101ExpectedResidues_chunked := by
  decide

private theorem block101ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block101ExpectedResidues_chunked[i.val]'(by
        simp [block101ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5050 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 101 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block101_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5050 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5050 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5050) (width := 50) (hbound := by omega)
      (expected := block101ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block101_eq_chunked)
      (hzeroCandidates := block101ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
