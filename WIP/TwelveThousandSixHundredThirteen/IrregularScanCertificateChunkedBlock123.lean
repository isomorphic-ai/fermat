import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 123

This block covers scan coordinates `[6150, 6200)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[6150, 6200)`. -/
def block123ExpectedResidues_chunked : List (ZMod 12613) :=
  [4467, 10583, 3454, 5942, 12465, 461, 2811, 9584, 11293, 2467,
    9083, 4145, 11217, 4182, 10899, 3000, 10327, 5492, 4428, 8619,
    11782, 6477, 5590, 8275, 558, 12565, 10541, 8017, 3299, 4841,
    10675, 9431, 2970, 10104, 4587, 3991, 12218, 11184, 645, 12263,
    11225, 10629, 5558, 9288, 8618, 322, 4068, 2974, 9857, 2350]

/-- The one batched computation certificate for block 123. -/
theorem scanBlockResidues_block123_eq_chunked :
    scanBlockResidues 6150 50 = block123ExpectedResidues_chunked := by
  decide

private theorem block123ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block123ExpectedResidues_chunked[i.val]'(by
        simp [block123ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 6150 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 123 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block123_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 6150 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 6150 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 6150) (width := 50) (hbound := by omega)
      (expected := block123ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block123_eq_chunked)
      (hzeroCandidates := block123ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
