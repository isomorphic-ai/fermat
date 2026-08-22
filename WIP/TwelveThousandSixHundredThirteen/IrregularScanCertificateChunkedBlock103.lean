import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 103

This block covers scan coordinates `[5150, 5200)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5150, 5200)`. -/
def block103ExpectedResidues_chunked : List (ZMod 12613) :=
  [11172, 9274, 3577, 6669, 4217, 9621, 2356, 8532, 7453, 8039,
    12298, 5221, 6863, 4763, 130, 6026, 5318, 6116, 1831, 915,
    9925, 4134, 6403, 10992, 779, 5565, 6977, 10062, 9024, 6832,
    12421, 160, 7240, 6598, 9949, 8063, 12393, 12041, 10762, 3257,
    12299, 9626, 8357, 6727, 7760, 8190, 3098, 6415, 11673, 12402]

/-- The one batched computation certificate for block 103. -/
theorem scanBlockResidues_block103_eq_chunked :
    scanBlockResidues 5150 50 = block103ExpectedResidues_chunked := by
  decide

private theorem block103ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block103ExpectedResidues_chunked[i.val]'(by
        simp [block103ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5150 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 103 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block103_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5150 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5150 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5150) (width := 50) (hbound := by omega)
      (expected := block103ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block103_eq_chunked)
      (hzeroCandidates := block103ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
