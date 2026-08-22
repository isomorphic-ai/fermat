import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 23

This block covers scan coordinates `[1150, 1200)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1150, 1200)`. -/
def block23ExpectedResidues_chunked : List (ZMod 12613) :=
  [8074, 3122, 1994, 575, 760, 7855, 1586, 6377, 1717, 3867,
    1734, 8046, 1334, 5403, 6219, 3993, 9366, 5875, 12241, 6849,
    4542, 10698, 9030, 2114, 1724, 2348, 3137, 7028, 8996, 9324,
    2586, 7687, 744, 4145, 2862, 9179, 7542, 7325, 12462, 7125,
    403, 3685, 1984, 7252, 8037, 10908, 467, 8449, 4185, 9736]

/-- The one batched computation certificate for block 23. -/
theorem scanBlockResidues_block23_eq_chunked :
    scanBlockResidues 1150 50 = block23ExpectedResidues_chunked := by
  decide

private theorem block23ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block23ExpectedResidues_chunked[i.val]'(by
        simp [block23ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1150 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 23 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block23_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1150 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1150 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1150) (width := 50) (hbound := by omega)
      (expected := block23ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block23_eq_chunked)
      (hzeroCandidates := block23ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
