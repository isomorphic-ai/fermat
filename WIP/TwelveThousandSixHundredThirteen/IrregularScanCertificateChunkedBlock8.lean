import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 8

This block covers scan coordinates `[400, 450)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[400, 450)`. -/
def block8ExpectedResidues_chunked : List (ZMod 12613) :=
  [1887, 625, 3102, 11061, 802, 451, 11032, 4388, 9011, 229,
    1191, 3221, 3042, 701, 11629, 825, 9491, 10770, 4147, 8157,
    5328, 10755, 2534, 6064, 7751, 249, 253, 7651, 4262, 2353,
    4536, 10661, 9448, 5965, 10781, 778, 6993, 5819, 1356, 9265,
    803, 9133, 8918, 2757, 7382, 7621, 9618, 1780, 10076, 1042]

/-- The one batched computation certificate for block 8. -/
theorem scanBlockResidues_block8_eq_chunked :
    scanBlockResidues 400 50 = block8ExpectedResidues_chunked := by
  decide

private theorem block8ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block8ExpectedResidues_chunked[i.val]'(by
        simp [block8ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 400 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 8 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block8_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 400 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 400 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 400) (width := 50) (hbound := by omega)
      (expected := block8ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block8_eq_chunked)
      (hzeroCandidates := block8ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
