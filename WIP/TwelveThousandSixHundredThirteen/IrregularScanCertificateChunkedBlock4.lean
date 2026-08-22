import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 4

This block covers scan coordinates `[200, 250)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[200, 250)`. -/
def block4ExpectedResidues_chunked : List (ZMod 12613) :=
  [2704, 10452, 6659, 9619, 3061, 2837, 6254, 2255, 10096, 3482,
    12181, 11676, 3015, 2983, 10607, 11235, 8253, 7365, 1763, 6887,
    495, 1906, 8131, 12053, 6978, 3317, 5870, 4846, 8509, 12167,
    5341, 6266, 11411, 8012, 5670, 7332, 2629, 3951, 9944, 6481,
    2821, 9940, 11551, 2444, 7844, 7452, 10964, 11387, 1372, 1651]

/-- The one batched computation certificate for block 4. -/
theorem scanBlockResidues_block4_eq_chunked :
    scanBlockResidues 200 50 = block4ExpectedResidues_chunked := by
  decide

private theorem block4ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block4ExpectedResidues_chunked[i.val]'(by
        simp [block4ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 200 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 4 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block4_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 200 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 200 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 200) (width := 50) (hbound := by omega)
      (expected := block4ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block4_eq_chunked)
      (hzeroCandidates := block4ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
