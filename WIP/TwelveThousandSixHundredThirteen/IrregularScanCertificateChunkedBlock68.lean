import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 68

This block covers scan coordinates `[3400, 3450)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3400, 3450)`. -/
def block68ExpectedResidues_chunked : List (ZMod 12613) :=
  [5380, 699, 9654, 7942, 3578, 10562, 6866, 12021, 6445, 8289,
    10983, 9068, 5967, 2994, 10839, 12425, 1436, 7235, 8417, 1877,
    5604, 7453, 1486, 12535, 6926, 7445, 2298, 52, 10343, 10321,
    2428, 5608, 8802, 10840, 2751, 445, 928, 672, 6038, 2451,
    3375, 6550, 12035, 3179, 2895, 9393, 11100, 10764, 1464, 12091]

/-- The one batched computation certificate for block 68. -/
theorem scanBlockResidues_block68_eq_chunked :
    scanBlockResidues 3400 50 = block68ExpectedResidues_chunked := by
  decide

private theorem block68ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block68ExpectedResidues_chunked[i.val]'(by
        simp [block68ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3400 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 68 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block68_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3400 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3400 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3400) (width := 50) (hbound := by omega)
      (expected := block68ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block68_eq_chunked)
      (hzeroCandidates := block68ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
