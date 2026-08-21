import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 30

This block covers scan coordinates `[1500, 1550)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1500, 1550)`. -/
def block30ExpectedResidues_chunked : List (ZMod 12613) :=
  [4439, 5217, 12104, 2818, 3396, 12459, 851, 5574, 1942, 6308,
    1701, 2026, 12181, 11938, 11559, 6550, 3280, 2135, 7905, 6026,
    2893, 1497, 6976, 10638, 6121, 6718, 4742, 2295, 9035, 8503,
    7920, 3884, 1901, 2101, 4740, 9324, 916, 7775, 9827, 5963,
    9789, 9202, 1567, 8666, 7689, 9610, 3664, 6582, 9535, 6954]

/-- The one batched computation certificate for block 30. -/
theorem scanBlockResidues_block30_eq_chunked :
    scanBlockResidues 1500 50 = block30ExpectedResidues_chunked := by
  decide

private theorem block30ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block30ExpectedResidues_chunked[i.val]'(by
        simp [block30ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1500 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 30 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block30_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1500 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1500 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1500) (width := 50) (hbound := by omega)
      (expected := block30ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block30_eq_chunked)
      (hzeroCandidates := block30ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
