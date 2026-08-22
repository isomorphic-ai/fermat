import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 24

This block covers scan coordinates `[1200, 1250)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1200, 1250)`. -/
def block24ExpectedResidues_chunked : List (ZMod 12613) :=
  [12155, 12156, 12417, 12422, 9588, 4326, 1042, 8413, 3134, 1305,
    10706, 7854, 6093, 5005, 8430, 12154, 10672, 2825, 11549, 10927,
    3924, 956, 7617, 6678, 3612, 3260, 4364, 7109, 10153, 8485,
    3070, 7814, 1875, 2748, 7526, 6245, 12103, 1096, 6301, 6028,
    4820, 3173, 9957, 6964, 12612, 7643, 2328, 2847, 273, 565]

/-- The one batched computation certificate for block 24. -/
theorem scanBlockResidues_block24_eq_chunked :
    scanBlockResidues 1200 50 = block24ExpectedResidues_chunked := by
  decide

private theorem block24ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block24ExpectedResidues_chunked[i.val]'(by
        simp [block24ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1200 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 24 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block24_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1200 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1200 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1200) (width := 50) (hbound := by omega)
      (expected := block24ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block24_eq_chunked)
      (hzeroCandidates := block24ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
