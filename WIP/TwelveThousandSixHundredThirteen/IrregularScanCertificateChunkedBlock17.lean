import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 17

This block covers scan coordinates `[850, 900)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[850, 900)`. -/
def block17ExpectedResidues_chunked : List (ZMod 12613) :=
  [707, 3811, 460, 3256, 10635, 6437, 4259, 1819, 12414, 3113,
    3766, 3167, 7995, 3061, 4652, 8971, 6825, 11691, 8273, 40,
    6973, 4173, 11825, 11865, 326, 10709, 5164, 1892, 4923, 1500,
    6827, 2739, 12083, 9847, 9109, 4075, 6585, 8036, 11487, 7358,
    8895, 2292, 238, 3448, 10196, 2580, 10076, 12214, 8843, 2729]

/-- The one batched computation certificate for block 17. -/
theorem scanBlockResidues_block17_eq_chunked :
    scanBlockResidues 850 50 = block17ExpectedResidues_chunked := by
  decide

private theorem block17ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block17ExpectedResidues_chunked[i.val]'(by
        simp [block17ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 850 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 17 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block17_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 850 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 850 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 850) (width := 50) (hbound := by omega)
      (expected := block17ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block17_eq_chunked)
      (hzeroCandidates := block17ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
