import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 119

This block covers scan coordinates `[5950, 6000)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5950, 6000)`. -/
def block119ExpectedResidues_chunked : List (ZMod 12613) :=
  [9093, 9543, 1066, 3720, 2995, 2008, 2215, 8261, 8028, 4295,
    5713, 12579, 3956, 6258, 6223, 10409, 7235, 10710, 10317, 12109,
    11383, 7714, 3752, 3274, 905, 8170, 4842, 2619, 4025, 3958,
    1856, 7873, 8806, 11477, 5249, 10449, 4782, 10231, 3581, 4916,
    11469, 3504, 10488, 7325, 1571, 11821, 12100, 2950, 5330, 9260]

/-- The one batched computation certificate for block 119. -/
theorem scanBlockResidues_block119_eq_chunked :
    scanBlockResidues 5950 50 = block119ExpectedResidues_chunked := by
  decide

private theorem block119ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block119ExpectedResidues_chunked[i.val]'(by
        simp [block119ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5950 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 119 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block119_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5950 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5950 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5950) (width := 50) (hbound := by omega)
      (expected := block119ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block119_eq_chunked)
      (hzeroCandidates := block119ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
