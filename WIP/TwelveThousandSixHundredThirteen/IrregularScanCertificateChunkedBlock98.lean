import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 98

This block covers scan coordinates `[4900, 4950)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4900, 4950)`. -/
def block98ExpectedResidues_chunked : List (ZMod 12613) :=
  [8672, 905, 10701, 11986, 6012, 6801, 143, 4281, 10088, 11250,
    5786, 815, 1411, 12361, 7062, 10495, 7027, 3192, 7947, 10120,
    7304, 9761, 8031, 5223, 6738, 5085, 5483, 6136, 1864, 5102,
    7489, 5843, 2547, 5867, 1475, 2119, 5570, 9815, 7708, 11146,
    10532, 365, 6792, 7728, 260, 12124, 9594, 11678, 5132, 3688]

/-- The one batched computation certificate for block 98. -/
theorem scanBlockResidues_block98_eq_chunked :
    scanBlockResidues 4900 50 = block98ExpectedResidues_chunked := by
  decide

private theorem block98ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block98ExpectedResidues_chunked[i.val]'(by
        simp [block98ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4900 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 98 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block98_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4900 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4900 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4900) (width := 50) (hbound := by omega)
      (expected := block98ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block98_eq_chunked)
      (hzeroCandidates := block98ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
