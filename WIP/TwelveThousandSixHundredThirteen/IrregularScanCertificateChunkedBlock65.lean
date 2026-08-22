import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 65

This block covers scan coordinates `[3250, 3300)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3250, 3300)`. -/
def block65ExpectedResidues_chunked : List (ZMod 12613) :=
  [8157, 7099, 3325, 3411, 8202, 4683, 1722, 9347, 4993, 9270,
    11934, 10478, 4067, 4701, 10201, 10440, 6709, 5504, 1724, 7297,
    9172, 1052, 2649, 1227, 12109, 530, 18, 11580, 650, 12214,
    7594, 2366, 4712, 2774, 5911, 6873, 6374, 1951, 3917, 9419,
    9129, 4063, 5394, 2743, 956, 6878, 1949, 35, 9594, 248]

/-- The one batched computation certificate for block 65. -/
theorem scanBlockResidues_block65_eq_chunked :
    scanBlockResidues 3250 50 = block65ExpectedResidues_chunked := by
  decide

private theorem block65ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block65ExpectedResidues_chunked[i.val]'(by
        simp [block65ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3250 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 65 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block65_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3250 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3250 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3250) (width := 50) (hbound := by omega)
      (expected := block65ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block65_eq_chunked)
      (hzeroCandidates := block65ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
