import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 50

This block covers scan coordinates `[2500, 2550)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2500, 2550)`. -/
def block50ExpectedResidues_chunked : List (ZMod 12613) :=
  [6466, 9051, 7261, 10578, 8821, 2281, 9155, 8442, 2603, 12432,
    7462, 9779, 5806, 5566, 4013, 765, 3657, 4674, 7450, 8219,
    5884, 3050, 6053, 1499, 5999, 7518, 12037, 4833, 8059, 12037,
    1901, 6703, 12309, 8390, 10633, 55, 2145, 446, 2569, 11321,
    3063, 3844, 2890, 11551, 7232, 1488, 5994, 9066, 7636, 12320]

/-- The one batched computation certificate for block 50. -/
theorem scanBlockResidues_block50_eq_chunked :
    scanBlockResidues 2500 50 = block50ExpectedResidues_chunked := by
  decide

private theorem block50ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block50ExpectedResidues_chunked[i.val]'(by
        simp [block50ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2500 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 50 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block50_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2500 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2500 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2500) (width := 50) (hbound := by omega)
      (expected := block50ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block50_eq_chunked)
      (hzeroCandidates := block50ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
