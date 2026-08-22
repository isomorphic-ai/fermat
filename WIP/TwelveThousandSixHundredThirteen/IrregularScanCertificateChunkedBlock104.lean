import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 104

This block covers scan coordinates `[5200, 5250)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[5200, 5250)`. -/
def block104ExpectedResidues_chunked : List (ZMod 12613) :=
  [9420, 8768, 560, 1077, 8768, 5269, 8965, 9600, 10577, 8057,
    7322, 9, 8750, 3884, 10508, 4308, 5556, 6746, 1844, 7823,
    795, 11170, 10632, 1379, 3613, 284, 8319, 2476, 1648, 2184,
    3661, 8078, 6921, 12234, 5407, 9473, 3682, 12228, 3629, 10188,
    10905, 8265, 1565, 6053, 5498, 9850, 4634, 1197, 6061, 1271]

/-- The one batched computation certificate for block 104. -/
theorem scanBlockResidues_block104_eq_chunked :
    scanBlockResidues 5200 50 = block104ExpectedResidues_chunked := by
  decide

private theorem block104ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block104ExpectedResidues_chunked[i.val]'(by
        simp [block104ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 5200 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 104 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block104_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 5200 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 5200 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 5200) (width := 50) (hbound := by omega)
      (expected := block104ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block104_eq_chunked)
      (hzeroCandidates := block104ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
