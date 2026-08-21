import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 38

This block covers scan coordinates `[1900, 1950)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1900, 1950)`. -/
def block38ExpectedResidues_chunked : List (ZMod 12613) :=
  [5472, 7484, 11984, 8284, 7990, 4859, 11118, 4408, 7624, 1197,
    9943, 9613, 2919, 11223, 6300, 12554, 1347, 6509, 3214, 3780,
    10594, 6443, 2190, 1625, 8841, 9723, 10830, 6373, 9968, 7790,
    3974, 7258, 4734, 1895, 8609, 11733, 9652, 7353, 2789, 3842,
    2368, 8602, 3748, 7911, 8938, 10360, 4917, 4961, 3043, 12201]

/-- The one batched computation certificate for block 38. -/
theorem scanBlockResidues_block38_eq_chunked :
    scanBlockResidues 1900 50 = block38ExpectedResidues_chunked := by
  decide

private theorem block38ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block38ExpectedResidues_chunked[i.val]'(by
        simp [block38ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1900 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 38 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block38_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1900 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1900 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1900) (width := 50) (hbound := by omega)
      (expected := block38ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block38_eq_chunked)
      (hzeroCandidates := block38ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
