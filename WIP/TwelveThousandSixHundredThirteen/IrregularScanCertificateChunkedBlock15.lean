import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 15

This block covers scan coordinates `[750, 800)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[750, 800)`. -/
def block15ExpectedResidues_chunked : List (ZMod 12613) :=
  [5864, 11807, 6780, 9566, 7342, 5697, 11315, 1354, 1558, 10442,
    5195, 2855, 10778, 11516, 6056, 10661, 4711, 9836, 5404, 6415,
    3327, 3859, 11815, 1322, 159, 6570, 9490, 11664, 3984, 7289,
    10731, 10818, 2374, 8275, 8523, 10868, 874, 8966, 6415, 4726,
    5805, 11613, 2076, 7834, 10901, 2010, 11822, 10295, 2800, 5422]

/-- The one batched computation certificate for block 15. -/
theorem scanBlockResidues_block15_eq_chunked :
    scanBlockResidues 750 50 = block15ExpectedResidues_chunked := by
  decide

private theorem block15ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block15ExpectedResidues_chunked[i.val]'(by
        simp [block15ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 750 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 15 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block15_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 750 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 750 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 750) (width := 50) (hbound := by omega)
      (expected := block15ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block15_eq_chunked)
      (hzeroCandidates := block15ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
