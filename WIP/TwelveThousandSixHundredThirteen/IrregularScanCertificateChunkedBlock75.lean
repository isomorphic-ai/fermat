import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 75

This block covers scan coordinates `[3750, 3800)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[3750, 3800)`. -/
def block75ExpectedResidues_chunked : List (ZMod 12613) :=
  [3763, 7267, 7863, 6875, 8049, 6132, 9827, 9191, 3358, 7875,
    8093, 11202, 5251, 9441, 4110, 9543, 5787, 4153, 4974, 4237,
    2534, 1685, 2639, 1421, 6139, 455, 12584, 4275, 704, 10799,
    6400, 6037, 3135, 6803, 2519, 6028, 873, 6857, 9197, 7618,
    9357, 1627, 1199, 6860, 2487, 141, 10423, 1869, 4117, 5405]

/-- The one batched computation certificate for block 75. -/
theorem scanBlockResidues_block75_eq_chunked :
    scanBlockResidues 3750 50 = block75ExpectedResidues_chunked := by
  decide

private theorem block75ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block75ExpectedResidues_chunked[i.val]'(by
        simp [block75ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 3750 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 75 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block75_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 3750 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 3750 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 3750) (width := 50) (hbound := by omega)
      (expected := block75ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block75_eq_chunked)
      (hzeroCandidates := block75ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
