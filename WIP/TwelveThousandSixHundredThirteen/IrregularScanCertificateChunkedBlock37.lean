import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 37

This block covers scan coordinates `[1850, 1900)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[1850, 1900)`. -/
def block37ExpectedResidues_chunked : List (ZMod 12613) :=
  [7906, 1460, 9111, 7380, 5119, 5301, 9183, 11278, 10760, 10643,
    10392, 11073, 2443, 6554, 9328, 10551, 9160, 7067, 10228, 3219,
    1844, 2059, 10666, 8450, 11701, 4333, 5965, 35, 4467, 3073,
    10702, 647, 10707, 9313, 5932, 12235, 11583, 11851, 8924, 5262,
    8904, 10691, 8310, 9114, 7319, 11641, 9147, 8963, 8137, 11295]

/-- The one batched computation certificate for block 37. -/
theorem scanBlockResidues_block37_eq_chunked :
    scanBlockResidues 1850 50 = block37ExpectedResidues_chunked := by
  decide

private theorem block37ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block37ExpectedResidues_chunked[i.val]'(by
        simp [block37ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 1850 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 37 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block37_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 1850 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 1850 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 1850) (width := 50) (hbound := by omega)
      (expected := block37ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block37_eq_chunked)
      (hzeroCandidates := block37ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
