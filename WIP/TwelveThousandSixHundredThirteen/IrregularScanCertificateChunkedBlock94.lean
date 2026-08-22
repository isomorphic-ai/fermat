import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 94

This block covers scan coordinates `[4700, 4750)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4700, 4750)`. -/
def block94ExpectedResidues_chunked : List (ZMod 12613) :=
  [6705, 1580, 7278, 1039, 830, 10751, 5598, 3757, 5139, 8754,
    2963, 1167, 245, 10681, 12000, 6103, 10954, 11129, 6711, 12434,
    10543, 12556, 4097, 9652, 7719, 6241, 5850, 9782, 12602, 5616,
    1047, 12408, 10847, 5383, 1751, 6862, 2469, 2532, 6916, 2702,
    1386, 11212, 1431, 11256, 12473, 3124, 6021, 7852, 9374, 7452]

/-- The one batched computation certificate for block 94. -/
theorem scanBlockResidues_block94_eq_chunked :
    scanBlockResidues 4700 50 = block94ExpectedResidues_chunked := by
  decide

private theorem block94ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block94ExpectedResidues_chunked[i.val]'(by
        simp [block94ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4700 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 94 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block94_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4700 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4700 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4700) (width := 50) (hbound := by omega)
      (expected := block94ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block94_eq_chunked)
      (hzeroCandidates := block94ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
