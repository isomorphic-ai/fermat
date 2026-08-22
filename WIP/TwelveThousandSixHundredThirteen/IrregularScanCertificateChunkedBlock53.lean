import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 53

This block covers scan coordinates `[2650, 2700)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2650, 2700)`. -/
def block53ExpectedResidues_chunked : List (ZMod 12613) :=
  [4830, 4730, 7679, 4504, 290, 405, 2243, 3355, 667, 99,
    4572, 12450, 3316, 10992, 9908, 5979, 4992, 8365, 10665, 4853,
    3125, 2887, 27, 47, 1789, 10783, 504, 3592, 11352, 12107,
    11443, 729, 5309, 11366, 5618, 11021, 3531, 7108, 5904, 1383,
    3659, 3092, 4353, 4780, 12181, 1665, 11741, 11447, 9252, 509]

/-- The one batched computation certificate for block 53. -/
theorem scanBlockResidues_block53_eq_chunked :
    scanBlockResidues 2650 50 = block53ExpectedResidues_chunked := by
  decide

private theorem block53ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block53ExpectedResidues_chunked[i.val]'(by
        simp [block53ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2650 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 53 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block53_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2650 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2650 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2650) (width := 50) (hbound := by omega)
      (expected := block53ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block53_eq_chunked)
      (hzeroCandidates := block53ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
