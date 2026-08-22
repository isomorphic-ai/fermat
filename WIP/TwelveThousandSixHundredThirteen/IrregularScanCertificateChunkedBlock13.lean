import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 13

This block covers scan coordinates `[650, 700)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[650, 700)`. -/
def block13ExpectedResidues_chunked : List (ZMod 12613) :=
  [7661, 12276, 1883, 500, 9827, 1322, 6249, 10417, 7684, 9815,
    11208, 2139, 4785, 3777, 8370, 7647, 7207, 9249, 7872, 10114,
    1610, 2257, 1514, 4736, 10482, 2525, 11847, 11747, 7661, 1935,
    10636, 6994, 1051, 7387, 2860, 317, 7726, 20, 791, 7778,
    4559, 5930, 5176, 6294, 518, 4054, 10630, 11844, 10092, 3190]

/-- The one batched computation certificate for block 13. -/
theorem scanBlockResidues_block13_eq_chunked :
    scanBlockResidues 650 50 = block13ExpectedResidues_chunked := by
  decide

private theorem block13ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block13ExpectedResidues_chunked[i.val]'(by
        simp [block13ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 650 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 13 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block13_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 650 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 650 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 650) (width := 50) (hbound := by omega)
      (expected := block13ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block13_eq_chunked)
      (hzeroCandidates := block13ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
