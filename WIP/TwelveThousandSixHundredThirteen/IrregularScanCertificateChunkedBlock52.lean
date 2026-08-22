import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 52

This block covers scan coordinates `[2600, 2650)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2600, 2650)`. -/
def block52ExpectedResidues_chunked : List (ZMod 12613) :=
  [372, 11662, 8923, 1713, 3493, 8068, 5461, 9724, 1884, 6031,
    1919, 5409, 5831, 12177, 10650, 10813, 7284, 4863, 5768, 2671,
    10019, 8067, 6162, 584, 11845, 12045, 4505, 7680, 5967, 5460,
    5895, 6634, 6746, 5387, 1424, 5625, 2186, 337, 5232, 12553,
    12150, 10277, 8883, 8652, 6885, 9829, 8972, 12318, 7761, 7166]

/-- The one batched computation certificate for block 52. -/
theorem scanBlockResidues_block52_eq_chunked :
    scanBlockResidues 2600 50 = block52ExpectedResidues_chunked := by
  decide

private theorem block52ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block52ExpectedResidues_chunked[i.val]'(by
        simp [block52ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2600 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 52 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block52_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2600 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2600 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2600) (width := 50) (hbound := by omega)
      (expected := block52ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block52_eq_chunked)
      (hzeroCandidates := block52ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
