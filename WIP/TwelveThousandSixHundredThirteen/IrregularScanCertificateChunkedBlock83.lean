import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 83

This block covers scan coordinates `[4150, 4200)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[4150, 4200)`. -/
def block83ExpectedResidues_chunked : List (ZMod 12613) :=
  [10951, 328, 6218, 8508, 5775, 3959, 12155, 1361, 2922, 7071,
    5511, 8594, 11845, 7684, 608, 2653, 10927, 8279, 4830, 4215,
    4182, 6317, 5172, 6306, 11308, 11676, 5152, 8913, 9606, 5124,
    4207, 702, 6921, 4125, 5394, 2701, 3334, 9397, 2852, 9478,
    9047, 2403, 8324, 6557, 12483, 12430, 7488, 7122, 11267, 5332]

/-- The one batched computation certificate for block 83. -/
theorem scanBlockResidues_block83_eq_chunked :
    scanBlockResidues 4150 50 = block83ExpectedResidues_chunked := by
  decide

private theorem block83ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block83ExpectedResidues_chunked[i.val]'(by
        simp [block83ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 4150 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 83 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block83_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 4150 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 4150 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 4150) (width := 50) (hbound := by omega)
      (expected := block83ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block83_eq_chunked)
      (hzeroCandidates := block83ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
