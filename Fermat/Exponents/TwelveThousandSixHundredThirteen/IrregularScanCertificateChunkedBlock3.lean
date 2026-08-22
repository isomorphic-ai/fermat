import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 3

This block covers scan coordinates `[150, 200)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[150, 200)`. -/
def block3ExpectedResidues_chunked : List (ZMod 12613) :=
  [10513, 1857, 2820, 0, 1935, 9891, 6832, 5279, 6495, 8666,
    8513, 10453, 5638, 5679, 3994, 8483, 6285, 2113, 5465, 1814,
    2427, 347, 2948, 8279, 4291, 6427, 5577, 218, 11386, 6608,
    3095, 2712, 8005, 9791, 556, 5568, 1847, 9357, 3618, 1309,
    517, 7142, 2426, 48, 5217, 9023, 8796, 6782, 12590, 6025]

/-- The one batched computation certificate for block 3. -/
theorem scanBlockResidues_block3_eq_chunked :
    scanBlockResidues 150 50 = block3ExpectedResidues_chunked := by
  decide

private theorem block3ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block3ExpectedResidues_chunked[i.val]'(by
        simp [block3ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 150 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 3 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block3_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 150 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 150 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 150) (width := 50) (hbound := by omega)
      (expected := block3ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block3_eq_chunked)
      (hzeroCandidates := block3ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
