import Fermat.TwelveThousandSixHundredThirteen.IrregularScanCertificateChunkedCore

/-!
# Batched irregular-scan certificate: block 49

This block covers scan coordinates `[2450, 2500)` with one computation
of the complete residue list.  Coordinate transport reuses the generic
`scanBlockResidues_getElem` bridge.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Independently audited residues for scan coordinates
`[2450, 2500)`. -/
def block49ExpectedResidues_chunked : List (ZMod 12613) :=
  [5672, 5669, 4871, 3898, 9519, 2570, 7321, 3548, 5105, 9961,
    4097, 9101, 11277, 3167, 2212, 10883, 8302, 3513, 9449, 8838,
    9904, 7106, 12240, 3614, 5046, 5046, 6128, 84, 2174, 963,
    11031, 5604, 818, 11235, 4294, 426, 5875, 315, 4219, 960,
    8557, 10122, 3089, 5174, 545, 325, 2643, 11308, 10929, 10998]

/-- The one batched computation certificate for block 49. -/
theorem scanBlockResidues_block49_eq_chunked :
    scanBlockResidues 2450 50 = block49ExpectedResidues_chunked := by
  decide

private theorem block49ExpectedResidues_zero_imp_candidate_chunked
    (i : Fin 50)
    (hzero :
      block49ExpectedResidues_chunked[i.val]'(by
        simp [block49ExpectedResidues_chunked]) = 0) :
    scanIndex (offsetIndex 2450 50 (by omega) i) ∈
      irregularCandidates := by
  decide +revert

/-- Any zero scan residue in block 49 belongs to the reported irregular
candidate set. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_block49_chunked
    (i : Fin 50) :
    scanResidue 12613 2
        (scanIndex (offsetIndex 2450 50 (by omega) i)) = 0 →
      scanIndex (offsetIndex 2450 50 (by omega) i) ∈
        irregularCandidates := by
  exact
    scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
      (offset := 2450) (width := 50) (hbound := by omega)
      (expected := block49ExpectedResidues_chunked)
      (hlength := by decide)
      (hcertificate := scanBlockResidues_block49_eq_chunked)
      (hzeroCandidates := block49ExpectedResidues_zero_imp_candidate_chunked)
      i

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
