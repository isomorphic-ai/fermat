import Fermat.Exponents.TwelveThousandSixHundredThirteen.IrregularScanBatch

/-!
# Reusable transport for chunked irregular-scan certificates

A serialized block proves one equality for the complete list returned by
`scanBlockResidues`.  This helper transports any zero entry through
`scanBlockResidues_getElem`; the block module then checks only the explicit
residue list when deciding whether the corresponding index is a reported
irregular candidate.

The interface is independent of block size.  It therefore supports 126
width-50 blocks followed by the final width-5 block covering all `6305`
coordinates.
-/

namespace Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked

open Fermat.Irregular.ModularBernoulliScan
open Fermat.TwelveThousandSixHundredThirteen.IrregularScan

/-- Transport one batched list certificate to the classical scan residue.
The `hzeroCandidates` argument inspects only the explicit list supplied by
the block certificate. -/
theorem scanResidue_zero_imp_mem_irregularCandidates_of_block_eq_chunked
    (offset width : ℕ) (hbound : offset + width ≤ 6305)
    (expected : List (ZMod 12613)) (hlength : expected.length = width)
    (hcertificate : scanBlockResidues offset width = expected)
    (hzeroCandidates :
      ∀ i : Fin width,
        expected[i.val]'(by
          rw [hlength]
          exact i.isLt) = 0 →
          scanIndex (offsetIndex offset width hbound i) ∈
            irregularCandidates)
    (i : Fin width) :
    scanResidue 12613 2
        (scanIndex (offsetIndex offset width hbound i)) = 0 →
      scanIndex (offsetIndex offset width hbound i) ∈
        irregularCandidates := by
  subst expected
  intro hzero
  apply hzeroCandidates i
  rw [scanBlockResidues_getElem offset width i.val i.isLt]
  simpa [scanIndex, offsetIndex] using hzero

end Fermat.TwelveThousandSixHundredThirteen.IrregularScanChunked
