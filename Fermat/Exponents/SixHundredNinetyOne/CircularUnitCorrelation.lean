import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk9
import Fermat.Exponents.SixHundredNinetyOne.CircularUnitCorrelationChunk9B

/-!
# Finite cyclic-correlation data at exponent 691

One module kernel-checks residues 0--34. The remaining eighteen modules
kernel-check disjoint 17- or 18-residue blocks in nine dependency waves of
two. This bounds cold-build memory while retaining safe parallelism,
fine-grained caching, and recovery. This module joins the blocks into the
complete 345-correlation theorem, replacing a dense `344 × 344` inverse.
-/

namespace Fermat.SixHundredNinetyOne.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredNinetyOne.CircularUnitCyclic
open Fermat.SixHundredNinetyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Kernel-checked cyclic-correlation certificate. -/
theorem phase_correlation (d : Cyc) :
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  by_cases h0 : d.val < 35
  · exact phase_correlation_chunk0 d h0
  by_cases h1 : d.val < 52
  · exact phase_correlation_chunk1 d (by omega) h1
  by_cases h1B : d.val < 69
  · exact phase_correlation_chunk1B d (by omega) h1B
  by_cases h2 : d.val < 87
  · exact phase_correlation_chunk2 d (by omega) h2
  by_cases h2B : d.val < 104
  · exact phase_correlation_chunk2B d (by omega) h2B
  by_cases h3 : d.val < 121
  · exact phase_correlation_chunk3 d (by omega) h3
  by_cases h3B : d.val < 138
  · exact phase_correlation_chunk3B d (by omega) h3B
  by_cases h4 : d.val < 156
  · exact phase_correlation_chunk4 d (by omega) h4
  by_cases h4B : d.val < 173
  · exact phase_correlation_chunk4B d (by omega) h4B
  by_cases h5 : d.val < 190
  · exact phase_correlation_chunk5 d (by omega) h5
  by_cases h5B : d.val < 207
  · exact phase_correlation_chunk5B d (by omega) h5B
  by_cases h6 : d.val < 225
  · exact phase_correlation_chunk6 d (by omega) h6
  by_cases h6B : d.val < 242
  · exact phase_correlation_chunk6B d (by omega) h6B
  by_cases h7 : d.val < 259
  · exact phase_correlation_chunk7 d (by omega) h7
  by_cases h7B : d.val < 276
  · exact phase_correlation_chunk7B d (by omega) h7B
  by_cases h8 : d.val < 294
  · exact phase_correlation_chunk8 d (by omega) h8
  by_cases h8B : d.val < 311
  · exact phase_correlation_chunk8B d (by omega) h8B
  by_cases h9 : d.val < 328
  · exact phase_correlation_chunk9 d (by omega) h9
  · exact phase_correlation_chunk9B d (by omega)

end

end Fermat.SixHundredNinetyOne.CircularUnitCertificate
