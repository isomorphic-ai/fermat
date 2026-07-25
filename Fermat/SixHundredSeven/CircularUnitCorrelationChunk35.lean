import Fermat.SixHundredSeven.CircularUnitCorrelationChunk21
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk22
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk23
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk24
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk25
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk26
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk27
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk28
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk29
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk30

/-!
# Cyclic-correlation data at exponent 607: residues 175--179

This module kernel-checks five or fewer shifts as separate tail-recursive
natural computations. The modules are arranged in restartable dependency
tiers of width ten.
-/

namespace Fermat.SixHundredSeven.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_175 :
    natCorrelation (175 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_176 :
    natCorrelation (176 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_177 :
    natCorrelation (177 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_178 :
    natCorrelation (178 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_179 :
    natCorrelation (179 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk35 (i : Fin 5) :
    let d : Cyc := ((175 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_175
  · exact phaseCorrelation_of_nat nat_phase_correlation_176
  · exact phaseCorrelation_of_nat nat_phase_correlation_177
  · exact phaseCorrelation_of_nat nat_phase_correlation_178
  · exact phaseCorrelation_of_nat nat_phase_correlation_179

end

end Fermat.SixHundredSeven.CircularUnitCertificate
