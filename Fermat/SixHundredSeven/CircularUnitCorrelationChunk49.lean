import Fermat.SixHundredSeven.CircularUnitCorrelationChunk31
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk32
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk33
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk34
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk35
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk36
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk37
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk38
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk39
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk40

/-!
# Cyclic-correlation data at exponent 607: residues 245--249

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

private theorem nat_phase_correlation_245 :
    natCorrelation (245 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_246 :
    natCorrelation (246 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_247 :
    natCorrelation (247 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_248 :
    natCorrelation (248 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_249 :
    natCorrelation (249 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk49 (i : Fin 5) :
    let d : Cyc := ((245 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_245
  · exact phaseCorrelation_of_nat nat_phase_correlation_246
  · exact phaseCorrelation_of_nat nat_phase_correlation_247
  · exact phaseCorrelation_of_nat nat_phase_correlation_248
  · exact phaseCorrelation_of_nat nat_phase_correlation_249

end

end Fermat.SixHundredSeven.CircularUnitCertificate
