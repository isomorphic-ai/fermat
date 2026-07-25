import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk34
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk35
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk36

/-!
# Cyclic-correlation data at exponent 1831: residues 395--404

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_395 :
    natCorrelation (395 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_396 :
    natCorrelation (396 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_397 :
    natCorrelation (397 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_398 :
    natCorrelation (398 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_399 :
    natCorrelation (399 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_400 :
    natCorrelation (400 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_401 :
    natCorrelation (401 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_402 :
    natCorrelation (402 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_403 :
    natCorrelation (403 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_404 :
    natCorrelation (404 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk37 (i : Fin 10) :
    let d : Cyc := ((395 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_395
  · exact phaseCorrelation_of_nat nat_phase_correlation_396
  · exact phaseCorrelation_of_nat nat_phase_correlation_397
  · exact phaseCorrelation_of_nat nat_phase_correlation_398
  · exact phaseCorrelation_of_nat nat_phase_correlation_399
  · exact phaseCorrelation_of_nat nat_phase_correlation_400
  · exact phaseCorrelation_of_nat nat_phase_correlation_401
  · exact phaseCorrelation_of_nat nat_phase_correlation_402
  · exact phaseCorrelation_of_nat nat_phase_correlation_403
  · exact phaseCorrelation_of_nat nat_phase_correlation_404

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
