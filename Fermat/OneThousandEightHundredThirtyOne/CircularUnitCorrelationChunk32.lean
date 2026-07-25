import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk28
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk29
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk30

/-!
# Cyclic-correlation data at exponent 1831: residues 345--354

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

private theorem nat_phase_correlation_345 :
    natCorrelation (345 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_346 :
    natCorrelation (346 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_347 :
    natCorrelation (347 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_348 :
    natCorrelation (348 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_349 :
    natCorrelation (349 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_350 :
    natCorrelation (350 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_351 :
    natCorrelation (351 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_352 :
    natCorrelation (352 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_353 :
    natCorrelation (353 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_354 :
    natCorrelation (354 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk32 (i : Fin 10) :
    let d : Cyc := ((345 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_345
  · exact phaseCorrelation_of_nat nat_phase_correlation_346
  · exact phaseCorrelation_of_nat nat_phase_correlation_347
  · exact phaseCorrelation_of_nat nat_phase_correlation_348
  · exact phaseCorrelation_of_nat nat_phase_correlation_349
  · exact phaseCorrelation_of_nat nat_phase_correlation_350
  · exact phaseCorrelation_of_nat nat_phase_correlation_351
  · exact phaseCorrelation_of_nat nat_phase_correlation_352
  · exact phaseCorrelation_of_nat nat_phase_correlation_353
  · exact phaseCorrelation_of_nat nat_phase_correlation_354

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
