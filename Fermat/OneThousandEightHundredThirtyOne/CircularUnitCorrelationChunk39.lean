import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk34
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk35
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk36

/-!
# Cyclic-correlation data at exponent 1831: residues 415--424

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

private theorem nat_phase_correlation_415 :
    natCorrelation (415 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_416 :
    natCorrelation (416 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_417 :
    natCorrelation (417 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_418 :
    natCorrelation (418 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_419 :
    natCorrelation (419 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_420 :
    natCorrelation (420 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_421 :
    natCorrelation (421 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_422 :
    natCorrelation (422 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_423 :
    natCorrelation (423 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_424 :
    natCorrelation (424 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk39 (i : Fin 10) :
    let d : Cyc := ((415 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_415
  · exact phaseCorrelation_of_nat nat_phase_correlation_416
  · exact phaseCorrelation_of_nat nat_phase_correlation_417
  · exact phaseCorrelation_of_nat nat_phase_correlation_418
  · exact phaseCorrelation_of_nat nat_phase_correlation_419
  · exact phaseCorrelation_of_nat nat_phase_correlation_420
  · exact phaseCorrelation_of_nat nat_phase_correlation_421
  · exact phaseCorrelation_of_nat nat_phase_correlation_422
  · exact phaseCorrelation_of_nat nat_phase_correlation_423
  · exact phaseCorrelation_of_nat nat_phase_correlation_424

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
