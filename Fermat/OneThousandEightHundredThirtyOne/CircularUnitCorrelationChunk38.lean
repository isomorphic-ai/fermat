import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk34
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk35
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk36

/-!
# Cyclic-correlation data at exponent 1831: residues 405--414

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

private theorem nat_phase_correlation_405 :
    natCorrelation (405 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_406 :
    natCorrelation (406 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_407 :
    natCorrelation (407 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_408 :
    natCorrelation (408 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_409 :
    natCorrelation (409 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_410 :
    natCorrelation (410 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_411 :
    natCorrelation (411 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_412 :
    natCorrelation (412 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_413 :
    natCorrelation (413 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_414 :
    natCorrelation (414 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk38 (i : Fin 10) :
    let d : Cyc := ((405 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_405
  · exact phaseCorrelation_of_nat nat_phase_correlation_406
  · exact phaseCorrelation_of_nat nat_phase_correlation_407
  · exact phaseCorrelation_of_nat nat_phase_correlation_408
  · exact phaseCorrelation_of_nat nat_phase_correlation_409
  · exact phaseCorrelation_of_nat nat_phase_correlation_410
  · exact phaseCorrelation_of_nat nat_phase_correlation_411
  · exact phaseCorrelation_of_nat nat_phase_correlation_412
  · exact phaseCorrelation_of_nat nat_phase_correlation_413
  · exact phaseCorrelation_of_nat nat_phase_correlation_414

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
