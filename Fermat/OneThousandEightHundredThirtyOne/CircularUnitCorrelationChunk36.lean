import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk31
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk32
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk33

/-!
# Cyclic-correlation data at exponent 1831: residues 385--394

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

private theorem nat_phase_correlation_385 :
    natCorrelation (385 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_386 :
    natCorrelation (386 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_387 :
    natCorrelation (387 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_388 :
    natCorrelation (388 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_389 :
    natCorrelation (389 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_390 :
    natCorrelation (390 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_391 :
    natCorrelation (391 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_392 :
    natCorrelation (392 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_393 :
    natCorrelation (393 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_394 :
    natCorrelation (394 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk36 (i : Fin 10) :
    let d : Cyc := ((385 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_385
  · exact phaseCorrelation_of_nat nat_phase_correlation_386
  · exact phaseCorrelation_of_nat nat_phase_correlation_387
  · exact phaseCorrelation_of_nat nat_phase_correlation_388
  · exact phaseCorrelation_of_nat nat_phase_correlation_389
  · exact phaseCorrelation_of_nat nat_phase_correlation_390
  · exact phaseCorrelation_of_nat nat_phase_correlation_391
  · exact phaseCorrelation_of_nat nat_phase_correlation_392
  · exact phaseCorrelation_of_nat nat_phase_correlation_393
  · exact phaseCorrelation_of_nat nat_phase_correlation_394

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
