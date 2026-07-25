import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk37
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk38
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk39

/-!
# Cyclic-correlation data at exponent 1831: residues 435--444

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

private theorem nat_phase_correlation_435 :
    natCorrelation (435 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_436 :
    natCorrelation (436 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_437 :
    natCorrelation (437 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_438 :
    natCorrelation (438 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_439 :
    natCorrelation (439 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_440 :
    natCorrelation (440 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_441 :
    natCorrelation (441 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_442 :
    natCorrelation (442 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_443 :
    natCorrelation (443 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_444 :
    natCorrelation (444 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk41 (i : Fin 10) :
    let d : Cyc := ((435 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_435
  · exact phaseCorrelation_of_nat nat_phase_correlation_436
  · exact phaseCorrelation_of_nat nat_phase_correlation_437
  · exact phaseCorrelation_of_nat nat_phase_correlation_438
  · exact phaseCorrelation_of_nat nat_phase_correlation_439
  · exact phaseCorrelation_of_nat nat_phase_correlation_440
  · exact phaseCorrelation_of_nat nat_phase_correlation_441
  · exact phaseCorrelation_of_nat nat_phase_correlation_442
  · exact phaseCorrelation_of_nat nat_phase_correlation_443
  · exact phaseCorrelation_of_nat nat_phase_correlation_444

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
