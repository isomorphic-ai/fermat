import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk46
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk47
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk48

/-!
# Cyclic-correlation data at exponent 1831: residues 525--534

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

private theorem nat_phase_correlation_525 :
    natCorrelation (525 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_526 :
    natCorrelation (526 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_527 :
    natCorrelation (527 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_528 :
    natCorrelation (528 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_529 :
    natCorrelation (529 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_530 :
    natCorrelation (530 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_531 :
    natCorrelation (531 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_532 :
    natCorrelation (532 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_533 :
    natCorrelation (533 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_534 :
    natCorrelation (534 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk50 (i : Fin 10) :
    let d : Cyc := ((525 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_525
  · exact phaseCorrelation_of_nat nat_phase_correlation_526
  · exact phaseCorrelation_of_nat nat_phase_correlation_527
  · exact phaseCorrelation_of_nat nat_phase_correlation_528
  · exact phaseCorrelation_of_nat nat_phase_correlation_529
  · exact phaseCorrelation_of_nat nat_phase_correlation_530
  · exact phaseCorrelation_of_nat nat_phase_correlation_531
  · exact phaseCorrelation_of_nat nat_phase_correlation_532
  · exact phaseCorrelation_of_nat nat_phase_correlation_533
  · exact phaseCorrelation_of_nat nat_phase_correlation_534

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
