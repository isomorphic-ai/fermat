import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk43
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk44
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk45

/-!
# Cyclic-correlation data at exponent 1831: residues 495--504

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

private theorem nat_phase_correlation_495 :
    natCorrelation (495 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_496 :
    natCorrelation (496 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_497 :
    natCorrelation (497 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_498 :
    natCorrelation (498 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_499 :
    natCorrelation (499 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_500 :
    natCorrelation (500 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_501 :
    natCorrelation (501 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_502 :
    natCorrelation (502 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_503 :
    natCorrelation (503 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_504 :
    natCorrelation (504 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk47 (i : Fin 10) :
    let d : Cyc := ((495 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_495
  · exact phaseCorrelation_of_nat nat_phase_correlation_496
  · exact phaseCorrelation_of_nat nat_phase_correlation_497
  · exact phaseCorrelation_of_nat nat_phase_correlation_498
  · exact phaseCorrelation_of_nat nat_phase_correlation_499
  · exact phaseCorrelation_of_nat nat_phase_correlation_500
  · exact phaseCorrelation_of_nat nat_phase_correlation_501
  · exact phaseCorrelation_of_nat nat_phase_correlation_502
  · exact phaseCorrelation_of_nat nat_phase_correlation_503
  · exact phaseCorrelation_of_nat nat_phase_correlation_504

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
