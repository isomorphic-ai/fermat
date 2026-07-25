import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk37
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk38
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk39

/-!
# Cyclic-correlation data at exponent 1831: residues 445--454

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

private theorem nat_phase_correlation_445 :
    natCorrelation (445 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_446 :
    natCorrelation (446 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_447 :
    natCorrelation (447 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_448 :
    natCorrelation (448 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_449 :
    natCorrelation (449 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_450 :
    natCorrelation (450 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_451 :
    natCorrelation (451 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_452 :
    natCorrelation (452 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_453 :
    natCorrelation (453 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_454 :
    natCorrelation (454 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk42 (i : Fin 10) :
    let d : Cyc := ((445 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_445
  · exact phaseCorrelation_of_nat nat_phase_correlation_446
  · exact phaseCorrelation_of_nat nat_phase_correlation_447
  · exact phaseCorrelation_of_nat nat_phase_correlation_448
  · exact phaseCorrelation_of_nat nat_phase_correlation_449
  · exact phaseCorrelation_of_nat nat_phase_correlation_450
  · exact phaseCorrelation_of_nat nat_phase_correlation_451
  · exact phaseCorrelation_of_nat nat_phase_correlation_452
  · exact phaseCorrelation_of_nat nat_phase_correlation_453
  · exact phaseCorrelation_of_nat nat_phase_correlation_454

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
