import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk40
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk41
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk42

/-!
# Cyclic-correlation data at exponent 1831: residues 475--484

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

private theorem nat_phase_correlation_475 :
    natCorrelation (475 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_476 :
    natCorrelation (476 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_477 :
    natCorrelation (477 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_478 :
    natCorrelation (478 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_479 :
    natCorrelation (479 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_480 :
    natCorrelation (480 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_481 :
    natCorrelation (481 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_482 :
    natCorrelation (482 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_483 :
    natCorrelation (483 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_484 :
    natCorrelation (484 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk45 (i : Fin 10) :
    let d : Cyc := ((475 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_475
  · exact phaseCorrelation_of_nat nat_phase_correlation_476
  · exact phaseCorrelation_of_nat nat_phase_correlation_477
  · exact phaseCorrelation_of_nat nat_phase_correlation_478
  · exact phaseCorrelation_of_nat nat_phase_correlation_479
  · exact phaseCorrelation_of_nat nat_phase_correlation_480
  · exact phaseCorrelation_of_nat nat_phase_correlation_481
  · exact phaseCorrelation_of_nat nat_phase_correlation_482
  · exact phaseCorrelation_of_nat nat_phase_correlation_483
  · exact phaseCorrelation_of_nat nat_phase_correlation_484

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
