import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk40
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk41
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk42

/-!
# Cyclic-correlation data at exponent 1831: residues 465--474

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

private theorem nat_phase_correlation_465 :
    natCorrelation (465 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_466 :
    natCorrelation (466 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_467 :
    natCorrelation (467 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_468 :
    natCorrelation (468 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_469 :
    natCorrelation (469 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_470 :
    natCorrelation (470 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_471 :
    natCorrelation (471 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_472 :
    natCorrelation (472 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_473 :
    natCorrelation (473 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_474 :
    natCorrelation (474 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk44 (i : Fin 10) :
    let d : Cyc := ((465 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_465
  · exact phaseCorrelation_of_nat nat_phase_correlation_466
  · exact phaseCorrelation_of_nat nat_phase_correlation_467
  · exact phaseCorrelation_of_nat nat_phase_correlation_468
  · exact phaseCorrelation_of_nat nat_phase_correlation_469
  · exact phaseCorrelation_of_nat nat_phase_correlation_470
  · exact phaseCorrelation_of_nat nat_phase_correlation_471
  · exact phaseCorrelation_of_nat nat_phase_correlation_472
  · exact phaseCorrelation_of_nat nat_phase_correlation_473
  · exact phaseCorrelation_of_nat nat_phase_correlation_474

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
