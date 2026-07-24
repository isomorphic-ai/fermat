import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk46
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk47
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk48

/-!
# Cyclic-correlation data at exponent 1381: residues 535--544

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_535 :
    natCorrelation (535 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_536 :
    natCorrelation (536 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_537 :
    natCorrelation (537 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_538 :
    natCorrelation (538 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_539 :
    natCorrelation (539 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_540 :
    natCorrelation (540 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_541 :
    natCorrelation (541 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_542 :
    natCorrelation (542 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_543 :
    natCorrelation (543 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_544 :
    natCorrelation (544 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk51 (i : Fin 10) :
    let d : Cyc := ((535 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_535
  · exact phaseCorrelation_of_nat nat_phase_correlation_536
  · exact phaseCorrelation_of_nat nat_phase_correlation_537
  · exact phaseCorrelation_of_nat nat_phase_correlation_538
  · exact phaseCorrelation_of_nat nat_phase_correlation_539
  · exact phaseCorrelation_of_nat nat_phase_correlation_540
  · exact phaseCorrelation_of_nat nat_phase_correlation_541
  · exact phaseCorrelation_of_nat nat_phase_correlation_542
  · exact phaseCorrelation_of_nat nat_phase_correlation_543
  · exact phaseCorrelation_of_nat nat_phase_correlation_544

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
