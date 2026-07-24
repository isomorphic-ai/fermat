import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk52
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk53
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk54

/-!
# Cyclic-correlation data at exponent 1381: residues 585--594

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

private theorem nat_phase_correlation_585 :
    natCorrelation (585 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_586 :
    natCorrelation (586 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_587 :
    natCorrelation (587 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_588 :
    natCorrelation (588 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_589 :
    natCorrelation (589 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_590 :
    natCorrelation (590 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_591 :
    natCorrelation (591 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_592 :
    natCorrelation (592 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_593 :
    natCorrelation (593 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_594 :
    natCorrelation (594 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk56 (i : Fin 10) :
    let d : Cyc := ((585 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_585
  · exact phaseCorrelation_of_nat nat_phase_correlation_586
  · exact phaseCorrelation_of_nat nat_phase_correlation_587
  · exact phaseCorrelation_of_nat nat_phase_correlation_588
  · exact phaseCorrelation_of_nat nat_phase_correlation_589
  · exact phaseCorrelation_of_nat nat_phase_correlation_590
  · exact phaseCorrelation_of_nat nat_phase_correlation_591
  · exact phaseCorrelation_of_nat nat_phase_correlation_592
  · exact phaseCorrelation_of_nat nat_phase_correlation_593
  · exact phaseCorrelation_of_nat nat_phase_correlation_594

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
