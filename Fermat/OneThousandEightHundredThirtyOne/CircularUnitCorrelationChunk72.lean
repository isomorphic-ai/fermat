import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk67
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk68
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk69

/-!
# Cyclic-correlation data at exponent 1831: residues 745--754

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

private theorem nat_phase_correlation_745 :
    natCorrelation (745 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_746 :
    natCorrelation (746 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_747 :
    natCorrelation (747 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_748 :
    natCorrelation (748 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_749 :
    natCorrelation (749 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_750 :
    natCorrelation (750 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_751 :
    natCorrelation (751 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_752 :
    natCorrelation (752 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_753 :
    natCorrelation (753 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_754 :
    natCorrelation (754 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk72 (i : Fin 10) :
    let d : Cyc := ((745 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_745
  · exact phaseCorrelation_of_nat nat_phase_correlation_746
  · exact phaseCorrelation_of_nat nat_phase_correlation_747
  · exact phaseCorrelation_of_nat nat_phase_correlation_748
  · exact phaseCorrelation_of_nat nat_phase_correlation_749
  · exact phaseCorrelation_of_nat nat_phase_correlation_750
  · exact phaseCorrelation_of_nat nat_phase_correlation_751
  · exact phaseCorrelation_of_nat nat_phase_correlation_752
  · exact phaseCorrelation_of_nat nat_phase_correlation_753
  · exact phaseCorrelation_of_nat nat_phase_correlation_754

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
