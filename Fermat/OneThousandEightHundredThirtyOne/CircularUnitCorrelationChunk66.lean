import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk61
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk62
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk63

/-!
# Cyclic-correlation data at exponent 1831: residues 685--694

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

private theorem nat_phase_correlation_685 :
    natCorrelation (685 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_686 :
    natCorrelation (686 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_687 :
    natCorrelation (687 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_688 :
    natCorrelation (688 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_689 :
    natCorrelation (689 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_690 :
    natCorrelation (690 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_691 :
    natCorrelation (691 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_692 :
    natCorrelation (692 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_693 :
    natCorrelation (693 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_694 :
    natCorrelation (694 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk66 (i : Fin 10) :
    let d : Cyc := ((685 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_685
  · exact phaseCorrelation_of_nat nat_phase_correlation_686
  · exact phaseCorrelation_of_nat nat_phase_correlation_687
  · exact phaseCorrelation_of_nat nat_phase_correlation_688
  · exact phaseCorrelation_of_nat nat_phase_correlation_689
  · exact phaseCorrelation_of_nat nat_phase_correlation_690
  · exact phaseCorrelation_of_nat nat_phase_correlation_691
  · exact phaseCorrelation_of_nat nat_phase_correlation_692
  · exact phaseCorrelation_of_nat nat_phase_correlation_693
  · exact phaseCorrelation_of_nat nat_phase_correlation_694

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
