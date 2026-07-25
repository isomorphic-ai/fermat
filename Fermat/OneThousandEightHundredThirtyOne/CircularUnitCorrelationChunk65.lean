import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk61
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk62
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk63

/-!
# Cyclic-correlation data at exponent 1831: residues 675--684

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

private theorem nat_phase_correlation_675 :
    natCorrelation (675 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_676 :
    natCorrelation (676 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_677 :
    natCorrelation (677 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_678 :
    natCorrelation (678 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_679 :
    natCorrelation (679 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_680 :
    natCorrelation (680 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_681 :
    natCorrelation (681 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_682 :
    natCorrelation (682 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_683 :
    natCorrelation (683 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_684 :
    natCorrelation (684 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk65 (i : Fin 10) :
    let d : Cyc := ((675 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_675
  · exact phaseCorrelation_of_nat nat_phase_correlation_676
  · exact phaseCorrelation_of_nat nat_phase_correlation_677
  · exact phaseCorrelation_of_nat nat_phase_correlation_678
  · exact phaseCorrelation_of_nat nat_phase_correlation_679
  · exact phaseCorrelation_of_nat nat_phase_correlation_680
  · exact phaseCorrelation_of_nat nat_phase_correlation_681
  · exact phaseCorrelation_of_nat nat_phase_correlation_682
  · exact phaseCorrelation_of_nat nat_phase_correlation_683
  · exact phaseCorrelation_of_nat nat_phase_correlation_684

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
