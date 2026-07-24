import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk61
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk62
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk63

/-!
# Cyclic-correlation data at exponent 1381: residues 685--689

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

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk66 (i : Fin 5) :
    let d : Cyc := ((685 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_685
  · exact phaseCorrelation_of_nat nat_phase_correlation_686
  · exact phaseCorrelation_of_nat nat_phase_correlation_687
  · exact phaseCorrelation_of_nat nat_phase_correlation_688
  · exact phaseCorrelation_of_nat nat_phase_correlation_689

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
