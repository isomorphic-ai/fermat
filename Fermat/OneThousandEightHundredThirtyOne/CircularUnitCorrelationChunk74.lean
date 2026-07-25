import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk70
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk71
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk72

/-!
# Cyclic-correlation data at exponent 1831: residues 765--774

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

private theorem nat_phase_correlation_765 :
    natCorrelation (765 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_766 :
    natCorrelation (766 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_767 :
    natCorrelation (767 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_768 :
    natCorrelation (768 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_769 :
    natCorrelation (769 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_770 :
    natCorrelation (770 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_771 :
    natCorrelation (771 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_772 :
    natCorrelation (772 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_773 :
    natCorrelation (773 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_774 :
    natCorrelation (774 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk74 (i : Fin 10) :
    let d : Cyc := ((765 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_765
  · exact phaseCorrelation_of_nat nat_phase_correlation_766
  · exact phaseCorrelation_of_nat nat_phase_correlation_767
  · exact phaseCorrelation_of_nat nat_phase_correlation_768
  · exact phaseCorrelation_of_nat nat_phase_correlation_769
  · exact phaseCorrelation_of_nat nat_phase_correlation_770
  · exact phaseCorrelation_of_nat nat_phase_correlation_771
  · exact phaseCorrelation_of_nat nat_phase_correlation_772
  · exact phaseCorrelation_of_nat nat_phase_correlation_773
  · exact phaseCorrelation_of_nat nat_phase_correlation_774

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
