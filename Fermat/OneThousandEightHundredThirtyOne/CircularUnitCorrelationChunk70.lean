import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk67
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk68
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk69

/-!
# Cyclic-correlation data at exponent 1831: residues 725--734

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

private theorem nat_phase_correlation_725 :
    natCorrelation (725 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_726 :
    natCorrelation (726 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_727 :
    natCorrelation (727 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_728 :
    natCorrelation (728 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_729 :
    natCorrelation (729 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_730 :
    natCorrelation (730 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_731 :
    natCorrelation (731 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_732 :
    natCorrelation (732 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_733 :
    natCorrelation (733 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_734 :
    natCorrelation (734 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk70 (i : Fin 10) :
    let d : Cyc := ((725 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_725
  · exact phaseCorrelation_of_nat nat_phase_correlation_726
  · exact phaseCorrelation_of_nat nat_phase_correlation_727
  · exact phaseCorrelation_of_nat nat_phase_correlation_728
  · exact phaseCorrelation_of_nat nat_phase_correlation_729
  · exact phaseCorrelation_of_nat nat_phase_correlation_730
  · exact phaseCorrelation_of_nat nat_phase_correlation_731
  · exact phaseCorrelation_of_nat nat_phase_correlation_732
  · exact phaseCorrelation_of_nat nat_phase_correlation_733
  · exact phaseCorrelation_of_nat nat_phase_correlation_734

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
