import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk64
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk65
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk66

/-!
# Cyclic-correlation data at exponent 1831: residues 695--704

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

private theorem nat_phase_correlation_695 :
    natCorrelation (695 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_696 :
    natCorrelation (696 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_697 :
    natCorrelation (697 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_698 :
    natCorrelation (698 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_699 :
    natCorrelation (699 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_700 :
    natCorrelation (700 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_701 :
    natCorrelation (701 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_702 :
    natCorrelation (702 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_703 :
    natCorrelation (703 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_704 :
    natCorrelation (704 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk67 (i : Fin 10) :
    let d : Cyc := ((695 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_695
  · exact phaseCorrelation_of_nat nat_phase_correlation_696
  · exact phaseCorrelation_of_nat nat_phase_correlation_697
  · exact phaseCorrelation_of_nat nat_phase_correlation_698
  · exact phaseCorrelation_of_nat nat_phase_correlation_699
  · exact phaseCorrelation_of_nat nat_phase_correlation_700
  · exact phaseCorrelation_of_nat nat_phase_correlation_701
  · exact phaseCorrelation_of_nat nat_phase_correlation_702
  · exact phaseCorrelation_of_nat nat_phase_correlation_703
  · exact phaseCorrelation_of_nat nat_phase_correlation_704

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
