import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk73
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk74
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk75

/-!
# Cyclic-correlation data at exponent 1831: residues 785--794

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

private theorem nat_phase_correlation_785 :
    natCorrelation (785 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_786 :
    natCorrelation (786 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_787 :
    natCorrelation (787 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_788 :
    natCorrelation (788 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_789 :
    natCorrelation (789 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_790 :
    natCorrelation (790 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_791 :
    natCorrelation (791 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_792 :
    natCorrelation (792 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_793 :
    natCorrelation (793 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_794 :
    natCorrelation (794 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk76 (i : Fin 10) :
    let d : Cyc := ((785 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_785
  · exact phaseCorrelation_of_nat nat_phase_correlation_786
  · exact phaseCorrelation_of_nat nat_phase_correlation_787
  · exact phaseCorrelation_of_nat nat_phase_correlation_788
  · exact phaseCorrelation_of_nat nat_phase_correlation_789
  · exact phaseCorrelation_of_nat nat_phase_correlation_790
  · exact phaseCorrelation_of_nat nat_phase_correlation_791
  · exact phaseCorrelation_of_nat nat_phase_correlation_792
  · exact phaseCorrelation_of_nat nat_phase_correlation_793
  · exact phaseCorrelation_of_nat nat_phase_correlation_794

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
