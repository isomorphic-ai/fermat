import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk82
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk83
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk84

/-!
# Cyclic-correlation data at exponent 1831: residues 895--904

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

private theorem nat_phase_correlation_895 :
    natCorrelation (895 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_896 :
    natCorrelation (896 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_897 :
    natCorrelation (897 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_898 :
    natCorrelation (898 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_899 :
    natCorrelation (899 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_900 :
    natCorrelation (900 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_901 :
    natCorrelation (901 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_902 :
    natCorrelation (902 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_903 :
    natCorrelation (903 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_904 :
    natCorrelation (904 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk87 (i : Fin 10) :
    let d : Cyc := ((895 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_895
  · exact phaseCorrelation_of_nat nat_phase_correlation_896
  · exact phaseCorrelation_of_nat nat_phase_correlation_897
  · exact phaseCorrelation_of_nat nat_phase_correlation_898
  · exact phaseCorrelation_of_nat nat_phase_correlation_899
  · exact phaseCorrelation_of_nat nat_phase_correlation_900
  · exact phaseCorrelation_of_nat nat_phase_correlation_901
  · exact phaseCorrelation_of_nat nat_phase_correlation_902
  · exact phaseCorrelation_of_nat nat_phase_correlation_903
  · exact phaseCorrelation_of_nat nat_phase_correlation_904

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
