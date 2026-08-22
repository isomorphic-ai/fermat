import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk76
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk77
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk78

/-!
# Cyclic-correlation data at exponent 1831: residues 825--834

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

private theorem nat_phase_correlation_825 :
    natCorrelation (825 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_826 :
    natCorrelation (826 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_827 :
    natCorrelation (827 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_828 :
    natCorrelation (828 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_829 :
    natCorrelation (829 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_830 :
    natCorrelation (830 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_831 :
    natCorrelation (831 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_832 :
    natCorrelation (832 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_833 :
    natCorrelation (833 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_834 :
    natCorrelation (834 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk80 (i : Fin 10) :
    let d : Cyc := ((825 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_825
  · exact phaseCorrelation_of_nat nat_phase_correlation_826
  · exact phaseCorrelation_of_nat nat_phase_correlation_827
  · exact phaseCorrelation_of_nat nat_phase_correlation_828
  · exact phaseCorrelation_of_nat nat_phase_correlation_829
  · exact phaseCorrelation_of_nat nat_phase_correlation_830
  · exact phaseCorrelation_of_nat nat_phase_correlation_831
  · exact phaseCorrelation_of_nat nat_phase_correlation_832
  · exact phaseCorrelation_of_nat nat_phase_correlation_833
  · exact phaseCorrelation_of_nat nat_phase_correlation_834

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
