import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk79
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk80
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk81

/-!
# Cyclic-correlation data at exponent 1831: residues 865--874

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

private theorem nat_phase_correlation_865 :
    natCorrelation (865 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_866 :
    natCorrelation (866 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_867 :
    natCorrelation (867 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_868 :
    natCorrelation (868 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_869 :
    natCorrelation (869 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_870 :
    natCorrelation (870 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_871 :
    natCorrelation (871 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_872 :
    natCorrelation (872 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_873 :
    natCorrelation (873 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_874 :
    natCorrelation (874 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk84 (i : Fin 10) :
    let d : Cyc := ((865 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_865
  · exact phaseCorrelation_of_nat nat_phase_correlation_866
  · exact phaseCorrelation_of_nat nat_phase_correlation_867
  · exact phaseCorrelation_of_nat nat_phase_correlation_868
  · exact phaseCorrelation_of_nat nat_phase_correlation_869
  · exact phaseCorrelation_of_nat nat_phase_correlation_870
  · exact phaseCorrelation_of_nat nat_phase_correlation_871
  · exact phaseCorrelation_of_nat nat_phase_correlation_872
  · exact phaseCorrelation_of_nat nat_phase_correlation_873
  · exact phaseCorrelation_of_nat nat_phase_correlation_874

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
