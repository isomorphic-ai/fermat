import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk82
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk83
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk84

/-!
# Cyclic-correlation data at exponent 1831: residues 875--884

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

private theorem nat_phase_correlation_875 :
    natCorrelation (875 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_876 :
    natCorrelation (876 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_877 :
    natCorrelation (877 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_878 :
    natCorrelation (878 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_879 :
    natCorrelation (879 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_880 :
    natCorrelation (880 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_881 :
    natCorrelation (881 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_882 :
    natCorrelation (882 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_883 :
    natCorrelation (883 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_884 :
    natCorrelation (884 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk85 (i : Fin 10) :
    let d : Cyc := ((875 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_875
  · exact phaseCorrelation_of_nat nat_phase_correlation_876
  · exact phaseCorrelation_of_nat nat_phase_correlation_877
  · exact phaseCorrelation_of_nat nat_phase_correlation_878
  · exact phaseCorrelation_of_nat nat_phase_correlation_879
  · exact phaseCorrelation_of_nat nat_phase_correlation_880
  · exact phaseCorrelation_of_nat nat_phase_correlation_881
  · exact phaseCorrelation_of_nat nat_phase_correlation_882
  · exact phaseCorrelation_of_nat nat_phase_correlation_883
  · exact phaseCorrelation_of_nat nat_phase_correlation_884

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
