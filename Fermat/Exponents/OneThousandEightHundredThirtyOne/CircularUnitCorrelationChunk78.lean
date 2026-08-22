import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk73
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk74
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk75

/-!
# Cyclic-correlation data at exponent 1831: residues 805--814

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

private theorem nat_phase_correlation_805 :
    natCorrelation (805 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_806 :
    natCorrelation (806 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_807 :
    natCorrelation (807 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_808 :
    natCorrelation (808 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_809 :
    natCorrelation (809 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_810 :
    natCorrelation (810 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_811 :
    natCorrelation (811 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_812 :
    natCorrelation (812 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_813 :
    natCorrelation (813 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_814 :
    natCorrelation (814 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk78 (i : Fin 10) :
    let d : Cyc := ((805 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_805
  · exact phaseCorrelation_of_nat nat_phase_correlation_806
  · exact phaseCorrelation_of_nat nat_phase_correlation_807
  · exact phaseCorrelation_of_nat nat_phase_correlation_808
  · exact phaseCorrelation_of_nat nat_phase_correlation_809
  · exact phaseCorrelation_of_nat nat_phase_correlation_810
  · exact phaseCorrelation_of_nat nat_phase_correlation_811
  · exact phaseCorrelation_of_nat nat_phase_correlation_812
  · exact phaseCorrelation_of_nat nat_phase_correlation_813
  · exact phaseCorrelation_of_nat nat_phase_correlation_814

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
