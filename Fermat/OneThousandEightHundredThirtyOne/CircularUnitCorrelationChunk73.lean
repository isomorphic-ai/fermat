import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk70
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk71
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk72

/-!
# Cyclic-correlation data at exponent 1831: residues 755--764

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

private theorem nat_phase_correlation_755 :
    natCorrelation (755 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_756 :
    natCorrelation (756 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_757 :
    natCorrelation (757 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_758 :
    natCorrelation (758 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_759 :
    natCorrelation (759 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_760 :
    natCorrelation (760 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_761 :
    natCorrelation (761 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_762 :
    natCorrelation (762 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_763 :
    natCorrelation (763 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_764 :
    natCorrelation (764 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk73 (i : Fin 10) :
    let d : Cyc := ((755 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_755
  · exact phaseCorrelation_of_nat nat_phase_correlation_756
  · exact phaseCorrelation_of_nat nat_phase_correlation_757
  · exact phaseCorrelation_of_nat nat_phase_correlation_758
  · exact phaseCorrelation_of_nat nat_phase_correlation_759
  · exact phaseCorrelation_of_nat nat_phase_correlation_760
  · exact phaseCorrelation_of_nat nat_phase_correlation_761
  · exact phaseCorrelation_of_nat nat_phase_correlation_762
  · exact phaseCorrelation_of_nat nat_phase_correlation_763
  · exact phaseCorrelation_of_nat nat_phase_correlation_764

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
