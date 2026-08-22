import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk67
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk68
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk69

/-!
# Cyclic-correlation data at exponent 1831: residues 735--744

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

private theorem nat_phase_correlation_735 :
    natCorrelation (735 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_736 :
    natCorrelation (736 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_737 :
    natCorrelation (737 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_738 :
    natCorrelation (738 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_739 :
    natCorrelation (739 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_740 :
    natCorrelation (740 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_741 :
    natCorrelation (741 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_742 :
    natCorrelation (742 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_743 :
    natCorrelation (743 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_744 :
    natCorrelation (744 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk71 (i : Fin 10) :
    let d : Cyc := ((735 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_735
  · exact phaseCorrelation_of_nat nat_phase_correlation_736
  · exact phaseCorrelation_of_nat nat_phase_correlation_737
  · exact phaseCorrelation_of_nat nat_phase_correlation_738
  · exact phaseCorrelation_of_nat nat_phase_correlation_739
  · exact phaseCorrelation_of_nat nat_phase_correlation_740
  · exact phaseCorrelation_of_nat nat_phase_correlation_741
  · exact phaseCorrelation_of_nat nat_phase_correlation_742
  · exact phaseCorrelation_of_nat nat_phase_correlation_743
  · exact phaseCorrelation_of_nat nat_phase_correlation_744

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
