import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk76
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk77
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk78

/-!
# Cyclic-correlation data at exponent 1831: residues 815--824

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

private theorem nat_phase_correlation_815 :
    natCorrelation (815 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_816 :
    natCorrelation (816 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_817 :
    natCorrelation (817 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_818 :
    natCorrelation (818 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_819 :
    natCorrelation (819 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_820 :
    natCorrelation (820 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_821 :
    natCorrelation (821 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_822 :
    natCorrelation (822 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_823 :
    natCorrelation (823 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_824 :
    natCorrelation (824 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk79 (i : Fin 10) :
    let d : Cyc := ((815 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_815
  · exact phaseCorrelation_of_nat nat_phase_correlation_816
  · exact phaseCorrelation_of_nat nat_phase_correlation_817
  · exact phaseCorrelation_of_nat nat_phase_correlation_818
  · exact phaseCorrelation_of_nat nat_phase_correlation_819
  · exact phaseCorrelation_of_nat nat_phase_correlation_820
  · exact phaseCorrelation_of_nat nat_phase_correlation_821
  · exact phaseCorrelation_of_nat nat_phase_correlation_822
  · exact phaseCorrelation_of_nat nat_phase_correlation_823
  · exact phaseCorrelation_of_nat nat_phase_correlation_824

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
