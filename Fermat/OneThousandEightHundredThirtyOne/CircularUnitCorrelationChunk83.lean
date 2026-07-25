import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk79
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk80
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk81

/-!
# Cyclic-correlation data at exponent 1831: residues 855--864

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

private theorem nat_phase_correlation_855 :
    natCorrelation (855 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_856 :
    natCorrelation (856 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_857 :
    natCorrelation (857 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_858 :
    natCorrelation (858 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_859 :
    natCorrelation (859 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_860 :
    natCorrelation (860 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_861 :
    natCorrelation (861 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_862 :
    natCorrelation (862 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_863 :
    natCorrelation (863 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_864 :
    natCorrelation (864 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk83 (i : Fin 10) :
    let d : Cyc := ((855 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_855
  · exact phaseCorrelation_of_nat nat_phase_correlation_856
  · exact phaseCorrelation_of_nat nat_phase_correlation_857
  · exact phaseCorrelation_of_nat nat_phase_correlation_858
  · exact phaseCorrelation_of_nat nat_phase_correlation_859
  · exact phaseCorrelation_of_nat nat_phase_correlation_860
  · exact phaseCorrelation_of_nat nat_phase_correlation_861
  · exact phaseCorrelation_of_nat nat_phase_correlation_862
  · exact phaseCorrelation_of_nat nat_phase_correlation_863
  · exact phaseCorrelation_of_nat nat_phase_correlation_864

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
