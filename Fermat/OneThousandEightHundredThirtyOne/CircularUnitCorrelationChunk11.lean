import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk7
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk8
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk9

/-!
# Cyclic-correlation data at exponent 1831: residues 135--144

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

private theorem nat_phase_correlation_135 :
    natCorrelation (135 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_136 :
    natCorrelation (136 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_137 :
    natCorrelation (137 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_138 :
    natCorrelation (138 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_139 :
    natCorrelation (139 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_140 :
    natCorrelation (140 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_141 :
    natCorrelation (141 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_142 :
    natCorrelation (142 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_143 :
    natCorrelation (143 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_144 :
    natCorrelation (144 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk11 (i : Fin 10) :
    let d : Cyc := ((135 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_135
  · exact phaseCorrelation_of_nat nat_phase_correlation_136
  · exact phaseCorrelation_of_nat nat_phase_correlation_137
  · exact phaseCorrelation_of_nat nat_phase_correlation_138
  · exact phaseCorrelation_of_nat nat_phase_correlation_139
  · exact phaseCorrelation_of_nat nat_phase_correlation_140
  · exact phaseCorrelation_of_nat nat_phase_correlation_141
  · exact phaseCorrelation_of_nat nat_phase_correlation_142
  · exact phaseCorrelation_of_nat nat_phase_correlation_143
  · exact phaseCorrelation_of_nat nat_phase_correlation_144

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
