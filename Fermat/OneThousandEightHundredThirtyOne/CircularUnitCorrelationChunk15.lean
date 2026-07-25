import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk10
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk11
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk12

/-!
# Cyclic-correlation data at exponent 1831: residues 175--184

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

private theorem nat_phase_correlation_175 :
    natCorrelation (175 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_176 :
    natCorrelation (176 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_177 :
    natCorrelation (177 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_178 :
    natCorrelation (178 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_179 :
    natCorrelation (179 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_180 :
    natCorrelation (180 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_181 :
    natCorrelation (181 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_182 :
    natCorrelation (182 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_183 :
    natCorrelation (183 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_184 :
    natCorrelation (184 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk15 (i : Fin 10) :
    let d : Cyc := ((175 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_175
  · exact phaseCorrelation_of_nat nat_phase_correlation_176
  · exact phaseCorrelation_of_nat nat_phase_correlation_177
  · exact phaseCorrelation_of_nat nat_phase_correlation_178
  · exact phaseCorrelation_of_nat nat_phase_correlation_179
  · exact phaseCorrelation_of_nat nat_phase_correlation_180
  · exact phaseCorrelation_of_nat nat_phase_correlation_181
  · exact phaseCorrelation_of_nat nat_phase_correlation_182
  · exact phaseCorrelation_of_nat nat_phase_correlation_183
  · exact phaseCorrelation_of_nat nat_phase_correlation_184

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
