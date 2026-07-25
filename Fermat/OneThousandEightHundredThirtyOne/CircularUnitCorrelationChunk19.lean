import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk16
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk17
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk18

/-!
# Cyclic-correlation data at exponent 1831: residues 215--224

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

private theorem nat_phase_correlation_215 :
    natCorrelation (215 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_216 :
    natCorrelation (216 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_217 :
    natCorrelation (217 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_218 :
    natCorrelation (218 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_219 :
    natCorrelation (219 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_220 :
    natCorrelation (220 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_221 :
    natCorrelation (221 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_222 :
    natCorrelation (222 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_223 :
    natCorrelation (223 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_224 :
    natCorrelation (224 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk19 (i : Fin 10) :
    let d : Cyc := ((215 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_215
  · exact phaseCorrelation_of_nat nat_phase_correlation_216
  · exact phaseCorrelation_of_nat nat_phase_correlation_217
  · exact phaseCorrelation_of_nat nat_phase_correlation_218
  · exact phaseCorrelation_of_nat nat_phase_correlation_219
  · exact phaseCorrelation_of_nat nat_phase_correlation_220
  · exact phaseCorrelation_of_nat nat_phase_correlation_221
  · exact phaseCorrelation_of_nat nat_phase_correlation_222
  · exact phaseCorrelation_of_nat nat_phase_correlation_223
  · exact phaseCorrelation_of_nat nat_phase_correlation_224

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
