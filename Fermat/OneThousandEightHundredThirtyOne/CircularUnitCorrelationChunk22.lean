import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk19
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk20
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk21

/-!
# Cyclic-correlation data at exponent 1831: residues 245--254

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

private theorem nat_phase_correlation_245 :
    natCorrelation (245 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_246 :
    natCorrelation (246 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_247 :
    natCorrelation (247 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_248 :
    natCorrelation (248 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_249 :
    natCorrelation (249 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_250 :
    natCorrelation (250 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_251 :
    natCorrelation (251 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_252 :
    natCorrelation (252 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_253 :
    natCorrelation (253 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_254 :
    natCorrelation (254 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk22 (i : Fin 10) :
    let d : Cyc := ((245 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_245
  · exact phaseCorrelation_of_nat nat_phase_correlation_246
  · exact phaseCorrelation_of_nat nat_phase_correlation_247
  · exact phaseCorrelation_of_nat nat_phase_correlation_248
  · exact phaseCorrelation_of_nat nat_phase_correlation_249
  · exact phaseCorrelation_of_nat nat_phase_correlation_250
  · exact phaseCorrelation_of_nat nat_phase_correlation_251
  · exact phaseCorrelation_of_nat nat_phase_correlation_252
  · exact phaseCorrelation_of_nat nat_phase_correlation_253
  · exact phaseCorrelation_of_nat nat_phase_correlation_254

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
