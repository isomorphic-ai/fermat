import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk19
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk20
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk21

/-!
# Cyclic-correlation data at exponent 1831: residues 265--274

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

private theorem nat_phase_correlation_265 :
    natCorrelation (265 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_266 :
    natCorrelation (266 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_267 :
    natCorrelation (267 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_268 :
    natCorrelation (268 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_269 :
    natCorrelation (269 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_270 :
    natCorrelation (270 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_271 :
    natCorrelation (271 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_272 :
    natCorrelation (272 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_273 :
    natCorrelation (273 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_274 :
    natCorrelation (274 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk24 (i : Fin 10) :
    let d : Cyc := ((265 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_265
  · exact phaseCorrelation_of_nat nat_phase_correlation_266
  · exact phaseCorrelation_of_nat nat_phase_correlation_267
  · exact phaseCorrelation_of_nat nat_phase_correlation_268
  · exact phaseCorrelation_of_nat nat_phase_correlation_269
  · exact phaseCorrelation_of_nat nat_phase_correlation_270
  · exact phaseCorrelation_of_nat nat_phase_correlation_271
  · exact phaseCorrelation_of_nat nat_phase_correlation_272
  · exact phaseCorrelation_of_nat nat_phase_correlation_273
  · exact phaseCorrelation_of_nat nat_phase_correlation_274

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
