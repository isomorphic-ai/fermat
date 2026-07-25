import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk25
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk26
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk27

/-!
# Cyclic-correlation data at exponent 1831: residues 325--334

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

private theorem nat_phase_correlation_325 :
    natCorrelation (325 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_326 :
    natCorrelation (326 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_327 :
    natCorrelation (327 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_328 :
    natCorrelation (328 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_329 :
    natCorrelation (329 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_330 :
    natCorrelation (330 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_331 :
    natCorrelation (331 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_332 :
    natCorrelation (332 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_333 :
    natCorrelation (333 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_334 :
    natCorrelation (334 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk30 (i : Fin 10) :
    let d : Cyc := ((325 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_325
  · exact phaseCorrelation_of_nat nat_phase_correlation_326
  · exact phaseCorrelation_of_nat nat_phase_correlation_327
  · exact phaseCorrelation_of_nat nat_phase_correlation_328
  · exact phaseCorrelation_of_nat nat_phase_correlation_329
  · exact phaseCorrelation_of_nat nat_phase_correlation_330
  · exact phaseCorrelation_of_nat nat_phase_correlation_331
  · exact phaseCorrelation_of_nat nat_phase_correlation_332
  · exact phaseCorrelation_of_nat nat_phase_correlation_333
  · exact phaseCorrelation_of_nat nat_phase_correlation_334

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
