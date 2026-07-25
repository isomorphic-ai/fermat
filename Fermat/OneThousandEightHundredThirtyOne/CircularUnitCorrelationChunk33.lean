import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk28
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk29
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk30

/-!
# Cyclic-correlation data at exponent 1831: residues 355--364

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

private theorem nat_phase_correlation_355 :
    natCorrelation (355 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_356 :
    natCorrelation (356 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_357 :
    natCorrelation (357 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_358 :
    natCorrelation (358 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_359 :
    natCorrelation (359 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_360 :
    natCorrelation (360 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_361 :
    natCorrelation (361 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_362 :
    natCorrelation (362 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_363 :
    natCorrelation (363 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_364 :
    natCorrelation (364 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk33 (i : Fin 10) :
    let d : Cyc := ((355 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_355
  · exact phaseCorrelation_of_nat nat_phase_correlation_356
  · exact phaseCorrelation_of_nat nat_phase_correlation_357
  · exact phaseCorrelation_of_nat nat_phase_correlation_358
  · exact phaseCorrelation_of_nat nat_phase_correlation_359
  · exact phaseCorrelation_of_nat nat_phase_correlation_360
  · exact phaseCorrelation_of_nat nat_phase_correlation_361
  · exact phaseCorrelation_of_nat nat_phase_correlation_362
  · exact phaseCorrelation_of_nat nat_phase_correlation_363
  · exact phaseCorrelation_of_nat nat_phase_correlation_364

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
