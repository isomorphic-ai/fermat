import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk31
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk32
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk33

/-!
# Cyclic-correlation data at exponent 1381: residues 375--384

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_375 :
    natCorrelation (375 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_376 :
    natCorrelation (376 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_377 :
    natCorrelation (377 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_378 :
    natCorrelation (378 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_379 :
    natCorrelation (379 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_380 :
    natCorrelation (380 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_381 :
    natCorrelation (381 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_382 :
    natCorrelation (382 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_383 :
    natCorrelation (383 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_384 :
    natCorrelation (384 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk35 (i : Fin 10) :
    let d : Cyc := ((375 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_375
  · exact phaseCorrelation_of_nat nat_phase_correlation_376
  · exact phaseCorrelation_of_nat nat_phase_correlation_377
  · exact phaseCorrelation_of_nat nat_phase_correlation_378
  · exact phaseCorrelation_of_nat nat_phase_correlation_379
  · exact phaseCorrelation_of_nat nat_phase_correlation_380
  · exact phaseCorrelation_of_nat nat_phase_correlation_381
  · exact phaseCorrelation_of_nat nat_phase_correlation_382
  · exact phaseCorrelation_of_nat nat_phase_correlation_383
  · exact phaseCorrelation_of_nat nat_phase_correlation_384

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
