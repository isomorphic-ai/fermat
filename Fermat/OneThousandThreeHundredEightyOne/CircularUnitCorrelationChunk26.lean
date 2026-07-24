import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk22
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk23
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk24

/-!
# Cyclic-correlation data at exponent 1381: residues 285--294

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

private theorem nat_phase_correlation_285 :
    natCorrelation (285 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_286 :
    natCorrelation (286 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_287 :
    natCorrelation (287 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_288 :
    natCorrelation (288 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_289 :
    natCorrelation (289 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_290 :
    natCorrelation (290 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_291 :
    natCorrelation (291 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_292 :
    natCorrelation (292 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_293 :
    natCorrelation (293 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_294 :
    natCorrelation (294 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk26 (i : Fin 10) :
    let d : Cyc := ((285 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_285
  · exact phaseCorrelation_of_nat nat_phase_correlation_286
  · exact phaseCorrelation_of_nat nat_phase_correlation_287
  · exact phaseCorrelation_of_nat nat_phase_correlation_288
  · exact phaseCorrelation_of_nat nat_phase_correlation_289
  · exact phaseCorrelation_of_nat nat_phase_correlation_290
  · exact phaseCorrelation_of_nat nat_phase_correlation_291
  · exact phaseCorrelation_of_nat nat_phase_correlation_292
  · exact phaseCorrelation_of_nat nat_phase_correlation_293
  · exact phaseCorrelation_of_nat nat_phase_correlation_294

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
