import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk25
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk26
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk27

/-!
# Cyclic-correlation data at exponent 1381: residues 315--324

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

private theorem nat_phase_correlation_315 :
    natCorrelation (315 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_316 :
    natCorrelation (316 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_317 :
    natCorrelation (317 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_318 :
    natCorrelation (318 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_319 :
    natCorrelation (319 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_320 :
    natCorrelation (320 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_321 :
    natCorrelation (321 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_322 :
    natCorrelation (322 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_323 :
    natCorrelation (323 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_324 :
    natCorrelation (324 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk29 (i : Fin 10) :
    let d : Cyc := ((315 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_315
  · exact phaseCorrelation_of_nat nat_phase_correlation_316
  · exact phaseCorrelation_of_nat nat_phase_correlation_317
  · exact phaseCorrelation_of_nat nat_phase_correlation_318
  · exact phaseCorrelation_of_nat nat_phase_correlation_319
  · exact phaseCorrelation_of_nat nat_phase_correlation_320
  · exact phaseCorrelation_of_nat nat_phase_correlation_321
  · exact phaseCorrelation_of_nat nat_phase_correlation_322
  · exact phaseCorrelation_of_nat nat_phase_correlation_323
  · exact phaseCorrelation_of_nat nat_phase_correlation_324

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
