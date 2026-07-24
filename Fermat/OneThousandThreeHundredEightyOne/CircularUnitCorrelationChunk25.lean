import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk22
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk23
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk24

/-!
# Cyclic-correlation data at exponent 1381: residues 275--284

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

private theorem nat_phase_correlation_275 :
    natCorrelation (275 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_276 :
    natCorrelation (276 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_277 :
    natCorrelation (277 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_278 :
    natCorrelation (278 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_279 :
    natCorrelation (279 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_280 :
    natCorrelation (280 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_281 :
    natCorrelation (281 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_282 :
    natCorrelation (282 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_283 :
    natCorrelation (283 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_284 :
    natCorrelation (284 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk25 (i : Fin 10) :
    let d : Cyc := ((275 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_275
  · exact phaseCorrelation_of_nat nat_phase_correlation_276
  · exact phaseCorrelation_of_nat nat_phase_correlation_277
  · exact phaseCorrelation_of_nat nat_phase_correlation_278
  · exact phaseCorrelation_of_nat nat_phase_correlation_279
  · exact phaseCorrelation_of_nat nat_phase_correlation_280
  · exact phaseCorrelation_of_nat nat_phase_correlation_281
  · exact phaseCorrelation_of_nat nat_phase_correlation_282
  · exact phaseCorrelation_of_nat nat_phase_correlation_283
  · exact phaseCorrelation_of_nat nat_phase_correlation_284

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
