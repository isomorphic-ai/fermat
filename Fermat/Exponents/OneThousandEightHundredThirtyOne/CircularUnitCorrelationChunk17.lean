import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk13
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk14
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk15

/-!
# Cyclic-correlation data at exponent 1831: residues 195--204

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

private theorem nat_phase_correlation_195 :
    natCorrelation (195 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_196 :
    natCorrelation (196 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_197 :
    natCorrelation (197 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_198 :
    natCorrelation (198 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_199 :
    natCorrelation (199 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_200 :
    natCorrelation (200 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_201 :
    natCorrelation (201 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_202 :
    natCorrelation (202 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_203 :
    natCorrelation (203 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_204 :
    natCorrelation (204 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk17 (i : Fin 10) :
    let d : Cyc := ((195 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_195
  · exact phaseCorrelation_of_nat nat_phase_correlation_196
  · exact phaseCorrelation_of_nat nat_phase_correlation_197
  · exact phaseCorrelation_of_nat nat_phase_correlation_198
  · exact phaseCorrelation_of_nat nat_phase_correlation_199
  · exact phaseCorrelation_of_nat nat_phase_correlation_200
  · exact phaseCorrelation_of_nat nat_phase_correlation_201
  · exact phaseCorrelation_of_nat nat_phase_correlation_202
  · exact phaseCorrelation_of_nat nat_phase_correlation_203
  · exact phaseCorrelation_of_nat nat_phase_correlation_204

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
