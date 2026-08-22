import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk16
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk17
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk18

/-!
# Cyclic-correlation data at exponent 1831: residues 225--234

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

private theorem nat_phase_correlation_225 :
    natCorrelation (225 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_226 :
    natCorrelation (226 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_227 :
    natCorrelation (227 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_228 :
    natCorrelation (228 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_229 :
    natCorrelation (229 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_230 :
    natCorrelation (230 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_231 :
    natCorrelation (231 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_232 :
    natCorrelation (232 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_233 :
    natCorrelation (233 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_234 :
    natCorrelation (234 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk20 (i : Fin 10) :
    let d : Cyc := ((225 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_225
  · exact phaseCorrelation_of_nat nat_phase_correlation_226
  · exact phaseCorrelation_of_nat nat_phase_correlation_227
  · exact phaseCorrelation_of_nat nat_phase_correlation_228
  · exact phaseCorrelation_of_nat nat_phase_correlation_229
  · exact phaseCorrelation_of_nat nat_phase_correlation_230
  · exact phaseCorrelation_of_nat nat_phase_correlation_231
  · exact phaseCorrelation_of_nat nat_phase_correlation_232
  · exact phaseCorrelation_of_nat nat_phase_correlation_233
  · exact phaseCorrelation_of_nat nat_phase_correlation_234

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
