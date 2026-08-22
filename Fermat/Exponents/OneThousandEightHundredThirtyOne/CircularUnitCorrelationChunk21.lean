import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk16
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk17
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk18

/-!
# Cyclic-correlation data at exponent 1831: residues 235--244

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

private theorem nat_phase_correlation_235 :
    natCorrelation (235 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_236 :
    natCorrelation (236 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_237 :
    natCorrelation (237 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_238 :
    natCorrelation (238 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_239 :
    natCorrelation (239 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_240 :
    natCorrelation (240 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_241 :
    natCorrelation (241 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_242 :
    natCorrelation (242 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_243 :
    natCorrelation (243 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_244 :
    natCorrelation (244 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk21 (i : Fin 10) :
    let d : Cyc := ((235 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_235
  · exact phaseCorrelation_of_nat nat_phase_correlation_236
  · exact phaseCorrelation_of_nat nat_phase_correlation_237
  · exact phaseCorrelation_of_nat nat_phase_correlation_238
  · exact phaseCorrelation_of_nat nat_phase_correlation_239
  · exact phaseCorrelation_of_nat nat_phase_correlation_240
  · exact phaseCorrelation_of_nat nat_phase_correlation_241
  · exact phaseCorrelation_of_nat nat_phase_correlation_242
  · exact phaseCorrelation_of_nat nat_phase_correlation_243
  · exact phaseCorrelation_of_nat nat_phase_correlation_244

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
