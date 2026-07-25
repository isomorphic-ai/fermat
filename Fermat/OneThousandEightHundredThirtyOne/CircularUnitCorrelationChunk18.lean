import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk13
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk14
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk15

/-!
# Cyclic-correlation data at exponent 1831: residues 205--214

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

private theorem nat_phase_correlation_205 :
    natCorrelation (205 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_206 :
    natCorrelation (206 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_207 :
    natCorrelation (207 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_208 :
    natCorrelation (208 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_209 :
    natCorrelation (209 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_210 :
    natCorrelation (210 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_211 :
    natCorrelation (211 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_212 :
    natCorrelation (212 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_213 :
    natCorrelation (213 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_214 :
    natCorrelation (214 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk18 (i : Fin 10) :
    let d : Cyc := ((205 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_205
  · exact phaseCorrelation_of_nat nat_phase_correlation_206
  · exact phaseCorrelation_of_nat nat_phase_correlation_207
  · exact phaseCorrelation_of_nat nat_phase_correlation_208
  · exact phaseCorrelation_of_nat nat_phase_correlation_209
  · exact phaseCorrelation_of_nat nat_phase_correlation_210
  · exact phaseCorrelation_of_nat nat_phase_correlation_211
  · exact phaseCorrelation_of_nat nat_phase_correlation_212
  · exact phaseCorrelation_of_nat nat_phase_correlation_213
  · exact phaseCorrelation_of_nat nat_phase_correlation_214

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
