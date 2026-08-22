import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk13
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk14
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk15

/-!
# Cyclic-correlation data at exponent 1831: residues 185--194

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

private theorem nat_phase_correlation_185 :
    natCorrelation (185 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_186 :
    natCorrelation (186 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_187 :
    natCorrelation (187 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_188 :
    natCorrelation (188 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_189 :
    natCorrelation (189 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_190 :
    natCorrelation (190 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_191 :
    natCorrelation (191 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_192 :
    natCorrelation (192 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_193 :
    natCorrelation (193 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_194 :
    natCorrelation (194 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk16 (i : Fin 10) :
    let d : Cyc := ((185 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_185
  · exact phaseCorrelation_of_nat nat_phase_correlation_186
  · exact phaseCorrelation_of_nat nat_phase_correlation_187
  · exact phaseCorrelation_of_nat nat_phase_correlation_188
  · exact phaseCorrelation_of_nat nat_phase_correlation_189
  · exact phaseCorrelation_of_nat nat_phase_correlation_190
  · exact phaseCorrelation_of_nat nat_phase_correlation_191
  · exact phaseCorrelation_of_nat nat_phase_correlation_192
  · exact phaseCorrelation_of_nat nat_phase_correlation_193
  · exact phaseCorrelation_of_nat nat_phase_correlation_194

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
