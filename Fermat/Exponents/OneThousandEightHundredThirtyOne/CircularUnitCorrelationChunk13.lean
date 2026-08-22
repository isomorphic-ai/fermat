import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk10
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk11
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk12

/-!
# Cyclic-correlation data at exponent 1831: residues 155--164

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

private theorem nat_phase_correlation_155 :
    natCorrelation (155 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_156 :
    natCorrelation (156 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_157 :
    natCorrelation (157 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_158 :
    natCorrelation (158 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_159 :
    natCorrelation (159 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_160 :
    natCorrelation (160 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_161 :
    natCorrelation (161 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_162 :
    natCorrelation (162 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_163 :
    natCorrelation (163 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_164 :
    natCorrelation (164 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk13 (i : Fin 10) :
    let d : Cyc := ((155 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_155
  · exact phaseCorrelation_of_nat nat_phase_correlation_156
  · exact phaseCorrelation_of_nat nat_phase_correlation_157
  · exact phaseCorrelation_of_nat nat_phase_correlation_158
  · exact phaseCorrelation_of_nat nat_phase_correlation_159
  · exact phaseCorrelation_of_nat nat_phase_correlation_160
  · exact phaseCorrelation_of_nat nat_phase_correlation_161
  · exact phaseCorrelation_of_nat nat_phase_correlation_162
  · exact phaseCorrelation_of_nat nat_phase_correlation_163
  · exact phaseCorrelation_of_nat nat_phase_correlation_164

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
