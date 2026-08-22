import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk10
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk11
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk12

/-!
# Cyclic-correlation data at exponent 1831: residues 165--174

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

private theorem nat_phase_correlation_165 :
    natCorrelation (165 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_166 :
    natCorrelation (166 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_167 :
    natCorrelation (167 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_168 :
    natCorrelation (168 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_169 :
    natCorrelation (169 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_170 :
    natCorrelation (170 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_171 :
    natCorrelation (171 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_172 :
    natCorrelation (172 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_173 :
    natCorrelation (173 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_174 :
    natCorrelation (174 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk14 (i : Fin 10) :
    let d : Cyc := ((165 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_165
  · exact phaseCorrelation_of_nat nat_phase_correlation_166
  · exact phaseCorrelation_of_nat nat_phase_correlation_167
  · exact phaseCorrelation_of_nat nat_phase_correlation_168
  · exact phaseCorrelation_of_nat nat_phase_correlation_169
  · exact phaseCorrelation_of_nat nat_phase_correlation_170
  · exact phaseCorrelation_of_nat nat_phase_correlation_171
  · exact phaseCorrelation_of_nat nat_phase_correlation_172
  · exact phaseCorrelation_of_nat nat_phase_correlation_173
  · exact phaseCorrelation_of_nat nat_phase_correlation_174

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
