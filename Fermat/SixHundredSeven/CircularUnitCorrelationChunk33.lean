import Fermat.SixHundredSeven.CircularUnitCorrelationChunk21
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk22
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk23
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk24
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk25
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk26
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk27
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk28
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk29
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk30

/-!
# Cyclic-correlation data at exponent 607: residues 165--169

This module kernel-checks five or fewer shifts as separate tail-recursive
natural computations. The modules are arranged in restartable dependency
tiers of width ten.
-/

namespace Fermat.SixHundredSeven.CircularUnitCertificate

noncomputable section

open Fermat.SixHundredSeven.CircularUnitCyclic
open Fermat.SixHundredSeven.CircularUnitMatrix

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

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk33 (i : Fin 5) :
    let d : Cyc := ((165 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_165
  · exact phaseCorrelation_of_nat nat_phase_correlation_166
  · exact phaseCorrelation_of_nat nat_phase_correlation_167
  · exact phaseCorrelation_of_nat nat_phase_correlation_168
  · exact phaseCorrelation_of_nat nat_phase_correlation_169

end

end Fermat.SixHundredSeven.CircularUnitCertificate
