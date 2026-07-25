import Fermat.SixHundredSeven.CircularUnitCorrelationChunk31
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk32
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk33
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk34
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk35
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk36
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk37
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk38
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk39
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk40

/-!
# Cyclic-correlation data at exponent 607: residues 215--219

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

private theorem nat_phase_correlation_215 :
    natCorrelation (215 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_216 :
    natCorrelation (216 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_217 :
    natCorrelation (217 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_218 :
    natCorrelation (218 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_219 :
    natCorrelation (219 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk43 (i : Fin 5) :
    let d : Cyc := ((215 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_215
  · exact phaseCorrelation_of_nat nat_phase_correlation_216
  · exact phaseCorrelation_of_nat nat_phase_correlation_217
  · exact phaseCorrelation_of_nat nat_phase_correlation_218
  · exact phaseCorrelation_of_nat nat_phase_correlation_219

end

end Fermat.SixHundredSeven.CircularUnitCertificate
