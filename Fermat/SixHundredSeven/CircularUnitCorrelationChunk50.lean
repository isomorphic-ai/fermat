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
# Cyclic-correlation data at exponent 607: residues 250--254

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

private theorem nat_phase_correlation_250 :
    natCorrelation (250 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_251 :
    natCorrelation (251 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_252 :
    natCorrelation (252 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_253 :
    natCorrelation (253 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_254 :
    natCorrelation (254 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk50 (i : Fin 5) :
    let d : Cyc := ((250 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_250
  · exact phaseCorrelation_of_nat nat_phase_correlation_251
  · exact phaseCorrelation_of_nat nat_phase_correlation_252
  · exact phaseCorrelation_of_nat nat_phase_correlation_253
  · exact phaseCorrelation_of_nat nat_phase_correlation_254

end

end Fermat.SixHundredSeven.CircularUnitCertificate
