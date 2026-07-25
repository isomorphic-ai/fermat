import Fermat.SixHundredSeven.CircularUnitCorrelationChunk41
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk42
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk43
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk44
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk45
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk46
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk47
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk48
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk49
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk50

/-!
# Cyclic-correlation data at exponent 607: residues 290--294

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

private theorem nat_phase_correlation_290 :
    natCorrelation (290 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_291 :
    natCorrelation (291 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_292 :
    natCorrelation (292 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_293 :
    natCorrelation (293 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_294 :
    natCorrelation (294 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk58 (i : Fin 5) :
    let d : Cyc := ((290 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_290
  · exact phaseCorrelation_of_nat nat_phase_correlation_291
  · exact phaseCorrelation_of_nat nat_phase_correlation_292
  · exact phaseCorrelation_of_nat nat_phase_correlation_293
  · exact phaseCorrelation_of_nat nat_phase_correlation_294

end

end Fermat.SixHundredSeven.CircularUnitCertificate
