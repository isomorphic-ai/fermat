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
# Cyclic-correlation data at exponent 607: residues 275--279

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

private theorem nat_phase_correlation_275 :
    natCorrelation (275 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_276 :
    natCorrelation (276 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_277 :
    natCorrelation (277 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_278 :
    natCorrelation (278 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_279 :
    natCorrelation (279 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk55 (i : Fin 5) :
    let d : Cyc := ((275 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_275
  · exact phaseCorrelation_of_nat nat_phase_correlation_276
  · exact phaseCorrelation_of_nat nat_phase_correlation_277
  · exact phaseCorrelation_of_nat nat_phase_correlation_278
  · exact phaseCorrelation_of_nat nat_phase_correlation_279

end

end Fermat.SixHundredSeven.CircularUnitCertificate
