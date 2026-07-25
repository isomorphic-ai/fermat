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
# Cyclic-correlation data at exponent 607: residues 260--264

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

private theorem nat_phase_correlation_260 :
    natCorrelation (260 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_261 :
    natCorrelation (261 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_262 :
    natCorrelation (262 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_263 :
    natCorrelation (263 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_264 :
    natCorrelation (264 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk52 (i : Fin 5) :
    let d : Cyc := ((260 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_260
  · exact phaseCorrelation_of_nat nat_phase_correlation_261
  · exact phaseCorrelation_of_nat nat_phase_correlation_262
  · exact phaseCorrelation_of_nat nat_phase_correlation_263
  · exact phaseCorrelation_of_nat nat_phase_correlation_264

end

end Fermat.SixHundredSeven.CircularUnitCertificate
