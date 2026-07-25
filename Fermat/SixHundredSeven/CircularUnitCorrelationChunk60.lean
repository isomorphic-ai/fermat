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
# Cyclic-correlation data at exponent 607: residues 300--302

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

private theorem nat_phase_correlation_300 :
    natCorrelation (300 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_301 :
    natCorrelation (301 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_302 :
    natCorrelation (302 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `3`-shift block. -/
theorem phase_correlation_chunk60 (i : Fin 3) :
    let d : Cyc := ((300 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_300
  · exact phaseCorrelation_of_nat nat_phase_correlation_301
  · exact phaseCorrelation_of_nat nat_phase_correlation_302

end

end Fermat.SixHundredSeven.CircularUnitCertificate
