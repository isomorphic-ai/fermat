import Fermat.SixHundredSeven.CircularUnitCorrelationChunk11
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk12
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk13
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk14
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk15
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk16
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk17
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk18
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk19
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk20

/-!
# Cyclic-correlation data at exponent 607: residues 140--144

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

private theorem nat_phase_correlation_140 :
    natCorrelation (140 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_141 :
    natCorrelation (141 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_142 :
    natCorrelation (142 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_143 :
    natCorrelation (143 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_144 :
    natCorrelation (144 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk28 (i : Fin 5) :
    let d : Cyc := ((140 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_140
  · exact phaseCorrelation_of_nat nat_phase_correlation_141
  · exact phaseCorrelation_of_nat nat_phase_correlation_142
  · exact phaseCorrelation_of_nat nat_phase_correlation_143
  · exact phaseCorrelation_of_nat nat_phase_correlation_144

end

end Fermat.SixHundredSeven.CircularUnitCertificate
