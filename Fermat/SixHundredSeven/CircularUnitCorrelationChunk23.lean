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
# Cyclic-correlation data at exponent 607: residues 115--119

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

private theorem nat_phase_correlation_115 :
    natCorrelation (115 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_116 :
    natCorrelation (116 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_117 :
    natCorrelation (117 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_118 :
    natCorrelation (118 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_119 :
    natCorrelation (119 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk23 (i : Fin 5) :
    let d : Cyc := ((115 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_115
  · exact phaseCorrelation_of_nat nat_phase_correlation_116
  · exact phaseCorrelation_of_nat nat_phase_correlation_117
  · exact phaseCorrelation_of_nat nat_phase_correlation_118
  · exact phaseCorrelation_of_nat nat_phase_correlation_119

end

end Fermat.SixHundredSeven.CircularUnitCertificate
