import Fermat.SixHundredSeven.CircularUnitCorrelationChunk1
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk2
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk3
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk4
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk5
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk6
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk7
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk8
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk9
import Fermat.SixHundredSeven.CircularUnitCorrelationChunk10

/-!
# Cyclic-correlation data at exponent 607: residues 80--84

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

private theorem nat_phase_correlation_80 :
    natCorrelation (80 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_81 :
    natCorrelation (81 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_82 :
    natCorrelation (82 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_83 :
    natCorrelation (83 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_84 :
    natCorrelation (84 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk16 (i : Fin 5) :
    let d : Cyc := ((80 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_80
  · exact phaseCorrelation_of_nat nat_phase_correlation_81
  · exact phaseCorrelation_of_nat nat_phase_correlation_82
  · exact phaseCorrelation_of_nat nat_phase_correlation_83
  · exact phaseCorrelation_of_nat nat_phase_correlation_84

end

end Fermat.SixHundredSeven.CircularUnitCertificate
