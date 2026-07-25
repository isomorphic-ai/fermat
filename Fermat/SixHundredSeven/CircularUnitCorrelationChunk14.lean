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
# Cyclic-correlation data at exponent 607: residues 70--74

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

private theorem nat_phase_correlation_70 :
    natCorrelation (70 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_71 :
    natCorrelation (71 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_72 :
    natCorrelation (72 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_73 :
    natCorrelation (73 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_74 :
    natCorrelation (74 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk14 (i : Fin 5) :
    let d : Cyc := ((70 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_70
  · exact phaseCorrelation_of_nat nat_phase_correlation_71
  · exact phaseCorrelation_of_nat nat_phase_correlation_72
  · exact phaseCorrelation_of_nat nat_phase_correlation_73
  · exact phaseCorrelation_of_nat nat_phase_correlation_74

end

end Fermat.SixHundredSeven.CircularUnitCertificate
