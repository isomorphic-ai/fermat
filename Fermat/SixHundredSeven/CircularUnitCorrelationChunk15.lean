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
# Cyclic-correlation data at exponent 607: residues 75--79

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

private theorem nat_phase_correlation_75 :
    natCorrelation (75 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_76 :
    natCorrelation (76 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_77 :
    natCorrelation (77 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_78 :
    natCorrelation (78 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_79 :
    natCorrelation (79 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `5`-shift block. -/
theorem phase_correlation_chunk15 (i : Fin 5) :
    let d : Cyc := ((75 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_75
  · exact phaseCorrelation_of_nat nat_phase_correlation_76
  · exact phaseCorrelation_of_nat nat_phase_correlation_77
  · exact phaseCorrelation_of_nat nat_phase_correlation_78
  · exact phaseCorrelation_of_nat nat_phase_correlation_79

end

end Fermat.SixHundredSeven.CircularUnitCertificate
