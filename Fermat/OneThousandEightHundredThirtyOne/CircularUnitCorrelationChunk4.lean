import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk1
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk2
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk3

/-!
# Cyclic-correlation data at exponent 1831: residues 65--74

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_65 :
    natCorrelation (65 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_66 :
    natCorrelation (66 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_67 :
    natCorrelation (67 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_68 :
    natCorrelation (68 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_69 :
    natCorrelation (69 : Cyc) = 0 := by
  decide

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

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk4 (i : Fin 10) :
    let d : Cyc := ((65 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_65
  · exact phaseCorrelation_of_nat nat_phase_correlation_66
  · exact phaseCorrelation_of_nat nat_phase_correlation_67
  · exact phaseCorrelation_of_nat nat_phase_correlation_68
  · exact phaseCorrelation_of_nat nat_phase_correlation_69
  · exact phaseCorrelation_of_nat nat_phase_correlation_70
  · exact phaseCorrelation_of_nat nat_phase_correlation_71
  · exact phaseCorrelation_of_nat nat_phase_correlation_72
  · exact phaseCorrelation_of_nat nat_phase_correlation_73
  · exact phaseCorrelation_of_nat nat_phase_correlation_74

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
