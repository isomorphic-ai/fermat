import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk4
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk5
import Fermat.Exponents.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk6

/-!
# Cyclic-correlation data at exponent 1831: residues 115--124

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

private theorem nat_phase_correlation_120 :
    natCorrelation (120 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_121 :
    natCorrelation (121 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_122 :
    natCorrelation (122 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_123 :
    natCorrelation (123 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_124 :
    natCorrelation (124 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk9 (i : Fin 10) :
    let d : Cyc := ((115 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_115
  · exact phaseCorrelation_of_nat nat_phase_correlation_116
  · exact phaseCorrelation_of_nat nat_phase_correlation_117
  · exact phaseCorrelation_of_nat nat_phase_correlation_118
  · exact phaseCorrelation_of_nat nat_phase_correlation_119
  · exact phaseCorrelation_of_nat nat_phase_correlation_120
  · exact phaseCorrelation_of_nat nat_phase_correlation_121
  · exact phaseCorrelation_of_nat nat_phase_correlation_122
  · exact phaseCorrelation_of_nat nat_phase_correlation_123
  · exact phaseCorrelation_of_nat nat_phase_correlation_124

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
