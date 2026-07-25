import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk7
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk8
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk9

/-!
# Cyclic-correlation data at exponent 1381: residues 145--154

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandThreeHundredEightyOne.CircularUnitCyclic
open Fermat.OneThousandThreeHundredEightyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_145 :
    natCorrelation (145 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_146 :
    natCorrelation (146 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_147 :
    natCorrelation (147 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_148 :
    natCorrelation (148 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_149 :
    natCorrelation (149 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_150 :
    natCorrelation (150 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_151 :
    natCorrelation (151 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_152 :
    natCorrelation (152 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_153 :
    natCorrelation (153 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_154 :
    natCorrelation (154 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk12 (i : Fin 10) :
    let d : Cyc := ((145 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_145
  · exact phaseCorrelation_of_nat nat_phase_correlation_146
  · exact phaseCorrelation_of_nat nat_phase_correlation_147
  · exact phaseCorrelation_of_nat nat_phase_correlation_148
  · exact phaseCorrelation_of_nat nat_phase_correlation_149
  · exact phaseCorrelation_of_nat nat_phase_correlation_150
  · exact phaseCorrelation_of_nat nat_phase_correlation_151
  · exact phaseCorrelation_of_nat nat_phase_correlation_152
  · exact phaseCorrelation_of_nat nat_phase_correlation_153
  · exact phaseCorrelation_of_nat nat_phase_correlation_154

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
