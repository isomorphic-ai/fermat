import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk7
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk8
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk9

/-!
# Cyclic-correlation data at exponent 1381: residues 125--134

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

private theorem nat_phase_correlation_125 :
    natCorrelation (125 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_126 :
    natCorrelation (126 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_127 :
    natCorrelation (127 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_128 :
    natCorrelation (128 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_129 :
    natCorrelation (129 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_130 :
    natCorrelation (130 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_131 :
    natCorrelation (131 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_132 :
    natCorrelation (132 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_133 :
    natCorrelation (133 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_134 :
    natCorrelation (134 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk10 (i : Fin 10) :
    let d : Cyc := ((125 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_125
  · exact phaseCorrelation_of_nat nat_phase_correlation_126
  · exact phaseCorrelation_of_nat nat_phase_correlation_127
  · exact phaseCorrelation_of_nat nat_phase_correlation_128
  · exact phaseCorrelation_of_nat nat_phase_correlation_129
  · exact phaseCorrelation_of_nat nat_phase_correlation_130
  · exact phaseCorrelation_of_nat nat_phase_correlation_131
  · exact phaseCorrelation_of_nat nat_phase_correlation_132
  · exact phaseCorrelation_of_nat nat_phase_correlation_133
  · exact phaseCorrelation_of_nat nat_phase_correlation_134

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
