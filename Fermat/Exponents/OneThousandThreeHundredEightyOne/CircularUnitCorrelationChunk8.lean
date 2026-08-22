import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk4
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk5
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk6

/-!
# Cyclic-correlation data at exponent 1381: residues 105--114

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

private theorem nat_phase_correlation_105 :
    natCorrelation (105 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_106 :
    natCorrelation (106 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_107 :
    natCorrelation (107 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_108 :
    natCorrelation (108 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_109 :
    natCorrelation (109 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_110 :
    natCorrelation (110 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_111 :
    natCorrelation (111 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_112 :
    natCorrelation (112 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_113 :
    natCorrelation (113 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_114 :
    natCorrelation (114 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk8 (i : Fin 10) :
    let d : Cyc := ((105 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_105
  · exact phaseCorrelation_of_nat nat_phase_correlation_106
  · exact phaseCorrelation_of_nat nat_phase_correlation_107
  · exact phaseCorrelation_of_nat nat_phase_correlation_108
  · exact phaseCorrelation_of_nat nat_phase_correlation_109
  · exact phaseCorrelation_of_nat nat_phase_correlation_110
  · exact phaseCorrelation_of_nat nat_phase_correlation_111
  · exact phaseCorrelation_of_nat nat_phase_correlation_112
  · exact phaseCorrelation_of_nat nat_phase_correlation_113
  · exact phaseCorrelation_of_nat nat_phase_correlation_114

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
