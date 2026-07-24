import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk4
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk5
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk6

/-!
# Cyclic-correlation data at exponent 1381: residues 95--104

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

private theorem nat_phase_correlation_95 :
    natCorrelation (95 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_96 :
    natCorrelation (96 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_97 :
    natCorrelation (97 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_98 :
    natCorrelation (98 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_99 :
    natCorrelation (99 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_100 :
    natCorrelation (100 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_101 :
    natCorrelation (101 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_102 :
    natCorrelation (102 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_103 :
    natCorrelation (103 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_104 :
    natCorrelation (104 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk7 (i : Fin 10) :
    let d : Cyc := ((95 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_95
  · exact phaseCorrelation_of_nat nat_phase_correlation_96
  · exact phaseCorrelation_of_nat nat_phase_correlation_97
  · exact phaseCorrelation_of_nat nat_phase_correlation_98
  · exact phaseCorrelation_of_nat nat_phase_correlation_99
  · exact phaseCorrelation_of_nat nat_phase_correlation_100
  · exact phaseCorrelation_of_nat nat_phase_correlation_101
  · exact phaseCorrelation_of_nat nat_phase_correlation_102
  · exact phaseCorrelation_of_nat nat_phase_correlation_103
  · exact phaseCorrelation_of_nat nat_phase_correlation_104

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
