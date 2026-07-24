import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk58
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk59
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk60

/-!
# Cyclic-correlation data at exponent 1381: residues 645--654

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

private theorem nat_phase_correlation_645 :
    natCorrelation (645 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_646 :
    natCorrelation (646 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_647 :
    natCorrelation (647 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_648 :
    natCorrelation (648 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_649 :
    natCorrelation (649 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_650 :
    natCorrelation (650 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_651 :
    natCorrelation (651 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_652 :
    natCorrelation (652 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_653 :
    natCorrelation (653 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_654 :
    natCorrelation (654 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk62 (i : Fin 10) :
    let d : Cyc := ((645 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_645
  · exact phaseCorrelation_of_nat nat_phase_correlation_646
  · exact phaseCorrelation_of_nat nat_phase_correlation_647
  · exact phaseCorrelation_of_nat nat_phase_correlation_648
  · exact phaseCorrelation_of_nat nat_phase_correlation_649
  · exact phaseCorrelation_of_nat nat_phase_correlation_650
  · exact phaseCorrelation_of_nat nat_phase_correlation_651
  · exact phaseCorrelation_of_nat nat_phase_correlation_652
  · exact phaseCorrelation_of_nat nat_phase_correlation_653
  · exact phaseCorrelation_of_nat nat_phase_correlation_654

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
