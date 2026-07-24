import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk61
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk62
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk63

/-!
# Cyclic-correlation data at exponent 1381: residues 665--674

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

private theorem nat_phase_correlation_665 :
    natCorrelation (665 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_666 :
    natCorrelation (666 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_667 :
    natCorrelation (667 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_668 :
    natCorrelation (668 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_669 :
    natCorrelation (669 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_670 :
    natCorrelation (670 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_671 :
    natCorrelation (671 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_672 :
    natCorrelation (672 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_673 :
    natCorrelation (673 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_674 :
    natCorrelation (674 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk64 (i : Fin 10) :
    let d : Cyc := ((665 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_665
  · exact phaseCorrelation_of_nat nat_phase_correlation_666
  · exact phaseCorrelation_of_nat nat_phase_correlation_667
  · exact phaseCorrelation_of_nat nat_phase_correlation_668
  · exact phaseCorrelation_of_nat nat_phase_correlation_669
  · exact phaseCorrelation_of_nat nat_phase_correlation_670
  · exact phaseCorrelation_of_nat nat_phase_correlation_671
  · exact phaseCorrelation_of_nat nat_phase_correlation_672
  · exact phaseCorrelation_of_nat nat_phase_correlation_673
  · exact phaseCorrelation_of_nat nat_phase_correlation_674

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
