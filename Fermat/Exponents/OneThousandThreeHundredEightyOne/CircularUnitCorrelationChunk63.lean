import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk58
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk59
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk60

/-!
# Cyclic-correlation data at exponent 1381: residues 655--664

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

private theorem nat_phase_correlation_655 :
    natCorrelation (655 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_656 :
    natCorrelation (656 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_657 :
    natCorrelation (657 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_658 :
    natCorrelation (658 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_659 :
    natCorrelation (659 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_660 :
    natCorrelation (660 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_661 :
    natCorrelation (661 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_662 :
    natCorrelation (662 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_663 :
    natCorrelation (663 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_664 :
    natCorrelation (664 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk63 (i : Fin 10) :
    let d : Cyc := ((655 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_655
  · exact phaseCorrelation_of_nat nat_phase_correlation_656
  · exact phaseCorrelation_of_nat nat_phase_correlation_657
  · exact phaseCorrelation_of_nat nat_phase_correlation_658
  · exact phaseCorrelation_of_nat nat_phase_correlation_659
  · exact phaseCorrelation_of_nat nat_phase_correlation_660
  · exact phaseCorrelation_of_nat nat_phase_correlation_661
  · exact phaseCorrelation_of_nat nat_phase_correlation_662
  · exact phaseCorrelation_of_nat nat_phase_correlation_663
  · exact phaseCorrelation_of_nat nat_phase_correlation_664

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
