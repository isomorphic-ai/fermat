import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk49
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk50
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk51

/-!
# Cyclic-correlation data at exponent 1381: residues 545--554

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

private theorem nat_phase_correlation_545 :
    natCorrelation (545 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_546 :
    natCorrelation (546 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_547 :
    natCorrelation (547 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_548 :
    natCorrelation (548 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_549 :
    natCorrelation (549 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_550 :
    natCorrelation (550 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_551 :
    natCorrelation (551 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_552 :
    natCorrelation (552 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_553 :
    natCorrelation (553 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_554 :
    natCorrelation (554 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk52 (i : Fin 10) :
    let d : Cyc := ((545 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_545
  · exact phaseCorrelation_of_nat nat_phase_correlation_546
  · exact phaseCorrelation_of_nat nat_phase_correlation_547
  · exact phaseCorrelation_of_nat nat_phase_correlation_548
  · exact phaseCorrelation_of_nat nat_phase_correlation_549
  · exact phaseCorrelation_of_nat nat_phase_correlation_550
  · exact phaseCorrelation_of_nat nat_phase_correlation_551
  · exact phaseCorrelation_of_nat nat_phase_correlation_552
  · exact phaseCorrelation_of_nat nat_phase_correlation_553
  · exact phaseCorrelation_of_nat nat_phase_correlation_554

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
