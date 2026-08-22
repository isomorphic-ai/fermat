import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk55
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk56
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk57

/-!
# Cyclic-correlation data at exponent 1381: residues 605--614

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

private theorem nat_phase_correlation_605 :
    natCorrelation (605 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_606 :
    natCorrelation (606 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_607 :
    natCorrelation (607 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_608 :
    natCorrelation (608 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_609 :
    natCorrelation (609 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_610 :
    natCorrelation (610 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_611 :
    natCorrelation (611 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_612 :
    natCorrelation (612 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_613 :
    natCorrelation (613 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_614 :
    natCorrelation (614 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk58 (i : Fin 10) :
    let d : Cyc := ((605 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_605
  · exact phaseCorrelation_of_nat nat_phase_correlation_606
  · exact phaseCorrelation_of_nat nat_phase_correlation_607
  · exact phaseCorrelation_of_nat nat_phase_correlation_608
  · exact phaseCorrelation_of_nat nat_phase_correlation_609
  · exact phaseCorrelation_of_nat nat_phase_correlation_610
  · exact phaseCorrelation_of_nat nat_phase_correlation_611
  · exact phaseCorrelation_of_nat nat_phase_correlation_612
  · exact phaseCorrelation_of_nat nat_phase_correlation_613
  · exact phaseCorrelation_of_nat nat_phase_correlation_614

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
