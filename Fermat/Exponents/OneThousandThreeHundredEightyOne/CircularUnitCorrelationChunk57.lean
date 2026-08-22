import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk52
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk53
import Fermat.Exponents.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk54

/-!
# Cyclic-correlation data at exponent 1381: residues 595--604

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

private theorem nat_phase_correlation_595 :
    natCorrelation (595 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_596 :
    natCorrelation (596 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_597 :
    natCorrelation (597 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_598 :
    natCorrelation (598 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_599 :
    natCorrelation (599 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_600 :
    natCorrelation (600 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_601 :
    natCorrelation (601 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_602 :
    natCorrelation (602 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_603 :
    natCorrelation (603 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_604 :
    natCorrelation (604 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk57 (i : Fin 10) :
    let d : Cyc := ((595 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_595
  · exact phaseCorrelation_of_nat nat_phase_correlation_596
  · exact phaseCorrelation_of_nat nat_phase_correlation_597
  · exact phaseCorrelation_of_nat nat_phase_correlation_598
  · exact phaseCorrelation_of_nat nat_phase_correlation_599
  · exact phaseCorrelation_of_nat nat_phase_correlation_600
  · exact phaseCorrelation_of_nat nat_phase_correlation_601
  · exact phaseCorrelation_of_nat nat_phase_correlation_602
  · exact phaseCorrelation_of_nat nat_phase_correlation_603
  · exact phaseCorrelation_of_nat nat_phase_correlation_604

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
