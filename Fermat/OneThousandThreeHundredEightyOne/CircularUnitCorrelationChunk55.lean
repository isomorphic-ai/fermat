import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk52
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk53
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk54

/-!
# Cyclic-correlation data at exponent 1381: residues 575--584

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

private theorem nat_phase_correlation_575 :
    natCorrelation (575 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_576 :
    natCorrelation (576 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_577 :
    natCorrelation (577 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_578 :
    natCorrelation (578 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_579 :
    natCorrelation (579 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_580 :
    natCorrelation (580 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_581 :
    natCorrelation (581 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_582 :
    natCorrelation (582 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_583 :
    natCorrelation (583 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_584 :
    natCorrelation (584 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk55 (i : Fin 10) :
    let d : Cyc := ((575 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_575
  · exact phaseCorrelation_of_nat nat_phase_correlation_576
  · exact phaseCorrelation_of_nat nat_phase_correlation_577
  · exact phaseCorrelation_of_nat nat_phase_correlation_578
  · exact phaseCorrelation_of_nat nat_phase_correlation_579
  · exact phaseCorrelation_of_nat nat_phase_correlation_580
  · exact phaseCorrelation_of_nat nat_phase_correlation_581
  · exact phaseCorrelation_of_nat nat_phase_correlation_582
  · exact phaseCorrelation_of_nat nat_phase_correlation_583
  · exact phaseCorrelation_of_nat nat_phase_correlation_584

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
