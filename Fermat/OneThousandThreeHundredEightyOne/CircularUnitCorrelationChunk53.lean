import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk49
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk50
import Fermat.OneThousandThreeHundredEightyOne.CircularUnitCorrelationChunk51

/-!
# Cyclic-correlation data at exponent 1381: residues 555--564

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

private theorem nat_phase_correlation_555 :
    natCorrelation (555 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_556 :
    natCorrelation (556 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_557 :
    natCorrelation (557 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_558 :
    natCorrelation (558 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_559 :
    natCorrelation (559 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_560 :
    natCorrelation (560 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_561 :
    natCorrelation (561 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_562 :
    natCorrelation (562 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_563 :
    natCorrelation (563 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_564 :
    natCorrelation (564 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk53 (i : Fin 10) :
    let d : Cyc := ((555 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_555
  · exact phaseCorrelation_of_nat nat_phase_correlation_556
  · exact phaseCorrelation_of_nat nat_phase_correlation_557
  · exact phaseCorrelation_of_nat nat_phase_correlation_558
  · exact phaseCorrelation_of_nat nat_phase_correlation_559
  · exact phaseCorrelation_of_nat nat_phase_correlation_560
  · exact phaseCorrelation_of_nat nat_phase_correlation_561
  · exact phaseCorrelation_of_nat nat_phase_correlation_562
  · exact phaseCorrelation_of_nat nat_phase_correlation_563
  · exact phaseCorrelation_of_nat nat_phase_correlation_564

end

end Fermat.OneThousandThreeHundredEightyOne.CircularUnitCertificate
