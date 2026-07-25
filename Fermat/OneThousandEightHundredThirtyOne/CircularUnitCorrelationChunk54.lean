import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk49
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk50
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk51

/-!
# Cyclic-correlation data at exponent 1831: residues 565--574

This module kernel-checks its shifts as separate tail-recursive natural
computations. Keeping each decision in its own declaration lets Lean
release normalization state before checking the next shift.
-/

namespace Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate

noncomputable section

open Fermat.OneThousandEightHundredThirtyOne.CircularUnitCyclic
open Fermat.OneThousandEightHundredThirtyOne.CircularUnitMatrix

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem nat_phase_correlation_565 :
    natCorrelation (565 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_566 :
    natCorrelation (566 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_567 :
    natCorrelation (567 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_568 :
    natCorrelation (568 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_569 :
    natCorrelation (569 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_570 :
    natCorrelation (570 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_571 :
    natCorrelation (571 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_572 :
    natCorrelation (572 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_573 :
    natCorrelation (573 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_574 :
    natCorrelation (574 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk54 (i : Fin 10) :
    let d : Cyc := ((565 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_565
  · exact phaseCorrelation_of_nat nat_phase_correlation_566
  · exact phaseCorrelation_of_nat nat_phase_correlation_567
  · exact phaseCorrelation_of_nat nat_phase_correlation_568
  · exact phaseCorrelation_of_nat nat_phase_correlation_569
  · exact phaseCorrelation_of_nat nat_phase_correlation_570
  · exact phaseCorrelation_of_nat nat_phase_correlation_571
  · exact phaseCorrelation_of_nat nat_phase_correlation_572
  · exact phaseCorrelation_of_nat nat_phase_correlation_573
  · exact phaseCorrelation_of_nat nat_phase_correlation_574

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
