import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk55
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk56
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk57

/-!
# Cyclic-correlation data at exponent 1831: residues 625--634

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

private theorem nat_phase_correlation_625 :
    natCorrelation (625 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_626 :
    natCorrelation (626 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_627 :
    natCorrelation (627 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_628 :
    natCorrelation (628 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_629 :
    natCorrelation (629 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_630 :
    natCorrelation (630 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_631 :
    natCorrelation (631 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_632 :
    natCorrelation (632 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_633 :
    natCorrelation (633 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_634 :
    natCorrelation (634 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk60 (i : Fin 10) :
    let d : Cyc := ((625 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_625
  · exact phaseCorrelation_of_nat nat_phase_correlation_626
  · exact phaseCorrelation_of_nat nat_phase_correlation_627
  · exact phaseCorrelation_of_nat nat_phase_correlation_628
  · exact phaseCorrelation_of_nat nat_phase_correlation_629
  · exact phaseCorrelation_of_nat nat_phase_correlation_630
  · exact phaseCorrelation_of_nat nat_phase_correlation_631
  · exact phaseCorrelation_of_nat nat_phase_correlation_632
  · exact phaseCorrelation_of_nat nat_phase_correlation_633
  · exact phaseCorrelation_of_nat nat_phase_correlation_634

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
