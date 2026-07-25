import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk64
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk65
import Fermat.OneThousandEightHundredThirtyOne.CircularUnitCorrelationChunk66

/-!
# Cyclic-correlation data at exponent 1831: residues 715--724

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

private theorem nat_phase_correlation_715 :
    natCorrelation (715 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_716 :
    natCorrelation (716 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_717 :
    natCorrelation (717 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_718 :
    natCorrelation (718 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_719 :
    natCorrelation (719 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_720 :
    natCorrelation (720 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_721 :
    natCorrelation (721 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_722 :
    natCorrelation (722 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_723 :
    natCorrelation (723 : Cyc) = 0 := by
  decide

private theorem nat_phase_correlation_724 :
    natCorrelation (724 : Cyc) = 0 := by
  decide

/-- Abstract field-valued correlations for the local `10`-shift block. -/
theorem phase_correlation_chunk69 (i : Fin 10) :
    let d : Cyc := ((715 + i.val : ℕ) : Cyc)
    (∑ u : Cyc, symbolPhase u * correlationInverse (u + d)) =
      if d = 0 then 1 else 0 := by
  fin_cases i
  · exact phaseCorrelation_of_nat nat_phase_correlation_715
  · exact phaseCorrelation_of_nat nat_phase_correlation_716
  · exact phaseCorrelation_of_nat nat_phase_correlation_717
  · exact phaseCorrelation_of_nat nat_phase_correlation_718
  · exact phaseCorrelation_of_nat nat_phase_correlation_719
  · exact phaseCorrelation_of_nat nat_phase_correlation_720
  · exact phaseCorrelation_of_nat nat_phase_correlation_721
  · exact phaseCorrelation_of_nat nat_phase_correlation_722
  · exact phaseCorrelation_of_nat nat_phase_correlation_723
  · exact phaseCorrelation_of_nat nat_phase_correlation_724

end

end Fermat.OneThousandEightHundredThirtyOne.CircularUnitCertificate
